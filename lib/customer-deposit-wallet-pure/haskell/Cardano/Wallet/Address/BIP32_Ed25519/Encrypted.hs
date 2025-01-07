module Cardano.Wallet.Address.BIP32_Ed25519.Encrypted
    ( -- * Types
      Passphrase
    , EncryptedXPrv
    , check
    , decrypt
      -- $prop-check-decrypt
    , encrypt
      -- $prop-decrypt-encrypt
    , toXPub
      -- $prop-toXPub-decrypt
    , sign
      -- $prop-sign-decrypt

      -- * Serialization
    , EncryptedXPrvBytes (..)
    , serializeEncryptedXPrv
    , deserializeEncryptedXPrv
      -- $prop-deserialize-serializeEncryptedXPrv

      -- * Key derivation
    , deriveEncryptedXPrvSoft
      -- $prop-deriveEncryptedXPrvSoft-decrypt
    , deriveEncryptedXPrvHard
      -- $prop-deriveEncryptedXPrvHard-decrypt
    , deriveEncryptedXPrvBIP32Path
    )
where

import Cardano.Wallet.Address.BIP32
    ( BIP32Path (Root, Segment)
    , DerivationType (Hardened, Soft)
    )
import Cardano.Wallet.Address.BIP32_Ed25519 (XPrv, XPub, XSignature, verify)
import Data.Word.Odd (Word31)
import qualified Haskell.Cardano.Crypto.Wallet as CC
    ( DerivationScheme (DerivationScheme2)
    , XPub
    , deriveXPrv
    , sign
    , toXPub
    , unXPrv
    , unXSignature
    , word32fromWord31High
    , word32fromWord31Low
    , xPrvChangePass
    , xprv
    , xsignature
    )
import Haskell.Data.ByteString (ByteString)
import qualified Haskell.Data.ByteString as BS (empty)
import Prelude hiding (null, subtract)

-- |
-- A passphrase for encrypting a private key.
-- Any string of bytes is a valid passphrase.
type Passphrase = ByteString

-- |
-- Extended private key in memory, encrypted with a passphrase.
--
-- The point of encrypting a private key with a passphrase in memory is
-- that an adversary who has acces to a memory dump of the running program
-- will have a difficult time trying to extract the key,
-- unless they can also get access to the passphrase.
--
-- Note: Operations are slightly slower than on plain private keys,
-- because each operation checks whether the passphrase decrypts
-- the key before operating on it.
data EncryptedXPrv = EncryptedXPrv
    { encryptedXPrv :: XPrv
    , salt :: ByteString
    , saltSigned :: XSignature
    }

-- |
-- Internal.
--
-- Make an 'EncryptedXPrv' from an encrypted 'XPrv'
-- by also signing a passphrase.
mkEncryptedXPrv
    :: Passphrase -> ByteString -> XPrv -> EncryptedXPrv
mkEncryptedXPrv pass saltToSign xprv =
    EncryptedXPrv xprv saltToSign (CC.sign pass xprv saltToSign)

-- |
-- Internal.
-- Decrypt an encrypted 'XPrv' regardless of whether the passphrase
-- is correct.
decryptXPrv :: Passphrase -> XPrv -> XPrv
decryptXPrv pass = CC.xPrvChangePass pass BS.empty

-- |
-- Check whether this 'Passphrase' decrypts the given 'EncryptedXPrv'.
--
-- TODO: Don't decrypt the key here for checking!!
-- Instead, simply check signatures for equality.
check :: Passphrase -> EncryptedXPrv -> Bool
check pass key = verify xpub (salt key) (saltSigned key)
  where
    xpub :: CC.XPub
    xpub = CC.toXPub $ decryptXPrv pass (encryptedXPrv key)

-- |
-- Decrypt the encrypted private key.
--
-- Try not to use this function, as the decrypted key may linger in memory.
-- See note at 'EncryptedXPrv'.
decrypt :: Passphrase -> EncryptedXPrv -> Maybe XPrv
decrypt pass key =
    if check pass key
        then Just (decryptXPrv pass $ encryptedXPrv key)
        else Nothing

-- |
-- Encrypt a plaintext private key
-- using a passphrase and a salt.
encrypt :: Passphrase -> ByteString -> XPrv -> EncryptedXPrv
encrypt pass saltToSign =
    mkEncryptedXPrv pass saltToSign . CC.xPrvChangePass BS.empty pass

-- |
-- Obtain the public key corresponding to a private key.
toXPub :: Passphrase -> EncryptedXPrv -> Maybe XPub
toXPub pass key = CC.toXPub <$> decrypt pass key

-- |
-- Sign a sequence of bytes with a private key.
sign
    :: Passphrase -> EncryptedXPrv -> ByteString -> Maybe XSignature
sign pass key msg =
    if check pass key
        then Just (CC.sign pass (encryptedXPrv key) msg)
        else Nothing

-- |
-- Semi-serialized form of 'EncryptedXPrv'.
--
-- This format can be stored externally.
data EncryptedXPrvBytes = EncryptedXPrvBytes
    { encryptedXPrvBytes
        :: ByteString
    , saltBytes :: ByteString
    , saltSignedBytes :: ByteString
    }

serializeEncryptedXPrv :: EncryptedXPrv -> EncryptedXPrvBytes
serializeEncryptedXPrv e =
    EncryptedXPrvBytes
        (CC.unXPrv (encryptedXPrv e))
        (salt e)
        (CC.unXSignature (saltSigned e))

deserializeEncryptedXPrv
    :: EncryptedXPrvBytes -> Either String EncryptedXPrv
deserializeEncryptedXPrv e =
    do
        f1 <- CC.xprv (encryptedXPrvBytes e)
        f3 <- CC.xsignature (saltSignedBytes e)
        pure (EncryptedXPrv f1 (saltBytes e) f3)

-- |
-- Derive a child extended private key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveEncryptedXPrvSoft
    :: Passphrase -> EncryptedXPrv -> Word31 -> Maybe EncryptedXPrv
deriveEncryptedXPrvSoft pass key ix =
    if check pass key
        then
            Just
                $ mkEncryptedXPrv pass (salt key)
                $ CC.deriveXPrv
                    CC.DerivationScheme2
                    pass
                    (encryptedXPrv key)
                    (CC.word32fromWord31Low ix)
        else Nothing

-- |
-- Derive a hardened child extended private key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveEncryptedXPrvHard
    :: Passphrase -> EncryptedXPrv -> Word31 -> Maybe EncryptedXPrv
deriveEncryptedXPrvHard pass key ix =
    if check pass key
        then
            Just
                $ mkEncryptedXPrv pass (salt key)
                $ CC.deriveXPrv
                    CC.DerivationScheme2
                    pass
                    (encryptedXPrv key)
                    (CC.word32fromWord31High ix)
        else Nothing

-- |
-- Derive an extended private key from a root private key
-- along a path as described in the
-- [BIP-32](https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki#user-content-The_key_tree) standard.
deriveEncryptedXPrvBIP32Path
    :: Passphrase -> EncryptedXPrv -> BIP32Path -> Maybe EncryptedXPrv
deriveEncryptedXPrvBIP32Path pass key Root = Just key
deriveEncryptedXPrvBIP32Path pass key (Segment path Hardened ix) =
    do
        key' <- deriveEncryptedXPrvBIP32Path pass key path
        deriveEncryptedXPrvHard pass key' ix
deriveEncryptedXPrvBIP32Path pass key (Segment path Soft ix) =
    do
        key' <- deriveEncryptedXPrvBIP32Path pass key path
        deriveEncryptedXPrvSoft pass key' ix

-- * Properties

-- $prop-check-decrypt
-- #p:prop-check-decrypt#
--
-- [prop-check-decrypt]:
--     A key matches a passphrase iff it can be decrypted.
--
--     > prop-check-decrypt
--     >   : ∀ (key : EncryptedXPrv) (pass : Passphrase)
--     >   → check pass key
--     >     ≡ isJust (decrypt pass key)

-- $prop-check-mkEncryptedXPrv
-- #p:prop-check-mkEncryptedXPrv#
--
-- [prop-check-mkEncryptedXPrv]:
--     'mkEncryptedXPrv' will generate a key that matches the
--     given passphrase.
--
--     > prop-check-mkEncryptedXPrv
--     >   : ∀ (pass : Passphrase) (salt : ByteString) (xprv : XPrv)
--     >   → check pass (mkEncryptedXPrv pass salt xprv)
--     >     ≡ True

-- $prop-decrypt-encrypt
-- #p:prop-decrypt-encrypt#
--
-- [prop-decrypt-encrypt]:
--     Decrypting an encrypted 'XPrv' will return the original.
--
--     > prop-decrypt-encrypt
--     >   : ∀ (pass : Passphrase) (salt : ByteString) (xprv : XPrv)
--     >   → decrypt pass (encrypt pass salt xprv)
--     >     ≡ Just xprv

-- $prop-decrypt-mkEncryptedXPrv
-- #p:prop-decrypt-mkEncryptedXPrv#
--
-- [prop-decrypt-mkEncryptedXPrv]:
--     Decrypting 'mkEncryptedXPrv' will yield
--     the decrypted key.
--
--     > prop-decrypt-mkEncryptedXPrv
--     >   : ∀ (pass : Passphrase) (salt : ByteString) (xprv : XPrv)
--     >   → decrypt pass (mkEncryptedXPrv pass salt xprv)
--     >     ≡ Just (decryptXPrv pass xprv)

-- $prop-deriveEncryptedXPrvHard-decrypt
-- #p:prop-deriveEncryptedXPrvHard-decrypt#
--
-- [prop-deriveEncryptedXPrvHard-decrypt]:
--     Key derivation of an encrypted private key
--     yields the same result as the plain variant.
--
--     > prop-deriveEncryptedXPrvHard-decrypt
--     >   : ∀ (pass : Passphrase)
--     >       (key : EncryptedXPrv)
--     >       (ix : Word31)
--     >   → (decrypt pass =<< deriveEncryptedXPrvHard pass key ix)
--     >     ≡ ((λ xprv → BIP32_Ed25519.deriveXPrvHard xprv ix) <$> decrypt pass key)

-- $prop-deriveEncryptedXPrvSoft-decrypt
-- #p:prop-deriveEncryptedXPrvSoft-decrypt#
--
-- [prop-deriveEncryptedXPrvSoft-decrypt]:
--     Key derivation of an encrypted private key
--     yields the same result as the plain variant.
--
--     > prop-deriveEncryptedXPrvSoft-decrypt
--     >   : ∀ (pass : Passphrase)
--     >       (key : EncryptedXPrv)
--     >       (ix : Word31)
--     >   → (decrypt pass =<< deriveEncryptedXPrvSoft pass key ix)
--     >     ≡ ((λ xprv → BIP32_Ed25519.deriveXPrvSoft xprv ix) <$> decrypt pass key)

-- $prop-deserialize-serializeEncryptedXPrv
-- #p:prop-deserialize-serializeEncryptedXPrv#
--
-- [prop-deserialize-serializeEncryptedXPrv]:
--     'deserializeEncryptedXPrv' always deserializes 'serializeEncryptedXPrv'.
--
--     > prop-deserialize-serializeEncryptedXPrv
--     >   : ∀ (x : EncryptedXPrv)
--     >   → deserializeEncryptedXPrv (serializeEncryptedXPrv x)
--     >     ≡ Right x

-- $prop-sign-decrypt
-- #p:prop-sign-decrypt#
--
-- [prop-sign-decrypt]:
--     Signing with an encrypted key is the same as signing with
--     the unencrypted key.
--
--     > prop-sign-decrypt
--     >   : ∀ (key : EncryptedXPrv) (pass : Passphrase) (msg : ByteString)
--     >   → sign pass key msg
--     >     ≡ ((λ xprv → BIP32_Ed25519.sign xprv msg) <$> decrypt pass key)

-- $prop-toXPub-decrypt
-- #p:prop-toXPub-decrypt#
--
-- [prop-toXPub-decrypt]:
--     The extended public key can be obtained by first decrypting the key
--     and then taking extended public key.
--
--     > prop-toXPub-decrypt
--     >   : ∀ (key : EncryptedXPrv) (pass : Passphrase)
--     >   → toXPub pass key
--     >     ≡ (BIP32_Ed25519.toXPub <$> decrypt pass key)
