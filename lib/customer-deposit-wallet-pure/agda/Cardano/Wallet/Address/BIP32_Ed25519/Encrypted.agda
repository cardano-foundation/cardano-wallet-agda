{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.BIP32_Ed25519.Encrypted
  {-|
  -- * Types
  ; Passphrase
  ; EncryptedXPrv
    ; check
    ; decrypt
      ; prop-check-decrypt
    ; encrypt
      ; prop-decrypt-encrypt
    ; toXPub
      ; prop-toXPub-decrypt
    ; sign
      ; prop-sign-decrypt

  -- * Serialization
  ; EncryptedXPrvBytes (..)
    ; serializeEncryptedXPrv
    ; deserializeEncryptedXPrv
      ; prop-deserialize-serializeEncryptedXPrv

  -- * Key derivation
  ; deriveEncryptedXPrvSoft
    ; prop-deriveEncryptedXPrvSoft-decrypt
  ; deriveEncryptedXPrvHard
    ; prop-deriveEncryptedXPrvHard-decrypt
  ; deriveEncryptedXPrvBIP32Path
  -} where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Cardano.Wallet.Address.BIP32_Ed25519 using
  ( XPrv
  ; XPub
  ; XSignature
  ; verify
    ; prop-verify-sign
  )
open import Cardano.Wallet.Address.BIP32 using
  ( BIP32Path
  ; DerivationType
  )
open DerivationType
open import Haskell.Data.ByteString using
  ( ByteString
  )
open import Haskell.Data.Maybe using
  ( isJust
  )
open import Haskell.Data.Word using
  ( Word32
  )
open import Haskell.Data.Word.Odd using
  ( Word31
  )

import Cardano.Wallet.Address.BIP32_Ed25519 as BIP32_Ed25519
import Haskell.Cardano.Crypto.Wallet.Extra as CC
import Haskell.Data.ByteString as BS

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import qualified Cardano.Crypto.Wallet.Extra as CC
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
#-}
{-----------------------------------------------------------------------------
    Types
------------------------------------------------------------------------------}
-- | A passphrase for encrypting a private key.
-- Any string of bytes is a valid passphrase.
Passphrase : Set
Passphrase = ByteString

{-# COMPILE AGDA2HS Passphrase #-}

-- | Extended private key in memory, encrypted with a passphrase.
--
-- The point of encrypting a private key with a passphrase in memory is 
-- that an adversary who has acces to a memory dump of the running program
-- will have a difficult time trying to extract the key,
-- unless they can also get access to the passphrase.
--
-- Note: Operations are slightly slower than on plain private keys,
-- because each operation checks whether the passphrase decrypts
-- the key before operating on it.
record EncryptedXPrv : Set where
  field
    encryptedXPrv : XPrv
    salt : ByteString
    saltSigned : XSignature

open EncryptedXPrv public

{-# COMPILE AGDA2HS EncryptedXPrv #-}

{-----------------------------------------------------------------------------
    Encrypted private keys
------------------------------------------------------------------------------}
-- | Internal.
--
-- Make an 'EncryptedXPrv' from an encrypted 'XPrv'
-- by also signing a passphrase.
mkEncryptedXPrv : Passphrase → ByteString → XPrv → EncryptedXPrv
mkEncryptedXPrv pass saltToSign xprv = record
  { encryptedXPrv = xprv
  ; salt = saltToSign
  ; saltSigned = CC.sign pass xprv saltToSign
  }

{-# COMPILE AGDA2HS mkEncryptedXPrv #-}

-- | Internal.
-- Decrypt an encrypted 'XPrv' regardless of whether the passphrase
-- is correct.
decryptXPrv : Passphrase → XPrv → XPrv
decryptXPrv pass = CC.xPrvChangePass pass BS.empty

-- | Check whether this 'Passphrase' decrypts the given 'EncryptedXPrv'.
--
-- TODO: Don't decrypt the key here for checking!!
-- Instead, simply check signatures for equality.
--
check : Passphrase → EncryptedXPrv → Bool
check pass key = verify xpub (salt key) (saltSigned key)
  where
    xpub = CC.toXPub $ decryptXPrv pass (encryptedXPrv key)

-- | Decrypt the encrypted private key.
--
-- Try not to use this function, as the decrypted key may linger in memory.
-- See note at 'EncryptedXPrv'.
decrypt : Passphrase → EncryptedXPrv → Maybe XPrv
decrypt pass key =
  if check pass key
  then Just (decryptXPrv pass $ encryptedXPrv key)
  else Nothing

-- | Encrypt a plaintext private key
-- using a passphrase and a salt.
encrypt : Passphrase → ByteString → XPrv → EncryptedXPrv
encrypt pass saltToSign =
  mkEncryptedXPrv pass saltToSign ∘ CC.xPrvChangePass BS.empty pass

-- | Obtain the public key corresponding to a private key.
--
toXPub : Passphrase → EncryptedXPrv → Maybe XPub
toXPub pass key = CC.toXPub <$> decrypt pass key

-- | Sign a sequence of bytes with a private key.
sign : Passphrase → EncryptedXPrv → ByteString → Maybe XSignature
sign pass key msg =
    if check pass key
    then Just (CC.sign pass (encryptedXPrv key) msg)
    else Nothing

{-# COMPILE AGDA2HS check #-}
{-# COMPILE AGDA2HS decryptXPrv #-}
{-# COMPILE AGDA2HS decrypt #-}
{-# COMPILE AGDA2HS encrypt #-}
{-# COMPILE AGDA2HS toXPub #-}
{-# COMPILE AGDA2HS sign #-}

{-----------------------------------------------------------------------------
    Properties
    Internal
------------------------------------------------------------------------------}
-- | 'mkEncryptedXPrv' will generate a key that matches the
-- given passphrase.
prop-check-mkEncryptedXPrv
  : ∀ (pass : Passphrase) (salt : ByteString) (xprv : XPrv)
  → check pass (mkEncryptedXPrv pass salt xprv)
    ≡ True
--
prop-check-mkEncryptedXPrv pass salt xprv
  rewrite sym (CC.prop-sign-xPrvChangePass pass BS.empty xprv salt)
  = prop-verify-sign (decryptXPrv pass xprv) salt

-- | Decrypting 'mkEncryptedXPrv' will yield
-- the decrypted key.
prop-decrypt-mkEncryptedXPrv
  : ∀ (pass : Passphrase) (salt : ByteString) (xprv : XPrv)
  → decrypt pass (mkEncryptedXPrv pass salt xprv)
    ≡ Just (decryptXPrv pass xprv)
--
prop-decrypt-mkEncryptedXPrv pass salt xprv
  rewrite prop-check-mkEncryptedXPrv pass salt xprv
  = refl

{-----------------------------------------------------------------------------
    Properties
    Exported
------------------------------------------------------------------------------}
-- | A key matches a passphrase iff it can be decrypted.
prop-check-decrypt
  : ∀ (key : EncryptedXPrv) (pass : Passphrase)
  → check pass key
    ≡ isJust (decrypt pass key)
--
prop-check-decrypt key pass
  with check pass key
... | True = refl
... | False = refl

-- | Decrypting an encrypted 'XPrv' will return the original.
prop-decrypt-encrypt
  : ∀ (pass : Passphrase) (salt : ByteString) (xprv : XPrv)
  → decrypt pass (encrypt pass salt xprv)
    ≡ Just xprv
--
prop-decrypt-encrypt pass salt xprv
  rewrite prop-decrypt-mkEncryptedXPrv pass salt (CC.xPrvChangePass BS.empty pass xprv)
  rewrite CC.prop-xPrvChangePass-trans pass BS.empty pass xprv
  rewrite CC.prop-xPrvChangePass-refl pass xprv
  = refl

-- | The extended public key can be obtained by first decrypting the key
-- and then taking extended public key.
prop-toXPub-decrypt
  : ∀ (key : EncryptedXPrv) (pass : Passphrase)
  → toXPub pass key
    ≡ (BIP32_Ed25519.toXPub <$> decrypt pass key)
--
prop-toXPub-decrypt key pass = refl

-- | Signing with an encrypted key is the same as signing with
-- the unencrypted key.
prop-sign-decrypt
  : ∀ (key : EncryptedXPrv) (pass : Passphrase) (msg : ByteString)
  → sign pass key msg
    ≡ ((λ xprv → BIP32_Ed25519.sign xprv msg) <$> decrypt pass key)
--
prop-sign-decrypt key pass msg
  with check pass key
... | True = cong Just (sym (CC.prop-sign-xPrvChangePass pass BS.empty (encryptedXPrv key) msg))
... | False = refl

{-----------------------------------------------------------------------------
    Serialization
------------------------------------------------------------------------------}
-- | Semi-serialized form of 'EncryptedXPrv'.
--
-- This format can be stored externally.
record EncryptedXPrvBytes : Set where
  field
    encryptedXPrvBytes : ByteString
    saltBytes : ByteString
    saltSignedBytes : ByteString

open EncryptedXPrvBytes public
{-# COMPILE AGDA2HS EncryptedXPrvBytes #-}

serializeEncryptedXPrv : EncryptedXPrv → EncryptedXPrvBytes
serializeEncryptedXPrv e = record
  { encryptedXPrvBytes = CC.unXPrv (encryptedXPrv e)
  ; saltBytes = salt e
  ; saltSignedBytes = CC.unXSignature (saltSigned e)
  }

deserializeEncryptedXPrv : EncryptedXPrvBytes → Either String EncryptedXPrv
deserializeEncryptedXPrv e = do
  f1 ← CC.xprv (encryptedXPrvBytes e)
  f3 ← CC.xsignature (saltSignedBytes e)
  pure record
    { encryptedXPrv = f1
    ; salt = saltBytes e
    ; saltSigned = f3
    }

{-# COMPILE AGDA2HS serializeEncryptedXPrv #-}
{-# COMPILE AGDA2HS deserializeEncryptedXPrv #-}

{-----------------------------------------------------------------------------
    Properties
    Serialization
------------------------------------------------------------------------------}
-- | 'deserializeEncryptedXPrv' always deserializes 'serializeEncryptedXPrv'.
prop-deserialize-serializeEncryptedXPrv
  : ∀ (x : EncryptedXPrv)
  → deserializeEncryptedXPrv (serializeEncryptedXPrv x)
    ≡ Right x
--
prop-deserialize-serializeEncryptedXPrv x
  rewrite CC.prop-xprv-unXPrv (encryptedXPrv x)
  rewrite CC.prop-xsignature-unXSignature (saltSigned x)
  = refl

{-----------------------------------------------------------------------------
    Key derivation
------------------------------------------------------------------------------}
-- | Derive a child extended private key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveEncryptedXPrvSoft
  : Passphrase → EncryptedXPrv → Word31 → Maybe EncryptedXPrv
deriveEncryptedXPrvSoft pass key ix =
  if check pass key
  then Just
    $ mkEncryptedXPrv pass (salt key)
    $ CC.deriveXPrv
        CC.DerivationScheme2
        pass
        (encryptedXPrv key)
        (CC.word32fromWord31Low ix)
  else Nothing

-- | Derive a hardened child extended private key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveEncryptedXPrvHard
  : Passphrase → EncryptedXPrv → Word31 → Maybe EncryptedXPrv
deriveEncryptedXPrvHard pass key ix =
  if check pass key
  then Just
    $ mkEncryptedXPrv pass (salt key)
    $ CC.deriveXPrv
        CC.DerivationScheme2
        pass
        (encryptedXPrv key)
        (CC.word32fromWord31High ix)
  else Nothing

-- | Derive an extended private key from a root private key
-- along a path as described in the
-- [BIP-32](https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki#user-content-The_key_tree) standard.
--
deriveEncryptedXPrvBIP32Path
  : Passphrase → EncryptedXPrv → BIP32Path → Maybe EncryptedXPrv
deriveEncryptedXPrvBIP32Path pass key BIP32Path.Root = Just key
deriveEncryptedXPrvBIP32Path pass key (BIP32Path.Segment path Hardened ix) =
  deriveEncryptedXPrvBIP32Path pass key path
    >>= λ key' → deriveEncryptedXPrvHard pass key' ix
deriveEncryptedXPrvBIP32Path pass key (BIP32Path.Segment path Soft ix) =
  deriveEncryptedXPrvBIP32Path pass key path
    >>= λ key' → deriveEncryptedXPrvSoft pass key' ix

{-# COMPILE AGDA2HS deriveEncryptedXPrvSoft #-}
{-# COMPILE AGDA2HS deriveEncryptedXPrvHard #-}
{-# COMPILE AGDA2HS deriveEncryptedXPrvBIP32Path #-}

{-----------------------------------------------------------------------------
    Properties
    Key derivation
------------------------------------------------------------------------------}
-- | Key derivation of an encrypted private key
-- yields the same result as the plain variant.
prop-deriveEncryptedXPrvSoft-decrypt
  : ∀ (pass : Passphrase)
      (key : EncryptedXPrv)
      (ix : Word31)
  → (decrypt pass =<< deriveEncryptedXPrvSoft pass key ix)
    ≡ ((λ xprv → BIP32_Ed25519.deriveXPrvSoft xprv ix) <$> decrypt pass key)
--
prop-deriveEncryptedXPrvSoft-decrypt pass key ix31 = lem
  where
    ix = CC.word32fromWord31Low ix31
    parentXPrv = encryptedXPrv key
    childXPrv =
      CC.deriveXPrv
        CC.DerivationScheme2
        pass
        (encryptedXPrv key)
        ix

    lem
      : (decrypt pass =<< deriveEncryptedXPrvSoft pass key ix31)
      ≡ ((λ xprv → BIP32_Ed25519.deriveXPrvSoft xprv ix31) <$> decrypt pass key)
    lem
      with check pass key
    ... | False = refl
    ... | True
        rewrite prop-decrypt-mkEncryptedXPrv pass (salt key) childXPrv
        rewrite sym (CC.prop-deriveXPrv-xPrvChangePass pass BS.empty parentXPrv ix)
        = refl

-- | Key derivation of an encrypted private key
-- yields the same result as the plain variant.
prop-deriveEncryptedXPrvHard-decrypt
  : ∀ (pass : Passphrase)
      (key : EncryptedXPrv)
      (ix : Word31)
  → (decrypt pass =<< deriveEncryptedXPrvHard pass key ix)
    ≡ ((λ xprv → BIP32_Ed25519.deriveXPrvHard xprv ix) <$> decrypt pass key)
--
prop-deriveEncryptedXPrvHard-decrypt pass key ix31 = lem
  where
    ix = CC.word32fromWord31High ix31
    parentXPrv = encryptedXPrv key
    childXPrv =
      CC.deriveXPrv
        CC.DerivationScheme2
        pass
        (encryptedXPrv key)
        ix

    lem
      : (decrypt pass =<< deriveEncryptedXPrvHard pass key ix31)
      ≡ ((λ xprv → BIP32_Ed25519.deriveXPrvHard xprv ix31) <$> decrypt pass key)
    lem
      with check pass key
    ... | False = refl
    ... | True
        rewrite prop-decrypt-mkEncryptedXPrv pass (salt key) childXPrv
        rewrite sym (CC.prop-deriveXPrv-xPrvChangePass pass BS.empty parentXPrv ix)
        = refl
