{-# LANGUAGE StandaloneDeriving #-}

module Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO
    ( DeltaUTxO (..)
    , null
      -- $prop-null→empty
    , empty
      -- $prop-apply-empty
    , apply
    , fits
      -- $prop-fits
    , excludingD
      -- $prop-excluding-excludingD
      -- $prop-apply-excludingD
      -- $prop-fits-excludingD
    , receiveD
      -- $prop-union-receiveD
      -- $prop-apply-receiveD
    , append
      -- $prop-apply-append
    , appends
    )
where

import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO, dom)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
    ( disjoint
    , empty
    , excluding
    , excludingS
    , null
    , union
    )
import Cardano.Wallet.Read.Tx (TxIn)
import Data.Set (Set)
import qualified Haskell.Data.Map.Def as Map (empty)
import qualified Haskell.Data.Set as Set
    ( empty
    , intersection
    , isSubsetOf
    , null
    , union
    )
import Prelude hiding (null, subtract)

-- |
-- Representation of a change (delta) to a 'UTxO'.
--
-- The delta records inputs that are excluded, and outputs that are added.
data DeltaUTxO = DeltaUTxO {excluded :: Set TxIn, received :: UTxO}

deriving instance Show DeltaUTxO

-- |
-- Test efficiently whether the change does nothing.
null :: DeltaUTxO -> Bool
null du = Set.null (excluded du) && UTxO.null (received du)

-- |
-- The empty change does nothing.
empty :: DeltaUTxO
empty = DeltaUTxO Set.empty Map.empty

-- |
-- Apply a change to a 'UTxO'.
apply :: DeltaUTxO -> UTxO -> UTxO
apply du utxo =
    UTxO.union (received du) (UTxO.excluding utxo (excluded du))

-- |
-- Test whether a 'DeltaUTxO' fits onto a 'UTxO',
-- that is whether it removes only existing 'TxIn',
-- and adds only new 'Cardano.Wallet.Read.Tx.TxOut'.
fits :: DeltaUTxO -> UTxO -> Bool
fits du u =
    Set.isSubsetOf (excluded du) (dom u)
        && UTxO.disjoint (received du) u

-- |
-- Variant of 'excluding' that also returns a delta.
excludingD :: UTxO -> Set TxIn -> (DeltaUTxO, UTxO)
excludingD utxo txins = (du, UTxO.excluding utxo txins)
  where
    du :: DeltaUTxO
    du = DeltaUTxO (Set.intersection txins (dom utxo)) UTxO.empty

-- |
-- Variant of 'union' that also returns a delta.
-- The first argument is the 'UTxO' on which the delta acts.
--
-- > receiveD old new
receiveD :: UTxO -> UTxO -> (DeltaUTxO, UTxO)
receiveD old new = (du, UTxO.union new old)
  where
    du :: DeltaUTxO
    du = DeltaUTxO Set.empty new

-- |
-- Combine two deltas: Apply @x@ /after/ applying @y@.
-- Drops inputs that were created by @y@, but removed again by @x@
append :: DeltaUTxO -> DeltaUTxO -> DeltaUTxO
append x y =
    DeltaUTxO
        (Set.union excluded'x (excluded y))
        (UTxO.union (received x) received'y)
  where
    excluded'x :: Set TxIn
    excluded'x = UTxO.excludingS (excluded x) (received y)
    received'y :: UTxO
    received'y = UTxO.excluding (received y) (excluded x)

-- |
-- Combine a sequence of 'DeltaUTxO' using `append`
appends :: [DeltaUTxO] -> DeltaUTxO
appends = foldr append empty

-- * Properties

-- $prop-apply-append
-- #p:prop-apply-append#
--
-- [prop-apply-append]:
--     Defining property of 'append':
--     Applying the combination of two deltas is the same as
--     applying each delta in turn (right-to-left),
--     assuming that the delta and the utxo have disjoint 'TxIn's.
--
--     > @0 prop-apply-append
--     >   : ∀ (x y : DeltaUTxO) (utxo : UTxO)
--     >   → UTxO.disjoint (received y) utxo ≡ True
--     >   → apply (append x y) utxo ≡ apply x (apply y utxo)

-- $prop-apply-empty
-- #p:prop-apply-empty#
--
-- [prop-apply-empty]:
--
--     Applying the 'empty' delta does nothing.
--
--     > @0 prop-apply-empty
--     >   : ∀ (utxo : UTxO)
--     >   → apply empty utxo ≡ utxo

-- $prop-apply-excludingD
-- #p:prop-apply-excludingD#
--
-- [prop-apply-excludingD]:
--     Applying the 'DeltaUTxO' returned by 'excludingD'
--     to the argument 'UTxO' yields the result 'UTxO'.
--
--     > @0 prop-apply-excludingD
--     >   : ∀ {txins : Set.ℙ TxIn} {u0 : UTxO}
--     >   → let (du , u1) = excludingD u0 txins
--     >     in  apply du u0 ≡ u1

-- $prop-apply-receiveD
-- #p:prop-apply-receiveD#
--
-- [prop-apply-receiveD]:
--     Applying the 'DeltaUTxO' returned by 'receiveD'
--     to the argument 'UTxO' yields the result 'UTxO'.
--
--     > @0 prop-apply-receiveD
--     >   : ∀ {ua : UTxO} {u0 : UTxO}
--     >   → let (du , u1) = receiveD u0 ua
--     >     in  apply du u0 ≡ u1

-- $prop-excluding-excludingD
-- #p:prop-excluding-excludingD#
--
-- [prop-excluding-excludingD]:
--     The 'UTxO' returned by 'excludingD' is the same as 'excluding'.
--
--     > prop-excluding-excludingD
--     >   : ∀ {txins : Set.ℙ TxIn} {u0 : UTxO}
--     >   → let (du , u1) = excludingD u0 txins
--     >     in  u1 ≡ UTxO.excluding u0 txins

-- $prop-fits
-- #p:prop-fits#
--
-- [prop-fits]:
--
--     Definition of 'fits'.
--
--     > prop-fits
--     >   : ∀ (du : DeltaUTxO) (u : UTxO)
--     >   → fits du u
--     >     ≡ ( Set.isSubsetOf (excluded du) (dom u)
--     >         && UTxO.disjoint (received du) u
--     >       )

-- $prop-fits-excludingD
-- #p:prop-fits-excludingD#
--
-- [prop-fits-excludingD]:
--
--     The 'DeltaUTxO' returned by 'excludingD' 'fits' the 'UTxO'.
--
--     > prop-fits-excludingD
--     >   : ∀ {txins : Set.ℙ TxIn} {u0 : UTxO}
--     >   → let (du , u1) = excludingD u0 txins
--     >     in  fits du u0 ≡ True

-- $prop-null→empty
-- #p:prop-null→empty#
--
-- [prop-null→empty]:
--
--     'null' tests whether the delta is 'empty'.
--
--     > prop-null→empty
--     >   : ∀ (du : DeltaUTxO)
--     >   → null du ≡ True
--     >   → du ≡ empty

-- $prop-union-receiveD
-- #p:prop-union-receiveD#
--
-- [prop-union-receiveD]:
--     The 'UTxO' returned by 'receiveD' is the same as 'union'.
--
--     > prop-union-receiveD
--     >   : ∀ {ua : UTxO} {u0 : UTxO}
--     >   → let (du , u1) = receiveD u0 ua
--     >     in  u1 ≡ UTxO.union ua u0
