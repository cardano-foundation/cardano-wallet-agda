{-# OPTIONS --erasure #-}
module Cardano.Wallet.Deposit.Read.Value where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Haskell.Data.Maybe using
    ( fromMaybe
    )

import Haskell.Data.ByteString as BS
import Haskell.Data.Map as Map

{-----------------------------------------------------------------------------
    Coin
------------------------------------------------------------------------------}
Coin = Nat

monusCoin : Coin → Coin → Coin
monusCoin a b = case a < b of λ
  { False {{eq}} →
    _-_ a b {{subst IsFalse (sym eq) IsFalse.itsFalse}}
  ; True → 0
  }

{-# COMPILE AGDA2HS Coin #-}
{-# COMPILE AGDA2HS monusCoin #-}

{-----------------------------------------------------------------------------
    Assets
------------------------------------------------------------------------------}
AssetName  = BS.ByteString   -- max 32 bytes
ScriptHash = BS.ByteString   -- blake2b-224
PolicyID   = ScriptHash

{-# COMPILE AGDA2HS AssetName #-}
{-# COMPILE AGDA2HS ScriptHash #-}
{-# COMPILE AGDA2HS PolicyID #-}

Quantity = Integer

{-# COMPILE AGDA2HS Quantity #-}

data AssetID : Set where
    AdaID : AssetID
    Asset : PolicyID → AssetName → AssetID

{-# COMPILE AGDA2HS AssetID #-}

instance
  iEqAssetID : Eq AssetID
  iEqAssetID ._==_ AdaID AdaID = True
  iEqAssetID ._==_ (Asset a1 b1) (Asset a2 b2) = a1 == a2 && b1 == b2
  iEqAssetID ._==_ _ _ = False

postulate instance
  iOrdAssetID : Ord AssetID

{-# COMPILE AGDA2HS iEqAssetID derive #-}
{-# COMPILE AGDA2HS iOrdAssetID derive #-}

{-----------------------------------------------------------------------------
    Value
------------------------------------------------------------------------------}
record Value : Set where
  field
    ada    : Coin
    assets : Map.Map (PolicyID × AssetName) Quantity

open Value public

{-# COMPILE AGDA2HS Value #-}

instance
  iEqValue : Eq Value
  iEqValue ._==_ v1 v2 =
    ada v1 == ada v2 && assets v1 == assets v2

{-# COMPILE AGDA2HS iEqValue derive #-}

valueFromList : Coin → List (PolicyID × AssetName × Quantity) → Value
valueFromList coin xs = record
    { ada = coin
    ; assets = Map.fromList (map (λ { (p , n , q) → ((p , n) , q) }) xs)
    }

{-# COMPILE AGDA2HS valueFromList #-}

injectCoin : Coin → Value
injectCoin coin = record { ada = coin; assets = Map.empty }

{-# COMPILE AGDA2HS injectCoin #-}

getCoin : Value → Coin
getCoin v = ada v

{-# COMPILE AGDA2HS getCoin #-}

largerOrEqual : Value → Value → Bool
largerOrEqual a b =
    ada a >= ada b
    && Map.null (Map.filterWithKey isSmallerThanB (assets a))
  where
    isSmallerThanB : PolicyID × AssetName → Quantity → Bool
    isSmallerThanB key qa = qa < fromMaybe 0 (Map.lookup key (assets b))

{-# COMPILE AGDA2HS largerOrEqual #-}

instance
  iSemigroupValue : Semigroup Value
  _<>_ {{iSemigroupValue}} a b =
    record
      { ada = ada a + ada b
      ; assets = Map.unionWith (_+_) (assets a) (assets b)
      }

  iMonoidValue : Monoid Value
  iMonoidValue =
    record {DefaultMonoid (λ where
      .DefaultMonoid.mempty → record { ada = 0; assets = Map.empty }
    )}

{-# COMPILE AGDA2HS iSemigroupValue #-}
{-# COMPILE AGDA2HS iMonoidValue #-}

monus : Value → Value → Value
monus a b = record
  { ada = monusCoin (ada a) (ada b)
  ; assets = Map.unionWith minus (assets a) (assets b)
  }
  where
    minus : Quantity → Quantity → Quantity
    minus x y = x - y

{-# COMPILE AGDA2HS monus #-}

{-----------------------------------------------------------------------------
    Value properties
------------------------------------------------------------------------------}

prop-coin-inject
    : ∀ (c : Coin)
    → getCoin (injectCoin c) ≡ c
prop-coin-inject coin = refl
