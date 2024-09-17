{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Wallet.Deposit.Pure.RollbackWindow where

if' :: Bool -> a -> a -> a
if' True thn els = thn
if' False thn els = els

data RollbackWindow time = RollbackWindowC
    { finality :: time
    , tip :: time
    }

member :: Ord time => time -> RollbackWindow time -> Bool
member time w = finality w <= time && time <= tip w

singleton :: Ord time => time -> RollbackWindow time
singleton time = RollbackWindowC time time

rollForward
    :: Ord time
    => time
    -> RollbackWindow time
    -> Maybe (RollbackWindow time)
rollForward newTip w =
    if tip w < newTip
        then Just (RollbackWindowC (finality w) newTip)
        else Nothing

data MaybeRollback a
    = Past
    | Present a
    | Future

rollBackward
    :: Ord time
    => time
    -> RollbackWindow time
    -> MaybeRollback (RollbackWindow time)
rollBackward newTip w =
    if tip w < newTip
        then Future
        else
            if finality w <= newTip
                then Present (RollbackWindowC (finality w) newTip)
                else Past

prune
    :: Ord time
    => time
    -> RollbackWindow time
    -> Maybe (RollbackWindow time)
prune newFinality w =
    if member newFinality w
        then Just (RollbackWindowC newFinality (tip w))
        else Nothing

intersect
    :: forall time
     . Ord time
    => RollbackWindow time
    -> RollbackWindow time
    -> Maybe (RollbackWindow time)
intersect w1 w2 =
    if' (fin3 <= tip3) (Just (RollbackWindowC fin3 tip3)) Nothing
  where
    fin3 :: time
    fin3 = max (finality w1) (finality w2)
    tip3 :: time
    tip3 = min (tip w1) (tip w2)
