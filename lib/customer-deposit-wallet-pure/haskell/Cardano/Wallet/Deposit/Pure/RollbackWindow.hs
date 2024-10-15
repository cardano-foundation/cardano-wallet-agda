{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Wallet.Deposit.Pure.RollbackWindow where

import Prelude hiding (null, subtract)

-- |
-- (Internal function, exported for technical reasons.)
if' :: Bool -> a -> a -> a
if' True thn els = thn
if' False thn els = els

-- |
-- A 'RollbackWindow' is a time interval.
-- This time interval is used to keep track of data / transactions
-- that are not final and may still be rolled back.
-- The 'tip' is the higher end of the interval,
-- representing the latest state of the data.
-- The 'finality' is the lower end of the interval,
-- until which rollbacks are supported.
data RollbackWindow time = RollbackWindowC
    { finality :: time
    , tip :: time
    }

-- |
-- Test whether a given time is within a 'RollbackWindow'.
member :: Ord time => time -> RollbackWindow time -> Bool
member time w = finality w <= time && time <= tip w

-- |
-- Interval containing a single point
singleton :: Ord time => time -> RollbackWindow time
singleton time = RollbackWindowC time time

-- |
-- Move forward the tip of the 'RollbackWindow'.
-- Return 'Nothing' if the new tip would not actually be moving forward.
rollForward
    :: Ord time
    => time
    -> RollbackWindow time
    -> Maybe (RollbackWindow time)
rollForward newTip w =
    if tip w < newTip
        then Just (RollbackWindowC (finality w) newTip)
        else Nothing

-- |
-- Potential results of a 'rollBackwards'.
data MaybeRollback a
    = Past
    | Present a
    | Future

-- |
-- Roll back the tip of the 'RollbackWindow' to a point within the window.
-- Return different error conditions if the target is outside the window.
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

-- |
-- Move forward the finality of the 'RollbackWindow'.
-- Return 'Nothing' if the finality is not moving forward, or too far.
prune
    :: Ord time
    => time
    -> RollbackWindow time
    -> Maybe (RollbackWindow time)
prune newFinality w =
    if finality w <= newFinality && newFinality <= tip w
        then Just (RollbackWindowC newFinality (tip w))
        else Nothing

-- | Intersection of two 'RollbackWindow'.
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

-- * Properties

-- $prop-finality-member
-- #prop-finality-member#
--
-- [prop-finality-member]:
--
--     The 'finality' is always a 'member' of a 'RollbackWindow'.
--
--     @
--     @0 prop-finality-member
--       : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
--           (w : RollbackWindow time)
--       → member (finality w) w ≡ True
--     @

-- $prop-member-intersect
-- #prop-member-intersect#
--
-- [prop-member-intersect]:
--
--     A time @t@ is a 'member' of an intersection
--     if it is a member of both 'RollbackWindow's.
--
--     @
--     @0 prop-member-intersect
--       : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
--           (w1 w2 w3 : RollbackWindow time)
--           (t : time)
--       → intersect w1 w2 ≡ Just w3
--       → member t w3 ≡ (member t w1 && member t w2)
--     @

-- $prop-tip-member
-- #prop-tip-member#
--
-- [prop-tip-member]:
--
--     The 'tip' is always a 'member' of a 'RollbackWindow'.
--
--     @
--     @0 prop-tip-member
--       : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
--           (w : RollbackWindow time)
--       → member (tip w) w ≡ True
--     @
