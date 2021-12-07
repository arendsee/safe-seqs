{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

-- required to allow `forall` syntax
{-# LANGUAGE RankNTypes #-}

-- required since Hindley-Milner ignores everything to the left of the context arrow 
{-# LANGUAGE AllowAmbiguousTypes #-}

-- required for type applications such as `map @Int`
{-# LANGUAGE TypeApplications #-}

-- required to use type variables within a function declaration scope (such as when applying types)
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE GADTs #-}

{-# LANGUAGE FlexibleInstances #-}

-- required for polymorphic constraints (in All type family)
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE RankNTypes #-}

-- allow kind signatures
{-# LANGUAGE StandaloneKindSignatures #-}

-- allow kind variables in kind signatures
{-# LANGUAGE PolyKinds #-}

{-# LANGUAGE FlexibleContexts #-}

module TypeFoo
    ( HList(..)
    , Take(..)
    , IteratePlus5(..)
    , Depth(..)
    , Foo(..)
    , Number(..)
    , Viewable(..)
    , showType
    , hLength
    , hetHead
    , releaseString
    , label
    , Ord
    ) where

import GHC.TypeLits
import Data.Typeable hiding (Proxy)

import Data.Kind (Constraint, Type)

data Proxy a = Proxy

or :: Bool -> Bool -> Bool
or True _ = True
or _ y = y

-- DEFINITION: a higher-kinded type is any type that uses kinds other than
-- TYPE, ARROW, and CONSTRAINT.

type Or :: Bool -> Bool -> Bool
type family Or x y where
  Or True y = True -- there are no type level holes?
  Or x y = y

type Not :: Bool -> Bool
type family Not x where
  Not True = False -- True or 'True?
  Not False = True

showType :: forall a . Typeable a => String
showType = show . typeRep $ Proxy @a

type HList :: [Type] -> Type
data HList (ts :: [Type]) where
  -- using explicit type equality
  -- we could alternatively just write `HList '[]` without the explicit constraint
  HNil :: (ts ~ '[]) => HList ts
  (:#) :: t -> HList ts -> HList (t : ts)
infixr 5 :#

hLength :: HList ts -> Int
hLength HNil = 0
hLength (_ :# xs) = 1 + hLength xs


hHead :: HList (t : ts) -> t
hHead (t :# _) = t

type Append :: [Type] -> [Type] -> [Type]
type family Append xs ys where
  Append '[] ys = ys
  Append (x : xs) ys = x : Append xs ys

hAppend :: HList xs -> HList ys -> HList (Append xs ys)
hAppend HNil ys = ys
hAppend (x :# xs) ys = x :# hAppend xs ys


instance Eq (HList '[]) where
  (==) _ _ = True
instance (Eq t, Eq (HList ts)) => Eq (HList (t : ts)) where
  (==) (x :# xs) (y :# ys) = x == y && xs == ys


instance Ord (HList '[]) where
  compare _ _ = EQ
instance (Ord t, Ord (HList ts)) => Ord (HList (t : ts)) where
  compare (x :# xs) (y :# ys) = case compare x y of
    EQ -> compare xs ys
    x -> x

type family Length (ts :: [Type]) :: Nat where
  Length '[] = 0
  Length (_ : ts) = 0 + Length ts

type family LargerThan (n :: Nat) (ts :: [Type]) :: Bool where
  LargerThan i (t : ts) = LargerThan (i - 1) ts
  LargerThan 0 '[] = False
  LargerThan i '[] = True

-- define a list of length (a, b) inclusive
type family ListBound (a :: Nat) (b :: Nat) (ts :: [Type]) :: Constraint where
  ListBound a b ts = (a <= Length ts, Length ts <= b)

type If :: Bool -> a -> a -> a
type family If cond x y where
  If True x _ = x
  If False _ y = y

-- given two nats, return the smaller one
type Min :: Nat -> Nat -> Nat -- requires -XStandaloneKindSignatures
type family Min (x :: Nat) (y :: Nat) :: Nat where -- type family header
  Min x y = If (x <=? y) x y
-- and the larger
type family Max (x :: Nat) (y :: Nat) :: Nat where
  Max x y = If (x <=? y) y x

type Depth :: a -> Nat
type family Depth a where
  -- yes, we can pattern match over a universal type, this would NOT be legal for terms
  Depth '[] = 1
  Depth '[x] = 1 + Depth x
  Depth (x : xs) = Max (1 + Depth x) (Depth xs)
  Depth (HList xs) = Depth xs
  Depth a = 0 -- and type that we can't (or don't) recurse into is at level 0

type And :: Bool -> Bool -> Bool
type family And x y where
  And True True = True
  And _ _ = False

-- is the HList rose tree balanced?
type IsBalanced :: a -> Bool
type family IsBalanced x where
  IsBalanced '[] = True
  IsBalanced '[x] = IsBalanced x
  IsBalanced (x : xs)
    =     (IsBalanced x)
    `And` (IsBalanced xs)
    `And` (1 + Depth x <=? Depth xs)
    `And` (Depth xs <=? 1 + Depth x)
  IsBalanced (HList xs) = IsBalanced xs
  IsBalanced x = True -- leaf

-- does a type contain a particular term somewhere nested inside it?
type HasTerm :: a -> b -> Bool
type family HasTerm a b where
  -- non-linear pattern
  HasTerm x x = True
  HasTerm x (y : ys) = Or (HasTerm x y) (HasTerm x ys)
  HasTerm x (HList xs) = HasTerm x xs
  HasTerm _ _ = False

type family IsHomogenous (ts :: [a]) :: Bool where
  IsHomogenous '[] = True
  IsHomogenous '[_] = True
  -- What is this madness? It is a NON-LINEAR PATTERN. Yes really.
  IsHomogenous (x : x : xs) = IsHomogenous (x : xs)
  IsHomogenous _ = False

---- This toHomoList breaks for reasons I do not understand
-- -- only defined for non-empty lists
-- toHomoList :: IsHomogenous (t : ts) ~ True => HList (t : ts) -> [t]
-- -- toHomoList HNil = [] this is unreachable since the list cannot be empty
-- toHomoList (x :# HNil) = [x]
-- toHomoList (x :# xs) = x : toHomoList xs

-- kind signature
type FromMaybe :: a -> Maybe a -> a -- requires PolyKinds and StandaloneKindSignatures
-- and a type function
type family FromMaybe x y where
  FromMaybe x Nothing = x -- this is a bit confusing, Nothing or 'Nothing, both seem to work
  FromMaybe _ (Just y) = y

-- type signature
fromMaybe :: a -> Maybe a -> a
-- and a term functions (no header needed, unlike type families)
fromMaybe x Nothing = x
fromMaybe _ (Just y) = y


type family AllEq (ts :: [Type]) :: Constraint where
  AllEq '[] = () -- no constraint
  AllEq (t : ts) = (Eq t, AllEq ts)


type family All (c :: Type -> Constraint)
                (ts :: [Type]) :: Constraint where
  All c '[] = () -- no constraint
  All c (t : ts) = (c t, All c ts)

-- -- show instance WITHOUT All
-- instance Show (HList '[]) where
--   show _ = ""
-- instance (Show t, Show (HList ts)) => Show (HList (t : ts)) where
--   show (x :# HNil) = show x
--   show (x :# xs) = show x ++ " | " ++ show xs

-- show instance WITH all
instance (All Show ts) => Show (HList ts) where
  show HNil = ""
  show (x :# xs) = show x ++ " | " ++ show xs

newtype Cont a = Cont { unCont :: forall r . (a -> r) -> r }


hetHead :: HList (t : ts) -> t
hetHead (x :# _) = x

type Take :: Nat -> [a] -> [a]
type family Take n xs where
  Take _ '[] = '[]
  Take 0 _ = '[]
  Take n (x : xs) = x : Take (n - 1) xs

type Iterate :: (a -> a) -> a -> [a]
type family Iterate f x where
  Iterate f x = x : Iterate f (f x)

type IteratePlus5 :: Nat -> [Nat]
type family IteratePlus5 x where
  IteratePlus5 x = x : IteratePlus5 (x+5)

fromCont :: Cont a -> a
fromCont (Cont f) = f id

toCont :: a -> Cont a
toCont x = Cont (\f -> f x)

instance Functor Cont where
  fmap f (Cont g) = Cont (\g' -> g' . f . g $ id)

instance Applicative Cont where
  pure = toCont
  abrr <*> arr = toCont $ (fromCont abrr) (fromCont arr)

instance Monad Cont where
  return = toCont
  arr >>= abrr = abrr (fromCont arr)

---- Open Type Families -------------

-- In open type families, the instances are *unordered*. Closed families allow
-- overlapping definitions because they are evaluated in order, the first match
-- succeedes. This avoids the combinatorial explosion that could result in an
-- open family.

type Label :: Type -> Symbol
type family Label t -- no where, where is for closed families

type instance Label Double = "number"
type instance Label Int = "number"

data Foo = Foo
type instance Label Foo = "yolo!!!!"

-- non-type variable argument, requires FlexibleContexts
label :: forall t . KnownSymbol (Label t) => String
label = symbolVal (Proxy @(Label t)) -- TypeApplications

------------------- Rank N Types -------------
-- RankNType's are used to define call-back functions
-- The Continuation Monad

withVersionNumber :: (Double -> r) -> r
withVersionNumber f = f 1.0

withTimestamp :: (Int -> r) -> r
withTimestamp f = f 123456789

withOS :: (String -> r) -> r
withOS f = f "Linux"

releaseString :: String
releaseString = fromCont $ do
  version <- Cont withVersionNumber
  date <- Cont withTimestamp
  os <- Cont withOS
  return $ os ++ "-" ++ show version ++ "-" ++ show date

-- data Any = forall a . Any a
data Any where
  Any :: a -> Any

data Viewable where
  Viewable :: Show a => a -> Viewable

instance Show Viewable where
  show (Viewable x) = show x

data Number where
  Number :: (Num a, Show a) => a -> Number

instance Show Number where
  show (Number x) = show x
