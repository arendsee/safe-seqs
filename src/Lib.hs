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

module Lib
    ( someFunc
    ) where

import GHC.TypeLits
import Data.Typeable hiding (Proxy)

import Data.Kind (Constraint, Type)

data Proxy a = Proxy

or :: Bool -> Bool -> Bool
or True _ = True
or _ y = y

type family Or (x :: Bool) (y :: Bool) :: Bool where
  Or 'True y = 'True -- there are no type level holes?
  Or x y = y

type family Not (x :: Bool) :: Bool where
  Not 'True = 'False
  Not 'False = 'True

showType :: forall a . Typeable a => String
showType = show . typeRep $ Proxy @a

infixr 5 :#
data HList (ts :: [Type]) where
  -- using explicit type equality
  -- we could alternatively just write `HList '[]` without the explicit constraint
  HNil :: (ts ~ '[]) => HList ts  
  (:#) :: t -> HList ts -> HList (t ': ts)

hHead :: HList (t ': ts) -> t
hHead (t :# _) = t 

hLength :: HList ts -> Int
hLength HNil = 0
hLength (_ :# xs) = 1 + hLength xs


instance Eq (HList '[]) where
  (==) _ _ = True
instance (Eq t, Eq (HList ts)) => Eq (HList (t ': ts)) where
  (==) (x :# xs) (y :# ys) = x == y && xs == ys


instance Ord (HList '[]) where
  compare _ _ = EQ
instance (Ord t, Ord (HList ts)) => Ord (HList (t ': ts)) where
  compare (x :# xs) (y :# ys) = case compare x y of
    EQ -> compare xs ys
    x -> x


type family AllEq (ts :: [Type]) :: Constraint where
  AllEq '[] = () -- no constraint
  AllEq (t ': ts) = (Eq t, AllEq ts)


type family All (c :: Type -> Constraint)
                (ts :: [Type]) :: Constraint where
  All c '[] = () -- no constraint
  All c (t ': ts) = (c t, All c ts)

-- -- show instance WITHOUT All
-- instance Show (HList '[]) where
--   show _ = ""
-- instance (Show t, Show (HList ts)) => Show (HList (t ': ts)) where
--   show (x :# HNil) = show x
--   show (x :# xs) = show x ++ " | " ++ show xs

-- show instance WITH all
instance (All Show ts) => Show (HList ts) where
  show HNil = ""
  show (x :# xs) = show x ++ " | " ++ show xs

newtype Cont a = Cont { unCont :: forall r . (a -> r) -> r }

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

someFunc :: IO ()
someFunc = do
  putStrLn $ showType @Int
  putStrLn $ show $ hLength $ 1 :# HNil 
  putStrLn $ show $ 1 :# True :# HNil
  putStrLn $ show $ 1 :# (True :# 42 :# HNil) :# 21 :# HNil
  putStrLn $ show $ compare (1 :# True :# HNil) (1 :# True :# HNil)
  putStrLn $ show $ compare (1 :# True :# HNil) (1 :# False :# HNil)
  putStrLn $ show $ compare (1 :# True :# HNil) (1 :# False :# HNil)
  putStrLn $ releaseString
  putStrLn $ show $ [Viewable 1, Viewable True]
  putStrLn $ show $ [Number (2 * x) | Number x <- [Number (42 :: Integer), Number 2.1]]
