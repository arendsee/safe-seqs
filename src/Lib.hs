{-# LANGUAGE TypeApplications #-}

module Lib (someFunc) where

import GHC.TypeLits ()
import Data.Kind (Type)

import TypeFoo

someFunc :: IO ()
someFunc = do
  putStrLn $ showType @Int
  putStrLn $ show $ hLength $ 1 :# HNil
  putStrLn $ show $ 1 :# True :# HNil
  putStrLn $ show $ 1 :# (True :# 42 :# HNil) :# 21 :# HNil
  putStrLn $ show $ hetHead $ 999 :# (True :# 42 :# HNil) :# 21 :# HNil
  putStrLn $ show $ compare (1 :# True :# HNil) (1 :# True :# HNil)
  putStrLn $ show $ compare (1 :# True :# HNil) (1 :# False :# HNil)
  putStrLn $ show $ compare (1 :# True :# HNil) (1 :# False :# HNil)
  putStrLn $ releaseString
  putStrLn $ show $ [Viewable 1, Viewable True]
  putStrLn $ show $ [Number (2 * x) | Number x <- [Number (42 :: Integer), Number 2.1]]
  putStrLn $ label @(Foo)
  -- putStrLn $ show $ toHomoList $ (True :# False :# HNil)
