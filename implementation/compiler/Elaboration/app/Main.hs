{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Main where

import Prelude hiding (and, or)

import qualified Racket as R
import qualified Coercion as Co

type Label = Int

data Type = Int
          | Top
          | Arr Type Type
          | And Type Type
          | Rcd Label Type
          deriving (Show, Eq)


data Term = Lit Int
          | Var String
          | Lam String Type Term Type
          | App Term Term
          | Mrg Term Term
          | Fld Label Term
          | Prj Term Label
          deriving (Show, Eq)

-- Subtyping

data Arg = T Type | L Label

data PType = Normal Type | Partial Arg

data Result = Fail | Pass Co.Coercion  | Result Type Co.Coercion deriving (Show, Eq)

split :: Type -> Maybe (Type, Type)
split (And a b) = Just (a,b)
split (Rcd l a)
   | Just (a1, a2) <- split a
   = Just (Rcd l a1, Rcd l a2)
split (Arr a b)
   | Just (b1, b2) <- split b
   = Just (Arr a b1, Arr a b2)
split _ = Nothing

andand :: Result -> Result -> Result
andand (Pass c1) (Pass c2) = Pass (Co.pair c1 c2)
andand _ _ = Fail

andarr :: Result -> Result -> Result
andarr (Pass c1) (Pass c2) = Pass (Co.arrow c1 c2)
andarr _ _ = Fail

or :: Result -> Result -> Result
or (Pass c1) Fail = Pass Co.proj1
or Fail (Pass c2) = Pass Co.proj2
or (Pass c1) (Pass c2) = Pass Co.identity -- worry about this coercion
or Fail Fail = Fail

subtype :: Type -> PType -> Result
subtype Int (Normal Int) = Pass Co.identity
subtype _ (Normal Top) = Pass Co.top
subtype a (Normal b)
  | Just (b1, b2) <- split b
  = andand (subtype a (Normal b1)) (subtype a (Normal b2))
subtype (And a1 a2) (Normal b) =
  or (subtype a1 (Normal b)) (subtype a2 (Normal b))
subtype (Arr a1 a2) (Normal (Arr b1 b2)) =
  andarr (subtype b1 (Normal a1)) (subtype b2 (Normal b2))
subtype (Rcd la a) (Normal (Rcd lb b))
  | la == lb
  = subtype a (Normal b)


-- Typing

type Context = [(String, Type)]

find :: Context -> String -> Type
find ctx x = head [ t | (y, t) <- ctx, x == y]

infer :: Context -> Term -> Maybe (Type, R.Term)
infer ctx (Lit i) = Just (Int, R.Lit i)
infer ctx (Var x) = Just (find ctx x, R.Var x)
infer ctx (Lam x ta e tb) = case check ((x, ta) : ctx) e tb of
  Nothing -> Nothing
  Just (result, expr) -> Just (Arr ta tb, R.Lam x expr)

check :: Context -> Term -> Type -> Maybe (Bool, R.Term)
check ctx e tb = undefined

--- tests
main :: IO ()
main = do
  print $ infer [] (Lit 1)
  print $ infer [("x", Int), ("y", Arr Int Int)] (Var "y")
