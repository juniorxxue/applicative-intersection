module Racket where

data Term = Unit
          | Lit Int
          | Var String
          | Lam String Term
          | App Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          deriving (Show, Eq)