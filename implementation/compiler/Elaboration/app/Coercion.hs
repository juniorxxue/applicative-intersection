module Coercion where

import qualified Racket as R

type Coercion = R.Term

identity :: Coercion
identity = R.Lam "x" (R.Var "x")

top :: Coercion
top = R.Lam "x" R.Unit

arrow :: Coercion -> Coercion -> Coercion
arrow c1 c2 = R.Lam "f" (R.Lam "x" body)
    where body = R.App c2 (R.App (R.Var "f") (R.App c1 (R.Var "x")))

pair :: Coercion -> Coercion -> Coercion
pair c1 c2 = R.Lam "x" $ R.Pair (R.App c1 (R.Var "x")) (R.App c2 (R.Var "x"))

proj1 :: Coercion
proj1 = R.Lam "x" (R.Fst (R.Var "x"))

proj2 :: Coercion
proj2 = R.Lam "x" (R.Snd (R.Var "x"))