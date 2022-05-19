module Coercion where

import qualified Racket as R

type Coercion = R.Term -> R.Term

identity :: Coercion
identity = id

trans :: Coercion -> Coercion -> Coercion
trans = (.)

top :: Coercion
top t = R.Unit

arrow :: Coercion -> Coercion -> Coercion
arrow c1 c2 = \v1 -> R.Lam "v2" $ c2 $ R.App v1 (c1 (R.Var "v2"))

pair :: Coercion -> Coercion -> Coercion
pair c1 c2 = \v -> R.Pair (c1 v) (c2 v)

proj1 :: Coercion
proj1 = R.Fst

proj2 :: Coercion
proj2 = R.Snd

record :: Int -> Coercion -> Coercion
-- record l1 c (R.Fld l2 v) = if l1 == l2 then R.Fld l1 (c v) else error "error in record coercion"
record l1 c e =

parallel :: Coercion -> Coercion -> Coercion
parallel c1 c2 (R.Pair x y) = R.Pair (c1 x) (c2 y)
