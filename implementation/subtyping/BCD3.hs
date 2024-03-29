import Prelude hiding (and, or)

type Label = Int

data Type = TInt | TTop | TArrow Type Type | TAnd Type Type | TRcd Label Type
   deriving (Eq, Show)

data PType = T Type | TPar Type | TParl Label deriving (Eq, Show)

split :: Type -> Maybe (Type, Type)
split (TAnd a b) = Just (a,b)
split (TRcd l a)
   | Just (a1, a2) <- split a
   = Just (TRcd l a1, TRcd l a2)
split (TArrow a b)
   | Just (b1, b2) <- split b
   = Just (TArrow a b1, TArrow a b2)
split _ = Nothing

-- normal subtyping: Fail or Pass
-- computable subtyping: Fail or (Result _)

data Result = Fail | Pass | Result Type deriving (Show, Eq)

and :: Result -> Result -> Result
and Pass Pass = Pass
and _    _    = Fail

or :: Result -> Result -> Result
or Fail Fail = Fail
or _    _    = Pass

andR :: Result -> Result -> Result
andR (Result r1) (Result r2) = Result (TAnd r1 r2)
andR (Result r) _            = Result r
andR _          (Result r)   = Result r

checkSub :: Type -> PType -> Result
checkSub TInt (T TInt) = Pass
checkSub _ (T TTop)    = Pass
checkSub a (T b)
   | Just (b1, b2) <- split b
   = and (checkSub a (T b1)) (checkSub a (T b2))
checkSub (TAnd a1 a2) (T b) =
   or (checkSub a1 (T b)) (checkSub a2 (T b))
checkSub (TAnd a1 a2) (TPar b) =
   andR (checkSub a1 (TPar b)) (checkSub a2 (TPar b))
checkSub (TAnd a1 a2) (TParl b) =
   andR (checkSub a1 (TParl b)) (checkSub a2 (TParl b))   
checkSub (TArrow a1 a2) (T (TArrow b1 b2))
   = and (checkSub b1 (T a1)) (checkSub a2 (T b2))
checkSub (TRcd la a) (T (TRcd lb b))
   | la == lb
   = checkSub a (T b)
checkSub (TArrow a1 a2) (TPar b)
   | checkSub b (T a1) == Pass = Result a2
   | otherwise                 = Fail
checkSub (TRcd la a) (TParl lb)
   | la == lb   = Result a
   | otherwise  = Fail
checkSub _ _ = Fail

-- Given (Int -> ?)
-- (Int -> Int) & (Int -> (Int -> Int))
-- (Int -> Int) & ((Int -> Int) -> (Int -> Int))
t1 = TAnd (TArrow TInt TInt) (TArrow TInt (TArrow TInt TInt))

t2 = TAnd (TArrow TInt TInt) (TArrow (TArrow TInt TInt) (TArrow TInt TInt))

p1 = TPar TInt

test1 = checkSub t1 p1

test2 = checkSub t2 p1

test3 = checkSub (TAnd (TRcd 3 TInt) (TRcd 2 TTop)) (TParl 2)
test4 = checkSub (TAnd (TArrow TInt TInt) (TRcd 2 TTop)) (TParl 2)
test5 = checkSub (TAnd (TArrow TInt TInt) (TRcd 2 TTop)) (TPar TInt)