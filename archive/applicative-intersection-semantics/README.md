# 	Applicative Intersection Types

## Style Guides

```haskell
1
1 : Int
-- \x.x : Int -> Int
-- (\x.x) 4
1 ,, true
1 ,, true : Int & Bool 
(succ ,, not : Int -> Int) 5
(succ ,, f : Int -> Bool) 3 : Bool
(succ ,, not) 4
(succ ,, not) (4 ,, true)
(f : Int & Bool -> Int & Bool ,, g : String -> String) (4 ,, true)
(((\x.x) ,, True) : Int -> Bool) 1
((\x : A.x) ,, 3) 4 -- TBD
```

## Syntax

```haskell
A, B ::= Int | Top | A -> B | A & B
e ::= n | x | \x : A . e | e1 e2 | e1,,e2 | (e : A)

p ::= n | \x : A. e
v ::= p : A | v1 ,, v2

T ::= . | T, x : A
S ::= . | S, A
```

## Subtyping

```
------
A <: B     (Subtyping, rule form)
------

Int <: Int         S-Int


A <: Top           S-Top


Top <: B2
----------------   S-TopArr
A <: B1 -> B2


C <: A    B <: D
----------------   S-Arrow
A -> B <: C -> D


A <: B    A <: C
----------------   S-And
A <: B & C


A <: C
----------         S-AndL
A & B <: C


B <: C
----------         S-AndR
A & B <: C
```

## Application Subtyping

```
-----------
S |- A <: B
-----------


------------------------ AS-Refl
. |- A <: A


C <: A      S |- B <: D
------------------------ AS-Fun
S, C |- A -> B <: C -> D


S, C |- A <: D
side-condition1
------------------------ AS-AndL
S, C |- A & B <: D


S, C |- B <: D
side-condition2
------------------------ AS-AndR
S, C |- A & B <: D
```

## Typed Reduction

```
------------------
v -->A v'
------------------


------------------ Tred-Int-Anno
n : Int -->Int n : Int


Ordinary A
TopLike A
------------------- Tred-Top
v -->A (1 : A)


not (TopLike D)
C <: A
B <: D
----------------------------------------------------- Tred-Arrow-Annotated
(\x : E. e) : A -> B  -->(C -> D)     (\x : E . e) : C -> D


v1 -->A v1'
Ordinary A
---------------------------- Tred-Merge-L
v1,,v2 -->A v1'


v2 -->A v2'
Ordinary A
---------------------------- Tred-Merge-R
v1,,v2 -->A v2'


v -->A v1
v -->B v2
--------------------------------- Tred-And
v -->(A & B) v1,,v2
```
## Parallel Application

```
----------------
v ● vl --> e
----------------

TopLike (ptype v)
----------------------------- PApp-Top (Newly Added)
v ● vl --> 1 : (ptype v)


v -->A v'
not (toplike B)
-------------------------------------------- PApp-Abs-Anno (not sure)
\x : C. e : A -> B ● v --> e [x |-> v'] : B


ptype(vl) |- ptype(v1 ,, v2) <: ptype(v1)
not (toplike ptype(v1 ,, v2))
v1 ● vl --> e
-------------------------------------------- PApp-Merge-L
v1 ,, v2 ● vl --> e


ptype(vl) |- ptype(v1 ,, v2) <: ptype(v2)
not (toplike ptype(v1 ,, v2))
v2 ● vl --> e
-------------------------------------------- PApp-Merge-R
v1 ,, v2 ● vl --> e
```

## Reduction

```
-------------
e --> e'
-------------

----------------------- Step-Int-Anno
n --> n : Int


v ● vl --> e
---------------- Step-PApp
v vl --> e


v -->A v'
------------------------ Step-Anno-Value
v : A -> v'


not value (e : A)
e --> e'
------------------ Step-Anno
e : A --> e' : A


e1 --> e1'
------------------ Step-App-L
e1 e2 --> e1' e2


e2 --> e2'
------------------ Step-App-R
v e2 --> r e2'


e1 --> e1'
---------------------------- Step-Merge-L
e1 ,, e2 --> e1' ,, e2


e2 --> e2'
----------------------------- Step-Merge-R
v ,, e2 --> v ,, e2'
```

## Principal Typing

```
--------------------
ptype e => A
-------------------

------------------ ptype-int
ptype n => Int


------------------ ptype-anno
ptype (e : A) => A


ptype e1 => A   ptype e2 => B 
--------------------------------------------------- ptype-merge
ptype e1,,e2 => A & B
```

## Typing

```
--------------
T; S |- e => A
T |- e <= A
--------------

syntactic sugar:
T |- e => A   ==   T; . |- e => A


|- T
------------------ TInt
T |- n => Int


|- T   x : A \in T
--------------------- TVar
T |- x => A


TopLike B
-------------------------- pvalue-Top
T | p <= B


T, x : A |- e <= C     B <: A
--------------------------------- TLam
T |- \x : A .e <= B -> C
 

S |- A <: B    T |- e <= A
----------------------------- TAnn
T ; S |- e : A => B


T |- e2 => A   T ; S, A |- e1 => A -> B
----------------------------------------- TApp1
T ; S |- e1 e2 => B


T |- e2 => A    T |- e1 <= A -> B
----------------------------------- TApp2
T |- e1 e2 <= B


T |- e => B     B <: A
------------------------- TSub
T |- e <= A


disjoint A B        T, S |- e1 => A   T, S |- e2 => B
------------------------------------------------------ TMerge
T, S|- e1 ,, e2 => A & B


consist v1 v2      .; S |- v1 => A     .; S |- v2 => B
------------------------------------------------------ T-Merge-Value
T, S |- v1,,v2 => A & B


T; S |- e1,,e2 => B   S, A |- B <: C
----------------------------------------------- T-Merge-pick
T; S, A |- e1,,e2 => C


T |- e <= A    T |- e <= B
--------------------------------- T-Chk-And (newly added)
T |- e <= A & B
```

## Ordinary

```
-------------
Ordinary A
-------------

------------------ Ord-Top
Ordinary Top


------------------ Ord-Int
Ordinary Int


------------------ Ord-Arrow
Ordinary (A -> B)
```

## Disjoint

```
-----------------
Disjoint A B
-----------------


------------------- Disjoint-Top-L
Disjoint Top A


------------------- Disjoint-Top-R
Disjoint A Top


------------------------- Disjoint-Int-Arr
Disjoint Int (A1 -> A2)


------------------------- Disjoint-Arr-Int
Disjoint (A1 -> A2) Int


Disjoint B1 B2
----------------------------- Disjoint-Arr-Arr
Disjoint (A1 -> B1) (A2 -> B2)


Disjoint A1 B       Disjoint A2 B
------------------------------------ Disjoint-And-L
Disjoint (A1 & A2) B


Disjoint A B1       Disjoint A B2
------------------------------------ Disjoint-And-R
Disjoint A (B1 & B2)
```

## TopLike

```
-------------
TopLike A
-------------

--------------------- TL-Top
TopLike Top


TopLike A
TopLike B
--------------------- TL-And
TopLike (A & B)


TopLike B
-------------------- TL-Arrow
TopLike (A -> B)
```