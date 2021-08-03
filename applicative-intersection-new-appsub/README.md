# Syntax

```
A, B ::= Int | Top | A -> B | A & B
e    ::= n | x | \x:A. e | e1 e2 | e1,,e2 | e : A

p    ::= n | \x .e : A -> B
v    ::= p : A | v1,,v2

T    ::= . | T, x : A
S    ::= . | S, A
```

# TopLike

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

# Ordinary

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



# Subtyping

```
------
A <: B     (Subtyping, rule form)
------

Int <: Int         S-Int


A <: Top           S-Top


Top <: C
----------------   S-Top-Arr
A <: B -> C


C <: A    B <: D
----------------   S-Arrow
A -> B <: C -> D


A <: B    A <: C
----------------   S-And
A <: B & C


A <: C
----------         S-And-L
A & B <: C


B <: C
----------         S-And-R
A & B <: C
```

# Application Subtyping (2-ary)

```
-----------------
appsub? S B
-----------------

---------------------------- AS?-Refl
appsub? . A

C <: A     appsub? S B
----------------------------- AS?-Fun
appsub? (S, C) (A -> B)


appsub? (S, C) A
------------------------ AS?-And-L
appsub? (S, C) (A & B)


appsub? (S, C) B
------------------------ AS?-And-R
appsub? (S, C) (A & B)
```

# Application Subtyping

```
-----------
S |- A <: B
-----------


------------------------ AS-Refl
. |- A <: A


C <: A      S |- B <: D
------------------------ AS-Fun (do we need it?)
S, C |- A -> B <: C -> D


appsub? C A
not (appsub? C B)
------------------------ AS-And-L
S, C |- A & B <: A


appsub? C B
not (appsub? C A)
------------------------ AS-And-R
S, C |- A & B <: B


appsub? C A
appsub? C B
------------------------ AS-And-Both
S, C |- A & B <: A & B
```

# Disjoint

```
-----------------
Disjoint A B
-----------------

spec:
Disjoint A B :=
forall C, A <: C -> B <: C -> toplike C


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

# Typed Reduction

```
------------------
v -->A v'
------------------

A <: Int
---------------------- Tred-Int-Anno
n : A -->Int n : Int


Ordinary A
TopLike A
------------------- Tred-Top
v -->A (1 : A)


not (TopLike D)
E <: C -> D
---------------------------------------------------------- Tred-Arrow-Anno
(\x. e : A -> B) : E  -->(C -> D)     (\x. e : A -> B) : C -> D


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

# Principal Typing

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

# Parallel Application

```
----------------
v ● vl --> e
----------------

TopLike (ptype v)
----------------------------- PApp-Top
v ● vl --> 1 : (ptype v)


v -->C v'
not (toplike D)
-------------------------------------------- PApp-Abs-Anno
(\x. e : A -> B) : C -> D ● v --> e [x |-> v'] : D


ptype(vl) |- ptype(v1 ,, v2) <: ptype(v1)
not (toplike ptype(v1 ,, v2))
-------------------------------------------- PApp-Merge-L
v1 ,, v2 ● vl --> v1 ● vl


ptype(vl) |- ptype(v1 ,, v2) <: ptype(v2)
not (toplike ptype(v1 ,, v2))
-------------------------------------------- PApp-Merge-R
v1 ,, v2 ● vl --> v2 ● vl


ptype(vl) |- ptype(v1 ,, v2) <: ptype(v1) & ptype(v2)
not (toplike ptype(v1 ,, v2))
-------------------------------------------- PApp-Merge-Parallel
v1 ,, v2 ● vl --> (v1 ● vl) ,, (v2 ● vl)
```

# Reduction

```
-------------
e --> e'
-------------

----------------------- Step-Int-Anno
n --> n : Int


----------------------- Step-Abs-Anno
\x. e : A -> B --> (\x. e : A -> B) : A -> B


v ● vl --> e
---------------- Step-PApp
v vl --> e


v -->A v'
------------------------ Step-Anno-Value
v : A --> v'


not value (e : A)
e --> e'
------------------ Step-Anno
e : A --> e' : A


e1 --> e1'
------------------ Step-App-L
e1 e2 --> e1' e2


e2 --> e2'
------------------ Step-App-R
v e2 --> v e2'


e1 --> e1'
---------------------------- Step-Merge-L
e1 ,, e2 --> e1' ,, e2


e2 --> e2'
----------------------------- Step-Merge-R
v ,, e2 --> v ,, e2'
```

# Typing

```
T; S |- e => A


---------------- T-Int
T |- n => Int


x : A \in T
----------------- T-Var
T |- x => A


T, x : A |- e => B
----------------------------- T-Lam1
T |- \x. e : A -> B => A -> B


T, x : A |- e => B       S, C |- A -> B <: A -> B
-------------------------------------------------------- T-Lam2
T; S, C |- \x. e : A -> B => A -> B


T |- e => C      C <: A        S |- A <: B
--------------------------------------------- T-Ann
T; S |- e : A => B


T |- e2 => A    T; S, A |- e1 => A -> B
---------------------------------------- T-App
T; S |- e1 e2 => B


disjoint A B        T |- e1 => A   T |- e2 => B
------------------------------------------------------ T-Merge
T |- e1,,e2 => A & B


consist v1 v2      . |- v1 => A     . |- v2 => B
------------------------------------------------------ T-Merge-Value
T |- v1,,v2 => A & B


T |- e1,,e2 => A & B
S, C |- A & B <: D
----------------------------------------------- T-Merge-pick
T; S, C |- e1,,e2 => D
```
