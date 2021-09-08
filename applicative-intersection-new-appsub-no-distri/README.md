#  Syntax

```
A, B ::= Int | Top | A -> B | A & B
e    ::= n | x | \x:A. e | e1 e2 | e1,,e2 | e : A

p    ::= n | \x .e : A -> B
v    ::= p : A | v1,,v2
r    ::= v | v r

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

# Application Subtyping

```
-----------
S |- A <: B
-----------

Spec:
Exists O, A <: S -> O -> B <: S -> O.


------------------------ AS-Refl
. |- A <: A


C <: A      S |- B <: D
------------------------ AS-Fun
S, C |- A -> B <: C -> D


not (appsub? (S, C) B)
S, C |- A <: D
------------------------ AS-And-L
S, C |- A & B <: D


not (appsub? (S, C) A)
S, C |- B <: D
------------------------ AS-And-R
S, C |- A & B <: D
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
ptype r => A
-------------------

------------------ ptype-anno
ptype (e : A) => A


ptype e1 => A   ptype e2 => B 
--------------------------------------------------- ptype-merge
ptype e1,,e2 => A & B


ptype r => A -> B    ptype v => C   sub C A
----------------------------------------------- ptype-rvalue
ptype (r v) =>  B
```

# Collective Application (Phase I)

```
------------------
r * L --> e
------------------

v ● L --> e
-------------------- CApp-PApp
v * L --> e


r * (L, v) --> e
-------------------- CApp-Collect
(r v) * L --> e
```

# Parallel Application (Phase II)

```
------------------
v ● L --> e
------------------

(\x. e : A -> B) : C -> D ⊗ L --> e'
--------------------------------------- PApp-Beta
(\x. e : A -> B) : C -> D ● L --> e'


v1 ● L --> e
----------------------- PApp-pick-L
(v1 ,, v2) ● L --> e


v2 ● L --> e
---------------------- PApp-pick-R
(v1 ,, v2) ● L --> e
```

# Multiple Beta-Reduction (Phase III)

```
--------------------------------------------------
(\x. e : A -> B) : C -> D ⊗ L --> e (not complete) (induction on two terms)
---------------------------------------------------


v -->A v'
---------------------------------------------------------------- MBeta-Nil
(\x. e : A -> B) : C -> D ⊗ (nil, v) --> e [x |-> v'] : D


v -->A v'
e [x |- v'] : D ⊗ L --> e'
---------------------------------------------------------------- MBeta-List
(\x. e : A -> B) : C -> D ⊗ (L, v) --> e'
```

# Reduction

```
-------------
e --> e'
-------------

----------------------- Step-Int-Anno
n --> n : Int


--------------------------------------------- Step-Abs-Anno
\x. e : A -> B --> (\x. e : A -> B) : A -> B


toplike (ptype (r))
------------------------- Step-PApp-Toplike
r v --> 1 : (ptype r)


not toplike (ptype (r))
(r v) * nil --> e
----------------------- Step-PApp
r v --> e


v -->A v'
------------------------ Step-Anno-Value
v : A --> v'


not value (e : A)
e --> e'
------------------ Step-Anno
e : A --> e' : A


e1 --> e1'   not (rvalue(e1))
----------------------------- Step-App-L (part of arguments can pick)
e1 e2 --> e1' e2


e2 --> e2'
------------------ Step-App-R
r e2 --> r e2'


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
--------------- T-Var
T |- x => A


x : A \in T   S |- A <: B 
------------------------------- T-Var-stack
T; S |- x => B


T, x : A |- e => B
----------------------------- T-Lam1
T |- \x. e : A -> B => A -> B


T, x : A |- e => B       S, C |- A -> B <: D
-------------------------------------------------------- T-Lam2
T; S, C |- \x. e : A -> B => D


T |- e => C      C <: A        S |- A <: B 
--------------------------------------------- T-Ann
T; S |- e : A => B


T |- e2 => A      T; S, A |- e1 => A -> B
------------------------------------------- T-App
T; S |- e1 e2 => B


disjoint A B        T |- e1 => A   T |- e2 => B
------------------------------------------------------ T-Merge
T |- e1,,e2 => A & B


consist v1 v2      . |- v1 => A     . |- v2 => B
------------------------------------------------------ T-Merge-Value
T |- v1,,v2 => A & B


T; S, A |- e1 => C       T |- e2 => B
not appsub? (S, A) B
disjoint B C
----------------------------------------------- T-Merge-pick-L
T; S, A |- e1,,e2 => C


T; S, A |- e2 => C    T |- e1 => B
not appsub? (S, A) B
disjoint B C
----------------------------------------------- T-Merge-pick-R
T; S, A |- e1,,e2 => C
```
