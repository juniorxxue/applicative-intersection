# Syntax

```
A, B ::= Int | Top | A -> B | A & B
e    ::= n | x | \x.e : A -> B | e1 e2 | e1,,e2 | e : A

O    ::= Int | Top | A -> O

p    ::= n | \x. e : A -> B
v    ::= p : O | v1,,v2

u    ::= e : A | u1,,u2

T    ::= . | T, x : A
S    ::= . | A
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

# Splittable Types

 ```
 -------------
 B <| A |> C
 -------------
 
 -------------------- Sp-And
 A <| A & B |> B
 
 
 C <| B |> D
 ---------------------------- Sp-Arrow
 A -> C <| A -> B |> A -> D
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


Ordinary B
------------------ Ord-Arrow
Ordinary (A -> B)
```

# Proper Types

```
|-& A

------------------- PT-Int
|-& Int


------------------- PT-Top
|-& Top


Ordinary B   |-& A  |-& B
--------------------------- PT-Ord-Fun
|-& A -> B


B <| A |> C      |-& B    |-& C
---------------------------------- PT-Split
|-& A
```

# Subtyping (Dec)

```
----------
A <: B
----------

----------------- S-Refl
A <: A


A <: B    B <: C
--------------------- S-Trans
A <: C


-------------------- S-Top
A <: Top


-------------------- S-Top-Arr
Top <: Top -> Top


B <: A      C <: D
------------------------- S-Arr
A -> C <: B -> D


A <: B     A <: C
------------------------ S-And
A <: B & C


------------------------ S-And-L
A & B <: A


------------------------ S-And-R
A & B <: B


--------------------------------------- S-Distri-Arr
(A -> B) & (A -> C) <: A -> B & C
```

# Subtyping (Algo)

```
----------
A <: B
----------

------------------ S-Int
Int <: Int


ordinary B     toplike B
----------------------------- S-Top
A <: B


B <: A    C <: D     oridinary D
----------------------------------- S-Arr
A -> C <: B -> D


B <| D |> C    A <: B    A <: C
-----------------------------------   S-And
A <: D


A <: C     ordinary C
------------------------- S-And-L
A & B <: C


B <: C     ordinary C
-------------------------- S-And-R
A & B <: C
```

# Isomorphic Subtyping

```
----------
A << A
----------

----------------------- Iso-Refl
A << A


B1 <| B |> B2
A1 << B1     A2 << B2
----------------------- Iso-And
A1 & A2 << B
```

# Application Subtyping (Binary)

```
-----------------
appsub? S B
-----------------

---------------------------- AS?-Refl
appsub? . A

C <: A
----------------------------- AS?-Fun
appsub? C (A -> B)


appsub? C A
------------------------ AS?-And-L
appsub? C (A & B)


appsub? C B
------------------------ AS?-And-R
appsub? C (A & B)
```

# Application Subtyping

```
-----------
S |- A <: B
-----------


------------------------ AS-Refl
. |- A <: A


C <: A
------------------------ AS-Fun
C |- A -> B <: B


C |- A <: D
not (appsub? C B)
------------------------ AS-And-L
C |- A & B <: D


C |- B <: D
not (appsub? C A)
------------------------ AS-And-R
C |- A & B <: D


C |- A <: D1
C |- B <: D2
------------------------ AS-And-Both
C |- A & B <: D1 & D2
```

# Application Subtyping (Unified)

```
----------
syntax
---------

A, B ::= ...
p    ::= A | A ->?
R    ::= A | ∅

-------------------
A ⊗ B = A & B
∅ ⊗ B = ∅
A ⊗ ∅ = ∅


------------------
A <: P ~> R
------------------


------------------ S-Int
Int <: Int ~> ∅


ordinary B     toplike B
----------------------------- S-Top
A <: B ~> ∅


B <: A ~> ∅   C <: D ~> ∅     oridinary D
---------------------------------------- S-Arr
A -> C <: B -> D ~> ∅


B <| D |> C
A <: B ~> ∅    A <: C ~> ∅
-------------------------------------------  S-And
A <: D ~> ∅


A <: C ~> ∅    ordinary C
------------------------- S-And-L
A & B <: C ~> ∅


B <: C ~> ∅   ordinary C
-------------------------- S-And-R
A & B <: C ~> ∅


A1 <: B ~> R1          A2 <: B ~> R2
--------------------------------------- S-Appsub-Parallel
A1 & A2 <: B ->? ~> R1 ⊗ R2


B <: A1 ~> ∅
-------------------------- S-Appsub-Arrow
A1 -> A2 <: B ->? A2
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

# Consistent

```
-----------------
e1 ~~ e2
-----------------



---------------------------------------------- Con-Abs-Anno
(\x. e : A -> B1) : C ~~ (\x. e : A -> B2) : D


---------------------- Con-Anno
e : A ~~ e : B


ptype u1 A    ptype u2 B     disjoint A B
------------------------------------------------ Con-Disjoint
u1 ~~ u2


u1 ~~ u
u2 ~~ u
------------------------------------------------ Con-Merge-L
u1 ,, u2 ~~ u


u ~~ u1
u ~~ u2
------------------------------------------------ Con-Merge-R
u ~~ u1 ,, u2
```

# Typed Reduction

```
------------------
v -->A v'
------------------

A <: Int  (required for toplike)
---------------------- Tred-Int-Anno
n : A -->Int n : Int


Ordinary A
TopLike A
------------------- Tred-Top
v -->A (1 : A)


not (TopLike D)
E <: C -> D
Ordinary D
---------------------------------------------------------- Tred-Arrow-Anno
(\x. e : A -> B) : E  -->(C -> D)  (\x. e : A -> D) : C -> D


v1 -->A v1'
Ordinary A
---------------------------- Tred-Merge-L
v1,,v2 -->A v1'


v2 -->A v2'
Ordinary A
---------------------------- Tred-Merge-R
v1,,v2 -->A v2'


B <| A |> C
v -->B v1
v -->C v2
--------------------------------- Tred-And
v --> A v1,,v2
```

# Principal Typing

```
--------------------
ptype u => A
-------------------

------------------ ptype-int
ptype n => Int


--------------------------------- ptype-arrow
ptype (\x. e : A -> B) => A -> B


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

toplike B
---------------------------------- PApp-Int-Toplike
(n : A -> B) ● vl --> 1 : B


toplike D
--------------------------------------------------- PApp-Abs-Toplike
(\x. e : A -> B) : C -> D ● v --> 1 : D


v -->A v'
not (toplike D)
------------------------------------------------- PApp-Abs-Anno
(\x. e : A -> B) : C -> D ● v --> e [x |-> v'] : D


not (appsub? ptype(vl) ptype(v2))
v1 ● vl --> e
-------------------------------------------- PApp-Merge-L
v1 ,, v2 ● vl --> e


not (appsub? ptype(vl) ptype(v1))
v2 ● vl --> e
-------------------------------------------- PApp-Merge-R
v1 ,, v2 ● vl --> e


appsub? ptype(vl) ptype(v1)
appsub? ptype(vl) ptype(v2)
v1 ● vl --> e1
v2 ● vl --> e2
-------------------------------------------- PApp-Merge-Parallel
v1 ,, v2 ● vl --> e1 ,, e2
```

# Reduction

```
-------------
e --> e'
-------------

----------------------- Step-Int-Anno
n --> n : Int


-------------------------------------------- Step-Abs-Anno
\x. e : A -> B --> (\x. e : A -> B) : A -> B


A1 <| A |> A2
--------------------------------- Step-Pvalue-Split
p : A --> (p : A1) ,, (p : A2)


v ● vl --> e
----------------------- Step-PApp
v vl --> e


v -->A v'
------------------------ Step-Anno-Value
v : A --> v'


not pvalue e
e --> e'
------------------ Step-Anno
e : A --> e' : A


e1 --> e1'
------------------ Step-App-L
e1 e2 --> e1' e2


e2 --> e2'
------------------ Step-App-R
v e2 --> v e2'


e1 --> e1'     e2 --> e2'
---------------------------- Step-Merge-BCD
e1 ,, e2 --> e1' ,, e2'


e1 --> e1'
---------------------------- Step-Merge-L
e1 ,, v2 --> e1' ,, v2


e2 --> e2'
----------------------------- Step-Merge-R
v ,, e2 --> v ,, e2'
```

# Typing

```
T |- e => A (no subsumption lemma)


---------------- T-Int
T |- n => Int


x : A \in T
----------------- T-Var
T |- x => A


T, x : A |- e <= B
-------------------------------- T-Lam
T |- \x. e : A -> B => A -> B


T |- e <= A
--------------------------------------------- T-Ann
T |- e : A => A


T |- e2 => A      T |- e1 => B    A |- B <: C
---------------------------------------------------- T-App
T |- e1 e2 => C


disjoint A B        T |- e1 => A   T |- e2 => B
------------------------------------------------------ T-Merge
T |- e1,,e2 => A & B


consistent u1 u2      . |- u1 => A     . |- u2 => B
------------------------------------------------------ T-Merge-uValue
T |- u1,,u2 => A & B


T |- e => A
A <: B
----------------------- T-Sub
T |- e <= B
```
