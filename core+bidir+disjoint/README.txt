This proposal is about new rules for disjointness (operate disjoint on functions (input types))

which allows for showInt,,showBool

showInt  : Int -> String
showBool : Bool -> String

but reject succ,,pred

succ : Int -> String
pred : Int -> String

-------------------------------------------------------------
some possible specification of disjoint

1)
Definition disjoint_spec_forall A B :=
  forall C, ~ (ordinary C -> (auxas (Some C) A /\ auxas (Some C) B)).

Definition disjoint_spec_exist A B :=
  ~ (exists C, ordinary C -> auxas (Some C) A /\ auxas (Some C) B).

two definition are exactly the same


STATUS: completenss NOT proven (not easy), soundness NOT proven (not easy, and I conjecture that it suffer from the same problem with the next specification)

2)

Definition disjoint_spec_alter A B :=
  forall C, (auxas (Some C) A /\ auxas (Some C) B) -> ~ ordinary C.


disjoint_spec_forall -> disjoint_spec_alter is okay, but not in the reverse direction


STATUS: completenss proven, soundness broken


-------------------------------------------------------------
some possible specification of cost

1)
Definition cost_spec A B :=
  exists C, ordinary C -> sub C A /\ sub C B.

2)
Lemma cost_sound_alternative :
  forall A, ordinary A -> forall B, sub A B -> forall C, sub A C -> cost B C.



--------------------------------------------------------------
ALGO RULES
--------------------------------------------------------------

T |- e1 => A
T |- e2 => B
A ** B
----------------------
T |- e1 ,, e2 => A & B


------------------------
Overloadable A ** B
------------------------

~ cost A1 A2
------------------------ Arr
A1 -> B1 ** A2 -> B2



A1 ** B
A2 ** B
--------------- And-L
A1 & A2 ** B



A ** B1
A ** B2
---------------- And-R
A ** B1 & B2


----------------------
cost A B
----------------------

-------------- TOP
cost Top Top


ordinary A
toplike B
---------------- Ord-L
cost A B


toplike A
ordinary B
--------------- Ord-R
cost A B


-------------- Int
cost Int Int


cost B1 B2
--------------------------- Arr
cost (A1 -> B1) (A2 -> B2)


cost A C
cost B C
---------------- And-L
cost (A & B) C


cost A B
cost A C
---------------- And-R
cost A (B & C)


--------------------------------------------
Problems in TYPE SYSTEM

there are some lemma has been broken

1. determinism of casting

v1,,v2 : A -> e1
v1,,v2 : A -> e2
e1 should be equal to e2
normally we prove by inversion on step1 and step2, in subcase
v1 -A-> v1'
v2 -A-> v2'
by v1 and v2 can be casted under type A, type A is their super type
two disjoint types' common supertype is toplike <- this couldn't happen in NEW disjoint
v1' = v2' = "some top value", thus determinism proved

2. preservation of application
((\x:A1.e:B1):C1->D1),,((\x:A2.e:B2):C2->D2) v

suppose f1 and f2 are disjoint, which means C1 -> D1 is disjoint with C2 -> D2
the application result e[x|->v']:D1 and e[x|-v']:D2 is not disjoint <-- we force disjoint on the left of arrow type

UPDATE: if v can be accpeted by both branches, this case should be rejected (disjoint merges shouldn't accpet same argument at the same time)

go back to the specification of disjoint:

Definition disjoint_spec A B :=
  forall (C : type), ordinary C -> ~ (auxas (Some C) A /\ auxas (Some C) B).

the side-condition Ordinary C is because
if A is Int -> Int, B is Bool -> Int, we can always find Int & Bool to let both branches hold

------------------------------------------------------------------
disjoint should be transferred via subtyping? (it's currently not)
------------------------------------------------------------------

disjoint A B
A <: C
--------------
disjoint C B

gubtyping broken when C is Top (it's not a function-type)


one breaking example would be

f,,g v type checks, the result type is Bool & Bool

f : (Int -> Int) -> Bool
g : (Bool -> Bool) -> Bool
v : (Int -> Int) & (Bool -> Bool)


-------------------------------
some notes on soundness/completeness
-------------------------------
completenss can be held

soundness is always broken:


Indeed, when A B are not function types, the premise is false then this spec always holds,
but we cannot say they's algo-disojoint, soundness is broken

Definition disjoint_spec_alter A B :=
  forall C, (auxas (Some C) A /\ auxas (Some C) B) -> ~ ordinary C.


f : Int -> Int
g : Bool -> Int

(f,,g) : (Int & Bool) -> Int


f : (Int -> Int) -> Int
g : (Bool -> Bool) -> Int

(f,,g) : ((Int -> Int) & (Bool -> Bool)) -> Int


