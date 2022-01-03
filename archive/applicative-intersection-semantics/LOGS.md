# Style Guide

# Syntax

## \x : A . e

By comparing Snow's system, Fsub and mine in terms of narrowing lemma.

Bruno proposed that `\x. e` should become `\x : A . e`

This change will sacrifice the expressiveness of  `(\x. x) 1`, I'm okay with it since it's not our main motivation.

This approach would bring a lot of changes into my system.

## pvr

```
p ::= T | n | \x . e
v ::= p : A | v1 ,, v2
r ::= v | \x . e
```

we add a new category `r` to represent value that cannot be reduced further.

If `\x. e` has been considered as a value, `\x. e : A -> B` is a value too, and then triggers typed reduction.

## Value

### Stage 1

```
p ::= T | n | \x . e | p1,,p2
v ::= p : A | \x . e
```

* the typing info is at top-level, it's easy to fetch from anontaion
* we represent the same value with two different forms!

```
1,,True : Int & Bool is a well-typed value
1,,True : Bool & Int is also a well-typed value by subsumption rule.

so the lemma
Lemma merge_typing : 
value (p1,,p2 :: A & B) -> . |- p1,,p2 <= A & B  -> . |- p1 <= A /\ . |- p2 <= B 
is not valid here
```

### Stage 2

```
p ::= T | n | \x . e | p1,,p2
v ::= p : A | \x . e | (v1,,v2) : A & B

or

p ::= T | n | \x . e | p1,,p2
v ::= p : A | \x . e | (p1 : A ,, p2 : B) : A & B
```

* which makes (1 : Int ,, True : Bool) : Int & Bool become a value
* the typing info is also at top-level
* repated typing information
* not-scablable, inappropritate for merge more than two values

`[((1 : Int ,, True : Bool) : (Int & Bool) ,, ('c' : Char)) :] (Int & Bool) & Char` is werid

### Stage 3 (Current)

```
p ::= T | n | \x . e
v ::= p : A | \x . e | v1,,v2

or

p ::= T | n | \x . e
v ::= p : A | \x . e | p1 : A ,, p2 : B
(rejected)
```

* it's similar to snow's, possibly better for some lemmas
* typing info is not at top-level, thus we bring about a principal type judgment

# Application Subtyping

## Declarative Version

we may adopt the declarative one firstly in order to reason about its metatheory easiler.

so the side-condition

```
S, C |- A <: D
not (C in Nextinputs(B))
------------------------ AS-AndL
S, C |- A & B <: D
```

would become

```
S, C |- A <: D
not (B <: S -> E)    for arbitrary E
------------------------ AS-AndL
S, C |- A & B <: D
```

## Amiuguity

```
dicussion about amiuguity

--------- PROPOSAL 1 OPEN ------------------

S |- A <: D
not (B <: S -> E)
------------------------ AS-AndL
S |- A & B <: D

for arbitrary E, it's not algorithmic, denied

--------- PROPOSAL 1 CLOSE ------------------

--------- PROPOSAL 2 OPEN ------------------

S |- A <: D
not (B <: S -> Top)
------------------------ AS-AndL
S |- A & B <: D

S -> Top is top-like type,

(string -> char) <: (int -> top) <- that's not what we want
--------- PROPOSAL 2 CLOSE -------------------

--------- PROPOSAL 3 OPEN ------------------

S |- A <: D
not (S <: inputs(B))
------------------------ AS-AndL
S |- A & B <: D


(f: Int -> Int ,, g : Int -> Bool) 4
there's a ambiuguity above
S is Int, B is Int -> Bool, so inputs(Int -> Int) is Int, that works

But what if
(f : Int -> (String -> Int) ,, g : Int -> (Char -> Int)) 4
S is Int here
inputs (Int -> (Char -> Int)) should be Int or Int -> Char?

((f : Int -> (Char -> (String -> Int)) ,, g : Int -> (Char -> (String -> Bool)) 4) 'c'
., Char, Int 
S is probably Int -> Char
inputs (B) is Int? Int -> Char? Int -> Char -> String?
--------- PROPOSAL 3 OPEN CLOSE ------------------

--------- PROPOSAL 4 OPEN ---------------------
(f : Int -> Char -> Bool,, (g : String -> String -> Bool,, h : Bool -> Bool -> Bool)) 3
actually here you want to collect the *first* inputs of g and h
String,Bool
and check that Int is not one of those
so

S,I |- A <: D
not (I in Nextinputs(B))
------------------------ AS-AndL
S,I |- A & B <: D

--------- PROPOSAL 4 CLOSE --------------------
```

# Parallel Application

## Simplified due to one case

since the case is quite simple currently, only `succ,,not 3`

we can let original (more general)

```
ptype(vl) |- ptype(v1 ,, v2) <: A
v1 ,, v2 -->A v
v ● vl --> e
-------------------------------------------- PApp-Merge
v1 ,, v2 ● vl --> e
```

Become, then typed-reduction contributes nothing, thus we remove it from the rule

```
ptype(vl) |- ptype(v1 ,, v2) <: ptype(v1)
v1 ● vl --> e
-------------------------------------------- PApp-Merge-L
v1 ,, v2 ● vl --> e


ptype(vl) |- ptype(v1 ,, v2) <: ptype(v2)
v2 ● vl --> e
-------------------------------------------- PApp-Merge-R
v1 ,, v2 ● vl --> e
```
