# Applicative Merge

## Problem

`((\x. x) ,, 3) 4` cannot be type checked and cannot be reduced

but it should be

## Related Rules

```
T |- e2 => A   T ; S, A |- e1 => A -> B
----------------------------------------- TApp1
T ; S |- e1 e2 => B


T, x : A ; S |- e => B
------------------------------ TLam2
T ; S, A |- \x. e => A -> B


disjoint A B        T |- e1 => A   T |- e2 => B
----------------------------------------------- TMerge
T |- e1 ,, e2 => A & B


T; S |- e1,,e2 => B   S, A |- B <: C
----------------------------------------------- T-Merge-pick
T; S, A |- e1,,e2 => C


ptype(vl) |- ptype(v1 ,, v2) <: A
v1 ,, v2 -->A v
v ● vl --> e
-------------------------------------------- PApp-Merge
v1 ,, v2 ● vl --> e
```

## Typing

We look at typing fristly

```
             --------------------------------------- We-Stuck-Here!!
4 => Int     . ; Int |- (\x. x ,, 3) => Int -> Int
----------------------------------------------------- TApp1
.;. |- ((\x. x) ,, 3) 4 => Int
```

Intuitively,  `. ; Int |- (\x. x ,, 3) => Int -> Int`  is valid if `Int |- \x .x => Int -> Int`

```
----------------------- TVar
x : Int ; . |- x => Int
------------------------------ TLam2
Int |- \x. x => Int -> Int
```

**New: T-Merge-pick rule is valid if only one term of merge can infer some type under argument stack.**

```
T; S, A |- e1 => C
not()
------------------------------------------- T-Merge-pick-L
T; S, A |- e1,,e2 => C

T; S, A |- e2 => C
not()
------------------------------------------- T-Merge-pick-R
T; S, A |- e1,,e2 => C
```

```4 => Int     . ; Int |- (\x. x ,, 3) => Int -> Int
             ---------------------------------- T-Abs
             . ; Int |- \x. x => Int -> Int
             ------------------------------------- T-Merge-pick-L
4 => Int     . ; Int |- (\x. x ,, 3) => Int -> Int
---------------------------------------------------------- TApp1
.;. |- ((\x. x) ,, 3) 4 => Int
```

But what about `(succ ,, not) 4`,  that's the main motivation we create the `T-merge-pick` rule.

```
--------------------------------
Int |- Int -> Int <: Int -> Int    (\x. x+1) <= Int -> Int
---------------------------------------------------------- TAnn
Int |- succ => Int -> Int
------------------------------------ T-Merge-Pick-R
Int |- succ ,, not => Int -> Int
------------------------------------ TApp1
.;. |- succ ,, not 4 => Int
```

Bruno:

```
T; S, A |- e1 => C
T; . |- e2 => B      T; S, A |- B <: ??? 
------------------------------------------- T-Merge-pick-L
T; S, A |- e1,,e2 => C
```

Proposed rule cannot reject the above example, where `3 + True` is ill-typed

```
Int |- \x. x ,, 3 + True => Int -> Int
```

Ningning:

```
T; S, A |- e1 => C
T; . |- e2 => D
not (S, A |- D <: Top)
------------------------------------------- T-Merge-pick-L
T; S, A |- e1,,e2 => C
```

## Reduction

And then reduction part

```
ptype(vl) |- ptype(v1 ,, v2) <: A
v1 ,, v2 -->A v
v ● vl --> e
-------------------------------------------- PApp-Merge
v1 ,, v2 ● vl --> e
```

```
Int |- ptype(\x.x ,, (3 : Int)) <: 
-------------------------------------------------- PApp-Merge
\x.x ,, (3 : Int) ● (3 : Int) --> (3 : Int)
```

**Oops, no principle type for `\x.x` **

Well, how do we treat `(\x. x) 4` before in the reduction? We simply do the subsititution!

Why we need `ptype`, we try to avoid seeking help from `typing` in the reduction rule.

How snow's type system deal with `succ ,, not 4` , I guess it should be `((succ ,, not) : (Int -> Int)) 4`.

So, typed reduction should should appear at this place too.

like `Int |- \x. x ,, (3 : Int) --> \x. x`

Though it's a special version of `Typed Reduction`, we don't unify them firslty.

```
Int |- (\x. x) ,, 3 --> \x. x
Int |- succ ,, not --> succ
```

```
S, A |- A1 -> B1 <: C
--------------------------------------------------------------------- Anno-Pick-L
S, A |- (\x. e1 : A1 -> B1) ,, (\x.e2 : A2 -> B2) --> \x.e1 : A1 -> B1


S, A |- A2 -> B2 <: C
--------------------------------------------------------------------- Anno-Pick-R
S, A |- (\x. e1 : A1 -> B1) ,, (\x.e2 : A2 -> B2) -> \x.e2 : A2 -> B2
```

## Misc

Some angles to guide thinking

* How it behave in snow's type system (full annotation one)?
* How it behave in classical lambda calculus?
* What's its original intention?