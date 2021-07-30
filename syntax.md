```
succ : Int -> Int
pred : Int -> Int
odd : Int -> Bool
not  : Bool -> Bool
add  : Int -> Int -> Int
or   : Bool -> Bool -> Bool
chk  : Int -> Bool -> Bool
```

we have some possibly accepted application terms

```
(succ ,, not) 4
(add ,, or) 1
((add ,, or) 1) 2
(add ,, chk) 1
((add ,, chk) 1) true
```

# Classficiation

## Simple Way

Reject all possible terms that cause ambiuguity at first application

which means we reject

```
(succ ,, pred) 2 -- this would be rejected by disjoint
(succ ,, odd) 2
(and ,, chk) 1
((and ,, chk) 1) true
```

## Add-up

since our current type system collect all arguments and deletgate is role into abstraction (annoation + lambda)

**Same Behavior in Semantics** Do the picking after collecting all arguments

our intention is reject terms like

```
(succ ,, odd) 2
(and ,, chk) 1
```

and accpet

```
((and ,, chk) 1) true
```

## Full-blown (possibly a simpler formalization)

Parallel + Pick

How about deal with it in typing_application rule

If ambiougous happens, we distirbute, otherwise we pick.

# Problems

How it reflect in function overloading?

# Further

merge appears at arguments

