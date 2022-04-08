This proposal is about new rules for disjointness (operate disjoint on functions (input types))

which allows for showInt,,showBool

showInt : Int -> String
showBool : Bool -> String

but reject succ,,pred

succ : Int -> String
pred : Int -> String


T |- e1 => A
T |- e2 => B
A ** B
----------------------
T |- e1 ,, e2 => A & B



------------------------
Overloadable A ** B
------------------------

~ (A1 |-| A2)
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
