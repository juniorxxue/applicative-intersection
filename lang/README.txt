e ::= x
   |  n
   |  #t
   |  #f
   |  (λ (x : t) e t)
   |  (e1 e2)
   |  (m e1 e2)
   |  (: e t)
   |  (~> l e)
   |  (<~ e l)

t ::= int
   |  bool
   |  top
   |  (-> t1 t2)
   |  (& t1 t2)
   |  (* l t)


---------------------------------------------
Programming Idioms
---------------------------------------------

Beside parts in normal lambda calculus (variable, abstraction, and application),
function merges and record merges are a useful part in this language.

