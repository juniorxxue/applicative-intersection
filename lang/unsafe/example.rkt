#lang s-exp "main.rkt"

;; it provides a more genearal form of overloaded functions, any functions can be merged
;; but removal of disjointness would break type safety

;; this is not allowed in safe version
((m (λ (x : int) #t bool)
    (λ (x : bool) #f bool))
 1)