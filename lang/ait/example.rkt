#lang s-exp "main.rkt"

;; simple literals
42
#t
#f

;; lambda abstraction
(λ (x : int) x int)

;; function application
((λ (x : int) x int) 1)

;; record creation, for simplity, we use number to represent label
(~> 42 #t)

;; record projection
(<~ (~> 42 #t)
    42)

;; merge two disjoint values
(m 1 #t)

;; merge two functions
(m (λ (x : int) x int)
   (λ (x : bool) x bool))

;; merged function can be applied
((m (λ (x : int) x int)
    (λ (x : bool) x bool))
 1)

;; merge two records
(m (~> 1 #t)
   (~> 2 #f))

;; merged records can be selected by label
(<~ (m (~> 1 #t)
       (~> 2 #f))
    1)
   
;; merged arguments can also be automatically selected
((λ (x : int) x int)
 (m 1 #t))

;; a expression can be annotated
(: (λ (x : int) x int) (-> int int))

;; annotate a value can force a downcast/upcast
(: (: 1 int)
   (& int int)) ;; => generate a duplicate number

(: (: (λ (x : int) x int) (-> int int))
   (& (-> int int)
      (-> int int))) ;; => generate a duplicate function

(: (m (λ (x : int) x int)
      (λ (x : bool) x bool))
   (-> bool bool)) ;; => downcast to a boolean identity function