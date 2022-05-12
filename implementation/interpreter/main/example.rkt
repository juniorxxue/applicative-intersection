#lang s-exp "main.rkt"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; TODO ;;;;;;;;;;;;;;;;;;
;; 1. better error message
;; 2. define or let-binding
;; 3. better lambda-syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; simple literals
42
42.2
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

;; merge two values
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
(: (λ (x : int) x int)
   (-> int int))

;; annotate a "value" can force a downcast/upcast
(: (: 1 int)
   (& int int)) ;; => duplicate a number

(: (: (λ (x : int) x int) (-> int int))
   (& (-> int int)
      (-> int int))) ;; => duplicate a function

(: (m (λ (x : int) x int)
      (λ (x : bool) x bool))
   (-> bool bool)) ;; => downcast to a boolean identity function

;; we introduce some primitives: int+ and flo+

;; use int+ to add integers
(int+ 1 3)
;; use flo+ to add floats
(flo+ 1.0 2.1)

((λ (x : int) (int+ x x) int) 1)
((λ (x : float) (flo+ x x) float) 1.1)

;; overload int and flo+ to create a polymorphic "double" function

((m (λ (x : int) (int+ x x) int)
    (λ (x : float) (flo+ x x) float))
 1)

;; variadic version of merge operator
(<~ (M (~> 1 #t)
       (~> 2 #f)
       (~> 3 #t))
    2)

;; another syntactic sugar for records
(R (1 1) (43 43) (99 99))

(<~ (R (1 1) (43 43) (99 99))
    99)