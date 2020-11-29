#lang racket
(require redex)
(define-language AppL
  (e ::=
     n ;; int
     x ;; variable
     (λ x e) ;; abstraction
     (e e) ;; application
     (e ◇ e) ;; merge
     (x τ) ;; annotation
     )
  (n ::=
     number)
  (A B C D ::=
     Int ;; int type
     Top ;; top type
     (A → B) ;; function type
     (A & B) ;; intersection type
     )
  (x ::= variable-not-otherwise-mentioned))

(define-judgment-form AppL
  #:mode (subtype I I)
  #:contract (subtype A B)
  [--------------- sub_int
   (subtype Int Int)]
  [--------------- sub_top
   (subtype A Top)]
  [(subtype C A)
   (subtype B D)
   ------------------------ sub_arrow
   (subtype (A → B) (C → D))]
  [(subtype A B)
   (subtype A C)
   --------------------- sub_and
   (subtype A (B & C))]
  [(subtype A C)
   --------------------- sub_andl
   (subtype (A & B) C)]
  [(subtype B C)
   --------------------- sub_andr
   (subtype (A & B) C)])
   
     