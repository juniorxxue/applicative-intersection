#lang racket
(require redex)

(define-language λi
  (x ::= variable-not-otherwise-mentioned)
  (e ::= number false x (λ (x : A) e) (e e) (* e e) (: e A))
  (A B C D E ::= int bool top (→ A B) (& A B))
  (Γ ::= ((x A) ...))
  (Ψ ::= (A ...))
  #:binding-forms
  (λ (x : A) e :refers-to x))

(define-judgment-form λi
  #:mode (≤ I I)
  #:contract (≤ A A)
  [-------------------- "sub-int"
   (≤ int int)]
  [-------------------- "sub-bool"
   (≤ bool bool)]
  [-------------------- "sub-top"
   (≤ A top)]
  [(≤ C A)
   (≤ B D)
   -------------------- "sub-arrow"
   (≤ (→ A B) (→ C D))]
  [(≤ top C)
   -------------------- "sub-top-arrow"
   (≤ A (→ B C))]
  [(≤ A B)
   (≤ A C)
   -------------------- "sub-and"
   (≤ A (& B C))]
  [(≤ A C)
   -------------------- "sub-andl"
   (≤ (& A B) C)]
  [(≤ B C)
   -------------------- "sub-andr"
   (≤ (& A B) C)])

(define-judgment-form λi
  #:mode (appsub? I I)
  #:contract (appsub? Ψ B)
  [-------------------------"as?-refl"
   (appsub? () A)]
  [(≤ C A)
   (appsub? (E ...) B)
   ------------------------ "as?-fun"
   (appsub? (E ... C) (→ A B))]
  [(appsub? (E ... C) A)
   ------------------------ "as?-and-l"
   (appsub? (E ... C) (& A B))]
  [(appsub? (E ... C) B)
   ------------------------ "as?-and-r"
   (appsub? (E ... C) (& A B))])


(define-judgment-form λi
  #:mode (appsub I I O)
  #:contract (appsub Ψ A B)
  [-------------------- "as-refl"
   (appsub () A A)]
  [(≤ C A)
   (appsub (E ...) B D)
   -------------------- "as-fun"
   (appsub (E ... C) (→ A B) (→ C D))]
  [(appsub? (E ... C) A)
   (side-condition (not (judgment-holds (appsub? (E ... C) B))))
   -------------------- "as-and-l"
   (appsub (E ... C) (& A B) A)]
  [(appsub? (E ... C) B)
   (side-condition (not (judgment-holds (appsub? (E ... C) A))))
   -------------------- "as-and-r"
   (appsub (E ... C) (& A B) B)]
  [(appsub? (E ... C) A)
   (appsub? (E ... C) B)
   -------------------- "as-and-both"
   (appsub (E ... C) (& A B) (& A B))]
  )

(define-judgment-form λi
  #:mode (lookup I I O)
  #:contract (lookup ((any any) ...) any any)
  [(lookup (_ ... (any any_1) _ ...) any any_1)])


(define-judgment-form λi
  #:mode (disjoint I I)
  #:contract (disjoint A A)
  [---------------------------------- "disjoint-top-l"
   (disjoint top A)]
  [---------------------------------- "disjoint-top-r"
   (disjoint A top)]
  [---------------------------------- "disjoint-int-bool"
   (disjoint int bool)]
  [---------------------------------- "disjoint-bool-int"
   (disjoint bool int)]
  [---------------------------------- "disjoint-int-arr"
   (disjoint int (→ A B))]
  [---------------------------------- "disjoint-arr-int"
   (disjoint (→ A B) int)]
  [---------------------------------- "disjoint-bool-arr"
   (disjoint bool (→ A B))]
  [---------------------------------- "disjoint-arr-bool"
   (disjoint (→ A B) bool)]
  [(disjoint B D)
   ---------------------------------- "disjoint-arr"
   (disjoint (→ A B) (→ C D))]
  [(disjoint A C)
   (disjoint B C)
   ---------------------------------- "disjoint-and-l"
   (disjoint (& A B) C)]
  [(disjoint A B)
   (disjoint A C)
   ---------------------------------- "disjoint-and-r"
   (disjoint A (& B C))]
  )

(define-metafunction λi
    ext1 : ((any any) ...) (any any) -> ((any any) ...)
    [(ext1 (any_0 ... (any_k any_v0) any_1 ...) (any_k any_v1))
     (any_0 ... (any_k any_v1) any_1 ...)]
    [(ext1 (any_0 ...) (any_k any_v1))
     ((any_k any_v1) any_0 ...)])

(define-metafunction λi
    ext : ((any any) ...) (any any) ... -> ((any any) ...)
    [(ext any) any]
    [(ext any any_0 any_1 ...)
     (ext1 (ext any any_1 ...) any_0)])

(define-judgment-form λi
  #:mode (infer I I I I I O)
  #:contract (infer Γ Ψ ⊢ e ⇒ A)
  [---------------------------------- "typing-int"
   (infer Γ () ⊢ number ⇒ int)]
  [---------------------------------- "typing-true"
   (infer Γ () ⊢ true ⇒ bool)]
  [---------------------------------- "typing-false"
   (infer Γ () ⊢ false ⇒ bool)]
  [(lookup Γ x A)
   ---------------------------------- "typing-var"
   (infer Γ () ⊢ x ⇒ A)]
  [(infer (ext Γ (x A)) () ⊢ e ⇒ B)
   ---------------------------------- "typing-lam-1"
   (infer Γ () ⊢ (λ (x : A) e) ⇒ (→ A B))]
  [(infer (ext Γ (x A)) (E ...) ⊢ e ⇒ B)
   (≤ C A)
   ---------------------------------- "typing-lam-2"
   (infer Γ (E ... C) ⊢ (λ (x : A) e) ⇒ (→ A B))]
  [(infer Γ () ⊢ e ⇒ C)
   (≤ C A)
   (appsub Ψ A B)
   ---------------------------------- "typing-ann"
   (infer Γ Ψ ⊢ (: e A) ⇒ B)]
  [(infer Γ () ⊢ e_2 ⇒ A)
   (infer Γ (E ... A) ⊢ e_1 ⇒ (→ A B))
   ---------------------------------- "typing-app"
   (infer Γ (E ...) ⊢ (e_1 e_2) ⇒ B)]
  [(infer Γ () ⊢ e_1 ⇒ A)
   (infer Γ () ⊢ e_2 ⇒ B)
   (disjoint A B)
   ---------------------------------- "typing-merge"
   (infer Γ () ⊢ (* e_1 e_2) ⇒ (& A B))]
  [(infer Γ () ⊢ (* e_1 e_2) ⇒ B)
   (appsub (E ... A) B C)
   ---------------------------------- "typing-merge-pick"
   (infer Γ (E ... A) ⊢ (* e_1 e_2) ⇒ C)]
  )

(define-syntax-rule (draw-type x) (show-derivations (build-derivations (infer () () ⊢ x ⇒ A))))
(define-syntax-rule (holds? x) (judgment-holds x))
(define-syntax-rule (type? x) (judgment-holds (infer () () ⊢ x ⇒ A) A))
(define-syntax-rule (compute-as s t) (judgment-holds (appsub s t A) A))

(type? (* (λ (x : int) x)
          (λ (x : bool) x)))

(type? ((* (λ (x : int) x)
           (λ (x : bool) x)) 1))

(type? ((: (* (λ (x : int) x)
              (λ (x : bool) x))
           (→ int int))
        1))

#;(draw-type ((: (* (λ (x : int) x)
                    (λ (x : bool) x))
                 (→ int int))
              1))

(compute-as (int) (& (→ int int)
                     (→ int bool)))

(compute-as (int) (& (→ int int)
                     (→ bool bool)))
(compute-as (int) (& (→ bool int)
                     (→ int bool)))