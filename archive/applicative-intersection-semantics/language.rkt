#lang racket
(require redex)

;; this file is a prefix version
;; NOTE

(define-syntax-rule (draw x) (show-derivations (build-derivations x)))
(define-syntax-rule (holds x) (judgment-holds x))
(define-syntax-rule (reduce x) (apply-reduction-relation step (term x)))
(define-syntax-rule (reduces x) (apply-reduction-relation* step (term x)))

(define-language L
  (x ::= variable-not-otherwise-mentioned)
  (e ::= number top false true x (lambda (x) e) (e e) (doublecomma e e) (: e tau))
  (tau ::= int bool top (-> tau tau) (& tau tau))
  (Gamma ::= ((x tau) ...))
  (Psi ::= (tau ...))
  (p ::= top true false number (lambda (x) e))
  (v ::= (: p tau) (lambda (x) e) (: (doublecomma (: p_1 tau_1)
                                 (: p_2 tau_2))
                              (& tau_1 tau_2)))
  (E ::= hole (E e) (v E))
  #:binding-forms
  (lambda (x) e :refers-to x)
  )

(define-judgment-form L
  #:mode (sub I I)
  #:contract (sub tau tau)
  [-------------------- "sub-int"
   (sub int int)]
  [-------------------- "sub-bool"
   (sub bool bool)]
  [-------------------- "sub-top"
   (sub tau top)]
  [(sub tau_3 tau_1)
   (sub tau_2 tau_4)
   -------------------- "sub-arrow"
   (sub (-> tau_1 tau_2) (-> tau_3 tau_4))]
  [(sub top tau_3)
   -------------------- "sub-top-arrow"
   (sub tau_1 (tau_2 tau_3))]
  [(sub tau_1 tau_2)
   (sub tau_1 tau_3)
   -------------------- "sub-and"
   (sub tau_1 (& tau_2 tau_3))]
  [(sub tau_1 tau_3)
   -------------------- "sub-andl"
   (sub (& tau_1 tau_2) tau_3)]
  [(sub tau_2 tau_3)
   -------------------- "sub-andr"
   (sub (& tau_1 tau_2) tau_3)])

(define-judgment-form L
  #:mode (appsub I I O)
  #:contract (appsub Psi tau tau)
  [-------------------- "appsub-refl"
   (appsub () tau tau)]
  [(sub tau_3 tau_1)
   (appsub (tau ...) tau_2 tau_4)
   -------------------- "appsub-fun"
   (appsub (tau ... tau_3) (-> tau_1 tau_2) (-> tau_3 tau_4))]
  [(appsub (tau tau_4 ...) tau_1 tau_3)
   -------------------- "appsub-andl"
   (appsub (tau tau_4 ...) (& tau_1 tau_2) tau_3)]
  [(appsub (tau tau_4 ...) tau_2 tau_3)
   -------------------- "appsub-andr"
   (appsub (tau tau_4 ...) (& tau_1 tau_2) tau_3)]
  )


(define-judgment-form L
  #:mode (lookup I I O)
  #:contract (lookup ((any any) ...) any any)
  [(lookup (_ ... (any any_1) _ ...) any any_1)])


(define-judgment-form L
  #:mode (disjoint I I)
  #:contract (disjoint tau tau)
  [---------------------------------- "disjoint-top-l"
   (disjoint top tau)]
  [---------------------------------- "disjoint-top-r"
   (disjoint tau top)]
  [---------------------------------- "disjoint-int-bool"
   (disjoint int bool)]
  [---------------------------------- "disjoint-bool-int"
   (disjoint bool int)]
  [---------------------------------- "disjoint-int-arr"
   (disjoint int (-> tau_1 tau_2))]
  [---------------------------------- "disjoint-arr-int"
   (disjoint (-> tau_1 tau_2) int)]
  [---------------------------------- "disjoint-bool-arr"
   (disjoint bool (-> tau_1 tau_2))]
  [---------------------------------- "disjoint-arr-bool"
   (disjoint (-> tau_1 tau_2) bool)]
  [(disjoint tau_2 tau_4)
   ---------------------------------- "disjoint-arr"
   (disjoint (-> tau_1 tau_2) (-> tau_3 tau_4))]
  [(disjoint tau_1 tau_3)
   (disjoint tau_2 tau_3)
   ---------------------------------- "disjoint-and-l"
   (disjoint (& tau_1 tau_2) tau_3)]
  [(disjoint tau_1 tau_2)
   (disjoint tau_1 tau_3)
   ---------------------------------- "disjoint-and-r"
   (disjoint tau_1 (& tau_2 tau_3))]
  )


(define-metafunction L
  ext1 : ((any any) ...) (any any) -> ((any any) ...)
  [(ext1 (any_1 ... (any_2 any_3) any_4 ...) (any_2 any_5)) (any_1 ... (any_2 any_5) any_4 ...)]
  [(ext1 (any_1 ...) (any_2 any_3) ) ((any_2 any_3) any_1 ...)])

(define-metafunction L
  ext : ((any any) ..) (any any) ... -> ((any any) ...)
  [(ext any) any]
  [(ext any any_1 any_2 ...) (ext1 (ext any any_2 ...) any_1)])

(define-judgment-form L
  #:mode (infer I I I I O)
  #:contract (infer Gamma Psi e => tau)
  [---------------------------------- "typing-int"
   (infer Gamma ()  number => int)]
  [---------------------------------- "typing-top"
   (infer Gamma () top => top)]
  [---------------------------------- "typing-true"
   (infer Gamma () true => bool)]
  [---------------------------------- "typing-false"
   (infer Gamma () false => bool)]
  [(lookup Gamma x tau)
   ---------------------------------- "typing-var"
   (infer Gamma () x => tau)]
  [(infer (ext Gamma (x tau_1)) (tau ...) e => tau_2)
   ---------------------------------- "typing-lam-2"
   (infer Gamma (tau ... tau_1) (lambda (x) e) => (-> tau_1 tau_2))]
  [(appsub Psi tau_1 tau_2)
   (check Gamma () e <= tau_1)
   ---------------------------------- "typing-anno"
   (infer Gamma Psi (: e tau_1) => tau_2)]
  [(infer Gamma () e_2 => tau_1)
   (infer Gamma (tau ... tau_1) e_1 => (-> tau_1 tau_2))
   ---------------------------------- "typing-app-1"
   (infer Gamma (tau ...) (e_1 e_2) => tau_2)]
  [(infer Gamma () e_1 => tau_1)
   (infer Gamma () e_2 => tau_2)
   (disjoint tau_1 tau_2)
   ---------------------------------- "typing-merge"
   (infer Gamma () (doublecomma e_1 e_2) => (& tau_1 tau_2))]
  )

(define-judgment-form L
  #:mode (check I I I I I)
  #:contract (check Gamma Psi e <= tau)
  [(check (ext Gamma (x tau_1)) () e <= tau_2)
   ---------------------------------- "typing-lam-1"
   (check Gamma () (lambda (x) e) <= (-> tau_1 tau_2))]
  [(infer Gamma () e_2 => tau_1)
   (check Gamma () e_1 <= (-> tau_1 tau_2))
   ---------------------------------- "typing-app-2"
   (check Gamma () (e_1 e_2) <= tau_2)]
  [(infer Gamma () e => tau_2)
   (sub tau_2 tau_1)
   ---------------------------------- "typing-sub"
   (check Gamma () e <= tau_1)]
  )

#;(redex-match L v (term (: (doublecomma (: (lambda (x) x)
                                (-> int int))
                             (: (lambda (x) x)
                                (-> bool bool)))
                          (& (-> int int)
                             (-> bool bool)))))

(define-judgment-form L
  #:mode (ordinary I)
  #:contract (ordinary tau)
  [---------------------------------- "ord-top"
   (ordinary top)]
  [---------------------------------- "ord-int"
   (ordinary int)]
  [---------------------------------- "ord-arrow"
   (ordinary (-> tau_1 tau_2))])

(define-judgment-form L
  #:mode (toplike I)
  #:contract (toplike tau)
  [---------------------------------- "tl-top"
   (toplike top)]
  [(toplike tau_1)
   (toplike tau_2)
   ---------------------------------- "tl-and"
   (toplike (& tau_1 tau_2))]
  [(toplike tau_2)
   ---------------------------------- "tl-arrow"
   (toplike (-> tau_1 tau_2))]
  )

(define-judgment-form L
  #:mode (tred I I O)
  #:contract (tred v tau v)
  [---------------------------------- "tred-int"
   (tred (: number int) int (: number int))]
  [---------------------------------- "tred-true"
   (tred (: true bool) bool (: true bool))]
  [---------------------------------- "tred-false"
   (tred (: false bool) bool (: false bool))]
  [(ordinary tau)
   (toplike tau)
   ---------------------------------- "tred-top"
   (tred e tau (: top top))]
  [(side-condition (not (judgment-holds (toplike tau_3))))
   (sub tau_3 tau_1)
   (sub tau_2 tau_4)
   ---------------------------------- "tred-arr-anno"
   (tred (: (lambda (x) e) (-> tau_1 tau_2))
         (-> tau_3 tau_4)
         (: (lambda (x) e) (-> tau_1 tau_4)))]
  [(tred e_1 tau_2 e_3)
   (ordinary tau_2)
   ---------------------------------- "tred-merge-l"
   (tred (: (doublecomma e_1 e_2) tau_1)
         tau_2
         e_3)]
  [(tred e_2 tau_2 e_3)
   (ordinary tau_2)
   ---------------------------------- "tred-merge-r"
   (tred (: (doublecomma e_1 e_2) tau_1)
         tau_2
         e_3)]
  [(tred e tau_1 e_1)
   (tred e tau_2 e_2)
   ---------------------------------- "tred-and"
   (tred e
         (& tau_1 tau_2)
         (: (doublecomma e_1 e_2) (& tau_1 tau_2)))]
  )

(define-judgment-form L
  #:mode (papp I I O)
  #:contract (papp v v e)
  [---------------------------------- "papp-abs"
                                      (papp (lambda (x) e) v (substitute e x v))]
  [(tred v_1 tau_1 v_2)
   ---------------------------------- "papp-abs-anno"
   (papp (: (lambda (x) e)
            (-> tau_1 tau_2))
         v_1
         (: (substitute e x v_2)
            tau_2))]
  [---------------------------------- "papp-top"
   (papp top v top)]
  [(appsub (tau_3) (& tau_1 tau_2) tau_4)
   (tred (: (doublecomma (: p_1 tau_1)
               (: p_2 tau_2))
            (& tau_1 tau_2))
         tau_4
         v)
   (papp v (: p tau_3) e)
   ---------------------------------- "papp-merge"
   (papp (: (doublecomma (: p_1 tau_1)
               (: p_2 tau_2))
            (& tau_1 tau_2))
         (: p tau_3)
         e)]
  )

(define step
  (reduction-relation
   L
   #:domain e
   #:codomain e
   (--> number (: number int)
        "step-int-anno")
   (--> true (: true bool)
        "step-true-anno")
   (--> false (: false bool)
        "step-false-anno")
   (--> top (: top top)
        "step-top-anno")
   (--> (v_1 v_2) e
        (side-condition (judgment-holds (papp v_1 v_2 e)))
        (where e ,(first (judgment-holds (papp v_1 v_2 e) e)))
        "step-beta")
   (--> (doublecomma (: p_1 tau_1)
           (: p_2 tau_2))
        (: (doublecomma (: p_1 tau_1)
              (: p_2 tau_2))
           (& tau_1 tau_2))
        "step-merge-anno")
   (--> (: v_1 tau) v_2
        (side-condition  (judgment-holds (tred v_1 tau v_2)))
        (where v_2 ,(first (judgment-holds (tred v_1 tau v) v)))
        "step-anno-value")
   ))

;; (define -->r (compatible-closure step L e))
(define -->n (context-closure step L E))

#;(judgment-holds (papp (: (doublecomma (: (lambda (x) x)
                               (-> int int))
                            (: (lambda (x) true)
                               (-> bool bool)))
                         (& (-> int int)
                            (-> bool bool)))
                      (: 4 int)
                      e) e)

#;(apply-reduction-relation* -->n
                             (term ((: (doublecomma (: (lambda (x) x)
                                           (-> int int))
                                        (: (lambda (x) true)
                                           (-> bool bool)))
                                     (& (-> int int)
                                        (-> bool bool)))
                                  4)))
