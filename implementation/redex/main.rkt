#lang racket
(require redex)
(require rackunit)

(define-language λi+
  (x ::= variable-not-otherwise-mentioned)
  (n ::= number)
  ;; types
  (A B C D E ::= Int Top (→ A B) (& A B))
  ;; ordinary types
  (Ao Bo Co Do ::= Int Top (→ A Bo))
  ;; terms
  (e ::= n x (λ (x : A) e B) (: e A) (e e) (M e e))
  ;; values
  (p ::= n (λ (x : A) e B))
  (v ::= (: p Ao) (M v v))
  ;; evaluation contexts
  (♦ ::= hole (v ♦) (♦ e) (M v ♦) (M e ♦))
  ;; outputs
  (O ::= fail A)
  ;; context
  (Γ ::= ((x A) ...))
  #:binding-forms
  (λ (x : A) e B :refers-to x))


(define-judgment-form λi+
  #:mode (split I O O)
  #:contract (split A A A)
  [--------------------------- "Sp-And"
   (split (& A B) A B)]
  [(split B B_1 B_2)
   -------------------------------- "Sp-Arr"
   (split (→ A B) (→ A B_1) (→ A B_2))])

(check-true (judgment-holds (split (& Int Int) Int Int)))
(check-true (judgment-holds (split (→ Int (& Int Int))
                                   (→ Int Int)
                                   (→ Int Int))))

(define-judgment-form λi+
  #:mode (sub? I I)
  #:contract (sub? A A)
  [------------------------ "S-Int"
   (sub? Int Int)]
  [------------------------ "S-Top"
   (sub? A Top)]
  [(sub? C A)
   (sub? B Do)
   ------------------------- "S-Arr"
   (sub? (→ A B) (→ C Do))]
  [(split B B_1 B_2)
   (sub? A B_1)
   (sub? A B_2)
   ------------------------- "S-And"
   (sub? A B)]
  [(sub? A Co)
   ------------------------- "S-And-L"
   (sub? (& A B) Co)]
  [(sub? B Co)
   ------------------------- "S-And-R"
   (sub? (& A B) Co)])

(check-true (judgment-holds (sub? Int (& Int Int))))
(check-true (judgment-holds (sub? (→ Int Int) (→ Int (& Int Int)))))

(define-judgment-form λi+
  #:mode (combine I I O)
  #:contract (combine O O O)
  [--------------------------- "CB-FF"
   (combine fail fail fail)]
  [--------------------------- "CB-SF"
   (combine A_1 fail A_1)]
  [--------------------------- "CB-FS"
   (combine fail A_2 A_2)]
  [----------------------------- "CB-SS"
   (combine A_1 A_2 (& A_1 A_2))])

(define-judgment-form λi+
  #:mode (appsub I I O)
  #:contract (appsub A A O)
  [(sub? B A_1)
   ----------------------------- "As-Arr"
   (appsub (→ A_1 A_2) B A_2)]
  [(side-condition ,(not (judgment-holds (sub? B A_1))))
   ----------------------------------------------------- "As-Arr-F"
   (appsub (→ A_1 A_2) B fail)]
  [(appsub A_1 B O_1)
   (appsub A_2 B O_2)
   (combine O_1 O_2 O)
   -------------------------------------------- "As-And"
   (appsub (& A_1 A_2) B O)])

;; Int -> Int <: Int -> ?
(check-equal? (judgment-holds (appsub (→ Int Int) Int A) A)
              '(Int))
;; (Int -> Int) & ((Int -> Int) -> Top) <: Int -> ?
(check-equal? (judgment-holds (appsub (& (→ Int Int) (→ (→ Int Int) Top))
                        Int A) A)
              '(Int))
;; (Int -> Int) & ((Int -> Int) -> Top) <: (Int -> Int) -> ?            
(check-equal? (judgment-holds (appsub (& (→ Int Int) (→ (→ Int Int) Top))
                        (→ Int Int) A) A)
              '(Top))

(define-judgment-form λi+
  #:mode (lookup I I O)
  #:contract (lookup ((any any) ...) any any)
  [(lookup (_ ... (any any_1) _ ...) any any_1)])

(define-metafunction λi+
  ext1 : ((any any) ...) (any any) -> ((any any) ...)
  [(ext1 (any_0 ... (any_k any_v0) any_1 ...) (any_k any_v1))
   (any_0 ... (any_k any_v1) any_1 ...)]
  [(ext1 (any_0 ...) (any_k any_v1))
   ((any_k any_v1) any_0 ...)])

(define-metafunction λi+
  ext : ((any any) ...) (any any) ... -> ((any any) ...)
  [(ext any) any]
  [(ext any any_0 any_1 ...)
   (ext1 (ext any any_1 ...) any_0)])

(define-judgment-form λi+
  #:mode (infer I I O)
  #:contract (infer Γ e A)
  [------------------------ "T-Int"
   (infer Γ n Int)]
  [(lookup Γ x A)
   ----------------------- "T-Var"
   (infer Γ x A)]
  [(check (ext Γ (x A)) e B)
   ----------------------------------- "T-Lam"
   (infer Γ (λ (x : A) e B) (→ A B))]
  [(infer Γ e_1 A)
   (infer Γ e_2 B)
   (appsub A B C)
   ---------------------------------- "T-App"
   (infer Γ (e_1 e_2) C)]
  [(infer Γ e_1 A)
   (infer Γ e_2 B)
   ----------------------------- "T-Mrg"
   (infer Γ (M e_1 e_2) (& A B))]
  [(check Γ e A)
   ------------------------------- "T-Ann"
   (infer Γ (: e A) A)])

(define-judgment-form λi+
  #:mode (check I I I)
  #:contract (check Γ e A)
  [(infer Γ e A)
   (sub? A B)
   ------------------------- "T-Sub"
   (check Γ e B)])

(check-equal? (judgment-holds (infer () 2 A) A) '(Int))
(check-equal? (judgment-holds (infer ((x Int) (y Top)) x A) A) '(Int))

(judgment-holds
 (infer () (M (λ (x : Int) x Int)
              (λ (x : (→ Int Int)) x (→ Int Int)))             
        A) A)

(judgment-holds
 (infer () ((λ (x : Int) x Int) 1) A) A)

;; id-int : Int -> Int
;; id-fun : (Int -> Int) -> (Int -> Int)
;; . |- id-int,,id-fun 1 => Int
(judgment-holds
 (infer () ((M (λ (x : Int) x Int)
              (λ (x : (→ Int Int)) x (→ Int Int)))
            1)
        A) A)

(define-judgment-form λi+
  #:mode (cast I I O)
  #:contract (cast v A v)
  [------------------------------ "Ct-Int"
   (cast (: n A) Int (: n Int))]
  [----------------------------- "Ct-Top"
   (cast v Top (: 42 Top))]
  [(sub? E (→ C Do))
   ----------------------------------------------------------------- "Ct-Arr"
   (cast (: (λ (x : A) e B) E) (→ C Do) (: (λ (x : A) e Do) (→ C Do)))]
  [(cast v_1 Ao v_1_)
   ------------------------------ "Ct-Mrg-L"
   (cast (M v_1 v_2) Ao v_1_)]
  [(cast v_2 Ao v_2_)
   ------------------------------ "Ct-Mrg-R"
   (cast (M v_1 v_2) Ao v_2_)]
  [(split A A_1 A_2)
   (cast v A_1 v_1)
   (cast v A_2 v_2)
  -------------------------------- "Ct-And"
  (cast v A (M v_1 v_2))])


(judgment-holds (cast (: 1 Int) (& Int Int) v) v)

(define-metafunction λi+
  dynt : v -> A
  [(dynt (: e A)) A]
  [(dynt (M e_1 e_2)) (& (dynt e_1) (dynt e_2))])

(define-metafunction λi+
  [(equal O_1 O_1) #t]
  [(equal O_1 O_2) #f])

(define-judgment-form λi+
  #:mode (dispatch I I O)
  #:contract (dispatch v v e)
  [(cast v A v_)
   -------------------------------------------------- "App-Lam"
   (dispatch (: (λ (x : A) e B) (→ C D)) v
             (: (substitute e x v_) D))]
  [(appsub (dynt v_2) (dynt v) A)
   (side-condition ,(equal? (term A) 'fail))
   (dispatch v_1 v e)
   ---------------------------------------- "App-Mrg-L"
   (dispatch (M v_1 v_2) v e)]
  [(appsub (dynt v_1) (dynt v) A)
   (side-condition ,(equal? (term A) 'fail))
   (dispatch v_2 v e)
   ---------------------------------------- "App-Mrg-R"
   (dispatch (M v_1 v_2) v e)]
  [(appsub (dynt v_1) (dynt v) A)
   (appsub (dynt v_2) (dynt v) B)
   (dispatch v_1 v e_1)
   (dispatch v_2 v e_2)
   ---------------------------------------- "App-Mrg-P"
   (dispatch (M v_1 v_2) v (M e_1 e_2))])

(judgment-holds (dispatch (: (λ (x : Int) x Int) (→ Int Int))
                          (: 1 Int)
                          e)
                e)

(judgment-holds (dispatch (M (: (λ (x : Int) x Int) (→ Int Int))
                             (: (λ (x : (→ Int Int)) x (→ Int Int)) (→ (→ Int Int) (→ Int Int))))
                          (M (: 1 Int)
                             (: (λ (x : Int) x Int) (→ Int Int)))
                          e)
                e)