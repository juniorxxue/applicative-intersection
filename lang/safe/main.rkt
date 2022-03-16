#lang racket

;; -----------------------------------------------------------------------
;; Bootstrap
;; -----------------------------------------------------------------------

(provide
  (except-out (all-from-out racket) #%module-begin #%app #%datum)
  (rename-out [module-begin #%module-begin]
              [app          #%app]
              [datum        #%datum])
  λ m : ~> <~)

(require
  (for-syntax
     racket/base
     syntax/stx
     syntax/parse))

(define-syntax-rule (module-begin expr ...)
  (#%module-begin
   expr ...))

(define-syntax (λ stx)
  (syntax-parse stx
    #:datum-literals (:)
    [(_ (x : A) e B) #'(eval '(λ (x : A) e B))]))

(define-syntax (: stx)
  (syntax-parse stx
    [(_ e A) #'(eval '(: e A))]))

(define-syntax (app stx)
  (syntax-parse stx
    [(_ e1 e2) #'(eval '(e1 e2))]))

(define-syntax (m stx)
  (syntax-parse stx
    #:datum-literals (m)
    [(_ e1 e2) #'(eval '(m e1 e2))]))

(define-syntax (datum stx)
  (syntax-parse stx
    [(_ . d) #'(eval 'd)]))       

(define-syntax (~> stx)
  (syntax-parse stx
    [(_ l e) #'(eval '(~> l e))]))

(define-syntax (<~ stx)
  (syntax-parse stx
    [(_ e l) #'(eval '(<~ e l))]))

(require racket/match)

;; -----------------------------------------------------------------------
;; Syntax
;; -----------------------------------------------------------------------

;; e ::= x                   variable
;;    |  n                   number
;;    |  #t                  true
;;    |  #f                  false
;;    |  (λ (x : t) e t)     abstraction
;;    |  (e1 e2)             application
;;    |  (m e1 e2)           merge operator
;;    |  (: e t)             annotation
;;    |  (~> l e)            record creation
;;    |  (<~ e l)            record projection

;; t ::= int                 integer type
;;    |  bool                boolean type
;;    |  top                 top type
;;    |  (-> t1 t2)          arrow type
;;    |  (& t1 t2)           intersection type
;;    |  (* l t)             record type

;; l ::= n                   label

;; -----------------------------------------------------------------------
;; Statics
;; -----------------------------------------------------------------------

(define (fail? t)
  (not t))

(define label?
  number?)  

(define (type? t)
  (match t
    ['int                         #t]
    ['bool                        #t]
    ['top                         #t]
    [`(-> ,(? type?) ,(? type?))  #t]
    [`(& ,(? type?) ,(? type?))   #t]
    [`(* ,(? label?) ,(? type?))  #t] ;; record type
    [_                            #f]))

(define (expr? e)
  (match e
    [(? symbol?)                                            #t]
    [(? number?)                                            #t]
    ['#t                                                    #t]
    ['#f                                                    #t]
    [`(λ (,(? symbol?) : ,(? type?)) ,(? expr?) ,(? type?)) #t]
    [`(,(? expr?) ,(? expr?))                               #t]
    [`(m ,(? expr?) ,(? expr?))                             #t]
    [`(: ,(? expr?) ,(? type?))                             #t]
    [`(~> ,(? label?) ,(? expr?))                           #t] ;; record term
    [`(<~ ,(? expr?) ,(? label?))                           #t] ;; record projection
    [_                                                      #f]))

(define/contract (ordinary? t)
  (-> type? boolean?)
  (match t
    ['int           #t]
    ['bool          #t]
    ['top           #t]
    [`(-> ,_ ,B)    (ordinary? B)]
    [`(* ,_ ,A)     (ordinary? A)]
    [_              #f]))

(define/contract (split t)
  (-> type? (listof type?))
  (match t
    [`(-> ,A ,(? (not/c ordinary?) B)) (let ([Bs (split B)])
                                         `((-> ,A ,(car Bs)) (-> ,A ,(cadr Bs))))]
    [`(* ,l ,(? (not/c ordinary?) A))  (let ([As (split A)])
                                         `((* ,l ,(car As)) (* ,l ,(cadr As))))]
    [`(& ,A ,B)                       `(,A ,B)]
    [_                                 (error "fail to split" t)]))

(define/contract (toplike? t)
  (-> type? boolean?)
  (match t
    ['top          #t]
    [`(-> ,A ,B)   (toplike? B)]
    [`(& ,A ,B)    (and (toplike? A) (toplike? B))]
    [`(* ,l ,A)    (toplike? A)]
    [_             #f]))

(define/contract (sub? t1 t2)
  (-> type? type? boolean?)
  (match* (t1 t2)
    [('int 'int)                     #t]
    [('bool 'bool)                   #t]    
    [(_ (? toplike?))                #t]
    [(`(* ,l ,A) `(* ,l ,B))         (sub? A B)]
    [(A (? (not/c ordinary?) B))     (let ([Bs (split B)])
                                       (and (sub? A (car Bs)) (sub? A (cadr Bs))))]
    [(`(& ,A1 ,A2) B)                (or (sub? A1 B) (sub? A2 B))]
    [(`(-> ,A1 ,A2) `(-> ,B1 ,B2))   (and (sub? B1 A1) (sub? A2 B2))]
    [(_ _)                           #f]))

(define/contract (appsub? s t)
  (-> (or/c symbol? type? label?) type? boolean?)
  (match* (s t)
    [('nil _)         #t]
    [(C `(-> ,A ,B))  (sub? C A)]
    [(l `(* ,l ,A))   #t]
    [(S `(& ,A ,B))   (appsub? S A)]
    [(S `(& ,A ,B))   (appsub? S B)]
    [(_ _)            #f]))

(define/contract (appsub s t)
  (-> (or/c symbol? type? label?) type? type?)
  (match* (s t)
    [('nil A) A]
    [(C `(-> ,A ,B)) #:when (sub? C A)           B]
    [(l `(* ,l ,A))                              A]
    [(S `(& ,A ,B))  #:when (not (appsub? S B))  (appsub S A)]
    [(S `(& ,A ,B))  #:when (not (appsub? S A))  (appsub S B)]
    [(S `(& ,A ,B))                             `(& ,(appsub S A) ,(appsub S B))]))

(define/contract (disjoint? t1 t2)
  (-> type? type? boolean?)
  (match* (t1 t2)
    [('top _) #t]
    [(_ 'top) #t]
    [(`(& ,A1 ,A2) B)                (and (disjoint? A1 B) (disjoint? A2 B))]
    [(A `(& ,B1 ,B2))                (and (disjoint? A B1) (disjoint? A B2))]
    [('int `(-> ,_ ,_))              #t]
    [(`(-> ,_ ,_) 'int)              #t]
    [('bool `(-> ,_ ,_))             #t]
    [(`(-> ,_ ,_) 'bool)             #t]
    [(`(-> ,A1 ,B1) `(-> ,A2 ,B2))   (disjoint? B1 B2)]
    [('int 'bool)                    #t]
    [('bool 'int)                    #t]
    [(`(* ,l1 ,A) `(* ,l2 ,B))       (if (equal? l1 l2) (disjoint? A B) #t)]
    [('int `(* ,_ ,_))               #t]
    [(`(* ,_ ,_) 'int)               #t]
    [('bool `(* ,_ ,_))              #t]
    [(`(* ,_ ,_) 'bool)              #t]
    [(`(-> ,_ ,_) `(* ,_ ,_))        #t]
    [(`(* ,_ ,_) `(-> ,_ ,_))        #t]
    [(_ _)                           #f]))

(define/contract (uvalue? e)
  (-> expr? boolean?)
  (match e
    [`(: ,e ,A)        #t]
    [`(m ,u1 ,u2)      (and (uvalue? u1) (uvalue? u2))]
    [`(~> ,l ,u)       (uvalue? u)]
    [_                 #f]))

(define/contract (consistent? e1 e2)
  (-> uvalue? uvalue? boolean?)
  (match* (e1 e2)
    [(`(: (λ (,x : ,A) ,e ,B1) ,C) `(: (λ (,x : ,A) ,e ,B2) ,D)) #t]
    [(`(: ,e ,A) `(: ,e ,B))                                     #t]
    [(`(~> ,l ,u1) `(~> ,l ,u2))                                 (consistent? u1 u2)]
    [(u1 u2) #:when (disjoint? (ptype u1) (ptype u2))            #t]
    [(`(m ,u1 ,u2) u)                                            (and (consistent? u1 u) (consistent? u2 u))]
    [(u `(m ,u1 ,u2))                                            (and (consistent? u u1) (consistent? u u2))]))

(define (lookup env var)
  (if (equal? (caar env) var)
      (cadar env)
      (lookup (cdr env) var)))

(define/contract (infer e env)
  (-> expr? list? type?)
  (match e    
    [(? number?)                                                     'int]
    ['#t                                                             'bool]
    ['#f                                                             'bool]
    [(? symbol?)                                                      (lookup env e)]
    [`(λ (,x : ,A) ,e ,B) #:when (check e B (cons `(,x ,A) env))     `(-> ,A ,B)]
    [`(~> ,l ,e)                                                     `(* ,l ,(infer e env))]
    [`(: ,e ,A) #:when (check e A env)                                A]
    [`(,e1 ,e2)                                                       (let ([A (infer e1 env)] [B (infer e2 env)])
                                                                        (appsub B A))]
    [`(<~ ,e ,l)                                                      (let ([A (infer e env)])
                                                                        (appsub l A))]
    [`(m ,(? uvalue? u1) ,(? uvalue? u2)) #:when (consistent? u1 u2)  (let ([A (infer u1 '())] [B (infer u2 '())])
                                                                        `(& ,A ,B))]
    [`(m ,e1 ,e2)                                                     (let ([A (infer e1 env)] [B (infer e2 env)])
                                                                        (if (disjoint? A B) `(& ,A ,B) #f))]
    [_                                                                (error "cannot infer the type of" e "under" env)]))

(define/contract (check e t env)
  (-> expr? type? list? boolean?)
  (let ([A (infer e env)])
    (sub? A t)))

;; -----------------------------------------------------------------------
;; Dynamics
;; -----------------------------------------------------------------------

(define/contract (pvalue? e)
  (-> expr? boolean?)
  (match e
    [(? number?)            #t]
    ['#t                    #t]
    ['#f                    #t]
    [`(λ (,x : ,A) ,e ,B)   #t]
    [_                      #f]))
    
(define/contract (value? e)
  (-> expr? boolean?)
  (match e
    [`(: ,p ,t)         (pvalue? p)]
    [`(~> ,l ,v)        (value? v)]
    [`(m ,v1 ,v2)       (and (value? v1) (value? v2))]
    [_                  #f]))

(define/contract (cast e t)
  (-> value? type? (or/c value? fail?))
  (match* (e t)
    [(`(: ,n ,A) 'int) #:when (sub? A 'int)                                       `(: ,n int)]
    [(`(: #t ,A) 'bool) #:when (sub? A 'bool)                                     '(: #t bool)]
    [(`(: #f ,A) 'bool) #:when (sub? A 'bool)                                     '(: #f bool)]
    [(v (? (and/c ordinary? toplike?) A))                                         `(: 1 ,A)]
    [(`(: (λ (,x : ,A) ,e ,B) ,E) `(-> ,C ,(? (and/c (not/c toplike?) ordinary?) D)))
     #:when (sub? E `(-> ,C ,D))                                                  `(: (λ (,x : ,A) ,e ,D) (-> ,C ,D))]
    [(`(~> ,l ,v) `(* ,l ,(? (and/c ordinary? (not/c toplike?)) A)))              `(~> ,l ,(cast v A))]
    [(`(m ,v1 ,v2) (? ordinary? A)) #:when (cast v1 A)                             (cast v1 A)]
    [(`(m ,v1 ,v2) (? ordinary? A)) #:when (cast v2 A)                             (cast v2 A)]
    [(v (? (not/c ordinary?) A))                                                   (let ([As (split A)])
                                                                                     `(m ,(cast v (car As)) ,(cast v (cadr As))))]
    [(_ _)                                                                         #f]))

(define/contract (subst e x u)
  (-> expr? symbol? expr? expr?)
  (match e
    [(? symbol? y)                     (if (equal? y x) u y)]
    [`(λ (,y : ,A) ,e ,B)             `(λ (,y : ,A) ,(if (equal? y x) e (subst e x u)) ,B)]
    [`(,e1 ,e2)                       `(,(subst e1 x u) ,(subst e2 x u))]
    [`(m ,e1 ,e2)                     `(m ,(subst e1 x u) ,(subst e2 x u))]
    [`(: ,e ,A)                       `(: ,(subst e x u) ,A)]
    [`(~> ,l ,e)                      `(~> ,l ,(subst e x u))]
    [`(<~ ,e ,l)                      `(<~ ,(subst e x u) ,l)]
    [_                                 e]))

(define/contract (ptype e)
  (-> expr? type?)
  (match e
    [(? number?)                    'int]
    ['#t                            'bool]
    ['#f                            'bool]
    [`(λ (,x : ,A) ,e ,B)           `(-> ,A ,B)]
    [`(~> ,l ,e)                    `(* ,l ,(ptype e))]
    [`(: ,e ,A)                      A]
    [`(m ,e1 ,e2)                   `(& ,(ptype e1) ,(ptype e2))]))

(define/contract (atype vl)
  (-> (or/c label? value?) (or/c label? type?))
  (match vl
    [`(: ,e ,A)                     A]
    [`(~> ,l ,e)                   `(* ,l ,(atype e))]
    [`(m ,e1 ,e2)                  `(& ,(atype e1) ,(atype e2))]
    [(? label? l)                   l]))
  
(define/contract (papp v vl)
  (-> value? (or/c label? value?) expr?)
  (match v
    [`(: ,n (-> ,A ,(? toplike? B)))                             `(: 1 ,B)]
    [`(: #t (-> ,A ,(? toplike? B)))                             `(: 1 ,B)]
    [`(: #f (-> ,A ,(? toplike? B)))                             `(: 1 ,B)]
    [`(: (λ (,x : ,A) ,e ,B) (-> ,C ,(? toplike? D)))            `(: 1 ,D)]
    [`(: ,n (* ,l ,(? toplike? A)))                              `(: 1 ,A)]
    [`(: #t (* ,l ,(? toplike? A)))                              `(: 1 ,A)]
    [`(: #f (* ,l ,(? toplike? A)))                              `(: 1 ,A)]
    [`(: (λ (,x : ,A) ,e ,B) (* ,l ,(? toplike? C)))             `(: 1 ,C)]
    [`(: (λ (,x : ,A) ,e ,B) (-> ,C ,(? (not/c toplike?) D)))    `(: ,(subst e x (cast vl A)) ,D)]
    [`(~> ,l ,v)  #:when (equal? l vl)                            v]
    [`(m ,v1 ,v2) #:when (not (appsub? (atype vl) (ptype v2)))    (papp v1 vl)]
    [`(m ,v1 ,v2) #:when (not (appsub? (atype vl) (ptype v1)))    (papp v2 vl)]
    [`(m ,v1 ,v2) #:when (and (appsub? (atype vl) (ptype v1))
                              (appsub? (atype vl) (ptype v1)))   `(m ,(papp v1 vl) ,(papp v2 vl))]))

;; possibly need not-value? as condition check
(define/contract (step e)
  (-> expr? expr?)
  (match e
    [(? number? n)                                  `(: ,n int)]
    ['#t                                            '(: #t bool)]
    ['#f                                            '(: #f bool)]                             
    [`(λ (,x : ,A) ,e ,B)                           `(: (λ (,x : ,A) ,e ,B) (-> ,A ,B))]
    [`(: ,(? pvalue? p) ,(? (not/c ordinary?) A))    (let ([As (split A)])
                                                       `(m (: ,p ,(car As)) (: ,p ,(cadr As))))]
    [`(<~ ,(? value? v) ,(? label? l))               (papp v l)]
    [`(<~ ,(? (not/c value?) e) ,(? label? l))      `(<~ ,(step e) ,l)]
    [`(~> ,(? label? l) ,(? (not/c value?) e))      `(~> ,l ,(step e))]
    [`(,(? value? v) ,(? value? vl))                 (papp v vl)]
    [`(: ,(? value? v) ,A)                           (cast v A)]
    [`(: ,(? (not/c pvalue?) e) ,A)                 `(: ,(step e) ,A)]
    [`(,(? (not/c value?) e1) ,e2)                  `(,(step e1) ,e2)]
    [`(,(? value? v) ,e2)                           `(,v ,(step e2))]
    [`(m ,e1 ,(? value? v))                         `(m ,(step e1) ,v)]
    [`(m ,(? value? v) ,e2)                         `(m ,v ,(step e2))]
    [`(m ,e1 ,e2)                                   `(m ,(step e1) ,(step e2))]))

(define/contract (eval e)
  (-> expr? value?)
  (when (infer e '())
    (if (value? e) e (eval (step e)))))