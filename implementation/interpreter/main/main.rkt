#lang racket

;; -----------------------------------------------------------------------
;; Bootstrap
;; -----------------------------------------------------------------------

(provide
  (except-out (all-from-out racket) #%module-begin #%app #%datum)
  (rename-out [module-begin #%module-begin]
              [app          #%app]
              [datum        #%datum])
  λ m M R : ~> <~ int+ flo+)

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

(define-syntax (M stx)
  (syntax-parse stx
    [(_ e ...) #'(eval '(M e ...))]))

(define-syntax (R stx)
  (syntax-parse stx
    [(_ e ...) #'(eval '(R e ...))]))

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

(define-syntax (int+ stx)
    (syntax-parse stx
      [(_ e1 e2) #'(eval '(int+ e1 e2))]))

(define-syntax (flo+ stx)
    (syntax-parse stx
      [(_ e1 e2) #'(eval '(flo+ e1 e2))]))

(require racket/match)

;; -----------------------------------------------------------------------
;; Syntax
;; -----------------------------------------------------------------------

;; e ::= x                   variable
;;    |  n                   number (integer, float)
;;    |  s                   string
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
  (equal? t #f))

(define label?
  number?)  

(define (type? t)
  (match t
    ['int                         #t]
    ['float                       #t]
    ['bool                        #t]
    ['top                         #t]
    [`(-> ,(? type?) ,(? type?))  #t]
    [`(& ,(? type?) ,(? type?))   #t]
    [`(* ,(? label?) ,(? type?))  #t] ;; record type
    [_                            #f]))

(define (expr? e)
  (match e
    [(? symbol?)                                            #t]
    [(? exact-integer?)                                     #t]
    [(? flonum?)                                            #t]
    ['#t                                                    #t]
    ['#f                                                    #t]
    [`(λ (,(? symbol?) : ,(? type?)) ,(? expr?) ,(? type?)) #t]
    [`(,(? expr?) ,(? expr?))                               #t]
    [`(m ,(? expr?) ,(? expr?))                             #t]
    [`(: ,(? expr?) ,(? type?))                             #t]
    [`(~> ,(? label?) ,(? expr?))                           #t] ;; record term
    [`(<~ ,(? expr?) ,(? label?))                           #t] ;; record projection
    [`(int+ ,(? expr?) ,(? expr?))                          #t] ;; int+ primitive
    [`(flo+ ,(? expr?) ,(? expr?))                          #t] ;; flo+ primitive
    [_                                                      #f]))

(define/contract (ordinary? t)
  (-> type? boolean?)
  (match t
    ['int           #t]
    ['float         #t]
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

(define selector? (or/c type? label?))
  
(require racket/trace)

(define/contract (sub? t1 t2)
  (-> type? type? boolean?)
  (match* (t1 t2)
    [('int 'int)                                                           #t]
    [('float 'float)                                                       #t]
    [('bool 'bool)                                                         #t]
    [(_ 'top)                                                              #t]
    [(`(-> ,A ,B) `(-> ,C ,D))                                             (and (sub? C A) (sub? B D))]
    [(`(* ,l ,A) `(* ,l ,(? ordinary? B)))                                 (sub? A B)]
    [(A (? (not/c ordinary?) B))                                           (let ([Bs (split B)])
                                                                             (and (sub? A (car Bs)) (sub? A (cadr Bs))))]
    [(`(& ,A ,B) (? ordinary? C))                                          (or (sub? A C) (sub? B C))]
    [(_ _)                                                                 #f]))

(define output? (or/c type? fail?))

(define/contract (combine o1 o2)
  (-> output? output? output?)
  (match* (o1 o2)
    [((? type? A1) (? type? A2)) `(& ,A1 ,A2)]
    [((? fail?) (? type? A))      A]
    [((? type? A) (? fail?))      A]
    [((? fail?) (? fail?))        #f]))

(define/contract (appsub t s)
  (-> type? selector? output?)
  (match* (t s)
    [(`(-> ,A1 ,A2) (? type? B)) #:when (sub? B A1)      A2]
    [(`(-> ,A1 ,A2) (? type? B))                         #f]
    [(`(* ,l1 ,A) (? label? l2)) #:when (equal? l1 l2)  A]
    [(`(* ,l1 ,A) (? label? l2))                        #f]
    [(`(& ,A1 ,A2) S)                                    (combine (appsub A1 S)
                                                                  (appsub A2 S))]
    [(_ _)                                               #f]
  ))

(define (lookup env var)
  (if (equal? (caar env) var)
      (cadar env)
      (lookup (cdr env) var)))

(define/contract (infer e env)
  (-> expr? list? type?)
  (match e    
    [(? exact-integer?)                                              'int]
    [(? flonum?)                                                     'float]
    ['#t                                                             'bool]
    ['#f                                                             'bool]
    [(? symbol?)                                                      (lookup env e)]
    [`(λ (,x : ,A) ,e ,B) #:when (check e B (cons `(,x ,A) env))     `(-> ,A ,B)]
    [`(~> ,l ,e)                                                     `(* ,l ,(infer e env))]
    [`(: ,e ,A) #:when (check e A env)                                A]
    [`(,e1 ,e2)                                                       (let ([A (infer e1 env)] [B (infer e2 env)])
                                                                        (if (appsub A B)
                                                                            (appsub A B)
                                                                            (error "error when checking the application")))]
    [`(<~ ,e ,l)                                                      (let ([A (infer e env)])
                                                                        (if (appsub A l)
                                                                            (appsub A l)
                                                                            (error "error when checking the projection")))]
    [`(m ,e1 ,e2)                                                     (let ([A (infer e1 env)] [B (infer e2 env)])
                                                                        `(& ,A ,B))]
    [`(int+ ,e1 ,e2) #:when (and (check e1 'int env)
                                 (check e2 'int env))                'int]
    [`(flo+ ,e1 ,e2) #:when (and (check e1 'float env)
                                 (check e2 'float env))              'float]
    [_                                                                (error "cannot infer the type of" e "under" env)]))

#; (trace appsub)

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
    [(? exact-integer?)     #t]
    [(? flonum?)            #t]
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
    [(`(: ,n ,A) 'int) #:when (sub? A 'int)                                      `(: ,n int)]
    [(`(: ,n ,A) 'float) #:when (sub? A 'float)                                  `(: ,n float)]
    [(`(: #t ,A) 'bool) #:when (sub? A 'bool)                                    '(: #t bool)]
    [(`(: #f ,A) 'bool) #:when (sub? A 'bool)                                    '(: #f bool)]
    [(v  'top)                                                                    '(: 1 top)]
    [(`(: (λ (,x : ,A) ,e ,B) ,E) `(-> ,C ,(? ordinary? D)))
     #:when (sub? E `(-> ,C ,D))                                                 `(: (λ (,x : ,A) ,e ,D) (-> ,C ,D))]
    [(`(~> ,l ,v) `(* ,l ,(? ordinary? A)))                                       `(~> ,l ,(cast v A))]
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
    [`(int+ ,e1 ,e2)                  `(int+ ,(subst e1 x u) ,(subst e2 x u))]
    [`(flo+ ,e1 ,e2)                  `(flo+ ,(subst e1 x u) ,(subst e2 x u))]
    [_                                 e]))

(define/contract (ptype e)
  (-> expr? type?)
  (match e
    [(? exact-integer?)                   'int]
    [(? flonum?)                    'float]
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
  
(define/contract (dispatch v vl)
  (-> value? (or/c label? value?) expr?)
  (match v
    [`(: (λ (,x : ,A) ,e ,B) (-> ,C ,D))                            `(: ,(subst e x (cast vl A)) ,D)]
    [`(~> ,l ,v)  #:when (equal? l vl)                                v]
    [`(m ,v1 ,v2) #:when (not (appsub (ptype v2)  (atype vl)))       (dispatch v1 vl)]
    [`(m ,v1 ,v2) #:when (not (appsub (ptype v1)  (atype vl)))       (dispatch v2 vl)]
    [`(m ,v1 ,v2) #:when (and (appsub (ptype v1)  (atype vl))
                              (appsub (ptype v2)  (atype vl)))      `(m ,(dispatch v1 vl) ,(dispatch v2 vl))]))

(define/contract (plus v1 v2)
  (-> value? value? value?)
  (match* (v1 v2)
    [(`(: ,n1 int) `(: ,n2 int))     `(: ,(+ n1 n2) int)]
    [(`(: ,n1 float) `(: ,n2 float)) `(: ,(+ n1 n2) float)]
    [(_ _)                            (error "error when doing primitive plus")]))

;; possibly need not-value? as condition check
(define/contract (step e)
  (-> expr? expr?)
  (match e
    [(? exact-integer? n)                           `(: ,n int)]
    [(? flonum? n)                                  `(: ,n float)]
    ['#t                                            '(: #t bool)]
    ['#f                                            '(: #f bool)]                             
    [`(λ (,x : ,A) ,e ,B)                           `(: (λ (,x : ,A) ,e ,B) (-> ,A ,B))]
    [`(: ,(? pvalue? p) ,(? (not/c ordinary?) A))    (let ([As (split A)])
                                                       `(m (: ,p ,(car As)) (: ,p ,(cadr As))))]
    [`(<~ ,(? value? v) ,(? label? l))               (dispatch v l)]
    [`(<~ ,(? (not/c value?) e) ,(? label? l))      `(<~ ,(step e) ,l)]
    [`(~> ,(? label? l) ,(? (not/c value?) e))      `(~> ,l ,(step e))]
    [`(,(? value? v) ,(? value? vl))                 (dispatch v vl)]
    [`(: ,(? value? v) ,A)                           (cast v A)]
    [`(: ,(? (not/c pvalue?) e) ,A)                 `(: ,(step e) ,A)]
    [`(,(? (not/c value?) e1) ,e2)                  `(,(step e1) ,e2)]
    [`(,(? value? v) ,e2)                           `(,v ,(step e2))]
    [`(m ,e1 ,(? value? v))                         `(m ,(step e1) ,v)]
    [`(m ,(? value? v) ,e2)                         `(m ,v ,(step e2))]
    [`(m ,e1 ,e2)                                   `(m ,(step e1) ,(step e2))]
    [`(int+ ,(? (not/c value?) e1) ,e2)             `(int+ ,(step e1) ,e2)]
    [`(int+ ,(? value? v) ,(? (not/c value?) e2))   `(int+ ,v ,(step e2))]
    [`(int+ ,(? value? v1) ,(? value? v2))           (plus v1 v2)]
    [`(flo+ ,(? (not/c value?) e1) ,e2)             `(flo+ ,(step e1) ,e2)]
    [`(flo+ ,(? value? v) ,(? (not/c value?) e2))   `(flo+ ,v ,(step e2))]
    [`(flo+ ,(? value? v1) ,(? value? v2))           (plus v1 v2)]
    ))

(define/contract (eval e)
  (-> any/c value?)
  (let ([e (desugar e)])
    (when (infer e '())
      (if (value? e) e (eval (step e))))))

;; -----------------------------------------------------------------------
;; Non-core Features
;; -----------------------------------------------------------------------

(define (variadic->dyadic op args)
  (match args
    [(list last1 last2)          `(,op ,last1 ,last2)]
    [(list a as ...)             `(,op ,a ,(variadic->dyadic op as))]))

(define (unfold-field f)
  (match f
    [`(,l ,e)    `(~> ,l ,e)]))

(define/contract (desugar e)
  (-> any/c expr?)
  (match e
    [`(M ,e1 ...)                  (desugar (variadic->dyadic 'm e1))]
    [`(R ,fs ...)                  (desugar `(M ,@(map unfold-field fs)))]
    ;; recursive call
    [`(λ (,x : ,A) ,e ,B)         `(λ (,x : ,A) ,(desugar e) ,B)]
    [`(,e1 ,e2)                   `(,(desugar e1) ,(desugar e2))]
    [`(m ,e1 ,e2)                 `(m ,(desugar e1) ,(desugar e2))]
    [`(: ,e ,A)                   `(: ,(desugar e) ,A)]
    [`(~> ,l ,e)                  `(~> ,l ,(desugar e))]
    [`(<~ ,e ,l)                  `(<~ ,(desugar e) ,l)]
    [`(int+ ,e1 ,e2)              `(int+ ,(desugar e1) ,(desugar e2))]
    [`(flo+ ,e1 ,e2)              `(flo+ ,(desugar e1) ,(desugar e2))]
    [_                             e]))

#; (trace desugar)