#lang racket
(require racket/match)

;; -----------------------------------------------------------------------
;; Statics
;; -----------------------------------------------------------------------

(define (fail? t)
  (not t))

(define (type? t)
  (match t
    ['int                         #t]
    ['bool                        #t]
    ['top                         #t]
    [`(-> ,(? type?) ,(? type?))  #t]
    [`(& ,(? type?) ,(? type?))   #t]
    [_                            #f]))

(define (expr? e)
  (match e
    [(? symbol?)                                            #t]
    [(? number?)                                            #t]
    ['true                                                  #t]
    ['false                                                 #t]
    [`(λ (,(? symbol?) : ,(? type?)) ,(? expr?) ,(? type?)) #t]
    [`(,(? expr?) ,(? expr?))                               #t]
    [`(m ,(? expr?) ,(? expr?))                             #t]
    [`(: ,(? expr?) ,(? type?))                             #t]
    [_                                                      #f]))

(define/contract (ordinary? t)
  (-> type? boolean?)
  (match t
    ['int           #t]
    ['bool          #t]
    ['top           #t]
    [`(-> ,_ ,B)    (ordinary? B)]
    [_              #f]))

(define/contract (split t)
  (-> type? (listof type?))
  (match t
    [`(-> ,A ,B)    (let ([Bs (split B)])
                      `((-> ,A ,(car Bs)) (-> ,A ,(cadr Bs))))]
    [`(& ,A ,B)    `(,A ,B)]))    

(define/contract (toplike? t)
  (-> type? boolean?)
  (match t
    ['top          #t]
    [`(-> ,A ,B)   (toplike? B)]
    [`(& ,A ,B)    (and (toplike? A) (toplike? B))]
    [_             #f]))

(define/contract (sub? t1 t2)
  (-> type? type? boolean?)
  (match* (t1 t2)
    [('int 'int)                     #t]
    [('bool 'bool)                   #t]
    [(_ (? toplike?))                #t]
    [(A (? (not/c ordinary?) B))     (let ([Bs (split B)])
                                       (and (sub? A (car Bs)) (sub? A (cadr Bs))))]
    [(`(& ,A1 ,A2) B)                (or (sub? A1 B) (sub? A2 B))]
    [(`(-> ,A1 ,A2) `(-> ,B1 ,B2))   (and (sub? B1 A1) (sub? A2 B2))]
    [(_ _)                           #f]))

(define/contract (appsub? s t)
  (-> (or/c symbol? type?) type? boolean?)
  (match* (s t)
    [('nil A)         #t]
    [(C `(-> ,A ,B))  (sub? C A)]
    [(C `(& ,A ,B))   (appsub? C A)]
    [(C `(& ,A ,B))   (appsub? C B)]))

(define/contract (appsub s t)
  (-> (or/c symbol? type?) type? type?)
  (match* (s t)
    [('nil A) A]
    [(C `(-> ,A ,B)) #:when (sub? C A)           B]
    [(C `(& ,A ,B))  #:when (not (appsub? C B))  (appsub C A)]
    [(C `(& ,A ,B))  #:when (not (appsub? C A))  (appsub C B)]
    [(C `(& ,A ,B))                             `(& ,(appsub C A) ,(appsub C B))]))

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
    [(_ _)                           #f]))

(define/contract (uvalue? e)
  (-> expr? boolean?)
  (match e
    [`(: ,e ,A)        #t]
    [`(m ,u1 ,u2)      #t]
    [_                 #f]))

(define/contract (consistent? e1 e2)
  (-> uvalue? uvalue? boolean?)
  (match* (e1 e2)
    [(`(: (λ (,x : ,A) ,e ,B1) ,C) `(: (λ (,x : ,A) ,e ,B2) ,D)) #t]
    [(`(: ,e ,A) `(: ,e ,B))                                     #t]
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
    ['true                                                           'bool]
    ['false                                                          'bool]
    [(? symbol?)                                                      (lookup env e)]
    [`(λ (,x : ,A) ,e ,B) #:when (check e B (cons `(,x ,A) env))     `(-> ,A ,B)]
    [`(: ,e ,A) #:when (check e A env)                                A]
    [`(,e1 ,e2)                                                       (let ([A (infer e1 env)] [B (infer e2 env)])
                                                                        (appsub B A))]
    [`(m ,(? uvalue? u1) ,(? uvalue? u2)) #:when (consistent? u1 u2)  (let ([A (infer u1 '())] [B (infer u2 '())])
                                                                        `(& ,A ,B))]
    [`(m ,e1 ,e2)                                                     (let ([A (infer e1 env)] [B (infer e2 env)])
                                                                        (if (disjoint? A B) `(& ,A ,B) #f))]
    [_                                                                (error "type check error")]))

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
    ['true                  #t]
    ['false                 #t]
    [`(λ (,x : ,A) ,e ,B)   #t]
    [_                      #f]))
    
(define/contract (value? e)
  (-> expr? boolean?)
  (match e
    [`(: ,p ,t)         (pvalue? p)]
    [`(m ,v1 ,v2)       (and (value? v1) (value? v2))]
    [_                  #f]))

(define/contract (cast e t)
  (-> value? type? (or/c value? fail?))
  (match* (e t)
    [(`(: ,n ,A) 'int) #:when (sub? A 'int)                                       `(: ,n int)]
    [(`(: true ,A) 'bool) #:when (sub? A 'bool)                                   '(: true bool)]
    [(`(: false ,A) 'bool) #:when (sub? A 'bool)                                  '(: false bool)]
    [(v (? (and/c ordinary? toplike?) A))                                         `(: 1 ,A)]
    [(`(: (λ (,x : ,A) ,e ,B) ,E) `(-> ,C ,(? (and/c (not/c toplike?) ordinary?) D)))
     #:when (sub? E `(-> ,C ,D))                                                  `(: (λ (,x : ,A) ,e ,D) (-> ,C ,D))]
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
    [_                                 e]))

(define/contract (ptype e)
  (-> expr? type?)
  (match e
    [(? number?)                    'int]
    ['true                          'bool]
    ['false                         'bool]
    [`(λ (,x : ,A) ,e ,B)           `(-> ,A ,B)]
    [`(: ,e ,A)                      A]
    [`(m ,e1 ,e2)                   `(& ,(ptype e1) ,(ptype e2))]))
  
(define/contract (papp v vl)
  (-> value? value? expr?)
  (match v
    [`(: ,n (-> ,A ,(? toplike? B)))                             `(: 1 ,B)]
    [`(: (λ (,x : ,A) ,e ,B) (-> ,C ,(? toplike? D)))            `(: 1 ,D)]
    [`(: (λ (,x : ,A) ,e ,B) (-> ,C ,(? (not/c toplike?) D)))    `(: ,(subst e x (cast vl A)) ,D)]
    [`(m ,v1 ,v2) #:when (not (appsub? (ptype vl) (ptype v2)))    (papp v1 vl)]
    [`(m ,v1 ,v2) #:when (not (appsub? (ptype vl) (ptype v1)))    (papp v2 vl)]
    [`(m ,v1 ,v2) #:when (and (appsub? (ptype vl) (ptype v1))
                              (appsub? (ptype vl) (ptype v1)))   `(m ,(papp v1 vl) ,(papp v2 vl))]))

;; possibly need not-value? as condition check
(define/contract (step e)
  (-> expr? expr?)
  (match e
    [(? number? n)                                  `(: ,n int)]
    ['true                                          '(: true bool)]
    ['false                                         '(: false bool)]                             
    [`(λ (,x : ,A) ,e ,B)                           `(: (λ (,x : ,A) ,e ,B) (-> ,A ,B))]
    [`(: ,(? pvalue? p) ,(? (not/c ordinary?) A))    (let ([As (split A)])
                                                       `(m (: ,p ,(car As)) (: ,p ,(cadr As))))]
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

;; -----------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------

(require rackunit)

(check-equal? (type? '(& int int)) #t)
(check-equal? (type? '(-> int (& int int))) #t)
(check-equal? (split '(-> int (& int top))) '((-> int int) (-> int top)))
(check-equal? (toplike? '(-> int (& top top))) #t)
(check-equal? (ordinary? '(-> int (& int int))) #f)
(check-equal? (sub? 'int 'top) #t)
(check-equal? (sub? 'int '(-> int top)) #t)
(check-equal? (sub? 'int '(& int int)) #t)
(check-equal? (appsub 'int '(& (-> int int) (-> bool bool))) 'int)
(check-equal? (appsub 'int '(& (-> int int) (-> int bool)))  '(& int bool))
(check-equal? (disjoint? 'int 'top) #t)
(check-equal? (disjoint? 'int '(-> int int)) #t)
(check-equal? (disjoint? 'int '(& top int)) #f)
(check-equal? (lookup '((x int) (y bool)) 'x) 'int)
(check-equal? (lookup '((x int) (y bool)) 'y) 'bool)
 
(check-equal? (infer '(λ (x : int) x int) '()) '(-> int int))
(check-equal? (infer '((λ (x : int) x int) 1) '()) 'int)

(define id-int
  '(λ (x : int) x int))

(define id-bool
  '(λ (x : bool) x bool))

(check-equal? (expr? id-int) #t)
(check-equal? (expr? `(m ,id-int ,id-bool)) #t)
 
(check-equal? (infer `(m ,id-int ,id-bool) '()) '(& (-> int int) (-> bool bool)))
(check-equal? (infer `((m ,id-int ,id-bool) 1) '()) 'int)
(check-equal? (ptype `(m ,id-int ,id-bool)) '(& (-> int int) (-> bool bool)))
(check-equal? (ptype id-int) '(-> int int))

(check-equal? (cast '(: 1 int) 'int) '(: 1 int))
(check-equal? (cast '(: 1 int) '(& int int)) '(m (: 1 int) (: 1 int)))
(check-equal? (cast '(: (λ (x : int) x int) (-> int int)) '(-> int int)) '(: (λ (x : int) x int) (-> int int)))

(define annoed-id-int
  '(: (λ (x : int) x int) (-> int int)))
(define annoed-id-arr
  '(: (λ (x : (-> int int)) x (-> int int))
      (-> (-> int int) (-> int int))))
(check-equal? (papp `(m ,annoed-id-int ,annoed-id-arr) '(: 1 int)) '(: (: 1 int) int))

(define always-true
  '(λ (x : int) true bool))

(check-equal? (eval `((m ,id-int ,always-true) 1)) '(m (: 1 int) (: true bool)))
(check-equal? (eval '(: (m 1 true) bool)) '(: true bool))