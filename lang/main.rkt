#lang racket
(require racket/match)

;; -----------------------------------------------------------------------
;; Statics
;; -----------------------------------------------------------------------

(define (type? t)
  (match t
    ['int #t]
    ['bool #t]
    ['top #t]
    [`(-> ,(? type?) ,(? type?)) #t]
    [`(& ,(? type?) ,(? type?)) #t]
    [_ #f]))

(define (expr? e)
  (match e
    [(? symbol?) #t]
    [(? number?) #t]
    [`(λ (,(? symbol?) : ,(? type?)) ,(? expr?) ,(? type?)) #t]
    [`(,(? expr?) ,(? expr?)) #t]
    [`(m ,(? expr?) ,(? expr?)) #t]
    [`(: ,(? expr?) ,(? type?)) #t]
    [_ #f]))    

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
    [`(& ,A ,B)     `(,A ,B)]))    

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
    [(C `(& ,A ,B))                              `(& ,(appsub C A) ,(appsub C B))]))

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
    [(_ _)                           #f]))

(define (lookup env var)
  (if (equal? (caar env) var)
      (cadar env)
      (lookup (cdr env) var)))

(define/contract (infer e env)
  (-> expr? list? type?)
  (match e    
    [(? number?)                                                 'int]
    ['true                                                       'bool]
    ['false                                                      'bool]
    [(? symbol?)                                                 (lookup env e)]
    [`(λ (,x : ,A) ,e ,B) #:when (check e B (cons `(,x ,A) env)) `(-> ,A ,B)]
    [`(: ,e ,A) #:when (check e A env)                           A]
    [`(,e1 ,e2)                                                  (let ([A (infer e1 env)] [B (infer e2 env)])
                                                                   (appsub B A))]
    [`(m ,e1 ,e2)                                                (let ([A (infer e1 env)] [B (infer e2 env)])
                                                                   (if (disjoint? A B) `(& ,A ,B) #f))]))
(define/contract (check e t env)
  (-> expr? type? list? boolean?)
  (let ([A (infer e env)])
    (sub? A t)))

;; -----------------------------------------------------------------------
;; Dynamics
;; -----------------------------------------------------------------------

(define (pvalue? e)
  (match e
    [(? number?)            #t]
    [(? boolean?)           #t]
    [`(λ (,x : ,A) ,e ,B)   #t]
    [_                      #f]))
    
(define (value? e)
  (match e
    [`(: ,p ,t)         (pvalue? p)]
    [`(m ,v1 ,v2)       (and (value? v1) (value? v2))]
    [_                  #f]))

(define/contract (cast e t)
  (-> value? any/c value?)
  (match* (e t)
    [(`(: ,n ,A) 'int) #:when (sub? A 'int) `(: ,n int)]
    [(v (? (and/c ordinary? toplike?) A)) `(: 1 ,A)]
    [(`(: (λ (,x : ,A) ,e ,B) ,E) `(-> ,C ,(? (and/c (not/c toplike?) ordinary?) D))) #:when (sub? E `(-> ,C ,D)) `(: (λ (,x : ,A) ,e ,D) (-> ,C ,D))]
    ))

(cast '(: 1 int) 'int)
(cast '(: (λ (x : int) x int) (-> int int)) '(-> int int))

(define (eval e)
  (if (value? e) e (eval (step e))))

(define (step e)
  (match e
    [(? number?)                     `(: ,e int)]
    [`(: ,(? pvalue? p) ,A)          'split-type]
    [`(: ,(? (not/c pvalue?) e) ,A)  `(: ,(step e) ,A)]))

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

(check-equal? (pvalue? '(λ (x : int) x int)) #t)