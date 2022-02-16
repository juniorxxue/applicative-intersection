#lang racket
(require racket/match)

;; -----------------------------------------------------------------------
;; Statics
;; -----------------------------------------------------------------------

(define (ordinary? t)
  (match t
    ['int           #t]
    ['bool          #t]
    ['top           #t]
    [`(-> ,A ,B)    (ordinary? B)]
    [_              #f]))

(define (split t)
  (match t
    [`(-> ,A ,B)    (let ([Bs (split B)])
                      `((-> ,A ,(car Bs)) (-> ,A ,(cadr Bs))))]
    [`(& ,A ,B)     `(,A ,B)]))    

(define (toplike? t)
  (match t
    ['top          #t]
    [`(-> ,A ,B)   (toplike? B)]
    [`(& ,A ,B)    (and (toplike? A) (toplike? B))]
    [_             #f]))

(define (sub? t1 t2)
  (match* (t1 t2)
    [('int 'int)                     #t]
    [('bool 'bool)                   #t]
    [(_ (? toplike?))                #t]
    [(A (? (not/c ordinary?) B))     (let ([Bs (split B)])
                                       (and (sub? A (car Bs)) (sub? A (cadr Bs))))]
    [(`(& ,A1 ,A2) B)                (or (sub? A1 B) (sub? A2 B))]
    [(`(-> ,A1 ,A2) `(-> ,B1 ,B2))   (and (sub? B1 A1) (sub? A2 B2))]
    [(_ _)                           #f]))

(define (appsub? s t)
  (match* (s t)
    [('nil A)         #t]
    [(C `(-> ,A ,B))  (sub? C A)]
    [(C `(& ,A ,B))   (appsub? C A)]
    [(C `(& ,A ,B))   (appsub? C B)]))

(define (appsub s t)
  (match* (s t)
    [('nil A) A]
    [(C `(-> ,A ,B)) #:when (sub? C A)           B]
    [(C `(& ,A ,B))  #:when (not (appsub? C B))  (appsub C A)]
    [(C `(& ,A ,B))  #:when (not (appsub? C A))  (appsub C B)]
    [(C `(& ,A ,B))                              `(& ,(appsub C A) ,(appsub C B))]))

(define (disjoint? t1 t2)
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

(define (infer e env)
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

(define (check e t env)
  (let ([A (infer e env)])
    (sub? A t)))

;; -----------------------------------------------------------------------
;; Dynamics
;; -----------------------------------------------------------------------

(define (pvalue? exp)
  (match exp
    [(? number?)            #t]
    [(? boolean?)           #t]
    [`(λ (,x : ,A) ,e ,B)   #t]
    [_                      #f]))
    
(define (value? exp)
  (match exp
    [`(: ,p ,t)         (pvalue? p)]
    [`(m ,v1 ,v2)       (and (value? v1) (value? v2))]
    [_                  #f]))

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
 
(check-equal? (infer `(m ,id-int ,id-bool) '()) '(& (-> int int) (-> bool bool)))
(check-equal? (infer `((m ,id-int ,id-bool) 1) '()) 'int)

(check-equal? (pvalue? '(λ (x : int) x int)) #t)