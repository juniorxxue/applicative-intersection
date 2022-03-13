#lang racket

(require racket/match)

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
    ['#t                                                    #t]
    ['#f                                                    #t]
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
    [`(-> ,A ,(? (not/c ordinary?) B)) (let ([Bs (split B)])
                                         `((-> ,A ,(car Bs)) (-> ,A ,(cadr Bs))))]
    [`(& ,A ,B)                       `(,A ,B)]
    [_                                 (error "fail to split" t)]))

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

(define (lookup env var)
  (if (equal? (caar env) var)
      (cadar env)
      (lookup (cdr env) var)))

(define (appsub B A)
  (error "WIP"))

(define/contract (infer e env)
  (-> expr? list? type?)
  (match e    
    [(? number?)                                                     'int]
    ['#t                                                             'bool]
    ['#f                                                             'bool]
    [(? symbol?)                                                      (lookup env e)]
    [`(λ (,x : ,A) ,e ,B) #:when (check e B (cons `(,x ,A) env))     `(-> ,A ,B)]
    [`(: ,e ,A) #:when (check e A env)                                A]
    [`(,e1 ,e2)                                                       (let ([A (infer e1 env)] [B (infer e2 env)])
                                                                        (appsub B A))]
    [`(m ,e1 ,e2)                                                     (let ([A (infer e1 env)] [B (infer e2 env)])
                                                                        (if (disjoint? A B) `(& ,A ,B) #f))]
    [_                                                                (error "cannot infer the type of" e "under" env)]))

(define/contract (check e t env)
  (-> expr? type? list? boolean?)
  (let ([A (infer e env)])
    (sub? A t)))