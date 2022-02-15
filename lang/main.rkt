#lang racket

(require racket/match)
(require rackunit)

;; e ::= n | x | \x : A. e B | e1 e2 | e1 ,, e2 | e : A

;; -----------------------------------------------------------------------
;; Statics
;; -----------------------------------------------------------------------

;; subtyping
(define (ordinary? t)
  (match t
    ['int           #t]
    ['top           #t]
    [`(-> ,A ,B)    (ordinary? B)]
    [_              #f]))

(check-equal? (ordinary? '(-> int (& int int))) #f)

(define (appsub s t)
  'int)

(define (infer exp ctx)
  (match exp
    [(? symbol?)          (ctx-lookup ctx exp)]
    [(? number?)          'int]
    [`(λ (,x : ,A) ,e ,B) #:when (check e (extend-ctx ctx `(,x . ,A))) `(-> ,A ,B)]
    [`(,f ,arg)           (let ([t-A (infer f ctx)]
                                [t-B (infer arg ctx)])
                            (appsub t-B t-A))]))

(define (check exp ctx)
  #t)

(define (extend-ctx ctx pr)
  '())

(define (ctx-lookup ctx exp)
  (error "WIP"))

(check-equal? (infer '(λ (x : int) x int) '()) '(-> int int))
(check-equal? (infer '((λ (x : int) x int) 1) '()) 'int)

;; -----------------------------------------------------------------------
;; Dynamics
;; -----------------------------------------------------------------------

(define (pvalue? exp)
  (match exp
    [(? number?)          #t]
    [(? boolean?)         #t]
    [`(λ (,x : ,A) ,e ,B)   #t]
    [_                    #f]))
    
(define (value? exp)
  (match exp
    [`(: ,p ,t)         (pvalue? p)]
    [`(m ,v1 ,v2)       (and (value? v1) (value? v2))]
    [_                  #f]))

(check-equal? (pvalue? '(λ (x : int) x int)) #t)

(define (eval e)
  (if (value? e)
      e
      (eval (step e))))

(define (lambda? e)
  1
  )
    

(define (step e)
  (match e
    [(? number?)                `(: ,e int)]
    [`(: ,(? pvalue? p) ,A)     'split-type]))