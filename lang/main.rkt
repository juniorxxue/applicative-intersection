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

(define (eval exp env)
  (match exp
    [(? symbol?)              (env-lookup env exp)]
    [(? number?)              exp]
    [`(λ (,x : ,A) ,e ,B)     `(closure ,exp ,env)]
    [`(,f ,arg)               (apply-proc (eval f env) (eval arg env))]
    [`(m ,e1 ,e2)             `(merge ,e1 ,e2)]
    [`(: ,e ,A)               `(anno ,e ,A)]))

(define (apply-proc f env)
  (error "WIP"))

(define (env-lookup env exp)
  (error "WIP"))

(eval '(λ (x : int) x int) '())
(eval '(: 1 int) '())
(eval '(m 1 1) '())