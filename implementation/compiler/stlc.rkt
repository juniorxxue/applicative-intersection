#lang racket

(require
  (for-syntax syntax/parse)
  (for-meta 2 racket/base syntax/parse))

(provide (except-out (all-from-out racket) #%app))

(provide (rename-out [app/tc #%app]))

(provide M)

(define-syntax (M stx)
  (syntax-parse stx
    ([_ e1 e2] (syntax/loc stx (list e1 e2)))))

(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (M)
    ([_ (M e1 e2) e] (syntax/loc stx (cons (#%app e1 e) (#%app e2 e))))
    ([_ e1 e2 ...] (syntax/loc stx (#%app e1 e2 ...)))
    ))