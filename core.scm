(module core)

(define (caar x) (car (car x)))
(define (cadr x) (car (cdr x)))
(define (cdar x) (cdr (car x)))
(define (cddr x) (cdr (cdr x)))

(define (not x) (if x #f #t))
(define (list . args) args)
(export 
    caar 
    cadr 
    cdar 
    cddr
    not
    list)