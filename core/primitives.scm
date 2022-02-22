(module core primitives)

(define (map fn ls)
    (if (null? ls)
        '()
        (cons (fn (car ls)) (map fn (cdr ls)))))

(define (append xs ys)
    (if (null? xs)
        ys
        (cons (car xs) (append (cdr xs) ys))))
(define (cadr x) (car (cdr x)))
(define (cdar x) (cdr (car x)))
(define (caar x) (car (car x)))
(define (cddr x) (cdr (cdr x)))
(define (cadar x) (car (cdr (car x))))
(define (caddr x) (car (cdr (cdr x))))
(define (cdddr x) (cdr (cdr (cdr x))))

(export 
    map 
    append 
    cadr 
    cdar 
    caar 
    cddr 
    cadar 
    caddr 
    cdddr 
)