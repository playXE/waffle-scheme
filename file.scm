(define (x . y) (42))
(define (x y z . w )
    (+ 1 2)
    (+ 2 3))
(define x (lambda (y z . w) (+ 1 2) (+ 2 3)))
(define z (lambda i 42))

`(1 2 3 ,(+ 1 3) 5)