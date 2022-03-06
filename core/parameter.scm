(module core parameter)

(define (make-parameter val)
    (define l (lambda xval 
        (if (null? xval)
            val 
            (set! val (car xval)))))   
    (l val)
    l
)

(export make-parameter)