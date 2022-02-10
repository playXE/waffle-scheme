(import core)


(define %allocate-instance-internal '())
(defun %allocate-instance (class nfields)
    (%allocate-instance-internal class #t (lambda args (displayln "An instance is not a procedure")) nfields)
)
(letrec ((instances '()))
    (set! %allocate-instance-internal 
        (lambda (class lock proc nfields)
            (letrec ((vector (make-vector (+ nfields 3) #f))
                     (closure (lambda args 
                        (apply (vector-ref vector 0) args))))
                (vector-set! vector 0 proc)
                (vector-set! vector 1 lock)
                (vector-set! vector 2 class)
                (set! instances (cons (cons closure vector) instances))
                closure))))
(export %allocate-instance)