(import core)


;;(define x 10)

(let loop ((i 0))
    (cond 
        ((< i 10) (displayln i) (loop (+ i 1)))
        (else i)))

(let ((i 0))
    (while (< i 10)
        (displayln i)
        (set! i (+ i 1))))