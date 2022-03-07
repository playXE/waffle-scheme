(import core)

(let loop ((i 0))
    (cond 
        ((< i 100) (print i) (loop (+ i 1)))
        (else i)))