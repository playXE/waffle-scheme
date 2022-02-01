(module foo)
(import core)

(define counter 10)

(while (> counter 0)
    (displayln counter)
   
    (set! counter (- counter 1)))

(for (x 0 (< x 10) (+ x 1)) (displayln x))