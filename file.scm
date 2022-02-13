(import core)

(defun nano-to-milli (x) (/ x 1000000))
(define start (time/now))

(for (x 0 (< x 1000000) (+ x 1)) 
    
)
(define end (time/elapsed start))
(displayln (nano-to-milli end))