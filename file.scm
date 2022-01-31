(import core)

(letrec ((x (lambda () y)) 
        (y 42)) 
        (x)) 