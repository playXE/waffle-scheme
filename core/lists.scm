(module core lists) 

(import core primitives)

(define (assq obj lst)
    (if (pair? lst)
        (if (pair? (car lst))
            (if (eq? (caar lst) obj)
                (car lst)
                (assq obj (cdr lst)))
            (assq obj (cdr lst)))
        (displayln "list expected in assq but found")))


(export assq)