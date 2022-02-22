(module core macros)

(import core primitives)

(define (transfer ls)
    (if (pair? ls)
        (if (pair? (car ls))
            (if (eq? (caar ls) 'unquote)
                (list 'cons (cadar ls) (transfer (cdr ls)))
                (if (eq? (caar ls) 'unquote-splicing)
                    (list 'append (cadar ls) (transfer (cdr ls)))
                    (list 'cons (transfer (car ls)) (transfer (cdr ls)))))
            (list 'cons (list 'quote (car ls)) (transfer (cdr ls))))
        (list 'quote ls)))

(defmacro quasiquote (x)
    (transfer x))

;; (let ((x 1) (y 2)) 
;;    (+ x 1)) 
;; => 
;; ((lambda (x y) (+ x y)) 1 2)
;;
;; (let loop ((x 0))
;;      (loop (+ x 1)))
;; => 
;; ((lambda (loop) (set! loop (lambda (x) (loop (+ x 1)))) (loop 0)) (quote ()))
(defmacro let (bindings . body) 
    (if (symbol? bindings)
        `(let ((,bindings '()))
            (set! ,bindings (lambda ,(map car (car body)) ,@(cdr body)))
            (,bindings ,@(map cadr (car body))))
        `((lambda ,(map car bindings) ,@body) 
            ,@(map cadr bindings))))


(defmacro let* (bindings . body)
	(if (null? bindings)
		`(begin ,@body)
		`(let (,(car bindings))
			(let* ,(cdr bindings) ,@body))))
(defmacro letrec (bindings . body)
	`(let ,(map (lambda (v) (list (car v) nil)) bindings)
		,@(map (lambda (v) `(set! ,@v)) bindings)
		,@body))

(export 
    let 
    let* 
    letrec
    quasiquote
)