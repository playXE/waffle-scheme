(module core)


(defun append (xs ys)
    (if (null? xs)
        ys
        (cons (car xs) (append (cdr xs) ys))))
(defun cadr (x) (car (cdr x)))
(defun cdar (x) (cdr (car x)))
(defun caar (x) (car (car x)))
(defun cddr (x) (cdr (cdr x)))
(defun cadar (x) (car (cdr (car x))))
(defun caddr (x) (car (cdr (cdr x))))
(defun cdddr (x) (cdr (cdr (cdr x))))
(defun transfer (ls)
    (if (pair? ls)
        (if (pair? (car ls))
            (if (eq? (caar ls) 'unquote)
                (list 'cons (cadar ls) (transfer (cdr ls)))
                (if (eq? (caar ls) 'unquote-splicing)
                    (list 'append (cadar ls) (transfer (cdr ls)))
                    (list 'cons (transfer (car ls)) (transfer (cdr ls)))))
            (list 'cons (list 'quote (car ls)) (transfer (cdr ls))))
        (list 'quote ls)))


(defun map (fn ls)
    (if (null? ls)
        '()
        (cons (fn (car ls)) (map fn (cdr ls)))))

(defmacro quasiquote (x) (transfer x))
(defmacro let (bindings . body) 
	`((lambda ,(map car bindings) ,@body) 
		,@(map cadr bindings)))
(defmacro let* (bindings . body)
	(if (null? bindings)
		`(begin ,@body)
		`(let (,(car bindings))
			(let* ,(cdr bindings) ,@body))))
(defmacro letrec (bindings . body)
	`(let ,(map (lambda (v) (list (car v) nil)) bindings)
		,@(map (lambda (v) `(set! ,@v)) bindings)
		,@body))

(defun range (start end step proc) 
    (defun helper (n)   
        (if (eq? n end)
            '()
            (begin 
                (proc n)
                (helper (+ n step))
            )
        )
    )
    (helper start)
)
(defun vector-empty? (v) (eq? (vector-length v) 0))
(defun vector-foreach (proc v) 
    (range 0 (vector-length v) 1 
        (lambda (i) 
            (proc (vector-ref v i))))
)

(defun vector-map (proc v)
    (let ((nv (vector)))
      (begin (vector-foreach 
            (lambda (elem)
                (vector-push nv (proc elem))
            ) v)
        nv
      )
    )
)

(defun vector-map! (proc v) 
    (range 0 (vector-length v) 1 
        (lambda (i) 
            (vector-set! v i (proc (vector-ref v i)))
        )
    )
    v
)
(defmacro cond (first . rest)
	(if (null? rest)
		`(begin ,first)
		`(if ,(car first) 
			(begin ,@(cdr first))
			(cond ,@rest))))
			


(defmacro for (test . body)
    (let ((varname (car test)) 
	      (init-value (cadr test)) 
		  (predicate (caddr test)) 
		  (step-value (car (cdddr test))))
	    `(let ((,varname ,init-value)) 
		    (while ,predicate ,@body (set! ,varname ,step-value)))))


(defun foreach (proc list)
    (defun helper (c)
        (if (list? c)
            (begin 
                (proc (car c))
                (helper (cdr c))
            )
            '()
        )
    )
    (helper list)
)

(defun parallel thunks 
    (let ((handles (vector) ))
        (begin 
            (foreach 
                (lambda (thunk) 
                    (vector-push handles (thread/spawn thunk)))
                thunks)
            (vector-map thread/join handles))))

(export append cadr cdar caar cddr caddr transfer map vector-empty? parallel)