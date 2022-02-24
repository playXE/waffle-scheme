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

(define-macro quasiquote (x)
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

(define-syntax letrec*
  (syntax-rules ()
    ((letrec* ((var1 init1) ...) body1 body2 ...)
     (let ((var1 <undefined>) ...)
       (set! var1 init1)
       ...
       (let () body1 body2 ...)))))

(define-syntax letrec
  (syntax-rules ()
    ((letrec* ((var1 init1) ...) body1 body2 ...)
     (let ((var1 #f) ...)
       (set! var1 init1)
       ...
       (let () body1 body2 ...)))))

(define-syntax let
    (syntax-rules ()
      ((let ((name val) ...) body1 body2 ...)
       ((lambda (name ...) body1 body2 ...)
        val ...))
    ((let tag ((name val) ...) body1 body2 ...)
       ((letrec ((tag (lambda (name ...)
               body1 body2 ...)))
         tag)
       val ...))))

(define-syntax let*
 (syntax-rules ()
 ((let* () body1 body2 ...)
          (let () body1 body2 ...))
         ((let* ((name1 val1) (name2 val2) ...)
            body1 body2 ...)
          (let ((name1 val1))
            (let* ((name2 val2) ...)
              body1 body2 ...)))))

(define-syntax cond
      (syntax-rules (else =>)
        ((cond (else result1 result2 ...))
         (begin result1 result2 ...))
        ((cond (test => result))
         (let ((temp test))
           (if temp (result temp))))
        ((cond (test => result) clause1 clause2 ...)
         (let ((temp test))
           (if temp
               (result temp)
               (cond clause1 clause2 ...))))
        ((cond (test)) test)
        ((cond (test) clause1 clause2 ...)
         (let ((temp test))
        (if temp temp
               (cond clause1 clause2 ...))))
        ((cond (test result1 result2 ...))
         (if test (begin result1 result2 ...)))
        ((cond (test result1 result2 ...)
               clause1 clause2 ...)
         (if test
             (begin result1 result2 ...)
             (cond clause1 clause2 ...)))))


;; can't use define-syntax because they are not hygienic so we use define-macro with gensym inside.
(define-macro while (condition . body)
  (let ((loop (gensym))) 
    `(let ,loop ()
       (cond 
        (,condition => ,@body (,loop))
        (else '())))))



(export 
    let 
    let* 
    letrec
    quasiquote
    cond
    while
)