(module core)
(import core parameter)


(define (cons-source kar kdr source) (cons kar kdr))
(define (caar x) (car (car x)))
(define (cadr x) (car (cdr x)))
(define (cdar x) (cdr (car x)))
(define (cddr x) (cdr (cdr x)))
(define (cadar x) (car (cdr (car x))))
(define (caddr x) (car (cdr (cdr x))))
(define (cdddr x) (cdr (cdr (cdr x))))
(define (not x) (if x #f #t))
(define (list . args) args)
(define (length ls)
    (if (list? ls)
        (length* ls)
        (error "length: not a list" ls)))
(define (map proc ls)
    (if (list? ls)
        (if (pair? ls)
            (cons (proc (car ls)) (map proc (cdr ls)))
            '())
        (error "map: not a list" ls)))

(define (for-each proc ls)
    (define (for-each-helper proc ls)
        (if (pair? ls)
            (begin 
                (proc (car ls))
                (for-each-helper proc (cdr ls)))
            '()))
    (if (list? ls)
        (for-each-helper proc ls)
        (error "for-each: not a list" ls)
    )
)
(define (any pred ls . lol)
  (define (any1 pred ls)
    (if (pair? (cdr ls))
        ((lambda (x) (if x x (any1 pred (cdr ls)))) (pred (car ls)))
        (pred (car ls))))
  (define (anyn pred lol)
    (if (every pair? lol)
        ((lambda (x) (if x x (anyn pred (map cdr lol))))
         (apply pred (map car lol)))
        #f))
  (if (null? lol) (if (pair? ls) (any1 pred ls) #f) (anyn pred (cons ls lol))))
(define (every pred ls . lol)
  (define (every1 pred ls)
    (if (null? (cdr ls))
        (pred (car ls))
        (if (pred (car ls)) (every1 pred (cdr ls)) #f)))
  (if (null? lol)
      (if (pair? ls) (every1 pred ls) #t)
      (not (apply any (lambda xs (not (apply pred xs))) ls lol))))
(define (list-tail ls k)
  (if (eq? k 0)
      ls
      (list-tail (cdr ls) (- k 1))))

(define (list-ref ls k) (car (list-tail ls k)))

(define (any pred ls . lol)
  (define (any1 pred ls)
    (define (h x)
        (if x x (any1 pred (cdr ls))))
    (if (pair? (cdr ls))
        (h (pred (car ls)))
        (pred (car ls))))
  (define (anyn pred lol)
    (if (every pair? lol)
        ((lambda (x) (if x x (anyn pred (map cdr lol))))
         (pred (map car lol)))
        #f))
  (if (null? lol) (if (pair? ls) (any1 pred ls) #f) (anyn pred (cons ls lol))))



(define close-syntax
  (lambda (form env)
    (make-syntactic-closure env '() form)))

(define make-renamer
  (lambda (mac-env)
    (define rename
      ((lambda (renames)
         (lambda (identifier)
       ;   (print "rename's" renames)
           ((lambda (cell)
              (if cell
                  (cdr cell)
                  ((lambda (name)
                     (set! renames (cons (cons identifier name) renames))
                     name)
                   ((lambda (id)
                      (syntactic-closure-set-rename! id rename)
                      id)
                    (close-syntax identifier mac-env)))))
            (assq identifier renames))))
       '()))
    rename))

(define er-macro-transformer
  (lambda (f)
    (lambda (expr use-env mac-env)
      (f expr
         (make-renamer mac-env)
         (lambda (x y) (identifier=? use-env x use-env y))))))


(%define-syntax cond
  (er-macro-transformer
   (lambda (expr rename compare)
     (if (null? (cdr expr))
         (if #f #f)
         ((lambda (cl)
            (if (compare (rename 'else) (car cl))
                (if (pair? (cddr expr))
                    (error "non-final else in cond" expr)
                    (cons (rename 'begin) (cdr cl)))
                (if (if (null? (cdr cl)) #t (compare (rename '=>) (cadr cl)))
                    (list (list (rename 'lambda) (list (rename 'tmp))
                                (list (rename 'if) (rename 'tmp)
                                      (if (null? (cdr cl))
                                          (rename 'tmp)
                                          (list (car (cddr cl)) (rename 'tmp)))
                                      (cons (rename 'cond) (cddr expr))))
                          (car cl))
                    (list (rename 'if)
                          (car cl)
                          (cons (rename 'begin) (cdr cl))
                          (cons (rename 'cond) (cddr expr))))))
          (cadr expr))))))
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

(%define-syntax or
  (er-macro-transformer
   (lambda (expr rename compare)
     (cond ((null? (cdr expr)) #f)
           ((null? (cddr expr)) (cadr expr))
           (else
            (list (rename 'let) (list (list (rename 'tmp) (cadr expr)))
                  (list (rename 'if) (rename 'tmp)
                        (rename 'tmp)
                        (cons (rename 'or) (cddr expr)))))))))

(%define-syntax and
  (er-macro-transformer
   (lambda (expr rename compare)
     (cond ((null? (cdr expr)))
           ((null? (cddr expr)) (cadr expr))
           (else (list (rename 'if) (cadr expr)
                       (cons (rename 'and) (cddr expr))
                       #f))))))

(%define-syntax quasiquote
  (er-macro-transformer 
    (lambda (expr rename compare)
      (print expr)
      (transfer (cadr expr)))))

(%define-syntax letrec
  (er-macro-transformer
   (lambda (expr rename compare)
     ((lambda (defs)
        `((,(rename 'lambda) () ,@defs ,@(cddr expr))))
      (map (lambda (x) (cons (rename 'define) x)) (cadr expr))))))

(%define-syntax let
  (er-macro-transformer
   (lambda (expr rename compare)
     (if (null? (cdr expr)) (error "empty let" expr))
     (if (null? (cddr expr)) (error "no let body" expr))
     ((lambda (bindings)
        (if (list? bindings) #f (error "bad let bindings"))
        (if (every (lambda (x)
                     (if (pair? x) (if (pair? (cdr x)) (null? (cddr x)) #f) #f))
                   bindings)
            ((lambda (vars vals)
               (if (identifier? (cadr expr))
                   `((,(rename 'lambda) ,vars
                      (,(rename 'letrec) ((,(cadr expr)
                                           (,(rename 'lambda) ,vars
                                            ,@(cdr (cddr expr)))))
                       (,(cadr expr) ,@vars)))
                     ,@vals)
                   `((,(rename 'lambda) ,vars ,@(cddr expr)) ,@vals)))
             (map car bindings)
             (map cadr bindings))
            (error "bad let syntax" expr)))
      (if (identifier? (cadr expr)) (car (cddr expr)) (cadr expr))))))

(%define-syntax let*
  (er-macro-transformer
   (lambda (expr rename compare)
     (if (null? (cdr expr)) (error "empty let*" expr))
     (if (null? (cddr expr)) (error "no let* body" expr))
     (if (null? (cadr expr))
         `(,(rename 'let) () ,@(cddr expr))
         (if (if (list? (cadr expr))
                 (every
                  (lambda (x)
                    (if (pair? x) (if (pair? (cdr x)) (null? (cddr x)) #f) #f))
                  (cadr expr))
                 #f)
             `(,(rename 'let) (,(caar (cdr expr)))
               (,(rename 'let*) ,(cdar (cdr expr)) ,@(cddr expr)))
             (error "bad let* syntax"))))))
  

(%define-syntax define-auxiliary-syntax
  (er-macro-transformer
   (lambda (expr rename compare)
      (list '%define-syntax (cadr expr) 
        (list 'lambda (list 'expr 'use-env 'mac-env)
          (list 'error "incorrect use of auxilary syntax" (list 'car 'expr)))))))


(define-auxiliary-syntax _)
(define-auxiliary-syntax =>)
(define-auxiliary-syntax ...)
(define-auxiliary-syntax else)
(define-auxiliary-syntax unquote)
(define-auxiliary-syntax unquote-splicing)


(export 
    caar 
    cadr 
    cdar 
    cddr
    not
    list
    length
    map
    for-each
    every 
    any
    list-tail 
    list-ref
    let 
    letrec 
    let*
    => 
    else
    cond
    quasiquote
    or
    and 
    unquote 
    unquote-splicing 
    _ 
    ...
    make-parameter)