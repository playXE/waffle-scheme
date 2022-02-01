(module foo)
(import core)

(defun simple () (displayln (thread-id)) 24)

(parallel simple simple)