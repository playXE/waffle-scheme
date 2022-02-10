(import core)

(defun print-thread-id () (displayln (thread-id)))

(parallel print-thread-id print-thread-id print-thread-id)

(gc)