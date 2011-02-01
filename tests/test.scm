(define (fact n)
  (if (zero? n) 1
    (* n (fact (- n 1)))))

(display (fact 10000))
(newline)
