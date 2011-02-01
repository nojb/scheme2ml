(import (rnrs))
; Given a number 'n', build a list (2..n)
(define (iota n)
  (letrec
      ((loop 
	(lambda (curr counter)
	  (if (< counter 2) '()
	      (cons curr (loop (+ 1 curr) (- counter 1)))))))
    (loop 2 n)))

; The sieve algorithm itself
; Given the list (2..n), return a sieved list
; all composite numbers are replaced by 0

(define (sieve lst)
  (letrec
      ((choose-pivot ; choose the first non-zero element in lst
	(lambda (lst)
	  (cond
	   ((null? lst) lst)
	   ((= 0 (car lst)) ; skip over zeros
	    (cons (car lst) (choose-pivot (cdr lst))))
	   (else 
	    (cons (car lst)          ; sieve with the pivot, and recurse
		  (choose-pivot
		   (do-sieve (car lst) (- (car lst) 1) (cdr lst))))))))
       ; Run the sieve
       ; (do-sieve step current lst)
       ; Return the new lst with each step-th element sieved out:
       ; replaced by 0.
       (do-sieve
	(lambda (step current lst)
	  (cond
	   ((null? lst) lst)
	   ((= 0 current)    ; replace the current element with zero
	    (cons 0 (do-sieve step (- step 1) (cdr lst))))
	   (else
	    (cons (car lst) (do-sieve step (- current 1) (cdr lst)))))))
       )
    (choose-pivot lst)))

; Check if a given number is a prime: return 'prime or 'composite
; We run the sieve and then check if the last element has been weeded out

(define (is-prime n)
  (if (= 0 (car (reverse (sieve (iota n)))))
      'composite
      'prime))

(do () ()
  (display (is-prime (read)))
  (newline))
