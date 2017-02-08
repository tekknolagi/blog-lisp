(val Y (lambda (f)
         ((lambda (x) (x x))
          (lambda (x) (f (lambda (y) ((x x) y)))))))

(define almost-factorial (f)
  (lambda (n) (if (< n 2) 1 (* n (f (- n 1))))))

(val factorial (Y almost-factorial))

(define o (f g) (lambda (x) (f (g x))))

(define <= (x y) (or (< x y) (= x y)))

(define >= (x y) (or (> x y) (= x y)))
