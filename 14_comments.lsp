(define null. (x)
  (eq x '()))

(define and. (x y)
  (cond (x (cond (y #t)
                 (#t #f)))
        (#t #f)))

(define not. (x)
  (cond (x #f)
        (#t #t)))

(val cons pair)

(define append. (x y)
  (cond ((null. x) y)
        (#t (cons (car x)
                  (append. (cdr x) y)))))

(define list. (x y)
  (cons x (cons y '())))

(define zip. (x y)
  (cond ((and. (null. x) (null. y)) '())
        ((and. (not. (atom? x)) (not. (atom? y)))
         (cons (list. (car x) (car y))
               (zip. (cdr x) (cdr y))))))

(define o (f g) (lambda (x) (f (g x))))
(val caar (o car car))
(val cadr (o car cdr))
(val caddr (o cadr cdr))
(val cadar (o car (o cdr car)))
(val caddar (o car (o cdr (o cdr car))))


(define lookup. (key alist)
  (cond ((null. alist) 'error)
        ((eq (caar alist) key) (cadar alist))
        (#t (lookup. key (cdr alist)))))

; eval takes two parameters: an expression and an environment. It's like our
; evalexp.
(define eval. (e env)
   (letrec (
        ; cond works by evaluating each of the conditions in order until it
        ; encounters a truthy one.
        (eval-cond. (lambda (c a)
            ; If we have no more conditions left, there's an error.
            (cond ((null. c) 'error)
                  ; If the current condition is true, evaluate that branch.
                  ((eval. (caar c) a)  (eval. (cadar c) a))
                  ; Otherwise, keep going.
                  (#t (eval-cond. (cdr c) a)))))

        ; This is a manually curried form of map. It runs eval over every
        ; element in a list using the given environment.
        (map-eval. (lambda (exps env)
          (cond ((null. exps) '())
                (#t (cons (eval.  (car exps) env)
                          (map-eval. (cdr exps) env))))))
            )

      ; There are a lot of cases to consider. This is like our large match
      ; expression.
      (cond
        ; If it's a symbol, look it up. This is different from pg's Lisp in
        ; that he *only* has symbols to work with.
        ((sym? e) (lookup. e env))
        ; If it's some other type of atom, just leave it be. Let it
        ; self-evaluate.
        ((atom? e) e)
        ; If it's a list (the only alternative to being an atom), check if the
        ; first item is an atom.
        ((atom? (car e))
         ; What kind of form is it?
         (cond
           ; Quote accepts one argument, so just return that argument as an
           ; unevaluated expression (note the lack of a recursive call to
           ; eval.).
           ((eq (car e) 'quote) (cadr e))
           ; For atom?, eq, car, cdr, and cons, just evaluate the expression
           ; then pass it through to the built-in form.
           ((eq (car e) 'atom?) (atom? (eval. (cadr e)  env)))
           ((eq (car e) 'eq)    (eq    (eval. (cadr e)  env)
                                       (eval. (caddr e) env)))
           ((eq (car e) 'car)   (car   (eval. (cadr e)  env)))
           ((eq (car e) 'cdr)   (cdr   (eval. (cadr e)  env)))
           ((eq (car e) 'cons)  (cons  (eval. (cadr e)  env)
                                       (eval. (caddr e) env)))
           ; For cond, it's a wee bit tricker. We get to this function a bit
           ; later.
           ((eq (car e) 'cond)  (eval-cond. (cdr e) env))
           ; A bunch of pass-through math operations.
           ((eq (car e) '+)     (+ (eval. (cadr e) env)
                                   (eval. (caddr e) env)))
           ((eq (car e) '*)     (* (eval. (cadr e) env)
                                   (eval. (caddr e) env)))
           ((eq (car e) '-)     (- (eval. (cadr e) env)
                                   (eval. (caddr e) env)))
           ((eq (car e) '<)     (< (eval. (cadr e) env)
                                   (eval. (caddr e) env)))
           ; ...else, try and evaluate the function as a user-defined function,
           ; applying it to the arguments.
           (#t (eval. (cons (lookup. (car e) env)
                            (cdr e))
                      env))))
        ; If it's a compound expression in which the first element is a
        ; label-expression,
        ((eq (caar e) 'label)
         ; ...evaluate the expression in environment with a new recursive
         ; binding.
         (eval. (cons (caddar e) (cdr e))
                (cons (list. (cadar e) (car e)) env)))
        ; If it's a compound expression in which the first element is a
        ; lambda-expresison,
        ((eq (caar e) 'lambda)
         ; ...evaluate the application of the lambda to the given arguments,
         ; evaluating them.
         (eval. (caddar e)
                (append. (zip. (cadar e)
                               (map-eval. (cdr e) env))
                         env))))))

(eval. '((label fact
                (lambda (x)
                  (cond ((< x 2) 1)
                        (#t (* x (fact (- x 1)))))))
         5)
       '())
