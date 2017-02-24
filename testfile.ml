(val x 3)
(define addone (x) (+ x 1))
(print_endline (string_of_int (addone 5)))
(print_endline (string_of_int ((lambda (x) (+ x 1)) 3)))
(print_endline (string_of_bool (or #t #f)))

(val ls (List.map (+ 1) '(1 2 3)))
(List.iter (Printf.printf "%d ") ls)
(print_endline ())
