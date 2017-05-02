exception ThisCan'tHappenError
exception UniqueError of string
exception TypeError of string

let rec assert_unique = function
  | [] -> ()
  | x::xs -> if List.mem x xs then raise (UniqueError x) else assert_unique xs

let stringOfChar c = String.make 1 c

module Env : sig
  type 'a env = (string * 'a option ref) list
  exception NotFound of string
  exception UnspecifiedValue of string
  val mkloc : 'a -> 'b option ref
  val bind : string * 'a * 'a env -> 'a env
  val bindloc : string * 'a option ref * 'a env -> 'a env
  val bindlist : string list -> 'a list -> 'a env -> 'a env
  val bindloclist : string list -> 'a option ref list -> 'a env -> 'a env
  val lookup : string * 'a env -> 'a
  val extend : 'a env -> 'a env -> 'a env
end = struct
  type 'a env = (string * 'a option ref) list

  exception NotFound of string
  exception UnspecifiedValue of string

  let mkloc _ = ref None
  let bind (n, v, e) = (n, ref (Some v))::e
  let bindloc (n, vor, e) = (n, vor)::e

  let rec lookup = function
    | (n, []) -> raise (NotFound n)
    | (n, (n', v)::_) when n=n' ->
       begin
         match !v with
         | Some v' -> v'
         | None -> raise (UnspecifiedValue n)
       end
    | (n, (n', _)::bs) -> lookup (n, bs)

  let bindlist ns vs env =
    List.fold_left2 (fun acc n v -> bind (n, v, acc)) env ns vs

  let bindloclist ns vs env =
    List.fold_left2 (fun acc n v -> bindloc (n, v, acc)) env ns vs

  let extend newenv oldenv =
    List.fold_right (fun (n, v) acc -> bindloc (n, v, acc)) newenv oldenv
end

module Ast = struct
  type lobject =
    | Fixnum of int
    | Boolean of bool
    | Symbol of string
    | Nil
    | Pair of lobject * lobject
    | Primitive of string * (lobject list -> lobject)
    | Quote of value
    | Closure of name list * exp * value Env.env

  and value = lobject
  and name = string
  and let_kind = LET | LETSTAR | LETREC
  and exp =
    | Literal of value
    | Var of name
    | If of exp * exp * exp
    | And of exp * exp
    | Or of exp * exp
    | Apply of exp * exp
    | Call of exp * exp list
    | Lambda of name list * exp
    | Let of let_kind * (name * exp) list * exp
    | Defexp of def

  and def =
    | Val of name * exp
    | Def of name * name list * exp
    | Exp of exp

  let rec string_exp =
    let spacesep ns = String.concat " " ns in
    let spacesep_exp es = spacesep (List.map string_exp es) in
    let string_of_binding (n, e) = "(" ^ n ^ " " ^ string_exp e ^ ")" in
    function
    | Literal e -> string_val e
    | Var n -> n
    | If (c, t, f) ->
        "(if " ^ string_exp c ^ " " ^ string_exp t ^ " " ^ string_exp f ^ ")"
    | And (c0, c1) -> "(and " ^ string_exp c0 ^ " " ^ string_exp c1 ^ ")"
    | Or (c0, c1) -> "(or " ^ string_exp c0 ^ " " ^ string_exp c1 ^ ")"
    | Apply (f, e) -> "(apply " ^ string_exp f ^ " " ^ string_exp e ^ ")"
    | Call (f, es) -> "(" ^ string_exp f ^ " " ^ spacesep_exp es ^ ")"
    | Lambda (ns, e) ->  "(lambda (" ^ spacesep ns ^ ") " ^ string_exp e ^ ")"
    | Let (k, bs, e) ->
        let s = List.assoc k [LET, "let"; LETSTAR, "let*"; LETREC, "letrec"] in
        let bindings = spacesep (List.map string_of_binding bs) in
        "(" ^ s ^ " (" ^ bindings ^ ") " ^ string_exp e ^ ")"
    | Defexp (Val (n, e)) -> "(val " ^ n ^ " " ^ string_exp e ^ ")"
    | Defexp (Def (n, ns, e)) ->
        "(define " ^ n ^ "(" ^ spacesep ns ^ ") " ^ string_exp e ^ ")"
    | Defexp (Exp e) -> string_exp e

  and string_val = function
      | Fixnum v -> string_of_int v
      | Boolean b -> if b then "#t" else "#f"
      | Symbol s -> s
      | Nil -> "nil"
      | Pair (car, cdr) ->
          let rec tail = function
            | Pair (car', cdr') -> " " ^ string_val car' ^ tail cdr'
            | Nil -> ")"
            | v -> " . " ^ string_val v ^ ")"
           in "(" ^ string_val car ^ tail cdr
      | Quote v -> "'" ^ string_val v
      | Primitive (name, _) -> "#<primitive:" ^ name ^ ">"
      | Closure (ns, e, _) -> "#<closure>"

  let rec pair_to_list pr =
      match pr with
      | Nil -> []
      | Pair(a, b) -> a::(pair_to_list b)
      | _ -> raise ThisCan'tHappenError
end

module PushbackReader : sig
  type 'a t

  val of_string : string -> char t
  val of_channel : in_channel -> char t

  val do_stdin : 'a t -> 'b -> ('b -> unit) -> unit
  val read_char : char t -> char
  val unread_char : char t -> char -> char t
end = struct
  type 'a t = {
    mutable line_num: int;
    mutable chr: char list;
    stdin: bool;
    stm: 'a Stream.t
  }

  let make is_stdin stm = { chr=[]; line_num=1; stdin=is_stdin; stm=stm }

  let of_string s  = make false     @@ Stream.of_string s
  let of_channel f = make (f=stdin) @@ Stream.of_channel f

  let do_stdin stm arg f = if stm.stdin then f arg else ()

  let read_char stm =
    match stm.chr with
        | [] ->
            let c = Stream.next stm.stm in
            if c = '\n' then (stm.line_num <- stm.line_num + 1; c) else c
        | c::rest ->
            let _ = stm.chr <- rest in c

  let unread_char stm c = let () = stm.chr <- c :: stm.chr in stm
end

module type READER = sig
  val read_exp : char PushbackReader.t -> Ast.exp
end

module type EVALUATOR = sig
  val eval : Ast.exp -> Ast.value Env.env -> Ast.value * Ast.value Env.env
end

module Reader : READER = struct
  let is_white c = c = ' ' || c = '\t' || c = '\n'

  let rec eat_whitespace stm =
    let c = PushbackReader.read_char stm in
    if is_white c then
      eat_whitespace stm
    else
      let _ = PushbackReader.unread_char stm c in ()

  exception SyntaxError of string

  let rec read_sexp stm =
    let open Ast in
    let is_digit c =
      let code = Char.code c in
      code >= Char.code('0') && code <= Char.code('9')
    in
    let rec read_fixnum acc =
      let nc = PushbackReader.read_char stm in
      if is_digit nc
      then read_fixnum (acc ^ stringOfChar nc)
      else
        let _ = PushbackReader.unread_char stm nc in
        Fixnum(int_of_string acc)
    in
    let is_symstartchar =
        let isalpha = function | 'A'..'Z'|'a'..'z' -> true
                               | _ -> false
        in
        function | '*'|'/'|'>'|'<'|'='|'?'|'!'|'-'|'+' -> true
                 | c -> isalpha c
    in
    let rec read_symbol () =
        let is_delimiter = function | '('|')'|'{'|'}'|'"'|';' -> true
                                    | c -> is_white c
        in
        let nc = PushbackReader.read_char stm in
        if is_delimiter nc
        then let _ = PushbackReader.unread_char stm nc in ""
        else stringOfChar nc ^ read_symbol ()
    in
    let rec read_list stm =              (* NEW *)
      eat_whitespace stm;
      let c = PushbackReader.read_char stm in
      if c = ')' then
        Nil
      else
        let _ = PushbackReader.unread_char stm c in
        let car = read_sexp stm in
        let cdr = read_list stm in
        Pair(car, cdr)
    in
    let rec eat_comment stm =
      if (PushbackReader.read_char stm) = '\n' then () else eat_comment stm
    in
    eat_whitespace stm;
    let c = PushbackReader.read_char stm in
    if c = ';' then (eat_comment stm; read_sexp stm)
    else if is_symstartchar c
    then Symbol(stringOfChar c ^ read_symbol ())
    else if is_digit c || c='~'
    then read_fixnum (stringOfChar (if c='~' then '-' else c))
    else if c = '('
    then read_list stm
    else if c = '#' then
        match (PushbackReader.read_char stm) with
        | 't' -> Boolean(true)
        | 'f' -> Boolean(false)
        | x -> raise (SyntaxError ("Invalid boolean literal " ^ (stringOfChar x)))
    else if c = '\'' then Quote (read_sexp stm)
    else raise (SyntaxError ("Unexpected char " ^ (stringOfChar c)));;

  exception ParseError of string

  let rec build sexp =
    let open Ast in
    let rec is_list e =
        match e with
            | Nil -> true
            | Pair(a, b) -> is_list b
            | _ -> false
    in
    let rec cond_to_if = function
      | [] -> Literal (Symbol "error")
      | (Pair(cond, Pair(res, Nil)))::condpairs ->
          If (build cond, build res, cond_to_if condpairs)
      | _ -> raise (TypeError "(cond c0 c1 c2 c3 ...)")
    in
    let let_kinds = ["let", LET; "let*", LETSTAR; "letrec", LETREC] in
    let valid_let s = List.mem_assoc s let_kinds in
    let to_kind s = List.assoc s let_kinds in
    match sexp with
    | Primitive _ | Closure _ -> raise ThisCan'tHappenError
    | Fixnum _ | Boolean _ | Nil | Quote _ -> Literal sexp
    | Symbol s -> Var s
    | Pair _ when is_list sexp ->
        (match pair_to_list sexp with
        | [Symbol "if"; cond; iftrue; iffalse] ->
            If (build cond, build iftrue, build iffalse)
        | [Symbol "and"; c1; c2] -> And (build c1, build c2)
        | [Symbol "or"; c1; c2] -> Or (build c1, build c2)
        | [Symbol "quote"; e] -> Literal (Quote e)
        | [Symbol "val"; Symbol n; e] -> Defexp (Val (n, build e))
        | [Symbol "lambda"; ns; e] when is_list ns ->
            let err () = raise (TypeError "(lambda (formals) body)") in
            let names = List.map (function Symbol s -> s | _ -> err ())
                                 (pair_to_list ns)
            in
            let () = assert_unique names in
            Lambda (names, build e)
        | [Symbol "define"; Symbol n; ns; e] ->
            let err () = raise (TypeError "(define name (formals) body)") in
            let names = List.map (function Symbol s -> s | _ -> err ())
                                 (pair_to_list ns)
            in
            let () = assert_unique names in
            Defexp (Def (n, names, build e))
        | [Symbol "apply"; fnexp; args] ->
            Apply (build fnexp, build args)
        | (Symbol "cond")::conditions -> cond_to_if conditions
        | (Symbol s)::bindings::exp::[] when is_list bindings && valid_let s ->
            let mkbinding = function
              | Pair (Symbol n, Pair (e, Nil)) -> n, build e
              | _ -> raise (TypeError "(let bindings exp)")
            in
            let bindings = List.map mkbinding (pair_to_list bindings) in
            let () = assert_unique (List.map fst bindings) in
            Let (to_kind s, bindings, build exp)
        | fnexp::args -> Call (build fnexp, List.map build args)
        | [] -> raise (ParseError "poorly formed expression"))
    | Pair _ -> Literal sexp

  let read_exp stm = build @@ read_sexp stm
end

module Evaluator : EVALUATOR = struct
  open Ast

  let rec env_to_val =
    let b_to_val (n, vor) =
      Pair (Symbol n, (match !vor with
                       | None -> Symbol "unspecified"
                       | Some v -> v))
    in
    function
      | [] -> Nil
      | b::bs -> Pair(b_to_val b, env_to_val bs)

  let rec evalexp exp env =
    let evalapply f vs =
      match f with
      | Primitive (_, f) -> f vs
      | Closure (ns, e, clenv) -> evalexp e (Env.bindlist ns vs clenv)
      | _ -> raise (TypeError "(apply prim '(args)) or (prim args)")
    in
    let rec unzip l =
      match l with
      | [] -> [], []
      | (a,b)::rst -> let (flist, slist) = unzip rst in a::flist, b::slist
    in
    let rec ev = function
      | Literal Quote e -> e
      | Literal l -> l
      | Var n -> Env.lookup (n, env)
      | If (c, t, f) when ev c = Boolean true -> ev t
      | If (c, t, f) when ev c = Boolean false -> ev f
      | If _ -> raise (TypeError "(if bool e1 e2)")
      | And (c1, c2) ->
          begin
            match (ev c1, ev c2) with
            | (Boolean v1, Boolean v2) -> Boolean (v1 && v2)
            | _ -> raise (TypeError "(and bool bool)")
          end
      | Or (c1, c2) ->
          begin
            match (ev c1, ev c2) with
            | (Boolean v1, Boolean v2) -> Boolean (v1 || v2)
            | _ -> raise (TypeError "(or bool bool)")
          end
      | Apply (fn, e) -> evalapply (ev fn) (pair_to_list (ev e))
      | Call (Var "env", []) -> env_to_val env
      | Call (e, es) -> evalapply (ev e) (List.map ev es)
      | Lambda (ns, e) -> Closure (ns, e, env)
      | Let (LET, bs, body) ->
          let evbinding (n, e) = n, ref (Some (ev e)) in
          evalexp body (Env.extend (List.map evbinding bs) env)
      | Let (LETSTAR, bs, body) ->
          let evbinding acc (n, e) = Env.bind (n, evalexp e acc, acc) in
          evalexp body (List.fold_left evbinding env bs)
      | Let (LETREC, bs, body) ->
          let names, values = unzip bs in
          let env' = Env.bindloclist names (List.map Env.mkloc values) env in
          let updates = List.map (fun (n, e) -> n, Some (evalexp e env')) bs in
          let () = List.iter (fun (n, v) -> (List.assoc n env') := v) updates in
          evalexp body env'
      | Defexp d -> raise ThisCan'tHappenError
    in
    try
      ev exp
    with e ->
      (
        let err = Printexc.to_string e in
        print_endline @@ "Error: " ^ err ^ " in expression " ^ string_exp exp;
        raise e
      )

  let evaldef def env =
    match def with
    | Val (n, e) -> let v = evalexp e env in (v, Env.bind (n, v, env))
    | Def (n, ns, e) ->
        let (formals, body, cl_env) =
            (match evalexp (Lambda (ns, e)) env with
             | Closure (fs, bod, env) -> (fs, bod, env)
             | _ -> raise (TypeError "Expecting closure."))
        in
        let loc = Env.mkloc () in
        let clo = Closure (formals, body, Env.bindloc (n, loc, cl_env)) in
        let () = loc := Some clo in
        (clo, Env.bindloc (n, loc, env))
    | Exp e -> (evalexp e env, env)

  let eval ast env =
    match ast with
    | Defexp d -> evaldef d env
    | e -> evalexp e env, env
end

exception MismatchError of string

let basis =
  let open Ast in
  let numprim name op =
    (name, (function [Fixnum a; Fixnum b] -> Fixnum (op a b)
            | _ -> raise (MismatchError ("(" ^ name ^ " int int)"))))
  in
  let cmpprim name op =
    (name, (function [Fixnum a; Fixnum b] -> Boolean (op a b)
            | _ -> raise (MismatchError ("(" ^ name ^ " int int)"))))
  in
  let rec prim_list = function
    | [] -> Nil
    | car::cdr -> Pair(car, prim_list cdr)
  in
  let prim_pair = function
    | [a; b] -> Pair(a, b)
    | _ -> raise (MismatchError "(pair a b)")
  in
  let prim_car = function
    | [Pair (car, _)] -> car
    | [e] -> raise (MismatchError ("(car non-nil-pair) " ^ string_val e))
    | _ -> raise (MismatchError "(car single-arg)")
  in
  let prim_cdr = function
    | [Pair (_, cdr)] -> cdr
    | [e] -> raise (MismatchError ("(cdr non-nil-pair) " ^ string_val e))
    | _ -> raise (MismatchError "(cdr single-arg)")
  in
  let prim_eq = function
    | [a; b] -> Boolean (a=b)
    | _ -> raise (MismatchError "(eq a b)")
  in
  let prim_symp = function
    | [Symbol _] -> Boolean true
    | [_] -> Boolean false
    | _ -> raise (MismatchError "(sym? single-arg)")
  in
  let prim_atomp = function
    | [Nil] -> Boolean true
    | [Pair (_, _)] -> Boolean false
    | [_] -> Boolean true
    | _ -> raise (MismatchError "(atom? single-arg)")
  in
  let prim_getchar = function
    | [] ->
        (try Fixnum (int_of_char @@ input_char stdin)
        with End_of_file -> Fixnum (-1))
    | _ -> raise (MismatchError "(getchar)")
  in
  let prim_print = function
    | [v] -> let () = print_string @@ string_val v in Symbol "ok"
    | _ -> raise (MismatchError "(print val)")
  in
  let prim_itoc = function
    | [Fixnum i] -> Symbol (stringOfChar @@ char_of_int i)
    | _ -> raise (MismatchError "(itoc int)")
  in
  let prim_cat = function
    | [Symbol a; Symbol b] -> Symbol (a ^ b)
    | _ -> raise (MismatchError "(cat sym sym)")
  in
  let newprim acc (name, func) =
    Env.bind (name, Primitive(name, func), acc)
  in
  List.fold_left newprim ["empty-symbol", ref (Some (Symbol ""))] [
    numprim "+" (+);
    numprim "-" (-);
    numprim "*" ( * );
    numprim "/" (/);
    cmpprim "<" (<);
    cmpprim ">" (>);
    cmpprim "=" (=);
    ("list", prim_list);
    ("pair", prim_pair);
    ("car", prim_car);
    ("cdr", prim_cdr);
    ("eq", prim_eq);
    ("atom?", prim_atomp);
    ("sym?", prim_symp);
    ("getchar", prim_getchar);
    ("print", prim_print);
    ("itoc", prim_itoc);
    ("cat", prim_cat);
  ]

let stdlib =
  let open Ast in
  let ev env e =
    match e with
    | Defexp _ -> Evaluator.eval e env
    | _ -> raise (MismatchError "Can only have definitions in stdlib")
  in
  let rec slurp stm env =
    try  stm |> Reader.read_exp |> ev env |> snd |> slurp stm
    with Stream.Failure -> env
  in
  let stm = PushbackReader.of_string "
  (define o (f g) (lambda (x) (f (g x))))
  (val caar (o car car))
  (val cadr (o car cdr))
  (val caddr (o cadr cdr))
  (val cadar (o car (o cdr car)))
  (val caddar (o car (o cdr (o cdr car))))

  (val cons pair)

  (val newline (itoc 10))
  (val space (itoc 32))

  ; This is pretty awkward looking because we have no other way to sequence
  ; operations. We have no begin, nothing.
  (define println (s)
    (let ((ok (print s)))
      (print newline)))

  ; This is less awkward because we actually use ic and c.
  (define getline ()
    (let* ((ic (getchar))
           (c (itoc ic)))
      (if (or (eq c newline) (eq ic ~1))
        empty-symbol
        (cat c (getline)))))

  (define null? (xs)
    (eq xs '()))

  (define length (ls)
    (if (null? ls)
      0
      (+ 1 (length (cdr ls)))))

  (define take (n ls)
    (if (or (< n 1) (null? ls))
      '()
      (cons (car ls) (take (- n 1) (cdr ls)))))

  (define drop (n ls)
    (if (or (< n 1) (null? ls))
      ls
      (drop (- n 1) (cdr ls))))

  (define merge (xs ys)
    (if (null? xs)
      ys
      (if (null? ys)
        xs
        (if (< (car xs) (car ys))
          (cons (car xs) (merge (cdr xs) ys))
          (cons (car ys) (merge xs (cdr ys)))))))

  (define mergesort (ls)
    (if (null? ls)
      ls
      (if (null? (cdr ls))
        ls
        (let* ((size (length ls))
               (half (/ size 2))
               (first (take half ls))
               (second (drop half ls)))
          (merge (mergesort first) (mergesort second))))))
  "
  in slurp stm basis

let rec repl stm env =
  PushbackReader.do_stdin stm "> " print_string;
  PushbackReader.do_stdin stm stdout flush;
  let ast = Reader.read_exp stm in
  let (result, env') = Evaluator.eval ast env in
  PushbackReader.do_stdin stm (Ast.string_val result) print_endline;
  repl stm env';;

let get_ic () =
  try  open_in Sys.argv.(1)
  with Invalid_argument s -> stdin

let main =
  let ic = get_ic () in
  try  repl (PushbackReader.of_channel ic) stdlib
  with Stream.Failure -> if ic <> stdin then close_in ic
