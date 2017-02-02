type stream =
  { mutable line_num: int; mutable chr: char list; chan: in_channel };;

let stringOfChar c =
    String.make 1 c;;

let read_char stm =
    match stm.chr with
      | [] ->
              let c = input_char stm.chan in
              if c = '\n' then let _ = stm.line_num <- stm.line_num + 1 in c
              else c
      | c::rest ->
              let _ = stm.chr <- rest in c

let unread_char stm c =
  stm.chr <- c :: stm.chr;;

let is_white c =
  c = ' ' || c = '\t' || c = '\n';;

let rec eat_whitespace stm =
  let c = read_char stm in
  if is_white c then
    eat_whitespace stm
  else
    unread_char stm c;
    ();;

(* type 'a env = (string * 'a) list *)

type lobject =
  | Fixnum of int
  | Boolean of bool
  | Symbol of string
  | Nil
  | Pair of lobject * lobject
  | Primitive of string * (lobject list -> lobject)
  | Quote of value

and value = lobject
and name = string
and exp =
  | Literal of value
  | Var of name
  | If of exp * exp * exp
  | And of exp * exp
  | Or of exp * exp
  | Apply of exp * exp
  | Call of exp * exp list
  | Defexp of def

and def =
  | Val of name * exp
  | Exp of exp

exception SyntaxError of string;;
exception ThisCan'tHappenError;;
exception NotFound of string;;

let bind (n, v, e) = Pair(Pair(Symbol n, v), e);;

let rec lookup (n, e) =
    match e with
    | Nil -> raise (NotFound n)
    | Pair(Pair(Symbol n', v), rst) ->
            if n=n' then v else lookup (n, rst)
    | _ -> raise ThisCan'tHappenError;;

let rec pair_to_list pr =
    match pr with
    | Nil -> []
    | Pair(a, b) -> a::(pair_to_list b)
    | _ -> raise ThisCan'tHappenError;;

let rec read_sexp stm =
  let is_digit c =
    let code = Char.code c in
    code >= Char.code('0') && code <= Char.code('9')
  in
  let rec read_fixnum acc =
    let nc = read_char stm in
    if is_digit nc
    then read_fixnum (acc ^ stringOfChar nc)
    else
      let _ = unread_char stm nc in
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
      let nc = read_char stm in
      if is_delimiter nc
      then let _ = unread_char stm nc in ""
      else stringOfChar nc ^ read_symbol ()
  in
  let rec read_list stm =              (* NEW *)
    eat_whitespace stm;
    let c = read_char stm in
    if c = ')' then
      Nil
    else
      let _ = unread_char stm c in
      let car = read_sexp stm in
      let cdr = read_list stm in
      Pair(car, cdr)
  in
  eat_whitespace stm;
  let c = read_char stm in
  if is_symstartchar c
  then Symbol(stringOfChar c ^ read_symbol ())
  else if is_digit c || c='~'
  then read_fixnum (stringOfChar (if c='~' then '-' else c))
  else if c = '('
  then read_list stm
  else if c = '#' then
      match (read_char stm) with
      | 't' -> Boolean(true)
      | 'f' -> Boolean(false)
      | x -> raise (SyntaxError ("Invalid boolean literal " ^ (stringOfChar x)))
  else if c = '\'' then Quote (read_sexp stm)
  else raise (SyntaxError ("Unexpected char " ^ (stringOfChar c)));;

let rec is_list e =
    match e with
        | Nil -> true
        | Pair(a, b) -> is_list b
        | _ -> false

let rec string_exp = function
  | Literal e -> string_val e
  | Var n -> n
  | If (c, t, f) ->
      "(if " ^ string_exp c ^ " " ^ string_exp t ^ " " ^ string_exp f ^ ")"
  | And (c0, c1) -> "(and " ^ string_exp c0 ^ " " ^ string_exp c1 ^ ")"
  | Or (c0, c1) -> "(or " ^ string_exp c0 ^ " " ^ string_exp c1 ^ ")"
  | Apply (f, e) -> "(apply " ^ string_exp f ^ " " ^ string_exp e ^ ")"
  | Call (f, es) ->
      let string_es = (String.concat " " (List.map string_exp es)) in
      "(" ^ string_exp f ^ " " ^ string_es ^ ")"
  | Defexp (Val (n, e)) -> "(val " ^ n ^ " " ^ string_exp e ^ ")"
  | Defexp (Exp e) -> string_exp e

and string_val e =
    let rec string_list l =
        match l with
        | Pair (a, Nil) -> string_val a
        | Pair (a, b) -> string_val a ^ " " ^ string_list b
        | _ -> raise ThisCan'tHappenError
    in
    let string_pair p =
        match p with
        | Pair (a, b) -> string_val a ^ " . " ^ string_val b
        | _ -> raise ThisCan'tHappenError
    in
    match e with
    | Fixnum v -> string_of_int v
    | Boolean b -> if b then "#t" else "#f"
    | Symbol s -> s
    | Nil -> "nil"
    | Pair (a, b) ->
            "(" ^ (if is_list e then string_list e else string_pair e) ^ ")"
    | Primitive (name, _) -> "#<primitive:" ^ name ^ ">"
    | Quote v -> "'" ^ string_val v


exception TypeError of string;;
exception ParseError of string

let rec eval sexp env =
  match sexp with
  | Literal l -> (l, env)
  | _ -> raise (TypeError "uh")

let rec build_ast sexp =
  match sexp with
  | Primitive _ -> raise ThisCan'tHappenError
  | Fixnum _ | Boolean _ | Nil | Quote _ -> Literal sexp
  | Symbol s -> Var s
  | Pair _ when is_list sexp ->
      (match pair_to_list sexp with
      | [Symbol "if"; cond; iftrue; iffalse] ->
          If (build_ast cond, build_ast iftrue, build_ast iffalse)
      | [Symbol "and"; c1; c2] -> And (build_ast c1, build_ast c2)
      | [Symbol "or"; c1; c2] -> Or (build_ast c1, build_ast c2)
      | [Symbol "quote"; e] -> Literal (Quote e)
      | [Symbol "val"; Symbol n; e] -> Defexp (Val (n, build_ast e))
      | [Symbol "apply"; fnexp; args] ->
          Apply (build_ast fnexp, build_ast args)
      | fnexp::args -> Call (build_ast fnexp, List.map build_ast args)
      | [] -> raise (ParseError "poorly formed expression"))
  | Pair _ -> Literal sexp

let rec evalexp exp env =
  let evalapply f es =
    match f with
    | Primitive (_, f) -> f es
    | _ -> raise (TypeError "(apply prim '(args)) or (prim args)")
  in
  let rec ev = function
    | Literal Quote e -> e
    | Literal l -> l
    | Var n -> lookup (n, env)
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
    | Call (Var "env", []) -> env
    | Call (e, es) -> evalapply (ev e) (List.map ev es)
    | Defexp d -> raise ThisCan'tHappenError
  in ev exp

let evaldef def env =
  match def with
  | Val (n, e) -> let v = evalexp e env in (v, bind (n, v, env))
  | Exp e -> (evalexp e env, env)

let eval ast env =
  match ast with
  | Defexp d -> evaldef d env
  | e -> (evalexp e env, env)

let rec repl stm env =
  print_string "> ";
  flush stdout;
  let ast = build_ast (read_sexp stm) in
  let (result, env') = eval ast env in
  print_endline (string_val result);
  repl stm env';;

let basis =
    let rec prim_list = function
        | [] -> Nil
        | car::cdr -> Pair(car, prim_list cdr)
    in
    let prim_plus = function
        | [Fixnum(a); Fixnum(b)] -> Fixnum(a+b)
        | _ -> raise (TypeError "(+ int int)")
    in
    let prim_pair = function
        | [a; b] -> Pair(a, b)
        | _ -> raise (TypeError "(pair a b)")
    in
    let newprim acc (name, func) =
        bind (name, Primitive(name, func), acc)
    in
    List.fold_left newprim Nil [
        ("list", prim_list);
        ("+", prim_plus);
        ("pair", prim_pair)
       ]

let main =
  let stm = { chr=[]; line_num=1; chan=stdin } in
  repl stm basis;;
