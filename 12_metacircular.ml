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

type 'a env = (string * 'a option ref) list

type lobject =
  | Fixnum of int
  | Boolean of bool
  | Symbol of string
  | Nil
  | Pair of lobject * lobject
  | Primitive of string * (lobject list -> lobject)
  | Quote of value
  | Closure of name list * exp * value env

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
  | Lambda of name list * exp
  | Defexp of def

and def =
  | Val of name * exp
  | Def of name * name list * exp
  | Exp of exp

exception SyntaxError of string;;
exception ThisCan'tHappenError;;
exception NotFound of string;;
exception UnspecifiedValue of string

let mkloc () = ref None
let bind (n, v, e) = (n, ref (Some v))::e
let bindloc : name * 'a option ref * 'a env -> 'a env = fun (n, vor, e) -> (n, vor)::e

let rec lookup : name * 'a env -> 'a = function
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

let rec env_to_val =
  let b_to_val (n, vor) =
    Pair (Symbol n, (match !vor with
                     | None -> Symbol "unspecified"
                     | Some v -> v))
  in
  function
    | [] -> Nil
    | b::bs -> Pair(b_to_val b, env_to_val bs)


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

let spacesep ns = String.concat " " ns

let rec string_exp =
  let spacesep_exp es = spacesep (List.map string_exp es) in
  function
  | Literal e -> string_val e
  | Var n -> n
  | If (c, t, f) ->
      "(if " ^ string_exp c ^ " " ^ string_exp t ^ " " ^ string_exp f ^ ")"
  | And (c0, c1) -> "(and " ^ string_exp c0 ^ " " ^ string_exp c1 ^ ")"
  | Or (c0, c1) -> "(or " ^ string_exp c0 ^ " " ^ string_exp c1 ^ ")"
  | Apply (f, e) -> "(apply " ^ string_exp f ^ " " ^ string_exp e ^ ")"
  | Call (f, es) -> "(" ^ string_exp f ^ " " ^ spacesep_exp es ^ ")"
  | Lambda (ns, e) -> "#<lambda>"
  | Defexp (Val (n, e)) -> "(val " ^ n ^ " " ^ string_exp e ^ ")"
  | Defexp (Def (n, ns, e)) ->
          "(define " ^ n ^ "(" ^ spacesep ns ^ ") " ^ string_exp e ^ ")"
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
    | Quote v -> "'" ^ string_val v
    | Primitive (name, _) -> "#<primitive:" ^ name ^ ">"
    | Closure (ns, e, _) -> "#<closure>"
        (* "[lambda (" ^ spacesep ns ^ ") " ^ string_exp e ^ "]" *)


exception TypeError of string;;
exception ParseError of string

let rec build_ast sexp =
  let rec cond_to_if = function
    | [] -> Literal (Symbol "error")
    | (Pair(cond, Pair(res, Nil)))::condpairs ->
        If (build_ast cond, build_ast res, cond_to_if condpairs)
    | _ -> raise (TypeError "(cond c0 c1 c2 c3 ...)")
  in
  match sexp with
  | Primitive _ | Closure _ -> raise ThisCan'tHappenError
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
      | [Symbol "lambda"; ns; e] when is_list ns ->
          let err () = raise (TypeError "(lambda (formals) body)") in
          let names = List.map (function Symbol s -> s | _ -> err ())
                               (pair_to_list ns)
          in Lambda (names, build_ast e)
      | [Symbol "define"; Symbol n; ns; e] ->
          let err () = raise (TypeError "(define name (formals) body)") in
          let names = List.map (function Symbol s -> s | _ -> err ())
                               (pair_to_list ns)
          in Defexp (Def (n, names, build_ast e))
      | [Symbol "apply"; fnexp; args] ->
          Apply (build_ast fnexp, build_ast args)
      | (Symbol "cond")::conditions -> cond_to_if conditions
      | fnexp::args -> Call (build_ast fnexp, List.map build_ast args)
      | [] -> raise (ParseError "poorly formed expression"))
  | Pair _ -> Literal sexp

let extend newenv oldenv =
  List.fold_right (fun (b, v) acc -> bindloc (b, v, acc)) newenv oldenv

let rec evalexp exp env =
  let evalapply f vs =
    match f with
    | Primitive (_, f) -> f vs
    | Closure (ns, e, clenv) ->
        evalexp e (extend (bindlist ns vs clenv) env)
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
    | Call (Var "env", []) -> env_to_val env
    | Call (e, es) -> evalapply (ev e) (List.map ev es)
    | Lambda (ns, e) -> Closure (ns, e, env)
    | Defexp d -> raise ThisCan'tHappenError
  in ev exp

let evaldef def env =
  match def with
  | Val (n, e) -> let v = evalexp e env in (v, bind (n, v, env))
  | Def (n, ns, e) ->
      let (formals, body, cl_env) =
          (match evalexp (Lambda (ns, e)) env with
           | Closure (fs, bod, env) -> (fs, bod, env)
           | _ -> raise (TypeError "Expecting closure."))
      in
      let loc = mkloc () in
      let clo = Closure (formals, body, bindloc (n, loc, cl_env)) in
      let () = loc := Some clo in
      (clo, bindloc (n, loc, env))
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

exception UserError of string

let basis =
  let numprim name op =
    (name, (function [Fixnum a; Fixnum b] -> Fixnum (op a b)
            | _ -> raise (TypeError ("(" ^ name ^ " int int)"))))
  in
  let cmpprim name op =
    (name, (function [Fixnum a; Fixnum b] -> Boolean (op a b)
            | _ -> raise (TypeError ("(" ^ name ^ " int int)"))))
  in
  let rec prim_list = function
    | [] -> Nil
    | car::cdr -> Pair(car, prim_list cdr)
  in
  let prim_pair = function
    | [a; b] -> Pair(a, b)
    | _ -> raise (TypeError "(pair a b)")
  in
  let prim_car es =
    (* let s = String.concat ", " (List.map string_val es) in
    let () = print_endline ("car on " ^ s) in *)
    match es with
    | [Pair (car, _)] -> car
    | [e] -> raise (TypeError ("(car non-nil-pair) " ^ string_val e))
    | _ -> raise (TypeError "(car single-arg)")
  in
  let prim_cdr = function
    | [Pair (_, cdr)] -> cdr
    | [e] -> raise (TypeError ("(cdr non-nil-pair) " ^ string_val e))
    | _ -> raise (TypeError "(cdr single-arg)")
  in
  let prim_eq = function
    | [a; b] -> Boolean (a=b)
    | _ -> raise (TypeError "(eq a b)")
  in
  let prim_symp = function
    | [Symbol _] -> Boolean true
    | [_] -> Boolean false
    | _ -> raise (TypeError "(sym? single-arg)")
  in
  let prim_atomp = function
    | [Nil] -> let () = print_endline "nil!!!" in Boolean true
    | [Pair (_, _)] -> Boolean false
    | [_] -> Boolean true
    | _ -> raise (TypeError "(atom? single-arg)")
  in
  let prim_error = function
    | [Symbol s] -> raise (UserError s)
    | _ -> raise (TypeError "(error sym)")
  in
  let prim_cat = function
    | [Symbol a; Symbol b] -> Symbol (a ^ b)
    | _ -> raise (TypeError "(cat sym1 sym2)")
  in
  let newprim acc (name, func) =
    bind (name, Primitive(name, func), acc)
  in
  List.fold_left newprim [] [
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
    ("error", prim_error);
    ("cat", prim_cat)
  ]

let main =
  let stm = { chr=[]; line_num=1; chan=stdin } in
  repl stm basis;;
