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
  let rec read_string stm =
    let c = read_char stm in
    if c = '"' then "" else stringOfChar c ^ read_string stm
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
  else if c = '"' then Quote (Symbol (read_string stm))
  else raise (SyntaxError ("Unexpected char " ^ (stringOfChar c)));;

let rec is_list e =
    match e with
        | Nil -> true
        | Pair(a, b) -> is_list b
        | _ -> false


exception TypeError of string;;
exception ParseError of string

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
    | Quote v -> "(quote " ^ string_val v ^ ")"
    | Primitive (name, _) -> "#<primitive:" ^ name ^ ">"
    | Closure (ns, e, _) -> "#<closure>"

let rec pair_to_list pr =
    match pr with
    | Nil -> []
    | Pair(a, b) -> a::(pair_to_list b)
    | _ -> raise ThisCan'tHappenError;;

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

let rec read_asts stm =
  try
    let ast = build_ast (read_sexp stm) in
    let () = prerr_endline (string_exp ast) in
    ast::(read_asts stm)
  with End_of_file -> []

let rec transform_ast ast =
  let open Ast_helper in
  let open Asttypes in
  let open Parsetree in
  let mklid s = Location.mknoloc (Longident.parse s) in
  let unit_ = Exp.construct (mklid "()") None in
  let mkvarpat name = Pat.var (Location.mknoloc name) in
  let rec tr = function
  | Literal Fixnum i -> Exp.constant (Const_int i)
  | Literal Boolean true -> Exp.construct (mklid "true") None
  | Literal Boolean false -> Exp.construct (mklid "false") None
  | Literal Symbol s -> Exp.constant (Const_string (s, None))
  | Literal Nil -> unit_
  | Literal Quote Nil -> Exp.construct (mklid "[]") None
  | Literal Quote Symbol s -> tr (Literal (Symbol s))
  | Literal Quote Pair (a, b) when is_list (Pair (a, b)) ->
      Exp.construct (mklid "::") (Some (Exp.tuple [tr (Literal a);
                                                   tr (Literal (Quote b))]))
  | Var name -> Exp.ident (mklid name)
  | If (c, b1, b2) -> Exp.ifthenelse (tr c) (tr b1) (Some (tr b2))
  | And (e1, e2) -> tr (Call (Var "&&", [e1; e2]))
  | Or (e1, e2) -> tr (Call (Var "||", [e1; e2]))
  | Call (fn, args) -> Exp.apply (tr fn) (List.map (fun e -> "", tr e) args)
  (* TODO: fix. lambdas with 0 args currently just eval to body *)
  (* like: mkfun (Pat.any ()) (tr body) *)
  | Lambda ([], body) -> (tr body)
  | Lambda (n::ns, body) -> Exp.fun_ "" None (mkvarpat n) (tr (Lambda (ns, body)))
  | Defexp d -> failwith "can't transform defexp here"
  | _ -> failwith "unknown transform"
  in
  match ast with
  | Defexp (Val (n, e)) -> Str.value Nonrecursive [Vb.mk (mkvarpat n) (tr e)]
  | Defexp (Def (n, formals, e)) -> transform_ast (Defexp (Val (n, (Lambda (formals, e)))))
  | Defexp (Exp e) -> Str.eval (tr e)
  | e -> Str.eval (tr e)

let process_file stm filename =
  let structure = List.map transform_ast (read_asts stm) in
  (* let () = Printast.implementation Format.err_formatter structure in *)
  output_string stdout Config.ast_impl_magic_number;
  output_value  stdout filename;
  output_value  stdout structure

let main =
  let filename = Sys.argv.(1) in
  let filechan = open_in filename in
  let stm = { chr=[]; line_num=1; chan=filechan } in
  let () = process_file stm filename in
  close_in filechan
