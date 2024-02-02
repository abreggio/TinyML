(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

let mutable COUNTER = 0

let get_fresh () = COUNTER <- COUNTER + 1; COUNTER

let print_type typ = printfn "%s" <| pretty_ty typ

type subst = (tyvar * ty) list

// TODO implement this
let rec apply_subst (t : ty) (s : subst) : ty = 
  match s with
    | [] -> t
    | s1 :: cons -> match t with
                      | TyName s -> t
                      | TyVar i1 -> if i1 = (fst s1)
                                      then snd s1
                                      else apply_subst t cons
                      | TyArrow (a1, a2) -> TyArrow (apply_subst a1 s, apply_subst a2 s)
                      | TyTuple l1 -> TyTuple (List.map (fun x -> apply_subst x s) l1)

let rec apply_subst_to_env (enviroment: scheme env) (s: subst): scheme env =
  match enviroment with
    | [] -> []
    | e :: cons -> 
      let 
        apply_subst_scheme (a: string * scheme) (subst: subst) = 
          let scheme = snd a
          let set_var, t = match scheme with Forall (c,b) -> c,b
          let pred x = Set.contains (fst x) set_var
          let s2 = List.filter <| (not << pred) <| subst
          in (fst a, Forall (set_var, apply_subst t s2))
      in 
        (apply_subst_scheme e s) :: (apply_subst_to_env cons s)


// dio boia quanto tempo ho perso perché qui . è <<

// TODO implement this
let rec compose_subst (s1 : subst) (s2 : subst) : subst =
  match s1 with
    | [] -> s2
    | left :: cons -> (fst left , apply_subst (snd left) s2) :: (compose_subst cons s2)

let ($) (s1 : subst) (s2 : subst) : subst = compose_subst s2 s1

// TODO implement this
let rec unify (t1 : ty) (t2 : ty) : subst = 
  match (t1, t2) with
    | TyName s1, TyName s2 -> if s1 = s2
                                then []
                                else type_error "cannot unify different primitive types"
    | TyVar i1, _ -> [(i1, t2)]
    | _, TyVar i1 -> [(i1, t1)]
    | TyArrow (a1, a2), TyArrow (a3, a4) -> (unify a1 a3) $ (unify a4 a2)
    | TyTuple l1, TyTuple l2 -> []
    | _, _ -> type_error "no rule for type merge"

// TODO implement this
let rec freevars_ty (t: ty) : tyvar Set= 
  match t with
    | TyName s1 -> Set.empty
    | TyVar i1 -> Set.singleton i1
    | TyArrow (a1, a2) -> Set.union <| freevars_ty a1 <| freevars_ty a2
    | TyTuple l -> List.fold Set.union Set.empty <| List.map freevars_ty l

// TODO implement this
let freevars_scheme (Forall (tvs, t)): tyvar Set = Set.difference <| freevars_ty t <| tvs

// TODO implement this
let rec freevars_scheme_env (env: scheme env) =
  match env with
    | [] -> Set.empty
    | l :: cons -> Set.union <| freevars_scheme (snd l) <| freevars_scheme_env cons

let gen (env : scheme env) (t : ty) : scheme = 
  let variables_type = freevars_ty t
  let variables_env = freevars_scheme_env env
  let variables_scheme = Set.difference variables_type variables_env
  Forall (variables_scheme, t)

let rec re (scheme_vars : tyvar Set) (t:ty) : subst = 
  match t with
    | TyName s -> []
    | TyVar i1 -> if Set.contains i1 scheme_vars
                            then [(get_fresh (), t)]
                            else []
    | TyArrow (t1, t2) -> (re scheme_vars t1) $ (re scheme_vars t2)
    | TyTuple l -> match l with
                               | [] -> []
                               | head::cons -> (re scheme_vars head) $ (re scheme_vars (TyTuple cons))

let inst (Forall (tvs, t)) : ty = apply_subst t (re tvs t)

// basic environment: add builtin operators at will
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("<", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    (">", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
]

let gamma_scheme0 = [
  ("+", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
  ("-", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
  ("*", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
  ("<", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
  (">", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
  ("<=", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
  (">=", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
  ("=", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
  ("<>", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
]
// type inference
//

let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []
    | BinOp (e1, op, e2) ->
        let t, s = typeinfer_expr env (App (App (Var op, e1), e2))
        t, s
    // TODO complete this implementation
    | Let (x, None, e1, e2) ->
      let t1, s1 = typeinfer_expr env e1
      let env_s1 = apply_subst_to_env env s1
      let scheme1 = gen env_s1 t1
      let t2, s2 = typeinfer_expr ((x, scheme1) :: env_s1) e2
      let s3 = s2 $ s1
      t2, s3

    | LetRec (x, tyo, e1, e2) -> 
      let n = TyVar (get_fresh ())
      let t1, s1 = typeinfer_expr <| (x, Forall(Set.empty, n)) :: env <| e1
      let gamma1 = apply_subst_to_env env s1
      let sigma1 = gen env t1
      let t2, s2 = typeinfer_expr <| (x, sigma1) :: gamma1 <| e2
      let s3 = unify n <| apply_subst t1 s1
      let s4 = s3 $ s2 $ s1
      t2, s4

    | Var x -> inst (snd <| List.find (fun el -> (fst el) = x ) env), []

    | Lambda (x, None, e) ->
        let n = TyVar (get_fresh ())
        let closure = (x, Forall(Set.empty, n)) :: env
        let t2, s1 = typeinfer_expr closure e
        let t1 = apply_subst n s1
        TyArrow (t1, t2), s1

    | App (e1, e2) ->
      let t1, s1 = typeinfer_expr env e1
      let t2, s2 = typeinfer_expr (apply_subst_to_env env s1) e2
      let n = TyVar (get_fresh ())
      let s3 = unify t1 (TyArrow (t2, n))
      let t3 = apply_subst n s3
      let s4 = s3 $ s2 $ s1
      t3, s4

    | IfThenElse (e1, e2, Some e3) ->
      // TODO optionally you can follow the original type inference rule and apply/compose substitutions incrementally (see Advanced Notes on ML, Table 4, page 5)
      let t1, s1 = typeinfer_expr env e1
      let s2 = unify t1 TyBool
      let t2, s3 = typeinfer_expr env e2
      let t3, s4 = typeinfer_expr env e3
      let s5 = unify t2 t3
      let s = s5 $ s4 $ s3 $ s2 $ s1
      apply_subst t2 s, s

    | Tuple l -> 
      let rec infer_type_list (env: scheme env) (type_list: expr list) =
        match type_list with
          | [] -> []
          | left::cons -> let (a, b) = typeinfer_expr env left in (a, b) :: (infer_type_list <| apply_subst_to_env env b <| cons)
      let s0 = []
      let ty_list_subs = infer_type_list env l 
      let ty_list, subs_list = List.unzip ty_list_subs
      let sub = List.head << List.rev <| subs_list
      (TyTuple ty_list), sub

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e


// type checker
//
// optionally, a simple type checker (without type inference) could be implemented
// you might start implementing this for simplicity and eventually write the type inference once you gain familiarity with the code

let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Let (x, None, e1, e2) ->
        let t1 = typecheck_expr env e1
        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Var x ->  snd <| List.find (fun el -> (fst el) = x) env

    | Let (x, Some t, e1, e2) ->
        let t1 = typecheck_expr env e1
        if t <> t1 then type_error "type %O differs from type %O in let-binding" t1 t 
        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Lambda (x, Some t, e) ->
        let env' = (x, t) :: env
        let te = typecheck_expr env' e
        TyArrow (t, te)

    | Lambda (x, None, e) ->
        type_error "unannotated lambdas are not supported by the type checker"

    | App (e1, e2) ->
        let t2 = typecheck_expr env e2
        match typecheck_expr env e1 with
        | TyArrow (ta, tb) -> 
            if ta <> t2 then type_error "argument has type %O while function parameter has type %O in application" t2 ta
            tb
        | t1 -> type_error "left hand of application is not an arrow type: %O" t1

    | IfThenElse (e1, e2, Some e3) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "bool expected in if guard, but got %O" t1
        let t2 = typecheck_expr env e2
        let t3 = typecheck_expr env e3
        if t2 <> t3 then type_error "then and else branches have different types: %O and %O" t2 t3
        t2

    | BinOp (e1, ("+" | "-" | "*" | "/" as op), e2) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyInt then type_error "left hand of (%s) operator is not an int: %O" op t1
        let t2 = typecheck_expr env e2
        if t2 <> TyInt then type_error "right hand of (%s) operator is not an int: %O" op t2
        TyInt

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "operand of not-operator is not a bool: %O" t
        TyBool
        
    | BinOp (e1, "=", e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        if t1 <> t2 then type_error "left and right hands of equality operator are different: %O and %O" t1 t2
        TyBool

    | BinOp (e1, ("<" | ">" | "<=" | ">=" as op), e2) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyInt then type_error "left hand of (%s) operator is not an int: %O" op t1
        let t2 = typecheck_expr env e2
        if t2 <> TyInt then type_error "right hand of (%s) operator is not an int: %O" op t2
        TyBool

    | Tuple es -> TyTuple (List.map (typecheck_expr env) es)
    // TODO optionally complete this implementation

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
