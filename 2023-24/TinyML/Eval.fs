(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

// evaluator
//

let rec eval_expr (venv : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Lambda (x, _, e) -> Closure (venv, x, e)

    | App (e1, e2) -> 
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        match v1 with
        | Closure (venv', x, e) ->
            let venv' = (x, v2) :: venv'
            eval_expr venv' e
        | RecClosure (venv', f, x, e) ->
            let venv' = (f, v1) :: (x, v2) :: venv'
            eval_expr venv' e

        | _ -> unexpected_error "non-closure on left hand of application"
        
    | Let (x, _, e1, e2) ->
      let v1 = eval_expr venv e1
      let v2 = eval_expr <| (x, v1) :: venv <| e2
      v2

    | Tuple l ->
      let value_list = List.map <| eval_expr venv <| l
      VTuple value_list
    
    | Var x -> snd <| List.find (fun el -> (fst el) = x) venv

    | LetRec (x, _, e1, e2) ->
      let v1 = eval_expr venv e1
      match v1 with
      | Closure (venv', s, e) ->
        let v1' = RecClosure(venv', x, s, e)
        let venv' = (x, v1') :: venv
        eval_expr venv' e2 
      | _ -> eval_expr <| (x, v1) :: venv <| e2
      
    | BinOp (e1, ("+" | "-" | "*" | "<" | ">" | "<=" | ">=" | "<>" | "=" as op), e2) ->
      let v1 = eval_expr venv e1
      let v2 = eval_expr venv e2
      let i1, i2 = 
        match v1, v2 with
          | VLit (LInt v1), VLit (LInt v2) -> v1, v2
          | _, _ -> unexpected_error "Unexpected operands in %s:\n first operand:%s\n second operand:%s" op <| pretty_value v1 <| pretty_value v2
      match op with
        | "+" -> VLit (LInt (i1 + i2))
        | "-" -> VLit (LInt (i1 - i2))
        | "*" -> VLit (LInt (i1 * i2))
        | "<" -> VLit (LBool (i1 < i2))
        | ">" -> VLit (LBool (i1 > i2))
        | ">=" -> VLit (LBool (i1 >= i2))
        | "<=" -> VLit (LBool (i1 <= i2))
        | "<>" -> VLit (LBool (i1 <> i2))
        | "=" -> VLit (LBool (i1 = i2))
        | _ -> unexpected_error "unexpected operation: %s" op

    | IfThenElse (e1, e2, e3) ->
      let v1 = eval_expr venv e1
      let bool_valuation = 
        match v1 with
          | VLit (LBool (b)) -> b
      if bool_valuation
        then eval_expr venv e2 
        else match e3 with | None -> VLit LUnit | Some e -> eval_expr venv e
    // TODO complete this implementation

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
