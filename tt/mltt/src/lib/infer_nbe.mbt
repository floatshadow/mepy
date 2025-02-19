///|
typealias VEnv = @immut/hashmap.T[String, Value]

///|
typealias NameList = @immut/list.T[String]

// Normalization by evaluation.
// Substitution based normalization simply repeatedly applies β-reduction.
// NbE does normalization in a way of interpreting the term.
// Major problems in developing NbE:
//  - Term may contains free variables, how to eval such open terms?
//    f a -> (fun x -> ...) a, but f may get stuck (neutral form)
//    Solution: we admit free variables as a value.
//  - Admit free variables as value would ban further evaluations.
//    f arg1 arg2 ... ->

///|
pub enum Value {
  VNe(Neutral)
  VUniverse(Int)
  VTyFun(Value, (Value) -> Value!Failure) // HOAS
  VLam(Value, (Value) -> Value!Failure)
} derive(Show)

///|
pub enum Neutral {
  NeVar(String)
  NeApp(Neutral, Value)
} derive(Show)

///|
pub fn eval(env : VEnv, expr : Syntax) -> Value!Failure {
  match expr {
    Var(x) => env.find(x).unwrap()
    Universe(i) => VUniverse(i)
    TyFun(param_name, param_ty, return_ty) =>
      VTyFun(eval!(env, param_ty), fn(param_value) {
        eval!(env.add(param_name, param_value), return_ty)
      })
    Lam(param_name, param_ty, body) =>
      VLam(eval!(env, param_ty), fn(param_value) {
        eval!(env.add(param_name, param_value), body)
      })
    App(func, arg) =>
      match eval!(env, func) {
        VLam(_, f) => f!(eval!(env, arg))
        VNe(ne) => VNe(NeApp(ne, eval!(env, arg)))
        _ => fail!("should not happen")
      }
  }
}

///|
fn neutral_to_expr(ne : Neutral, names : NameList) -> Syntax!Failure {
  match ne {
    NeVar(x) => Var(x)
    NeApp(ne, value) =>
      App(neutral_to_expr!(ne, names), value_to_expr!(value, names))
  }
}

///|
pub fn value_to_expr(value : Value, names : NameList) -> Syntax!Failure {
  fn fresh_name(names : NameList) -> String {
    loop 0 {
      i => {
        let name = "x\{i}"
        if names.contains(name) {
          continue i + 1
        } else {
          break name
        }
      }
    }
  }

  match value {
    VNe(ne) => neutral_to_expr!(ne, names)
    VUniverse(i) => Universe(i)
    VTyFun(param_ty_value, return_ty_func) => {
      // original param name may coincide with variables in env
      let name = fresh_name(names)
      TyFun(
        name,
        value_to_expr!(param_ty_value, names),
        value_to_expr!(return_ty_func!(VNe(NeVar(name))), names.add(name)),
      )
    }
    VLam(param_ty_value, body_func) => {
      let name = fresh_name(names)
      Lam(
        name,
        value_to_expr!(param_ty_value, names),
        value_to_expr!(body_func!(VNe(NeVar(name))), names.add(name)),
      )
    }
  }
}

///|
pub struct NbEContext {
  values : VEnv
  names : NameList
  typs : VEnv
}

///|
pub fn NbEContext::empty() -> NbEContext {
  NbEContext::{
    values: @immut/hashmap.new(),
    names: Nil,
    typs: @immut/hashmap.new(),
  }
}

///|
pub fn NbEContext::add_var(
  self : NbEContext,
  name : String,
  typ : Value
) -> NbEContext {
  let value = VNe(NeVar(name))
  NbEContext::{
    values: self.values.add(name, value),
    names: self.names.add(name),
    typs: self.typs.add(name, typ),
  }
}

///|
fn normalize_nbe(nbectx : NbEContext, expr : Syntax) -> Syntax!Failure {
  value_to_expr!(eval!(nbectx.values, expr), nbectx.names)
}

///|
fn values_are_equal(
  nbectx : NbEContext,
  value1 : Value,
  value2 : Value
) -> Bool!Failure {
  let expr1 = value_to_expr!(value1, nbectx.names)
  let expr2 = value_to_expr!(value2, nbectx.names)
  expr1 == expr2
}

///|
pub fn infer_nbe(env : NbEContext, expr : Syntax) -> Value!Failure {
  fn check_expr_is_type(env, expr) -> Int!Failure {
    match infer_nbe!(env, expr) {
      VUniverse(i) => i
      _ => fail!("not a type")
    }
  }

  match expr {
    Var(x) => env.typs.find(x).unwrap()
    Universe(i) => VUniverse(i + 1)
    TyFun(param_name, param_ty, return_ty) => {
      let param_universe = check_expr_is_type!(env, param_ty)
      // param_ty is guranteed to be a type, eval param_ty
      let param_ty_value = eval!(env.values, param_ty)
      let env2 = env.add_var(param_name, param_ty_value)
      let return_universe = check_expr_is_type!(env2, return_ty)
      VUniverse(@math.maximum(param_universe, return_universe))
    }
    Lam(param_name, param_ty, body) => {
      let _ = check_expr_is_type!(env, param_ty)
      let param_ty_value = eval!(env.values, param_ty)
      let env2 = env.add_var(param_name, param_ty_value)
      let return_ty_value = infer_nbe!(env2, body)
      let return_ty_expr = value_to_expr!(return_ty_value, env2.names)
      VTyFun(param_ty_value, fn(param_value) {
        eval!(env2.values.add(param_name, param_value), return_ty_expr)
      })
    }
    App(func, args) => {
      let func_ty = infer_nbe!(env, func)
      let arg_ty = infer_nbe!(env, args)
      // no need to normalize
      match func_ty {
        VTyFun(param_ty, return_ty_func) =>
          if values_are_equal!(env, arg_ty, param_ty) {
            let arg_ty_value = eval!(env.values, args)
            return_ty_func!(arg_ty_value)
          } else {
            fail!("argument type mismatch")
          }
        _ => fail!("expected a function type")
      }
    }
  }
}
