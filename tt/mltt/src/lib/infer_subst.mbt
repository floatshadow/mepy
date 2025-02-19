///|
pub typealias NameMap = @immut/hashmap.T[String, String]

///|
pub typealias Env = @immut/hashmap.T[String, Syntax]

// In dependent type, the type equality is not simply syntactic equality:
// e.g. (application) (fun x -> x) nat = nat
// e.g. (conversion)
// Γ |- t : A
// Γ |- A = B : Set
// ---------------- (conv)
// Γ |- t : B
//
// Whenever there happens type equality, we should first
// normalize the type and then compare them. 
///|
pub fn check_expr_is_type(env : Env, expr : Syntax) -> Int!Failure {
  match normalize_subst!(infer_subst!(env, expr)) {
    Universe(i) => i
    _ => fail!("expression is expected to be a type")
  }
}

///|
fn check_occur(name : String, expr : Syntax) -> Bool {
  match expr {
    Var(n) => n == name
    Universe(_) => false
    TyFun(param_name, param_ty, return_ty) =>
      if param_name == name {
        false
      } else {
        check_occur(name, param_ty) || check_occur(name, return_ty)
      }
    Lam(param_name, param_ty, body) =>
      if param_name == name {
        false
      } else {
        check_occur(name, param_ty) || check_occur(name, body)
      }
    App(func, arg) => check_occur(name, func) || check_occur(name, arg)
  }
}

///|
fn subst(name : String, subst_to : Syntax, expr : Syntax) -> Syntax!Failure {
  match expr {
    Var(n) => if n == name { subst_to } else { expr }
    Universe(_) as u => u
    TyFun(param_name, param_ty, return_ty) =>
      if param_name == name {
        TyFun(param_name, subst!(name, subst_to, param_ty), return_ty)
      } else if check_occur(param_name, subst_to) {
        // free variables in `subst_to` would be captured by lambda
        fail!("substitution would be captured")
      } else {
        TyFun(
          param_name,
          subst!(name, subst_to, param_ty),
          subst!(name, subst_to, return_ty),
        )
      }
    Lam(param_name, param_ty, body) =>
      if param_name == name {
        Lam(param_name, subst!(name, subst_to, param_ty), body)
      } else if check_occur(param_name, subst_to) {
        fail!("substitution would be captured")
      } else {
        Lam(
          param_name,
          subst!(name, subst_to, param_ty),
          subst!(name, subst_to, body),
        )
      }
    App(func, arg) =>
      App(subst!(name, subst_to, func), subst!(name, subst_to, arg))
  }
}

///|
pub fn normalize_subst(expr : Syntax) -> Syntax!Failure {
  match expr {
    Var(_) as v => v
    Universe(_) as u => u
    TyFun(param_name, param_ty, return_ty) =>
      TyFun(param_name, normalize_subst!(param_ty), normalize_subst!(return_ty))
    Lam(param_name, param_ty, body) =>
      Lam(param_name, normalize_subst!(param_ty), normalize_subst!(body))
    App(func, arg) =>
      match normalize_subst!(func) {
        Lam(param_name, _, body) =>
          normalize_subst!(subst!(param_name, arg, body))
        _ as f => App(f, normalize_subst!(arg))
      }
  }
}

// (alpha conversion) λ x. x = λ y. y

///|
pub fn alpha_equiv(maps : NameMap, expr1 : Syntax, expr2 : Syntax) -> Bool {
  match (expr1, expr2) {
    (Var(name1), Var(name2)) =>
      match maps.find(name1) {
        Some(n) => n == name2
        None => name1 == name2
      }
    (Universe(u1), Universe(u2)) => u1 == u2
    (TyFun(n1, p1, r1), TyFun(n2, p2, r2)) =>
      alpha_equiv(maps, p1, p2) && alpha_equiv(maps.add(n1, n2), r1, r2)
    (Lam(n1, p1, b1), Lam(n2, p2, b2)) =>
      alpha_equiv(maps, p1, p2) && alpha_equiv(maps.add(n1, n2), b1, b2)
    (App(f1, a1), App(f2, a2)) =>
      alpha_equiv(maps, f1, f2) && alpha_equiv(maps, a1, a2)
    _ => false
  }
}

///|
fn expr_equal(expr1 : Syntax, expr2 : Syntax) -> Bool!Failure {
  alpha_equiv(
    @immut/hashmap.new(),
    normalize_subst!(expr1),
    normalize_subst!(expr2),
  )
}

///|
pub fn infer_subst(env : Env, expr : Syntax) -> Syntax!Failure {
  match expr {
    Var(x) => env.find(x).unwrap()
    Universe(i) => Universe(i + 1)
    TyFun(param_name, param_ty, return_ty) => {
      let universe_param = check_expr_is_type!(env, param_ty)
      let env2 = env.add(param_name, param_ty)
      let universe_return = check_expr_is_type!(env2, return_ty)
      Universe(@math.maximum(universe_param, universe_return))
    }
    Lam(param_name, param_ty, body) => {
      let _ = check_expr_is_type!(env, param_ty)
      let env2 = env.add(param_name, param_ty)
      let body_ty = infer_subst!(env2, body)
      TyFun(param_name, param_ty, body_ty)
    }
    App(func, arg) => {
      let func_ty = infer_subst!(env, func)
      let arg_ty = infer_subst!(env, arg)
      match normalize_subst!(func_ty) {
        // Γ |- f: Π (x:A). B
        // Γ |- a: A
        // -------------------
        // Γ |- f a: B[x := a]
        TyFun(param_name, param_ty, return_ty) =>
          if expr_equal!(arg_ty, param_ty) {
            subst!(param_name, arg, return_ty)
          } else {
            fail!("argument type mismatch")
          }
        _ => fail!("expected a function type")
      }
    }
  }
}
