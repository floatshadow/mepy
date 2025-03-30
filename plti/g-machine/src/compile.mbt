
// In summary, the code generated for a supercombinator is to:
//   - construct the rhs of the supercombinator
//   - Slide n + 1, where n is the arity of the supercombinator
//   - Unwind, where Unwind is the instruction to cause machine evaluation to continue.
pub fn compile_sc(self: ScDef[String]) -> (String, Int, List[Instruction])!Failure {
  let name = self.name
  let body = self.body
  let mut arity = 0
  fn gen_ctx(i: Int, args: List[String]) -> List[(String, Int)] {
    match args {
      Nil => {
        arity = i
        Nil
      }
      Cons(s, ss) => Cons((s, i), gen_ctx(i + 1, ss))
    }
  }
  // relative offset of parameters on the stack.
  let ctx = gen_ctx(0, self.args)
  (name, arity, compile_r!(body, ctx, arity))
}


// `compileR` attach three instructions on generated code
// of super combinator:
//   - `Update(N)`, update the redex to `NInd` node.
//   - `Pop(N)`, clean addresses off the stack.
//   - `Unwind`, find the next redex.
pub fn compile_r(
  self : RawExpr[String],
  ctx : List[(String, Int)],
  arity : Int
) -> List[Instruction]!Failure {
  if arity == 0 {
    compile_c!(self, ctx) + @immut/list.of([Update(arity), Unwind])
  } else {
    compile_c!(self, ctx) + @immut/list.of([Update(arity), Pop(arity), Unwind])
  }
}

pub fn compile_c(
  self : RawExpr[String],
  ctx : List[(String, Int)]
) -> List[Instruction]!Failure {
  fn arg_offset(n : Int, ctx : List[(String, Int)]) -> List[(String, Int)] {
    match ctx {
      Nil => Nil
      Cons((name, offset), ctx2) => Cons((name, offset + n), arg_offset(n, ctx2))
    }
  }
  match self {
    Var(s) =>
      match ctx.lookup(s) {
        // If the variable is a parameter, assume it is a super combinator.
        None => @immut/list.of([PushGlobal(s)])
        Some(n) => @immut/list.of([PushArg(n)])
      }
    Num(n) => @immut/list.of([PushInt(n)])
    App(e1, e2) =>
      compile_c!(e2, ctx) + compile_c!(e1, arg_offset(1, ctx)) + @immut/list.of([MkApp])
    _ => fail!("compile_c(): not implemented")
  }
}