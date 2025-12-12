
// In summary, the code generated for a supercombinator is to:
//   - construct the rhs of the supercombinator
//   - Slide n + 1, where n is the arity of the supercombinator
//   - Unwind, where Unwind is the instruction to cause machine evaluation to continue.
pub fn ScDef::compile_sc(self: ScDef[String]) -> (String, Int, List[Instruction]) raise Failure {
  let name = self.name
  let body = self.body
  let mut arity = 0
  fn gen_ctx(i: Int, args: List[String]) -> List[(String, Int)] {
    match args {
      Empty => {
        arity = i
        @list.empty()
      }
      More(s, tail=ss) => @list.cons((s, i), gen_ctx(i + 1, ss))
    }
  }
  // relative offset of parameters on the stack.
  let ctx = gen_ctx(0, self.args)
  (name, arity, body.compile_r(ctx, arity))
}


// `compileR` attach three instructions on generated code
// of super combinator:
//   - `Update(N)`, update the redex to `NInd` node.
//   - `Pop(N)`, clean addresses off the stack.
//   - `Unwind`, find the next redex.
pub fn RawExpr::compile_r(
  self : RawExpr[String],
  ctx : List[(String, Int)],
  arity : Int
) -> List[Instruction] raise Failure {
  if arity == 0 {
    self.compile_c(ctx) + @list.from_array([Update(arity), Unwind])
  } else {
    self.compile_c(ctx) + @list.from_array([Update(arity), Pop(arity), Unwind])
  }
}

pub fn RawExpr::compile_c(
  self : RawExpr[String],
  ctx : List[(String, Int)]
) -> List[Instruction] raise Failure {
  fn arg_offset(n : Int, ctx : List[(String, Int)]) -> List[(String, Int)] {
    match ctx {
      Empty => @list.empty()
      More((name, offset), tail=ctx2) => @list.cons((name, offset + n), arg_offset(n, ctx2))
    }
  }
  match self {
    Var(s) =>
      match ctx.lookup(s) {
        // If the variable is a parameter, assume it is a super combinator.
        None => @list.from_array([PushGlobal(s)])
        Some(n) => @list.from_array([PushArg(n)])
      }
    Num(n) => @list.from_array([PushInt(n)])
    App(e1, e2) =>
      e2.compile_c(ctx) + e1.compile_c(arg_offset(1, ctx)) + @list.from_array([MkApp])
    _ => fail("compile_c(): not implemented")
  }
}