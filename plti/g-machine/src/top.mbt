

pub fn build_initial_heap(
  scdefs: List[(String, Int, List[Instruction])]
) -> (GHeap, GlobEnv) {
  let heap = { object_count : 0, memory: Array::make(100, None) }
  let globals = @hashmap.new(capacity=50)
  loop scdefs {
      Empty => ()
      More((name, arity, instrs), tail=rest) => {
        let addr = heap.alloc(NGlobal(name, arity, instrs))
        globals.set(name, addr)
        continue rest
      }
  }
  (heap, globals)
}

pub fn GState::step(self: GState) -> Bool raise Failure {
  match self.code {
    Empty => false
    More(i, tail=rest) => {
      self.code = rest
      self.stat_incr()
      match i {
        PushGlobal(f) => self.push_global(f)
        PushInt(n) => self.push_int(n)
        PushArg(n) => self.push_arg(n)
        MkApp => self.mk_app()
        Unwind => self.unwind()
        Update(n) => self.update(n)
        Pop(n) => self.stack = self.stack.drop(n)
      }
      true
    }
  }
}

pub fn GState::reify(self: GState) -> Node raise Failure {
  if self.step() {
    if opts.debug {
      println("[step]:")
      println("code: \{self.code}")
      println("stack:")
      for addr in self.stack {
        println("\{self.heap[addr]}")
      }
    }
    self.reify()
  } else {
    let stack = self.stack
    match stack {
      More(addr, tail=Empty) => {
        let res = self.heap[addr]
        res
      }
      _ => abort("reify(): stack is empty")
    }
  }
}


struct Options {
  mut file: String?
  mut debug: Bool
}

fn Options::new() -> Options {
  Options:: { file: None, debug: false }
}

let opts: Options = Options::new()

fn main {
  let argv = @sys.get_cli_args()
  // moonrun *.wasm [args...]
  let truncated_argv = argv[1:].to_array()
  @ArgParser.parse(
    [("--debug", "", @ArgParser.Unit(fn() {opts.debug = true}), "Debug mode" ) ],
    fn(s) {
      if opts.file is None {
        opts.file = Some(s)
      } else {
        abort("multiple files given")
      }
    },
    "",
    truncated_argv
  ) catch {
    // errors raised from callbacks
    @ArgParser.ErrorMsg(msg) => println(msg)
    // errors raised from callbacks
    e => println(e)
  }

  let file = match opts.file {
    Some(f) => f
    None => abort("no input file given")
  }

  try {
    let contents = @fs.read_file_to_string(file)
    let parser = Parser::new(contents)
    let scdefs = parser.parse()
    // compile super combinators.
    let mut code = @list.empty()
    for prelude in preludes {
      let (name, arity, instrs) = prelude.compile_sc()
      if opts.debug {
        println("compiled prelude sc: \{name} \{arity} \{instrs}")
      }
      code = @list.cons((name, arity, instrs), code)
    }
    for scdef in scdefs.inner {
      let (name, arity, instrs) = scdef.compile_sc()
      if opts.debug {
        println("compiled user sc: \{name} \{arity} \{instrs}")
      }
      code = @list.cons((name, arity, instrs), code)
    }

    let (heap, globals) = build_initial_heap(code)
    let initial_state : GState = {
      heap : heap,
      stack : @list.empty(),
      code : @list.from_array([PushGlobal("main"), Unwind]),
      globals : globals,
      stats : 0
    }
    let node = initial_state.reify()
    println("result: \{node}")
  } catch {
    Failure(msg) => println("\{msg}")
    _ as err => println("\{err}")
  }
}