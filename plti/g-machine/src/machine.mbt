pub typealias GlobEnv = @hashmap.T[String, Addr]

pub type Addr Int derive(Eq, Show)

// graph reduction algorithm on G-machine:
//   - Initialization: all compiled super combinators are stored 
//     in the `NGlobal` nodes in the heap. The code sequence contains
//     the push the `main` node nad load the instructions in `main` node.
//   - Instantiating main: code sequence of `main` is initialized on the heap, 
//     where nodes are allocated and data is loadded, ultimate constructing a
//     graph in the memory. Then push then entry node of the graph onto the stack.
//   - Evaluation: updating graph nodes and finding the next redex.
// 
pub enum Node {
  NNum(Int)
  NApp(Addr, Addr)
  NGlobal(String, Int, List[Instruction])
  NInd(Addr)
} derive(Show)

pub enum Instruction {
  // Unwind is always the last instruction of a sequence, and will construct a new state based on what’s on top of the stack.
  //   - NNum, the G-machine has terminated
  //   - NApp, must continue unwinding from next node
  //   - NGlobal, jump to the super combinator code by putting it onto code.
  Unwind
  // Looks up the name in global env and pushes the node in the heap onto the stack.
  PushGlobal(String)
  PushInt(Int)
  // Copy an argument that is passed to a function.
  // It has to look at the application node at the (n+1)-th place, and look at the rhs of the node.
  PushArg(Int)
  MkApp
  // Removes the top of the stack and update the index cell.
  Update(Int)
  // Tidies the stack by popping addresses off the stack.
  Pop(Int)
} derive(Eq, Show)

// Heap: graph nodes rather than bytes.
pub struct GHeap {
  mut object_count : Int
  memory : Array[Node?]
} derive(Show)

pub fn GHeap::op_get(self : GHeap, addr : Addr) -> Node {
  match self.memory[addr._] {
    Some(node) => node
    None => abort("op_get(): invalid address \{addr}")
  }
}

pub fn GHeap::op_set(self : GHeap, addr : Addr, node : Node) -> Unit {
  self.memory[addr._] = Some(node)
}


pub fn GHeap::alloc(self : GHeap, node : Node) -> Addr {
  fn next(n : Int) -> Int {
    (n + 1) % self.memory.length()
  }
  
  fn free(i : Int) -> Bool {
    match self.memory[i] {
      None => true
      _ => false
    }
  }

  let mut i = self.object_count
  while not(free(i)) {
    i = next(i)
  }
  // println("alloc(): allocating at \{i} for \{node}")
  self.memory[i] = Some(node)
  self.object_count = self.object_count + 1
  return Addr(i)
}

pub type GStats Int derive(Show)

// Stack: pointer to the heap.
// Globals: mapping from super combinator to `NGlobal` node address.
// Statistics: number of steps executed.
pub struct GState {
  mut stack : List[Addr]
  heap: GHeap
  globals: GlobEnv
  mut code: List[Instruction]
  mut stats: GStats
} derive(Show)

pub fn GState::stat_incr(self: GState) -> Unit {
  self.stats = self.stats._ + 1
}

pub fn GState::put_stack(self: GState, addr : Addr) -> Unit {
  self.stack = Cons(addr, self.stack)
}

pub fn GState::put_code(self: GState, instrs: List[Instruction]) -> Unit {
  self.code = instrs + self.code
}

pub fn GState::pop1(self: GState) -> Addr!Failure {
  match self.stack {
    Cons(addr, rest_stack) => {
      self.stack = rest_stack
      addr
    }
    Nil => fail!("pop1(): popping an empty stack")
  }
}

// e1 e2 ..... -> (e1, e2) .....
pub fn GState::pop2(self: GState) -> (Addr, Addr)!Failure {
  match self.stack {
    Cons(addr1, Cons(addr2, rest_stack)) => {
      self.stack = rest_stack
      (addr1, addr2)
    }
    _ => fail!("pop2(): popping an stack less than 2")
  }
}

// Effect of `PushInt`
pub fn GState::push_int(self: GState, n: Int) -> Unit {
  self.put_stack(self.heap.alloc(NNum(n)))
}

// Effect of `PushGlobal`
pub fn GState::push_global(self: GState, name: String) -> Unit!Failure {
  match self.globals.get(name) {
    Some(addr) => self.put_stack(addr)
    None => fail!("push_global(): cannot find super combinator \{name}")
  }
}

// Effect of `PushArg`: first address should point to the super combinator node,
// followed by n addresses pointing to the n `NApp` nodes
pub fn GState::push_arg(self: GState, offset: Int) -> Unit!Failure {
  let app_addr = match self.stack.nth(offset + 1) {
    Some(addr) => addr
    None => fail!("push_arg(): cannot find the argument")
  }
  let arg = match self.heap[app_addr] {
    NApp(_, arg) => arg
    _ as n => fail!("push_arg(): stack offset \{offset} address \{app_addr} node \{n}")
  }
  self.put_stack(arg)
}

pub fn GState::mk_app(self: GState) -> Unit!Failure {
  let (a1, a2) = self.pop2!()
  self.put_stack(self.heap.alloc(NApp(a1, a2)))
}

// Effect of `Update`: assumes first address on the stack 
// points to the current redex's evaluation result.
// it skips the addresses of the immediate following super combinator nodes
// and replaces the n-th `NApp` node with an indirect node pointing to the result.
//
// If the current redex is a CAF, it directly replaces its corresponding `NGlobal` node, which implies functions with parameters is the same as original variables 
// under lazy evaluation.
pub fn GState::update(self: GState, n: Int) -> Unit!Failure {
  let addr = self.pop1!()
  let dst = match self.stack.nth(n) {
    Some(addr) => addr
    None => fail!("update(): cannot find the n-th `NApp` node")
  }
  self.heap[dst] = NInd(addr)
}

pub fn GState::unwind(self : GState) -> Unit!Failure {
  let addr = self.pop1!()
  match self.heap[addr] {
    NNum(_) => self.put_stack(addr)
    NApp(a1, _) => {
      self.put_stack(addr)
      self.put_stack(a1)
      self.put_code(Cons(Unwind, Nil))
    }
    NGlobal(sc, n, c) => {
      if self.stack.length() < n {
        fail!("unwind(): too few arguments for \{sc}")
      } else {
        self.put_stack(addr)
        self.put_code(c)
      }
    }
    NInd(a) => {
      self.put_stack(a)
      self.put_code(Cons(Unwind, Nil))
    }
  }
}