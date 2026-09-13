#import "template.typ": *
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set

#show: doc => conf(doc)
#set math.equation(numbering: "(1)", supplement: "式")
#set document(
  title: "Verification Review Letters",
  author: "Siyuan Zhu",
  keywords: ("Verification", "Refinement Type", "Program Logic"),
)

// ---------------------------------------------------------------------------
// 记号
// ---------------------------------------------------------------------------
#let coverage-color = rgb("1747c8")
#let ordinary-color = rgb("ce006c")
// 覆盖类型（下近似，must）与常规精化类型（上近似，may）
#let cov(b, p) = $#text(coverage-color)[\[] nu:#b mid(|) #p #text(coverage-color)[\]]$
#let over(b, p) = $#text(ordinary-color)[{] nu:#b mid(|) #p #text(ordinary-color)[}]$
#let arr(x, a, b) = $#x:#a -> #b$
#let den(t, g: none) = if g == none { $⟦#t⟧$ } else { $⟦#t⟧_(#g)$ }
#let sub(e, x, v) = $#e [#x |-> #v]$
#let steps(e, v) = $#e arrow.r.hook^* #v$
#let st = math.class("relation", $<:$)
#let wf(g, t) = $#g scripts(tack.r)_"WF" #t$
#let syn = math.class("relation", sym.arrow.r.double)
#let chk = math.class("relation", sym.arrow.l.double)
#let letin(x, a, e) = $"let" #x = #a "in" #e$
#let matchw(v, ps) = $"match" #v "with" #ps$
#let err = $"err"$
#let intt = $"int"$
#let natt = $"nat"$
#let boolt = $"bool"$
#let unitt = $"unit"$
#let treet = $"int tree"$
#let Ex = math.op("Ex")
#let Fa = math.op("Fa")
#let Disj = math.op("Disj")
#let Conj = math.op("Conj")
#let Query = math.op("Query")
#let Ty = math.op("Ty")
#let bst = math.op("bst")
#let mem = math.op("mem")
#let mmod = math.op("mod")

// 推导规则：统一用 curryst 排版，多条规则用 rule-set 横向排列、自动换行。
// top/bottom-edge 取 "bounds"，让上划线、下标计入盒子高度，避免与横线或相邻行重叠。
#let R(name, ..elems) = rule(name: text(size: 0.85em, smallcaps(name)), ..elems)
#let rules(..trees) = align(center, block(width: 100%, above: 1.4em, below: 1.6em, {
  set par(first-line-indent: 0em)
  set text(top-edge: "bounds", bottom-edge: "bounds")
  rule-set(
    column-gutter: 3em,
    row-gutter: 1.8em,
    ..trees.pos().map(t => prooftree(
      t,
      min-premise-spacing: 2em,
      title-inset: 0.4em,
      vertical-spacing: 0.15em,
    )),
  )
}))
#let prem(..ps) = stack(dir: ttb, spacing: 0.9em, ..ps.pos())
// 同一行内的多个前提
#let prow(..ps) = ps.pos().join(h(2em))
#show table: set par(first-line-indent: 0em)
#show raw.where(block: true): set text(size: 8.5pt)
#let optable(f, g, ..rows) = align(center, table(
  columns: 3,
  align: center + horizon,
  stroke: 0.5pt,
  inset: 6pt,
  [], f, g,
  ..rows.pos().flatten(),
))

#set outline(depth: 2)
#makecontent()

= Coverage Type（PLDI '23）

本章整理 Zhou、Mishra、Delaware 与 Jagannathan 的 #link("https://arxiv.org/abs/2304.03393v2")[_Covering All the Bases: Type-Based Verification of Test Input Generators_]（PLDI 2023，依据 arXiv v2）。读者应熟悉 Liquid Types 一类精化类型系统，下文不重复共性，只讲本文偏离标准设定之处：下近似的类型解释、关键的声明式规则、双向算法与验证条件（VC）生成，以及元理论的形式陈述。读完后，读者应能自己动手实现一个覆盖类型检查器。

== 问题：生成器的完整性

基于性质的测试依赖输入生成器。常规精化类型 $e : over(b, phi)$ 只能刻画*安全性*，即输出都满足 $phi$；它刻画不了*完整性*，即每个满足 $phi$ 的值都有机会被生成。一个永远返回 `Leaf` 的函数，同样是良类型的“BST 生成器”。

#eg(supplement: [BST 生成器])[
  ```ocaml
  let rec bst_gen (lo: int) (hi: int) : int tree =
    if lo + 1 >= hi then Leaf else
    (* Leaf ⊕ *)
    (let (x: int) = int_range (lo + 1, hi - 1) in
     Node (x, bst_gen lo x, bst_gen x hi))
  ```
  $⊕$ 是非确定选择。若第 3 行保持注释，程序在区间非空时必然建节点，区间内每个整数都会进入树中：`bst_gen 0 3` 永远得不到 `Leaf` 或 `Node(1, Leaf, Leaf)`。但它输出的每棵树都是合法 BST，安全性规格无法区分两个版本。
]

== 覆盖类型

#def(supplement: [类型的指称])[
  设 $scripts(tack.r)_t$ 为擦除精化后的基本类型判断，$steps(e, v)$ 表示 $e$ 存在一条有限执行得到 $v$。
  $
    den(over(b, phi)) &= {v mid(|) emptyset scripts(tack.r)_t v : b and sub(phi, nu, v)} \
    den(cov(b, phi)) &= {e mid(|) emptyset scripts(tack.r)_t e : b and forall v : b. thin sub(phi, nu, v) ==> steps(e, v)} \
    den(arr(x, tau_x, tau)) &= {f mid(|) forall v in den(tau_x). thin f thin v in den(sub(tau, x, v))}
  $
]

蓝色方括号 $cov(b, phi)$ 是*覆盖类型*，表示 $e$ 必须能产生每个满足 $phi$ 的值，但它也可以产生别的值，或在某些执行上出错。玫红花括号仍是常规的上近似类型。两者的关系如同 Incorrectness Logic 之于 Hoare 逻辑。下表中 ✓ 表示可以赋予该类型：

#align(center, table(
  columns: 5,
  align: center,
  stroke: 0.5pt,
  inset: 5pt,
  [项], [$cov(intt, top)$], [$cov(intt, nu = 1 or nu = 2)$], [$cov(intt, nu = 1)$], [$cov(intt, bot)$],
  [`int_gen ()`], [✓], [✓], [✓], [✓],
  [`1 ⊕ 2`], [], [✓], [✓], [✓],
  [`1`], [], [], [✓], [✓],
  [`err`], [], [], [], [✓],
))

谓词越强，承诺越多。$cov(b, bot)$ 不作任何承诺，所有项都有这个类型，而 `err` 只有这个类型。

类型语法为 $tau ::= cov(b, phi) | over(b, phi) | arr(x, tau, tau)$。良构性规定花括号只出现在参数位置，方括号只出现在结果位置：参数由调用者给出，函数须对每个合法参数兑现承诺，因此参数取全称含义；结果则是必须产生的值。原语类型由 $Ty$ 给出，例如 $Ty("int_gen") = arr(\_, over(unitt, top), cov(intt, top))$，它编码了“随机数生成器以非零概率产生每个整数”这一假设。完整的 `bst_gen` 具有
$
  & "lo" : over(intt, top) -> "hi" : over(intt, "lo" <= nu) \
  & quad -> cov(treet, bst(nu) and forall u. thin mem(nu, u) ==> "lo" < u < "hi")
$
其中 $bst$、$mem$ 是 method predicate，即配有公理的未解释谓词。不完整版本只能获得把 $==>$ 换成 $<==>$ 的类型，两者恰好差一个蕴涵方向。

== 声明式规则：与常规精化类型的差异

以下假定项已通过基本类型检查，采用 MNF 语法，上下文同时含有上近似、覆盖与函数类型的绑定。常量、`err`、函数抽象等平凡规则从略，只列出本质不同的部分。

*子类型方向相反。* 子类型仍由指称包含定义，但覆盖类型的谓词越弱，指称越小。于是在空上下文中 $cov(b, phi_1) st cov(b, phi_2)$ 当且仅当 $phi_2 ==> phi_1$，例如 $cov(intt, top) st cov(intt, nu = 1) st cov(intt, bot)$：能产生全部整数的程序当然能产生 1。函数类型照常是参数逆变、结果协变。

*变量不能抄写上下文。* TVarBase 只给出 $Gamma tack.r x : cov(b, nu = x)$。在 $x : over(natt, top)$ 下，项 $x$ 并不具有 $cov(natt, top)$，因为对每个固定参数它只产生自己。

=== 上下文是执行见证

标准系统中的绑定是全称假设，这里的覆盖绑定 $y : cov(b, phi)$ 却是*存在性*的：存在一条执行，使 $y$ 能取遍 $phi$ 中的值，后续推理可以挑选 $y$ 的取值作为见证。因此上下文本身必须可行：

#rules(
  R("WfBase",
    prem($phi "在" Gamma "下闭合且为布尔谓词"$, $forall (y : cov(b_y, phi_y)) in Gamma. thin err in.not den(cov(b_y, phi_y), g: Gamma)$),
    $wf(Gamma, cov(b, phi))$),
)

`err` 不产生任何值，所以 $err in.not den(cov(b, phi), g: Gamma)$ 就是说 $phi$ 在 $Gamma$ 下非空。在 $x : over(natt, nu > 0), y : cov(natt, x = 0 and nu = 2)$ 之下没有良构类型；反过来，$cov(natt, bot)$ 在 $x : over(natt, nu > 0)$ 下良构。结果可以不作承诺，上下文却不能是空头支票。

=== 分支取并

#rules(
  R("TMatch",
    prem($Gamma tack.r v : tau_v$, $wf(Gamma, tau)$),
    prem($Gamma, overline(y : tau_y) tack.r d_i thin overline(y) : tau_v$, $Gamma, overline(y : tau_y) tack.r e_i : tau$),
    $Gamma tack.r matchw(v, overline(d_j thin overline(y) -> e_j)) : tau$),
  R("TMerge",
    $Gamma tack.r e : tau_1$, $Gamma tack.r e : tau_2$, $Gamma tack.r tau_1 or tau_2 = tau$, $wf(Gamma, tau)$,
    $Gamma tack.r e : tau$),
  R("Disjunction",
    $den(tau_1, g: Gamma) inter den(tau_2, g: Gamma) = den(tau_3, g: Gamma)$,
    $Gamma tack.r tau_1 or tau_2 = tau_3$),
)

若沿用“每个分支都具有目标类型”的规则，`if b then n else err` 只能得到 $cov(intt, bot)$。TMatch 因此只处理*一个*分支，前提 $Gamma, overline(y : tau_y) tack.r d_i thin overline(y) : tau_v$ 说明被匹配值能进入该分支；TMerge 再合并不同推导。合并在谓词上是析取，在指称上却是交集，因为同一个程序须同时兑现两份承诺：`1 ⊕ 2` 同属 $cov(natt, nu = 1)$ 与 $cov(natt, nu = 2)$，故属于 $cov(natt, nu = 1 or nu = 2)$。

=== 收窄只作用于闭项

#rules(
  R("TSub",
    $emptyset tack.r e : tau$, $emptyset tack.r tau st tau'$, $wf(Gamma, tau')$,
    $Gamma tack.r e : tau'$),
  R("TApp",
    prem($Gamma tack.r v_1 : arr(a, over(b, phi), tau_x)$, $Gamma tack.r v_2 : cov(b, phi)$),
    prem($Gamma, x : sub(tau_x, a, v_2) tack.r e : tau$, $wf(Gamma, tau)$),
    $Gamma tack.r letin(x, v_1 thin v_2, e) : tau$),
)

TApp 是 may 与 must 的接口：实参的覆盖谓词必须与形参谓词*完全一致*。不一致时须收窄实参，而 TSub 只能作用于闭项。例如 `let high = int_gen () in bst_gen low high` 中，`high` 的 $cov(intt, top)$ 比所需的 $cov(intt, "low" <= nu)$ 更强，但它是开项；只能先把闭项 `int_gen` 收窄为 $arr(\_, over(unitt, top), cov(intt, "low" <= nu))$，让 `high` 带着所需类型进入上下文。这保证上下文中每个绑定都描述真实可行的执行；需要多种收窄时，就分别推导再用 TMerge 合并。另有 TEq 允许在 $Gamma$ 下把类型换成互为子类型的等价形式，用于消去离开作用域的局部变量。

=== 递归必须终止

#rules(
  R("TFix",
    $Gamma tack.r lambda x. lambda f. thin e : arr(x, over(b, phi), arr(f, (arr(x, over(b, nu prec x and phi), tau)), tau))$,
    $wf(Gamma, arr(x, over(b, phi), tau))$,
    $Gamma tack.r "fix" f. lambda x. thin e : arr(x, over(b, phi), tau)$),
)

没有 $prec$ 时，`let rec loop n = loop n` 可以在自身签名的假设下“证明” $arr(n, over(natt, top), cov(natt, nu = 3))$。上近似系统里这只是部分正确性，下近似系统里却等于凭空制造可达性，因为假设会被当作见证。

== 双向算法

声明式规则的非确定性在于：TMatch 与 TMerge 怎样拆分路径，TSub 收窄到哪里，TEq 怎样改写。算法用三个机制消除它们：
+ *综合* $syn$ 沿 MNF 语法收集路径，并保持“结果类型在当前 $Gamma$ 下良构”这一不变量；
+ 每引入一批局部绑定 $Gamma'$，就用 $Ex(Gamma', dot)$ 把它们量化进结果类型；
+ 用*幽灵变量*记录路径条件，代替 TSub 的猜测；子类型义务只在 match 与模式切换处发出。

#rules(
  R("SynAppBase",
    prem($Gamma tack.r v_1 syn arr(a, over(b, phi), tau_x)$, $Gamma' = a : cov(b, nu = v_2 and phi), thin x : tau_x$),
    prem($Gamma, Gamma' tack.r e syn tau$, $tau' = Ex(Gamma', tau)$),
    $wf(Gamma, tau')$,
    $Gamma tack.r letin(x, v_1 thin v_2, e) syn tau'$),
  R("ChkMatch",
    prem(
      prow($forall i. thin Ty(d_i) = arr(overline(y), overline(over(b_y, theta_y)), cov(b, psi_i))$, $Gamma, Gamma'_i tack.r e_i syn tau_i$),
      prow($Gamma'_i = overline(y : cov(b_y, theta_y)), thin a : cov(b, nu = v and psi_i)$, $tau'_i = Ex(Gamma'_i, tau_i)$),
      prow($Gamma tack.r Disj(overline(tau'_i)) st tau$, $wf(Gamma, tau)$),
    ),
    $Gamma tack.r matchw(v, overline(d_i thin overline(y) -> e_i)) chk tau$),
)

SynAppBase 中，幽灵变量 $a : cov(b, nu = v_2 and phi)$ 取代了 TApp 的“谓词完全一致”：它是实参覆盖与形参要求的交集。$a$ 与形参同名，所以 $tau_x$ 对形参的引用自动指向它。交集为空时 $Gamma, Gamma'$ 不可行，WfBase 使 $e$ 综合不出任何类型。以 `bst_gen low high` 为例，$Gamma'$ 含 $a : cov(intt, nu = "high" and "low" <= nu)$，依次消去 $a$ 与 $"high" : cov(intt, top)$ 后得到
$
  cov(treet, exists "high". thin "low" <= "high" and bst(nu) and forall u. thin mem(nu, u) ==> "low" < u < "high"),
$
即“所有键都大于 `low` 的 BST”，整个过程无需猜测 TSub。

ChkMatch 为每个分支加入幽灵变量，记录进入条件 $nu = v and psi_i$（$psi_i$ 取自构造器的结果类型），模式变量按构造器参数谓词取覆盖类型。各分支分别综合，经 $Ex$ 封闭、$Disj$ 合并，最后只做一次子类型检查。这一条规则同时替代了 TSub、TEq 与 TMerge；去掉最后的子类型前提就是 SynMatch。其余规则的结构相同：SynLetE 的 $Gamma' = x : tau_x$；SynAppFun 先检查函数实参，再令 $Gamma' = x : tau_x$；SynAppOp 为每个基类型实参各引入一个幽灵变量。函数只能被检查（ChkFun、ChkFix，与 TFun、TFix 同形），因为参数的上近似谓词无从推断。模式切换由 ChkSub 完成：先综合，再检查子类型。

== 验证条件生成

=== Ex 与 Disj

记 $hat(phi)_x = sub(phi_x, nu, x)$。$Ex(x : cov(b_x, phi_x), tau)$ 把一个覆盖绑定量化进 $tau$，$Fa$ 是其对偶：

#optable([$Ex(x, tau)$], [$Fa(x, tau)$],
  ([$cov(b, phi)$], [$cov(b, exists x. thin hat(phi)_x and phi)$], [$cov(b, forall x. thin hat(phi)_x ==> phi)$]),
  ([$over(b, phi)$], [$over(b, forall x. thin hat(phi)_x ==> phi)$], [$over(b, exists x. thin hat(phi)_x and phi)$]),
  ([$arr(a, tau_a, tau)$], [$arr(a, Fa(x, tau_a), Ex(x, tau))$], [$arr(a, Ex(x, tau_a), Fa(x, tau))$]),
)

对上下文从右向左折叠：$Ex((Gamma, x : tau_x), tau) = Ex(Gamma, Ex(x : tau_x, tau))$。结果谓词中的局部变量是“某条执行选中的值”，所以取 $exists$；参数谓词须对所有这样的选择成立，所以取 $forall$；箭头左侧逆变，两者交换。例如 $Ex(x : cov(natt, nu > 0), cov(natt, nu = x + 1)) = cov(natt, exists x. thin x > 0 and nu = x + 1)$，覆盖所有大于 1 的自然数。$Disj$ 与 $Conj$ 同理互为对偶：

#optable([$Disj(tau_1, tau_2)$], [$Conj(tau_1, tau_2)$],
  ([$cov(b, phi_1), cov(b, phi_2)$], [$cov(b, phi_1 or phi_2)$], [$cov(b, phi_1 and phi_2)$]),
  ([$over(b, phi_1), over(b, phi_2)$], [$over(b, phi_1 and phi_2)$], [$over(b, phi_1 or phi_2)$]),
  ([$arr(a, tau_(a 1), tau_1), arr(a, tau_(a 2), tau_2)$], [$arr(a, Conj(tau_(a 1), tau_(a 2)), Disj(tau_1, tau_2))$], [$arr(a, Disj(tau_(a 1), tau_(a 2)), Conj(tau_1, tau_2))$]),
)

=== Query

所有基类型上的子类型与良构性义务都归结为 $Query$。它从右向左消去上下文，把上近似绑定编码为 $forall$、覆盖绑定编码为 $exists$，两侧谓词各自量化，函数绑定直接丢弃：
$
  Query(emptyset, phi_1, phi_2) &= forall nu : b. thin phi_2 ==> phi_1 \
  Query((Gamma, x : over(b_x, phi_x)), phi_1, phi_2) &= Query(Gamma, forall x. thin hat(phi)_x ==> phi_1, forall x. thin hat(phi)_x ==> phi_2) \
  Query((Gamma, x : cov(b_x, phi_x)), phi_1, phi_2) &= Query(Gamma, exists x. thin hat(phi)_x and phi_1, exists x. thin hat(phi)_x and phi_2)
$

#rules(
  R("", $⊨ Query(Gamma, phi_1, phi_2)$, $Gamma tack.r cov(b, phi_1) st cov(b, phi_2)$),
  R("", $⊨ Query(Gamma, phi_2, phi_1)$, $Gamma tack.r over(b, phi_1) st over(b, phi_2)$),
  R("", $⊭ Query(Gamma, bot, phi)$, $err in.not den(cov(b, phi), g: Gamma)$),
)

第三条规则说：$Query(Gamma, bot, phi)$ 无效，意味着 $phi$ 在 $Gamma$ 下可满足，WfBase 据此检查上下文是否可行。函数类型之间的子类型按参数逆变、结果协变结构分解。

#eg(supplement: [偶数生成器])[
  ```ocaml
  let even_gen () =
    let (n: int) = int_gen () in
    let (b: bool) = n mod 2 == 0 in
    match b with true -> n | false -> err
  ```
  检查 `match` 时 $Gamma = n : cov(intt, top), b : cov(boolt, nu <==> n mmod 2 = 0)$。`true` 分支加入幽灵变量 $b' : cov(boolt, nu = b and nu)$，综合出 $cov(intt, nu = n)$，$Ex$ 后化简为 $cov(intt, b and nu = n)$；`false` 分支得 $cov(intt, not b and bot)$。ChkMatch 发出义务 $Gamma tack.r cov(intt, phi_1) st cov(intt, nu mmod 2 = 0)$，其中 $phi_1 = (b and nu = n) or (not b and bot)$。Query 先消去 $b$，再消去 $n$：
  $
    forall nu. thin (exists n, b. thin (b <==> n mmod 2 = 0) and nu mmod 2 = 0) ==> (exists n, b. thin (b <==> n mmod 2 = 0) and phi_1).
  $
  前件里的存在部分恰是上下文的可行性，化简后得到
  $
    forall nu. thin nu mmod 2 = 0 ==> exists n, b. thin (b <==> n mmod 2 = 0) and phi_1.
  $
  取 $n = nu$、$b = "true"$ 即可满足。量词顺序就是覆盖的含义：先任取目标值，再为它找执行。在 Liquid Types 中 $n, b$ 会成为全称前件；若目标改为 $cov(intt, top)$，奇数找不到见证，检查失败。
]

=== 可判定性

Query 的结果形如 $forall^* exists^* phi$，其否定属于 EPR 片段 $exists^* forall^*$。为使量词确实能这样前束化，算法附加三条限制：
+ 上下文中的上近似类型不得引用覆盖变量，这样全称量词才能提到最外层。反例：$x : cov(natt, nu > 0), y : over(natt, nu > x + 1)$ 会产生 $forall nu thin exists x thin forall y$。
+ 上近似类型的谓词只使用全称量词。
+ method predicate 不嵌套，常量实参改写为 $forall u. thin u = 3 ==> mem(nu, u)$。

注意 EPR 的可判定性并不涵盖 `mod`、`<` 等整数算术，这部分实际依赖 SMT 求解器的理论支持。

== 动手实现

下面是按上述规则写出的检查器骨架（OCaml 风格）。上下文用列表表示，表头是最右端的绑定；`valid` 调用 SMT 求解器判定公式有效性。

```ocaml
type ty = Cov of base * prop | Over of base * prop | Arr of var * ty * ty
type ctx = (var * ty) list                  (* 表头 = 最右端绑定 *)

(* Ex / Fa：把覆盖绑定 x:[ν:bx | px] 量化进类型；hat x px = px[ν ↦ x] *)
let rec ex (x, bx, px) = function
  | Cov (b, p)     -> Cov  (b, Exists (x, bx, And (hat x px, p)))
  | Over (b, p)    -> Over (b, Forall (x, bx, Imp (hat x px, p)))
  | Arr (a, ta, t) -> Arr (a, fa (x, bx, px) ta, ex (x, bx, px) t)
and fa (x, bx, px) = function
  | Cov (b, p)     -> Cov  (b, Forall (x, bx, Imp (hat x px, p)))
  | Over (b, p)    -> Over (b, Exists (x, bx, And (hat x px, p)))
  | Arr (a, ta, t) -> Arr (a, ex (x, bx, px) ta, fa (x, bx, px) t)

(* Ex(Γ', τ)：delta 按从左到右列出，从最右端开始消去；函数绑定跳过 *)
let ex_ctx delta t =
  List.fold_left (fun t -> function
      | (x, Cov (bx, px)) -> ex (x, bx, px) t
      | _ -> t)
    t (List.rev delta)

(* Query：Γ ⊢ [ν:b | p1] <: [ν:b | p2] *)
let rec query b ctx p1 p2 = match ctx with
  | [] -> Forall (nu, b, Imp (p2, p1))
  | (x, Over (bx, px)) :: g ->
      let q p = Forall (x, bx, Imp (hat x px, p)) in
      query b g (q p1) (q p2)
  | (x, Cov (bx, px)) :: g ->
      let q p = Exists (x, bx, And (hat x px, p)) in
      query b g (q p1) (q p2)
  | (_, Arr _) :: g -> query b g p1 p2

let rec sub ctx t1 t2 = match t1, t2 with
  | Cov (b, p1), Cov (_, p2)   -> valid (query b ctx p1 p2)
  | Over (b, p1), Over (_, p2) -> valid (query b ctx p2 p1)
  | Arr (x, a1, r1), Arr (_, a2, r2) ->
      sub ctx a2 a1 && sub ((x, a2) :: ctx) r1 r2
  | _ -> false

(* WfBase：每个新覆盖绑定在其左侧上下文下必须非空 *)
let rec extend ctx = function
  | [] -> ctx
  | (x, Cov (b, p)) :: rest ->
      if valid (query b ctx False p) then fail "infeasible path";
      extend ((x, Cov (b, p)) :: ctx) rest
  | bnd :: rest -> extend (bnd :: ctx) rest

(* let x = rhs 引入的绑定 Γ' *)
let rec bindings ctx x rhs = match rhs with
  | App (f, v) ->
      (match synth ctx f with
       | Arr (a, Over (b, phi), tx) ->                  (* SynAppBase *)
           [ (a, Cov (b, And (Eq (nu, v), phi))); (x, tx) ]
       | Arr (_, ta, tx) ->                             (* SynAppFun *)
           check ctx v ta; [ (x, tx) ])
  | e -> [ (x, synth ctx e) ]                           (* SynLetE *)

(* 一个 match 分支：Ty(d) = ȳ:{θ̄} → [ν:b | ψ] *)
and branch ctx v (d, ys, body) =
  let thetas, b, psi = ctor_sig d in
  let ghost = (fresh (), Cov (b, And (Eq (nu, v), psi))) in
  let delta =
    List.map2 (fun y (by, th) -> (y, Cov (by, th))) ys thetas @ [ ghost ] in
  ex_ctx delta (synth (extend ctx delta) body)

and synth ctx = function
  | Var x ->
      (match lookup ctx x with
       | Arr _ as t -> t
       | t -> Cov (base t, Eq (nu, Var x)))
  | Const c -> ty_of_const c
  | Err b -> Cov (b, False)
  | Let (x, rhs, body) ->
      let delta = bindings ctx x rhs in
      ex_ctx delta (synth (extend ctx delta) body)
  | Match (v, bs) -> disj_all (List.map (branch ctx v) bs)   (* SynMatch *)
  | Lam _ | Fix _ -> fail "functions are only checked"

and check ctx e t = match e, t with
  | Lam (x, body), Arr (_, tx, tr) ->                         (* ChkFun *)
      check ((x, tx) :: ctx) body tr
  | Fix (f, x, body), Arr (_, Over (b, phi), tr) ->           (* ChkFix *)
      let tf = Arr (x, Over (b, And (Prec (nu, Var x), phi)), tr) in
      check ((f, tf) :: (x, Over (b, phi)) :: ctx) body tr
  | Let (x, rhs, body), _ ->                        (* 对应 TLetE / TApp *)
      check (extend ctx (bindings ctx x rhs)) body t
  | Match (v, bs), _ ->                                     (* ChkMatch *)
      let t' = disj_all (List.map (branch ctx v) bs) in
      if not (sub ctx t' t) then fail "coverage"
  | _ ->                                                      (* ChkSub *)
      if not (sub ctx (synth ctx e) t) then fail "coverage"
```

实现时有几点值得注意。
- *化简 Ex 产生的量词。* $Ex$ 生成的 $exists$ 会迅速堆积，红黑树一类的例子里可达数十个。实现时应在每次 $Ex$ 之后做化简，例如消去形如 $exists a. thin a = t and phi$ 的一点规则（one-point rule），前文 $exists b'. thin (b' = b and b') and nu = n$ 化为 $b and nu = n$ 用的就是它。
- *检查模式的 `let`。* 骨架中 `check` 对 `Let` 直接扩展上下文后继续检查，这对应声明式的 TLetE 与 TApp，也是论文例 5.1 的实际做法；但论文图 14–15 并未列出这条规则。
- *不可行分支。* 若某个分支的幽灵变量不可行（例如对常量做 match），按规则整个检查失败。由于 $cov(b, bot)$ 总是可靠的，实现上可以让该分支贡献 $cov(b, bot)$。
- *公理与限制。* method predicate 的语义以公理形式交给求解器，例如 $"len"(l, 0) ==> forall u. thin not mem(l, u)$。上一小节的三条量词限制应在规格载入时就检查。

== 元理论

#def(supplement: [上下文下的指称])[
  开放项的指称沿上下文从左到右解释。对上近似绑定照常取全称：
  $
    e in den(tau, g: #($x : over(b, phi), Gamma$)) & <==> forall v_x in den(over(b, phi)). thin letin(x, v_x, e) in den(sub(tau, x, v_x), g: sub(Gamma, x, v_x)).
  $
  对其余绑定 $x : tau_x$（覆盖类型或函数类型）：
  $
    e in den(tau, g: #($x : tau_x, Gamma$)) & <==> exists hat(e)_x in den(tau_x). thin forall e_x in den(tau_x). \
    & quad quad letin(x, e_x, e) in inter.big_(steps(hat(e)_x, v_x)) den(sub(tau, x, v_x), g: sub(Gamma, x, v_x)).
  $
  子类型所需的包含关系 $den(tau_1, g: Gamma) subset.eq den(tau_2, g: Gamma)$ 要求两侧对 $Gamma$ 使用同一替换（附录 A.4）。
]

第二种情形对应覆盖绑定：先选定见证 $hat(e)_x$，再要求对任意满足 $tau_x$ 的实现 $e_x$，`let` 之后的程序都属于 $hat(e)_x$ 所有结果对应指称的交集。用 `let` 而非代入，是为了让 $x$ 的多次出现共享同一次选择：`let x = 1 ⊕ 2 in x + x` 只产生 2 或 4。例如在 $x : cov(natt, nu = 1)$ 下取 $hat(e)_x = 1$，交集为 $den(cov(natt, nu = 2))$，因此 $x + 1 in den(cov(natt, nu = x + 1 or nu = x + x), g: Gamma)$。两侧须用同一替换，否则它们可以各自挑选互不相容的见证。

#thm[（类型可靠性，定理 4.3）若 $Gamma tack.r e : tau$，则 $e in den(tau, g: Gamma)$。于是闭生成器若具有 $cov(b, phi)$，就能产生每个满足 $phi$ 的值。]

#thm[（算法可靠性，定理 5.3）若 $Gamma tack.r e syn tau$ 或 $Gamma tack.r e chk tau$，则 $Gamma tack.r e : tau$。]

#thm[（相对完备性，定理 5.4）假设 Query 是精确的预言机，即 $Gamma tack.r cov(b, phi_1) st cov(b, phi_2)$ 当且仅当 $Query(Gamma, phi_1, phi_2)$ 有效，则 $Gamma tack.r e : tau$ 蕴涵 $Gamma tack.r e chk tau$。]

连接算法与语义的是以下几条引理（附录 B）：
$
  & Gamma, Gamma' tack.r e : tau ==> Gamma, Gamma' tack.r e : Ex(Gamma', tau) and wf(Gamma, Ex(Gamma', tau)) && "(Ex 保持类型)" \
  & Gamma tack.r tau_1 or tau_2 = Disj(tau_1, tau_2) && "(Disj 实现析取)" \
  & Gamma tack.r tau_1 st tau_2 <==> emptyset tack.r Ex(Gamma, tau_1) st Ex(Gamma, tau_2) && "(子类型可闭化)"
$
第三条说明，上下文中的子类型等价于把上下文量化进两侧之后的闭子类型，这正是 Query 的计算方式。算法可靠性的证明还用到*上下文子类型* $Gamma_1 ⊑ Gamma_2 := forall tau, e. thin e in den(tau, g: Gamma_1) ==> e in den(tau, g: Gamma_2)$：幽灵变量相当于在变量进入上下文时延迟、按需地做了 TSub。

需要注意，Coq 机械化只覆盖定理 4.3，上述引理在附录中只有陈述；ChkSub 的前提与 TSub 一样写作 $emptyset tack.r e syn tau$，但开放项的检查离不开它或未列出的检查模式 `let` 规则。

== 评注

- *规格负担*：覆盖规格与安全规格几乎同形，只是结果换成方括号，因此可以复用 Liquid Types 的谓词语言与公理。两者合用可刻画精确的输出集合，但安全性仍需另行检查。
- *保证强度*：只保证每个目标值以非零概率可达，不涉及分布或采样次数；递归必须良基终止，实际中通常需要显式的 size 或 fuel 参数。
- *版本校记*：v2 例 5.1 的两个分支写反，例 5.2 的目标类型又写成 $cov(intt, nu >= 0)$，本文统一为图 2 的偶数生成器；附录中 $Ex$ 对上下文的折叠式把内层绑定误写为 $x_1$，本文按从右向左消去理解。
