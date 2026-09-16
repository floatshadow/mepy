#import "template.typ": *
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set

#show: doc => conf(doc)
#set math.equation(numbering: "(1)", supplement: "式")
#set document(
  title: "Type System Review Letters",
  author: "Siyuan Zhu",
  keywords: ("Type System", "Aliasing", "Effect System"),
)

// ---------------------------------------------------------------------------
// 记号
// ---------------------------------------------------------------------------
#let qual-color = rgb("1747c8")
// 可达性限定符统一着色，T^q 写作 qt(T, q)
#let qc(q) = text(fill: qual-color, $#q$)
#let qt(t, q) = $#t^#qc(q)$
#let vs(..xs) = ${#xs.pos().join($, $)}$
#let fn(f, x, t1, q1, t2, q2) = $#f (#x : qt(#t1, #q1)) -> qt(#t2, #q2)$
#let earr(e) = $attach(stretch(->, size: #200%), t: #e)$
#let efn(f, x, t1, q1, e, t2, q2) = $#f (#x : qt(#t1, #q1)) earr(#e) qt(#t2, #q2)$
#let subt = math.class("relation", $<:$)
#let qleq = math.class("relation", $⊑$)
#let qjoin = math.class("binary", $⊔$)
#let qmeet = math.class("binary", $⊓$)
#let qplus = math.class("binary", $⊕$)
#let seqc = math.class("binary", $▷$)
#let refT(t) = $"Ref" #t$
#let unitT = $"Unit"$
#let intT = $"Int"$
#let botE = $bot_bb(E)$
#let rd = $"rd"$
#let wr = $"wr"$
#let kill = $"kill"$
#let FV = math.op("FV")
#let dom = math.op("dom")
#let eff(e) = $thin | thin #e$

// 推导规则：统一用 curryst 排版，多条规则用 rule-set 横向排列、自动换行。
// top/bottom-edge 取 "bounds"，让上标、下标计入盒子高度，避免与横线或相邻行重叠。
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
      vertical-spacing: 0.2em,
    )),
  )
}))
#let prem(..ps) = stack(dir: ttb, spacing: 0.9em, ..ps.pos())
#let prow(..ps) = ps.pos().join(h(2em))
#show table: set par(first-line-indent: 0em)
#show raw.where(block: true): set text(size: 8.5pt)

#set outline(depth: 2)
#makecontent()

= Reachability Types（OOPSLA '21）

本章整理 Bao、Wei、Bračevac、Jiang、He 与 Rompf 的 #link("https://doi.org/10.1145/3485516")[_Reachability Types: Tracking Aliasing and Separation in Higher-Order Functional Programs_]（OOPSLA 2021）。读者应熟悉带可变引用的 λ 演算、子类型与效果系统。论文分两层：基础系统 $lambda^*$ 在类型上标注值可能到达的变量，刻画别名与分离；$lambda^*_epsilon$ 叠加效果系统，支持移动语义等流敏感推理。

*代码约定。* 示例沿用论文的类 Scala 语法：`val x = e` 是 let 绑定，`def f(x: A) = e` 定义可递归的命名函数，`A => B` 是函数类型，`() => e` 是以 unit 为参数的闭包。注释里的 `T^{x,y}`、`T^∅`、`T^⊥` 分别对应 $qt(T, vs(x, y))$、$qt(T, emptyset)$、$qt(T, bot)$，省略限定符即为 $bot$。

== 问题：共享可变状态的闭包

Rust 遵循“共享与可变互斥”：可变引用唯一，只读引用才可共享。下面的计数器返回两个共享同一单元的闭包，Rust 只能借助 `Rc` 等运行时机制实现：

```scala
def counter(n: Int) = {
  val c = new Ref(n)
  (() => c += 1, () => c -= 1)   // 两个闭包共享同一个可变引用
}
```

本文反其道而行：类型系统的核心是追踪*共享*，分离即共享的缺席；唯一性由效果系统按需叠加。

== 语法与判断

$
  t & ::= c | x | lambda f(x). thin t | t_1 thin t_2 | "ref" t | !t | t_1 := t_2 \
  T & ::= B | refT(T) | fn(f, x, T, q, T, q) \
  q & ::= bot | alpha quad quad alpha, beta, gamma in cal(P)_"fin" ("Var") quad quad Gamma ::= emptyset | Gamma, x : qt(T, q)
$

- *项。* $c$ 是常量；$lambda f(x). thin t$ 是递归函数，体内 $f$ 指函数自身；`ref t` 分配可变单元，`!t` 读取，$t_1 := t_2$ 写入。let 与多参函数都是语法糖。
- *类型。* $B$ 是 Int、Unit 等基类型；$refT(T)$ 是存放 $T$ 值的单元。函数类型 $fn(f, x, T_1, q_1, T_2, q_2)$ 中，$x$ 命名形参，$f$ 命名函数值本身，称为*自引用*；二者可以出现在结果限定符 $q_2$ 中，$x$ 还可以出现在 $T_2$ 内部的限定符中。不用时省略名字。
- *限定符。* $q$ 是 $bot$ 或有限变量集合；$alpha, beta, gamma$ 专指集合。$FV(T)$ 是 $T$ 内部各限定符中自由出现的变量，不含 $T$ 自己绑定的 $f, x$。

判断 $Gamma tack.r t : qt(T, q)$ 表示 $t$ 具有类型 $T$，且其值*可能*到达 $q$ 中的变量（上近似）：
- $bot$ 表示*不被跟踪*，用于基类型值与不捕获被跟踪值的纯函数；
- 集合 $alpha$ 表示被跟踪，可能与 $alpha$ 中的变量共享；
- $emptyset$ 表示被跟踪但当前环境中没有名字能到达，称为*新鲜*。新鲜不等于全局唯一：$emptyset$ 形参的实参可能在调用者那里有名字。

所有引用都被跟踪，捕获被跟踪值的闭包也被跟踪。

```scala
val x = 4            // Int^⊥
val y = new Ref(7)   // Ref[Int]^{y}
val z = y            // Ref[Int]^{y,z}
new Ref(7)           // Ref[Int]^∅
```

另有两个子类型判断：$Gamma tack.r qt(T_1, q_1) subt qt(T_2, q_2)$ 与限定符上的 $Gamma tack.r q_1 subt q_2$。$Gamma(x) = qt(T, q)$ 表示在上下文中查到 $x : qt(T, q)$。上下文维持不变式：被跟踪的变量包含自身，即绑定总是形如 $x : qt(T, q + x)$。限定符上的运算如下：

#align(center, table(
  columns: 2,
  align: (center + horizon, left + horizon),
  stroke: 0.5pt,
  inset: 6pt,
  [记号], [定义],
  [$q_1 qleq q_2$], [$q_1 = bot$ 或 $q_1 subset.eq q_2$，即 $bot$ 为最小元的包含序],
  [$q_1 qjoin q_2$], [对应的并，$bot qjoin q = q$],
  [$q + x$], [$bot + x = bot$，$alpha + x = alpha union {x}$],
  [$q_1 qplus q_2$], [$bot qplus q = bot$，$alpha qplus q = alpha qjoin q$],
  [$q_1 qmeet q_2$], [$alpha qmeet beta = alpha inter beta$，$bot qmeet bot = bot$，$alpha qmeet bot = bot qmeet alpha = emptyset$],
  [$q[p \/ x]$], [把 $alpha$ 中的 $x$ 换成 $p$；$p = bot$ 时只删去 $x$；$bot[p \/ x] = bot$],
  [$Gamma^q$], [${x : qt(T, q' + x) in Gamma mid(|) q' + x qleq q}$],
))

$+$ 与 $qplus$ 保证未跟踪的仍未跟踪。$Gamma^q$ 称为*环境过滤*：未跟踪绑定总是保留，被跟踪的绑定仅当限定符落在 $q$ 内才保留。

== 类型规则

#rules(
  R("T-cst", $c in B$, $Gamma tack.r c : qt(B, bot)$),
  R("T-var", $Gamma(x) = qt(T, q)$, $Gamma tack.r x : qt(T, q)$),
  R("T-sub", $Gamma tack.r t : qt(T_1, q_1)$, $Gamma tack.r qt(T_1, q_1) subt qt(T_2, q_2)$, $Gamma tack.r t : qt(T_2, q_2)$),
  R("T-ref", $Gamma tack.r t : qt(T, bot)$, $Gamma tack.r "ref" t : qt((refT(T)), emptyset)$),
  R("T-assign", $Gamma tack.r t_1 : qt((refT(T)), q)$, $Gamma tack.r t_2 : qt(T, bot)$, $Gamma tack.r t_1 := t_2 : qt(unitT, bot)$),
  R("T-deref", $Gamma tack.r t : qt((refT(T)), q)$, $Gamma tack.r !t : qt(T, bot)$),
)

单元只能存放未跟踪的值，读出的值也未跟踪，因此基础系统没有嵌套引用；分配得到新鲜引用。

#rules(
  R("T-abs",
    prem(
      $F = fn(f, x, T_1, q_1, T_2, q_2)$,
      $(Gamma, f : qt(F, q_f + f), x : qt(T_1, q_1 + x))^qc(q_f qjoin {f, x}) tack.r t : qt(T_2, q_2)$,
    ),
    $Gamma tack.r lambda f(x). thin t : qt(F, q_f)$),
  R("T-app",
    prem(
      $Gamma tack.r t_1 : qt((fn(f, x, T_1, q_1 qmeet q_f, T_2, q_2)), q_f)$,
      prow($Gamma tack.r t_2 : qt(T_1, q_1)$, $x, f in.not FV(T_2)$),
    ),
    $Gamma tack.r t_1 thin t_2 : qt(T_2, q_2 [q_1 \/ x, q_f \/ f])$),
)

*T-abs：$q_f$ 约束函数能看见什么。* 函数体在过滤后的上下文中定型，所以 $q_f$ 是函数所捕获之物的上界，最小取值是除 $f, x$ 外各自由变量的限定符之并。形参同样要通过过滤：$q_1 + x qleq q_f qjoin {f, x}$ 要求 $q_1 subset.eq q_f$，即形参只能声明与函数捕获之物重叠。

*T-app：可观察分离。* 规则中的 $q_1$ 是*实参*的限定符。函数只能经由 $q_f$ 观察环境，所以实参与环境的共享中，只有 $q_1 qmeet q_f$ 可被观察到，规则要求函数的形参限定符恰为它。结合 T-sub 与 S-fun 的形参逆变可推知，对形参限定符为 $p$ 的函数，实际检查的是 $Gamma tack.r q_1 qmeet q_f subt p$。

```scala
val c1 = ...; val c2 = ...                  // Ref[Int]^{c1}, Ref[Int]^{c2}
def addRef(c: Ref[Int]^∅) = { c1 += !c }    // (Ref[Int]^∅ => Unit)^{c1}
addRef(c1)    // 错误：{c1} ⊓ {c1} = {c1}，形参只允许 ∅
addRef(c2)    // 通过：{c2} ⊓ {c1} = ∅
```

允许重叠须声明 `c: Ref[Int]^{c1}`。`addRef(c2)` 放行，因为函数看不到 `c2`。

*T-app：依赖应用。* 结果限定符 $q_2$ 中的 $x$、$f$ 在调用时分别换成 $q_1$、$q_f$，由此得到轻量的限定符多态：

```scala
def inc(x: Ref[Int]^∅) = { x := !x + 1; x }  // ((x: Ref[Int]^∅) => Ref[Int]^{x})^⊥
inc(c1)           // c1 : Ref[Int]^{a,b,c1}，结果 Ref[Int]^{a,b,c1}
inc(new Ref(0))   // 结果 Ref[Int]^∅
```

代换 $bot$ 时只删去变量。`def f(x: T^∅) = new Ref(0)` 的类型可以上转型为 $(x : qt(T, emptyset)) -> qt(refT(intT), vs(x))$；以 $bot$ 调用时若结果取 $bot$，新引用就被误标为未跟踪。

旁条件 $x, f in.not FV(T_2)$ 要求应用时依赖只在顶层 $q_2$，$T_2$ 内部的依赖须先经子类型消去，原因见下一节。let 编码为 $(lambda f(x). thin t_1) thin t_2$（$f$ 取新名），由此得到

#rules(
  R("Let-Encoding",
    $Gamma tack.r t_2 : qt(T_1, q_1)$, $Gamma, x : qt(T_1, q_1 + x) tack.r t_1 : qt(T_2, q_2)$, $x in.not FV(T_2)$,
    $Gamma tack.r "let" x = t_2 "in" t_1 : qt(T_2, q_2 [q_1 \/ x])$),
)

例如 `val y = new Ref(x); y` 在体内为 $qt(refT(intT), vs(y))$，离开作用域后为 $vs(y)[emptyset \/ y] = emptyset$，与直接分配无法区分。

#rm(supplement: [$qmeet$ 的字面定义])[
  按表中定义，被跟踪的函数接受 $bot$ 实参时得到 $bot qmeet alpha = emptyset$，而 $qt(B, emptyset) subt qt(B, bot)$ 不成立，于是形参为 $bot$（包括零参函数的 $qt(unitT, bot)$ 形参）的被跟踪函数无法调用。实现中应令 $bot qmeet q_f = bot$；$alpha qmeet bot = emptyset$ 须保留，否则未跟踪函数可把被跟踪实参当作未跟踪值接收。
]

== 子类型与逃逸闭包

#rules(
  R("S-base", $Gamma tack.r q_1 subt q_2$, $Gamma tack.r qt(B, q_1) subt qt(B, q_2)$),
  R("S-ref", $Gamma tack.r q_1 subt q_2$, $Gamma tack.r qt(T_1, bot) subt qt(T_2, bot)$, $Gamma tack.r qt(T_2, bot) subt qt(T_1, bot)$, $Gamma tack.r qt((refT(T_1)), q_1) subt qt((refT(T_2)), q_2)$),
  R("S-fun",
    prem(
      prow($Gamma tack.r q_5 subt q_6$, $Gamma tack.r qt(T_3, q_3) subt qt(T_1, q_1)$),
      $Gamma, f : qt((fn(f, x, T_1, q_1, T_2, q_2)), q_5 + f), x : qt(T_3, q_3 + x) tack.r qt(T_2, q_2) subt qt(T_4, q_4)$,
    ),
    $Gamma tack.r qt((fn(f, x, T_1, q_1, T_2, q_2)), q_5) subt qt((fn(f, x, T_3, q_3, T_4, q_4)), q_6)$),
)

引用对内容类型不变。S-fun 除形参逆变、结果协变外，比较结果时还把 $f$、$x$ 加入上下文，这是改写自引用的入口。限定符子类型在 $qleq$ 之外只多一条原则：若上下文中有函数绑定 $f : qt(F, q + f)$，则 ${f}$ 与 $q + f$ 等价，因为经由 $f$ 能到达的正是它捕获的东西。论文正文只有这一文字描述，下面的规则是按它整理的：

#rules(
  R("Q-sub", $q_1 qleq q_2$, $Gamma tack.r q_1 subt q_2$),
  R("Q-self", $f : qt(F, q + f) in Gamma$, $F "是函数类型"$, $Gamma tack.r q + f subt {f}$),
  R("Q-cong", $Gamma tack.r q_1 subt q_2$, $Gamma tack.r q_1 qjoin q subt q_2 qjoin q$),
  R("Q-trans", $Gamma tack.r q_1 subt q_2$, $Gamma tack.r q_2 subt q_3$, $Gamma tack.r q_1 subt q_3$),
)

限定符须良作用域。由于 $bot qleq q$，未跟踪的值可当作被跟踪，反之不行。

#eg(supplement: [逃逸闭包])[
  ```scala
  val y = new Ref(0)
  () => y
  ```
  闭包在体内的类型为 $qt((f() -> qt(refT(intT), vs(y))), vs(y))$。离开作用域时若把各处的 $y$ 都换成 $emptyset$，每次调用都会声称返回新鲜引用，实际却始终是同一个单元。顶层换成 $emptyset$ 没问题，闭包本身只是一个值；结果类型描述的却是每次调用产生的值。正确的推导是：
  + S-fun 取 $q_5 = q_6 = vs(y)$。在 $f : qt(F, vs(y, f))$ 下，由 Q-sub 与 Q-self 得 ${y} subt {y, f} subt {f}$，于是闭包类型可改写为 $qt((f() -> qt(refT(intT), vs(f))), vs(y))$；
  + 此时 $y in.not FV(T_2)$，由 Let-Encoding 得 $qt((f() -> qt(refT(intT), vs(f))), emptyset)$；
  + 绑定 `val g = ...` 后 $g$ 的限定符为 $vs(g)$；调用 `g()` 时 T-app 代入 $vs(f)[vs(g) \/ f] = vs(g)$，返回的引用与 `g` 有可见的别名。
]

这就是 T-app 禁止嵌套依赖的原因：若允许把实参限定符代入 $T_2$ 内部，就会得到上面错误的类型，所以必须先经 S-fun 改写为自引用。代价是精度。投影函数 $pi_1 = lambda f(a). thin lambda g(b). thin a$（柯里化的双参函数，返回第一个参数）只能定为
$
  pi_1 : qt((f(a : qt(A, q_1)) -> qt((g(b : qt(B, q_2)) -> qt(A, vs(g))), q_1 + a)), q_1).
$
内层结果本可写为 $q_1 + a$，但那样外层结果类型内部会出现 $a$。

序对编码为函数，因此也有自引用，计数器靠它定型：`Pair[p => A, B]` 表示自引用为 `p` 的序对类型，`fst`、`snd` 是投影。

```scala
// 体内：Pair[(()=>Unit)^{c}, (()=>Unit)^{c}]^{c}
// 对外：counter : Int => Pair[p => (()=>Unit)^{p}, (()=>Unit)^{p}]^∅
val p = counter(0)   // Pair[...]^{p}
val incr = fst(p)    // (()=>Unit)^{incr,p}
val decr = snd(p)    // (()=>Unit)^{decr,p}
```

`incr` 与 `decr` 的限定符都含 `p`，因此不分离。

== 元理论

运行时加入位置 $l$，值为 $v ::= c | lambda f(x). thin t | l$。存储 $sigma$ 是位置到值的有限映射，$t | sigma -> t' | sigma'$ 是标准的传值小步归约。存储类型 $Sigma$ 把位置映射到带 $bot$ 的基类型 $qt(T, bot)$，类型判断相应写作 $Gamma | Sigma tack.r t : qt(T, q)$；限定符中也可以出现位置，且位置跟踪自身：$Sigma(l) = qt(T, bot)$ 时 $Gamma | Sigma tack.r l : qt((refT(T)), vs(l))$。$Gamma | Sigma tack.r sigma$ 表示 $dom(sigma) = dom(Sigma)$，且每个 $sigma(l)$ 都具有类型 $Sigma(l)$。

#lemma[（代换，引理 3.1）若 $emptyset | Sigma tack.r v : qt(T_1, q_1)$，$emptyset | Sigma tack.r lambda f(x). thin t_1 : qt((fn(f, x, T_1, q_1 qmeet q_f, T_2, q_2)), q_f)$，且 $x, f in.not FV(T_2)$，则 $emptyset | Sigma tack.r t_1 [v \/ x, (lambda f(x). thin t_1) \/ f] : qt(T_2, q_2 [q_1 \/ x, q_f \/ f])$。]

引理对应 β 归约：函数体只经由 $q_f$ 观察环境，只看到实参的 $q_1 qmeet q_f$ 部分。

#thm[（进展，定理 3.2）若 $emptyset | Sigma tack.r t : qt(T, q)$，则 $t$ 是值，或对任意满足 $emptyset | Sigma tack.r sigma$ 的 $sigma$，存在 $t', sigma'$ 使 $t | sigma -> t' | sigma'$。]

#thm[（保持，定理 3.3）若 $emptyset | Sigma tack.r t : qt(T, q)$，$emptyset | Sigma tack.r sigma$，且 $t | sigma -> t' | sigma'$，则存在 $Sigma' supset.eq Sigma$ 与 $q' qleq dom(Sigma') without dom(Sigma)$，使 $emptyset | Sigma' tack.r sigma'$ 且 $emptyset | Sigma' tack.r t' : qt(T, q qplus q')$。]

$q'$ 是新分配的位置，限定符只因此增长：`ref 0` 的类型为 $qt(refT(intT), emptyset)$，归约为 $l$ 后为 $vs(l)$。$qplus$ 让未跟踪的项保持未跟踪。

#coro[（分离保持，推论 3.4）若 $emptyset | Sigma tack.r t_i : qt(T_i, q_i)$（$i = 1, 2$），$q_1 qmeet q_2 qleq emptyset$，$emptyset | Sigma tack.r sigma$，$t_1 | sigma -> t'_1 | sigma'$ 且 $t_2 | sigma' -> t'_2 | sigma''$，则存在 $Sigma'' supset.eq Sigma' supset.eq Sigma$ 与 $q'_1, q'_2$，使 $emptyset | Sigma' tack.r t'_1 : qt(T_1, q'_1)$，$emptyset | Sigma'' tack.r t'_2 : qt(T_2, q'_2)$，且 $q'_1 qmeet q'_2 qleq emptyset$。]

分配是唯一扩展存储的构造，不同步骤分配的位置互不相同，所以不相交得以保持。

== 效果系统 $lambda^*_epsilon$

嵌套可变状态的别名结构随写入变化，需要流敏感推理。$lambda^*_epsilon$ 让每个项再带一个*效果*，记录它对哪些别名组做了什么。

=== 效果的代数结构

*标签。* 效果标签取自一个*效果 quantale*（effect quantale）$(E, qjoin, seqc, I)$：$qjoin$ 是偏定义的并，用于合并分支；$seqc$ 是偏定义、结合、以 $I$ 为单位元的顺序复合，$e_1 seqc e_2$ 表示先 $e_1$ 后 $e_2$，一般不交换；并且 $seqc$ 对 $qjoin$ 双侧分配，两侧同时有定义或同时无定义。$qleq_E$ 是 $qjoin$ 诱导的序。本文用两种标签：
- $E_"rw"$：$botE qleq rd qleq wr$，依次表示仅提及、读、写；$seqc$ 就是 $qjoin$，$I = botE$；
- $E_k$：在 $E_"rw"$ 上加顶元 $kill$，表示此后不得再访问，其 $seqc$ 见后文表格。

*效果。* 效果 $epsilon = {(alpha_1, e_1), dots, (alpha_n, e_n)}$ 是有限个“别名组–标签”对，别名组 $alpha_i$ 是变量或位置的集合，两两不交，表示组 $alpha_i$ 可能发生 $e_i$。

#def(supplement: [存储敏感的效果 quantale，定义 4.2])[
  给定标签 quantale $E$，所有效果构成 $Delta(E)$，其运算为：
  - $epsilon_1 qjoin epsilon_2$ 与 $epsilon_1 seqc epsilon_2$：把 $epsilon_2$ 的对逐个并入 $epsilon_1$。若与 $epsilon_1$ 中某对的定义域相交，就合并定义域，并用 $qjoin_E$ 或 $seqc_E$ 合并标签（$epsilon_1$ 的标签在左）；否则直接加入。任一次 $seqc_E$ 无定义，整个复合就无定义。
  - $epsilon_1 qleq epsilon_2$ 当且仅当 $forall (alpha_1, e_1) in epsilon_1. thin exists (alpha_2, e_2) in epsilon_2. thin alpha_1 subt alpha_2 and e_1 qleq_E e_2$；单位元为 $emptyset$。
  - $epsilon[alpha \/ x]$ 把各定义域中的 $x$ 换成 $alpha$；$epsilon|_S$ 把各定义域与 $S$ 求交（论文未定义，按“去掉新位置”理解）。
]

若 $E$ 是效果 quantale，则 $Delta(E)$ 满足分配律（引理 4.3）。

*传递别名。* 效果的定义域用 $q^*$ 计算：$bot^* = emptyset$；$alpha^*$ 是包含 $alpha$ 的最小集合，并满足：若 $x in alpha^*$ 且 $x : qt(T, gamma) in Gamma$，则 $gamma subset.eq alpha^*$。上下文的限定符不一定传递封闭：可能有 $y : qt(T, vs(x, y))$ 与形参 $z : qt(T, vs(y, z))$。杀死 $x$ 后使用 $z$，${y, z}$ 与 ${x}$ 不相交，冲突会被漏掉，$vs(z)^* = {x, y, z}$ 才能暴露它。

=== 类型与效果规则

函数类型在箭头上加*潜在效果*，写作 $efn(f, x, T_1, q_1, epsilon, T_2, q_2)$，表示调用函数时发生的效果。判断 $Gamma | Sigma tack.r t : qt(T, q) eff(epsilon)$ 表示求值 $t$ 发生的效果不超过 $epsilon$。

#rules(
  R("E-var", $Gamma(x) = qt(T, q)$, $Gamma | Sigma tack.r x : qt(T, q) eff({(q^*, botE)})$),
  R("E-abs",
    prem(
      $F = efn(f, x, T_1, q_1, epsilon, T_2, q_2)$,
      $(Gamma, f : qt(F, q_f + f), x : qt(T_1, q_1 + x))^qc(q_f qjoin {f, x}) | Sigma tack.r t : qt(T_2, q_2) eff(epsilon)$,
    ),
    $Gamma | Sigma tack.r lambda f(x). thin t : qt(F, q_f) eff({(q_f^*, botE)})$),
  R("E-app",
    prem(
      $Gamma | Sigma tack.r t_1 : qt((efn(f, x, T_1, q_1 qmeet q_f, epsilon_3, T_2, q_2)), q_f) eff(epsilon_1)$,
      prow($Gamma | Sigma tack.r t_2 : qt(T_1, q_1) eff(epsilon_2)$, $x, f in.not FV(T_2)$),
    ),
    $Gamma | Sigma tack.r t_1 thin t_2 : qt(T_2, q_2 [q_1 \/ x, q_f \/ f]) eff(epsilon_1 seqc epsilon_2 seqc epsilon_3 [q_1^* \/ x, q_f^* \/ f])$),
  R("E-sub", $Gamma | Sigma tack.r t : qt(T, q) eff(epsilon_1)$, $Gamma | Sigma tack.r epsilon_1 qleq epsilon_2$, $Gamma | Sigma tack.r t : qt(T, q) eff(epsilon_2)$),
)

变量与闭包创建只*提及*别名组（标签 $botE$）。应用按求值顺序复合函数、实参与潜在效果，并把潜在效果中的形参与自引用换成调用点的传递别名。函数子类型 S-fun 再加一个前提 $epsilon_1 qleq epsilon_2$，即潜在效果协变。

为陈述可靠性，论文给归约加上实际效果，记作 $t | sigma ->^(epsilon) t' | sigma'$，例如 `!l` 产生 ${(l, rd)}$，`l := v` 产生 ${(l, wr)}$。

#prop[（保持，命题 4.4）若 $Gamma | Sigma tack.r t : qt(T, q) eff(epsilon_1)$，$Gamma | Sigma tack.r sigma$，且 $t | sigma ->^(epsilon_2) t' | sigma'$，则存在 $Sigma' supset.eq Sigma$ 与 $q' qleq dom(Sigma') without dom(Sigma)$，使 $Gamma | Sigma' tack.r sigma'$，$Gamma | Sigma' tack.r t' : qt(T, q qplus q') eff(epsilon_3)$，且 $epsilon_2 seqc epsilon_3|_(dom(Sigma)) qleq epsilon_1$。]

即单步实际效果接上剩余项的静态效果（去掉新位置），不超过原静态效果。论文只给出插桩语义的草图与命题，没有证明。

=== 读写效果：流不敏感

标签取 $E_"rw"$，读写规则为

#rules(
  R("E-deref", $Gamma | Sigma tack.r t : qt((refT(T)), q) eff(epsilon)$, $Gamma | Sigma tack.r !t : qt(T, bot) eff(epsilon seqc {(q^*, rd)})$),
  R("E-assign", $Gamma | Sigma tack.r t_1 : qt((refT(T)), q) eff(epsilon_1)$, $Gamma | Sigma tack.r t_2 : qt(T, bot) eff(epsilon_2)$, $Gamma | Sigma tack.r t_1 := t_2 : qt(unitT, bot) eff(epsilon_1 seqc epsilon_2 seqc {(q^*, wr)})$),
)

$seqc$ 即 $qjoin$，故流不敏感。

=== kill 效果与移动语义：流敏感

标签取 $E_k$，$seqc$ 如下表，左列为先发生的效果：

#align(center, table(
  columns: 5,
  align: center + horizon,
  stroke: 0.5pt,
  inset: 6pt,
  [$seqc$], [$botE$], [$rd$], [$wr$], [$kill$],
  [$botE$], [$botE$], [$rd$], [$wr$], [$kill$],
  [$rd$], [$rd$], [$rd$], [$wr$], [$kill$],
  [$wr$], [$wr$], [$wr$], [$wr$], [$kill$],
  [$kill$], table.cell(colspan: 4)[无定义],
))

$kill seqc e$ 对任何 $e$ 都无定义：别名组被杀死后，再使用乃至提及它都是类型错误。语言扩展如下：
- 类型 $refT(qt(T, emptyset))$：单元存放被跟踪的值，并且是其唯一持有者；
- `move t`：返回 $t$ 所指的单元，并杀死 $t$ 原有的全部别名，结果新鲜；
- `swap t1 t2`：把 $t_2$ 放进单元 $t_1$，杀死 $t_2$ 的全部别名，返回单元的旧内容，结果新鲜。

`!` 与 `:=` 仍只作用于存放未跟踪值的单元。

#rules(
  R("Ek-ref",
    $Gamma | Sigma tack.r t : qt(T, alpha) eff(epsilon_1)$,
    $Gamma | Sigma tack.r "ref" t : qt((refT(qt(T, emptyset))), emptyset) eff(epsilon_1 seqc {(alpha^*, kill)})$),
  R("E-move",
    $Gamma | Sigma tack.r t : qt((refT(qt(T, q))), alpha) eff(epsilon_1)$,
    $Gamma | Sigma tack.r "move" t : qt((refT(qt(T, q))), emptyset) eff(epsilon_1 seqc {(alpha^*, kill)})$),
  R("E-swap",
    prem(
      prow($Gamma | Sigma tack.r t_1 : qt((refT(qt(T, emptyset))), alpha) eff(epsilon_1)$, $Gamma | Sigma tack.r t_2 : qt(T, beta) eff(epsilon_2)$),
      $beta^* inter alpha^* = emptyset$,
    ),
    $Gamma | Sigma tack.r "swap" t_1 thin t_2 : qt(T, emptyset) eff(epsilon_1 seqc epsilon_2 seqc {(beta^*, kill), (alpha^*, wr)})$),
)

Ek-ref 处理被跟踪的值，未跟踪的值仍用 T-ref。E-swap 要求单元与换入值不相交，这也保证结果效果的两个定义域不交。

#eg(supplement: [移动之后])[
  ```scala
  val x = new Ref(1); val y = x   // x : Ref[Int]^{x},  y : Ref[Int]^{x,y}
  val z = move(x)                 // z : Ref[Int]^{z}
  !x + !y                         // 类型错误
  ```
  `move(x)` 的效果为 ${({x}, botE)} seqc {({x}, kill)} = {({x}, kill)}$。`!y` 的效果为 ${({x, y}, rd)}$，二者定义域相交，需要计算 $kill seqc rd$，无定义。同理，`val nc = new Ref(y)` 得到 $refT(qt(refT(intT), emptyset))$ 并杀死 `y`；`val z = swap(nc, x)` 取出旧内容作为新鲜的 `z`，并杀死 `x`。
]

动态语义中，`ref v` 与 `swap` 杀死换入值中出现的全部位置；`move l` 杀死 $l$，把内容复制到新位置并返回之。真实实现可以省去复制。

*提及与使用。* 严格的 $seqc$ 连定义捕获已杀死变量的闭包都会拒绝。若放宽为 $kill seqc botE = kill$，只禁止使用，则有漏洞：

```scala
// g : () => Ref[Int]^∅，潜在效果 {(∅, kill)}
def g() = { val x = new Ref(0); val y = move(x); x }
val c = g()   // Ref[Int]^{c}，实际已被杀死
```

$x$ 离开作用域时被代换为 $emptyset$，kill 随之丢失。作者建议的修复之一是让结果以自引用 $z$ 命名自己，把 $(z, kill)$ 附在结果类型上，而非箭头上。

== 应用

*基础系统中的模式。* 下面 `CanThrow` 是 `try` 传给块的抛异常能力，`canIO : CanIO` 是全局 I/O 能力；基础系统无多态，类型参数按元层参数理解。

```scala
def par(a: (() => Unit)^∅)(b: (() => Unit)^∅): Unit
def try[A^∅](block: (CanThrow^∅ => A^∅)^∅): Option[A]^∅
def withoutIO[A^∅](cap: CanIO^∅)(block: (() => A^∅)^∅): A^∅
def borrow[A^∅, B^∅](x: A^∅)(block: (A^∅ => B^∅)^∅): B^∅ = block(x)
```

- *非干扰*：设块 `b1`、`b2` 的限定符为 $q_(b 1)$、$q_(b 2)$。内层函数捕获 `a`，限定符含 $a$；`par(b1)` 的限定符经依赖应用为 $q_(b 1)$，再应用于 `b2` 时 T-app 要求 $q_(b 2) qmeet q_(b 1) = emptyset$。
- *不逃逸*：块结果为 $qt(A, emptyset)$，捕获 `throw` 的闭包无法作为结果逃出。
- *不可访问*：设作用域中只有 `canIO` 一个 `CanIO` 值，块须与它分离，因此用不了它。
- *借用*：`borrow(c1) { c2 => ... }` 中块与 `c1` 分离，只能经 `c2` 访问该单元。

同理，代数效应的操作可编码为限定符为 $emptyset$ 的能力值：被跟踪，所以不能存入单元，也不能逃出 handler。

*一次性延续。* 控制算子族有一条通用规则：

#rules(
  R("T-ctrl",
    prem($Gamma, k : qt((k(x : qt(T, q_1)) earr(epsilon seqc K E) "Ret"), vs(k)) tack.r t : qt(T, q_2) eff(epsilon_1)$, $N E$),
    $Gamma tack.r cal(C) thin k "in" t : qt(T, q_1) eff(epsilon_1)$),
)

$cal(C) thin k "in" t$ 把当前延续绑定到 $k$ 后求值 $t$。$"Ret"$ 是延续的返回类型；$epsilon$ 是延续所代表的剩余计算的效果（论文正文称之为 $delta$）；$K E$ 是每次调用 $k$ 附加的效果；$N E$ 是可选的不逃逸条件。一次性 `let/cc` 取 $"Ret" = qt("Nothing", bot)$、$K E = {(k, kill)}$、$N E = "true"$；不逃逸的一次性 `shift` 取 $"Ret" = qt(S, q_3)$、同样的 $K E$，并令 $N E$ 为 $k in.not FV(qt(T, q_2))$。第一次调用 $k$ 杀死 $k$，第二次调用需计算 $kill seqc botE$，无定义；取 $K E = emptyset$ 即得多次延续。

*无数据竞争的并行。* 完全分离会拒绝共享只读引用，借助读写效果可以放宽：

#rules(
  R("E-par-pair",
    $Gamma tack.r t_1 : qt(T_1, q_1) eff(epsilon_1)$, $Gamma tack.r t_2 : qt(T_2, q_2) eff(epsilon_2)$, $"non-interfering"(epsilon_1, epsilon_2)$,
    $Gamma tack.r "parPair"(t_1, t_2) : qt((qt(T_1, q_1), qt(T_2, q_2)), q_3) eff(epsilon_1 qjoin epsilon_2)$),
)

$
  "non-interfering"(epsilon_1, epsilon_2) equiv & forall (alpha_1, e_1) in epsilon_1, (alpha_2, e_2) in epsilon_2. \
  & quad alpha_1 inter alpha_2 != emptyset ==> e_1 qjoin_E e_2 qleq rd
$

$"parPair"$ 并行求值两侧并返回序对，$q_3$ 是序对的限定符；条件要求共享的别名组至多被读。在 `val c2 = c1` 之后，`par({ !c1 }, { !c2 })` 通过，`par({ c1 := 1 }, { !c2 })` 被拒绝。

== 动手实现

下面是 $lambda^*_epsilon$（含 kill）的综合式检查器骨架（OCaml 风格）。限定符表示为 `Bot` 或 `S α`，函数类型 `TFun (f, x, T1, q1, ε, T2, q2)` 对应 $efn(f, x, T_1, q_1, epsilon, T_2, q_2)$，上下文是列表，表头为最右端的绑定。λ 需标注函数类型，$q_f$ 由自由变量推出。`fv t` 求项的自由变量，`occurs x T` 判断 $x$ 是否出现在 $T$ 的限定符或潜在效果中，`lookup` 查上下文；函数类型已 α-换名。

```ocaml
module VS = Set.Make (String)
type q = Bot | S of VS.t                        (* ⊥ | α *)
type label = Mention | Rd | Wr | Kill           (* ⊥E ⊑ rd ⊑ wr ⊑ kill *)
type eff = (VS.t * label) list                  (* 定义域两两不交 *)
type ty =
  | TBase of string
  | TRef of ty * q                              (* Ref T（q = ⊥）或 Ref T^∅ *)
  | TFun of var * var * ty * q * eff * ty * q   (* f(x : T1^q1) -ε-> T2^q2 *)
type ctx = (var * ty * q) list                  (* 表头 = 最右端，绑定形如 x : T^(q+x) *)

let leq a b = match a, b with
  | Bot, _ -> true | S _, Bot -> false | S a, S b -> VS.subset a b
let join a b = match a, b with
  | Bot, q | q, Bot -> q | S a, S b -> S (VS.union a b)
let plus q x = match q with Bot -> Bot | S a -> S (VS.add x a)
let subst_q q x p = match q with                (* q[p/x]；p = ⊥ 时只删去 x *)
  | S a when VS.mem x a -> join (S (VS.remove x a)) p
  | q -> q
let meet_arg qa qf = match qa, qf with          (* T-app 的 q1 ⊓ qf，见 ⊓ 的注记 *)
  | Bot, _ -> Bot
  | S _, Bot -> S VS.empty
  | S a, S b -> S (VS.inter a b)
let filter ctx q = List.filter (fun (_, _, qx) -> leq qx q) ctx   (* Γ^q *)

(* 沿上下文限定符求闭包：step 为真的绑定才展开 *)
let reach step ctx a =
  let rec go seen = function
    | [] -> seen
    | x :: xs when VS.mem x seen -> go seen xs
    | x :: xs ->
        let more = match lookup ctx x with
          | (_, t, S g) when step t -> VS.elements g | _ -> [] in
        go (VS.add x seen) (more @ xs) in
  go VS.empty (VS.elements a)
let star ctx = function                                  (* q* *)
  | Bot -> VS.empty | S a -> reach (fun _ -> true) ctx a
let is_fun = function TFun _ -> true | _ -> false
let sub_q ctx a b = match a, b with             (* {f} ≡ q+f *)
  | Bot, _ -> true | S _, Bot -> false
  | S a, S b -> VS.subset a (reach is_fun ctx b)

(* 定义 4.2：把 e2 的对逐个并入 e1，与新对相交的旧对一次全部合并 *)
let rank = function Mention -> 0 | Rd -> 1 | Wr -> 2 | Kill -> 3
let lub a b = if rank a >= rank b then a else b
let seq_l a b = if a = Kill then None else Some (lub a b)
let compose comb e1 e2 =
  List.fold_left (fun acc (a, l) -> Option.bind acc (fun acc ->
      let hit, rest = List.partition (fun (b, _) -> not (VS.disjoint a b)) acc in
      let dom = List.fold_left (fun s (b, _) -> VS.union s b) a hit in
      let pre = List.fold_left (fun m (_, l') -> lub m l') Mention hit in
      Option.map (fun l -> (dom, l) :: rest) (comb pre l)))
    (Some e1) e2
let seq e1 e2 = match compose seq_l e1 e2 with
  | Some e -> e | None -> fail "use after kill"
let subst_eff e x p =                     (* 代换后重新合并相交的对 *)
  let e = List.map (fun (a, l) ->
      if VS.mem x a then (VS.union (VS.remove x a) p, l) else (a, l)) e in
  Option.get (compose (fun a b -> Some (lub a b)) [] e)
let eff_leq ctx e1 e2 =
  List.for_all (fun (a, l) ->
      List.exists (fun (b, l') -> sub_q ctx (S a) (S b) && rank l <= rank l') e2) e1

let rec sub ctx (t1, q1) (t2, q2) = sub_q ctx q1 q2 && sub_ty ctx q1 t1 t2
and sub_ty ctx q5 t1 t2 = match t1, t2 with
  | TBase a, TBase b -> a = b
  | TRef (a, qa), TRef (b, qb) -> sub ctx (a, qa) (b, qb) && sub ctx (b, qb) (a, qa)
  | TFun (f, x, a1, p1, e1, r1, s1), TFun (_, _, a2, p2, e2, r2, s2) ->   (* S-fun *)
      let ctx' = (x, a2, plus p2 x) :: (f, t1, plus q5 f) :: ctx in
      sub ctx (a2, p2) (a1, p1) && eff_leq ctx' e1 e2 && sub ctx' (r1, s1) (r2, s2)
  | _ -> false

(* 逃逸：协变位置上的 x 改写为自引用 f（{x} <: {f}），逆变位置无法改写 *)
let rec rewire x f pos t =
  let rq pos = function
    | S a when VS.mem x a ->
        if pos then S (VS.add f (VS.remove x a)) else fail "escape"
    | q -> q in
  let re e =
    if List.exists (fun (a, _) -> VS.mem x a) e && not pos then fail "escape"
    else subst_eff e x (VS.singleton f) in
  match t with
  | TBase _ -> t
  | TRef _ -> if occurs x t then fail "escape" else t
  | TFun (g, y, a, p, e, r, s) ->
      TFun (g, y, rewire x f (not pos) a, rq (not pos) p,
            re e, rewire x f pos r, rq pos s)
let avoid x qb tb = match tb, qb with
  | _ when not (occurs x tb) -> tb
  | TFun (f, _, _, _, _, _, _), S a when VS.mem x a -> rewire x f true tb
  | _ -> fail "x escapes its scope"

let rec synth ctx = function
  | Const (_, b) -> (TBase b, Bot, [])
  | Var x ->   (* E-var *)
      let _, t, q = lookup ctx x in (t, q, [ (star ctx q, Mention) ])
  | Lam (f, x, (TFun (_, _, a, p, lat, r, s) as ft), body) ->   (* E-abs *)
      let qf = VS.fold (fun y acc -> let _, _, qy = lookup ctx y in join acc qy)
                 (VS.remove f (VS.remove x (fv body))) Bot in
      let inner = filter ((x, a, plus p x) :: (f, ft, plus qf f) :: ctx)
                    (join qf (S (VS.of_list [ f; x ]))) in
      let tb, qb, eb = synth inner body in
      if not (sub inner (tb, qb) (r, s) && eff_leq inner eb lat) then fail "body";
      (ft, qf, [ (star ctx qf, Mention) ])
  | App (t1, t2) ->   (* E-app *)
      let tf, qf, e1 = synth ctx t1 in
      let ta, qa, e2 = synth ctx t2 in
      (match tf with
       | TFun (f, x, a, p, lat, r, s) ->
           if not (sub ctx (ta, meet_arg qa qf) (a, p)) then fail "argument overlaps";
           if occurs x r || occurs f r then fail "nested dependency";
           let lat = subst_eff (subst_eff lat x (star ctx qa)) f (star ctx qf) in
           (r, subst_q (subst_q s x qa) f qf, seq (seq e1 e2) lat)
       | _ -> fail "not a function")
  | Let (x, t2, t1) ->
      let ta, qa, e2 = synth ctx t2 in
      let tb, qb, e1 = synth ((x, ta, plus qa x) :: ctx) t1 in
      (avoid x qb tb, subst_q qb x qa, seq e2 (subst_eff e1 x (star ctx qa)))
  | Ref t ->
      (match synth ctx t with
       | u, Bot, e -> (TRef (u, Bot), S VS.empty, e)   (* T-ref *)
       | u, q, e ->   (* Ek-ref *)
           (TRef (u, S VS.empty), S VS.empty, seq e [ (star ctx q, Kill) ]))
  | Deref t ->
      (match synth ctx t with
       | TRef (u, Bot), q, e -> (u, Bot, seq e [ (star ctx q, Rd) ])
       | _ -> fail "deref")
  | Assign (t1, t2) ->
      (match synth ctx t1, synth ctx t2 with
       | (TRef (u, Bot), q, e1), (u', q', e2) when sub ctx (u', q') (u, Bot) ->
           (TBase "Unit", Bot, seq (seq e1 e2) [ (star ctx q, Wr) ])
       | _ -> fail "assign")
  | Move t ->   (* E-move *)
      (match synth ctx t with
       | (TRef _ as u), q, e -> (u, S VS.empty, seq e [ (star ctx q, Kill) ])
       | _ -> fail "move")
  | Swap (t1, t2) ->   (* E-swap *)
      (match synth ctx t1, synth ctx t2 with
       | (TRef (u, S _), qa, e1), (u', qb, e2) when sub_ty ctx qb u' u ->
           let a = star ctx qa and b = star ctx qb in
           if not (VS.disjoint a b) then fail "swap with alias";
           (u, S VS.empty, seq (seq e1 e2) [ (b, Kill); (a, Wr) ])
       | _ -> fail "swap")
```

实现时有几点值得注意。
- *实参不收窄。* 论文没说 ${f} equiv q + f$ 是否只适用于自引用。若先用 Q-self 把实参的 $vs(y, g)$ 收窄为 $vs(g)$ 再与 $vs(y)$ 求交，重叠就被藏起来了，所以骨架用综合出的完整限定符求交。
- *逃逸改写。* `avoid` 是逃逸闭包例子第一步的算法化：顶层限定符含 $x$ 时，把协变位置的 $x$ 换成自引用；逆变位置出现 $x$ 则报错。
- *合并的传递性。* 论文称运算保持不交性，但按其递归定义，新对只与一个旧对合并，结果可能又与另一旧对相交。`compose` 一次合并全部相交的对。
- *效果标注。* 变量出现本身就产生 $botE$ 效果，所以 λ 的潜在效果标注必须覆盖体内提及的别名组。

== 评注

- *定位*：分离是两个限定符之间二元、局部的性质，不强加所有权树之类的全局堆结构。
- *缺口与扩展*：限定符子类型没有形式规则，效果系统的可靠性只有命题。作者讨论的扩展有：以 $emptyset$ 为下界的有界限定符多态 $forall rho subt alpha. thin qt(T, rho)$，必达集与可达集并记的 $qt(T, l..u)$，以及反向可达。
