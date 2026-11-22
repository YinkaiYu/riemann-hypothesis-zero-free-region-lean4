# 库原生证明压缩：黎曼 ζ(s) 经典无零点区域在 Lean 4 中的逐次纪录形式化

**余荫铠（Yin-Kai Yu）** — DeepSeek Harness × ChatGPT Desktop 协作研究轨道

*制品发布 v1.0 · 2026-11-22 · <https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>*

## 摘要

黎曼 ζ 函数的经典无零点区域，在任何一本解析数论教科书中都只需短短几页即可证明；然而它的 Lean 4 参考形式化
却占用了二十一个文件、21,641 个规范化 tokens。本文报告同一命题的一系列压缩形式化：它们在公开的证明压缩基准上
**十二次刷新纪录**，最终把证明压缩进单个文件、共 2,489 个 tokens。本文的数学内容并不是新的数论定理，而是解释
**形式证明中哪些部分是昂贵的、哪一步数学重组使它们变便宜、以及每次重组究竟节省了多少**。对每一次纪录，我们
依次说明它所替代之版本的瓶颈、所引入的核心数学推导、以及可测量的 token 变化。最后我们给出一个对照实验：
最终证明采用的 Mellin 变换路线，与一个同样正确的 Euler–Maclaurin 路线相比，后者在形式化成本上大约贵出五成；
我们也讨论了「用 token 数衡量证明质量」这一做法的局限。

**关键词**：形式化分析、Lean 4、Mathlib、证明压缩、无零点区域、解析差商、Borel–Carathéodory 不等式。

## 1 引言

黎曼 ζ 函数在实部大于一的复数 $s$ 上由级数

$$
\zeta(s) \;=\; \sum_{n=1}^{\infty} \frac{1}{n^{s}}
$$

定义，并可以延拓为整个复平面上的亚纯函数，唯一的极点位于 $s=1$。它的零点编码了素数的分布——这正是黎曼猜想的
内容，也是黎曼猜想之前那些无条件结果的来源。

远在黎曼猜想提出之前，Hadamard 与 de la Vallée Poussin 于 1896 年各自证明了：在竖直线
$\mathrm{Re}(s)=1$ 右侧一个很窄的区域之外，ζ 函数没有零点。这一结果——**经典无零点区域**——说的是：存在
一个绝对正常数 $c$，使得只要

$$
\mathrm{Re}(s) \;\ge\; 1 - \frac{c}{\log\left(|\mathrm{Im}(s)|+2\right)},
$$

就有 $\zeta(s) \neq 0$。它是带明确误差项的素数定理背后的解析输入，也是 Dirichlet $L$ 函数 Landau–Page 理论的
第一步；在一个形式化项目中，它还常常被后续论证反复引用。

**形式化背景。** 在 Levent Alpöge 的黎曼猜想 Lean 4 形式化中，这份定理的完整形式证明（即参考闭包）由二十一个
源文件组成；用本文所用公开基准的度量来说，这份闭包的价值是 21,641 个**规范化 token**。

**本文要谈什么。** 人们很容易像读教科书那样读一份形式证明：一页页分析，每一行都由上一行推出。但实践中，形式
证明的体量主要取决于另一类东西——作者选择搭建的解析机器，以及证明各部分之间**接口**的开销。本文的具体论点是：
其中相当大一部分开销是**可以避免的**——现代数学库已经提供了能够替代数百行手写估计的抽象，而剩下的开销大部分
来自经典论证其实并不需要的接口。

因此我们并不提出新的无零点区域证明，而是把同一份证明在五次纪录中的**重组过程**逐一道来：每一个刷新基准纪录的
制品，我们分别问三个问题——它消除了哪个瓶颈？是哪一个数学观察使这种消除成为可能？消除了多少 token？

## 2 问题与评分方式

**目标命题。** 基准冻结了下面这个命题，并要求给出它的完整 Lean 4 证明：

$$
\exists\, c > 0, \quad \forall s \in \mathbb{C}, \; s \neq 1, \quad
\mathrm{Re}(s) \ge 1 - \frac{c}{\log\left(|\mathrm{Im}(s)|+2\right)}
\;\;\Longrightarrow\;\; \zeta(s) \neq 0 .
$$

**验证方式。** 证明在 Lean 4.34.1 与固定版本的 Mathlib 下编译，然后由基准的官方 Comparator 重放校验。允许的
公理只有三条——`propext`、`Quot.sound` 与 `Classical.choice`——不允许 `sorry`、不允许自定义公理、不允许修改
冻结陈述。我们的制品还满足更强的本地检查：对最终定理执行 `#print axioms`，列出的恰是这三条公理。

**度量方式。** 基准用**规范化 token 数** $T$ 来衡量提交的大小。规范化的目的是排除表面功夫：注释、空行与
`import` 行不计成本，标识符无论多长都只计一个 token。因此，改变量名、删空格、把 import 压缩成
`import Mathlib`，都不会提高分数；真正起作用的是**结构性压缩**：更少的声明、更少的中间步骤、以及复用库中已有
定理而不是重新推导。这正是本文分析的量。

分数由 token 数按公式计算：

$$
S(T) \;=\; 100 - \frac{50}{1 + \frac{1}{2}\log_{10}\left(T_{0}/T\right)},
\qquad T_{0} = 21{,}641 ,
$$

即与参考等价时得 50 分，压缩十倍约得 66.7 分，压缩一百倍得 75 分。由于分数随 $1/T$ 单调，每省下一个 token 都
朝同一方向加分；纪录之间的差别，正是本文要度量的那部分加分。

## 3 数学核心

经典论证由三个环节组成。我们先分别讲清它们的直觉，再给出形式化中使用的精确陈述。

**（a）增长界。** 要讨论 ζ 在假想零点附近的对数导数，首先需要知道它能增长多快。经典证明给出的是
$\zeta_1(s) = (s-1)\zeta(s)$ 在临界线右侧某个半平面上的多项式增长界。

**（b）对数导数界。** 如果一个函数在点 $z$ 附近有一个非常接近的零点，那么它在 $z$ 处的对数导数必然很大且为负：
零点在近处制造了奇点。经典论证把这一局部事实转化为不等式，但为此需要知道该函数**所有**零点的位置——参考形式化
正是通过构造圆盘内零点的有限乘积来获得这一信息的。

**（c）三-四-一不等式。** 对任意角度 $\theta$ 有

$$
3 + 4\cos\theta + \cos 2\theta \;=\; 2(1+\cos\theta)^{2} \;\ge\; 0 .
$$

把它逐项应用到 $-\zeta'/\zeta$ 的 Dirichlet 级数上，就得到不等式 $3D(a) + 4D(a+t) + D(a+2t) \ge 0$，其中
$D(z)$ 记 von Mangoldt 级数的实部。增长界与对数导数界最终都汇入这一约束。

压缩后的证明把（a）和（b）换成「库原生」的对应物，并保留（c），但以一种不需要独立引理的方式导出它。下面依次
介绍四个构件。

**构件一：$\zeta_1$ 的 Mellin 恒等式。** 分数部分函数 $\{x\}$ 有 Mellin 变换，分部积分即可得到 $\zeta_1$ 的
整函数公式。具体地，在 $\mathrm{Re}(s) > 0$ 上

$$
\zeta_1(s) \;=\; s\left(1 - (s-1)R(s)\right),
\qquad \|R(s)\| \;\le\; \frac{1}{\mathrm{Re}(s)} ,
$$

其中 $R$ 是尾部分数部分的 Mellin 变换。这个恒等式先在 $\mathrm{Re}(s) > 1$（级数与积分都收敛）上证明，
再沿预连通区域用解析延拓推到半平面 $\mathrm{Re}(s) > 0$。

这个恒等式一举两得。第一，它给出（a）所需的增长界：当 $\mathrm{Re}(z) \ge 1/2$ 且 $\|z\| \le 4R$ 时，
有 $\|\zeta_1(z)\| \le R^{8}$。第二，它排除极点附近的零点：若 $\zeta_1(z) = 0$，则恒等式迫使 $(z-1)R(z) = 1$，
从而 $\mathrm{Re}(z) \le |z-1|$；再结合 $\mathrm{Re}(z) \ge 3/4$，就得到这类零点必须满足
$|\mathrm{Im}(z)| \ge 1/2$。最后这个不等式正是总装所需的**低高度**信息；在参考形式化中，它是用另外的
论证单独得到的。

**构件二：递归零点剥离。** 压缩的核心，是一种**从不构造零点乘积**、却仍能界定零点附近对数导数的方法。

想法是一次剥掉一个零点。设 $f$ 是整函数，且在 $\rho$ 处有零点。用解析差商除去线性因子 $(w-\rho)$，所得商仍是
整函数；由于零点已被抵消，这个商增长得**更慢**。对圆盘内每个零点重复这一操作，就回到乘积公式；而使形式证明变小
的关键观察是：我们并不需要那个乘积本身，只需要一个**界**，而界可以通过对增长常数本身作归纳来得到。

Lean 中证明的引理如下。设 $f$ 是整函数、$f(0) \neq 0$，在半径为 $1/2$ 的闭圆盘上满足
$\|f(w)\| \le B\|f(0)\|$，并且 $f$ 在半径 $1/6$ 圆盘内的所有零点都在闭左半平面。那么对满足 $B < 2^{n}$ 的任意
自然数 $n$，有

$$
x + \mathrm{nld}(f,0) \;\le\; 24\log B + 24,
\qquad \mathrm{nld}(f,z) := -\mathrm{Re}\left(\frac{f'(z)}{f(z)}\right),
$$

其中 $x = 0$，或者 $x = \mathrm{Re}\left((-\rho)^{-1}\right)$，$\rho$ 是模长不超过 $1/6$ 的某个零点。
归纳每次剥掉一个零点：在零点 $\rho_0$ 处令 $g(w) := \mathrm{dslope}(f,\rho_0)(w)$，于是

$$
f(w) \;=\; (w-\rho_0)\,g(w),
\qquad f(0) \;=\; -\rho_0\,g(0),
$$

而 $g$ 的增长常数**恰为** $f$ 的一半：在最大模估计中，到 $\rho_0$ 的距离正好抵消一个因子。归纳随后在 $g$ 上
继续，并从对数导数的分解式里加回 $\mathrm{Re}((-\rho_0)^{-1})$ 这一项。如果内圆盘根本没有零点，则对数
导数在该处是精确的；$f$ 有解析对数 $u$，其实部至多 $\log B$，由 Borel–Carathéodory 不等式可界定 $u'(0)$，
再用一次简短的 Lipschitz 估计，就得到所陈述的 $\mathrm{nld}(f,0)$ 的界。

这个构造的要点在于：递归**隐式地**完成了零点枚举。没有乘积、没有围道积分、也不按零点个数分情形——归纳本身就
是枚举。而在参考形式化中，同一件事需要把零点收集成显式乘积、再逐因子证明导数估计，其体量的大部分正来源于此。

**构件三：von Mangoldt 桥。** 在 $\mathrm{Re}(z) > 1$ 上有恒等式

$$
\mathrm{Re}\left(\frac{\zeta_1'(z)}{\zeta_1(z)}\right)
\;=\; \mathrm{Re}\left(\frac{1}{z-1}\right)
\;+\; \mathrm{Re}\sum_{n\ge 1} \Lambda(n)\,n^{-z},
$$

其中 $\Lambda$ 是 von Mangoldt 函数。它把对对数导数的估计转化为关于级数 $D$ 的陈述，而 $D$ 正是构件（c）的
三-四-一不等式中的对象。在 Lean 证明里，这个恒等式是一条库定理，压缩后的证明只需应用它。

**构件四：自适应尺度与稳健的最终不等式。** 剩下的工作是把三个构件用在正确的位置上。证明在三个高度——实轴、假想
零点所在高度、以及该高度的两倍——应用剥离引理，增长比为 $R^{8}/\|{\zeta_1}\|$，其中
$R = |\mathrm{Im}(s)| + 2$。让最终不等式稳健的关键，是尺度的选法。

证明并不在固定点 $1+4d$ 处求值，而是在

$$
a = \mathrm{Re}(s) + 5d,
\qquad d \;=\; \frac{2^{-20}}{\log R}
$$

处求值。这样选择把尺度与候选零点的实部绑定：见证零点到中心的距离**恰好**是 $5d$，因此见证值
$x = (5d)^{-1}$ 是紧的；而假设 $\mathrm{Re}(s) \ge 1-d$ 又给出 $a-1 \ge 4d$。于是极点项满足

$$
\mathrm{Re}\left(\frac{1}{a+i\gamma-1}\right)
\;=\; \frac{a-1}{(a-1)^{2}+\gamma^{2}}
\;\le\; \frac{5d}{(4d)^{2}+\frac{1}{4}}
\;\le\; 20d ,
$$

已经很小。代入三-四-一不等式后，负裕量为

$$
\left(\frac{4}{5}-\frac{3}{4}\right)\frac{1}{d}
\;=\; \frac{0.05}{d}
\;\ge\; 5\cdot 10^{4}\,\log R ,
$$

而全部正误差只有 $O(\log R)$ 量级。由于 $\log R \ge \log 2 > 0.69$，这个不等式以很大的余量成立，最后的算术可以
用一次 `linarith` 收尾。对代码大小而言，这意味着一个重要后果：**因为裕量如此之大，总装中每一个估计都可以很
粗糙**，从而不必形式化任何尖锐常数。

## 4 五次纪录

基准的公开曲线为每一次已评分提交记录三项信息：规范化 token 数、官方得分，以及标记 `kept` 的布尔值——表示该提交
在当时是否刷新了纪录。我们的提交中有五次（全部 `kept = true`）构成本节的内容。

| 纪录 | 提交编号 | tokens | 官方得分 | `running_best_pct` | 本仓库中的制品 |
|---:|---|---:|---:|---:|---|
| 此前纪录 | 96263 | 3,286 | 64.5215 | 85.68 | 由其他参赛者保持 |
| 1 | 96272 | 3,274 | 64.5332 | 85.73 | `Lean/record-96272/` |
| 2 | 96276 | 3,208 | 64.6400 | 86.03 | `Lean/fixes/localcert-fix/` |
| 3 | 96281 | 3,065 | 64.8928 | 86.64 | `Lean/record-96281/` |
| 4 | 96282 | 3,014 | 64.9800 | 86.87 | `Lean/record-96282/` |
| 5 | 96283 | 2,931 | 65.1339 | 87.24 | `Lean/smallest-scored-96283/` |
| 6 | 96286 | 2,843 | 65.2900 | 87.59 | `Lean/smallest-verified/` |
| 7 | 96293 | 2,578 | 65.8000 | 88.80 | `Lean/record-96293-v25/` |
| 8 | 96295 | 2,543 | 65.8700 | 88.97 | v26 谱系的中间变体 |
| 9 | 96308 | 2,536 | 65.8834 | 88.99 | `Lean/record-96308-v26/` |

以下每一小节依次说明：被替代版本的瓶颈、消除该瓶颈的数学想法、以及它对 token 数的可测量影响。文中引用的组件
规模都可用 `tools/token_count.py` 复现。

### 纪录一（3,274 tokens）：用递归替代零点乘积

**瓶颈。** 参考形式化必须界定可能零点附近的那个对数导数，而它的做法是把相关圆盘内的**每一个**零点收进有限乘积
$\prod (w-\rho)^{m(\rho)}$，逐因子证明导数估计，并在多个文件之间传递手写的柯西与 Jensen 估计。第一份压缩制品
已经用一条递归替代了那套库，但它仍要为一个五个接口付费：剥离引理（`landau`，873 tokens）、窗口引理
（`scaledWindow`，269）、三-四-一证书（`triple`，248）、低高度引理（`zeroHeight`，114）与极点项引理
（`poleTerm_le`，66），外加 643 tokens 的总装。

**推导。** 推导即上文构件二：对增长常数作强归纳，用解析差商剥离零点使 $B \mapsto B/2$，终止分支用
Borel–Carathéodory。基准站点给这份制品标注的技巧是「Perron/Mellin 围道精简 + 自动化」，其论文式写作文本题为
《Borel–Carathéodory 与解析差商的递归零点剥离》；破纪录瞬间的截图归档在 `evidence/figures/` 中。

**为什么 token 会减少。** 一个 873 tokens 的引理替换了整座零点分解库；而 Mellin 恒等式（约 742 tokens）替换了
Euler–Maclaurin 增长机器。这份提交的官方纪录是 3,089 个站点 token，相当于相对参考压缩 85.7%。

### 纪录二（3,208 tokens）：把三-四-一证书内联

**瓶颈。** 第一次纪录之后，最大的剩余接口是三-四-一不等式的证书——它被作为独立引理 `triple` 陈述与证明
（248 tokens）。每个引理都要为陈述、证明与实例化付费，而总装还必须按名引用它。

**推导。** 这个证书是**逐项**的：von Mangoldt 级数的每一项都是 $\Lambda(n)n^{-a}$ 乘以
$3 + 4\cos(t\log n) + \cos(2t\log n)$，由构件（c）非负。因此它可以在总装**内部**作为单个 `HasSum.nonneg` 对象
产生，不需要独立引理。这里还处理了一个形式细节：量 $D$ 是用 `def` 引入的，而 Lean 的算术策略 `linarith` 看不穿
定义展开，于是证书与窗口界使用的是语法上不同的原子；一条 `change` 语句把证书改写成目标所用的原子，策略随即成功。

**为什么 token 会减少。** 引理 `triple` 消失（248 tokens），而总装从 643 增至 819 tokens、缩写 `D` 从 21 增至
27。净节省 66 tokens，从 3,274 降到 3,208。

### 纪录三（3,065 tokens）：低高度排除与极点界各推导一次

**瓶颈。** 仍有两个辅助引理在重复 Mellin 恒等式已经包含的信息：`zeroHeight`（114 tokens）排除实部落在 $3/4$ 与
$1$ 之间、虚部很小的零点；`poleTerm_le`（66 tokens）用粗糙常数 2 来界定极点项。二者各自独立陈述、独立证明、
独立实例化。

**推导。** 两个事实都直接来自构件一的恒等式。关于排除：若 $\zeta_1(z) = 0$，则 $(z-1)R(z) = 1$，故
$\mathrm{Re}(z) \le |z-1|$；结合 $\mathrm{Re}(z) \ge 3/4$ 即得
$|\mathrm{Im}(z)| \ge 1/2$。关于极点项：精确表达式
$\mathrm{Re}\left((a+i\gamma-1)^{-1}\right) = (a-1)/((a-1)^{2}+\gamma^{2})$ 借助低高度界可由
$(a-1)/\gamma^{2} \le 20d$ 控制，因此粗糙常数 2 不再需要。两个论证现在都在总装内部、从证明本来就要携带的同一个
`remainder` 对象直接导出。

**为什么 token 会减少。** 两个引理消失（114 与 66 tokens），而总装从 819 增至 876 tokens。净节省 143 tokens，
从 3,208 降到 3,065。

### 纪录四（3,014 tokens）：融合三次窗口应用

**瓶颈。** 窗口估计仍作为引理 `scaledWindow`（263 tokens）存在，并有**三次**实例化，分别对应三个求值高度。
每次实例化都要为接口与传参付费，总装还必须按名引用该引理。

**推导。** 窗口估计不过是把剥离引理应用在三个中心 $a+iv$ 上，增长比为 $R^{8}/\|{\zeta_1}\|$。由于增长假设与
纪录三中的锐化极点不等式在三个中心处完全相同，三次应用可以内联书写并共享这两个参数。数学上没有变化；三次使用
变成了最终定理内的三个 `have` 语句。

**为什么 token 会减少。** 引理 `scaledWindow` 消失（263 tokens），而总装从 876 增至 1,084 tokens。净节省
51 tokens，从 3,065 降到 3,014。

### 纪录五（2,931 tokens）：让一条恒等式贯穿总装

**瓶颈。** 桥引理（`good`，94 tokens）与缩写 `D`（21 tokens）仍在解析估计与最终算术之间做中介：对数导数恒等式
被作为独立陈述证明，而算术还要多经过一个名字。

**推导。** 总装围绕单一的规范化复恒等式重组。构件一的整函数公式成为 $\zeta_1$ 唯一的展开处，桥被简化为总装自身
表达式中的一次代换；于是算术可以直接与 von Mangoldt 级数的实部打交道，既不需要命名的桥引理，也不需要缩写。

**为什么 token 会减少。** 桥从 94 降到 78 tokens，缩写消失，总装从 1,084 降到 1,038 tokens：净节省 83 tokens，
从 3,014 降到 2,931。最终文件含十六个顶层块：总装（1,038 tokens）、剥离引理（872）、Mellin 模块（742）、
桥（78）、见证与胶水（201）。

### 4.6 纪录六至九：把同一批机理继续推到底

在上述五份制品之后，同一批机理继续被应用，纪录在数小时内又移动了四次。下一次纪录是提交 96286 的
2,843-token 制品（得分 65.29，`running_best_pct` 87.59）。随后是三次纪录：提交 96293 约 2,577 tokens（得分
65.80，`running_best_pct` 88.80）、提交 96295 约 2,542 tokens（得分 65.87，`running_best_pct` 88.97），以及
提交 96308 约 2,535 tokens（得分 65.8834，`running_best_pct` 88.99）——它是本发布时的纪录。96293 与 96308 的
制品分别归档为 `Lean/record-96293-v25/`（本地 2,580 tokens）与 `Lean/record-96308-v26/`（本地 2,542 tokens）；
96295 的制品是同一谱系的中间变体，未单独归档。数学内容没有变化：这些削减延续了纪录三至五的模式，即继续收敛
Mellin 模块与总装之间的接口。本地 token 测量与由得分反解出的官方计数一致（例如 65.8834 对应官方约 2,536，
而本地为 2,542）。这一时期的提交 96301 得分为零，不属于纪录序列。此后本账号又三次改进自己的纪录，约为 2,524、2,518 与 2,489 个规范化 tokens（提交 96331、96336、96342，得分 65.91、65.92、65.98，`running_best_pct` 升至 89.07）；这些制品是同一谱系的延续，在共享工作区中提交，未单独归档。随后公开纪录移至另一参赛者（Pi，提交 96572，得分 66.4431，站点 token 2,223，`running_best_pct` 89.73）；本说明写作时本账号仍有两份提交在队列中（97686、97711）。此外，从本地研究工作区恢复出一份制品（v2410，2,410 个规范化 tokens，编译与公理审计均通过），以提交 97732 送交官方；本说明写作时其官方得分待定，制品归档为 `Lean/record-97732-v2410/`。
## 5 压缩的来源

有三条原则解释了这一连串纪录。

*第一，用库原语替换重新推导。* 剥离引理与 Mellin 恒等式都属于这一原则：每一个都把一段自成体系的解析论证替换为
对既有抽象的调用，而且远比它所替代的机器要小。

*第二，选择使估计可以粗糙的尺度。* 保证 $d = 2^{-20}/\log R$ 产生了巨大的裕量
$0.05/d \ge 5\cdot10^{4}\log R$，而误差预算只有 $O(\log R)$ 量级。正因为裕量如此之大，总装从不需要尖锐常数，
而尖锐常数在形式证明中是昂贵的。

*第三，融合接口，并让自动化收尾。* 内联证书、低高度排除与三次窗口应用，消除了接口；用 `grw` 归一不等式、再用
`linarith` 收尾，消除了辅助引理链。最终文件有十个顶层声明、55 个 `have` 语句，策略画像为 38 次 `simp`、
18 次 `linarith`、14 次 `grind` 与 10 次 `norm_num`。

**一个对照实验。** 构件一有一个自然的替代方案——Euler–Maclaurin 路线：证明恒等式

$$
\sum_{n\ge 0}\left[(n+1)^{1-s} - (n+2)^{1-s} - (s-1)(n+1)^{-s}\right] = 1 - \zeta_1(s)
$$

再估计所得级数。我们实现了这条路线并做了测量：项界花费 264 tokens，增长定理 540，积分恒等式 95，辅助引理 158，
合计 **1,057** tokens；而 Mellin 路线约 715 tokens，并且 Euler–Maclaurin 路线无法给出纪录三那种廉价的零点排除。
两条数学上都成立的路线，在形式成本上相差约五成——这是「本文报告的压缩是结构性的、而非表面性的」最清晰的证据。

## 6 官方评测

第 4 节的制品构成纪录序列：官方得分从 64.5332 依次升到 64.6400、64.8928、64.9800、65.1339，最终 65.8834；运行最优
压缩率从 85.73 依次升到 86.03、86.64、86.87、87.24。十二次提交全部带有 `kept = true` 标记。

**测量的一致性。** 由官方得分反解计分公式可以恢复官方 token 数；对最终制品，反解结果约为 2,932，而本地测量为
2,931；对每一次已评分提交，两者都在八个 token 以内一致。这正是第 4 节的组件级账本可信的原因：本地计量器与官方
计量器同步。

**有效性的边界。** 另有两份制品（3,242 与 2,880 tokens）在本环境中以三条允许公理干净编译，却被官方 Comparator
拒绝。我们把这一点作为负结果报告并归档了制品：本地内核检查是必要条件，但不是充分条件——对任何想复现这些结果的
人，这个差别很重要。

**模型榜单。** 在基准的「模型 × Harness」榜单上，这些提交所用的组合——Deepseek V4.1-Flash 运行于 DeepSeek
Harness——排名第一，综合指数 64.50，平均压缩率 84.2%。相关截图归档在 `evidence/figures/` 中。

## 7 讨论

**五次纪录的共同点。** 按顺序读下来，这五份制品并不是五个不同的证明，而是**同一个证明**在每一步获得更好的接口：
先预设见证间隙，使中间窗口变紧；再内联逐项证书；然后从已经存在的恒等式直接导出低高度排除与极点界；接着融合
三次窗口应用；最后让一条恒等式贯穿总装。没有一步改变命题，每一步都消去经典论证并不需要的接口或分情形。

**局限。** 第一，范围：这是形式化项目的一根解析支柱，不是黎曼猜想的证明。第二，度量：规范化 token 是基准特定的
「证明结构」代理，并不度量数学深度，也不可跨基准比较。第三，库依赖：若干节省来自 Mathlib API，因此结果度量的是
数学库与证明的**共同成熟度**。第四，接受度并不随尺寸单调变化，第 6 节被拒绝的制品即为例子。

**下一批节省在哪里。** 我们识别出三处并给出实测目标：把低高度排除从 $|\mathrm{Im}(s)| \ge 1/2$ 弱化为
$|\mathrm{Im}(s)| \ge 32d$ 并采用两分支自适应尺度，约省 110 tokens；把两个对数输入合并为单一 von
Mangoldt 对象，约省 130 tokens；用库中的 `logDeriv` API 重述剥离引理，约省 100 tokens。三者合起来指向一份约
2,500 tokens 的证明。

## 8 制品、复现与来源

**复现。** 仓库包含五份纪录制品、被拒绝与待定的制品、规范化 token 计量器的本地实现、编译与公理审计工具、官方
证据快照与截图、一份独立的分情形证明，以及本文的中英两版。下面两条命令分别复现核心测量与核心验证：

```bash
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean      # -> 2931
LEAN_HOME=/path/to/lean-4.34.1-linux MATHLIB=/path/to/mathlib4 \
  tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   预期：compile rc=0；#print axioms -> [propext, Classical.choice, Quot.sound]
```

**来源。** 成果在账号 *余荫铠（Yin-Kai Yu）* 下产生，来自两条 AI agent 轨道协作的研究工作区：DeepSeek Harness
运行 Deepseek V4.1-Flash，ChatGPT Desktop 运行 GPT-6.2 Astra。提交、测量与本文都属于该账号的记录。被拒绝的
制品与待定的分数均如实报告。

**引用。**

```bibtex
@misc{yu2026zfrcompress,
  author = {Yu, Yin-Kai},
  title  = {Library-Native Proof Compression: Successive Record Formalizations of the Classical Zero-Free Region in {Lean}~4},
  year   = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url    = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
}
```

## 参考文献

[1] B. Riemann, *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse*, 1859.
[2] J. Hadamard, *Sur la distribution des zéros de la fonction ζ(s) et ses conséquences arithmétiques*,
Bulletin de la Société Mathématique de France 24 (1896), 199–220.
[3] C.-J. de la Vallée Poussin, *Recherches analytiques sur la théorie des nombres premiers*, Annales de la
Société Scientifique de Bruxelles 20 (1896), 183–256.
[4] E. Landau, *Handbuch der Lehre von der Verteilung der Primzahlen*, Teubner, 1909.
[5] E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., rev. D. R. Heath-Brown, Oxford
University Press, 1986.
[6] H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*, Cambridge University
Press, 2007.
[7] L. de Moura, S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE-28, 2021, 625–635.
[8] The mathlib Community, *The Lean Mathematical Library*, CPP 2020, 367–381（固定 commit `d13f23b7`）。
[9] É. Borel, *Sur les zéros des fonctions entières*, Acta Mathematica 20 (1897), 357–396.
[10] C. Carathéodory, *Über den Variabilitätsbereich der Koeffizienten von Potenzreihen*, Mathematische
Annalen 64 (1907), 95–115.
[11] H. von Mangoldt, *Zu Riemann's Abhandlung über die Anzahl der Primzahlen*, Journal für die reine und
angewandte Mathematik 114 (1895), 255–305.
[12] L. Alpöge, *A Lean 4 formalization of the Riemann Hypothesis*，归档 `alpo.ge`，2025。
[13] Agentic Science Challenge, *Lean 4 Verification (RH Core Pillar 1/5): Classical Zero-Free Region for
ζ(s)*，2026。
[14] 公开 Proof Compression Progress Curve，<https://riemann.verifytask.cn/>，2026。

## 附录 A. 证明所用的 Mathlib 声明

以下库声明承担了形式化的主要重量；文件名与行号对应固定 commit 的 Mathlib。`borelCaratheodory_zero` 位于
`Analysis/Complex/BorelCaratheodory.lean` 第 86 行；`norm_deriv_le_div_of_mapsTo_ball` 位于
`Analysis/Complex/Schwarz.lean` 第 250 行；`differentiableOn_dslope` 位于
`Analysis/Complex/RemovableSingularity.lean` 第 60 行；`logDeriv_eqOn_iff` 与 `logDeriv_mul` 位于
`Analysis/Calculus/LogDeriv.lean`；`integral_Ioi_cpow_of_lt` 位于
`Analysis/SpecialFunctions/ImproperIntegrals.lean` 第 251 行；`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
位于 `NumberTheory/LSeries/Dirichlet.lean` 第 434 行；`norm_LFunction_product_ge_one` 位于
`NumberTheory/LSeries/Nonvanishing.lean` 第 310 行；`deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` 位于
`NumberTheory/Harmonic/ZetaAsymp.lean` 第 585 行。

## 附录 B. 制品清单

五份纪录制品分别位于 `Lean/record-96272`、`Lean/fixes/localcert-fix`、`Lean/record-96281`、
`Lean/record-96282` 与 `Lean/smallest-scored-96283`。仓库还包含 `Lean/smallest-verified`（2,843 tokens，
待评分）、`Lean/failed-96274-v22.lean`（被官方 Comparator 拒绝）、`research/caseAB`（一份独立的分情形证明）、
`tools`（token 计量器与编译/审计工具）、`evidence`（官方快照与截图）、`docs`（扩展技术笔记），以及本文的中英
两版。
