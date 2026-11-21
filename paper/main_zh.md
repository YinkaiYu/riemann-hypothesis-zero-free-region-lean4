# 库原生证明压缩：黎曼 ζ(s) 经典无零点区域在 Lean 4 中的逐次纪录形式化

**余荫铠（Yin-Kai Yu）** — DeepSeek Harness × ChatGPT Desktop 协作研究轨道

*制品发布 v1.0 · 2026-11-22 · <https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>*

## 摘要

黎曼 ζ 函数的经典无零点区域只需教科书几页篇幅即可证明，但其参考 Lean 4 形式化占 21 个文件、$21{,}641$
个规范化 tokens。本文报告同一命题的五次逐次破纪录压缩，最终装进**单文件 $2{,}931$ tokens**，并以
（B）被消除的瓶颈、（M）引入的核心推导、（C）实测 token 增量三段式分析每一步。最终形式为：存在常数
$c>0$ 使 $\zeta(s)\neq 0$ 于 $\mathrm{Re}(s)\ge 1-c/\log(|\mathrm{Im}(s)|+2)$，全部包装为 8 个声明：
$\zeta_1=(s-1)\zeta$ 的 Mellin 整函数公式、由解析差商（`dslope`）与 Borel–Carathéodory 构造的递归零点
剥离引理、通往 $3+4\cos\theta+\cos 2\theta\ge 0$ 的 von Mangoldt 桥，以及自适应尺度
$a=\mathrm{Re}(s)+5d$、$d=2^{-20}/\log R$ 的总装。官方得分依次为
$64.5332\to 64.6400\to 64.8928\to 64.9800\to 65.1339$，曲线标记 `kept=true`；消融表明自然的
Euler–Maclaurin 增长路线多花约 50% 的 token。

**关键词**：形式化分析 · Lean 4 · Mathlib · 证明压缩 · 无零点区域 · 解析差商 · Borel–Carathéodory

## 1 引言

解析数论的形式证明之所以大，主要是因为它**重新推导**现代数学库已提供的机器——零点分解、围道估计、
Euler–Maclaurin 展开。本文所用基准把这量显式化：命题冻结、环境固定（Lean 4.34.1 + Mathlib、重放式
Comparator、允许公理 $\{\texttt{propext},\texttt{Quot.sound},\texttt{Classical.choice}\}$），得分只取决于
规范化 Lean token 数 $T$（注释、空白与 `import` 行不计；标识符长度不计）。我们取参考闭包为
$T_0=21{,}641$ tokens（21 个文件）的经典 de la Vallée Poussin 无零点区域，逐次压缩。本文的主题是每一步的
数学：被替换的机器为何昂贵、用什么替换、替换的代价是多少。

## 2 设定

目标（冻结）：

$$
\exists\,c>0:\quad \forall s\in\mathbb{C},\ s\neq 1,\quad
\mathrm{Re}(s)\ \ge\ 1-\frac{c}{\log\left(|\mathrm{Im}(s)|+2\right)}
\ \Longrightarrow\ \zeta(s)\neq 0 .
$$

度量：规范化 token 数 $T$，基线 $T_0=21{,}641$，得分

$$
S(T)\;=\;100-\frac{50}{1+\frac{1}{2}\log_{10}\left(T_0/T\right)} .
$$

本地计量器复现官方计数至 $\pm 8$ tokens，故下文账本与官方数可比。

## 3 数学核心

记 $\zeta_1(s)=(s-1)\zeta(s)$（整函数）。

**Mellin 整函数公式。** 在 $\mathrm{Re}(s)>0$ 上

$$
\zeta_1(s)\;=\;s\left(1-(s-1)R(s)\right),\qquad
\lVert R(s)\rVert\ \le\ \frac{1}{\mathrm{Re}(s)} ,
$$

其中 $R$ 为分数部分尾项的 Mellin 变换。它给出（i）多项式增长界
$\lVert z\rVert\le 4R\Rightarrow\lVert\zeta_1(z)\rVert\le R^8$（$\mathrm{Re}(z)\ge\frac{1}{2}$）；
（ii）$s=1$ 附近的零点排除：若 $\zeta_1(z)=0$ 则 $(z-1)R(z)=1$，故
$\mathrm{Re}(z)\le|z-1|$，于是 $\mathrm{Re}(z)\ge\frac{3}{4}$ 的零点满足
$|\mathrm{Im}(z)|\ge\frac{1}{2}$。

**递归零点剥离。** 令 $\mathrm{nld}(f,z):=-\mathrm{Re}\left(f'(z)/f(z)\right)$。设 $f$ 整、
$f(0)\neq 0$、在 $\overline{B}(0,\frac{1}{2})$ 上满足 $\lVert f(w)\rVert\le B\lVert f(0)\rVert$、
且 $\overline{B}(0,\frac{1}{6})$ 内零点均在闭左半平面，则对满足 $B<2^n$ 的 $n$ 强归纳可证

$$
x+\mathrm{nld}(f,0)\ \le\ 24\log B+24 ,
$$

其中 $x=0$，或 $x=\mathrm{Re}\left((-\rho)^{-1}\right)$（$\rho\in\overline{B}(0,\frac{1}{6})$ 为某零点）。
剥离步为

$$
g(w):=\mathrm{dslope}(f,\rho_0)(w),\qquad
f(w)=(w-\rho_0)\,g(w),\qquad f(0)=-\rho_0\,g(0),
$$

且 $g$ 的增长常数恰为 $f$ 的一半，$B\mapsto B/2$；终止分支（内盘无零点）用解析对数的
Borel–Carathéodory 估计。

**桥与总装。** 在 $\mathrm{Re}(z)>1$ 上
$\mathrm{Re}\left(\zeta_1'/\zeta_1\right)=\mathrm{Re}\left((z-1)^{-1}\right)+\mathrm{Re}\sum\Lambda(n)n^{-z}$，
把剥离估计变成经典不等式 $3D(a)+4D(a+t)+D(a+2t)\ge 0$、$D(z)=\mathrm{Re}\sum\Lambda(n)n^{-z}$
（等价于 $3+4\cos\theta+\cos2\theta\ge 0$）。取
$R=|\mathrm{Im}(s)|+2$、$d=2^{-20}/\log R$、自适应尺度 $a:=\mathrm{Re}(s)+5d$：见证零点恰距中心 $5d$，
故 $x=(5d)^{-1}$ 是紧的；$\mathrm{Re}(s)\ge 1-d$ 给出 $a-1\ge 4d$，并且

$$
\mathrm{Re}\left((a+i\gamma-1)^{-1}\right)\;=\;\frac{a-1}{(a-1)^2+\gamma^2}
\;\le\;\frac{5d}{(4d)^2+\frac{1}{4}}\;\le\;20d .
$$

于是 3–4–1 组合的负裕量为

$$
\left(\frac{4}{5}-\frac{3}{4}\right)\frac{1}{d}\;=\;\frac{0.05}{d}\;\ge\;5\cdot 10^{4}\log R ,
$$

而误差预算为 $O(\log R)$；所有估计都可以粗糙，一步 `linarith` 即闭合。

## 4 五次纪录

| # | 提交 | tokens | 官方得分 | `running_best_pct` | 制品 |
|---:|---|---:|---:|---:|---|
| — | 96263 | 3,286 | 64.5215 | 85.68 | 原纪录保持者 |
| 1 | 96272 | 3,274 | 64.5332 | 85.73 | `Lean/record-96272/` |
| 2 | 96276 | 3,208 | 64.6400 | 86.03 | `Lean/fixes/localcert-fix/` |
| 3 | 96281 | 3,065 | 64.8928 | 86.64 | `Lean/record-96281/` |
| 4 | 96282 | 3,014 | 64.9800 | 86.87 | `Lean/record-96282/` |
| 5 | 96283 | **2,931** | **65.1339** | **87.24** | `Lean/smallest-scored-96283/` |

**（B）瓶颈，（M）推导，（C）实测增量。**

**纪录 1。**（B）参考实现把圆盘内**全部**零点收进有限乘积 $\prod(w-\rho)^{m(\rho)}$，逐因子证明求导引理、
跨文件传递手写柯西/Jensen 估计；压缩谱系仍付五个接口（`landau` 873、`scaledWindow` 269、`triple` 248、
`zeroHeight` 114、`poleTerm_le` 66）加 643-token 总装。（M）上文剥离引理以 $B\mapsto B/2$ 的强归纳取代
零点乘积。（C）一个 873-token 引理替换整座零点分解库；Mellin 公式（约 742）替换 Euler–Maclaurin 增长机器。
站点记录：$3{,}089$ site tokens、$-85.7\%$，技巧标签「Perron/Mellin 围道精简 + grind 自动收口」。

**纪录 2。**（B）3–4–1 证书被做成独立引理 `triple`（248）。（M）证书是逐项陈述：von Mangoldt 级数每项
$\Lambda(n)n^{-a}\left(3+4\cos(t\log n)+\cos(2t\log n)\right)\ge 0$，故可在总装内部作为单个
`HasSum.nonneg` 对象产生；`def` 隐藏原子导致的不匹配以 `change` 修复，使证书与窗口界谈论同一原子。
（C）`triple` 消失、总装 $643\to 819$：净 $-66$。

**纪录 3。**（B）`zeroHeight`（114）与 `poleTerm_le`（66）重复了恒等式已含的信息。（M）排除
$\zeta_1(z)=0\Rightarrow\mathrm{Re}(z)\le|z-1|\Rightarrow|\mathrm{Im}(z)|\ge\frac{1}{2}$ 与锐化界
$\mathrm{Re}\left((a+i\gamma-1)^{-1}\right)\le(a-1)/\gamma^2\le 20d$ 都来自同一 `remainder`。
（C）两引理消失、总装 $819\to 876$：净 $-143$。

**纪录 4。**（B）`scaledWindow`（263）在三个高度被实例化，付三次接口成本。（M）三次应用共享增长假设与
锐化极点不等式，故可内联为同一引理的三个 `have` 绑定。（C）`scaledWindow` 消失、总装 $876\to 1{,}084$：
净 $-51$。

**纪录 5。**（B）`good`（94）与缩写 `D`（21）仍在结果与总装之间做中介。（M）总装围绕单一规范化恒等式
$\zeta_1(s)=s\left(1-(s-1)R(s)\right)$ 重组，桥化为代入，算术直接用 von Mangoldt 级数的实部。
（C）`good` $94\to 78$、`D` 消失、总装 $1{,}084\to 1{,}038$：净 $-83$。

## 5 机理与消融

三条原则解释这一序列：（P1）以库原语替换重推导；（P2）选尺度使估计可以粗糙——裕量
$0.05/d\ge 5\cdot10^4\log R$ 使收尾算术稳健；（P3）融合接口并自动化——10 个顶层声明、55 个 `have`，
策略画像 `simp` 38、`linarith` 18、`grind` 14、`norm_num` 10。

**消融。** 增长界的自然 Euler–Maclaurin 路线先证
$\sum_n\left[(n+1)^{1-s}-(n+2)^{1-s}-(s-1)(n+1)^{-s}\right]=1-\zeta_1(s)$ 再估计级数。实测成本：
项界 $264$ + 增长定理 $540$ + 积分恒等式 $95$ + 辅助 $158$ $=1{,}057$ tokens，而 Mellin 约 $715$，
且不提供廉价零点排除。两条数学上都成立的路线在形式成本上差约 50%：压缩是结构性的。

## 6 官方评测

纪录序列即 §4 表；`running_best_pct` 依次 $85.73\to 86.03\to 86.64\to 86.87\to 87.24$。反解计分公式
恢复的 token 数与本地一致（$65.1339\Rightarrow\approx 2{,}932$ vs $2{,}931$），验证账本。另有两份制品
（$3{,}242$ 与 $2{,}880$ tokens）本地干净编译却被官方 Comparator 拒绝，作为有效性边界归档。在基准的
模型 × Harness 榜单上，Deepseek V4.1-Flash / DeepSeek Harness 位列第一（综合指数 $64.50$；平均压缩率
$84.2\%$）；证据图见 `evidence/figures/`。

## 7 讨论与结论

五个制品是同一个构造在逐步获得更好的接口：预设见证间隙；内联逐项证书；从 `remainder` 直接读出低高度排除与
锐化极点界；融合三个窗口；以一条恒等式贯穿总装。没有一步改变命题；每一步都消去经典论证并不需要的接口。
一般启示：**证明体量主要由重复推导与接口开销决定，库原生化重写即压缩。** 局限：单一支柱而非黎曼猜想；
token 是基准特定的结构代理；若干节省属 Mathlib API 节省。通向 $2{,}500$ tokens 的路线：弱化低高度排除到
$|\mathrm{Im}(s)|\ge 32d$ 并采用两分支尺度（约 $-110$）、合并两个对数输入（约 $-130$）、用 `logDeriv`
重述剥离引理（约 $-100$）。

## 8 制品与复现

```bash
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean   # -> 2931
LEAN_HOME=... MATHLIB=... tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   预期：compile rc=0；#print axioms -> [propext, Classical.choice, Quot.sound]
```

**来源。** 成果在账号 *余荫铠（Yin-Kai Yu）* 下产生，来自 DeepSeek Harness / Deepseek V4.1-Flash 与
ChatGPT Desktop / GPT-6.2 Astra 两条 AI agent 轨道的协作；被拒制品与待定分数如实报告。

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

[1] B. Riemann, *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse*, 1859. ·
[2] J. Hadamard, *Sur la distribution des zéros de la fonction ζ(s)*, Bull. SMF 24 (1896) 199–220. ·
[3] C.-J. de la Vallée Poussin, *Recherches analytiques sur la théorie des nombres premiers*, 1896. ·
[4] E. Landau, *Handbuch der Lehre von der Verteilung der Primzahlen*, Teubner, 1909. ·
[5] E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., OUP, 1986. ·
[6] H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I*, CUP, 2007. ·
[7] L. de Moura, S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE-28, 2021. ·
[8] The mathlib Community, *The Lean Mathematical Library*, CPP 2020（mathlib4 commit `d13f23b7`）. ·
[9] É. Borel, *Sur les zéros des fonctions entières*, Acta Math. 20 (1897). ·
[10] C. Carathéodory, *Über den Variabilitätsbereich*, Math. Ann. 64 (1907). ·
[11] H. von Mangoldt, *Zu Riemann's Abhandlung*, J. Reine Angew. Math. 114 (1895). ·
[12] L. Alpöge, *A Lean 4 formalization of the Riemann Hypothesis*（`alpo.ge`），2025. ·
[13] Agentic Science Challenge, *Lean 4 Verification (RH Core Pillar 1/5)*, 2026. ·
[14] 公开 Proof Compression Progress Curve，<https://riemann.verifytask.cn/>，2026.

## 附录 A. 使用的 Mathlib 声明

`borelCaratheodory_zero` (`Analysis/Complex/BorelCaratheodory.lean:86`) ·
`norm_deriv_le_div_of_mapsTo_ball` (`Analysis/Complex/Schwarz.lean:250`) ·
`differentiableOn_dslope` (`Analysis/Complex/RemovableSingularity.lean:60`) ·
`logDeriv_eqOn_iff`、`logDeriv_mul` (`Analysis/Calculus/LogDeriv.lean`) ·
`integral_Ioi_cpow_of_lt` (`Analysis/SpecialFunctions/ImproperIntegrals.lean:251`) ·
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (`NumberTheory/LSeries/Dirichlet.lean:434`) ·
`norm_LFunction_product_ge_one` (`NumberTheory/LSeries/Nonvanishing.lean:310`) ·
`deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` (`NumberTheory/Harmonic/ZetaAsymp.lean:585`).

## 附录 B. 制品清单

`Lean/` 下五个纪录制品（`record-96272`、`fixes/localcert-fix`、`record-96281`、`record-96282`、
`smallest-scored-96283`）；`smallest-verified`（2,843 tokens，待定）；`failed-96274-v22.lean`（被拒）；
`research/caseAB/`；`tools/`；`evidence/`；`docs/`；中英两版论文。
