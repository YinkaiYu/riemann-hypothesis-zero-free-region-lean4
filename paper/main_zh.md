# 为什么它能装进去：2,931-Token 的 Lean 4 黎曼 ζ(s) 经典无零点区域证明的数学结构

**余荫铠（Yin-Kai Yu）**

*DeepSeek Harness × ChatGPT Desktop 协作研究轨道 · 制品发布 v1.0 · 2026-11-22*
<https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>

> **已发表技术。** 本证明的核心装置已在公开基准站点上提炼为技术 `core1_borel_dslope`——
> *Borel–Carathéodory + 差商 (DSlope) 直接零点分解*——其对应提交为 **96283**（本账号）。
> §5 原文复现该技术说明（中英双语），并展开其背后的数学。

---

## 摘要

黎曼 ζ 函数的经典无零点区域是教科书定理，其参考 Lean 4 形式化占 21 个文件、21,641 个规范化 tokens。
本文解释同一命题的一份**单文件 2,931 tokens** 证明背后的数学：该证明在公开证明压缩榜上保持纪录
（官方得分 65.1339，曲线标记 `kept = true`）。压缩不是表面功夫，而是用**结构**替换四处「重新推导」：
（i）`(s−1)ζ(s)` 的 Mellin 整函数公式，同时给出多项式增长界与 `s = 1` 附近两行式的零点排除；
（ii）递归**零点剥离引理**——把零点经 Mathlib 解析差商 `dslope` 分解出来，以减半的增长常数递归，再用
Borel–Carathéodory 收尾——以 872 tokens 的一次归纳替换参考实现中的有限零点乘积与柯西积分；
（iii）von Mangoldt 桥，把增长估计转成经典 3–4–1 不等式；（iv）**自适应尺度** `a = Re s + 5d`、
`d = 2⁻²⁰/log R`，使见证零点恰距中心 `5d`，并消去三处分常数情形。我们给出逐组件的 token 账本、一项
消融（Euler–Maclaurin 路线贵约 50%），以及让最后一步 `linarith` 必然成立的算术裕量。一般性结论：
**解析数论中的形式证明体量主要来自重复推导，库原生化重写即是压缩。**

**关键词**：形式化分析 · 证明压缩 · Lean 4 · Mathlib · 无零点区域 · 解析差商 · Borel–Carathéodory 不等式

---

## 1 引言

一个教科书定理可以是一个很大的形式化制品。经典 de la Vallée Poussin 无零点区域——存在 `c > 0` 使
`Re(s) ≥ 1 − c/log(|Im s|+2)` 时 `ζ(s) ≠ 0`——在 Titchmarsh [5] 或 Montgomery–Vaughan [6] 中数页可证，
但其参考 Lean 4 形式化 [12]（`src/Formalism/ZeroFreeRegion/FinalZFR.lean` 的闭包）为 21 个文件、
74,010 字符、**21,641 个规范化 tokens** [13]。现代基准 [13] 正是度量这一量，因为它是一个**证明暴露了
多少数学结构**的代理指标：注释与标识符命名不计成本，唯有真正的重构才能降低计数。

本文解释：该定理如何从 21,641 压到 **2,931 tokens**（−86.5%）。该证明的官方提交（96283）在公开曲线上
保持纪录（得分 65.1339，`kept = true`，`running_best_pct` 87.24），其提交谱系产生了连续五次纪录刷新。
论文的论点是定量的、结构性的：

> 参考形式化之所以大，是因为它**重新推导**了 Mathlib 已以库形式提供的解析机器——零点分解、围道估计、
> Euler–Maclaurin 展开。把每处重推导替换为相应库原语，并围绕单一自适应尺度重组总装，
> 即可在不削弱命题的前提下把证明压缩一个量级。

---

## 2 设定

冻结命题（Lean 4.34.1 [7]、Mathlib commit `d13f23b7…` [8]、官方重放 Comparator；允许公理
`{propext, Quot.sound, Classical.choice}`）：

```lean
theorem AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0
```

度量是**规范化 token 数** `T`（注释/空白/import 计 0；标识符计 1），基线 `T₀ = 21,641`；得分为
`100 − 50/(1 + 0.5·log₁₀(T₀/T))`。本地计量器在每次已评分提交上与官方计数误差 ≤ 8 tokens（§8.3），
故下文的 token 账本可靠。

---

## 3 数学骨架

记 `ζ₁(s) := (s−1)ζ(s)`（整函数）。经典论证三步：

**（S1）增长界。** 对 `1 < Re z`、`|Im z| ≤ 2R`（`R = |Im s| + 2`），用 `R` 的多项式控制 `z` 附近半径
`1/2` 圆盘上的 `‖ζ₁‖`。

**（S2）对数导数界。** 若 `−Re(f′/f)(0)` 很大且为负（零点靠近 `0`），则 `f` 必须快速增长。定量地
（`x = 0` 或距 `0` 不超过 `1/6` 的见证零点）：

```
x − Re(f′/f)(0) ≤ 24·(log B + 1),      其中 |w| ≤ 1/2 上 ‖f w‖ ≤ B‖f 0‖。
```

**（S3）3–4–1 不等式。** 对 `a > 1` 与一切 `t`：`3D(a) + 4D(a+t) + D(a+2t) ≥ 0`，
`D(z) = Re Σ Λ(n)n^{−z}`，等价于 `3 + 4cos θ + cos 2θ ≥ 0`。

参考实现用 Euler–Maclaurin 展开与柯西积分做（S1）、用有限零点乘积做（S2）。我们改由 Mellin 公式导出
（S1）（§4）、把（S2）实现为递归（§5）、由库恒等式得到（S3）（§6）；最终总装（§6.3）只剩几十行。

---

## 4 增长界与零点排除：一个 Mellin 恒等式

设 `fract` 为分数部分函数，`R(s) = mellin(fract·1_{>1})(−s)`。尾项的 Mellin 变换给出：在 `Re s > 0` 上

```lean
lemma entireFormula (hs : 0 < s.re) : riemannZeta₁ s = s * (1 - (s-1) * remainder s)
lemma mellin_bound (hs : 0 < s.re) : ‖remainder s‖ ≤ 1 / s.re
```

*证明要点。* 在 `Re s > 1` 上把 ζ 的 Mellin 积分在 `1` 处切开并分部积分，分数部分出现，恒等式成立；
两边在预连通区域 `{Re > 0}` 上解析，由恒等定理延拓。◻

两个推论（合计约 715 tokens）：
1. **增长**：`Re z ≥ 1/2`、`‖z‖ ≤ 4R` 时 `‖ζ₁ z‖ ≤ R⁸`（由 `‖remainder‖ ≤ 1/Re z`），即（S1）。
2. **`1` 附近零点排除**：若 `ζ₁(z) = 0` 则 `(z−1)R(z) = 1`，故 `Re z ≤ |z−1|`；结合 `Re z ≥ 3/4`
   得 `|Im z| ≥ 1/2`——正是（S3）在中间求值高度所需的低高度控制。

---

## 5 核心技术：递归零点剥离（872 tokens）

### 5.1 陈述

设 `f : ℂ → ℂ` 整、`f 0 ≠ 0`、在 `|w| ≤ 1/2` 上有单侧增长常数 `B`、所有零点在闭左半平面，且存在
见证零点 `ρ` 满足 `|ρ| ≤ 1/6`、`x ≤ Re((−ρ)⁻¹)`，则

```
x − Re(f′/f)(0) ≤ 24·(log B + 1)。
```

假设恰是应用端能提供的：`f := ζ₁(z + ·)` 整、`f 0 ≠ 0`（因 `Re > 1` 上 ζ 无零点 [8]）、零点集在
`Re = 0` 左侧（因 `Re ≥ 1` 上 ζ 无零点）、见证即假想零点 `s`，距离 `5d`——见 §6.3。

### 5.2 证明

对 `n` 归纳（`B < 2ⁿ`）。

*剥离。* 若内圆盘内存在 `f` 的零点 `ρ`，用解析差商：`f w = (w − ρ)·dslope f ρ w`。因子 `dslope f ρ` 整、
在 `0` 处非零，并在外圆盘上满足 `‖dslope f ρ w‖ ≤ (B/2)‖dslope f ρ 0‖`——因子 `1/2` 正是「到 `ρ` 的距离
与增长半径相消」的收益。对 `dslope f ρ` 递归，再由
`f′/f = (·−ρ)′/(·−ρ) + (dslope f ρ)′/(dslope f ρ)` 加回 `Re(−ρ⁻¹)`。

*收尾。* 若内圆盘无零点，`logDeriv f` 在该处精确；`f` 有解析对数 `g` 且 `Re g ≤ log B`，由
Borel–Carathéodory 不等式 [9,10] 以 `R = 1/2` 界定 `|g′(0)| ≤ 2Re g(0)/R`；再在 `0` 处做一个 Lipschitz
估计，把 `(f′/f)(0) = g′(0)` 转成所述界。

递归**隐式枚举**零点：无乘积公式、无围道积分、无按零点个数的分情形。这正是它替换参考实现零点分解机器
的原因，也是常数 `24`（而非教科书中的 `25`/`26`）可达的原因：见证圆盘 `1/6` 与增长圆盘 `1/2` 取得恰好
让两个分支消耗同一界。

### 5.3 Lean 实现

`dslope` 以定义方式给出分解（`sub_smul_dslope_of_zero`），可微性经 `differentiableOn_dslope` 下降，增长
转移用最大模原理 `norm_le_of_forall_mem_frontier_norm_le`，对数分支用 `logDeriv_eqOn_iff` 与
`borelCaratheodory_zero`。成本：**872 tokens**，无零点辅助引理；有此引理后，整个文件仅 10 个顶层声明。

### 5.4 已发表的技术说明

> **`core1_borel_dslope`——「Borel–Carathéodory 与差商 (DSlope) 直接零点分解」**
> （提交 96283；类别 *复分析 · Mathlib 复用*）。
>
> *中文原文。* 「不再维护原版 21 个文件的手写柯西积分与 Euler–Maclaurin 估计，而是直接借助 Mathlib 的
> `DSlope`（解析差商）剥离假想零点 ρ，配合 `BorelCaratheodory` 定理与 Landau 引理在仅 10 个顶层声明
> （200 行）内闭合 `−(ζ′/ζ).re` 估计；再用 Lean 4 广义不等式改写 `grw` 一步压平 3-4-1 三角放缩链，
> 省去大量中间引理。」
>
> *English.* "Instead of carrying 21 files of hand-rolled Cauchy integral and Euler–Maclaurin estimates,
> this proof factors out a putative zero ρ directly via Mathlib's `DSlope` (analytic divided difference) and
> bounds `−(ζ′/ζ).re` with `BorelCaratheodory` and Landau's lemma in just 10 top-level declarations
> (200 lines). Lean 4's `grw` collapses the 3-4-1 trigonometric bound chain without intermediate helper
> lemmas."
>
> *关键信号*：`BorelCaratheodory`, `differentiableOn_dslope`, `grw`, `ZetaAsymp`。
> *压缩*：21 → 1 文件，token −87.2%。

---

## 6 完成论证

### 6.1 von Mangoldt 桥（78 tokens）

`Re z > 1` 上 `Re(ζ₁′/ζ₁)(z) = Re((z−1)⁻¹) + Re Σ Λ(n)n^{−z}`
（`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`）。它把 §5 对 `ζ₁′/ζ₁` 的界变成 3–4–1 不等式中 `D` 的陈述。

### 6.2 窗口界

在三个高度 `v ∈ {0, Im s, 2·Im s}` 上应用 §5，增长比 `B = R⁸/‖ζ₁(a+iv)‖`：增长假设来自 §4，
零点侧假设来自 §6.1。中间高度的见证即假想零点本身，距离 `a − Re s`。

### 6.3 自适应尺度与算术

取 `R = |Im s| + 2`、`d = 2⁻²⁰/log R`（故 `d ≤ 1/100`），并令 **`a = Re s + 5d`**。于是：

* 见证恰距 `5d`，故 `x = (5d)⁻¹` 是紧的；
* 假设 `1 − d ≤ Re s` 给出 `4d ≤ a − 1`，故实中心极点项 `(a−1)⁻¹ ≤ (4d)⁻¹`；
* §4 的低高度排除给出中间极点项界 `Re((a+i·Im s−1)⁻¹) ≤ 5d/((4d)²+(1/2)²) ≤ 20d`，`2·Im s` 同理。

把三个窗口界按 `3r + 4t + u` 组合，配合 §6.1 与逐点 3–4–1 不等式得到的对数导数证书
`3D(a)+4D(a+it)+D(a+2it) ≥ 0`，以及 Mathlib 的乘积形式（`norm_LFunction_product_ge_one`），得到

```
4/(5d) − 192·(log log R + 20 log 2)  ≤  3/(4d) + 4·20d + 20d + 192·(8 log R + 1)。
```

左端负裕量为 `(4/5 − 3/4)/d = 0.05/d = 0.05·2²⁰·log R ≥ 5·10⁴ log R`，而右端除极点项外仅为 `O(log R)`；
因 `log R ≥ Real.log 2 > 0.69`，一步 `linarith`（配合 `Real.log_le_self` 与 `Real.log_two_lt_d9`）即闭合矛盾。
**破纪录的经济性正在此处**：`d = 2⁻²⁰/log R` 使负裕量极大，因而所有估计都可以很粗糙（极点项粗估为 `20d`！），
这也正是代码能够避开参考实现那些精确但冗长的界的原因。

---

## 7 为什么能破纪录：token 账本

### 7.1 组件预算（2,931 tokens）

| 组件 | tokens | 占比 | 作用 |
|---|---:|---:|---|
| 总装（§6.3） | 1,038 | 35.4 % | 解析数论内容本体 |
| 剥离引理（§5） | 872 | 29.7 % | 替换零点分解 + 围道估计 |
| Mellin 公式（§4） | 742 | 25.3 % | 替换 Euler–Maclaurin 增长机器 |
| von Mangoldt 桥（§6.1） | 78 | 2.7 % | 转为 3–4–1 |
| 见证、Mellin 辅助、前言 | 201 | 6.9 % | 胶水 |

相对 `T₀ = 21,641` 为 **−86.5%**。两个大项（剥离 + Mellin）恰是被消除的两处重推导；二者合计 1,614 tokens，
而参考实现的解析机器分布在多个文件中。

### 7.2 消融：Euler–Maclaurin 路线贵 50%

§4 的自然替代是 Euler–Maclaurin：先证
`Σₙ[(n+1)^{1−s} − (n+2)^{1−s} − (s−1)(n+1)^{−s}] = 1 − ζ₁(s)`，再估计级数。实测成本：
项界 **264** + 增长定理 **540** + 积分恒等式 **95** + 辅助 **158** = **1,057 tokens**，而 Mellin 路线约 715；
且前者不提供 §4（2）的廉价零点排除。两条数学上都成立，形式成本相差约 50%——这是压缩是**结构性**的最清晰证据。

### 7.3 另两项结构决策

* **融合**：三个窗口界直接内联进总装（省去独立 `scaledWindow` 引理及其实例化）。
* **自动化**：不等式经 `grw` 归一后由 `linarith`/`nlinarith` 收口，而非一串辅助引理；文件共 55 个 `have`、
  10 个顶层声明，策略画像为 `simp` 38、`linarith` 18、`grind` 14、`norm_num` 10、`grw`。

---

## 8 官方评测

| 提交 | 制品 | 官方得分 | 曲线 `kept` | `running_best_pct` | tokens（本地 ≈ 官方） |
|---|---|---|---:|---|---:|
| **96283** | 2,931 tokens | **65.1339** | **true** | **87.24** | **2,931** |
| 96282 | 3,014 tokens | 64.98 | true | 86.87 | 3,014 |
| 96281 | 3,065 tokens | 64.8928 | true | 86.64 | 3,065 |
| 96276 | 3,208 tokens（修复版） | 64.64 | true | 86.03 | 3,208 |
| 96272 | 3,274 tokens | 64.5332 | true | 85.73 | 3,274 |
| 96286 | 2,843 tokens | 待定 | — | — | 2,843 |

快照时公开榜：榜首余荫铠（Yin-Kai Yu），`top_score = 65.1339`，站内 `best_tokens = 2762`；曲线随我方提交
依次上升 85.68 → 85.73 → 86.03 → 86.64 → 86.87 → 87.24。

**核验**：每份制品都经 kernel 检查（`#print axioms AlpogeRHCore1.zeroFreeRegion` =
`[propext, Classical.choice, Quot.sound]`，无 `sorry`）并由官方 Comparator 重放。另有两份制品
（3,242 与 2,880 tokens）本地干净却**被官方 Comparator 拒绝**，作为有效性边界归档——本地检查必要但不充分。

**度量校准**：反解计分公式恢复官方 token 数：96272 → 3,277 vs 本地 3,274；96276 → 3,215 vs 3,208；
96282 → 3,019 vs 3,014；96283 → 2,932 vs 2,931。±8 的一致性验证了 §7 的账本。

---

## 9 讨论

**三条可迁移原则。**（P1）*以库原语替换重推导*——剥离引理与 Mellin 公式；（P2）*选择尺度使估计可以粗糙*——
`2⁻²⁰/log R` 的保证把精确性要求变成裕量；（P3）*融合与自动化*——内联接口并让判定过程收口。三条原则上应可
迁移到其他解析支柱。

**局限。** 本文只涉及形式化项目的一根支柱（1/5），不是黎曼猜想；token 是基准特定的代理而非数学深度的度量；
若干节省属 Mathlib API 节省，因此结果度量的是库与证明的联合成熟度；接受度非单调（§8）。

**通向 2,500 tokens。** 弱化低高度排除（`|Im s| ≥ 1/2` → `|Im s| ≥ 32d`）并采用两分支自适应尺度（≈ −110）；
把两个对数输入合并为单一 von Mangoldt 对象（≈ −130）；用 `logDeriv` 重述剥离引理（≈ −100）。

---

## 10 制品与复现

制品包含证明源码、规范化 token 计量器（校准至 ±8）、编译 + 公理审计工具、官方证据快照、独立 Case A/B
架构（`research/caseAB/`），以及本文的中英两版。

```bash
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean   # -> 2931
LEAN_HOME=... MATHLIB=... tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   预期：compile rc=0；#print axioms -> [propext, Classical.choice, Quot.sound]
```

**来源。** 成果在账号 *余荫铠（Yin-Kai Yu）* 下产生，来自两条 AI agent 轨道协作的研究工作区
（DeepSeek Harness / Deepseek V4.1-Flash 与 ChatGPT Desktop / GPT-6.2 Astra）；提交、度量与本文均属该账号的记录。

**引用。**

```bibtex
@misc{yu2026zfrmath,
  author       = {Yu, Yin-Kai},
  title        = {Why It Fits: The Mathematical Structure of a 2,931-Token Lean 4 Proof of the Classical Zero-Free Region},
  year         = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url          = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
  note         = {Technique core1_borel_dslope; submission 96283, official score 65.1339, curve kept=true},
}
```

## 参考文献

[1] B. Riemann, *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse*, 1859.
[2] J. Hadamard, *Sur la distribution des zéros de la fonction ζ(s)…*, Bull. SMF 24 (1896), 199–220.
[3] C.-J. de la Vallée Poussin, *Recherches analytiques sur la théorie des nombres premiers*, 1896.
[4] E. Landau, *Handbuch der Lehre von der Verteilung der Primzahlen*, Teubner, 1909.
[5] E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., OUP, 1986.
[6] H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I*, CUP, 2007.
[7] L. de Moura, S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE-28, 2021, 625–635.
[8] The mathlib Community, *The Lean Mathematical Library*, CPP 2020, 367–381；mathlib4 commit `d13f23b7…`。
[9] É. Borel, *Sur les zéros des fonctions entières*, Acta Math. 20 (1897), 357–396.
[10] C. Carathéodory, *Über den Variabilitätsbereich…*, Math. Ann. 64 (1907), 95–115.
[11] H. von Mangoldt, *Zu Riemann's Abhandlung …*, J. Reine Angew. Math. 114 (1895), 255–305.
[12] L. Alpöge, *A Lean 4 formalization of the Riemann Hypothesis*（归档 `alpo.ge`），2025。
[13] Agentic Science Challenge, *Lean 4 Verification (RH Core Pillar 1/5)*，challenge `lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729`。
[14] 公开 Proof Compression Progress Curve，<https://riemann.verifytask.cn/>（含技术 `core1_borel_dslope`），2026。

## 附录 A. 使用的 Mathlib 声明

| 声明 | 文件（固定 commit） |
|---|---|
| `borelCaratheodory_zero` | `Analysis/Complex/BorelCaratheodory.lean:86` |
| `norm_deriv_le_div_of_mapsTo_ball` | `Analysis/Complex/Schwarz.lean:250` |
| `differentiableOn_dslope` | `Analysis/Complex/RemovableSingularity.lean:60` |
| `logDeriv_eqOn_iff`, `logDeriv_mul` | `Analysis/Calculus/LogDeriv.lean` |
| `integral_Ioi_cpow_of_lt` | `Analysis/SpecialFunctions/ImproperIntegrals.lean:251` |
| `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | `NumberTheory/LSeries/Dirichlet.lean:434` |
| `norm_LFunction_product_ge_one` | `NumberTheory/LSeries/Nonvanishing.lean:310` |
| `deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` | `NumberTheory/Harmonic/ZetaAsymp.lean:585` |

## 附录 B. 制品清单

`Lean/smallest-scored-96283/`（2,931 tokens，官方 65.1339）、`Lean/record-96282/`、`Lean/record-96281/`、
`Lean/fixes/localcert-fix/`（3,208-token 修复版，官方 64.64）、`Lean/record-96272/`、
`Lean/smallest-verified/`（2,843 tokens，待定）、`Lean/failed-96274-v22.lean`、`research/caseAB/`、
`tools/`、`evidence/`、`docs/`、`paper/main_en.md`、`paper/main_zh.md`。
