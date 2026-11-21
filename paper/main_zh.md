# 库原生证明压缩：黎曼 ζ(s) 经典无零点区域在 Lean 4 中的逐次纪录形式化

**余荫铠（Yin-Kai Yu）**

*DeepSeek Harness × ChatGPT Desktop 协作研究轨道 · 制品发布 v1.0 · 2026-11-22*
<https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>

---

## 摘要

黎曼 ζ 函数的经典无零点区域在每本解析数论教科书里只需几页即可证明，但其参考 Lean 4 形式化占 21 个文件、
21,641 个规范化 tokens。本文报告一项**库原生证明压缩**工作：把重新推导的解析机器替换为 Mathlib 原语，直到同一
命题装进单文件；并分析每一个 successive 纪录制品的数学结构。在公开压缩榜上五次纪录刷新之间（官方得分
64.5332 → 64.6400 → 64.8928 → 64.9800 → 65.1339，曲线标记均为 `kept = true`），制品规模依次为
3,274 → 3,208 → 3,065 → 3,014 → **2,931 tokens**（相对基线 −86.5%）。每一步都对应一项具体的结构性洞察：
以递归零点剥离引理替换有限零点乘积与围道估计；以 Mellin 整函数公式同时给出增长界与廉价零点排除；
以自适应尺度 `a = Re s + 5d`、`d = 2⁻²⁰/log R` 使所有估计可以粗糙却仍然决定性；以及窗口/总装接口的逐次融合。
文中给出逐组件 token 账本、Euler–Maclaurin 增长路线贵约 50% 的消融，以及包含两项本地可编译却被官方拒绝制品在内的
官方评测。

**关键词**：形式化分析 · Lean 4 · Mathlib · 证明压缩 · 无零点区域 · 解析差商 · Borel–Carathéodory 不等式

---

## 1 引言

形式证明的大小是一个有数学内容的工程量。在一份追随教科书论证的证明里，大部分体量花在**机器**上：重新推导的估计、
枚举的零点集、被界定的积分。现代数学库已提供其中大量机器，因此用库语言写出的证明可以比重新推导的证明小一个量级。
本文使用的公开证明压缩基准把这量显式化：命题冻结、环境固定（Lean 4.34.1 + Mathlib）、得分取决于提交的规范化
Lean token 数 `T`，注释与标识符命名不计成本 [13]；目标参考闭包为 21 个文件、`T₀ = 21,641` tokens。

本文报告五次刷新纪录的压缩序列，并——这是本文的重点——解释每一步的**数学结构**。§3 固定数学核心；
§4 按被接受的先后逐个走过五个纪录制品，指出各自的结构变化及其 token 后果；§5 汇总压缩机理并量化。

---

## 2 设定与度量

目标（冻结）：`∃ c > 0, ∀ s ≠ 1, 1 − c/log(|Im s|+2) ≤ Re s ⇒ ζ(s) ≠ 0`，即经典 de la Vallée Poussin
无零点区域 [3]，是带余项素数定理与 Landau–Page 理论 [4,5] 的基础。验证：Lean 4.34.1 [7] + Mathlib commit
`d13f23b7…` [8]、官方重放 Comparator、允许公理 `{propext, Quot.sound, Classical.choice}`、无 `sorry`。
度量：规范化 token 数 `T`，`Score(T) = 100 − 50/(1 + 0.5·log₁₀(T₀/T))`；本地计量器与官方计数误差 ≤ 8 tokens
（§6），故下文的账本与官方数可比。

---

## 3 数学核心

记 `ζ₁(s) = (s−1)ζ(s)`（整函数）。§4 的全部版本共享同一三步骨架。

**（S1）增长界。** 对 `1 < Re z`、`|Im z| ≤ 2R`（`R = |Im s|+2`）的 `z`，以 `R` 的多项式控制其半径 `1/2`
圆盘上的 `‖ζ₁‖`。

**（S2）对数导数界。** `f := ζ₁(z + ·)` 在 `|w| ≤ 1/2` 上以 `B` 增长，见证零点 `ρ`（`|ρ| ≈ 5d`）：
`x − Re(f′/f)(0) ≤ C(log B + 1)`，其中 `x = 0` 或 `x ≤ Re((−ρ)⁻¹)`。

**（S3）3–4–1。** 对 `a > 1` 与一切 `t`：`3D(a)+4D(a+t)+D(a+2t) ≥ 0`，`D(z) = Re Σ Λ(n)n^{−z}`，
即 `3+4cos θ+cos 2θ ≥ 0`。

五个纪录制品都用 Mellin 整函数公式做（S1）、用递归剥离引理做（S2）、用 Mathlib 乘积不等式做（S3）；
版本之间变化的是三者之间的**接口**与算术总装。共享核心：

* **Mellin 公式。** 在 `Re s > 0` 上 `ζ₁(s) = s(1 − (s−1)R(s))`，`‖R(s)‖ ≤ 1/Re s`。它给出（S1）
  （`Re z ≥ 1/2`、`‖z‖ ≤ 4R` 时 `‖ζ₁ z‖ ≤ R⁸`）以及 `s = 1` 附近的零点排除：`ζ₁(z)=0 ⇒ Re z ≤ |z−1|`，
  故 `Re z ≥ 3/4` 的零点满足 `|Im z| ≥ 1/2`。
* **剥离引理。** 整函数 `f`、`f 0 ≠ 0`、`|w| ≤ 1/2` 上增长常数 `B`、零点在闭左半平面、见证零点 `|ρ| ≤ 1/6`：
  `x − Re(f′/f)(0) ≤ 24(log B + 1)`。证明：内圆盘有零点则经 `dslope` 分解并以常数 `B/2` 递归；
  否则 `f` 有对数且 `Re g ≤ log B`，由 Borel–Carathéodory [9,10] 界定 `g′(0)`。该引理以 872 tokens
  替换有限零点乘积与柯西积分。
* **桥。** `Re(ζ₁′/ζ₁) = Re((s−1)⁻¹) + Re Σ Λ(n)n^{−s}`（`Re > 1`），把（S2）与（S3）连接起来。
* **总装。** 取 `a = Re s + 5d`、`d = 2⁻²⁰/log R`。则见证距中心恰为 `5d`（`x = (5d)⁻¹` 紧），
  前提 `1−d ≤ Re s` 给出 `4d ≤ a−1`，实中心极点项 `≤ (4d)⁻¹`；配合（S1）的低高度排除，中间极点项为 `O(d)`；
  3–4–1 不等式给出负裕量 `0.05/d ≥ 5·10⁴ log R`，而误差预算为 `O(log R)`——因此收尾 `linarith` 对粗糙估计稳健。

---

## 4 逐次纪录制品

五个制品都通过官方 Comparator、仅标准公理、曲线标记 `kept = true`。表中 token 为本地度量，得分为公开榜官方成绩。

| 纪录 # | 提交 | 制品 | tokens | 官方得分 | `running_best_pct` | 谱系标签 |
|---:|---|---|---:|---:|---:|---|
| — | 96263 | 原纪录保持者（Pi） | 3,286 | 64.5215 | 85.68 | — |
| 1 | 96272 | `Lean/record-96272/` | 3,274 | 64.5332 | 85.73 | prescribed-gap / further-weighted |
| 2 | 96276 | `Lean/fixes/localcert-fix/` | 3,208 | 64.6400 | 86.03 | local-certificate（经修复） |
| 3 | 96281 | `Lean/record-96281/` | 3,065 | 64.8928 | 86.64 | root-window |
| 4 | 96282 | `Lean/record-96282/` | 3,014 | 64.9800 | 86.87 | fused windows |
| 5 | 96283 | `Lean/smallest-scored-96283/` | 2,931 | 65.1339 | 87.24 | complex identity |

以下逐段说明每个纪录制品的结构推进。

### 4.1 纪录 1（3,274）：预设间隙与加权证书

前纪录者的窗口界在三个求值高度都取见证值 `x = 0`，中间高度因此付出很大的极点项。本制品**预设间隙**：
把见证零点放在距中心一个预设距离处，中间窗口的 `x` 从 `0` 变为紧的 `(5d)⁻¹`，3–4–1 组合随之重新加权。
数学要点是：经典论证并不要求零点在圆盘**内部**，只要求**距离**受控；用预设的方式控制距离，可消去总装中的一处分情形。站点给该制品的技巧标签为 *Perron/Mellin 围道精简 + grind
自动收口*，其论文式推导题为 *Borel–Carathéodory 与解析差商（dslope）递归零点剥离*：引入
`nld(f,z) = −Re(f′(z)/f(z))`，对满足 `B < 2ⁿ` 的 `n` 做强归纳证明 `x + nld(f,0) ≤ 24(log B + 1)`；
剥离步写作 `g(w) = dslope(f,ρ₀)(w)`、`f(w) = (w−ρ₀)g(w)`、`f(0) = −ρ₀g(0)`，并以 `B → B/2` 递归。

### 4.2 纪录 2（3,208）：局部证书与自适应尺度

本制品围绕**局部证书**重组总装：低高度排除与三个窗口实例都在最终定理内部由 Mellin 公式导出，而非经各自接口的独立引理。
其数学步骤是**自适应尺度** `a = Re s + 5d`、`d = 2⁻²⁰/log R`：尺度绑定于**假设的实部**而非固定 `1+4d`，
于是对任何候选零点见证距离恰为 `5d`，两个分支条件（`a > 1` 与 `a−1 ≥ 4d`）由单一前提 `1−d ≤ Re s` 一次性满足。
（该制品还做过一次形式修复：一个 `def` 使其展开体对 `linarith` 不可见，von Mangoldt 证书与窗口界使用了同一量的语法不同原子；
一处 `change` 把证书改写为目标中的原子。数学陈述不受影响。）

### 4.3 纪录 3（3,065）：根窗口重组

第三个制品把低高度排除所服务的两项功能——界定极点项与排除内圆盘零点——合并为一次**根窗口**，在极点 `s = 1` 一侧
只应用一次，而非在每个高度应用。结构上省去一个窗口引理的实例与一段算术 `have`；数学上利用了：关于中间高度只需要
`Re(((a+i·Im s)−1)⁻¹)` 的上界，而它由 `|Im s| ≥ 1/2` 直接可得，无需独立窗口。

### 4.4 纪录 4（3,014）：窗口融合与锐化极点界

本制品把窗口引理**融合**进总装，并把粗糙的极点界 `Re((z−1)⁻¹) ≤ 2` 换为锐化的
`Re((z−1)⁻¹) ≤ |Im z|⁻¹`（经 `re_le_norm`、`norm_inv`、`abs_im_le_norm`）。数学收益是总装中常数的锐化：
极点项分别由 `|γ|⁻¹ ≤ 2` 与 `(2|γ|)⁻¹` 控制，低高度信息直接进入不等式链而不经过引理接口。实测后果：
最终定理体 1,084 tokens，且不再有独立窗口引理。

### 4.5 纪录 5（2,931）：单一复恒等式

纪录制品把最后两处分离推导——整函数公式与 `s = 1` 附近的零点排除——替换为同一条贯穿总装的**复恒等式**，
使增长界、低高度排除与 von Mangoldt 替换都从同一个 `remainder` 对象读出。结构上：16 个顶层块，其中总装 1,038 tokens、
剥离引理 872、Mellin 模块 742、桥 78，其余 201 tokens 为见证与 Mellin 胶水。该技术被基准站点提炼为
`core1_borel_dslope`，原文见 §4.6。

### 4.6 已发表技术说明

> **`core1_borel_dslope`——「Borel–Carathéodory 与差商 (DSlope) 直接零点分解」**（为提交 96283 创建）。
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
> *关键信号*：`BorelCaratheodory`, `differentiableOn_dslope`, `grw`, `ZetaAsymp`。*压缩*：21 → 1 文件，−87.2%。

---

## 5 序列为何收敛：压缩机理

1. **以库原语替换重推导。** 剥离引理（872 tokens）替换零点分解与围道估计；Mellin 公式（742 tokens）替换
   Euler–Maclaurin 展开。二者合计 1,614 of 2,931 tokens，而参考实现恰把这些花在 21 个文件上。
2. **选尺度使估计可以粗糙。** `d = 2⁻²⁰/log R` 给出负裕量 `0.05/d ≥ 5·10⁴ log R`，对 `O(log R)` 误差；
   精确估计不必要，于是代码避开参考实现那些精确但冗长的界。
3. **融合接口并自动化。** 窗口界内联；不等式经 `grw` 归一后由 `linarith`/`nlinarith` 收口；文件共 10 个顶层声明、
   55 个 `have`，策略画像 `simp` 38、`linarith` 18、`grind` 14、`norm_num` 10。

**消融。** （S1）的自然 Euler–Maclaurin 路线（先证
`Σ[(n+1)^{1−s} − (n+2)^{1−s} − (s−1)(n+1)^{−s}] = 1 − ζ₁(s)`，再估计级数）成本 264 + 540 + 95 + 158 =
**1,057 tokens**，而 Mellin 约 715，且不提供廉价零点排除。两条数学上都成立的路线在形式成本上相差约 50%：
压缩是结构性的，而非表面的。

---

## 6 官方评测

账号全部提交的分数与曲线统计见 §4 表与 `docs/EVIDENCE.md`：纪录序列为 64.5332 → 64.6400 → 64.8928 →
64.9800 → 65.1339，`running_best_pct` 85.73 → 86.03 → 86.64 → 86.87 → 87.24。更早的提交（3,315 tokens，
得分 64.4685）未被 kept；一份 2,843-token 制品已提交，发布时评分待定。另有两份制品（3,242 与 2,880 tokens）
本地干净编译却被**官方 Comparator 拒绝**，作为有效性边界归档。反解官方计分公式恢复的 token 数误差 ±8
（如 65.1339 ⇒ ≈2,932 vs 2,931），验证了本文账本。在基准的*模型 × Harness* 榜单上，Deepseek V4.1-Flash / DeepSeek Harness 位列第一
（综合指数 64.50；平均压缩率 84.2%），其后为 GPT-6.2 Astra / ChatGPT Desktop（63.83；80.2%）、
Gemini 4 Neon（58.61）、Claude Opus 5.5（55.83）；见 `evidence/figures/leaderboard-model-harness.png`
与 `evidence/figures/leaderboard-avg-compression.png`。

---

## 7 讨论与结论

五个纪录制品最好读作**同一个数学构造**在逐步获得更好的接口：预设见证间隙；把尺度绑定到假设实部；在极点侧取用低高度
信息；融合窗口并锐化极点界；最后，以一条恒等式贯穿总装。没有一步改变命题；每一步都消去一层经典论证并不需要的接口或分情形。
对形式化分析的一般启示是：**证明体量主要由重复推导与接口开销决定，库原生化重写即压缩之道。**
局限：本文只涉形式化项目的一根支柱（1/5），不是黎曼猜想；token 是基准特定的结构代理而非数学深度的度量；若干节省属
Mathlib API 节省，因此结果度量库与证明的联合成熟度。下一步目标 2,500 tokens：弱化低高度排除（`|Im s| ≥ 1/2` →
`|Im s| ≥ 32d`）并采用两分支尺度（≈ −110）、把两个对数输入合并为单一 von Mangoldt 对象（≈ −130）、
用 `logDeriv` 重述剥离引理（≈ −100）。

**制品与复现。** 仓库包含：五个纪录制品及被拒绝/待定制品、token 计量器、编译+公理审计工具、官方证据快照、
独立 Case A/B 架构，以及本文中英两版。

```bash
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean   # -> 2931
LEAN_HOME=... MATHLIB=... tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   预期：compile rc=0；#print axioms -> [propext, Classical.choice, Quot.sound]
```

**来源。** 成果在账号 *余荫铠（Yin-Kai Yu）* 下产生，来自两条 AI agent 轨道协作的研究工作区
（DeepSeek Harness / Deepseek V4.1-Flash 与 ChatGPT Desktop / GPT-6.2 Astra）；提交、度量与本文均属该账号的记录。

**引用。**

```bibtex
@misc{yu2026zfrcompress,
  author       = {Yu, Yin-Kai},
  title        = {Library-Native Proof Compression: Successive Record Formalizations of the Classical Zero-Free Region in {Lean}~4},
  year         = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url          = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
  note         = {Five record refreshes; best official score 65.1339 (submission 96283), curve kept=true},
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
[13] Agentic Science Challenge, *Lean 4 Verification (RH Core Pillar 1/5)*（基线 `T₀ = 21,641`），2026。
[14] 公开 Proof Compression Progress Curve，<https://riemann.verifytask.cn/>，2026。

## 附录 A. 使用的 Mathlib 声明

`borelCaratheodory_zero`（`Analysis/Complex/BorelCaratheodory.lean:86`）、
`norm_deriv_le_div_of_mapsTo_ball`（`Analysis/Complex/Schwarz.lean:250`）、
`differentiableOn_dslope`（`Analysis/Complex/RemovableSingularity.lean:60`）、
`logDeriv_eqOn_iff`、`logDeriv_mul`（`Analysis/Calculus/LogDeriv.lean`）、
`integral_Ioi_cpow_of_lt`（`Analysis/SpecialFunctions/ImproperIntegrals.lean:251`）、
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`（`NumberTheory/LSeries/Dirichlet.lean:434`）、
`norm_LFunction_product_ge_one`（`NumberTheory/LSeries/Nonvanishing.lean:310`）、
`deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add`（`NumberTheory/Harmonic/ZetaAsymp.lean:585`）。

## 附录 B. 制品清单

`Lean/record-96272/`、`Lean/fixes/localcert-fix/`、`Lean/record-96281/`、`Lean/record-96282/`、
`Lean/smallest-scored-96283/`（五个纪录制品）、`Lean/smallest-verified/`（2,843 tokens，待定）、
`Lean/failed-96274-v22.lean`（被拒）、`research/caseAB/`、`tools/`、`evidence/`、`docs/`、
`paper/main_en.md`、`paper/main_zh.md`。
