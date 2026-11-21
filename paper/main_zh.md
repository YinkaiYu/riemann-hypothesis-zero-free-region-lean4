# 验证、修复与度量压缩后的形式证明

### 黎曼 ζ(s) 经典无零点区域在 Lean 4 中的独立验证轨道

**余荫铠（Yin-Kai Yu）** · DeepSeek Harness RH-Core1 研究轨道

*制品发布 v1.0 — 2026-11-22 · 仓库：<https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>*

---

## 摘要

证明压缩类基准奖励的是「小且经机器验证」的形式证明，但它同时暴露出一个系统性的方法论缺口：本地可编译的
压缩制品可能在官方重放校验中失败；而「小」的证明未必由提交者本人产出。本文报告一条针对黎曼 ζ 函数经典
de la Vallée Poussin 无零点区域（Lean 4 / Mathlib；参考形式化 21 个文件、21,641 个规范化 tokens）的
**独立验证、修复与度量轨道**。我们的贡献是方法论与实证性的：（i）对每个候选制品在固定工具链上编译并审计
kernel 公理的验证流水线；（ii）一个**修复案例**——一份 3,179-token 的不可编译半成品被诊断为算术预处理器
原子失配（`def` 使 `linarith` 看不见其展开体），经一处 `change` 修复为 3,208-token 制品并被官方重放接受
（官方得分 64.64，曲线标记 `kept = true`）；（iii）对我们提交的压缩谱系的实测记录（2,931–3,315 tokens，
官方得分 64.47–65.13），以及「本地可编译是必要条件而非充分条件」这一负结果（两项本地干净制品被官方
Comparator 拒绝）；（iv）一条消除低高度零点排除的独立 Case A/B 架构；（v）一项消融：Euler–Maclaurin
增长路线在形式 token 上比 Mellin 路线贵约 50%。我们发布全部制品、工具与证据，并明确区分归属：压缩后的
证明族及其标志性技术由共享工作区中的并行轨道提出，本文按正确归属复述；我们的贡献是独立验证、修复、提交与度量。

**关键词**：形式验证 · 证明压缩 · 独立验证 · Lean 4 · Mathlib · 无零点区域 · 制品评估

---

## 1 引言

压缩后的形式证明正在成为独立意义上的「制品」：近期的基准会冻结命题、固定工具链，并以忽略注释、空白与
import 行的规范化 token 数计分 [12,13]。这类基准带来了新的评估问题：制品必须被**官方重放器**核验，而不仅是
由作者本地编译；同时，一次提交的记录必须区分「制品的来源」与「提交这一行为」。在共享工作区中获得的已证
明显然仍是独立验证下的实证对象，其在本方核验下的行为值得研究。

本文报告这样一条独立轨道。我们取该基准的目标——黎曼 ζ 函数的经典 de la Vallée Poussin 无零点区域，在
Mathlib [7,8] 之上的 Lean 4 形式化，参考闭包为 21 个文件、21,641 个规范化 tokens [12]（亦见 [5]）——并追问：

* **Q1（验证）**：在提交之前，我们能对一个候选压缩制品检查什么？本地检查在何处开始失去信息量？
* **Q2（修复）**：压缩制品失败时的故障分类学是什么？在不改变数学内容的前提下修复的代价有多大？
* **Q3（度量）**：所声称的压缩由什么组成（逐组件）？哪些数学替代路线在形式 token 上更便宜或更昂贵？

**贡献。**（1）验证流水线，以及一项负结果：两项本地干净（3,242 与 2,880 tokens）的制品被官方 Comparator
拒绝（§4.4）。（2）修复案例：3,179-token 半成品因 `def` 声明使 `linarith` 的原子比较看不见其展开体而失败；
以 `change` 为基础的修复得到 3,208-token 制品，官方得分 **64.64**、`kept = true`（§4.3）。（3）对我方提交的
压缩谱系的实测记录（§6），官方得分 64.47–65.13 及曲线统计。（4）一条消除低高度零点排除的独立 Case A/B
架构（§5.2）。（5）增长界路线的消融（§6.4）。（6）制品、工具与证据的发布。

**范围与诚信。** 压缩后的证明族——以及平台将其机器摘要为 `core1_borel_dslope` 的技术（「Borel–Carathéodory
+ 差商零点分解」）——源自共享工作区中的并行轨道；§5 在正确归属下描述它，并原文复现平台的技术说明。
我们不主张该技术的著作权；我们主张的是验证、修复、提交与度量工作，Case A/B 架构，以及消融实验。
本文**不涉及**黎曼猜想本体：它只涉及其形式化项目中的一根解析支柱（1/5）。

---

## 2 设定

**目标命题（冻结）**：

```lean
theorem AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0
```

即经典 de la Vallée Poussin 无零点区域 [3]，是带余项素数定理与 Landau–Page 理论 [4,5] 的标准前置输入。

**校验契约**：Lean 4.34.1 [7]、Mathlib commit `d13f23b7…` [8]、官方重放 Comparator；允许公理
`{propext, Quot.sound, Classical.choice}`；禁止 `sorry` 与自定义公理。

**度量协议**：规范化 token 数 `T`（注释/空白/import 计 0；标识符计 1），基准基线 `T₀ = 21,641` [12]。
我们用 `tools/token_count.py` 本地复现 `T`，并以官方得分校准至 ±8 tokens（§6.3）。基准得分为
`Score(T) = 100 − 50/(1 + 0.5·log₁₀(T₀/T))`。

---

## 3 验证流水线

每个候选制品在提交前经过四阶段：

1. **编译**：离线、固定工具链、指定 `LEAN_PATH`；
2. **公理审计**：`#print axioms AlpogeRHCore1.zeroFreeRegion` 必须恰为
   `[propext, Classical.choice, Quot.sound]`，以捕获隐藏的 `sorry` 与自定义公理；
3. **token 度量**：用本地规范化器排序候选；
4. **迭代修复**：失败则进入 §4 的修复循环。

该流水线刻意冗余：它能捕获最常见的静默失败（`sorry` 进入最终定理），但如下文 §4.4 所示，它并不覆盖一切。

---

## 4 修复：一个案例研究

### 4.1 观测到的故障分类学

在候选中我们观测到三类故障：（F1）重构后的类型类/定义性不匹配；（F2）**算术原子失配**——`linarith` 类
证明器看到同一量的两种语法上不同的表示而失败；（F3）本地成功但被官方 Comparator 拒绝。其中 F2 最值得注意：
它由 `def` 造成，而非由数学造成。

### 4.2 失败制品

一份半成品（3,179 tokens、单文件、239 行）把无零点区域证明归约到最后一个 `linarith` 步骤：从三个窗口界、
`3D(a)+4D(a+it)+D(a+2it) ≥ 0` 的非负证书（其中 `D(z) = Re Σ Λ(n)n^{−z}`），以及 `‖ζ₁‖` 的对数和下界推出
3–4–1 矛盾。该步骤报错

```
error: linarith failed to find a contradiction
...
⊢ False
```

尽管全部数值假设都在上下文中。

### 4.3 诊断与修复

该制品声明了 `def D z := (LSeries (fun n => (Λ n : ℂ)) z).re`。非负证书由 `HasSum.nonneg` 产生，因此其
结论原子形如 `(LSeries …).re`；而窗口界使用原子 `D …`。由于 `def` 是半可归约的，二者在定义上相等但在语法上
不同；算术预处理器只看到语法形式，于是某假设中的 `3D` 项永远无法与另一假设中的 `3·(LSeries …).re` 原子相约。
修复只需一行：

```lean
  change 0 ≤ 3*D ⟨a,0⟩+4*D ⟨a,s.im⟩+D ⟨a,2*s.im⟩ at M
```

在 `linarith` 之前把证书改写为 `D` 原子。修复后的制品干净编译（240 行，**3,208 tokens**，仅标准公理）。
以提交 **96276** 送交官方，得到官方得分 **64.64**，曲线标记 `kept = true`，`running_best_pct` 由 85.73 升至
**86.03**——当时的一次纪录刷新。

**教训。** 在压缩证明中，`def` 与 `abbrev` 不是风格选择：半可归约定义会给自动化插入不可见的边界。由于基准
度量忽略标识符长度，廉价的修法是在边界处 `change`，而不是逐个展开定义。

### 4.4 本地验证的极限

两项制品——3,242-token 候选与一份 2,880-token 候选——在本环境中以标准公理编译通过，却被**官方 Comparator
拒绝**（`scoringState = failed`，得分 0）。我们将其作为负结果报告：独立的外部重放是与本地 kernel 检查
不同层级的置信度，评估流水线必须包含前者。被拒绝的 3,242-token 制品已归档于发布中。

---

## 5 我们提交的压缩制品

我们提交的制品属于由共享工作区中的并行轨道（ChatGPT Desktop / GPT-6.2 Astra）开发的证明族。我们的角色是
验证、修复、提交与度量。为完整性，我们概述该族的技术内容，并给出归属。

### 5.1 该族的技术（归属）

平台为我们的提交 96283 机器合成的技术说明——原文复现于 §5.4——描述了该族的标志性装置：*把假想零点经
Mathlib 的解析差商 `dslope` 分解出来，对差商以减半的增长常数递归，再用 Borel–Carathéodory 控制对数导数。*
数学上，它把一个经典 Landau 型估计打包成一次归纳：若 `f` 在小圆盘内有零点，就剥离它；否则 `f` 无零点，
存在对数，Borel–Carathéodory 不等式适用。参考形式化则用 21 个文件重新推导零点分解与柯西积分估计。

### 5.2 独立架构（我方）

作为对数学的独立复核，我们开发了一条 **Case A/B 架构**（已验证、公理干净、9,344 tokens；
`research/caseAB/`）：Case A（`25d ≤ |Im s|`）取 `a = 1+4d`、见证 `(5d)⁻¹`；Case B（`|Im s| < 25d`）把
Landau 估计移到极点一侧（`f(w) = ζ₁(1+w)`，见证 `(1−s)⁻¹ ≥ 1/(626d)`）并施加 Schwarz 导数界，从而完全
消除低高度零点排除。它在 token 上不具竞争力，但是一条独立的推导。

### 5.3 路线简述

`ζ₁ = (s−1)ζ` 的 Mellin 整函数公式（余项 ≤ `1/Re s`；增长界与廉价零点排除）→ 剥离引理
（Borel–Carathéodory + `dslope`）→ von Mangoldt 桥 → 三个窗口界 → 以自适应尺度 `a = Re s + 5d`、
`d = 2⁻²⁰/log R` 的总装，配合 3–4–1 乘积不等式 `‖ζ(a)‖³‖ζ(a+it)‖⁴‖ζ(a+2it)‖ ≥ 1` 与一步 `linarith`。

### 5.4 已发表的技术说明（原文，平台为我们的提交 96283 生成）

> **技巧 `core1_borel_dslope` ——「Borel–Carathéodory 与差商 (DSlope) 直接零点分解」**
> （类别 *复分析 · Mathlib 复用*；提交 96283；模型 *Deepseek V4.1-Flash*；Harness *DeepSeek Harness*；
> 该说明由平台自动合成，来源：共享工作区、并行 ChatGPT 轨道——见 §8）。
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

## 6 度量

### 6.1 本轨道的提交

| 提交 | 制品 | 官方得分 | 曲线 `kept` | `running_best_pct` | tokens（本地 ≈ 官方） |
|---|---|---|---:|---|---:|
| 96268 | 3,315-token 共享制品 | 64.4685 | false | 85.68 | 3,315 |
| 96272 | 3,274-token 共享制品 | 64.5332 | **true** | 85.73 | 3,274 |
| **96276** | **修复后的半成品（§4.3）** | **64.64** | **true** | **86.03** | **3,208** |
| 96282 | 3,014-token 共享制品 | 64.98 | true | 86.87 | 3,014 |
| 96283 | 2,931-token 共享制品 | 65.1339 | true | 87.24 | 2,931 |
| 96286 | 2,843-token 制品 | 待定 | — | — | 2,843 |
| 96274 / 96284 | 3,242 / 2,880 tokens | 0（被拒） | — | — | — |

3,315/3,274/3,014/2,931/2,843 号制品均为并行轨道产出、由我方提交的共享族制品；96276 的 3,208-token 制品
是我们的修复成果。全部得分为官方成绩；`kept = true` 点为公开曲线纪录。

### 6.2 最小已评分制品的组件成本（2,931 tokens）

| 组件 | tokens | 占比 |
|---|---:|---:|
| 总装 | 1,038 | 35.4 % |
| 剥离引理 | 872 | 29.7 % |
| Mellin 整函数公式 | 742 | 25.3 % |
| von Mangoldt 桥 | 78 | 2.7 % |
| 其他 | 201 | 6.9 % |

### 6.3 度量校准

反解官方计分公式可恢复官方 token 数，与本地计量对比：96272：3,277 vs 3,274（Δ = −3）；96276：3,215 vs
3,208（−7）；96282：3,019 vs 3,014（−5）；96283：2,932 vs 2,931（−1）。±8 的一致性验证了提交前排序的有效性。

### 6.4 消融：增长界路线

增长界的自然 Euler–Maclaurin 路线（先证
`Σₙ[(n+1)^{1−s} − (n+2)^{1−s} − (s−1)(n+1)^{−s}] = 1 − ζ₁(s)`，再估计级数）成本为
264 + 540 + 95 + 158 = **1,057 tokens**，而 Mellin 路线约 715；且不提供 `s = 1` 附近的廉价零点排除。
故未采用。两条数学上都成立的路线之间存在约 50% 的形式成本差，这是「压缩是结构性的而非表面的」的最清晰证据。

---

## 7 讨论与局限

* **范围**：单一解析支柱（1/5），不是黎曼猜想。
* **度量特定性**：规范化 token 是基准特定的「证明结构」代理，不是数学深度的度量；跨基准比较无意义。
* **库依赖**：若干节省来自 Mathlib API；结果度量的是库与证明的联合成熟度。
* **接受度的非单调性**：本地成功不蕴含被接受（§4.4）；一份 2,843-token 制品已提交但发布时尚未评分。
* **归属**：压缩族的设计属并行轨道；我们的主张限于验证/修复/提交/度量、Case A/B 架构与消融（§8）。

**路线图（来自实测）**：将低高度排除从 `|Im s| ≥ 1/2` 弱化到 `|Im s| ≥ 32d` 并采用两分支自适应尺度
（≈ −110 tokens）；把两个对数输入合并为单一 von Mangoldt 级数对象（≈ −130）；用 `logDeriv` 重述剥离引理
（≈ −100）。目标：2,400–2,500 tokens。

---

## 8 来源与研究诚信

两个 AI agent 在同一基准账号上并发工作：**DeepSeek Harness** 轨道（`Deepseek V4.1-Flash`，本文作者）与
**ChatGPT Desktop** 轨道（`GPT-6.2 Astra`）。压缩后的证明族及其标志性技术属并行轨道的成果；平台为我们的
提交 96283 自动合成了 §5.4 的技术说明，这解释了为何该说明带有我们的账号与申报模型——该说明是**一次提交的
记录**，而非对技术著作权的声明。本文自身的贡献为：验证流水线（§3）、修复案例（§4.2–4.3）、提交与度量记录
（§6.1–6.3）、独立 Case A/B 架构（§5.2）、消融（§6.4）与制品发布。被拒绝制品与待定分数如实报告（§4.4、§6.1）。
本仓库包含**我方提交的制品及其官方证据**，不包含私钥、轨迹或第三方凭据。

**引用。**

```bibtex
@misc{yu2026zfrverify,
  author       = {Yu, Yin-Kai and {DeepSeek Harness RH-Core1 Research Track}},
  title        = {Verifying, Repairing, and Measuring Compressed Formal Proofs: An Independent Track on the Classical Zero-Free Region in Lean 4},
  year         = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url          = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
  note         = {Independent verification/repair track; technique note reproduced with attribution},
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
[12] L. Alpöge, *A Lean 4 formalization of the Riemann Hypothesis*（归档 `alpo.ge`，175,187 文件 / 980,408,459 字符），2025。
[13] Agentic Science Challenge, *Lean 4 Verification (RH Core Pillar 1/5)*，challenge
`lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729`。
[14] 公开 Proof Compression Progress Curve，<https://riemann.verifytask.cn/>（技巧 `core1_borel_dslope`），2026。

## 附录 A. 提交族使用的 Mathlib 声明

| 声明 | 文件（固定 commit） |
|---|---|
| `borelCaratheodory_zero` | `Analysis/Complex/BorelCaratheodory.lean:86` |
| `norm_deriv_le_div_of_mapsTo_ball` | `Analysis/Complex/Schwarz.lean:250` |
| `differentiableOn_dslope` | `Analysis/Complex/RemovableSingularity.lean:60` |
| `logDeriv_eqOn_iff`, `logDeriv_mul` | `Analysis/Calculus/LogDeriv.lean` |
| `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | `NumberTheory/LSeries/Dirichlet.lean:434` |
| `norm_LFunction_product_ge_one` | `NumberTheory/LSeries/Nonvanishing.lean:310` |
| `deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` | `NumberTheory/Harmonic/ZetaAsymp.lean:585` |

## 附录 B. 制品清单

`Lean/fixes/localcert-fix/Solution.lean`（我们的修复，3,208 tokens，官方 64.64，`kept=true`）；
`Lean/smallest-scored-96283/`（2,931 tokens，官方 65.1339——由我方提交的共享族制品）；
`Lean/record-96282/`、`Lean/record-96281/`、`Lean/record-96272/`、`Lean/smallest-verified/`、
`Lean/failed-96274-v22.lean`；`research/caseAB/`（我方独立架构）；`tools/`；`evidence/`；`docs/`；
`paper/main_en.md`、`paper/main_zh.md`。
