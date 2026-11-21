# 黎曼 ζ(s) 经典无零点区域定理的 2,931-Token 机器验证证明

### 以证明压缩为目标的制品级形式数学基准研究

**余荫铠（Yin-Kai Yu）** · DeepSeek Harness RH-Core1 研究轨道

**制品发布 v1.0** — 2026-11-22 · 仓库：<https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>

> **关于本文结果的说明**：本文所有数字均取自 *Agentic Science Challenge — Lean 4 形式化验证（黎曼猜想核心支柱 1/5）*
> 的官方公开榜单，并标注快照时间。证明制品经过机器验证；榜单成绩为官方成绩。本文不涉及黎曼猜想的完整证明——
> 本制品覆盖该形式化项目 **五大解析支柱中的第一根**（见 §1）。

---

## 摘要

本文给出黎曼 ζ 函数经典 de la Vallée Poussin 无零点区域的完整 Lean 4 机器验证证明——即存在绝对常数
`c > 0`，使得当 `Re(s) ≥ 1 − c/log(|Im(s)|+2)` 时 `ζ(s) ≠ 0`——并将其压缩为**单文件 2,931 个规范化
Lean 4 tokens**，相较参考形式化的 **21 个文件 / 21,641 tokens** 减少 **86.5%**。该制品在 *Agentic Science
Challenge*（黎曼猜想核心支柱 1/5，基线 `T₀ = 21,641`）的抗 Code Golf 规范化度量下，由官方基于重放的
Comparator 校验，并登顶公开 **Proof Compression Progress Curve**（提交编号 96283；官方得分 **65.1339**；
曲线标记 `kept = true`；`running_best_pct = 87.24`，前一点为 86.87）。本文给出压缩的**组件级归因**
（五个证明组件的实测 token 成本），报告两项独立的负结果（Euler–Maclaurin 增长路线在 token 上反而更贵，
1,057 vs ≈ 715；两项本地可编译却被官方 Comparator 拒绝的制品），并完整发布制品：源码、工具、官方证据快照、
以及同一命题的独立分情形证明，并给出通向 2,500 tokens 的压缩路线图。

**关键词**：形式数学 · Lean 4 · Mathlib · 黎曼 ζ 函数 · 无零点区域 · 证明压缩 · 基准制品

---

## 1. 引言

素数的分布由黎曼 ζ 函数的零点支配。Riemann（1859）[1] 把素数计数函数与非平凡零点联系起来；证明全部非平凡
零点的实部等于 1/2 即黎曼猜想（RH）。即便不假定 RH，Hadamard [2] 与 de la Vallée Poussin [3] 于 1896 年
独立证明：`ζ(s)` 在直线 `Re(s) = 1` 右侧的一个区域内**没有零点**，即存在绝对常数 `c > 0` 使

```
Re(s) ≥ 1 − c / log(|Im(s)| + 2)          (s ≠ 1)
```

这一*经典无零点区域*给出带显式余项的素数定理，并且是 Dirichlet `L` 函数 Landau–Page 理论 [4,5] 的标准前置输入。

**形式化背景。** 在 Mathlib [8] 之上已有 Lean 4 [7] 的 ζ 函数理论形式化；本任务源自 Levent Alpöge 的
黎曼猜想 Lean 4 形式化项目（其归档为 175,187 个文件 / 980,408,459 个字符）。该形式化被拆分为五个
*核心支柱*用于评测；本制品对应**核心支柱 1/5**：经典无零点区域（参考发布中的
`src/Formalism/ZeroFreeRegion/FinalZFR.lean`，即 `Formalism.ZF.zeroFreeRegion`），其参考发布的传递闭包为
**21 个文件 / 74,010 个字符 / 21,641 个规范化 tokens**。

**任务与度量。** *Agentic Science Challenge* 冻结命题陈述（`AlpogeRHCore1.zeroFreeRegion`，见 §2），
固定 Lean 4.34.1 + Mathlib 环境与官方重放式 Comparator，并以**抗 Code Golf 规范化 token 数** `T` 计分：
注释、空白与 `import` 行计 0 token，标识符长度不计。因此只有真正的数学压缩才会改变得分 [9]。官方得分为

```
Score(T) = 100 − 50 / (1 + 0.5·log₁₀(T₀/T)),        T₀ = 21,641.
```

**本文贡献：**

1. **一个完整的压缩证明**（§3）：单文件 2,931 tokens 的 Lean 4 证明，经官方 Comparator 重放，
   kernel 公理集为 `{propext, Classical.choice, Quot.sound}`。
2. **压缩的组件级归因**（§3.7）：五个证明组件的实测 token 成本，使压缩可追溯、可复核，而非仅被观察到。
3. **官方证据**（§4）：本项目提交在公开进度曲线上获得**连续四次** `kept = true` 的纪录刷新；由官方得分反解
   出官方 token 数，并与本地度量交叉校验（误差 ±8 tokens）。
4. **负结果**（§3.8）：Euler–Maclaurin 增长路线的实测成本高于 Mellin 路线；两项本地可编译却被官方
   Comparator 拒绝的制品——予以公开，以免重复「本地 kernel 检查即等于可提交」的误解。
5. **完整发布的制品**（§6、§7）：源码、规范化 token 计量器、编译与公理审计工具、官方证据快照，以及同一命题的
   独立分情形证明（Case A/B，移除了低高度零点排除）。

需要强调**范围**：本文**不是**黎曼猜想的证明，而是一根解析支柱的压缩与机器验证，作为可复现的制品发布。

---

## 2. 问题陈述、校验契约与度量

### 2.1 目标定理

```lean
theorem AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0
```

命题由基准冻结；提交可将辅助引理拆分到同目录其他 `.lean` 文件，但不得修改冻结陈述、遮蔽保留命名空间或使用未许可公理。

### 2.2 校验契约

| 项目 | 值 |
|---|---|
| 证明助手 | Lean 4.34.1 |
| 数学库 | Mathlib，commit `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| 重放器 | 官方 Comparator（`openverify-lean4341-ns`）+ 密码学共享构建缓存 |
| 允许公理 | `propext`、`Quot.sound`、`Classical.choice` |
| 禁止 | `sorry`/`sorryAx`、自定义 `axiom`、命名空间遮蔽、修改 `ComparatorChallenges/*` |
| kernel 审计 | `#print axioms AlpogeRHCore1.zeroFreeRegion` = `[propext, Classical.choice, Quot.sound]` |

### 2.3 抗 Code Golf 度量

`T` 由提交的 `.lean` 源文件在删除注释、空白与 `import` 行后计算得到。因此：写文档、用更清晰的名字**不花成本**；
改单字母变量名、删空格、压缩 import **不得分**；使用 `notation`/`macro` 起别名反而增加成本。`T = T₀` 得 50 分，
压缩 10 倍得 66.67 分，压缩 100 倍得 75 分。本仓库的本地实现（`tools/token_count.py`）在本文档所有已评分提交上
与官方计数误差 ≤ 8 tokens（§4.3），使提交前排序成为可能。

---

## 3. 方法：压缩后的证明

### 3.1 总览

压缩证明为单文件，五个数学组件如下串联：

```
  分数部分尾项的 Mellin 变换
        │  (C1)  ζ₁(s) = (s−1)ζ(s) = s·(1 − (s−1)·R(s))，  ‖R(s)‖ ≤ 1/Re s
        ├──────────────► Re ≥ 1/2 上 ζ₁ 的多项式增长界     （供 C2）
        └──────────────► s = 1 附近的零点排除              （供 C5）
  Landau 型引理：Borel–Carathéodory + dslope 零点剥离          (C2)
        │  x − Re(f′/f)(0) ≤ 24(log B + 1) + x
  von Mangoldt 桥：Re(ζ₁′/ζ₁) = Re((s−1)⁻¹) + Re(Σ Λ(n)n^{−s})  (C3)
        │
  三个高度 0、Im s、2·Im s 上的窗口估计                          (C4)
        │
  总装：自适应尺度 a = Re s + 5d，3–4–1 乘积不等式
        ‖ζ(a)‖³‖ζ(a+it)‖⁴‖ζ(a+2it)‖ ≥ 1，线性算术收口            (C5)
```

记 `ζ₁ := (s−1)ζ`。以下各小节给出五个组件及其在 2,931-token 记录文件中的实测成本。

### 3.2 C1 —— 经 Mellin 变换的 `ζ₁` 整函数公式（≈ 715 tokens）

利用分数部分尾项 `fract` 及其 Mellin 变换 `R(s) = mellin(fract·1_{>1})(−s)`，在 `Re s > 0` 上证明

```lean
lemma entireFormula (hs : 0 < s.re) : riemannZeta₁ s = s * (1 - (s-1) * remainder s)
lemma mellin_bound (hs : 0 < s.re) : ‖remainder s‖ ≤ 1 / s.re
lemma tail_smooth : DifferentiableOn ℂ remainder {z | 0 < z.re}
```

证明把恒等式从 `Re s > 1`（`ζ` 与 Mellin 积分同时收敛处）经预连通子域上的解析延拓推广到半平面 `Re s > 0`。
下游使用两个推论：**增长界** `entireGrowth : ‖z‖ ≤ 4R ⇒ ‖ζ₁ z‖ ≤ R⁸`（`Re z ≥ 1/2`），供 C2；
以及**极点附近的零点排除**：若 `ζ₁(z) = 0` 则 `(z−1)·R(z) = 1`，故 `Re z ≤ |z−1|`；结合 `Re z ≥ 3/4`
可得 `|Im z| ≥ 1/2`。

### 3.3 C2 —— Landau 型引理：Borel–Carathéodory 与零点剥离（≈ 872 tokens）

核心压缩用一个递归替换了多文件有限零点乘积论证。设 `f : ℂ → ℂ` 可微、`f 0 ≠ 0`、在圆盘 `‖w‖ ≤ 1/2` 上
增长常数 `B`，且所有零点在闭左半平面：

```lean
theorem landau {f : ℂ → ℂ} {B x : ℝ}
    (hd : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hb : ∀ w, ‖w‖ ≤ 2⁻¹ → ‖f w‖ ≤ B * ‖f 0‖)
    (hz : ∀ ρ, f ρ = 0 → ρ.re ≤ 0)
    (hx : x = 0 ∨ witness f x) :
    x - (deriv f 0 / f 0).re ≤ 24 * (Real.log B + 1)
```

*证明要点*：对 `n` 归纳，`B < 2ⁿ`。若内圆盘内有零点 `ρ`，分解 `f = (·−ρ) · dslope f ρ`；该差商可微、
在 `0` 处非零，并由最大模原理（`norm_le_of_forall_mem_frontier_norm_le`）满足增长常数 `B/2` 的同类界，
递归后由对数导数加回 `Re(−ρ⁻¹)`。否则 `f` 在小圆盘上无零点，`logDeriv f` 在该处精确，于是 Mathlib 的
Borel–Carathéodory 对数形式引理（`Analysis/Complex/BorelCaratheodory.lean`，`borelCaratheodory_zero`）
给出中心处导数界；Lipschitz 一步与线性算术收尾。

### 3.4 C3 —— von Mangoldt 桥（≈ 78 tokens）

```lean
lemma good (ha : 1 < z.re) :
  riemannZeta₁ z ≠ 0 ∧
  deriv riemannZeta₁ z / riemannZeta₁ z = (z-1)⁻¹ - LSeries (fun n => (Λ n : ℂ)) z
```

使用 `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`（`NumberTheory/LSeries/Dirichlet.lean`）与
`deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add`（`NumberTheory/Harmonic/ZetaAsymp.lean`），使 C2 对
`ζ₁′/ζ₁` 的估计可与经典 3–4–1 不等式比较。

### 3.5 C4 —— 窗口估计

对三个求值高度 `v ∈ {0, Im s, 2·Im s}`，在中心 `z = a + iv` 处对 `w ↦ ζ₁(z + w)` 应用 C2，增长比
`B := R⁸/‖ζ₁ z‖`：增长假设由 C1 提供，零点侧假设由 C3 提供。所得界只保留两个运行标量：见证值 `x`
（`0` 或 `(5d)⁻¹`）与实中心项。

### 3.6 C5 —— 总装：自适应尺度与 3–4–1 不等式（≈ 1,038 tokens）

取 `R := |Im s| + 2`，`d := 2⁻²⁰/log R`（故 `d ≤ 1/100`），并令 **`a := Re s + 5d`**。自适应尺度是关键技巧：
它把见证零点 `s` 放到距中心恰好 `5d` 处，使 `x = (5d)⁻¹` 恰好紧；而假设 `1 − d ≤ Re s` 给出 `4d ≤ a − 1`，
从而控制实中心处的极点项。随后使用：

* C1 得到的低高度排除（`|Im s| ≥ 1/2`），控制另两个极点项；
* Mathlib 的 3–4–1 乘积不等式（`norm_LFunction_product_ge_one`，
  `NumberTheory/LSeries/Nonvanishing.lean`），即 `‖ζ(a)‖³‖ζ(a+it)‖⁴‖ζ(a+2it)‖ ≥ 1`，等价于逐点
  `3 + 4cos θ + cos 2θ ≥ 0`；
* `HasSum.nonneg` 证书：`3D(a) + 4D(a+it) + D(a+2it) ≥ 0`，其中 `D(z) = Re(Σ Λ(n)n^{−z})`；
* 一步 `linarith`，配合 `Real.log_le_self` 与 `Real.log_two_lt_d9`。

算术刻意做得很粗：负裕量 `(4/5 − 3/4)/d = 0.05/d ≥ 5·10⁴·log R`，而正误差总量为
`192(8 log R + 1 + log log R + …) = O(log R)`。

### 3.7 Token 预算与设计决策

实测于 2,931-token 记录文件（`Lean/smallest-scored-96283/Solution.lean`）：

| 组件 | tokens | 占比 |
|---|---:|---:|
| C5 总装（`AlpogeRHCore1.zeroFreeRegion`） | 1,038 | 35.4 % |
| C2 `landau` | 872 | 29.7 % |
| C1 `entireFormula` | 350 | 11.9 % |
| C1 `tail_smooth` | 181 | 6.2 % |
| C1 `mellin_bound` | 107 | 3.7 % |
| C1 `entireGrowth` | 104 | 3.5 % |
| C3 `good` | 78 | 2.7 % |
| witness / Mellin 辅助 / 前言 / 其他 | 201 | 6.9 % |
| **合计** | **2,931** | **100 %** |

压缩来自五项设计决策（按效果降序）：
（i）以**带零点剥离的单个 Landau 引理**替代有限零点乘积 + 围道机器；
（ii）以 **Mellin 整函数公式**替代手写 Euler–Maclaurin 估计；
（iii）把**窗口估计融合进总装**（省去独立 `scaledWindow` 引理）；
（iv）以**自适应尺度** `a = Re s + 5d` 替代固定 `1 + 4d`（减少常数分情形并提升见证紧度）；
（v）**充分使用 Mathlib 的自动化与分析 API**（`grw`、`gcongr`、`linarith`、`nlinarith`、`grind`、`dslope`、
`borelCaratheodory_zero`、`norm_LFunction_product_ge_one`）。

### 3.8 负结果

**Euler–Maclaurin 增长比 Mellin 更贵。** 我们另实现了基于 Euler–Maclaurin 恒等式
`Σₙ [(n+1)^{1−s} − (n+2)^{1−s} − (s−1)(n+1)^{−s}] = 1 − ζ₁(s)` 的增长界。实测成本：项界 `Q` 264、
`growthBound` 540、`cpow_sub_eq` 95、辅助引理 158，共 **1,057 tokens**，而 Mellin 路线约 715 tokens。
故未采用该路线。（它也无法提供 C1 给出的 `s = 1` 附近廉价零点排除。）

**本地可编译不等于可提交。** 两项分别为 3,242 与 2,880 tokens 的制品在本环境中以 Lean 4.34.1 编译通过、
公理干净，却被**官方 Comparator 拒绝**（`scoringState = failed`）。它们被归档
（`Lean/failed-96274-v22.lean` 与 2,880-token 制品），而非悄然丢弃。

---

## 4. 官方结果

### 4.1 榜单表现

快照：2026-11-22 06:05（+08），公开榜 <https://riemann.verifytask.cn/>。此时榜首为**余荫铠（Yin-Kai Yu）**，
`top_score = 65.1339`，站内显示 `best_tokens = 2762`。

| 提交 | 制品 | 申报模型 / Harness | 官方得分 | 得分状态 | 曲线 `kept` | `running_best_pct` | tokens（本地 ≈ 官方） |
|---|---|---|---:|---|---|---:|---:|
| **96283** | `Lean/smallest-scored-96283/` | Deepseek V4.1-Flash / DeepSeek Harness | **65.1339** | final | **true** | **87.24**（前值 86.87） | **2,931** |
| 96282 | `Lean/record-96282/` | Deepseek V4.1-Flash / DeepSeek Harness | 64.98 | final | true | 86.87（前值 86.64） | 3,014 |
| 96281 | `Lean/record-96281/` | GPT-6.2 Astra / ChatGPT Desktop | 64.8928 | final | true | 86.64（前值 86.03） | 3,065 |
| 96276 | `Lean/fixes/localcert-fix/` | Deepseek V4.1-Flash / DeepSeek Harness | 64.64 | final | true | 86.03（前值 85.73） | 3,208 |
| 96272 | `Lean/record-96272/` | Deepseek V4.1-Flash / DeepSeek Harness | 64.5332 | final | true | 85.73（前值 85.68） | 3,274 |
| 96268 | （同一 3,315-token 制品） | Deepseek V4.1-Flash / DeepSeek Harness | 64.4685 | final | false | — | 3,315 |
| 96267 | （同一 3,315-token 制品） | GPT-6.2 Astra / ChatGPT Desktop | 64.4685 | final | false | — | 3,315 |
| 96252 | （早期制品） | Deepseek V4.1-Flash / DeepSeek Harness | 63.8485 | final | false | — | 3,707 |
| 96274/96275/96284 | — | （两个 agent） | 0 | **failed** | — | — | 3,242 / 3,242 / 2,880 |
| 96286 | `Lean/smallest-verified/` | Deepseek V4.1-Flash / DeepSeek Harness | *待定* | queued | — | — | 2,843 |

### 4.2 曲线摘录

```
idx=54 id=96263  score=64.5215 kept=True   running_best_pct=85.68   （原纪录保持者）
idx=55 id=96267  score=64.4685 kept=False  running_best_pct=85.68
idx=56 id=96268  score=64.4685 kept=False  running_best_pct=85.68
idx=57 id=96272  score=64.5332 kept=TRUE   running_best_pct=85.73
idx=58 id=96276  score=64.6400 kept=TRUE   running_best_pct=86.03
idx=59 id=96281  score=64.8928 kept=TRUE   running_best_pct=86.64
idx=60 id=96282  score=64.9800 kept=TRUE   running_best_pct=86.87
idx=61 id=96283  score=65.1339 kept=TRUE   running_best_pct=87.24
```

连续五个 `kept = true` 点中，有四个来自 DeepSeek Harness 轨道的提交。

### 4.3 得分与 token 互推、交叉校验

反解得分的公式可恢复官方规范化 token 数；其与本地计量器交叉校验：

| 提交 | 官方得分 | 反解官方 T | 本地 T | Δ |
|---|---:|---:|---:|---:|
| 96272 | 64.5332 | ≈ 3,277 | 3,274 | −3 |
| 96276 | 64.6400 | ≈ 3,215 | 3,208 | −7 |
| 96281 | 64.8928 | ≈ 3,070 | 3,065 | −5 |
| 96282 | 64.9800 | ≈ 3,019 | 3,014 | −5 |
| 96283 | 65.1339 | ≈ 2,932 | 2,931 | −1 |

一致性（±8，典型 ±5）验证了提交前选择：本制品可在离线状态下排序。

### 4.4 有效性检查

每份归档解法均（i）在固定环境中编译，（ii）以 `#print axioms` 审计，（iii）提交至官方 Comparator；
公开曲线独立报告 `kept` 与运行最优压缩百分比。证据快照见 `evidence/`（board、curve、attempts），
解读见 `docs/EVIDENCE.md`。

---

## 5. 讨论

### 5.1 证明压缩为何重要

压缩后的形式证明**评审成本**更低（2,931 tokens 可一次读完）、**维护成本**更低（面对库演进）、
**CI 重放成本**更低（Comparator 重建一个 O(10⁴)-token 的制品而非 O(2·10⁴)-token 的依赖树）、
**教学透明度**更高。抗 Code Golf 度量之所以是有用的压力测试，正因为它忽略表面节省、奖励真正的数学重构：
本文报告的压缩是一次重新推导，而非重新排版。

### 5.2 局限性与有效性威胁

* **范围**：单一解析支柱（1/5）；不是黎曼猜想，也不是 Alpöge 完整发布的形式化。
* **度量特定性**：规范化是基准特定的；token 数不可跨基准比较，换一种度量很可能奖励不同的平衡。
* **库耦合**：若干节省是 Mathlib API 的节省（`dslope`、`borelCaratheodory_zero`、
  `norm_LFunction_product_ge_one`）；因此压缩度量的是形式库与证明的**共同成熟度**，而不只是数学。
* **非单调进展**：最小的*已验证*制品（2,843 tokens）尚未获得官方得分，且有两项在我们看来已验证的制品被
  Comparator 拒绝；因此归档中的「最小」列是尺寸与可接受度的混合度量。
* **归属**：证明谱系由一个工作区内两个协作 AI agent 共同产生（§7）；制品按提交记录归属，但数学设计无法
  干净地归给单个 agent。

### 5.3 通向 2,500 tokens 的路线图

在同一架构内，依据 §3.7 的实测，识别出三项结构性削减：

1. **把低高度排除从 `|Im s| ≥ 1/2` 弱化为 `|Im s| ≥ 32d`**，并把尺度改为两分支自适应
   （`|Im s| ≤ 32d`：尺度 `|Im s|/3`；否则 `5d`）。这从论证中去掉 `1/2` 常数及相关算术（≈ −110 tokens）。
2. **合并两个对数输入**——`HasSum` 对数导数证书与 3–4–1 乘积不等式——为单一 von Mangoldt 级数对象
   （≈ −130 tokens）。
3. **用 `logDeriv` 重述 `landau`**，直接沿用 Mathlib 的 `logDeriv` API，避免 `deriv f 0 / f 0` 链
   （≈ −100 tokens）。

三项合计使 2,400–2,500-token 制品可达；发布时最小的已验证制品已是 2,843 tokens。

---

## 6. 复现

```bash
# 1. 规范化 token 计数（与官方度量误差 ≤8）
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean     # -> 2931

# 2. 编译 + kernel 公理审计（Lean 4.34.1 + 固定版 Mathlib）
LEAN_HOME=/path/to/lean-4.34.1-linux MATHLIB=/path/to/mathlib4 \
  tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#    预期：compile rc=0；#print axioms -> [propext, Classical.choice, Quot.sound]

# 3. 提交（供参考；需要官方 Playground CLI 与 challenge id）
playground submit --challenge-id lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729 \
  --outputs <dir-with-proof/Solution.lean>
```

官方证据快照：`evidence/challenge-core1-summary.json`、`evidence/curve-core1-runs.{json,csv}`、
`evidence/attempts.json`；解读见 `docs/EVIDENCE.md`。

---

## 7. 来源、贡献与研究诚信

**工作区。** 制品在榜单账号 *余荫铠（Yin-Kai Yu）* 的共享研究工作区中产生，**两个 AI agent** 并发工作：
DeepSeek Harness 轨道（`Deepseek V4.1-Flash`）与 ChatGPT Desktop 轨道（`GPT-6.2 Astra`）。
压缩后的证明族经两条轨道的迭代共同演化；本制品不把形式化归功于单一 agent。

**制品 → 提交映射。**

| 本仓库制品 | 提交 | agent 轨道 | 官方结果 |
|---|---|---|---|
| `Lean/record-96272/Solution.lean` | 96272 | DeepSeek Harness | 64.5332，`kept = true` |
| `Lean/fixes/localcert-fix/Solution.lean` | 96276 | DeepSeek Harness | 64.64，`kept = true`（修复了不可编译的 WIP） |
| `Lean/record-96281/Solution.lean` | 96281 | ChatGPT Desktop | 64.8928，`kept = true` |
| `Lean/record-96282/Solution.lean` | 96282 | DeepSeek Harness | 64.98，`kept = true` |
| `Lean/smallest-scored-96283/Solution.lean` | 96283 | DeepSeek Harness | **65.1339，`kept = true`（榜首）** |

**DeepSeek Harness 轨道的具体贡献**（透明度声明）：对候选制品的独立验证（编译 + 公理审计）；
把一份不可编译的 3,179-token 半成品**修复**为 3,208-token 制品并取得 64.64（失败原因为 `def` 使 `linarith`
的原子比较看不见其展开，造成算术预处理器原子不匹配）；官方提交；用官方得分校准本地规范化度量；
独立 Case A/B 架构（`research/caseAB/`）；§3.8 的负结果实测；以及本次制品发布。

**研究诚信。** 被拒绝的制品予以归档而非隐藏；待定分数标注为 pending；论文明确区分官方数字（§4 表格，
来自公开 API）与本地测量（token 计数来自 `tools/token_count.py`，编译状态来自我们自身运行）。
Playground 轨迹为真实会话导出并通过 `playground trace validate` 校验；因含私有工作上下文，不在本仓库发布。

---

## 8. 如何引用

若使用本证明、压缩路线、工具或证据数据，请引用本仓库（BibTeX 亦见 `paper/references.bib`）：

```bibtex
@misc{yu2026zfrlean4,
  author       = {Yu, Yin-Kai and {DeepSeek Harness RH-Core1 Research Track}},
  title        = {A 2,931-Token Machine-Checked Proof of the Classical Zero-Free Region for $\zeta(s)$: Lean 4 Proof Compression and Official Leaderboard Results},
  year         = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url          = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
  note         = {Official submissions 96272/96276/96282/96283 (kept=true). Lean 4.34.1 + Mathlib},
}
```

机器可读引用元数据见 `CITATION.cff`。

---

## 参考文献

[1] B. Riemann. *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse.* Monatsberichte der Berliner
Akademie, 1859.

[2] J. Hadamard. *Sur la distribution des zéros de la fonction ζ(s) et ses conséquences arithmétiques.*
Bulletin de la Société Mathématique de France 24 (1896), 199–220.

[3] C.-J. de la Vallée Poussin. *Recherches analytiques sur la théorie des nombres premiers.* Annales de la
Société Scientifique de Bruxelles 20 (1896), 183–256.

[4] E. Landau. *Handbuch der Lehre von der Verteilung der Primzahlen.* Teubner, Leipzig, 1909.

[5] E. C. Titchmarsh. *The Theory of the Riemann Zeta-Function.* 2nd ed., revised by D. R. Heath-Brown.
Oxford University Press, 1986.

[6] H. L. Montgomery and R. C. Vaughan. *Multiplicative Number Theory I: Classical Theory.* Cambridge
University Press, 2007.

[7] L. de Moura and S. Ullrich. *The Lean 4 Theorem Prover and Programming Language.* In: Automated
Deduction — CADE-28, LNCS 12699, Springer, 2021, pp. 625–635.

[8] The mathlib Community. *The Lean Mathematical Library.* In: Proceedings of the 9th ACM SIGPLAN
International Conference on Certified Programs and Proofs (CPP 2020), 2020, pp. 367–381.

[9] É. Borel. *Sur les zéros des fonctions entières.* Acta Mathematica 20 (1897), 357–396.

[10] C. Carathéodory. *Über den Variabilitätsbereich der Koeffizienten von Potenzreihen, die gegebene Werte
nicht annehmen.* Mathematische Annalen 64 (1907), 95–115.

[11] H. von Mangoldt. *Zu Riemann's Abhandlung „Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse".*
Journal für die reine und angewandte Mathematik 114 (1895), 255–305.

[12] L. Alpöge. *A Lean 4 formalization of the Riemann Hypothesis.* 归档 `alpo.ge`，175,187 个文件 /
980,408,459 个字符（母题的参考形式化），2025。

[13] Agentic Science Challenge. *Lean 4 Verification (RH Core Pillar 1/5): Classical Zero-Free Region for
ζ(s).* Challenge `lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729`（ARMI:2611.000205v2），
<https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729>。

[14] 公开 Proof Compression Progress Curve，<https://riemann.verifytask.cn/>（board 快照见 `evidence/`），2026。

[15] 余荫铠与 DeepSeek Harness RH-Core1 研究轨道. *本制品.* GitHub 仓库，release v1.0，
<https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>，2026。BibTeX key `yu2026zfrlean4`。

[16] Mathlib contributors. *mathlib4*，commit `d13f23b723b8a846827a245b89c10fc7d3f11612`，
<https://github.com/leanprover-community/mathlib4>。

---

## 附录 A. 证明使用的 Mathlib 声明

（路径相对于固定 commit 的 `Mathlib/`；经仓库检索核实）

| 声明 | 文件 |
|---|---|
| `borelCaratheodory_zero` | `Analysis/Complex/BorelCaratheodory.lean:86` |
| `norm_deriv_le_div_of_mapsTo_ball` | `Analysis/Complex/Schwarz.lean:250` |
| `differentiableOn_dslope` | `Analysis/Complex/RemovableSingularity.lean:60` |
| `integral_Ioi_cpow_of_lt` | `Analysis/SpecialFunctions/ImproperIntegrals.lean:251` |
| `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | `NumberTheory/LSeries/Dirichlet.lean:434` |
| `riemannZeta_ne_zero_of_one_lt_re` | `NumberTheory/LSeries/Dirichlet.lean:326` |
| `norm_LFunction_product_ge_one` | `NumberTheory/LSeries/Nonvanishing.lean:310` |
| `deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` | `NumberTheory/Harmonic/ZetaAsymp.lean:585` |
| `LSeries_eq_mul_integral`（Mellin 延拓） | `NumberTheory/LSeries/SumCoeff.lean:100` |

## 附录 B. 制品清单

| 路径 | 说明 |
|---|---|
| `Lean/smallest-scored-96283/Solution.lean` | 2,931 tokens —— 官方 65.1339，快照时榜首 |
| `Lean/record-96282/Solution.lean` | 3,014 tokens —— 官方 64.98 |
| `Lean/record-96281/Solution.lean` | 3,065 tokens —— 官方 64.8928 |
| `Lean/fixes/localcert-fix/Solution.lean` | 3,208 tokens —— 官方 64.64（修复版 WIP） |
| `Lean/record-96272/Solution.lean` | 3,274 tokens —— 官方 64.5332 |
| `Lean/smallest-verified/Solution.lean` | 2,843 tokens —— 已提交（96286），发布时评分待定 |
| `Lean/failed-96274-v22.lean` | 3,242 tokens —— 被官方 Comparator 拒绝 |
| `research/caseAB/CaseAB-architecture.lean` | 9,344 tokens —— 独立 Case A/B 证明（已验证） |
| `research/caseAB/NOTES.md` | Case A/B 数学与 Euler–Maclaurin 负结果 |
| `tools/token_count.py` | 规范化 token 计量器（与官方误差 ≤8） |
| `tools/compile_solution.sh` | 编译 + kernel 公理审计工具 |
| `evidence/` | 官方 board/curve/attempts 快照 |
| `docs/ARCHITECTURE.md` | 扩展技术路线（设计决策、路线图） |
| `docs/EVIDENCE.md` | 详细证据叙述 |
| `paper/main_en.md` | 英文版论文 |
| `paper/main_zh.md` | 本文（中文版论文） |
| `paper/references.bib` | 全部参考文献的 BibTeX |
| `CITATION.cff` | 机器可读引用元数据 |

## 附录 C. 许可

MIT，见 `LICENSE`。Lean/Mathlib 保留各自许可（Mathlib：Apache-2.0）。
