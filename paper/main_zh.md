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

### 4.1 纪录 1 —— 3,274 tokens（官方 64.5332；站点 3,089 tok，−85.7%）

**（B）原版瓶颈。** 参考形式化（Alpöge，21 个文件）要得到 `ζ₁` 在假想零点附近的 Landau 型估计
`−Re(f′/f)`，必须把圆盘内**全部**零点收进有限乘积 `Π(w−ρ)^{m(ρ)}`，逐因子证明求导引理
（`hasDerivAt_prod_sub_pow`），并在多个文件间传递手写的柯西/Jensen 估计。压缩谱系先用五个独立标量引理
替代这套库——`landau`(873)、`scaledWindow`(269)、`triple`(248)、`zeroHeight`(114)、`poleTerm_le`(66)
——再加 643 tokens 的总装；这些**接口**正是此后要继续偿还的成本。

**（M）核心数学推导。** 引入 `nld(f,z) := −Re(f′(z)/f(z))`，以**对增长常数的强归纳**取代零点乘积：
设 `f` 在 `B̄(0,1/2)` 上全纯、`f(0) ≠ 0`、`‖f(w)‖ ≤ B‖f(0)‖`，且 `B̄(0,1/6)` 内所有零点满足 `Re ρ ≤ 0`，
则对一切满足 `B < 2ⁿ` 的 `n` 证明

```
x + nld(f,0) ≤ 24·(log B + 1)，     x = 0 或 x = Re((−ρ)⁻¹)（ρ ∈ B̄(0,1/6) 为某零点）。
```

剥离步：在零点 `ρ₀` 处令 `g(w) := dslope(f,ρ₀)(w)`，则 `f(w) = (w−ρ₀)g(w)`、`f(0) = −ρ₀g(0)`；
`g` 的增长常数**恰为一半**，`B → B/2`（到 `ρ₀` 的距离在最大模界中抵消一个因子），随后对 `g` 继续归纳。
终止步：内盘无零点时 `f` 有解析对数 `u` 且 `Re u ≤ log B`，Borel–Carathéodory 给出 `|u′(0)| ≤ 2(Re u(0))/R`，
再做一次 Lipschitz 估计转化为 `nld(f,0)` 的界。

**（C）为何能压到此比例。** 剥离引理（873 tokens）替换参考实现的整座零点分解库；第二处大替换是 Mellin
增长界（≈742 tokens），§5 的消融表明它比 Euler–Maclaurin 路线省约 50%。站点记录该制品为 **3,089 site
tokens = −85.7%**，技巧标签为「Perron/Mellin 围道精简 + grind 自动收口」，论文式推导题为
《Borel–Carathéodory 与解析差商（dslope）递归零点剥离》；破纪录瞬间与该推导已归档于 `evidence/figures/`。

### 4.2 纪录 2 —— 3,208 tokens（官方 64.64；站点 3,024 tok，−86.0%）

**（B）原版瓶颈。** 纪录 1 之后最大的可拆接口是 3–4–1 证书被做成独立引理 `triple`(248)：其陈述、
逐点不等式 `3+4cos θ+cos 2θ ≥ 0` 的证明、以及总装中的调用，都在付接口成本；而总装(643) 还要按名引用它。

**（M）核心数学推导。** 该证书是**逐项**陈述：von Mangoldt 级数的第 n 项为
`Λ(n)n^{−a}(3+4cos(t log n)+cos(2t log n)) ≥ 0`。因此它可以在总装内部一次性作为 `HasSum.nonneg` 对象产生，
无需独立引理；同时让 `D(z) = Re Σ Λ(n)n^{−z}` 的两处使用（证书与窗口界）谈论同一原子——`def` 使
`linarith` 看不见其展开体，故需以 `change` 把证书的 `(LSeries …).re` 原子改写成目标中的 `D` 原子。
（该原子失配也是未修复的 3,179-token 前身无法编译的原因。）

**（C）为何能压到此比例。** 实测：`triple`(248) 消失，总装 643 → 819（+176），`D` 21 → 27（+6）：
净 **−66** tokens，3,274 → 3,208。

### 4.3 纪录 3 —— 3,065 tokens（官方 64.8928；站点 2,762 tok，−87.2%）

**（B）原版瓶颈。** 还有两个引理在重复 Mellin 恒等式已包含的信息：`zeroHeight`(114) 排除
`Re z ∈ (3/4,1)`、`|Im z| ≤ 1/2` 的零点；`poleTerm_le`(66) 给出粗糙界 `Re((z−1)⁻¹) ≤ 2`；二者都独立陈述、
独立证明、独立实例化。

**（M）核心数学推导。** Mellin 恒等式**直接**给出低高度排除：`ζ₁(z) = 0` 蕴含 `(z−1)R(z) = 1`，故
`Re z ≤ |z−1|`；结合 `Re z ≥ 3/4` 在总装内部几行即得 `|Im z| ≥ 1/2`。同一恒等式还给出**锐化**极点界：
`Re((a+iγ−1)⁻¹) = (a−1)/((a−1)²+γ²) ≤ 5d/((4d)²+1/4) ≤ 20d`，粗糙的 `≤ 2` 引理因此不再必要。
两项事实都成为已携带的 `remainder` 对象的推论。

**（C）为何能压到此比例。** 实测：`zeroHeight`(114) 与 `poleTerm_le`(66) 消失，总装 819 → 876（+57）：
净 **−143** tokens，3,208 → 3,065。

### 4.4 纪录 4 —— 3,014 tokens（官方 64.98；站点 2,842 tok，−86.9%）

**（B）原版瓶颈。** 窗口估计仍作为引理 `scaledWindow`(263) 存在，并有**三次**实例化（高度 `0`、`Im s`、
`2·Im s`）；每次实例化都付接口与传参成本，总装(876) 还要按名引用它。

**（M）核心数学推导。** 窗口估计就是在三个中心 `a + iv` 上应用剥离引理，增长比 `B = R⁸/‖ζ₁(a+iv)‖`；
由于增长假设（`entireGrowth` on `Re ≥ 1/2`）与纪录 3 的锐化极点不等式对三个中心相同，三次应用可以内联并共享
这两个参数。数学上没有变化；三次使用变成对同一引理的三个内联 `have` 绑定。

**（C）为何能压到此比例。** 实测：`scaledWindow`(263) 消失，总装 876 → 1,084（+208）：净 **−51** tokens，
3,065 → 3,014。

### 4.5 纪录 5 —— 2,931 tokens（官方 65.1339；站点 2,762 tok，−87.2%）

**（B）原版瓶颈。** 桥引理 `good`(94) 与缩写 `D`(21) 仍在 Mellin/剥离结果与总装之间做中介：对数导数形式
`ζ₁′/ζ₁ = (z−1)⁻¹ − Σ Λ(n)n^{−z}` 被作为独立陈述证明，而 `D` 又是算术需要多经过的一个对象。

**（M）核心数学推导。** 总装围绕**单一规范化复恒等式**重组：整函数公式 `ζ₁(s) = s(1 − (s−1)R(s))` 成为
`ζ₁` 唯一展开处，桥被简化为把 von Mangoldt 恒等式代入总装自身的表达式，于是「独立桥引理 + `D` 缩写」的拆分
不再必要——算术直接使用 `LSeries (Λ)` 的实部。

**（C）为何能压到此比例。** 实测：`good` 94 → 78（−16），`D` 消失（−21），总装 1,084 → 1,038（−46）：
净 **−83** tokens，3,014 → 2,931。2,931-token 文件共 16 个顶层块：总装 1,038、剥离 872、Mellin 742、桥 78、
见证/胶水 201。
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
