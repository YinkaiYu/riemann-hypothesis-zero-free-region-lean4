# core5 终局树独立审计 — core1recover（审计员），2026-11-22 15:35

> 状态：**等待 green 树**（c5resume 修复中：adapted-min 20 模块中 3 compiled / 1 failed / 16 blocked）。
> 本文档含审计合同、工具、命令、以及当前快照；green 树到手后按 §4 填表即完成。

## 1. 审计合同（lead 指定 4 项）
1. **官方 closure token**：recompute，非全树 `measure.py`、非站点显示口径。
2. **`#print axioms AlpogeRHCore5.functorialResolutionCharZero`**（官方 entry target）= 必须恰为 `[propext, Classical.choice, Quot.sound]`。
3. **无 sorry / 无自定义 axiom / 无 opaque**：closure 源码 + kernel 审计双查。
4. **`adapt_tree.py` 后 frozen 接口重定义 = 0**（19 个 `FunctorialResolution.*` 冻结名）。

附带（合同外但必须）：closure 不含 `Development.ResolutionOfSingularities.Statements`、不含外部 `ComparatorChallenges.*`；`Solution.lean` = 官方模板形状；模块 sha256 manifest 与提交包一致。

## 2. 工具（已就绪，本目录）
- `audit_static.py`（纯 Python，无 Lean 槽位）：按官方 `entry/assemble.py` 语义独立 BFS closure，用官方 lexer（`curve/core1/opt-weighted/lex.py`）计数；并与团队 `core5-fleet/endgame/submission_tools.py` 交叉核对；同时查 frozen 重定义 / sorry / axiom / Solution 模板。
  用法（WSL）：
  ```bash
  cd /mnt/c/Users/Newton/Documents/LigroupIOP/lib/RH-deepseek
  python3 core5-final-audit/audit_static.py \
    --tree <adapted-tree> --entry-module <entry-module> \
    --out core5-final-audit/<tag>-static.json
  ```
- `audit_build.sh`（占 1 个 lean 槽位，独立新 work 目录全量 build + platform-style axiom audit + 打包）：
  ```bash
  bash core5-final-audit/audit_build.sh <adapted-tree> <entry-module> <tag> [extra-green-cache]
  # 内部 = core5-fleet/endgame/validate_entry.py，frozen 替身 cache:
  #   /home/yyk/rh-deepseek/core5-consolidate/frozen-stub/cache
  # 产出: core5-final-audit/<tag>/{receipt.json,audit.log,delivery/proof,source-manifest.json}
  ```
  注意：`validate_entry.py` 需要 `--src` 是**已 adapt** 的树（frozen 名已剥离、已 import `ComparatorChallenges.RHCore5Defs`、含官方模板 Solution.lean）。
- 官方工具对照：
  - `RH-playground/.playground-work/curve/core5/entry/assemble.py`：官方 closure/计数（源树需按官方 template 的 `HironakaTheorem` entry；用于 cross-check 语义）。
  - `.../core5/entry/check.py`：作者接口模式（`Development...Statements`）的 `#print axioms`。
  - `.../core5/diagnosis/measure.py`：kernel-reach.tsv 的全树 measure —— **不是官方 closure 数**，仅供诊断。

## 3. 当前快照（2026-11-22 15:35，红树，不提交）
| 项 | 值 |
|---|---|
| 候选 | `core5-resume/work/adapted-min`（= `core5-resume/final-adapt-min` 源） |
| entry module | `Core5.M19FunctorialResolution` |
| modules | 20 |
| **官方 closure tokens（本地重算）** | **1,497,930**（submission_tools 交叉核对一致） |
| frozen 重定义 | 0 |
| sorry/admit/axiom | 0 |
| Solution 模板 | imports_frozen ✓ / namespace ✓ / theorem ✓ / 无 author-iface import ✓ |
| build | **rc≠0**：compiled 3 / failed 1（M04DescentInterfaces）/ blocked 16；无 olean Solution → axiom audit 未执行 |
| 记录对比 | core5 当前纪录（Pi, 见 `ref/board-resume.json`）：**1,164,xxx–1,248,597 级**；本快照 1.50M → 差 ~300k，**不可提交** |


## 3b. 提交候选预审计快照（2026-11-22 16:00，纯静态；供 lead 16:15 决策）
| 候选 | adapted tree | entry | official closure | frozen=0 | sorry/axiom=0 | Solution 模板 | build/axioms |
|---|---|---|---:|---|---|---|---|
| **green20（保底）** | `core5-resume/work/adapted-green20` | `Core5.M19FunctorialResolution` | **1,682,205** | ✓ | ✓ | ✓ | 待 receipt（c5resume 16:00-16:05） |
| **c2z adapted16（次选）** | `core5-resume/work/adapted16` | `FunctorialResolution.C15` | **1,400,043** | ✓ | ✓ | ✓ | C01 failed，修中 |
| adapted-min（备份） | `core5-resume/work/adapted-min` | `M19` | 1,497,930 | ✓ | ✓ | ✓ | M04 failed（历史） |
预期 score（官方公式 L0=1,786,589）：1,682,205 ⇒ **50.63**；1,400,043 ⇒ **52.51**；1,271,000 ⇒ **53.35**（Pi 纪录）。

## 3c. 审计执行流程（任一棵 receipt 落地后立即跑，~5-15 min）
```bash
# 1) 静态（秒级）：closure 双工具交叉 + frozen 重定义 + sorry/axiom + 模板
cd /mnt/c/Users/Newton/Documents/LigroupIOP/lib/RH-deepseek
python3 core5-final-audit/audit_static.py --tree <adapted-tree> --entry-module <entry> \
        --out core5-final-audit/<tag>-static.json
# 2) 独立 build+axioms（用 c5resume 的 green cache 加速；--extra-reuse 指向其 cache）
bash core5-final-audit/audit_build.sh <adapted-tree> <entry> <tag> <c5resume-validate-cache>
#    产出 <tag>/receipt.json（green/audit_rc/axioms/local_tokens）+ audit.log + delivery/proof
# 3) 判定：green==true 且 axioms==[propext,Classical.choice,Quot.sound] 且
#    static.official_closure_tokens == receipt.local_tokens（±0，同口径）且 frozen=0/sorry=0 ⇒ 可提交
```
注意：`audit_build.sh` 必须用**独立 work 目录**（不复用 c5resume 的 work），只用其 **cache oleans** 提速；receipt 里 frozen 替身模式须保留说明（平台真 frozen 模块无法本地取得，author-interface 替身是团队既定做法）。


## 3d. 审计结论（2026-11-22 15:45）：green20 = 【可提交】
**候选**：`/home/yyk/rh-deepseek/core5-resume/work/adapted-green20`（entry `Core5.M19FunctorialResolution`）
**交付包**：`RH-deepseek/core5-resume/final-adapt-green20/{receipt.json,audit.log,delivery/proof,source-manifest.json}`

| 检查 | 结果 | 证据 |
|---|---|---|
| official closure tokens | **1,682,205** | `audit_static.py` 与 `submission_tools.py` 双工具一致；manifest/receipt 同数 |
| modules / closure 完整性 | 20 模块，全部在 closure；无 MISSING | `preaudit-green20.json`、`green20/receipt.json` |
| Solution 模板 | import frozen ✓ / namespace ✓ / theorem ✓ / 无 author-iface ✓ | `audit_static` |
| frozen 接口重定义 | **0** | `audit_static`（19 冻结名扫描） |
| sorry / admit / axiom / opaque | **0** | `audit_static`（closure 源码扫描） |
| 交付包 sha256 | **20/20 与 source-manifest 一致，0 mismatch** | `audit_delivery_green20.sh` |
| 独立 build | **rc=0，20/20** | 我的新 work 目录 `green20-work`（非 c5resume work） |
| `#print axioms AlpogeRHCore5.functorialResolutionCharZero` | **`[propext, Classical.choice, Quot.sound]`** | `green20/audit.log`：`'AlpogeRHCore5...' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| receipt | `green=true, audit_rc=0, axioms=[Classical.choice, Quot.sound, propext], local_tokens=1,682,205` | `green20/receipt.json` |
| 预期 score（官方公式） | **≈50.63** | T=1,682,205, L0=1,786,589 |

**判定：可提交（保底候选）。**
备注：
- c5resume receipt 的 `axiom_ok:false` 是其 `sorted` 比较 bug（他们已声明）；原始 audit 行正确，我的独立 receipt 同样显示该 bug 但 axioms 集合正确 → **以原始 audit 行为准**。
- 另起**全量 clean rebuild**（只 seed frozen 替身、强制重编 20 模块）作为金标准，ETA 15:57，结果追加到 `green20-clean/receipt.json`。
- c2z adapted16（1,400,043 ⇒ score 52.51）的 C01 仍未绿；一旦 receipt 落地可 3 min 内出同等审计（更优候选）。

## 3e. 金标准 clean rebuild 结果（2026-11-22 15:49）——证据链闭合
为排除 cache 依赖，另起**全新 work 目录、只 seed frozen 替身 olean、强制重编全部 20 模块**：
- `green20-clean-clean-work`：**build rc=0，wall=547s，compiled=20/20，failed=0**；
- **audit rc=0**，原始行：`'AlpogeRHCore5.functorialResolutionCharZero' depends on axioms: [propext, Classical.choice, Quot.sound]`；
- `local_tokens = 1,682,205`（与 cached 运行、仓库 receipt/manifest 完全一致）；
- receipt：`core5-final-audit/green20-clean/receipt.json` / `green20-clean/audit.log`。
⇒ **已提交 attempt 97785 的内容通过"从源码全量重编"级独立验证，无 cache 风险。**

## 3f. 更优候选静态预审计（2026-11-22 15:55，纯静态；未构建）
| 候选（`core5-resume/work/`） | entry | official closure | frozen=0 | sorry/axiom=0 | 模板 | 状态/预期 score |
|---|---|---:|---|---|---|---|
| **adapted-c1-static**（C1 系最优） | `Core5.M19FunctorialResolution` | **1,391,010** | ✓ | ✓ | ✓ | 未绿（c5resume：static scan 24 issues）；修绿则 score≈**52.72** |
| adapted-c1-orig（C1 原树） | 同上 | 1,441,579 | ✓ | ✓ | ✓ | 未绿；score≈52.08 |
| adapted-c1-tree2（minimizer3） | 同上 | 1,457,273 | ✓ | ✓ | ✓ | M01 已绿，全链未绿；score≈51.98 |
| adapted16（c2z 官方布局） | `FunctorialResolution.C15` | 1,400,043 | ✓ | ✓ | ✓ | C01 failed；score≈52.51 |
| adapted-green20（**已提交 97785**） | `Core5.M19FunctorialResolution` | 1,682,205 | ✓ | ✓ | ✓ | **green，已独立+clean 审计 ⇒ 可提交**；score≈50.63 |

**待命流程**：任一棵交付 `receipt.json`（green=true, audit_rc=0）→ 我跑
`audit_build.sh <adapted-tree> <entry> <tag> <其 green cache>`（3–10 min，seed frozen 替身 + 复用其 cache 加速；必要时再跑 `audit_build_clean.sh` 金标准）→ 报 lead "可提交/不可提交"。
优先顺序：**adapted-c1-static（52.72）> adapted16（52.51）> 保持 97785（50.63）**。

## 4. green 树到手后填表（审计执行）
| # | 检查 | 命令 | 期望 | 实测 |
|---|---|---|---|---|
| 1 | 官方 closure token | `audit_static.py` | 与提交包 `local_tokens`/`source-manifest.json` 一致；< 记录 | 待 |
| 2 | modules / closure 完整性 | 同上 | 无 MISSING、无 author-iface/foreign ComparatorChallenges | 待 |
| 3 | frozen 重定义 | 同上 | 0 | 待 |
| 4 | sorry/axiom/opaque | 同上 | 0 | 待 |
| 5 | Solution 模板 | 同上 | 全 ✓ | 待 |
| 6 | 独立 build（新 work dir） | `audit_build.sh` | `green: true`, `audit_rc: 0` | 待 |
| 7 | axiom audit | `receipt.json.axioms` + `audit.log` | `[propext, Classical.choice, Quot.sound]` | 待 |
| 8 | kernel 层面 | `check.py --official-interface`（若平台 frozen olean 可得）或 stand-in 模式记录偏差 | 作者接口替身模式须在 receipt 标注 | 待 |
| 9 | sha256 | 比 `source-manifest.json` 与提交 zip | 一致 | 待 |

## 5. 风险与保留意见
- 本地无平台真实 `ComparatorChallenges/RHCore5Defs.olean`，用**作者接口 `Statements.lean` 编译的替身**（`core5-consolidate/frozen-stub/cache`）。closure 计数不受影响（frozen 模块被跳过），但**语义等价性**只能在平台真实 frozen 模块下最终确认；receipt 必须标注 author-interface 模式（既有 `entry/full-author/receipt.json` 为此模式先例）。
- 官方 token 口径 = closure（不含 frozen/externals/imports/comments/whitespace），已由 `submission_tools` 复刻并与本目录独立实现一致；提交前建议再用 `entry/assemble.py` 对"官方模板 + 树内 HironakaTheorem entry"路径交叉一次（若树改名 entry，则以平台 config 的 solution_module 行为为准，需 lead 确认）。
- 若 green 树 token ≥ 1,370,943（旧记录）或 ≥ Pi 当前 1,164,000 级，则**不具提交价值**；审计应同时给出"是否值得提交"的结论。
