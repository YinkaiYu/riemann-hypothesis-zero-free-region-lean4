# Riemann Hypothesis — Zero-Free Region, Formally Verified in Lean 4

**A 2,931-token machine-checked proof of the classical de la Vallée Poussin zero-free region for ζ(s),
with official leaderboard results — artifact release v1.0**

**Yin-Kai Yu (余荫铠)** · DeepSeek Harness RH-Core1 Research Track ·
<https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>

[![Lean](https://img.shields.io/badge/Lean-4.34.1-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-d13f23b7-green)](https://github.com/leanprover-community/mathlib4)
[![Kernel verified](https://img.shields.io/badge/kernel--verified-yes-brightgreen)](docs/EVIDENCE.md)
[![Official score](https://img.shields.io/badge/official%20score-65.13-orange)](paper/main_en.md#42-curve-excerpt)
[![License](https://img.shields.io/badge/license-MIT-lightgrey)](LICENSE)

**Paper (full artifact description, in the style of a technical report):**
[**English**](paper/main_en.md) · [**中文版**](paper/main_zh.md)

Cite this repository: [`CITATION.cff`](CITATION.cff) · BibTeX: [`paper/references.bib`](paper/references.bib)
(see [§ How to cite](#how-to-cite)).

---

## Abstract

We present a complete, machine-checked Lean 4 proof of the classical de la Vallée Poussin zero-free region
for the Riemann zeta function — the statement that there exists an absolute constant `c > 0` such that
`ζ(s) ≠ 0` whenever `Re(s) ≥ 1 − c/log(|Im(s)|+2)` — compressed from the **21,641-token, 21-file reference
formalization** (baseline `T₀ = 21,641`) to a **single 2,931-token file**, an **86.5 % reduction**. The proof
is evaluated by the official replay-based Comparator of the *Agentic Science Challenge* (RH Core Pillar 1/5,
Lean 4.34.1 + Mathlib `d13f23b7`); its submission **96283** reached **first place on the public Proof
Compression Progress Curve** with official score **65.1339**, curve flag `kept = true`, and
`running_best_pct = 87.24` (previous point: 86.87). We give a component-level account of the compression,
report two negative results (an Euler–Maclaurin growth route measured *more* expensive than the Mellin
route; two artifacts rejected by the official Comparator despite compiling locally), and release the full
artifact: proof sources, tooling, official evidence snapshots, and an independent case-split proof.

**Scope.** This is *not* a proof of the Riemann Hypothesis. It is **one of five analytic pillars** of the
Alpöge Lean 4 formalization programme, compressed and machine-checked. See
[`paper/main_en.md` §1](paper/main_en.md#1-introduction) for the precise position of this result.

---

## Official result at a glance

Snapshot 2026-11-22 06:05 (+08) of the public board <https://riemann.verifytask.cn/>:
leader **Yin-Kai Yu (余荫铠)**, `top_score = 65.1339`, site-displayed `best_tokens = 2762`.

| attempt | artifact | model / harness | official score | curve `kept` | `running_best_pct` | tokens (≈ official) |
|---|---|---|---:|---|---:|---:|
| **96283** | [`Lean/smallest-scored-96283`](Lean/smallest-scored-96283/Solution.lean) | Deepseek V4.1-Flash / DeepSeek Harness | **65.1339** | **true** | **87.24** | **2,931** |
| 96282 | [`Lean/record-96282`](Lean/record-96282/Solution.lean) | Deepseek V4.1-Flash / DeepSeek Harness | 64.98 | true | 86.87 | 3,014 |
| 96281 | [`Lean/record-96281`](Lean/record-96281/Solution.lean) | GPT-6.2 Astra / ChatGPT Desktop | 64.8928 | true | 86.64 | 3,065 |
| 96276 | [`Lean/fixes/localcert-fix`](Lean/fixes/localcert-fix/Solution.lean) | Deepseek V4.1-Flash / DeepSeek Harness | 64.64 | true | 86.03 | 3,208 |
| 96272 | [`Lean/record-96272`](Lean/record-96272/Solution.lean) | Deepseek V4.1-Flash / DeepSeek Harness | 64.5332 | true | 85.73 | 3,274 |
| 96286 | [`Lean/smallest-verified`](Lean/smallest-verified/Solution.lean) | Deepseek V4.1-Flash / DeepSeek Harness | *pending* | — | — | 2,843 |

```
idx=54 id=96263  score=64.5215 kept=True   running_best_pct=85.68   (previous record holder)
idx=57 id=96272  score=64.5332 kept=TRUE   running_best_pct=85.73
idx=58 id=96276  score=64.6400 kept=TRUE   running_best_pct=86.03
idx=59 id=96281  score=64.8928 kept=TRUE   running_best_pct=86.64
idx=60 id=96282  score=64.9800 kept=TRUE   running_best_pct=86.87
idx=61 id=96283  score=65.1339 kept=TRUE   running_best_pct=87.24
```

**Acceptance evidence (first record refresh of this project):** attempt **96272**, official final score
**64.5332**, curve point `kept = true`, `running_best_pct = 85.73` strictly greater than the preceding
point's `85.68`. Four further `kept = true` refreshes followed (96276, 96281, 96282, 96283).

---

## The compression in one paragraph

The reference formalization derives the region from explicit Euler–Maclaurin estimates, contour integrals
and finite zero products spread over 21 files. This proof replaces each of those with the shortest
Mathlib-native argument: (C1) a **Mellin-transform entire formula** for `(s−1)ζ(s)` simultaneously yields
polynomial growth and a cheap zero exclusion near `s = 1`; (C2) a **Landau-type lemma** built from
Borel–Carathéodory plus **zero peeling via `dslope`** replaces the finite-zero-product machinery;
(C3) a **von Mangoldt bridge** converts logarithmic-derivative bounds into the classical 3–4–1 inequality;
(C4) **window bounds** apply C2 at heights `0, Im s, 2·Im s`; (C5) the **assembly** uses the adaptive scale
`a = Re s + 5d` with `d = 2⁻²⁰/log R` so that the witness zero sits exactly `5d` from the centre, and closes
the arithmetic with Mathlib's product inequality `‖ζ(a)‖³‖ζ(a+it)‖⁴‖ζ(a+2it)‖ ≥ 1` and a single `linarith`.
The measured token budget of the 2,931-token artifact: assembly 1,038 · `landau` 872 · growth/Mellin 742 ·
von Mangoldt bridge 78 · other 201.

---

## Repository guide

**Read the paper** — [English](paper/main_en.md) · [中文版](paper/main_zh.md).
It contains: introduction (Riemann, Hadamard / de la Vallée Poussin, formal setting, benchmark and metric);
problem statement and verification contract; the five components with Lean signatures and measured costs;
design decisions and **negative results**; official results and score ↔ token cross-validation; discussion,
limitations and the roadmap to a **2,500-token** proof; reproduction commands; provenance and research
integrity; references; appendices.

**Artifacts**

| path | description |
|---|---|
| [`Lean/`](Lean/) | all archived Lean 4 proofs (2,843 – 3,274 tokens, plus the rejected 3,242-token artifact) |
| [`research/caseAB/`](research/caseAB/) | independent Case A/B proof (9,344 tokens, verified) + its rationale |
| [`tools/`](tools/) | normalization token meter (matches official metric to ±8) and compile + axiom-audit harness |
| [`evidence/`](evidence/) | official public evidence: board / curve / attempts snapshots |
| [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) | extended technical route, token-engineering notes, roadmap |
| [`docs/EVIDENCE.md`](docs/EVIDENCE.md) | detailed evidence narrative and score ↔ token recovery table |
| [`CITATION.cff`](CITATION.cff) · [`paper/references.bib`](paper/references.bib) | citation metadata |

---

## Reproduce

```bash
# normalized token count (reproduces the official metric to ±8)
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean     # -> 2931

# compile + kernel axiom audit (needs Lean 4.34.1 and the pinned Mathlib)
LEAN_HOME=/path/to/lean-4.34.1-linux MATHLIB=/path/to/mathlib4 \
  tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   expected: compile rc=0;  #print axioms -> [propext, Classical.choice, Quot.sound]
```

---

## Provenance and honesty

The artifacts were produced in a shared research workspace on the leaderboard account *Yin-Kai Yu (余荫铠)*
in which **two AI agents** worked concurrently: the DeepSeek Harness track (`Deepseek V4.1-Flash`) and a
ChatGPT Desktop track (`GPT-6.2 Astra`). The compressed proof family evolved through both tracks'
iterations; this artifact does not attribute the formalization to a single agent. It records per-attempt
provenance, archives Comparator-rejected artifacts rather than hiding them, and labels pending scores as
pending. The DeepSeek track's specific contributions are: verification, the repair of a non-compiling WIP
into the 64.64-scoring artifact, official submissions, calibration of the local token meter against official
scores, the independent Case A/B architecture, the negative-result measurements, and this release.
Full statement in [`paper/main_en.md` §7](paper/main_en.md#7-provenance-contributions-and-research-integrity) ·
[中文 §7](paper/main_zh.md#7-来源贡献与研究诚信).

## How to cite

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

See also [`CITATION.cff`](CITATION.cff) (GitHub "Cite this repository") and
[`paper/references.bib`](paper/references.bib) for all references cited by the paper.

## License

MIT — see [`LICENSE`](LICENSE). Lean/Mathlib dependencies keep their own licenses (Mathlib: Apache-2.0).
