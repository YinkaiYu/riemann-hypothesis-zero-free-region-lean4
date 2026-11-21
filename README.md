# Why It Fits — the mathematics behind a record-breaking 2,931-token Lean 4 proof

**A research paper (English + 中文) explaining *why* the compressed proof of the classical zero-free
region works — with the proof, the token accounting, and the official record.**

**Yin-Kai Yu (余荫铠)** · DeepSeek Harness × ChatGPT Desktop collaborative research track
<https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>

[![Lean](https://img.shields.io/badge/Lean-4.34.1-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-d13f23b7-green)](https://github.com/leanprover-community/mathlib4)
[![Kernel verified](https://img.shields.io/badge/kernel--verified-yes-brightgreen)](docs/EVIDENCE.md)
[![Official score](https://img.shields.io/badge/official%20score-65.13-orange)](docs/EVIDENCE.md)
[![License](https://img.shields.io/badge/license-MIT-lightgrey)](LICENSE)

**Paper:** [**English**](paper/main_en.md) · [**中文版**](paper/main_zh.md) · **Cite:** [`CITATION.cff`](CITATION.cff) ·
[`paper/references.bib`](paper/references.bib)

---

## Abstract

The classical zero-free region of the Riemann zeta function is a textbook theorem whose reference Lean 4
formalization occupies 21 files and 21,641 normalized tokens. This paper explains the **mathematics** of a
proof of the same theorem that fits in **one file of 2,931 tokens** and holds the record on the public
proof-compression board (official score 65.1339, curve flag `kept = true`, `running_best_pct` 87.24).
The compression is structural, not cosmetic:

1. **One Mellin identity replaces the growth machinery.** For `Re s > 0`,
   `(s−1)ζ(s) = s(1 − (s−1)R(s))` with `‖R(s)‖ ≤ 1/Re s`. It yields, in ≈715 tokens, both the polynomial
   growth bound used by the logarithmic-derivative estimate *and* a two-line exclusion of zeros near
   `s = 1` that the classical argument needs at low heights.
2. **A recursive zero-peeling lemma replaces zero factorization** (872 tokens). Factor a putative zero
   through Mathlib's analytic divided difference `dslope`, recurse on the divided difference with a halved
   growth constant, close with Borel–Carathéodory. This replaces the reference's finite zero products and
   contour estimates by a single induction — and is the technique published on the benchmark site as
   `core1_borel_dslope`.
3. **The assembly chooses a scale that makes every estimate crude and still decisive.** With
   `a = Re s + 5d`, `d = 2⁻²⁰/log R`, the witness zero sits exactly `5d` from the centre (`x = (5d)⁻¹` is
   sharp), the real-centre pole term is `≤ (4d)⁻¹`, and the negative margin in the 3–4–1 inequality is
   `0.05/d ≥ 5·10⁴ log R` against an `O(log R)` error budget — so pole terms may be bounded by `20d` and one
   `linarith` closes the proof.

**Why it breaks the record**: the two eliminated re-derivations (peeling + Mellin) account for 1,614 of the
remaining 2,931 tokens, while the reference spends its 21 files on exactly those. An ablation confirms the
structural nature of the gain: the natural Euler–Maclaurin route costs **1,057** tokens versus ≈715 for
Mellin (≈50 % more) and yields no cheap zero exclusion.

Official results (public curve): submissions 96272 / 96276 / 96282 / 96283 are `kept = true` record
refreshes — scores 64.5332 → 64.64 → 64.98 → **65.1339**, with `running_best_pct` rising 85.73 → 86.03 →
86.87 → **87.24**; a 2,843-token artifact was submitted with scoring pending at release. Full tables in
[`docs/EVIDENCE.md`](docs/EVIDENCE.md).

---

## Repository guide

| what | where |
|---|---|
| **Paper (English)** — the mathematical structure, section by section | [`paper/main_en.md`](paper/main_en.md) |
| **论文（中文）** — 同样的数学，中文表述 | [`paper/main_zh.md`](paper/main_zh.md) |
| **Record artifact** — 2,931 tokens, official 65.1339, `kept=true` | [`Lean/smallest-scored-96283/Solution.lean`](Lean/smallest-scored-96283/Solution.lean) |
| Record lineage | [`Lean/record-96282/`](Lean/record-96282/), [`Lean/record-96281/`](Lean/record-96281/), [`Lean/fixes/localcert-fix/`](Lean/fixes/localcert-fix/) (3,208-token repair, official 64.64), [`Lean/record-96272/`](Lean/record-96272/) |
| Smallest verified (2,843 tokens, score pending) + rejected artifact | [`Lean/smallest-verified/`](Lean/smallest-verified/), [`Lean/failed-96274-v22.lean`](Lean/failed-96274-v22.lean) |
| Independent Case A/B architecture (validated alternative) | [`research/caseAB/`](research/caseAB/) |
| Token meter + compile/axiom-audit harness | [`tools/`](tools/) |
| Official evidence snapshots | [`evidence/`](evidence/) · [`docs/EVIDENCE.md`](docs/EVIDENCE.md) |
| Extended technical notes | [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) |
| Citation metadata | [`CITATION.cff`](CITATION.cff) · [`paper/references.bib`](paper/references.bib) |

---

## Reproduce in two commands

```bash
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean      # -> 2931
LEAN_HOME=/path/to/lean-4.34.1-linux MATHLIB=/path/to/mathlib4 \
  tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   expected: compile rc=0;  #print axioms -> [propext, Classical.choice, Quot.sound]
```

---

## Provenance

The results were produced under the account *Yin-Kai Yu (余荫铠)* by a collaborative research track in which
two AI agent tracks worked together (DeepSeek Harness / Deepseek V4.1-Flash and ChatGPT Desktop /
GPT-6.2 Astra). The submissions, measurements and this paper are part of that account's record. Rejected
artifacts and pending scores are reported as such (paper §8.2).

## How to cite

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

## License

MIT — see [`LICENSE`](LICENSE). Lean/Mathlib dependencies keep their own licenses (Mathlib: Apache-2.0).
