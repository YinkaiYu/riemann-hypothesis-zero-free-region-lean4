# Verifying, Repairing, and Measuring Compressed Formal Proofs

### An independent track on the classical zero-free region of ζ(s) in Lean 4

**Yin-Kai Yu (余荫铠)** · DeepSeek Harness RH-Core1 Research Track ·
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

Proof-compression benchmarks reward small machine-checked formal proofs, but they expose a systematic
methodological gap: a compressed artifact that compiles locally may fail official replay, and a small proof
may be produced by someone other than the submitter. We report an **independent verification, repair and
measurement track** on the classical de la Vallée Poussin zero-free region for `ζ(s)` (Lean 4 / Mathlib;
reference formalization 21 files, 21,641 normalized tokens). Contributions: (i) a verification pipeline
(compile + kernel axiom audit + token measurement) applied to every candidate; (ii) a **repair case study**
— a non-compiling 3,179-token work-in-progress is diagnosed (an arithmetic atom mismatch caused by a `def`
hiding its body from `linarith`) and repaired into a 3,208-token artifact accepted by official replay
(official score **64.64**, curve flag `kept = true`); (iii) a measured record of the compressed lineage we
submitted (2,931–3,315 tokens, official scores 64.47–65.13), including the negative result that local
compilation is necessary but not sufficient (two locally clean artifacts were rejected by the official
comparator); (iv) an independent Case A/B architecture eliminating the low-height zero exclusion; and
(v) an ablation showing the Euler–Maclaurin growth route to be ~50 % more expensive in formal tokens than
the Mellin route. **Attribution.** The compressed proof family and its headline technique (recursive zero
peeling via analytic divided differences and Borel–Carathéodory) were developed in a shared workshop by a
parallel track; the platform's technique note for our submission 96283 is reproduced verbatim with
attribution. This paper claims the verification, repair, submission and measurement work, the Case A/B
architecture, and the ablation — **not** authorship of the technique. **Scope:** one analytic pillar (1/5),
not the Riemann Hypothesis.

---

## Repository guide

| what | where |
|---|---|
| **Paper (EN)** — full text, in research-paper form | [`paper/main_en.md`](paper/main_en.md) |
| **论文（中文）** | [`paper/main_zh.md`](paper/main_zh.md) |
| **Our repair** — the artifact of this track (3,208 tokens, official 64.64, `kept=true`) | [`Lean/fixes/localcert-fix/Solution.lean`](Lean/fixes/localcert-fix/Solution.lean) |
| Submitted artifacts of the shared lineage | [`Lean/`](Lean/) (2,843–3,274 tokens + rejected 3,242-token artifact) |
| **Independent architecture (ours)** — Case A/B, verified | [`research/caseAB/`](research/caseAB/) |
| Tooling — normalization token meter, compile + axiom-audit harness | [`tools/`](tools/) |
| Official evidence — board / curve / attempts snapshots | [`evidence/`](evidence/) · [`docs/EVIDENCE.md`](docs/EVIDENCE.md) |
| Extended technical notes (route, token engineering, roadmap) | [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) |
| Citation metadata | [`CITATION.cff`](CITATION.cff) · [`paper/references.bib`](paper/references.bib) |

---

## What this track actually established

1. **A verification pipeline** that catches hidden `sorry`s and non-standard axioms before submission
   (`compile → #print axioms → token meter → submit`), calibrated against official scores to ±8 tokens.
2. **A repair case study** (paper §4): the failing step is an arithmetic **atom mismatch** — `def D z := …`
   keeps its body invisible to `linarith`, while a `HasSum.nonneg` certificate mentions `(LSeries …).re`.
   One `change` line re-expresses the certificate in `D` atoms; the artifact compiles (3,208 tokens) and
   scores **64.64** with `kept = true`.
3. **The evaluation boundary** (paper §4.4): two artifacts (3,242 and 2,880 tokens) compile locally with
   clean axioms yet were **rejected by the official comparator** — external replay is a distinct confidence
   level. Both are archived, not hidden.
4. **An independent derivation** (paper §5.2): a Case A/B architecture that removes the low-height zero
   exclusion by relocating the Landau estimate to the pole side (verified, 9,344 tokens, clean axioms).
5. **An ablation** (paper §6.4): the Euler–Maclaurin growth route costs **1,057 tokens** versus ≈715 for
   the Mellin route (~50 % more), with no cheap zero exclusion — evidence that compression is structural.

Official results of the submissions recorded here (public curve, <https://riemann.verifytask.cn/>):
attempt **96272** — final score 64.5332, `kept = true`, `running_best_pct` 85.68 → **85.73**;
attempt **96276** — final score **64.64**, `kept = true`, 85.73 → **86.03** (this track's repair);
later submissions of the shared lineage reached 64.98 and 65.13 (`kept = true`). Full tables in
[`docs/EVIDENCE.md`](docs/EVIDENCE.md).

---

## Reproduce

```bash
python3 tools/token_count.py Lean/fixes/localcert-fix/Solution.lean        # -> 3208
LEAN_HOME=/path/to/lean-4.34.1-linux MATHLIB=/path/to/mathlib4 \
  tools/compile_solution.sh Lean/fixes/localcert-fix/Solution.lean demo
#   expected: compile rc=0;  #print axioms -> [propext, Classical.choice, Quot.sound]
```

---

## Provenance and integrity

Two AI agents worked concurrently on the same benchmark account: the **DeepSeek Harness** track
(`Deepseek V4.1-Flash`, this work) and a **ChatGPT Desktop** track (`GPT-6.2 Astra`). The compressed proof
family — and its headline technique, machine-summarized by the platform as `core1_borel_dslope` — is the
parallel track's product; the note is reproduced in the paper with attribution, because the platform
synthesized it for a submission of our account (it is *a record of a submission*, not a claim of
authorship). This repository claims the verification, repair, submission and measurement work, the
independent Case A/B architecture, the ablation, and this release. Rejected artifacts and pending scores
are reported as such.

## How to cite

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

## License

MIT — see [`LICENSE`](LICENSE). Lean/Mathlib dependencies keep their own licenses (Mathlib: Apache-2.0).
