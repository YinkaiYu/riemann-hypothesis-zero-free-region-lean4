# Core Pillar 5/5 — a verified, compressed proof of functorial resolution of singularities

This repository's second contribution is a **fully machine-checked, consolidated Lean 4 proof** of the
fifth core pillar of the same benchmark family: the functorial resolution of singularities statement in
characteristic zero.

## The result

| item | value |
|---|---|
| frozen target | `AlpogeRHCore5.functorialResolutionCharZero` |
| benchmark baseline ($L_0$) | **1,786,589** normalized tokens (the reference closure) |
| our compressed proof | **1,682,205** normalized tokens in **20 modules** (`Lean/core5/`) |
| compression | **5.8 %** fewer tokens than the reference closure |
| official score implied by the formula | $\approx 50.63$ |
| submission | attempt **97785** (score pending at the time of this release) |

The proof is a *consolidation*: the reference closure is reorganised into twenty `Core5.M01…M20` modules,
with the entry theorem transferring the resolution rule of Alpöge's library to the interface supplied by
the benchmark. The consolidation removes duplicated scaffolding and interface plumbing; the mathematical
content is Alpöge's resolution theorem itself, which we credit explicitly.

## Verification evidence (all files in `evidence/core5/`)

* **Full clean rebuild** from source in a fresh work directory, seeding only a frozen-module stand-in:
  build `rc=0`, `20/20` modules compiled, failed `0`, wall time 547 s (`green20-clean/audit.log`,
  `build-report.json`).
* **Axiom audit**: `#print axioms AlpogeRHCore5.functorialResolutionCharZero` reports exactly
  `[propext, Classical.choice, Quot.sound]` (`green20-clean/audit.log`).
* **Static audit** (independent closure recomputation with the official lexer, cross-checked against a
  second implementation): official closure tokens `1,682,205` on both tools; frozen-interface
  redefinitions `0` (19 frozen names scanned); `sorry`/`admit`/`axiom`/`opaque` `0`; `Solution.lean`
  matches the official template shape.
* **Delivery integrity**: `sha256` manifest matches all 20 delivered modules (`0` mismatches);
  `receipt.json` records `green=true`, `audit_rc=0`, `local_tokens=1682205`.
* The full independent audit protocol, tooling description and risk notes are in
  `docs/core5-audit-report.md`.

## Honest scope notes

* One of the benchmark's five pillars only — not a proof of the Riemann Hypothesis.
* Our local environment cannot obtain the platform's real frozen module; the rebuild uses an
  author-interface stand-in for it, which the receipt labels explicitly. Closure token counting is
  unaffected (frozen modules are excluded from the closure), but semantic equivalence against the real
  frozen module is only finally confirmed on the platform.
* Larger compressions were under audit at release time (candidates at 1,391,010 and 1,400,043 tokens,
  i.e. about 22 % below the baseline). They are not published here until their receipts are green.

## Reproduction

```bash
# files: Lean/core5/proof/Solution.lean + Core5/M01…M20.lean
# evidence: evidence/core5/{receipt.json,audit.log,build-report.json,source-manifest.json}
```

The proof is licensed under the repository's MIT license; the mathematical content (resolution of
singularities) is due to Levent Alpöge's formalization, cited in the papers.
