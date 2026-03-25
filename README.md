# On the Quartic Invariant of Odd-Degree Binary Forms

**Author:** Ashvin A. Swaminathan

## Summary

We determine the squarefree part of the scalar factor that arises when the quartic invariant of the generic binary form of odd degree $2n+1$ is expressed as the discriminant of the unique quadratic covariant $(F,F)_{2n}$.

**Main Theorem (Theorem 1.3).** For every integer $n \geq 1$ and every prime $p$:

1. $v_2(S(n))$ is always even.
2. For every odd prime $p$, $v_p(S(n))$ is odd if and only if $n+2$ is a power of $p$.

Equivalently, $\mathrm{sqf}(S(n)) = a(n+2)$, where $a(m) = p$ if $m$ is a power of an odd prime $p$, and $a(m) = 1$ otherwise. This is [OEIS A155457](https://oeis.org/A155457).

For $n = 1$ (binary cubics), this recovers the classical identity $\mathrm{disc}(H(F)) = -3 \cdot \mathrm{disc}(F)$.

## Contents

### `paper/`
- `paper_v2.tex` — the paper source
- `references.bib` — bibliography

### `computation/`
- `verification.ipynb` — a Jupyter notebook that independently verifies every stated formula and lemma by direct symbolic computation for $n = 1, \ldots, 30$ and all primes, including a complete step-by-step check of the $p=2$ proof (26 individual claims verified)

### `lean/`
A complete Lean 4 formalization of the main theorem, compiling against Mathlib.

- **25 files** in `Modular/`, totalling approximately **14,500 lines**
- **Zero `sorry` statements**
- **Zero `axiom` declarations**
- Entry point: `Modular/MainFull.lean`

The formalization covers all three prime cases:

| Case | File(s) | Description |
|------|---------|-------------|
| $p \geq 5$ | `MainP5.lean` | Valuation shift formula + deformation witness |
| $p = 3$ | `MainP3.lean`, `P3Witness.lean` | Ternary digit recursion for non-prime-power case |
| $p = 2$ | `MainP2.lean`, `P2Step5.lean`, `P2CaseB.lean`, `P2CRS.lean`, `P2CarryMax.lean` | Gauss's lemma, ultrametric/mod-4 analysis, CRS witness |

Supporting infrastructure:

| File | Purpose |
|------|---------|
| `Defs.lean` | Core definitions ($\alpha$, $\beta$, $A_n$, $B_n$, $C_n$, $\Delta_n$, $S(n)$) |
| `GaussMV.lean` | Gauss's lemma for multivariate polynomials over $\mathbb{Z}$ |
| `CentralDom.lean` | Strict central dominance of scalar$_{AB}$ (all primes) |
| `ScalarBounds.lean` | Coefficient divisibility and $b_k$ formula |
| `CoeffDivPP.lean` | Coefficient divisibility for prime powers |
| `CoeffCongP2.lean` | Mod-2/mod-4 congruences for $p=2$ |
| `CoeffExtract.lean` | MvPolynomial coefficient extraction lemmas |
| `P2CarryMax.lean` | Binary carry combinatorics (Kummer's theorem) |
| `Rank1Collapse.lean` | Rank-1 structure of primitive part |
| `Deformation.lean`, `DeformAssembly.lean` | Deformation witness construction |
| `KummerCarry.lean` | Kummer carry-counting infrastructure |
| `Mod4Lift.lean` | Mod-4 lifting lemmas |
| `ContentBasics.lean` | Basic content/evaluation lemmas |
| `PairSpec.lean` | Pair specialization utilities |
| `BEvalDiv.lean` | Evaluation divisibility |
| `OffCenter.lean` | Off-centre index analysis |
| `MainFull.lean` | Final assembly combining all cases |

#### Building the formalization

```bash
cd lean
lake build Modular.MainFull
```

Requires Lean 4 and Mathlib. See `lean-toolchain` for the exact Lean version.

## AI-Assisted Workflow

This project was completed using an AI-assisted research workflow:

- **Claude Code** (Anthropic): numerical experimentation, proof construction, paper writing, and the bulk of the Lean formalization across all three prime cases
- **Codex** (OpenAI): patched proof-engineering gaps in the $p=2$ Lean formalization, including the key combinatorial lemma on binary carry maximizers
- **Aristotle** (Harmonic): automated Lean 4 theorem proving for targeted lemmas

The workflow is described in detail in Section 7 of the paper.

## License

This work is released under the MIT License.
