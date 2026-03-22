# On the Quartic Invariant of Odd Degree Binary Forms

**Author:** Ashvin A. Swaminathan

## Summary

We determine the squarefree part of the scalar factor that arises when the quartic invariant of the generic binary form of odd degree $2n+1$ is expressed as the discriminant of the unique quadratic covariant $(F,F)_{2n}$.

**Main Theorem.** For every integer $n \geq 1$ and every prime $p$:

1. $v_2(S(n))$ is always even.
2. For every odd prime $p$, $v_p(S(n))$ is odd if and only if $n+2$ is a power of $p$.

Equivalently, $\mathrm{sqf}(S(n)) = a(n+2)$, where $a(m) = p$ if $m$ is a power of an odd prime $p$, and $a(m) = 1$ otherwise. This is [OEIS A155457](https://oeis.org/A155457).

For $n = 1$ (binary cubics), this recovers the classical identity $\mathrm{disc}(H(F)) = -3 \cdot \mathrm{disc}(F)$.

## Contents

### `paper/`
The paper draft (`paper_v2.tex` and `references.bib`).

### `computation/`
A Jupyter notebook (`verification.ipynb`) that independently verifies every stated formula and lemma by direct symbolic computation for $n = 1, \ldots, 30$ and all primes.

### `lean/`
A Lean 4 formalization of the main theorem. The file `Complete.lean` (~6000 lines) is a single self-contained proof with zero `sorry` statements and zero `axiom` declarations, compiling against Mathlib. See `lean/README.md` for details.

## AI-Assisted Workflow

This project was completed using an AI-assisted research workflow:

- **Claude Code** (Anthropic): numerical experimentation, proof construction, paper writing, and Lean proof engineering
- **Aristotle** (Harmonic): automated Lean 4 theorem proving for key lemmas

The workflow is described in detail in Section 7 of the paper.
