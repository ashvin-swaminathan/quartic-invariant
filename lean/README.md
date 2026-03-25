# Lean 4 Formalization

This directory contains a complete Lean 4 formalization of Theorem 1.3 from the paper "On the Quartic Invariant of Odd-Degree Binary Forms."

## Building

```bash
lake build Modular.MainFull
```

## Structure

The formalization is split across 25 files in `Modular/`, totalling approximately 14,500 lines. The entry point is `Modular/MainFull.lean`, which assembles the three prime cases:

- **p >= 5**: `MainP5.lean`
- **p = 3**: `MainP3.lean`
- **p = 2**: `MainP2.lean` (with supporting files `P2Step5.lean`, `P2CaseB.lean`, `P2CRS.lean`, `P2CarryMax.lean`)

## Verification

The formalization contains **zero `sorry` statements** and **zero `axiom` declarations**. It compiles against Mathlib with no errors.
