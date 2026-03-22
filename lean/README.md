# Lean Formalization: On the Quartic Invariant of an Odd Degree Binary Form

A complete Lean 4 formalization of **Theorem 1.3** from the paper.

## Main Result

**Theorem 1.3.** Let S(n) = cont(Delta_n) be the integer content of the discriminant of the quadratic covariant of the quartic invariant of the generic binary (2n+1)-form. For every prime p and every n >= 1:

- **p = 2:** v_2(S(n)) is always even.
- **Odd primes p >= 5:** v_p(S(n)) is odd if and only if n + 2 is a power of p.

(The cases p = 3 are excluded since 3 does not divide S(n) for degree reasons.)

## Files

### Self-contained formalization

- **`Complete.lean`** -- The entire formalization in a single file (~5800 lines). Imports only Mathlib. Contains all definitions, all lemmas, and the final theorems with complete proofs.

### Axiom-based files showing logical structure

- **`MainTheorem.lean`** -- States the main theorem for odd primes p >= 5 and assembles the proof from component results declared as axioms. Each axiom is proved in full in its referenced component file (and in `Complete.lean`). Includes `main_theorem_full`, combining the odd-prime and p = 2 cases.
- **`PrimeTwo.lean`** -- The p = 2 case: proves `v2_always_even`, that v_2(S(n)) is even for all n >= 1. Handles the non-power-of-2 and power-of-2 subcases separately, using the stronger rank-1 collapse (divisibility by 2^{2e+2} rather than 2^{2e+1}).

### Component files (for reading individual proofs)

| File | Contents |
|------|----------|
| `Definitions.lean` | Core definitions: alpha, beta, gamma, A_n, B_n, C_n, Delta_n, mvContent, S(n), phi, b_k_val, e_central |
| `ContentBasics.lean` | S(n) divides every evaluation of Delta_n; upper/lower bounds on v_p(S) via evaluations and coefficients |
| `PairSpecialization.lean` | Under phi_k (k not in {n, n+1}), A_n and C_n vanish, so Delta(phi_k) = B(phi_k)^2 |
| `ScalarCoeffBounds.lean` | If p^e divides all coefficients of A_n, B_n, C_n, then p^{2e} divides all coefficients of Delta_n |
| `CentralDominance.lean` | The central index i = n achieves the minimum p-adic valuation among scalar coefficients |
| `OffCenterWitness.lean` | When n+2 is not a prime power of p, an off-center index k_0 achieves the minimum v_p(b_k) |
| `BEvalDivisibility.lean` | p^{e_central} divides B_eval(n, c) for all c when n + 2 = p^k |
| `Rank1Collapse.lean` | Rank-1 cancellation: B'^2 - 4A'C' vanishes mod p, yielding p^{2e+1} divides Delta_eval |
| `KummerCarryAnalysis.lean` | Kummer carry analysis for off-center binomial coefficients |
| `Deformation.lean` | Constructs a specialization c with v_p(Delta_eval(n, c)) = 2e+1 exactly |
| `BinomialGCD.lean` | gcd of C(m, r) for 1 <= r < m equals p if m is a prime power p^k, else 1 |
| `CancellationFreeBn.lean` | Closed-form formula for b_k, the diagonal coefficient of B_n |

## Proof Architecture

The proof splits into two directions.

### Direction 1: v_p(S(n)) is even when n+2 is not a power of p

(`even_of_not_prime_power` in Complete.lean / MainTheorem.lean)

1. Find an off-center index k_0 (not in {n, n+1}) with minimum v_p(b_{k_0}) = e.
2. **Upper bound:** Specialize Delta_n at phi_{k_0}. Since A_n and C_n vanish, Delta(phi_{k_0}) = b_{k_0}^2, giving v_p(S) <= v_p(b_{k_0}^2) = 2e.
3. **Lower bound:** Central dominance + scalar coefficient bounds give p^{2e} dividing every coefficient of Delta_n, so v_p(S) >= 2e.
4. Therefore v_p(S) = 2e, which is even.

### Direction 2: v_p(S(n)) is odd when n+2 = p^k (odd primes)

(`odd_of_prime_power` in Complete.lean / MainTheorem.lean)

1. **Lower bound (rank-1 collapse):** When n+2 = p^k, factor out p^{e_central} from A_eval, B_eval, C_eval. The reduced discriminant B'^2 - 4A'C' vanishes mod p (because B' ~ -2*lambda*c_n*c_{n+1} makes the quadratic form rank 1 mod p). So p^{2e+1} divides every evaluation, hence every coefficient.
2. **Upper bound (deformation):** Construct a specialization c (a perturbation of the central pair) where Delta_eval factors as (B+2u)(B-2u) with v_p = e and v_p = e+1 respectively, giving v_p(Delta_eval) = 2e+1 exactly.
3. Therefore v_p(S) = 2e+1, which is odd.

### The p = 2 case

(`v2_always_even` in Complete.lean / PrimeTwo.lean)

The non-power-of-2 case is identical to odd primes. The power-of-2 case differs: the rank-1 collapse gives divisibility by 2^{2e+2} (not 2^{2e+1}) because B' is even, and the deformation achieves v_2 = 2e+2 exactly. So v_2(S(n)) = 2e+2, which is even.

## Paper-to-Lean Mapping

| Paper | Lean theorem name (in Complete.lean) |
|-------|--------------------------------------|
| Def. of S(n) | `S`, `mvContent`, `Δ_n` |
| Prop. 3.1 (phi_k kills A, C) | `eval_A_n_phi_eq_zero`, `eval_C_n_phi_eq_zero`, `eval_Delta_n_phi_eq_sq` |
| Prop. 3.2 (b_k closed form) | `cancellation_free_Bn_coefficient` |
| Prop. 3.3 (content bounds) | `S_dvd_eval`, `vp_S_le_eval`, `vp_S_ge_of_coeff_dvd` |
| Prop. 4.1 (binomial gcd) | `g_val` |
| Prop. 4.2 (scalar coeff bounds) | `coeff_B_n_dvd`, `coeff_Δ_n_dvd_sq` |
| Prop. 5.1 (central dominance) | `scalar_AB_central_min`, `scalar_A2_central_min`, `scalar_B2_central_min` |
| Prop. 5.2 (Kummer off-center) | `padicValNat_choose_off_center`, `padicValNat_choose_central` |
| Prop. 5.3 (off-center witness) | `vp_b_witness_bound` |
| Prop. 5.4 (B_eval divisibility) | `B_eval_dvd_pe` |
| Prop. 5.5 (B_eval congruence) | `B_eval_cong` |
| Prop. 5.6 (reduced disc mod p) | `reduced_disc_dvd_p` |
| Prop. 5.7 (rank-1 collapse) | `rank1_collapse` |
| Prop. 5.8 (deformation) | `deformation_valuation` |
| Thm 1.3 (odd primes) | `main_theorem` (in MainTheorem.lean) |
| Thm 1.3 (p = 2) | `v2_always_even` (in PrimeTwo.lean) |
| Thm 1.3 (combined) | `main_theorem_full` (in MainTheorem.lean) |

## Building

Requires **Lean 4** and **Mathlib**.

To verify the self-contained formalization:
```
lake env lean Complete.lean
```

To build via the lakefile:
```
lake build
```
