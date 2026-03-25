import Mathlib
import Modular.Defs

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant


/-
PROBLEM
Under the two-point specialization φ_k, every summand of A_n vanishes
because f_i · f_{2n-i} cannot be nonzero: the support {k, 2n+1-k}
sums to 2n+1, but the monomial indices sum to 2n.

PROVIDED SOLUTION
Unfold A_n and phi, then use MvPolynomial.eval to distribute over the sum. Each summand has the form c * X_i * X_{2n-i}, which evaluates to c * phi(n,k)(i) * phi(n,k)(2n-i). For a summand to be nonzero, both phi(n,k)(i) and phi(n,k)(2n-i) must be nonzero, meaning i ∈ {k, 2n+1-k} and (2n-i) ∈ {k, 2n+1-k}. But i + (2n-i) = 2n while k + (2n+1-k) = 2n+1, so we can't have both in the support unless k = n (excluded). Show each summand is zero and the sum is zero. Key approach: use Finset.sum_eq_zero, then for each i show that phi(n,k)(i) * phi(n,k)(2n-i) = 0 by case analysis on whether i ∈ {k, 2n+1-k}. If i ∉ {k, 2n+1-k}, then phi(n,k)(i) = 0. If i = k, then 2n-i = 2n-k, and we need 2n-k ∈ {k, 2n+1-k}; 2n-k = k implies k=n (excluded), 2n-k = 2n+1-k is impossible. If i = 2n+1-k, then 2n-i = k-1, and we need k-1 ∈ {k, 2n+1-k}; k-1=k is impossible, k-1=2n+1-k implies k=n+1 (excluded).
-/
theorem eval_A_n_phi_eq_zero (n k : ℕ)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ 2 * n)
    (hk_ne_n : k ≠ n) (hk_ne_n1 : k ≠ n + 1) :
    MvPolynomial.eval (phi n k) (A_n n) = 0 := by
  simp +decide [ A_n, MvPolynomial.eval_sum ];
  rw [ Finset.sum_eq_zero ];
  unfold phi;
  grind +ring

/-
PROBLEM
Same argument for C_n: f_{i+1} · f_{2n+1-i} cannot be nonzero under φ_k
when k ∉ {n, n+1}, because the monomial pair {i+1, 2n+1-i} sums to 2n+2
while the support pair {k, 2n+1-k} sums to 2n+1.

PROVIDED SOLUTION
Unfold C_n and phi, then use MvPolynomial.eval to distribute over the sum. Each summand has the form c * X_{i+1} * X_{2n+1-i}, which evaluates to c * phi(n,k)(i+1) * phi(n,k)(2n+1-i). For a summand to be nonzero, both phi(n,k)(i+1) and phi(n,k)(2n+1-i) must be nonzero, meaning (i+1) ∈ {k, 2n+1-k} and (2n+1-i) ∈ {k, 2n+1-k}. But (i+1) + (2n+1-i) = 2n+2 while k + (2n+1-k) = 2n+1, so we can't have both in the support unless k=n or k=n+1 (both excluded). Use Finset.sum_eq_zero, then for each i show phi(n,k)(i+1) * phi(n,k)(2n+1-i) = 0 by case analysis. If i+1 ∉ {k, 2n+1-k}, then phi(n,k)(i+1) = 0. If i+1 = k, then 2n+1-i = 2n+2-k, and 2n+2-k = k implies k=n+1 (excluded), 2n+2-k = 2n+1-k is impossible. If i+1 = 2n+1-k, then 2n+1-i = k+1, and k+1 = k is impossible, k+1 = 2n+1-k implies k=n (excluded).
-/
theorem eval_C_n_phi_eq_zero (n k : ℕ)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ 2 * n)
    (hk_ne_n : k ≠ n) (hk_ne_n1 : k ≠ n + 1) :
    MvPolynomial.eval (phi n k) (C_n n) = 0 := by
  -- By definition of $C_n$, each summand has the form $c * X_{i+1} * X_{2n+1-i}$, which evaluates to $c * phi(n,k)(i+1) * phi(n,k)(2n+1-i)$.
  have h_summand : ∀ i ∈ Finset.range (2 * n + 1), (MvPolynomial.eval (phi n k)) ((MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) * (β n i : ℤ))) * (MvPolynomial.X (i + 1)) * (MvPolynomial.X (2 * n + 1 - i))) = 0 := by
    simp_all +decide [ phi, Finset.sum_range_succ ];
    omega;
  convert Finset.sum_eq_zero h_summand using 1;
  unfold C_n; simp +decide [ Finset.sum_mul ] ;

/-
PROBLEM
Therefore Δ_n(φ_k) = B_n(φ_k)².

PROVIDED SOLUTION
Unfold Δ_n as B_n^2 - 4*A_n*C_n, apply eval as a ring homomorphism, then substitute eval_A_n_phi_eq_zero and eval_C_n_phi_eq_zero (both applied with the same hypotheses). This gives B_n^2 - 4*0*0 = B_n^2. Use simp/ring to close.
-/
theorem eval_Delta_n_phi_eq_sq (n k : ℕ)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ 2 * n)
    (hk_ne_n : k ≠ n) (hk_ne_n1 : k ≠ n + 1) :
    MvPolynomial.eval (phi n k) (Δ_n n) =
      (MvPolynomial.eval (phi n k) (B_n n)) ^ 2 := by
  unfold Δ_n
  simp
  exact Or.inl <| eval_A_n_phi_eq_zero n k hk_lo hk_hi hk_ne_n hk_ne_n1

end QuarticInvariant
