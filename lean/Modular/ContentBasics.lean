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
The content of a polynomial divides the evaluation at any integer point.

PROVIDED SOLUTION
Unfold S and mvContent. We need to show that `(Finset.gcd support (fun m => |coeff m|) : ℤ) ∣ MvPolynomial.eval x (Δ_n n)`.

Use `MvPolynomial.eval_eq_sum` or the fact that `MvPolynomial.eval x p = p.sum (fun m a => a * m.prod (fun i k => x i ^ k))` which equals `∑ m ∈ p.support, p.coeff m * ∏ i ∈ m.support, x i ^ m i`.

Then use `Finset.dvd_sum`. For each term, the gcd divides |coeff m| (by `Finset.gcd_dvd`), hence (gcd : ℤ) divides coeff m (via Int.natAbs), hence divides coeff m * monomial_eval.
-/
theorem S_dvd_eval (n : ℕ) (x : ℕ → ℤ) :
    (S n : ℤ) ∣ MvPolynomial.eval x (Δ_n n) := by
  -- By definition of $S$, we know that for any monomial $x_i$ in $\Delta_n(n)$, $(S n : ℤ)$ divides the coefficient of $x_i$.
  have h_divides_coeff : ∀ m ∈ (Δ_n n).support, (S n : ℤ) ∣ Int.natAbs ((Δ_n n).coeff m) := by
    exact fun m hm => Int.natCast_dvd_natCast.2 <| Finset.gcd_dvd hm |> fun h => dvd_trans h <| by simpa;
  generalize_proofs at *; (
  simp_all +decide [ MvPolynomial.eval_eq' ];
  exact Finset.dvd_sum fun m hm => dvd_mul_of_dvd_left ( h_divides_coeff m ( by aesop ) ) _;)

/-
PROBLEM
Upper bound: v_p(S(n)) ≤ v_p(|Δ_n(x)|) for any nonzero evaluation.

PROVIDED SOLUTION
From S_dvd_eval we get (S n : ℤ) ∣ eval. So S n ∣ |eval| as natural numbers (Int.natAbs). Since eval ≠ 0, |eval| ≠ 0. Use padicValNat.dvd_of_le or the fact that if a ∣ b and b ≠ 0 then padicValNat p a ≤ padicValNat p b.
-/
theorem vp_S_le_eval (p n : ℕ) [Fact p.Prime] (x : ℕ → ℤ)
    (hne : MvPolynomial.eval x (Δ_n n) ≠ 0) :
    padicValNat p (S n) ≤
      padicValNat p (Int.natAbs (MvPolynomial.eval x (Δ_n n))) := by
  -- From S_dvd_eval, we get that S(n) divides the evaluation.
  have h_div : S n ∣ Int.natAbs (MvPolynomial.eval x (Δ_n n)) := by
    convert Int.natCast_dvd.mp ( S_dvd_eval n x ) using 1;
  rw [ ← Nat.factorization_def, ← Nat.factorization_def ];
  · exact ( Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) ) |>.2 h_div p;
  · exact Fact.out;
  · exact Fact.out

/-
PROBLEM
Lower bound: if p^r divides every coefficient, then r ≤ v_p(S(n)).

PROVIDED SOLUTION
If p^r divides every |coeff m| for m in support, then p^r divides gcd of |coeff m| = S n. This uses Finset.dvd_gcd: to show p^r ∣ Finset.gcd support f, it suffices to show p^r ∣ f m for each m in support. Then since hS says S n ≠ 0, use padicValNat.le_of_dvd to get r ≤ padicValNat p (S n).
-/
theorem vp_S_ge_of_coeff_dvd (p n r : ℕ) [Fact p.Prime]
    (hS : S n ≠ 0)
    (hcoeff : ∀ m ∈ (Δ_n n).support, p ^ r ∣ Int.natAbs ((Δ_n n).coeff m)) :
    r ≤ padicValNat p (S n) := by
  -- From hcoeff, we know that p^r divides the gcd of all coefficients' absolute values.
  have h_div_gcd : p^r ∣ (Finset.gcd (Δ_n n).support (fun m => Int.natAbs ((Δ_n n).coeff m))) := by
    exact Finset.dvd_gcd hcoeff;
  rw [ ← Nat.factorization_le_iff_dvd ] at h_div_gcd <;> norm_num at *;
  · simp_all +decide [ Nat.Prime.factorization Fact.out ];
    rw [ ← Nat.factorization_def ] ; aesop;
    exact Fact.out;
  · exact fun h => absurd h ( Nat.Prime.ne_zero Fact.out );
  · contrapose! hS; aesop;

/-
PROBLEM
S(n) is nonzero if some evaluation is nonzero.

PROVIDED SOLUTION
Proof by contradiction. Assume S n = 0. By S_dvd_eval, (S n : ℤ) ∣ eval. Since S n = 0, we get (0 : ℤ) ∣ eval, so eval = 0. This contradicts hne.
-/
theorem S_ne_zero_of_eval_ne_zero (n : ℕ) (x : ℕ → ℤ)
    (hne : MvPolynomial.eval x (Δ_n n) ≠ 0) :
    S n ≠ 0 := by
  contrapose! hne; have := S_dvd_eval n x; aesop;

/-- The evaluation of a MvPolynomial at x equals the scalar Δ_eval. -/




/-
PROBLEM
The MvPolynomial evaluation agrees with the scalar evaluation.

PROVIDED SOLUTION
Unfold Δ_n, A_n, B_n, C_n, Δ_eval, A_eval, B_eval, C_eval. Then use simp with MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_sub, MvPolynomial.eval_add, and ring.
-/
theorem eval_Δ_eq_Δ_eval (n : ℕ) (c : ℕ → ℤ) :
    MvPolynomial.eval c (Δ_n n) = Δ_eval n c := by
  unfold Δ_n Δ_eval A_eval B_eval C_eval; norm_num [ MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_add, MvPolynomial.eval_C ] ; ring;
  unfold B_n A_n C_n; norm_num [ MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C ] ; ring;

end QuarticInvariant
