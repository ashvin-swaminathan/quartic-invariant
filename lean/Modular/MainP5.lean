import Mathlib
import Modular.Defs
import Modular.ContentBasics
import Modular.PairSpec
import Modular.ScalarBounds
import Modular.CentralDom
import Modular.OffCenter
import Modular.DeformAssembly
import Modular.CoeffDivPP

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant

private lemma natAbs_dvd_int_pow {p : ℕ} {e : ℕ} {a : ℤ}
    (h : p ^ e ∣ a.natAbs) : (p : ℤ) ^ e ∣ a :=
  Int.natAbs_dvd_natAbs.mp (by simpa [Int.natAbs_pow, Int.natAbs_natCast] using h)

/-! ## Main theorem: Direction 2 (prime power → odd valuation) -/

theorem odd_of_prime_power (p n : ℕ) [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) (hpow : n + 2 = p ^ k) :
    Odd (padicValNat p (S n)) := by
  have hp_odd : p ≠ 2 := by omega
  -- Get deformation witness
  obtain ⟨c, hc_ne, hc_val⟩ := deformation_valuation_exists p hp_odd k hk (fun _ => hp5) n hpow hn
  -- Translate to MvPolynomial evaluation
  have hc_ne' : MvPolynomial.eval c (Δ_n n) ≠ 0 := by
    rw [eval_Δ_eq_Δ_eval]; exact hc_ne
  have hc_val' : padicValNat p (Int.natAbs (MvPolynomial.eval c (Δ_n n))) =
      2 * e_central p n + 1 := by
    rw [eval_Δ_eq_Δ_eval]; exact hc_val
  -- S is nonzero
  have hS : S n ≠ 0 := S_ne_zero_of_eval_ne_zero n c hc_ne'
  -- Upper bound: v_p(S) ≤ 2e+1
  have h_upper : padicValNat p (S n) ≤ 2 * e_central p n + 1 :=
    hc_val' ▸ vp_S_le_eval p n c hc_ne'
  -- Lower bound: v_p(S) ≥ 2e+1 from coefficient divisibility
  have h_lower : 2 * e_central p n + 1 ≤ padicValNat p (S n) :=
    vp_S_ge_of_coeff_dvd p n (2 * e_central p n + 1) hS
      (coeff_Δ_n_dvd_prime_power p hp5 k hk n hpow hn)
  exact ⟨e_central p n, by omega⟩

/-! ## Direction 1: non-prime-power → even valuation -/

/-- b_k_val is nonzero for valid indices (the numerator has (2n+1-k) ≠ 0 and (2n+1-2k) ≠ 0
    since 2n+1 is odd, and C(2n,k) divides the numerator exactly). -/
lemma b_k_val_ne_zero (n k : ℕ) (hn : 1 ≤ n) (hk_lo : 1 ≤ k) (hk_hi : k ≤ 2 * n) :
    b_k_val n k ≠ 0 := by
  rw [← b_formula_eq_b_k_val]
  rw [b_formula_factored n k hk_hi]
  apply mul_ne_zero
  · apply mul_ne_zero; norm_num
    exact pow_ne_zero _ (by norm_num)
  · apply mul_ne_zero; apply mul_ne_zero; apply mul_ne_zero
    · exact_mod_cast (Nat.factorial_pos _).ne'
    · -- 2n+1-2k ≠ 0 since 2n+1 is odd
      omega
    · exact_mod_cast (Nat.factorial_pos _).ne'
    · exact_mod_cast (Nat.factorial_pos _).ne'

/-- Evaluation of B_n at the pair specialization φ_k gives b_k_val.
    This follows from B_n_eq_alt: in the rearranged form, at φ_k only
    the monomial X_k · X_{2n+1-k} (or its symmetric partner) survives. -/
lemma eval_B_phi_eq_bk (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * n)
    (hkn : k ≠ n) (hkn1 : k ≠ n + 1) (hn : 0 < n) :
    MvPolynomial.eval (phi n k) (B_n n) = b_k_val n k := by
  -- Symmetry of b_formula: b_formula(n, 2n+1-k) = b_formula(n, k)
  have b_symm : b_formula n (2 * n + 1 - k) = b_formula n k := by
    have hk2n1 : 2 * n + 1 - k ≤ 2 * n := by omega
    rw [b_formula_factored n (2 * n + 1 - k) hk2n1, b_formula_factored n k hk2]
    have h_neg1 : (-1 : ℤ) ^ (2 * n + 1 - k) = -(-1 : ℤ) ^ k := by
      have key : (-1 : ℤ) ^ (2 * n + 1 - k) * (-1) ^ k = -1 := by
        rw [← pow_add, show 2 * n + 1 - k + k = 2 * n + 1 from by omega]
        have : ∀ m, (-1 : ℤ) ^ (2 * m + 1) = -1 := by
          intro m; induction m with
          | zero => simp
          | succ t ih => rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 2 from by ring, pow_add, ih]; ring
        exact this n
      have sq_one : ((-1 : ℤ) ^ k) ^ 2 = 1 := by
        rw [← pow_mul, show k * 2 = 2 * k from by ring, pow_mul, neg_one_sq, one_pow]
      -- From key: a*b = -1 and b^2 = 1, so a = a*b*b = -b
      have := mul_right_cancel₀ (pow_ne_zero k (show (-1 : ℤ) ≠ 0 from by norm_num))
        (show (-1 : ℤ) ^ (2 * n + 1 - k) * (-1) ^ k = -(-1) ^ k * (-1) ^ k from by
          rw [key]; rw [show ((-1 : ℤ) ^ k) ^ 2 = (-1) ^ k * (-1) ^ k from sq ((-1 : ℤ) ^ k)] at sq_one
          linarith)
      linarith
    have h_sub : ((2 * n : ℤ) + 1 - 2 * (2 * n + 1 - k : ℕ)) = -((2 * n : ℤ) + 1 - 2 * k) := by
      zify [show k ≤ 2 * n + 1 from by omega]; ring
    have h_fact1 : ((2 * n + 1 - (2 * n + 1 - k)).factorial : ℤ) = (k.factorial : ℤ) := by
      rw [Nat.sub_sub_self (by omega : k ≤ 2 * n + 1)]
    rw [h_neg1, h_sub, h_fact1]; ring
  -- Use B_n_eq_alt to rewrite B_n
  rw [B_n_eq_alt n hn, ← b_formula_eq_b_k_val]
  -- Evaluate B_n_alt at phi(n,k)
  simp only [B_n_alt, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  -- The boundary term X_0 * X_{2n+1} vanishes because phi(n,k)(0) = 0
  have h0 : phi n k 0 = 0 := by simp [phi]; omega
  simp only [h0, mul_zero, zero_mul, zero_add]
  -- Now the goal is about the sum
  -- Helper for phi vanishing
  have hp0 : ∀ j, j ≠ k → j ≠ 2 * n + 1 - k → phi n k j = 0 := by
    intro j h1 h2; simp [phi, h1, h2]
  -- Each summand has factor phi(n,k)(j) or phi(n,k)(2n+1-j); if j ∉ {k, 2n+1-k}, one is 0
  -- Case split on k ≤ n vs k > n
  -- Each summand vanishes unless j ∈ {k, 2n+1-k}, because phi(n,k)(j) = 0
  have h_vanish : ∀ j ∈ Finset.Icc 1 n, j ≠ k → j ≠ 2 * n + 1 - k →
      b_formula n j * phi n k j * phi n k (2 * n + 1 - j) = 0 := by
    intro j _ hjk hjs
    rw [hp0 j hjk hjs]; ring
  by_cases hle : k ≤ n
  · -- k ≤ n: term j = k survives
    rw [Finset.sum_eq_single k]
    · simp [phi]
    · intro j hj hne
      have hj_mem := Finset.mem_Icc.mp hj
      exact h_vanish j hj hne (by omega)
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hk1, hle⟩) h
  · -- k > n: term j = 2n+1-k survives
    push_neg at hle
    rw [Finset.sum_eq_single (2 * n + 1 - k)]
    · have hsk : 2 * n + 1 - (2 * n + 1 - k) = k := by omega
      simp only [phi, hsk, ite_true, eq_self_iff_true, or_true, mul_one, true_or]
      exact b_symm
    · intro j hj hne
      have hj_mem := Finset.mem_Icc.mp hj
      have hjk : j ≠ k := by omega
      exact h_vanish j hj hjk hne
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) h

/-- Symmetry of b_formula: b_formula(n, 2n+1-k) = b_formula(n, k). -/
private lemma b_formula_symm_index (n k : ℕ) (hk : 1 ≤ k) (hk2 : k ≤ 2 * n) :
    b_formula n (2 * n + 1 - k) = b_formula n k := by
  have hk2n1 : 2 * n + 1 - k ≤ 2 * n := by omega
  rw [b_formula_factored n (2 * n + 1 - k) hk2n1, b_formula_factored n k hk2]
  have h_neg1 : (-1 : ℤ) ^ (2 * n + 1 - k) = -(-1 : ℤ) ^ k := by
    have key : (-1 : ℤ) ^ (2 * n + 1 - k) * (-1) ^ k = -1 := by
      rw [← pow_add, show 2 * n + 1 - k + k = 2 * n + 1 from by omega]
      have : ∀ m, (-1 : ℤ) ^ (2 * m + 1) = -1 := by
        intro m; induction m with
        | zero => simp
        | succ t ih => rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 2 from by ring, pow_add, ih]; ring
      exact this n
    have sq_one : ((-1 : ℤ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, show k * 2 = 2 * k from by ring, pow_mul, neg_one_sq, one_pow]
    have := mul_right_cancel₀ (pow_ne_zero k (show (-1 : ℤ) ≠ 0 from by norm_num))
      (show (-1 : ℤ) ^ (2 * n + 1 - k) * (-1) ^ k = -(-1) ^ k * (-1) ^ k from by
        rw [key]; rw [show ((-1 : ℤ) ^ k) ^ 2 = (-1) ^ k * (-1) ^ k from sq ((-1 : ℤ) ^ k)] at sq_one
        linarith)
    linarith
  have h_sub : ((2 * n : ℤ) + 1 - 2 * (2 * n + 1 - k : ℕ)) = -((2 * n : ℤ) + 1 - 2 * k) := by
    zify [show k ≤ 2 * n + 1 from by omega]; ring
  have h_fact1 : ((2 * n + 1 - (2 * n + 1 - k)).factorial : ℤ) = (k.factorial : ℤ) := by
    rw [Nat.sub_sub_self (by omega : k ≤ 2 * n + 1)]
  rw [h_neg1, h_sub, h_fact1]; ring

/-- vp_b is symmetric: vp_b(n, n) = vp_b(n, n+1). Since 2n+1-n = n+1. -/
private lemma vp_b_symm_n_n1 (p n : ℕ) (hn : 1 ≤ n) :
    vp_b p n n = vp_b p n (n + 1) := by
  unfold vp_b
  rw [← b_formula_eq_b_k_val, ← b_formula_eq_b_k_val]
  congr 1
  rw [show n + 1 = 2 * n + 1 - n from by omega]
  rw [b_formula_symm_index n n (by omega) (by omega)]

/-- Recurrence: n * b_formula(n, n-1) + 3*(n+2) * b_formula(n, n) = 0.
    From b_formula_factored:
      b_formula(n,n-1) = 2*(-1)^(n-1) * (2n)! * 3 * (n+2)! * (n-1)!
      b_formula(n,n)   = 2*(-1)^n * (2n)! * 1 * (n+1)! * n!
    So n*b(n-1) = 2*(-1)^(n-1)*n*(2n)!*3*(n+2)!*(n-1)!
               = -2*(-1)^n*3*(2n)!*(n+2)!*n!    [since (-1)^(n-1) = -(-1)^n and n*(n-1)! = n!]
       3*(n+2)*b(n) = 2*(-1)^n*3*(n+2)*(2n)!*(n+1)!*n!
                    = 2*(-1)^n*3*(2n)!*(n+2)!*n!    [since (n+2)*(n+1)! = (n+2)!]
    Sum = 0. -/
private lemma b_formula_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (n : ℤ) * b_formula n (n - 1) + 3 * (↑(n + 2)) * b_formula n n = 0 := by
  have hn1 : n - 1 ≤ 2 * n := by omega
  have hn2 : n ≤ 2 * n := by omega
  rw [b_formula_factored n (n - 1) hn1, b_formula_factored n n hn2]
  -- After factoring, both terms share 2 * (2n)! and we can combine
  have h1 : ((2 * n + 1 - (n - 1)).factorial : ℤ) = ((n + 2).factorial : ℤ) := by
    have heq : 2 * n + 1 - (n - 1) = n + 2 := by omega
    rw [heq]
  have h2 : ((n - 1).factorial : ℤ) = ((n - 1).factorial : ℤ) := rfl
  have h3 : ((2 * n + 1 - n).factorial : ℤ) = ((n + 1).factorial : ℤ) := by
    have heq : 2 * n + 1 - n = n + 1 := by omega
    rw [heq]
  have h4 : ((2 * n : ℤ) + 1 - 2 * (n - 1 : ℕ)) = 3 := by omega
  have h5 : ((2 * n : ℤ) + 1 - 2 * n) = 1 := by omega
  rw [h1, h3, h4, h5]
  -- Now expand (n+2)! = (n+2)*(n+1)! and n! = n*(n-1)!
  have h6 : ((n + 2).factorial : ℤ) = (↑(n + 2)) * ((n + 1).factorial : ℤ) := by
    push_cast [Nat.factorial_succ]; ring
  have h7 : (n.factorial : ℤ) = (↑n) * ((n - 1).factorial : ℤ) := by
    rcases n with _ | n
    · omega
    · push_cast [Nat.factorial_succ]; ring
  have h8 : (-1 : ℤ) ^ (n - 1) = -(-1 : ℤ) ^ n := by
    rcases n with _ | n
    · omega
    · simp only [show n + 1 - 1 = n from by omega, pow_succ]
      ring
  rw [h6, h7, h8]; ring

/-- When p ≥ 5 and p ∤ (n+2), vp_b(n-1) ≤ vp_b(n). -/
private lemma vp_b_n_minus_one_le_n (p n : ℕ) [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 2 ≤ n) (hpm : ¬ (p ∣ (n + 2))) :
    vp_b p n (n - 1) ≤ vp_b p n n := by
  -- From the recurrence: n * b_{n-1} = -3*(n+2) * b_n
  have h_rec := b_formula_recurrence n hn
  have h_eq : (↑n : ℤ) * b_formula n (n - 1) = -(3 * ↑(n + 2) * b_formula n n) := by linarith
  -- Take natAbs of both sides
  have h_abs : n * Int.natAbs (b_formula n (n - 1)) =
      3 * (n + 2) * Int.natAbs (b_formula n n) := by
    have := congr_arg Int.natAbs h_eq
    simp only [Int.natAbs_neg, Int.natAbs_mul] at this
    push_cast at this ⊢
    exact this
  -- Take p-adic valuations
  have hbn_ne : Int.natAbs (b_formula n n) ≠ 0 := by
    rw [Int.natAbs_ne_zero, b_formula_eq_b_k_val]
    exact b_k_val_ne_zero n n (by omega) (by omega) (by omega)
  have hbn1_ne : Int.natAbs (b_formula n (n - 1)) ≠ 0 := by
    rw [Int.natAbs_ne_zero, b_formula_eq_b_k_val]
    exact b_k_val_ne_zero n (n - 1) (by omega) (by omega) (by omega)
  have h_vp : padicValNat p (n * Int.natAbs (b_formula n (n - 1))) =
      padicValNat p (3 * (n + 2) * Int.natAbs (b_formula n n)) := by
    rw [h_abs]
  rw [padicValNat.mul (by omega : n ≠ 0) hbn1_ne,
      padicValNat.mul (by positivity) hbn_ne] at h_vp
  rw [padicValNat.mul (by norm_num) (by omega : n + 2 ≠ 0)] at h_vp
  -- v_p(3) = 0 since p ≥ 5
  have h_vp3 : padicValNat p 3 = 0 :=
    padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
  -- v_p(n+2) = 0 since p ∤ (n+2)
  have h_vpn2 : padicValNat p (n + 2) = 0 :=
    padicValNat.eq_zero_of_not_dvd hpm
  -- So padicValNat p n + vp_b(n-1) = 0 + 0 + vp_b(n)
  unfold vp_b
  rw [← b_formula_eq_b_k_val, ← b_formula_eq_b_k_val]
  omega

/-- The non-prime-power case: v_p(S(n)) is even.

    Upper bound: S | Δ(φ_{k₀}) = b_{k₀}², so v_p(S) ≤ 2·v_p(b_{k₀}) = 2e.
    Lower bound: p^{2e} | every coeff of Δ_n (from b_k minimum bounds +
      coefficient analysis), so v_p(S) ≥ 2e. -/
-- For p ≥ 5, if e ≤ v_p(|b_formula(n,k)|) for all k ∈ [1,2n], then p^e | scalar_AB(n,i) for all i.
-- This holds because scalar_AB(n,i) = C(2n,i)*α(n,i)*β(n,i) and the relationship between
-- scalar_AB and b_formula involves only factors coprime to p (for p ≥ 5).
private lemma scalar_AB_dvd_of_vp_b_min (p n : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hn : 0 < n)
    (e : ℕ) (he : ∀ k ∈ Finset.Icc 1 (2 * n), e ≤ padicValNat p (Int.natAbs (b_formula n k))) :
    ∀ i, i ≤ 2 * n → (p ^ e) ∣ scalar_AB n i := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_odd : p ≠ 2 := by omega
  have hp_pos : 0 < p := hp_prime.pos
  -- Key helper: p does not divide 2
  have hp_not_dvd_2 : ¬(p ∣ 2) := by
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  -- Helper: p^e is coprime to 2
  have hcop2 : Nat.Coprime (p ^ e) 2 :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp_prime).2 hp_not_dvd_2)
  -- Helper: from the hypothesis, p^e | Int.natAbs(b_formula n k) for k ∈ [1,2n]
  have he_dvd : ∀ k, k ∈ Finset.Icc 1 (2 * n) →
      p ^ e ∣ Int.natAbs (b_formula n k) := by
    intro k hk
    have hk_ne : Int.natAbs (b_formula n k) ≠ 0 := by
      rw [Int.natAbs_ne_zero, b_formula_eq_b_k_val]
      exact b_k_val_ne_zero n k (by omega) (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    exact (padicValNat_dvd_iff_le hk_ne).mpr (he k hk)
  -- Helper: extract p^e divisibility from b_formula_factored, removing coprime factors
  -- For k ∈ [1,2n]: b_formula n k = 2 * (-1)^k * ((2n)! * (2n+1-2k) * (2n+1-k)! * k!)
  -- So Int.natAbs(b_formula n k) = 2 * (2n)! * |2n+1-2k| * (2n+1-k)! * k!
  -- If p ∤ |2n+1-2k|, then p^e | (2n)! * (2n+1-k)! * k!
  have factor_out (k : ℕ) (hk_lo : 1 ≤ k) (hk_hi : k ≤ 2 * n)
      (hcop : ¬(p ∣ Int.natAbs ((2 * n : ℤ) + 1 - 2 * k))) :
      p ^ e ∣ (2 * n).factorial * (2 * n + 1 - k).factorial * k.factorial := by
    have hk_mem : k ∈ Finset.Icc 1 (2 * n) := Finset.mem_Icc.mpr ⟨hk_lo, hk_hi⟩
    have h_dvd := he_dvd k hk_mem
    have h_eq := b_formula_factored n k hk_hi
    -- Compute Int.natAbs of b_formula from the factored form (all in ℕ)
    have h_natabs : Int.natAbs (b_formula n k) =
        2 * (2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * k) *
        (2 * n + 1 - k).factorial * k.factorial := by
      rw [h_eq]
      rw [show 2 * (-1 : ℤ) ^ k *
          (((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ)) =
          (2 * (-1 : ℤ) ^ k) *
          (((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ)) from by ring]
      rw [Int.natAbs_mul]
      have h_unit : Int.natAbs (2 * (-1 : ℤ) ^ k) = 2 := by
        rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;> simp
      rw [h_unit]
      -- Now simplify the natAbs of the product of (positive ℤ) and (possibly negative) (2n+1-2k)
      rw [show ((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ) =
          ((2 * n).factorial : ℤ) * ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ) *
          ((2 * n : ℤ) + 1 - 2 * ↑k) from by ring]
      rw [Int.natAbs_mul]
      rw [show Int.natAbs (((2 * n).factorial : ℤ) * ((2 * n + 1 - k).factorial : ℤ) *
          (k.factorial : ℤ)) = (2 * n).factorial * (2 * n + 1 - k).factorial * k.factorial from by
        simp [Int.natAbs_mul, Int.natAbs_natCast]]
      ring
    rw [h_natabs] at h_dvd
    -- p^e | 2 * (2n)! * |2n+1-2k| * (2n+1-k)! * k!
    -- Since gcd(p^e, 2) = 1: p^e | (2n)! * |2n+1-2k| * (2n+1-k)! * k!
    have h_no2 : p ^ e ∣ (2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * k) *
        (2 * n + 1 - k).factorial * k.factorial := by
      have h_rearr2 : 2 * (2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * ↑k) *
          (2 * n + 1 - k).factorial * k.factorial =
          2 * ((2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * ↑k) *
          (2 * n + 1 - k).factorial * k.factorial) := by ring
      rw [h_rearr2] at h_dvd
      exact hcop2.dvd_of_dvd_mul_left h_dvd
    -- Since gcd(p^e, |2n+1-2k|) = 1: p^e | (2n)! * (2n+1-k)! * k!
    have hcop_abs : Nat.Coprime (p ^ e) (Int.natAbs ((2 * n : ℤ) + 1 - 2 * k)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp_prime).2 hcop)
    have h_rearr : (2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * ↑k) *
        (2 * n + 1 - k).factorial * k.factorial =
        Int.natAbs ((2 * n : ℤ) + 1 - 2 * ↑k) *
        ((2 * n).factorial * (2 * n + 1 - k).factorial * k.factorial) := by ring
    rw [h_rearr] at h_no2
    exact hcop_abs.dvd_of_dvd_mul_left h_no2
  -- Main proof: case split on i
  intro i hi
  -- Case A: i = 0 or i = 2n (boundary cases)
  -- Boundary helper: for i=0 or i=2n, scalar_AB = (2n)! * (2n+1)!
  -- Use: (p:ℤ)^e | b_formula(n,n) and C(2n+1,n+1) * b_formula(n,n) = ±2 * ↑(scalar_AB(n,i))
  have boundary_case (i : ℕ) (hi_le : i ≤ 2 * n) (hi_bdy : i = 0 ∨ i = 2 * n) :
      p ^ e ∣ scalar_AB n i := by
    have hn_mem : n ∈ Finset.Icc 1 (2 * n) := Finset.mem_Icc.mpr ⟨hn, by omega⟩
    have h_dvd_bn_int : (p : ℤ) ^ e ∣ b_formula n n :=
      natAbs_dvd_int_pow (he_dvd n hn_mem)
    have h_eq_bn := b_formula_factored n n (by omega : n ≤ 2 * n)
    -- scalar_AB(n,i) = (2n)! * (2n+1)! for boundary i
    have h_scalar_bdy : scalar_AB n i = (2 * n).factorial * (2 * n + 1).factorial := by
      rw [scalar_AB_formula n i hi_le]
      rcases hi_bdy with rfl | rfl
      · simp only [Nat.sub_zero, Nat.zero_add, Nat.factorial_one]; ring
      · rw [show 2 * n + 1 - 2 * n = 1 from by omega,
            show 2 * n + 1 = (2 * n + 1) from rfl]
        simp only [Nat.factorial_one]; ring
    -- C(2n+1,n+1) * (n+1)! * n! = (2n+1)!
    have h_choose_fact : Nat.choose (2 * n + 1) (n + 1) * (n + 1).factorial * n.factorial =
        (2 * n + 1).factorial := by
      have h := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 2 * n + 1 from by omega)
      rw [show 2 * n + 1 - (n + 1) = n from by omega] at h; linarith
    -- Key identity: 2 * scalar_AB(n,i) = C(2n+1,n+1) * |b_formula(n,n)| (as ℕ)
    -- From b_formula_factored: |b_formula(n,n)| = 2 * (2n)! * (n+1)! * n!
    -- So C(2n+1,n+1) * |b_formula(n,n)| = C(2n+1,n+1) * 2 * (2n)! * (n+1)! * n!
    --   = 2 * (2n)! * C(2n+1,n+1) * (n+1)! * n! = 2 * (2n)! * (2n+1)! = 2 * scalar_AB
    -- Work in ℤ for the proof:
    -- Show p^e | scalar_AB by showing p^e | (2n)! * (2n+1-n)! * n! (from factor_out at k=n)
    -- Note: 2n+1-n = n+1, |2n+1-2n| = 1, p ∤ 1
    have h_not_dvd_one : ¬(p ∣ Int.natAbs ((2 * n : ℤ) + 1 - 2 * n)) := by
      have : (2 * n : ℤ) + 1 - 2 * n = 1 := by omega
      rw [this]; simp; exact Nat.Prime.one_lt hp_prime |>.ne'
    have h_factor := factor_out n hn (by omega) h_not_dvd_one
    -- h_factor: p^e | (2n)! * (n+1)! * n!
    rw [show 2 * n + 1 - n = n + 1 from by omega] at h_factor
    -- scalar_AB(n,i) = (2n)! * (2n+1)! = (2n)! * (2n+1) * (2n)! * ... no
    -- Actually: scalar_AB = (2n)! * (2n+1)!
    -- (2n+1)! = C(2n+1,n+1) * (n+1)! * n! (from h_choose_fact)
    -- So scalar_AB = (2n)! * C(2n+1,n+1) * (n+1)! * n!
    --             = C(2n+1,n+1) * ((2n)! * (n+1)! * n!)
    -- Since p^e | (2n)! * (n+1)! * n!, p^e | scalar_AB
    have h_rearrange : (2 * n).factorial * (2 * n + 1).factorial =
        Nat.choose (2 * n + 1) (n + 1) * ((2 * n).factorial * (n + 1).factorial * n.factorial) := by
      nlinarith [h_choose_fact]
    rw [h_scalar_bdy, h_rearrange]
    exact dvd_mul_of_dvd_right h_factor _
  by_cases hi0 : i = 0
  · exact boundary_case i (by omega) (Or.inl hi0)
  · by_cases hi2n : i = 2 * n
    · exact boundary_case i hi (Or.inr hi2n)
    · -- Case B: 1 ≤ i ≤ 2n-1
      have hi_pos : 1 ≤ i := by omega
      have hi_lt : i ≤ 2 * n - 1 := by omega
      -- scalar_AB(n,i) = (2n)! * (2n+1-i)! * (i+1)!
      have h_scalar := scalar_AB_formula n i hi
      -- By cases: p ∤ |2n+1-2i| or p | |2n+1-2i|
      by_cases hdvd : p ∣ Int.natAbs ((2 * n : ℤ) + 1 - 2 * i)
      · -- Case B2: p | |2n+1-2i|. Then p ∤ |2n-1-2i| (since difference is 2, p ≥ 5)
        have hdiff : (2 * n + 1 - 2 * i : ℤ) - (2 * n - 1 - 2 * i : ℤ) = 2 := by omega
        have hcop_other : ¬(p ∣ Int.natAbs ((2 * n : ℤ) - 1 - 2 * i)) := by
          intro h_other
          have h1 : (p : ℤ) ∣ ((2 * n : ℤ) + 1 - 2 * i) :=
            Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdvd)
          have h2 : (p : ℤ) ∣ ((2 * n : ℤ) - 1 - 2 * i) :=
            Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h_other)
          have h3 : (p : ℤ) ∣ 2 := by
            have := Int.dvd_sub h1 h2
            rwa [show (2 * n + 1 - 2 * i : ℤ) - (2 * n - 1 - 2 * i : ℤ) = 2 from by omega]
              at this
          have h4 : (p : ℕ) ∣ 2 := by exact_mod_cast h3
          exact hp_not_dvd_2 h4
        -- Note: (2n+1-2*(i+1)) = (2n-1-2i), so |2n+1-2*(i+1)| = |2n-1-2i|
        have h_eq_idx : (2 * n : ℤ) + 1 - 2 * (↑(i + 1)) = (2 * n : ℤ) - 1 - 2 * i := by
          push_cast; ring
        -- Use b_formula at k = i+1 (which is in [1, 2n] since 2 ≤ i+1 ≤ 2n)
        have hi1_lo : 1 ≤ i + 1 := by omega
        have hi1_hi : i + 1 ≤ 2 * n := by omega
        have h_factor := factor_out (i + 1) hi1_lo hi1_hi (by rwa [h_eq_idx])
        -- h_factor: p^e | (2n)! * (2n-i)! * (i+1)!
        -- scalar_AB(n,i) = (2n)! * (2n+1-i)! * (i+1)! = (2n+1-i) * ((2n)! * (2n-i)! * (i+1)!)
        -- So p^e | scalar_AB(n,i)
        rw [h_scalar]
        have h_fact_split : (2 * n + 1 - i).factorial = (2 * n + 1 - i) * (2 * n - i).factorial := by
          rw [show 2 * n + 1 - i = (2 * n - i) + 1 from by omega]
          exact Nat.factorial_succ (2 * n - i)
        -- (2n)! * (2n+1-i)! * (i+1)! = (2n+1-i) * ((2n)! * (2n-i)! * (i+1)!)
        have h_rearrange : (2 * n).factorial * (2 * n + 1 - i).factorial * (i + 1).factorial =
            (2 * n + 1 - i) * ((2 * n).factorial * (2 * n - i).factorial * (i + 1).factorial) := by
          rw [h_fact_split]; ring
        -- h_factor gives: p^e | (2n)! * (2n+1-(i+1))! * (i+1)!
        -- Note: 2n+1-(i+1) = 2n-i
        have h_idx : 2 * n + 1 - (i + 1) = 2 * n - i := by omega
        rw [h_idx] at h_factor
        rw [h_rearrange]
        exact dvd_mul_of_dvd_right h_factor _
      · -- Case B1: p ∤ |2n+1-2i|
        -- Use b_formula at k = i (which is in [1, 2n])
        have h_factor := factor_out i hi_pos hi hdvd
        -- h_factor: p^e | (2n)! * (2n+1-i)! * i!
        -- scalar_AB(n,i) = (2n)! * (2n+1-i)! * (i+1)! = (i+1) * ((2n)! * (2n+1-i)! * i!)
        rw [h_scalar]
        have h_fact_split : (i + 1).factorial = (i + 1) * i.factorial :=
          Nat.factorial_succ i
        have h_rearrange : (2 * n).factorial * (2 * n + 1 - i).factorial * (i + 1).factorial =
            (i + 1) * ((2 * n).factorial * (2 * n + 1 - i).factorial * i.factorial) := by
          rw [h_fact_split]; ring
        rw [h_rearrange]
        exact dvd_mul_of_dvd_right h_factor _

-- For the non-prime-power upper bound: we need a valid specialization index
-- (one that is ≠ n and ≠ n+1) whose vp_b equals the minimum over [1,2n].
-- This always exists because if the minimum is at n, then by vp_b_witness_bound
-- there is a witness n - p^a with the same or smaller vp_b, and this witness ≠ n, n+1.
-- (If p ∤ n+2, the minimum is not necessarily at n.)
private lemma exists_valid_min_vp_b (p n : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hn : 2 ≤ n)
    (h_not_pp : ∀ k : ℕ, 1 ≤ k → n + 2 ≠ p ^ k) :
    ∃ k₀, 1 ≤ k₀ ∧ k₀ ≤ 2 * n ∧ k₀ ≠ n ∧ k₀ ≠ n + 1 ∧
    ∀ k ∈ Finset.Icc 1 (2 * n), vp_b p n k₀ ≤ vp_b p n k := by
  -- Find the overall minimizer
  have hne : (Finset.Icc 1 (2 * n)).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩⟩
  obtain ⟨k_min, hk_min_mem, hk_min_le⟩ :=
    Finset.exists_min_image (Finset.Icc 1 (2 * n)) (vp_b p n) hne
  have hk_min_bounds := Finset.mem_Icc.mp hk_min_mem
  -- If k_min ∉ {n, n+1}, we're done
  -- Helper: find an off-center index with vp_b ≤ vp_b(n)
  have h_off_center : ∃ w, 1 ≤ w ∧ w ≤ 2 * n ∧ w ≠ n ∧ w ≠ n + 1 ∧
      vp_b p n w ≤ vp_b p n n := by
    by_cases h_div : p ∣ (n + 2)
    · -- Case 2: p | (n+2), use vp_b_witness_bound
      have h_wit := vp_b_witness_bound p n hp5 hn h_div h_not_pp
      have h_pa_le := pa_le_n p n hn h_div h_not_pp
      have ha_pos := a_ge_one p n h_div
      have h_pa_ge : p ^ padicValNat p (n + 2) ≥ 5 := by
        calc p ^ padicValNat p (n + 2) ≥ p ^ 1 := Nat.pow_le_pow_right (by omega) ha_pos
          _ = p := pow_one p
          _ ≥ 5 := hp5
      have h_2pa : n + 2 ≥ 2 * p ^ padicValNat p (n + 2) := by
        have hr := r_ge_two p n hn h_div h_not_pp
        set a := padicValNat p (n + 2) with ha_def
        set r := (n + 2) / p ^ a with hr_def
        have h_pa_dvd : p ^ a ∣ (n + 2) := pow_padicValNat_dvd
        have h_eq : n + 2 = p ^ a * r := by rw [hr_def, Nat.mul_div_cancel' h_pa_dvd]
        nlinarith [pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) a]
      exact ⟨n - p ^ padicValNat p (n + 2), by omega, by omega, by omega, by omega, h_wit⟩
    · -- Case 1: p ∤ (n+2), use vp_b_n_minus_one_le_n
      exact ⟨n - 1, by omega, by omega, by omega, by omega, vp_b_n_minus_one_le_n p n hp5 hn h_div⟩
  obtain ⟨w, hw1, hw2, hwn, hwn1, hw_le⟩ := h_off_center
  -- Now: w is off-center with vp_b(w) ≤ vp_b(n) = vp_b(n+1)
  have h_symm := vp_b_symm_n_n1 p n (by omega)
  -- If k_min ∉ {n, n+1}: use k_min directly
  -- If k_min ∈ {n, n+1}: use w (which has vp_b(w) ≤ vp_b(n) = vp_b(n+1) = vp_b(k_min))
  by_cases hkn : k_min = n ∨ k_min = n + 1
  · -- k_min ∈ {n, n+1}: w has vp_b(w) ≤ vp_b(k_min) and is also ≤ all others
    refine ⟨w, hw1, hw2, hwn, hwn1, fun k hk => ?_⟩
    calc vp_b p n w ≤ vp_b p n n := hw_le
      _ ≤ vp_b p n k_min := by rcases hkn with rfl | rfl <;> [exact le_refl _; exact h_symm.le]
      _ ≤ vp_b p n k := hk_min_le k hk
  · -- k_min ∉ {n, n+1}: use k_min
    push_neg at hkn
    exact ⟨k_min, hk_min_bounds.1, hk_min_bounds.2, hkn.1, hkn.2, fun k hk => hk_min_le k hk⟩

theorem even_of_not_prime_power (p n : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 2 ≤ n)
    (h_not_pp : ∀ k : ℕ, 1 ≤ k → n + 2 ≠ p ^ k) :
    Even (padicValNat p (S n)) := by
  have hn_pos : 0 < n := by omega
  -- Get a valid specialization index achieving the minimum vp_b
  obtain ⟨k₀, hk₀_lo, hk₀_hi, hk₀_ne_n, hk₀_ne_n1, hk₀_min⟩ :=
    exists_valid_min_vp_b p n hp5 hn h_not_pp
  -- e_min = vp_b(k₀) = min of vp_b over [1,2n]
  set e_min := vp_b p n k₀
  -- Step 1: Δ(phi_{k₀}) = b_{k₀}²
  have h_delta_sq : MvPolynomial.eval (phi n k₀) (Δ_n n) = (b_k_val n k₀) ^ 2 := by
    rw [eval_Delta_n_phi_eq_sq n k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1,
        eval_B_phi_eq_bk n k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1 hn_pos]
  have hb_ne : b_k_val n k₀ ≠ 0 := b_k_val_ne_zero n k₀ (by omega) hk₀_lo hk₀_hi
  have h_eval_ne : MvPolynomial.eval (phi n k₀) (Δ_n n) ≠ 0 := by
    rw [h_delta_sq]; exact pow_ne_zero 2 hb_ne
  have hS_ne : S n ≠ 0 := S_ne_zero_of_eval_ne_zero n (phi n k₀) h_eval_ne
  -- Upper bound: v_p(S) ≤ 2 * e_min
  have h_upper : padicValNat p (S n) ≤ 2 * e_min := by
    have h1 := vp_S_le_eval p n (phi n k₀) h_eval_ne
    rw [h_delta_sq] at h1
    simp only [Int.natAbs_pow] at h1
    rw [padicValNat.pow 2 (show Int.natAbs (b_k_val n k₀) ≠ 0 from by
      rwa [Int.natAbs_ne_zero])] at h1
    exact h1
  -- Lower bound from coefficient divisibility
  have he_bformula : ∀ k ∈ Finset.Icc 1 (2 * n),
      e_min ≤ padicValNat p (Int.natAbs (b_formula n k)) := by
    intro k hk; rw [b_formula_eq_b_k_val]; exact hk₀_min k hk
  have hB : ∀ m, ((p ^ e_min : ℕ) : ℤ) ∣ (B_n n).coeff m :=
    coeff_B_n_dvd p n e_min hn_pos he_bformula
  have hA : ∀ m, ((p ^ e_min : ℕ) : ℤ) ∣ (A_n n).coeff m := by
    have h_scalar := scalar_AB_dvd_of_vp_b_min p n hp5 hn_pos e_min he_bformula
    intro m; unfold A_n; erw [MvPolynomial.coeff_sum]
    exact Finset.dvd_sum fun i hi => by
      have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h_dvd : ((p ^ e_min : ℕ) : ℤ) ∣
          ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) * (β n i : ℤ)) := by
        have := Int.natCast_dvd_natCast.mpr (h_scalar i hi')
        convert this.mul_left ((-1 : ℤ) ^ i) using 1; simp [scalar_AB]; push_cast; ring
      rw [MvPolynomial.coeff_mul]; exact Finset.dvd_sum fun x _ => by
        erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']; aesop
  have hC : ∀ m, ((p ^ e_min : ℕ) : ℤ) ∣ (C_n n).coeff m := by
    have h_scalar := scalar_AB_dvd_of_vp_b_min p n hp5 hn_pos e_min he_bformula
    intro m; unfold C_n; erw [MvPolynomial.coeff_sum]
    exact Finset.dvd_sum fun i hi => by
      have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h_dvd : ((p ^ e_min : ℕ) : ℤ) ∣
          ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) * (β n i : ℤ)) := by
        have := Int.natCast_dvd_natCast.mpr (h_scalar i hi')
        convert this.mul_left ((-1 : ℤ) ^ i) using 1; simp [scalar_AB]; push_cast; ring
      generalize_proofs at *
      rw [MvPolynomial.coeff_mul]; exact Finset.dvd_sum fun x _ => by
        erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']; aesop
  have h_coeff : ∀ m ∈ (Δ_n n).support,
      p ^ (2 * e_min) ∣ Int.natAbs ((Δ_n n).coeff m) := by
    intro m _
    have h2e := coeff_Δ_n_dvd_sq p n e_min hA hB hC m
    exact Int.natCast_dvd.mp h2e
  have h_lower : 2 * e_min ≤ padicValNat p (S n) :=
    vp_S_ge_of_coeff_dvd p n (2 * e_min) hS_ne h_coeff
  exact ⟨e_min, by omega⟩

/-! ## Main Theorem -/

/--
**Theorem 1.3 (for p ≥ 5, n ≥ 2).** For every prime p ≥ 5 and every n ≥ 2,
the p-adic valuation of the content S(n) of the quartic invariant
is odd if and only if n + 2 is a power of p.
-/
theorem main_theorem (p n : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 2 ≤ n) :
    Odd (padicValNat p (S n)) ↔ ∃ k : ℕ, 1 ≤ k ∧ n + 2 = p ^ k := by
  constructor
  · -- Forward: Odd → ∃ k, n+2 = p^k (by contrapositive)
    intro hodd
    by_contra h_not
    push_neg at h_not
    exact absurd hodd (by rw [Nat.not_odd_iff_even]; exact even_of_not_prime_power p n hp5 hn h_not)
  · -- Backward: ∃ k, n+2 = p^k → Odd
    rintro ⟨k, hk, hpow⟩
    exact odd_of_prime_power p n hp5 (by linarith) k hk hpow

end QuarticInvariant
