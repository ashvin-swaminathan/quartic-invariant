import Mathlib
import Modular.Defs
import Modular.ScalarBounds
import Modular.CentralDom
import Modular.CoeffDivPP

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 12800000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## Step 6.6: Witness k₀ properties -/

private lemma two_pow_eq_two_mul {K : ℕ} (hK : 1 ≤ K) :
    2 ^ K = 2 * 2 ^ (K - 1) := by
  cases K with
  | zero => omega
  | succ k => simp [pow_succ, mul_comm]

-- Helper: omega-friendly form of n + 2 = 2^K => useful inequalities
private lemma n_bound (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    n = 2 * 2 ^ (K - 1) - 2 ∧ 2 ≤ 2 ^ (K - 1) := by
  constructor
  · have h2 : 2 ^ K = 2 * 2 ^ (K - 1) := two_pow_eq_two_mul (by omega); omega
  · calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (K - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem k0_le_two_n (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    n + 2 ^ (K - 1) ≤ 2 * n := by
  obtain ⟨hn_eq, h_pow_ge⟩ := n_bound K hK n hn; omega

theorem k0_ne_n (K : ℕ) (_ : 2 ≤ K) (n : ℕ) (_ : n + 2 = 2 ^ K) :
    n + 2 ^ (K - 1) ≠ n := by
  have : 0 < 2 ^ (K - 1) := Nat.pos_of_ne_zero (by positivity); omega

theorem k0_ne_n_succ (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    n + 2 ^ (K - 1) ≠ n + 1 := by
  obtain ⟨_, h_pow_ge⟩ := n_bound K hK n hn; omega

theorem k0_even (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    Even (n + 2 ^ (K - 1)) := by
  obtain ⟨hn_eq, h_pow_ge⟩ := n_bound K hK n hn
  rw [hn_eq]
  -- 2 * 2^(K-1) - 2 + 2^(K-1) = 3 * 2^(K-1) - 2
  -- Even because both n and 2^(K-1) are even
  have hev_n : Even (2 * 2 ^ (K - 1) - 2) := ⟨2 ^ (K - 1) - 1, by omega⟩
  have hev_pow : Even (2 ^ (K - 1)) := by
    cases K with
    | zero => omega
    | succ k =>
      cases k with
      | zero => omega
      | succ k =>
        show Even (2 ^ (k + 1))
        exact ⟨2 ^ k, by rw [pow_succ]; ring⟩
  exact hev_n.add hev_pow

theorem k0_succ_odd (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    ¬ 2 ∣ (n + 2 ^ (K - 1) + 1) := by
  obtain ⟨r, hr⟩ := k0_even K hK n hn
  intro ⟨m, hm⟩; omega

theorem v2_k0_succ_eq_zero (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    padicValNat 2 (n + 2 ^ (K - 1) + 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (k0_succ_odd K hK n hn)

theorem two_pow_sub_one_odd (K : ℕ) (hK : 1 ≤ K) : ¬ 2 ∣ (2 ^ K - 1) := by
  intro ⟨m, hm⟩
  have h1 : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by norm_num)
  obtain ⟨r, hr⟩ := show 2 ∣ 2 ^ K from ⟨2 ^ (K - 1), by rw [two_pow_eq_two_mul hK]⟩
  omega

theorem n_succ_odd (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    ¬ 2 ∣ (n + 1) := by
  rw [show n + 1 = 2 ^ K - 1 from by omega]
  exact two_pow_sub_one_odd K (by omega)

theorem k0_succ_eq (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    n + 2 ^ (K - 1) + 1 = 3 * 2 ^ (K - 1) - 1 := by
  obtain ⟨hn_eq, h_pow_ge⟩ := n_bound K hK n hn; omega

/-! ## Step 6.7: v₂(b_{k₀}) formula -/

private lemma padicValNat_two_eq : padicValNat 2 2 = 1 :=
  padicValNat.self (by norm_num)

private lemma natAbs_two_mul_neg_one_pow_mul (k : ℕ) (z : ℤ) :
    Int.natAbs (2 * (-1 : ℤ) ^ k * z) = 2 * Int.natAbs z := by
  rw [Int.natAbs_mul, Int.natAbs_mul]
  simp [show Int.natAbs (2 : ℤ) = 2 from rfl, show Int.natAbs ((-1 : ℤ) ^ k) = 1 from by simp]

theorem v2_b_k0_formula (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    padicValNat 2 (Int.natAbs (b_formula n (n + 2 ^ (K - 1)))) =
      1 + padicValNat 2 (scalar_AB n (n + 2 ^ (K - 1))) := by
  set k₀ := n + 2 ^ (K - 1) with hk₀_def
  have hk₀_le : k₀ ≤ 2 * n := k0_le_two_n K hK n hn
  have h_fact := b_formula_factored n k₀ hk₀_le
  have h_sAB := scalar_AB_formula n k₀ hk₀_le
  have h2K : 2 ^ K = 2 * 2 ^ (K - 1) := two_pow_eq_two_mul (by omega)
  have h_int_val : (2 * (n : ℤ) + 1 - 2 * k₀) = 1 - 2 ^ K := by
    push_cast [hk₀_def]; linarith [show (2 : ℤ) ^ K = 2 * 2 ^ (K - 1) from by exact_mod_cast h2K]
  rw [h_fact, natAbs_two_mul_neg_one_pow_mul]
  have h_P_ne : Int.natAbs (((2 * n).factorial : ℤ) * ((2 * ↑n : ℤ) + 1 - 2 * ↑k₀) *
      ((2 * n + 1 - k₀).factorial : ℤ) * (k₀.factorial : ℤ)) ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    apply mul_ne_zero; apply mul_ne_zero; apply mul_ne_zero
    · exact_mod_cast (Nat.factorial_pos _).ne'
    · rw [h_int_val]
      have : (2 : ℤ) ^ K ≥ 4 := by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hK
      omega
    · exact_mod_cast (Nat.factorial_pos _).ne'
    · exact_mod_cast (Nat.factorial_pos _).ne'
  rw [padicValNat.mul (by norm_num) h_P_ne, padicValNat_two_eq]
  congr 1
  have h_neg : (2 * (n : ℤ) + 1 - 2 * ↑k₀) = -((2 : ℤ) ^ K - 1) := by linarith [h_int_val]
  have h_natabs : Int.natAbs (((2 * n).factorial : ℤ) * ((2 * ↑n : ℤ) + 1 - 2 * ↑k₀) *
      ((2 * n + 1 - k₀).factorial : ℤ) * (k₀.factorial : ℤ)) =
      (2 * n).factorial * (2 ^ K - 1) * (2 * n + 1 - k₀).factorial * k₀.factorial := by
    rw [h_neg]
    rw [show (2 : ℤ) ^ K - 1 = ((2 ^ K - 1 : ℕ) : ℤ) from by
      rw [Nat.cast_sub (Nat.one_le_pow K 2 (by norm_num))]; simp]
    rw [show ((2 * n).factorial : ℤ) * (-(↑(2 ^ K - 1 : ℕ))) * ↑(2 * n + 1 - k₀).factorial * ↑k₀.factorial =
        -(↑((2 * n).factorial * (2 ^ K - 1) * (2 * n + 1 - k₀).factorial * k₀.factorial)) from by push_cast; ring]
    rw [Int.natAbs_neg, Int.natAbs_natCast]
  rw [h_natabs, h_sAB, Nat.factorial_succ]
  have h_odd_M : padicValNat 2 (2 ^ K - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (two_pow_sub_one_odd K (by omega))
  have h_odd_k0 : padicValNat 2 (k₀ + 1) = 0 :=
    v2_k0_succ_eq_zero K hK n hn
  have h1 : 2 ^ K - 1 ≠ 0 := by
    have := Nat.one_le_pow K 2 (by norm_num); omega
  rw [padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
      padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
      padicValNat.mul (Nat.factorial_pos _).ne' h1]
  rw [padicValNat.mul (by positivity) (by positivity),
      padicValNat.mul (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne']
  rw [padicValNat.mul (by omega : k₀ + 1 ≠ 0) (Nat.factorial_pos _).ne']
  rw [h_odd_M, h_odd_k0]
  ring

/-! ## Step 6.8: CRS argument — v₂(scalar_AB(n,k₀)) = v₂(scalar_AB(n,n)) + 1 -/

private theorem v2_scalar_AB_split (n i : ℕ) (hi : i ≤ 2 * n) :
    padicValNat 2 (scalar_AB n i) =
      padicValNat 2 (2 * n).factorial +
      padicValNat 2 (2 * n + 1 - i).factorial +
      padicValNat 2 (i + 1).factorial := by
  rw [scalar_AB_formula n i hi,
      padicValNat.mul (by positivity) (by positivity),
      padicValNat.mul (by positivity) (by positivity)]

private theorem v2_central_binom (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    padicValNat 2 (Nat.choose (2 * n + 2) (n + 1)) = K := by
  rw [show 2 * n + 2 = 2 * (2 ^ K - 1) from by omega,
      show n + 1 = 2 ^ K - 1 from by omega]
  exact padicValNat_choose_central 2 K (by omega)

private lemma mod_pred_of_dvd (m i : ℕ) (hm : 0 < m) (hdvd : 2 ^ i ∣ m) :
    (m - 1) % 2 ^ i = 2 ^ i - 1 := by
  have hi_pos : 0 < 2 ^ i := Nat.pos_of_ne_zero (by positivity)
  obtain ⟨c, hc⟩ := hdvd
  subst hc
  cases c with
  | zero => simp at hm
  | succ c =>
    have h_one_le : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by norm_num)
    have h1 : 2 ^ i * (c + 1) - 1 = 2 ^ i * c + (2 ^ i - 1) := by
      have : 2 ^ i * (c + 1) = 2 ^ i * c + 2 ^ i := by ring
      omega
    rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

theorem v2_choose_at_k0 (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    padicValNat 2 (Nat.choose (2 * n + 2) (n + 2 ^ (K - 1) + 1)) = K - 1 := by
  set k₀ := n + 2 ^ (K - 1)
  have h2K : 2 ^ K = 2 * 2 ^ (K - 1) := two_pow_eq_two_mul (by omega)
  have h_le : k₀ + 1 ≤ 2 * n + 2 := by
    have := k0_le_two_n K hK n hn; omega
  have h_complement : 2 * n + 2 - (k₀ + 1) = 2 ^ (K - 1) - 1 := by omega
  rw [padicValNat_choose (b := K + 1)]
  · have h_filter_eq : Finset.filter
        (fun i => 2 ^ i ≤ (k₀ + 1) % 2 ^ i + (2 * n + 2 - (k₀ + 1)) % 2 ^ i)
        (Finset.Ico 1 (K + 1)) = Finset.Ico 1 K := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · intro ⟨⟨hi_lo, hi_hi⟩, h_carry⟩
        refine ⟨hi_lo, ?_⟩
        by_contra h_not_lt
        push_neg at h_not_lt
        have hi_eq : i = K := by omega
        -- After rewriting i → K everywhere
        rw [h_complement] at h_carry
        rw [k0_succ_eq K hK n hn] at h_carry
        rw [hi_eq] at h_carry
        have h_3_ge : 3 * 2 ^ (K - 1) - 1 ≥ 2 ^ K := by omega
        have h_mod1 : (3 * 2 ^ (K - 1) - 1) % 2 ^ K = 2 ^ (K - 1) - 1 := by
          rw [Nat.mod_eq_sub_mod h_3_ge, Nat.mod_eq_of_lt (by omega)]; omega
        have h_mod2 : (2 ^ (K - 1) - 1) % 2 ^ K = 2 ^ (K - 1) - 1 :=
          Nat.mod_eq_of_lt (by
            have := Nat.pow_le_pow_right (show 0 < 2 from by norm_num) (show K - 1 ≤ K from by omega)
            omega)
        rw [h_mod1, h_mod2] at h_carry
        -- h_carry : 2^K ≤ (2^(K-1) - 1) + (2^(K-1) - 1) but 2^K = 2*2^(K-1) > that
        have h_pos : 1 ≤ 2 ^ (K - 1) := Nat.one_le_pow (K-1) 2 (by norm_num)
        -- 2*(2^(K-1) - 1) = 2*2^(K-1) - 2 < 2*2^(K-1) = 2^K
        have h_sum_bound : 2 ^ (K - 1) - 1 + (2 ^ (K - 1) - 1) = 2 * 2 ^ (K - 1) - 2 := by omega
        rw [h_sum_bound] at h_carry
        omega
      · intro ⟨hi_lo, hi_lt_K⟩
        refine ⟨⟨hi_lo, by omega⟩, ?_⟩
        rw [h_complement, k0_succ_eq K hK n hn]
        have h_i_le : i ≤ K - 1 := by omega
        have h_mod1 : (3 * 2 ^ (K - 1) - 1) % 2 ^ i = 2 ^ i - 1 :=
          mod_pred_of_dvd (3 * 2 ^ (K - 1)) i (by positivity)
            (dvd_mul_of_dvd_right (pow_dvd_pow 2 h_i_le) 3)
        have h_mod2 : (2 ^ (K - 1) - 1) % 2 ^ i = 2 ^ i - 1 :=
          mod_pred_of_dvd (2 ^ (K - 1)) i (by positivity) (pow_dvd_pow 2 h_i_le)
        rw [h_mod1, h_mod2]
        have : 2 ≤ 2 ^ i :=
          le_trans (show 2 ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by norm_num) hi_lo)
        omega
    rw [h_filter_eq]
    exact Nat.card_Ico 1 K
  · exact h_le
  · have h_lt : 2 * n + 2 < 2 ^ (K + 1) := by
      have h2K := two_pow_eq_two_mul (show 1 ≤ K + 1 from by omega)
      -- 2^(K+1) = 2 * 2^K, and 2*n+2 = 2*(2^K - 1) = 2*2^K - 2 < 2*2^K = 2^(K+1)
      omega
    exact Nat.log_lt_of_lt_pow (by omega) h_lt

/-- THE MAIN THEOREM (Step 6.8):
    v₂(scalar_AB(n, k₀)) = v₂(scalar_AB(n, n)) + 1 -/
theorem v2_scalar_AB_k0_eq (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    padicValNat 2 (scalar_AB n (n + 2 ^ (K - 1))) =
      padicValNat 2 (scalar_AB n n) + 1 := by
  set k₀ := n + 2 ^ (K - 1) with hk₀_def
  have hk₀_le : k₀ ≤ 2 * n := k0_le_two_n K hK n hn
  rw [v2_scalar_AB_split n k₀ hk₀_le,
      v2_scalar_AB_split n n (by omega),
      show 2 * n + 1 - n = n + 1 from by omega]
  have h_sum_k0 : (k₀ + 1) + (2 * n + 1 - k₀) = 2 * n + 2 := by omega
  have h_fs_k0 : padicValNat 2 (k₀ + 1).factorial +
      padicValNat 2 (2 * n + 1 - k₀).factorial +
      padicValNat 2 (Nat.choose (2 * n + 2) (k₀ + 1)) =
      padicValNat 2 (2 * n + 2).factorial := by
    have := padicValNat_factorial_sum 2 (k₀ + 1) (2 * n + 1 - k₀)
    rw [h_sum_k0] at this; linarith
  have h_fs_center : padicValNat 2 (n + 1).factorial +
      padicValNat 2 (n + 1).factorial +
      padicValNat 2 (Nat.choose (2 * n + 2) (n + 1)) =
      padicValNat 2 (2 * n + 2).factorial := by
    have := padicValNat_factorial_sum 2 (n + 1) (n + 1)
    rw [show (n + 1) + (n + 1) = 2 * n + 2 from by omega] at this; linarith
  have h_central := v2_central_binom K hK n hn
  have h_k0_binom := v2_choose_at_k0 K hK n hn
  -- From h_fs_k0: (k₀+1)! + (2n+1-k₀)! = (2n+2)! - (K-1)
  -- From h_fs_center: 2*(n+1)! = (2n+2)! - K
  -- Difference: [(2n+2)! - (K-1)] - [(2n+2)! - K] = K - (K-1) = 1 (since K ≥ 2)
  have hK1 : K - 1 + 1 = K := by omega
  linarith

/-! ## Step 6.9: Final bounds -/

theorem v2_b_center (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    padicValNat 2 (Int.natAbs (b_formula n n)) =
      1 + padicValNat 2 (scalar_AB n n) := by
  have h_le : n ≤ 2 * n := by omega
  have h_fact := b_formula_factored n n h_le
  have h_sAB := scalar_AB_formula n n h_le
  have h_int_val : (2 * (n : ℤ) + 1 - 2 * n) = 1 := by ring
  rw [h_fact, show 2 * n + 1 - n = n + 1 from by omega]
  have h_P_ne : Int.natAbs (((2 * n).factorial : ℤ) * ((2 * ↑n : ℤ) + 1 - 2 * ↑n) *
      ((n + 1).factorial : ℤ) * (n.factorial : ℤ)) ≠ 0 := by
    rw [Int.natAbs_ne_zero, h_int_val]
    simp only [mul_one]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne')
      (by exact_mod_cast (Nat.factorial_pos _).ne')) (by exact_mod_cast (Nat.factorial_pos _).ne')
  rw [natAbs_two_mul_neg_one_pow_mul,
      padicValNat.mul (by norm_num) h_P_ne, padicValNat_two_eq]
  congr 1
  have h_natabs : Int.natAbs (((2 * n).factorial : ℤ) * ((2 * ↑n : ℤ) + 1 - 2 * ↑n) *
      ((n + 1).factorial : ℤ) * (n.factorial : ℤ)) =
      (2 * n).factorial * (n + 1).factorial * n.factorial := by
    rw [h_int_val]; simp only [mul_one, Int.natAbs_mul]; simp [Int.natAbs_natCast]
  rw [h_natabs, h_sAB, show 2 * n + 1 - n = n + 1 from by omega]
  -- LHS: v₂((2n)! * (n+1)! * n!)
  -- RHS: v₂((2n)! * (n+1)! * (n+1)!)
  -- (n+1)! = (n+1) * n!, v₂(n+1) = 0
  -- So v₂((n+1)!) = v₂(n+1) + v₂(n!) = v₂(n!)
  -- RHS = v₂((2n)!) + v₂((n+1)!) + v₂((n+1)!) = v₂((2n)!) + 2*v₂(n!)
  -- LHS = v₂((2n)!) + v₂((n+1)!) + v₂(n!) = v₂((2n)!) + 2*v₂(n!)
  have h_v2_n1 : padicValNat 2 (n + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (n_succ_odd K hK n hn)
  have h_n1_fact : padicValNat 2 (n + 1).factorial = padicValNat 2 n.factorial := by
    rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_pos _).ne', h_v2_n1, zero_add]
  -- Split both sides
  rw [padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
      padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
      padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
      padicValNat.mul (by positivity) (Nat.factorial_pos _).ne']
  linarith [h_n1_fact]

theorem v2_b_k0 (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    padicValNat 2 (Int.natAbs (b_formula n (n + 2 ^ (K - 1)))) =
      padicValNat 2 (Int.natAbs (b_formula n n)) + 1 := by
  rw [v2_b_k0_formula K hK n hn,
      v2_b_center K hK n hn,
      v2_scalar_AB_k0_eq K hK n hn]
  ring

end QuarticInvariant
