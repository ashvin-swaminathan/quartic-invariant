import Mathlib
import Modular.Defs
import Modular.CentralDom
import Modular.KummerCarry
import Modular.ScalarBounds

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant


/-! ### Helper: ℤ ↔ ℕ divisibility for p-adic valuations -/

private lemma int_pow_dvd_natAbs {p : ℕ} {e : ℕ} {a : ℤ}
    (h : (p : ℤ) ^ e ∣ a) : p ^ e ∣ a.natAbs := by
  have := Int.natAbs_dvd_natAbs.mpr h
  simpa [Int.natAbs_pow, Int.natAbs_natCast] using this

private lemma natAbs_dvd_int_pow {p : ℕ} {e : ℕ} {a : ℤ}
    (h : p ^ e ∣ a.natAbs) : (p : ℤ) ^ e ∣ a :=
  Int.natAbs_dvd_natAbs.mp (by simpa [Int.natAbs_pow, Int.natAbs_natCast] using h)

/-! ### Ultrametric lemma for p-adic valuations -/

/-- If v_p(a) = e and p^{e+1} | b, then v_p(a+b) = e. -/
private lemma padic_val_add_of_strict_lt (p : ℕ) [hp : Fact p.Prime] (a b : ℤ) (e : ℕ)
    (ha_ne : a ≠ 0)
    (ha_val : padicValNat p (Int.natAbs a) = e)
    (hb_dvd : (p : ℤ) ^ (e + 1) ∣ b) :
    a + b ≠ 0 ∧ padicValNat p (Int.natAbs (a + b)) = e := by
  have ha_dvd : (p : ℤ) ^ e ∣ a :=
    natAbs_dvd_int_pow ((padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr ha_ne)).mpr (by omega))
  have ha_ndvd : ¬ (p : ℤ) ^ (e + 1) ∣ a := by
    intro h
    have := (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr ha_ne)).mp (int_pow_dvd_natAbs h)
    omega
  have hpe_dvd_b : (p : ℤ) ^ e ∣ b := dvd_trans (pow_dvd_pow _ (Nat.le_succ _)) hb_dvd
  have hab_ne : a + b ≠ 0 := by
    intro hab
    apply ha_ndvd
    have heq : a = -b := by linarith
    rw [heq]
    exact dvd_neg.mpr hb_dvd
  have hab_dvd : (p : ℤ) ^ e ∣ a + b := dvd_add ha_dvd hpe_dvd_b
  have hab_ndvd : ¬ (p : ℤ) ^ (e + 1) ∣ a + b := by
    intro h
    apply ha_ndvd
    have heq : a = (a + b) - b := by ring
    rw [heq]
    exact dvd_sub h hb_dvd
  refine ⟨hab_ne, le_antisymm ?_ ?_⟩
  · by_contra h
    push_neg at h
    apply hab_ndvd
    exact natAbs_dvd_int_pow
      ((padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hab_ne)).mpr (by omega))
  · exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hab_ne)).mp
      (int_pow_dvd_natAbs hab_dvd)

/-! ### B_eval summand analysis under deform_spec -/

/-- The B_eval summand function. -/
private def f_B (n t : ℕ) (i : ℕ) : ℤ :=
    (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      ((α n i : ℤ) ^ 2 * deform_spec n t i * deform_spec n t (2 * n + 1 - i) +
       (β n i : ℤ) ^ 2 * deform_spec n t (i + 1) * deform_spec n t (2 * n - i))

/-- Summands vanish for indices far from center and off-center. -/
private lemma f_B_zero (n t i : ℕ) (ht : 2 ≤ t) (htn : t + 2 ≤ n)
    (h1 : i ≠ n - t - 1) (h2 : i ≠ n - t) (h3 : i ≠ n - 1) (h4 : i ≠ n)
    (h5 : i ≠ n + 1) (h6 : i ≠ n + t) (h7 : i ≠ n + t + 1) :
    f_B n t i = 0 := by
  unfold f_B
  have : deform_spec n t i = 0 := by unfold deform_spec; split_ifs <;> omega
  have : deform_spec n t (i + 1) = 0 := by unfold deform_spec; split_ifs <;> omega
  simp [*]

/-- At i = n: the summand equals -2 * u_val n. -/
private lemma f_B_at_n (n t : ℕ) (ht : 2 ≤ t) (htn : t + 2 ≤ n) :
    f_B n t n = -2 * u_val n := by
  unfold f_B u_val
  have hα : α n n = γ n := by unfold α γ; rw [show 2 * n + 1 - n = n + 1 from by omega]
  have hβ : β n n = γ n := by unfold β γ; rw [show 2 * n - n = n from by omega]; ring
  have h1 : deform_spec n t n = 1 := by unfold deform_spec; split_ifs <;> omega <;> rfl
  have h2 : deform_spec n t (2 * n + 1 - n) = -1 := by
    rw [show 2 * n + 1 - n = n + 1 from by omega]; unfold deform_spec; split_ifs <;> omega
  have h3 : deform_spec n t (n + 1) = -1 := by unfold deform_spec; split_ifs <;> omega
  have h4 : deform_spec n t (2 * n - n) = 1 := by
    rw [show 2 * n - n = n from by omega]; unfold deform_spec; split_ifs <;> omega <;> rfl
  rw [h1, h2, h3, h4, hα, hβ]; ring

/-- At i = n-1: only the β² part survives, giving (-1)^n * C(2n,n-1) * γ². -/
private lemma f_B_at_nm1 (n t : ℕ) (ht : 2 ≤ t) (htn : t + 2 ≤ n) :
    f_B n t (n - 1) =
    (-1 : ℤ) ^ n * (Nat.choose (2 * n) (n - 1) : ℤ) * ((γ n : ℤ) ^ 2) := by
  unfold f_B
  have hc1 : deform_spec n t (n - 1) = 0 := by unfold deform_spec; split_ifs <;> omega
  have hc2 : deform_spec n t (2 * n + 1 - (n - 1)) = 0 := by
    rw [show 2 * n + 1 - (n - 1) = n + 2 from by omega]
    unfold deform_spec; split_ifs <;> omega
  have hc3 : deform_spec n t (n - 1 + 1) = 1 := by
    rw [show n - 1 + 1 = n from by omega]
    unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc4 : deform_spec n t (2 * n - (n - 1)) = -1 := by
    rw [show 2 * n - (n - 1) = n + 1 from by omega]
    unfold deform_spec; split_ifs <;> omega
  have hβ : β n (n - 1) = γ n := by
    unfold β γ
    rw [show 2 * n - (n - 1) = n + 1 from by omega, show n - 1 + 1 = n from by omega]
  rw [hc1, hc2, hc3, hc4, hβ]
  have hpow : (-1 : ℤ) ^ (n - 1) = -(-1 : ℤ) ^ n := by
    conv_rhs => rw [show n = n - 1 + 1 from by omega, pow_succ]; ring
  rw [hpow]; ring

/-- At i = n+1: only the α² part survives, giving (-1)^n * C(2n,n+1) * γ². -/
private lemma f_B_at_np1 (n t : ℕ) (ht : 2 ≤ t) (htn : t + 2 ≤ n) :
    f_B n t (n + 1) =
    (-1 : ℤ) ^ n * (Nat.choose (2 * n) (n + 1) : ℤ) * ((γ n : ℤ) ^ 2) := by
  unfold f_B
  have hc1 : deform_spec n t (n + 1) = -1 := by unfold deform_spec; split_ifs <;> omega
  have hc2 : deform_spec n t (2 * n + 1 - (n + 1)) = 1 := by
    rw [show 2 * n + 1 - (n + 1) = n from by omega]
    unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc3 : deform_spec n t ((n + 1) + 1) = 0 := by
    rw [show (n + 1) + 1 = n + 2 from by omega]
    unfold deform_spec; split_ifs <;> omega
  have hα : α n (n + 1) = γ n := by
    unfold α γ; rw [show 2 * n + 1 - (n + 1) = n from by omega]; ring
  rw [hc1, hc2, hc3, hα]
  have hpow : (-1 : ℤ) ^ (n + 1) = -(-1 : ℤ) ^ n := by simp [pow_succ]
  rw [hpow]; ring

/-- C(2n, n+1) = C(2n, n-1) by symmetry. -/
private lemma choose_symm' (n : ℕ) (hn : 1 ≤ n) :
    (Nat.choose (2 * n) (n + 1) : ℤ) = (Nat.choose (2 * n) (n - 1) : ℤ) := by
  congr 1
  have h := Nat.choose_symm (show n - 1 ≤ 2 * n from by omega)
  rw [show 2 * n - (n - 1) = n + 1 from by omega] at h; exact h

/-- Finset sum expansion for the 7-element active set. -/
private lemma finset_expand (f : ℕ → ℤ) (n t : ℕ) (ht : 2 ≤ t) (htn : t + 2 ≤ n) :
    ∑ i ∈ ({n - t - 1, n - t, n - 1, n, n + 1, n + t, n + t + 1} : Finset ℕ), f i =
    f (n - t - 1) + f (n - t) + f (n - 1) + f n + f (n + 1) + f (n + t) + f (n + t + 1) := by
  rw [Finset.sum_insert (show n - t - 1 ∉ ({n - t, n - 1, n, n + 1, n + t, n + t + 1} : Finset ℕ)
    from by simp; omega)]
  rw [Finset.sum_insert (show n - t ∉ ({n - 1, n, n + 1, n + t, n + t + 1} : Finset ℕ)
    from by simp; omega)]
  rw [Finset.sum_insert (show n - 1 ∉ ({n, n + 1, n + t, n + t + 1} : Finset ℕ)
    from by simp; omega)]
  rw [Finset.sum_insert (show n ∉ ({n + 1, n + t, n + t + 1} : Finset ℕ)
    from by simp; omega)]
  rw [Finset.sum_insert (show n + 1 ∉ ({n + t, n + t + 1} : Finset ℕ)
    from by simp; omega)]
  rw [Finset.sum_pair (show n + t ≠ n + t + 1 from by omega)]
  ring

/-! ### Off-center contribution -/

/-- The off-center terms: contributions from i ∈ {n-t-1, n-t, n+t, n+t+1}. -/
private def R_off (n t : ℕ) : ℤ :=
  f_B n t (n - t - 1) + f_B n t (n - t) + f_B n t (n + t) + f_B n t (n + t + 1)

/-! ### Bplus formula: B_eval + 2u = 2*(-1)^n*C(2n,n-1)*γ² + R_off -/

/-- The explicit formula for Bplus = B_eval + 2u. -/
private lemma Bplus_formula (n t : ℕ) (ht : 2 ≤ t) (htn : t + 2 ≤ n) :
    B_eval n (deform_spec n t) + 2 * u_val n =
    2 * (-1 : ℤ) ^ n * (Nat.choose (2 * n) (n - 1) : ℤ) * ((γ n : ℤ) ^ 2) + R_off n t := by
  have hB : B_eval n (deform_spec n t) =
    ∑ i ∈ ({n - t - 1, n - t, n - 1, n, n + 1, n + t, n + t + 1} : Finset ℕ), f_B n t i := by
    unfold B_eval; show _ = _; symm
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hx ⊢; omega
    · intro x hx hxA
      apply f_B_zero n t x ht htn <;> (intro heq; exact hxA (by simp [heq]))
  rw [hB, finset_expand _ n t ht htn,
      f_B_at_n n t ht htn, f_B_at_nm1 n t ht htn, f_B_at_np1 n t ht htn,
      choose_symm' n (by omega)]
  unfold R_off; ring

/-! ### p-adic valuation helpers (arithmetic core) -/

/-- p does not divide n+1 when n+2 = p^k. -/
private lemma p_not_dvd_n1 (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) : ¬ p ∣ (n + 1) := by
  intro hdvd
  have h1 := Int.ofNat_dvd.mpr (show p ∣ n + 2 from hn ▸ dvd_pow_self p (by omega))
  have h3 : (p : ℤ) ∣ 1 := by
    convert dvd_sub h1 (Int.ofNat_dvd.mpr hdvd) using 1; push_cast; ring
  exact Nat.Prime.one_lt Fact.out |>.ne'
    (Nat.eq_one_of_dvd_one (Int.ofNat_dvd.mp (by exact_mod_cast h3)))

/-- p does not divide n when n+2 = p^k and p is odd. -/
private lemma p_not_dvd_n (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2) (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) : ¬ p ∣ n := by
  intro hdvd
  have h1 := Int.ofNat_dvd.mpr (show p ∣ n + 2 from hn ▸ dvd_pow_self p (by omega))
  have h3 : (p : ℤ) ∣ 2 := by
    convert dvd_sub h1 (Int.ofNat_dvd.mpr hdvd) using 1; push_cast; ring
  have hp2 : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) h3
  have hp_ge : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have : p = 2 := by omega
  exact absurd this hp_odd

/-- C(2n,n-1)*(n+1) = C(2n,n)*n. -/
private lemma choose_identity (n : ℕ) (hn : 1 ≤ n) :
    Nat.choose (2 * n) (n - 1) * (n + 1) = Nat.choose (2 * n) n * n := by
  have h1 : Nat.choose (2 * n) (n + 1) * (n + 1) = Nat.choose (2 * n) n * n := by
    have h := Nat.choose_succ_right_eq (2 * n) n
    rw [show 2 * n - n = n from by omega] at h; exact h
  have h2 : Nat.choose (2 * n) (n - 1) = Nat.choose (2 * n) (n + 1) := by
    have h := Nat.choose_symm (show n - 1 ≤ 2 * n from by omega)
    rw [show 2 * n - (n - 1) = n + 1 from by omega] at h; exact h.symm
  rw [h2]; exact h1

/-- v_p(C(2n,n-1) * γ²) = e_central p n.
Uses C(2n,n-1) = C(2n,n)*n/(n+1), v_p(n) = 0, v_p(n+1) = 0. -/
private lemma choose_nm1_val (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    Nat.choose (2 * n) (n - 1) * (γ n) ^ 2 ≠ 0 ∧
    padicValNat p (Nat.choose (2 * n) (n - 1) * (γ n) ^ 2) = e_central p n := by
  have hchoose_ne : Nat.choose (2 * n) (n - 1) ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hgamma_ne : (γ n) ^ 2 ≠ 0 := Nat.ne_of_gt (by unfold γ; positivity)
  have hchoose_n_ne : Nat.choose (2 * n) n ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  constructor
  · exact mul_ne_zero hchoose_ne hgamma_ne
  · unfold e_central
    have hvn : padicValNat p n = 0 := by
      rw [padicValNat.eq_zero_iff]; right; right; exact p_not_dvd_n p hp_odd k (by omega) n hn
    have hvn1 : padicValNat p (n + 1) = 0 := by
      rw [padicValNat.eq_zero_iff]; right; right; exact p_not_dvd_n1 p k (by omega) n hn
    have hident := choose_identity n hn_pos
    have h_val : padicValNat p (Nat.choose (2 * n) (n - 1) * (n + 1)) =
                 padicValNat p (Nat.choose (2 * n) n * n) := congr_arg _ hident
    rw [padicValNat.mul hchoose_ne (show n + 1 ≠ 0 from by omega), hvn1,
        padicValNat.mul hchoose_n_ne (show n ≠ 0 from by omega), hvn] at h_val
    simp only [add_zero] at h_val
    rw [padicValNat.mul hchoose_ne hgamma_ne, padicValNat.mul hchoose_n_ne hgamma_ne, h_val]

/-- p^{e+1} divides the off-center sum R_off. -/
private lemma R_off_dvd (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    let t := p ^ (k - 1)
    (p : ℤ) ^ (e_central p n + 1) ∣ R_off n t := by
  intro t
  -- Derive basic bounds
  have hp_prime := (Fact.out : p.Prime)
  have hp_ge : 3 ≤ p := by have := hp_prime.two_le; omega
  have ht_ge_2 : 2 ≤ t := le_trans (show 2 ≤ p from by omega) (Nat.le_self_pow (by omega) p)
  have htn : t + 2 ≤ n := by
    have h1 : p ^ k = p * p ^ (k - 1) := by
      cases k with | zero => omega | succ k => simp [pow_succ, mul_comm]
    have hp_le_t : p ≤ t := Nat.le_self_pow (show k - 1 ≠ 0 from by omega) p
    -- n + 2 = p^k = p * t, t ≥ p ≥ 3, so n = p*t - 2 ≥ 3*t - 2 ≥ t + 2
    have h2 : n + 2 = p * t := by rw [hn, h1]
    have : p * t ≥ 3 * t := Nat.mul_le_mul_right t hp_ge
    omega
  -- Evaluate f_B at each off-center index
  have hfB1 : f_B n t (n - t - 1) =
      (-1 : ℤ) ^ (n - t - 1) * ((Nat.choose (2 * n) (n - t - 1) : ℤ) *
        (β n (n - t - 1) : ℤ) ^ 2) := by
    unfold f_B
    have hc1 : deform_spec n t (n - t - 1) = 0 := by unfold deform_spec; split_ifs <;> omega
    have hc2 : deform_spec n t (2 * n + 1 - (n - t - 1)) = 0 := by
      rw [show 2 * n + 1 - (n - t - 1) = n + t + 2 from by omega]
      unfold deform_spec; split_ifs <;> omega
    have hc3 : deform_spec n t (n - t - 1 + 1) = 1 := by
      rw [show n - t - 1 + 1 = n - t from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc4 : deform_spec n t (2 * n - (n - t - 1)) = 1 := by
      rw [show 2 * n - (n - t - 1) = n + t + 1 from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    rw [hc1, hc2, hc3, hc4]; ring
  have hfB2 : f_B n t (n - t) =
      (-1 : ℤ) ^ (n - t) * ((Nat.choose (2 * n) (n - t) : ℤ) *
        (α n (n - t) : ℤ) ^ 2) := by
    unfold f_B
    have hc1 : deform_spec n t (n - t) = 1 := by unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc2 : deform_spec n t (2 * n + 1 - (n - t)) = 1 := by
      rw [show 2 * n + 1 - (n - t) = n + t + 1 from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc3 : deform_spec n t (n - t + 1) = 0 := by
      unfold deform_spec; split_ifs <;> omega
    have hc4 : deform_spec n t (2 * n - (n - t)) = 0 := by
      rw [show 2 * n - (n - t) = n + t from by omega]
      unfold deform_spec; split_ifs <;> omega
    rw [hc1, hc2, hc3, hc4]; ring
  have hfB3 : f_B n t (n + t) =
      (-1 : ℤ) ^ (n + t) * ((Nat.choose (2 * n) (n + t) : ℤ) *
        (β n (n + t) : ℤ) ^ 2) := by
    unfold f_B
    have hc1 : deform_spec n t (n + t) = 0 := by unfold deform_spec; split_ifs <;> omega
    have hc2 : deform_spec n t (2 * n + 1 - (n + t)) = 0 := by
      rw [show 2 * n + 1 - (n + t) = n - t + 1 from by omega]
      unfold deform_spec; split_ifs <;> omega
    have hc3 : deform_spec n t (n + t + 1) = 1 := by
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc4 : deform_spec n t (2 * n - (n + t)) = 1 := by
      rw [show 2 * n - (n + t) = n - t from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    rw [hc1, hc2, hc3, hc4]; ring
  have hfB4 : f_B n t (n + t + 1) =
      (-1 : ℤ) ^ (n + t + 1) * ((Nat.choose (2 * n) (n + t + 1) : ℤ) *
        (α n (n + t + 1) : ℤ) ^ 2) := by
    unfold f_B
    have hc1 : deform_spec n t (n + t + 1) = 1 := by
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc2 : deform_spec n t (2 * n + 1 - (n + t + 1)) = 1 := by
      rw [show 2 * n + 1 - (n + t + 1) = n - t from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc3 : deform_spec n t (n + t + 1 + 1) = 0 := by
      unfold deform_spec; split_ifs <;> omega
    have hc4 : deform_spec n t (2 * n - (n + t + 1)) = 0 := by
      rw [show 2 * n - (n + t + 1) = n - t - 1 from by omega]
      unfold deform_spec; split_ifs <;> omega
    rw [hc1, hc2, hc3, hc4]; ring
  -- Central dominance: p^(e+1) | C(2n,i)*α² and C(2n,i)*β² for off-center i
  -- Key observation: α(n, n-t) = β(n, n-t-1) = (n+t+1)! * (n-t)!
  have hαβ : α n (n - t) = β n (n - t - 1) := by
    unfold α β
    rw [show 2 * n + 1 - (n - t) = n + t + 1 from by omega,
        show 2 * n - (n - t - 1) = n + t + 1 from by omega,
        show n - t - 1 + 1 = n - t from by omega]
  -- Core fact: p^(e+1) | C(2n, n-t) * α(n, n-t)²
  -- This follows from central dominance (Kummer's theorem): the binomial coefficient
  -- C(2n, n-t) has fewer carries in its Kummer representation than C(2n, n),
  -- but the factorial product α(n, n-t)² more than compensates.
  have hdvd_A2 : p ^ (e_central p n + 1) ∣
      (Nat.choose (2 * n) (n - t) * (α n (n - t)) ^ 2) := by
    have hval := off_center_alpha_sq_val p hp_odd k hk n hn
    have hne : Nat.choose (2 * n) (n - t) * (α n (n - t)) ^ 2 ≠ 0 := by
      apply mul_ne_zero
      · exact Nat.ne_of_gt (Nat.choose_pos (by omega))
      · exact Nat.ne_of_gt (by unfold α; positivity)
    exact (padicValNat_dvd_iff_le hne).mpr (by rw [hval])
  -- Derive hdvd_B2 from hdvd_A2 using the identity:
  -- C(2n, n-t-1) * (n+t+1) = C(2n, n-t) * (n-t)
  -- Since α(n,n-t) = β(n,n-t-1), both involve the same factorial square.
  -- Then coprimality of p and (n+t+1) gives the result.
  have hdvd_B2 : p ^ (e_central p n + 1) ∣
      (Nat.choose (2 * n) (n - t - 1) * (β n (n - t - 1)) ^ 2) := by
    rw [← hαβ]
    -- Use identity: C(2n, n-t-1) * (n+t+1) = C(2n, n-t) * (n-t)
    have hident : Nat.choose (2 * n) (n - t - 1) * (n + t + 1) =
        Nat.choose (2 * n) (n - t) * (n - t) := by
      have h := Nat.choose_succ_right_eq (2 * n) (n - t - 1)
      rw [show 2 * n - (n - t - 1) = n + t + 1 from by omega,
          show n - t - 1 + 1 = n - t from by omega] at h
      linarith
    -- v_p(n+t+1) = 0 since n+t+1 = p^k + p^{k-1} - 1 ≡ -1 (mod p)
    have hp_not_dvd_ntp1 : ¬ p ∣ (n + t + 1) := by
      intro hdvd
      -- n + t + 1 = (p^k - 2) + p^{k-1} + 1 = p^k + p^{k-1} - 1
      -- p | (n + t + 2) since n + t + 2 = p^k + p^{k-1} = p^{k-1}(p+1)
      -- and p | p^{k-1}... wait, p | p^{k-1}(p+1) since p | p^{k-1}? No, p | p^{k-1} iff k-1 ≥ 1.
      -- Actually n + 2 = p^k and t = p^{k-1}, so n + t + 2 = p^k + p^{k-1}
      -- p | p^k and p | p^{k-1} (since k ≥ 2, so k-1 ≥ 1).
      -- So p | (n + t + 2). Since p | (n + t + 1), p | 1. Contradiction.
      have h_dvd_sum : p ∣ (n + t + 2) := by
        have : n + t + 2 = p ^ k + p ^ (k - 1) := by omega
        rw [this]; exact dvd_add (dvd_pow_self p (by omega)) (dvd_pow_self p (by omega))
      have : p ∣ 1 := by
        have := Nat.dvd_sub h_dvd_sum hdvd
        rwa [show n + t + 2 - (n + t + 1) = 1 from by omega] at this
      exact Nat.Prime.one_lt Fact.out |>.ne' (Nat.eq_one_of_dvd_one this)
    -- p^(e+1) | C(2n, n-t) * α² (by hdvd_A2)
    -- p^(e+1) | C(2n, n-t) * α² * (n-t) (multiply by (n-t))
    -- C(2n, n-t) * (n-t) = C(2n, n-t-1) * (n+t+1) (by identity)
    -- So p^(e+1) | C(2n, n-t-1) * (n+t+1) * α²
    -- Since gcd(p, n+t+1) = 1, p^(e+1) | C(2n, n-t-1) * α²
    have hdvd_mul : p ^ (e_central p n + 1) ∣
        Nat.choose (2 * n) (n - t - 1) * (n + t + 1) * (α n (n - t)) ^ 2 := by
      rw [show Nat.choose (2 * n) (n - t - 1) * (n + t + 1) * (α n (n - t)) ^ 2 =
          Nat.choose (2 * n) (n - t) * (α n (n - t)) ^ 2 * (n - t) from by
            rw [show Nat.choose (2 * n) (n - t - 1) * (n + t + 1) =
                Nat.choose (2 * n) (n - t) * (n - t) from hident]; ring]
      exact dvd_mul_of_dvd_left hdvd_A2 _
    have hdvd_mul' : p ^ (e_central p n + 1) ∣
        Nat.choose (2 * n) (n - t - 1) * (α n (n - t)) ^ 2 * (n + t + 1) := by
      rw [show Nat.choose (2 * n) (n - t - 1) * (α n (n - t)) ^ 2 * (n + t + 1) =
          Nat.choose (2 * n) (n - t - 1) * (n + t + 1) * (α n (n - t)) ^ 2 from by ring]
      exact hdvd_mul
    -- Cancel (n+t+1) using coprimality
    have hcoprime : Nat.Coprime (p ^ (e_central p n + 1)) (n + t + 1) := by
      apply Nat.Coprime.pow_left
      rwa [Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact hcoprime.dvd_of_dvd_mul_right hdvd_mul'
  -- Symmetry: C(2n,n+t)=C(2n,n-t), β(n,n+t)=α(n,n-t); C(2n,n+t+1)=C(2n,n-t-1), α(n,n+t+1)=β(n,n-t-1)
  have hdvd_B2s : p ^ (e_central p n + 1) ∣
      (Nat.choose (2 * n) (n + t) * (β n (n + t)) ^ 2) := by
    have h1 : Nat.choose (2 * n) (n + t) = Nat.choose (2 * n) (n - t) := by
      have h := (Nat.choose_symm (show n + t ≤ 2 * n from by omega)).symm
      rwa [show 2 * n - (n + t) = n - t from by omega] at h
    have h2 : β n (n + t) = α n (n - t) := by
      simp only [β, α]
      rw [show 2 * n - (n + t) = n - t from by omega,
          show n + t + 1 = 2 * n + 1 - (n - t) from by omega, mul_comm]
    rw [h1, h2]; exact hdvd_A2
  have hdvd_A2s : p ^ (e_central p n + 1) ∣
      (Nat.choose (2 * n) (n + t + 1) * (α n (n + t + 1)) ^ 2) := by
    have h1 : Nat.choose (2 * n) (n + t + 1) = Nat.choose (2 * n) (n - t - 1) := by
      have h := (Nat.choose_symm (show n + t + 1 ≤ 2 * n from by omega)).symm
      rwa [show 2 * n - (n + t + 1) = n - t - 1 from by omega] at h
    have h2 : α n (n + t + 1) = β n (n - t - 1) := by
      unfold α β
      have : 2 * n + 1 - (n + t + 1) = n - t := by omega
      have : 2 * n - (n - t - 1) = n + t + 1 := by omega
      have : n - t - 1 + 1 = n - t := by omega
      simp_all only; ring
    rw [h1, h2]; exact hdvd_B2
  -- Lift to ℤ
  have h1z : (p : ℤ) ^ (e_central p n + 1) ∣
      ((Nat.choose (2 * n) (n - t - 1) : ℤ) * (β n (n - t - 1) : ℤ) ^ 2) :=
    natAbs_dvd_int_pow (by simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]; exact hdvd_B2)
  have h2z : (p : ℤ) ^ (e_central p n + 1) ∣
      ((Nat.choose (2 * n) (n - t) : ℤ) * (α n (n - t) : ℤ) ^ 2) :=
    natAbs_dvd_int_pow (by simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]; exact hdvd_A2)
  have h3z : (p : ℤ) ^ (e_central p n + 1) ∣
      ((Nat.choose (2 * n) (n + t) : ℤ) * (β n (n + t) : ℤ) ^ 2) :=
    natAbs_dvd_int_pow (by simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]; exact hdvd_B2s)
  have h4z : (p : ℤ) ^ (e_central p n + 1) ∣
      ((Nat.choose (2 * n) (n + t + 1) : ℤ) * (α n (n + t + 1) : ℤ) ^ 2) :=
    natAbs_dvd_int_pow (by simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]; exact hdvd_A2s)
  -- Sum divisibility
  unfold R_off; rw [hfB1, hfB2, hfB3, hfB4]
  apply dvd_add
  · apply dvd_add
    · apply dvd_add
      · exact dvd_mul_of_dvd_right h1z _
      · exact dvd_mul_of_dvd_right h2z _
    · exact dvd_mul_of_dvd_right h3z _
  · exact dvd_mul_of_dvd_right h4z _

/-- The central part cancellation: 2*C(2n,n-1)*γ² - 4*C(2n,n)*γ² is divisible by p^{e+2}.
Uses n+2 = p^k, so the difference involves a factor of p^k with k ≥ 2. -/
private lemma central_cancel_dvd (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    (p : ℤ) ^ (e_central p n + 2) ∣
      (2 * (Nat.choose (2 * n) (n - 1) : ℤ) * ((γ n : ℤ) ^ 2) -
       4 * (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2)) := by
  -- Step 1: Multiply out by (n+1) to use the identity C(2n,n-1)*(n+1) = C(2n,n)*n
  -- We show (n+1) * expression = -2*(n+2) * C(2n,n) * γ²
  -- Then since p ∤ (n+1), dividing preserves p-divisibility.
  have hn1_pos : (0 : ℤ) < (n : ℤ) + 1 := by omega
  have hn1_ne : (n : ℤ) + 1 ≠ 0 := by omega
  -- The identity: C(2n,n-1)*(n+1) = C(2n,n)*n
  have hident := choose_identity n hn_pos
  -- Cast to ℤ
  have hident_int : (Nat.choose (2 * n) (n - 1) : ℤ) * ((n : ℤ) + 1) =
      (Nat.choose (2 * n) n : ℤ) * (n : ℤ) := by exact_mod_cast hident
  -- Key: (n+1) * expr = -2*(n+2) * C(2n,n) * γ²
  have hmul_eq : ((n : ℤ) + 1) *
      (2 * (Nat.choose (2 * n) (n - 1) : ℤ) * ((γ n : ℤ) ^ 2) -
       4 * (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2)) =
      -2 * ((n : ℤ) + 2) * (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2) := by
    nlinarith [hident_int]
  -- Step 2: p^(e+2) divides -2*(n+2)*C(2n,n)*γ²
  -- Since n+2 = p^k, we have p^k | (n+2). Also e_central = v_p(C(2n,n)*γ²).
  -- So p^(e+k) | C(2n,n)*γ²*(n+2), and k ≥ 2 gives p^(e+2) | that.
  -- Also p ∤ 2 since p is odd.
  -- Step 2a: p^k divides (n+2)
  have hpk_dvd_n2 : (p : ℤ) ^ k ∣ ((n : ℤ) + 2) := by
    rw [show (n : ℤ) + 2 = ↑(n + 2) from by push_cast; ring, hn]
    exact dvd_refl _
  -- Step 2b: p^e divides C(2n,n)*γ²
  have hchoose_n_ne : Nat.choose (2 * n) n ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hgamma_ne : (γ n) ^ 2 ≠ 0 := Nat.ne_of_gt (by unfold γ; positivity)
  have hprod_ne : Nat.choose (2 * n) n * (γ n) ^ 2 ≠ 0 := mul_ne_zero hchoose_n_ne hgamma_ne
  have hpe_dvd : p ^ e_central p n ∣ (Nat.choose (2 * n) n * (γ n) ^ 2) := by
    unfold e_central
    exact padicValNat_dvd_iff_le hprod_ne |>.mpr le_rfl
  have hpe_dvd_int : (p : ℤ) ^ e_central p n ∣
      ((Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2)) := by
    have := natAbs_dvd_int_pow (p := p) (e := e_central p n)
      (a := (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2))
    apply this
    simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    exact hpe_dvd
  -- Step 2c: p^(e+k) divides (n+2)*C(2n,n)*γ²
  have hpek_dvd : (p : ℤ) ^ (e_central p n + k) ∣
      ((n : ℤ) + 2) * ((Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2)) := by
    rw [show e_central p n + k = k + e_central p n from by omega, pow_add]
    exact mul_dvd_mul hpk_dvd_n2 hpe_dvd_int
  -- Step 2d: p^(e+2) divides it too since k ≥ 2
  have hpe2_dvd_prod : (p : ℤ) ^ (e_central p n + 2) ∣
      ((n : ℤ) + 2) * ((Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2)) :=
    dvd_trans (pow_dvd_pow _ (by omega)) hpek_dvd
  -- Step 2e: p^(e+2) divides -2*(n+2)*C(2n,n)*γ²
  have hpe2_dvd_rhs : (p : ℤ) ^ (e_central p n + 2) ∣
      -2 * ((n : ℤ) + 2) * (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2) := by
    have : -2 * ((n : ℤ) + 2) * (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2) =
      -2 * (((n : ℤ) + 2) * ((Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2))) := by ring
    rw [this]
    exact dvd_mul_of_dvd_right hpe2_dvd_prod (-2)
  -- Step 3: Since (n+1) * expr = rhs and p^(e+2) | rhs and p ∤ (n+1), conclude p^(e+2) | expr
  have hp_not_dvd_n1 : ¬ (p : ℕ) ∣ (n + 1) := p_not_dvd_n1 p k (by omega) n hn
  -- p^(e+2) | (n+1) * expr, so p^(e+2) | expr (since gcd(p, n+1) = 1)
  have hpe2_dvd_mul : (p : ℤ) ^ (e_central p n + 2) ∣
      ((n : ℤ) + 1) * (2 * (Nat.choose (2 * n) (n - 1) : ℤ) * ((γ n : ℤ) ^ 2) -
       4 * (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2)) := by
    rw [hmul_eq]; exact hpe2_dvd_rhs
  -- Since p is prime and p ∤ (n+1), gcd(p^(e+2), n+1) = 1
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hcoprime : IsCoprime ((p : ℤ) ^ (e_central p n + 2)) ((n : ℤ) + 1) := by
    apply IsCoprime.pow_left
    rw [hp_prime_int.coprime_iff_not_dvd]
    intro hdvd
    apply hp_not_dvd_n1
    exact Int.ofNat_dvd.mp (show (↑p : ℤ) ∣ ↑(n + 1) by push_cast; exact hdvd)
  have hpe2_dvd_mul' : (p : ℤ) ^ (e_central p n + 2) ∣
      (2 * (Nat.choose (2 * n) (n - 1) : ℤ) * ((γ n : ℤ) ^ 2) -
       4 * (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2)) * ((n : ℤ) + 1) := by
    rw [show (2 * (Nat.choose (2 * n) (n - 1) : ℤ) * ((γ n : ℤ) ^ 2) -
       4 * (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2)) * ((n : ℤ) + 1) =
       ((n : ℤ) + 1) * (2 * (Nat.choose (2 * n) (n - 1) : ℤ) * ((γ n : ℤ) ^ 2) -
       4 * (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2)) from by ring]
    exact hpe2_dvd_mul
  exact hcoprime.dvd_of_dvd_mul_right hpe2_dvd_mul'

/-- R_off is nonzero with v_p = exactly e+1 (off-center terms dominate at this valuation). -/
private lemma R_off_val_exact (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    let t := p ^ (k - 1)
    R_off n t ≠ 0 ∧
    padicValNat p (Int.natAbs (R_off n t)) = e_central p n + 1 := by
  intro t
  -- Derive basic bounds
  have hp_prime := (Fact.out : p.Prime)
  have hp_ge : 3 ≤ p := by have := hp_prime.two_le; omega
  have ht_ge_2 : 2 ≤ t := le_trans (show 2 ≤ p from by omega) (Nat.le_self_pow (by omega) p)
  have htn : t + 2 ≤ n := by
    have h1 : p ^ k = p * p ^ (k - 1) := by
      cases k with | zero => omega | succ k => simp [pow_succ, mul_comm]
    have hp_le_t : p ≤ t := Nat.le_self_pow (show k - 1 ≠ 0 from by omega) p
    have h2 : n + 2 = p * t := by rw [hn, h1]
    have : p * t ≥ 3 * t := Nat.mul_le_mul_right t hp_ge
    omega
  -- Symmetry facts for binomial coefficients and factorial products
  have hchoose_sym : Nat.choose (2 * n) (n + t) = Nat.choose (2 * n) (n - t) := by
    have h := (Nat.choose_symm (show n + t ≤ 2 * n from by omega)).symm
    rwa [show 2 * n - (n + t) = n - t from by omega] at h
  have hchoose_sym2 : Nat.choose (2 * n) (n + t + 1) = Nat.choose (2 * n) (n - t - 1) := by
    have h := (Nat.choose_symm (show n + t + 1 ≤ 2 * n from by omega)).symm
    rwa [show 2 * n - (n + t + 1) = n - t - 1 from by omega] at h
  have hβα : β n (n + t) = α n (n - t) := by
    simp only [β, α]
    rw [show 2 * n - (n + t) = n - t from by omega,
        show n + t + 1 = 2 * n + 1 - (n - t) from by omega, mul_comm]
  have hαβ2 : α n (n + t + 1) = β n (n - t - 1) := by
    unfold α β
    have : 2 * n + 1 - (n + t + 1) = n - t := by omega
    have : 2 * n - (n - t - 1) = n + t + 1 := by omega
    have : n - t - 1 + 1 = n - t := by omega
    simp_all only; ring
  have hαβ_eq : α n (n - t) = β n (n - t - 1) := by
    unfold α β
    rw [show 2 * n + 1 - (n - t) = n + t + 1 from by omega,
        show 2 * n - (n - t - 1) = n + t + 1 from by omega,
        show n - t - 1 + 1 = n - t from by omega]
  -- Sign facts: (-1)^{n+t} = (-1)^{n-t} and (-1)^{n+t+1} = (-1)^{n-t-1}
  have hsign1 : (-1 : ℤ) ^ (n + t) = (-1 : ℤ) ^ (n - t) := by
    have h2t : n + t = n - t + 2 * t := by omega
    rw [h2t, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  have hsign2 : (-1 : ℤ) ^ (n + t + 1) = (-1 : ℤ) ^ (n - t - 1) := by
    have h2t : n + t + 1 = n - t - 1 + 2 * (t + 1) := by omega
    rw [h2t, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  -- Evaluate f_B at each off-center index (same as in R_off_dvd)
  have hfB1 : f_B n t (n - t - 1) =
      (-1 : ℤ) ^ (n - t - 1) * ((Nat.choose (2 * n) (n - t - 1) : ℤ) *
        (β n (n - t - 1) : ℤ) ^ 2) := by
    unfold f_B
    have hc1 : deform_spec n t (n - t - 1) = 0 := by unfold deform_spec; split_ifs <;> omega
    have hc2 : deform_spec n t (2 * n + 1 - (n - t - 1)) = 0 := by
      rw [show 2 * n + 1 - (n - t - 1) = n + t + 2 from by omega]
      unfold deform_spec; split_ifs <;> omega
    have hc3 : deform_spec n t (n - t - 1 + 1) = 1 := by
      rw [show n - t - 1 + 1 = n - t from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc4 : deform_spec n t (2 * n - (n - t - 1)) = 1 := by
      rw [show 2 * n - (n - t - 1) = n + t + 1 from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    rw [hc1, hc2, hc3, hc4]; ring
  have hfB2 : f_B n t (n - t) =
      (-1 : ℤ) ^ (n - t) * ((Nat.choose (2 * n) (n - t) : ℤ) *
        (α n (n - t) : ℤ) ^ 2) := by
    unfold f_B
    have hc1 : deform_spec n t (n - t) = 1 := by unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc2 : deform_spec n t (2 * n + 1 - (n - t)) = 1 := by
      rw [show 2 * n + 1 - (n - t) = n + t + 1 from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc3 : deform_spec n t (n - t + 1) = 0 := by
      unfold deform_spec; split_ifs <;> omega
    have hc4 : deform_spec n t (2 * n - (n - t)) = 0 := by
      rw [show 2 * n - (n - t) = n + t from by omega]
      unfold deform_spec; split_ifs <;> omega
    rw [hc1, hc2, hc3, hc4]; ring
  have hfB3 : f_B n t (n + t) =
      (-1 : ℤ) ^ (n + t) * ((Nat.choose (2 * n) (n + t) : ℤ) *
        (β n (n + t) : ℤ) ^ 2) := by
    unfold f_B
    have hc1 : deform_spec n t (n + t) = 0 := by unfold deform_spec; split_ifs <;> omega
    have hc2 : deform_spec n t (2 * n + 1 - (n + t)) = 0 := by
      rw [show 2 * n + 1 - (n + t) = n - t + 1 from by omega]
      unfold deform_spec; split_ifs <;> omega
    have hc3 : deform_spec n t (n + t + 1) = 1 := by
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc4 : deform_spec n t (2 * n - (n + t)) = 1 := by
      rw [show 2 * n - (n + t) = n - t from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    rw [hc1, hc2, hc3, hc4]; ring
  have hfB4 : f_B n t (n + t + 1) =
      (-1 : ℤ) ^ (n + t + 1) * ((Nat.choose (2 * n) (n + t + 1) : ℤ) *
        (α n (n + t + 1) : ℤ) ^ 2) := by
    unfold f_B
    have hc1 : deform_spec n t (n + t + 1) = 1 := by
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc2 : deform_spec n t (2 * n + 1 - (n + t + 1)) = 1 := by
      rw [show 2 * n + 1 - (n + t + 1) = n - t from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc3 : deform_spec n t (n + t + 1 + 1) = 0 := by
      unfold deform_spec; split_ifs <;> omega
    have hc4 : deform_spec n t (2 * n - (n + t + 1)) = 0 := by
      rw [show 2 * n - (n + t + 1) = n - t - 1 from by omega]
      unfold deform_spec; split_ifs <;> omega
    rw [hc1, hc2, hc3, hc4]; ring
  -- Step 1: Rewrite R_off using symmetry to get R_off = 2*(f_B(n-t) + f_B(n-t-1))
  have hR_eq : R_off n t =
      2 * ((-1 : ℤ) ^ (n - t) * ((Nat.choose (2 * n) (n - t) : ℤ) * (α n (n - t) : ℤ) ^ 2) +
       (-1 : ℤ) ^ (n - t - 1) * ((Nat.choose (2 * n) (n - t - 1) : ℤ) * (β n (n - t - 1) : ℤ) ^ 2)) := by
    unfold R_off
    rw [hfB1, hfB2, hfB3, hfB4, hchoose_sym, hchoose_sym2, ← hβα, ← hαβ2, hsign1, hsign2]
    ring
  -- Step 2: Use β(n,n-t-1) = α(n,n-t) and simplify signs
  -- (-1)^{n-t-1} = -(-1)^{n-t}
  have hsign_rel : (-1 : ℤ) ^ (n - t - 1) = -(-1 : ℤ) ^ (n - t) := by
    have h : n - t = n - t - 1 + 1 := by omega
    conv_rhs => rw [h, pow_succ]
    ring
  -- Rewrite using α = β and sign relation
  have hR_eq2 : R_off n t =
      2 * (-1 : ℤ) ^ (n - t) * ((Nat.choose (2 * n) (n - t) : ℤ) * (α n (n - t) : ℤ) ^ 2 -
       (Nat.choose (2 * n) (n - t - 1) : ℤ) * (α n (n - t) : ℤ) ^ 2) := by
    rw [hR_eq, ← hαβ_eq, hsign_rel]; ring
  -- Factor out α²
  have hR_eq3 : R_off n t =
      2 * (-1 : ℤ) ^ (n - t) * (α n (n - t) : ℤ) ^ 2 *
       ((Nat.choose (2 * n) (n - t) : ℤ) - (Nat.choose (2 * n) (n - t - 1) : ℤ)) := by
    rw [hR_eq2]; ring
  -- Step 3: Show C(2n,n-t) > C(2n,n-t-1)
  -- Use: C(2n,n-t-1)*(n+t+1) = C(2n,n-t)*(n-t), so C(2n,n-t)/C(2n,n-t-1) = (n+t+1)/(n-t) > 1
  have hident : Nat.choose (2 * n) (n - t - 1) * (n + t + 1) =
      Nat.choose (2 * n) (n - t) * (n - t) := by
    have h := Nat.choose_succ_right_eq (2 * n) (n - t - 1)
    rw [show 2 * n - (n - t - 1) = n + t + 1 from by omega,
        show n - t - 1 + 1 = n - t from by omega] at h
    linarith
  have hchoose_lt : Nat.choose (2 * n) (n - t - 1) < Nat.choose (2 * n) (n - t) := by
    -- From identity: C(n-t-1)*(n+t+1) = C(n-t)*(n-t)
    -- Since n+t+1 > n-t (because t ≥ 2, so 2t+1 > 0), and C(n-t) > 0, C(n-t-1) > 0:
    -- C(n-t-1) = C(n-t)*(n-t)/(n+t+1) < C(n-t) (since (n-t)/(n+t+1) < 1)
    by_contra h_ge
    push_neg at h_ge
    -- C(n-t-1) ≥ C(n-t), so C(n-t-1)*(n+t+1) ≥ C(n-t)*(n+t+1) > C(n-t)*(n-t) = C(n-t-1)*(n+t+1)
    have hcnt_pos : 0 < Nat.choose (2 * n) (n - t) := Nat.choose_pos (by omega)
    have : Nat.choose (2 * n) (n - t - 1) * (n + t + 1) ≥ Nat.choose (2 * n) (n - t) * (n + t + 1) :=
      Nat.mul_le_mul_right _ h_ge
    have : Nat.choose (2 * n) (n - t) * (n + t + 1) > Nat.choose (2 * n) (n - t) * (n - t) := by
      apply Nat.mul_lt_mul_of_pos_left _ hcnt_pos; omega
    omega
  have hchoose_diff_pos : 0 < Nat.choose (2 * n) (n - t) - Nat.choose (2 * n) (n - t - 1) := by
    omega
  -- Step 4: Show the difference times (n+t+1) equals C(2n,n-t) * (2t+1)
  have hdiff_ident : (Nat.choose (2 * n) (n - t) - Nat.choose (2 * n) (n - t - 1)) * (n + t + 1) =
      Nat.choose (2 * n) (n - t) * (2 * t + 1) := by
    -- C(n-t)*(n+t+1) = C(n-t-1)*(n+t+1) + C(n-t)*(2t+1)
    -- because C(n-t-1)*(n+t+1) = C(n-t)*(n-t) [hident] and C(n-t)*(n-t) + C(n-t)*(2t+1) = C(n-t)*(n+t+1)
    have h1 : Nat.choose (2 * n) (n - t - 1) * (n + t + 1) + Nat.choose (2 * n) (n - t) * (2 * t + 1) =
        Nat.choose (2 * n) (n - t) * (n + t + 1) := by
      rw [hident, ← mul_add]; congr 1; omega
    -- So (C(n-t) - C(n-t-1)) * (n+t+1) = C(n-t)*(n+t+1) - C(n-t-1)*(n+t+1) = C(n-t)*(2t+1)
    have hle : Nat.choose (2 * n) (n - t - 1) ≤ Nat.choose (2 * n) (n - t) := by omega
    rw [Nat.sub_mul]; omega
  -- Step 5: v_p(n+t+1) = 0 and v_p(2t+1) = 0
  have hp_not_dvd_ntp1 : ¬ p ∣ (n + t + 1) := by
    intro hdvd
    have h_dvd_sum : p ∣ (n + t + 2) := by
      have : n + t + 2 = p ^ k + p ^ (k - 1) := by omega
      rw [this]; exact dvd_add (dvd_pow_self p (by omega)) (dvd_pow_self p (by omega))
    have : p ∣ 1 := by
      have := Nat.dvd_sub h_dvd_sum hdvd
      rwa [show n + t + 2 - (n + t + 1) = 1 from by omega] at this
    exact Nat.Prime.one_lt Fact.out |>.ne' (Nat.eq_one_of_dvd_one this)
  have hp_not_dvd_2tp1 : ¬ p ∣ (2 * t + 1) := by
    intro hdvd
    -- 2t+1 = 2*p^{k-1}+1 ≡ 0+1 = 1 (mod p) since p | p^{k-1} (k-1 ≥ 1)
    have hp_dvd_2t : p ∣ (2 * t) := by
      have : p ∣ t := dvd_pow_self p (by omega : k - 1 ≠ 0)
      exact dvd_mul_of_dvd_right this 2
    have : p ∣ 1 := by
      have h := Nat.dvd_sub hdvd hp_dvd_2t
      rwa [show 2 * t + 1 - 2 * t = 1 from by omega] at h
    exact Nat.Prime.one_lt Fact.out |>.ne' (Nat.eq_one_of_dvd_one this)
  -- Step 6: v_p(C(2n,n-t) - C(2n,n-t-1)) = v_p(C(2n,n-t))
  have hvp_diff : padicValNat p (Nat.choose (2 * n) (n - t) - Nat.choose (2 * n) (n - t - 1)) =
      padicValNat p (Nat.choose (2 * n) (n - t)) := by
    -- From (diff) * (n+t+1) = C(n-t) * (2t+1), v_p of both sides equal
    have hdiff_ne : Nat.choose (2 * n) (n - t) - Nat.choose (2 * n) (n - t - 1) ≠ 0 := by omega
    have hcnt_ne : Nat.choose (2 * n) (n - t) ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
    have h_val_eq : padicValNat p (Nat.choose (2 * n) (n - t) - Nat.choose (2 * n) (n - t - 1)) +
        padicValNat p (n + t + 1) =
        padicValNat p (Nat.choose (2 * n) (n - t)) + padicValNat p (2 * t + 1) := by
      rw [← padicValNat.mul hdiff_ne (by omega), ← padicValNat.mul hcnt_ne (by omega)]
      exact congr_arg _ hdiff_ident
    rw [padicValNat.eq_zero_of_not_dvd hp_not_dvd_ntp1,
        padicValNat.eq_zero_of_not_dvd hp_not_dvd_2tp1] at h_val_eq
    omega
  -- Step 7: Compute v_p(R_off)
  -- v_p(|R_off|) = v_p(2 * α² * (C(n-t) - C(n-t-1)))
  --             = v_p(2) + 2*v_p(α) + v_p(C(n-t))   [since v_p(diff) = v_p(C(n-t))]
  --             = 0 + v_p(C(n-t) * α²) = e+1
  -- First, get the exact valuation from off_center_alpha_sq_val
  have hval_exact := off_center_alpha_sq_val p hp_odd k hk n hn
  -- Nonzero facts
  have hα_ne : (α n (n - t)) ≠ 0 := Nat.ne_of_gt (by unfold α; positivity)
  have hα_sq_ne : (α n (n - t)) ^ 2 ≠ 0 := Nat.ne_of_gt (by unfold α; positivity)
  have hcnt_ne : Nat.choose (2 * n) (n - t) ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hdiff_ne : Nat.choose (2 * n) (n - t) - Nat.choose (2 * n) (n - t - 1) ≠ 0 := by omega
  -- Set up the key product
  set D := (α n (n - t)) ^ 2 * (Nat.choose (2 * n) (n - t) - Nat.choose (2 * n) (n - t - 1)) with hD_def
  have hD_pos : 0 < D := by positivity
  -- v_p(D) = v_p(α² * diff) = v_p(α²) + v_p(diff) = v_p(α²) + v_p(C(n-t)) = v_p(C(n-t)*α²) = e+1
  have hvp_prod : padicValNat p D = e_central p n + 1 := by
    rw [hD_def, padicValNat.mul hα_sq_ne hdiff_ne, hvp_diff, add_comm,
        ← padicValNat.mul hcnt_ne hα_sq_ne]
    exact hval_exact
  -- Now compute v_p(|R_off|)
  -- |R_off| = |2 * (-1)^{n-t} * α² * (C(n-t) - C(n-t-1))| = 2 * D
  -- Express R_off as an integer in a form we can take natAbs of
  have hchoose_le : Nat.choose (2 * n) (n - t - 1) ≤ Nat.choose (2 * n) (n - t) := by omega
  have hdiff_cast : (Nat.choose (2 * n) (n - t) : ℤ) - (Nat.choose (2 * n) (n - t - 1) : ℤ) =
      ↑(Nat.choose (2 * n) (n - t) - Nat.choose (2 * n) (n - t - 1)) := by
    push_cast; omega
  have hR_eq4 : R_off n t = 2 * (-1 : ℤ) ^ (n - t) * ↑D := by
    rw [hR_eq3, hdiff_cast, hD_def]
    push_cast; ring
  have hR_natAbs : Int.natAbs (R_off n t) = 2 * D := by
    rw [hR_eq4]
    have hD_cast : (0 : ℤ) ≤ ↑D := Int.natCast_nonneg D
    have : (2 : ℤ) * (-1) ^ (n - t) * ↑D = (if Even (n - t) then (2 : ℤ) * ↑D else -(2 * ↑D)) := by
      split
      · next h => rw [Even.neg_one_pow h]; ring
      · next h => rw [Odd.neg_one_pow (Nat.not_even_iff_odd.mp h)]; ring
    rw [this]
    split
    · simp [Int.natAbs_mul, Int.natAbs_natCast]
    · rw [Int.natAbs_neg, Int.natAbs_mul]
      simp [Int.natAbs_natCast]
  -- v_p(2) = 0 since p ≥ 3
  have hvp_two : padicValNat p 2 = 0 := by
    rw [padicValNat.eq_zero_of_not_dvd]
    intro h; have := Nat.le_of_dvd (by omega) h; omega
  -- Final assembly
  have hD_ne : D ≠ 0 := by omega
  have hR_ne : R_off n t ≠ 0 := by
    intro h
    have h1 : Int.natAbs (R_off n t) = 0 := by rw [h]; simp
    rw [hR_natAbs] at h1
    omega
  refine ⟨hR_ne, ?_⟩
  rw [hR_natAbs, padicValNat.mul (by omega) hD_ne, hvp_two, zero_add]
  exact hvp_prod

/-! ### Main proof of B_vals_k_ge_2 -/

/-- For k ≥ 2: B+2u has v_p = e and B-2u has v_p = e+1. -/
lemma B_vals_k_ge_2 (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    let t := p ^ (k - 1)
    let Bplus := B_eval n (deform_spec n t) + 2 * u_val n
    let Bminus := B_eval n (deform_spec n t) - 2 * u_val n
    Bplus ≠ 0 ∧ Bminus ≠ 0 ∧
    padicValNat p (Int.natAbs Bplus) = e_central p n ∧
    padicValNat p (Int.natAbs Bminus) = e_central p n + 1 := by
  -- Setup: derive t ≥ 2 and t + 2 ≤ n from hypotheses
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have ht_ge_2 : 2 ≤ p ^ (k - 1) :=
    le_trans (by omega : 2 ≤ p) (Nat.le_self_pow (by omega) p)
  have ht_n : p ^ (k - 1) + 2 ≤ n := by
    have h1 : p ^ k = p * p ^ (k - 1) := by
      cases k with | zero => omega | succ k => simp [pow_succ, mul_comm]
    nlinarith [Nat.le_self_pow (show k - 1 ≠ 0 from by omega) p]
  set t := p ^ (k - 1)
  simp only
  -- Step 1: Rewrite Bplus using the explicit formula
  have hBplus_eq := Bplus_formula n t ht_ge_2 ht_n
  -- Step 2: Get the valuation helpers
  obtain ⟨hcnz, hcval⟩ := choose_nm1_val p hp_odd k hk n hn hn_pos
  have hR_dvd := R_off_dvd p hp_odd k hk n hn hn_pos
  obtain ⟨hR_ne, hR_val⟩ := R_off_val_exact p hp_odd k hk n hn hn_pos
  have hcancel := central_cancel_dvd p hp_odd k hk n hn hn_pos
  -- Step 3: v_p of leading term = e
  have hleading_ne : 2 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) (n - 1)) * ↑(γ n) ^ 2 ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · exact two_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact_mod_cast (show Nat.choose (2 * n) (n - 1) ≠ 0 from
        Nat.ne_of_gt (Nat.choose_pos (by omega)))
    · exact pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt (by unfold γ; positivity))
  have hleading_val : padicValNat p (Int.natAbs
      (2 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) (n - 1)) * ↑(γ n) ^ 2)) = e_central p n := by
    -- |2 * (-1)^n * C * γ²| = 2 * C * γ²
    have habs : Int.natAbs (2 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) (n - 1)) * ↑(γ n) ^ 2) =
      2 * (Nat.choose (2 * n) (n - 1) * (γ n) ^ 2) := by
      simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
            show Int.natAbs ((-1 : ℤ) ^ n) = 1 from by simp,
            show Int.natAbs (2 : ℤ) = 2 from by norm_num]
      ring
    rw [habs, padicValNat.mul (by omega) (by exact Nat.ne_of_gt (by positivity))]
    have : padicValNat p 2 = 0 := padicValNat_primes hp_odd
    rw [this, zero_add, hcval]
  -- Step 4: Bplus = leading + R_off, v_p(leading) = e, p^{e+1} | R_off
  -- By ultrametric: v_p(Bplus) = e
  rw [hBplus_eq]
  obtain ⟨hBplus_ne, hBplus_val⟩ :=
    padic_val_add_of_strict_lt p
      (2 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) (n - 1)) * ↑(γ n) ^ 2)
      (R_off n t) (e_central p n) hleading_ne hleading_val hR_dvd
  -- Step 5: Bminus = Bplus - 4u = (leading - 4u) + R_off
  -- Bminus = B_eval - 2u = (B_eval + 2u) - 4u = leading + R_off - 4u
  -- = (leading - 4u) + R_off = R_off + (leading - 4u)
  have hBminus_eq : B_eval n (deform_spec n t) - 2 * u_val n =
    R_off n t + (2 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) (n - 1)) * ↑(γ n) ^ 2 -
     4 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) n) * ↑(γ n) ^ 2) := by
    have := hBplus_eq; unfold u_val at *; linarith
  -- The (leading - 4u) part is divisible by p^{e+2}
  have hcancel' : (p : ℤ) ^ (e_central p n + 1 + 1) ∣
    (2 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) (n - 1)) * ↑(γ n) ^ 2 -
     4 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) n) * ↑(γ n) ^ 2) := by
    have hfactor : 2 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) (n - 1)) * ↑(γ n) ^ 2 -
      4 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) n) * ↑(γ n) ^ 2 =
      (-1 : ℤ) ^ n * (2 * ↑(Nat.choose (2 * n) (n - 1)) * ↑(γ n) ^ 2 -
        4 * ↑(Nat.choose (2 * n) n) * ↑(γ n) ^ 2) := by ring
    rw [hfactor]
    exact dvd_mul_of_dvd_right hcancel _
  -- By ultrametric: v_p(R_off + (leading - 4u)) = v_p(R_off) = e+1
  -- since v_p(R_off) = e+1 < e+2 ≤ v_p(leading - 4u)
  obtain ⟨hBm_ne, hBm_val⟩ := padic_val_add_of_strict_lt p (R_off n t)
    (2 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) (n - 1)) * ↑(γ n) ^ 2 -
     4 * (-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) n) * ↑(γ n) ^ 2)
    (e_central p n + 1) hR_ne hR_val hcancel'
  rw [hBminus_eq] at *
  exact ⟨hBplus_ne, hBm_ne, hBplus_val, hBm_val⟩

/-! ### k=1 helpers: deform_spec_k1 coincides with deform_spec at t=1 -/

/-- deform_spec_k1 n = deform_spec n 1 pointwise. -/
private lemma deform_spec_k1_eq_deform (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    deform_spec_k1 n j = deform_spec n 1 j := by
  unfold deform_spec_k1 deform_spec
  split_ifs <;> omega

/-- B_eval under deform_spec_k1 equals B_eval under deform_spec with t=1. -/
private lemma B_eval_k1_eq (n : ℕ) (hn : 1 ≤ n) :
    B_eval n (deform_spec_k1 n) = B_eval n (deform_spec n 1) := by
  unfold B_eval
  congr 1; ext i
  simp only [deform_spec_k1_eq_deform n hn]

/-! ### k=1 B_eval summand analysis -/

/-- The B_eval summand function for t=1. -/
private def f_B_k1 (n : ℕ) (i : ℕ) : ℤ :=
    (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      ((α n i : ℤ) ^ 2 * deform_spec n 1 i * deform_spec n 1 (2 * n + 1 - i) +
       (β n i : ℤ) ^ 2 * deform_spec n 1 (i + 1) * deform_spec n 1 (2 * n - i))

/-- Summands vanish for i outside {n-2, n-1, n, n+1, n+2} when t=1. -/
private lemma f_B_k1_zero (n i : ℕ) (hn : 3 ≤ n)
    (h1 : i ≠ n - 2) (h2 : i ≠ n - 1) (h3 : i ≠ n)
    (h4 : i ≠ n + 1) (h5 : i ≠ n + 2) :
    f_B_k1 n i = 0 := by
  unfold f_B_k1
  have hd1 : deform_spec n 1 i = 0 := by unfold deform_spec; split_ifs <;> omega
  have hd2 : deform_spec n 1 (i + 1) = 0 := by unfold deform_spec; split_ifs <;> omega
  simp [hd1, hd2]

/-- At i = n: summand = -2 * u_val n (same as k≥2 case). -/
private lemma f_B_k1_at_n (n : ℕ) (hn : 3 ≤ n) :
    f_B_k1 n n = -2 * u_val n := by
  unfold f_B_k1 u_val
  have hα : α n n = γ n := by unfold α γ; rw [show 2 * n + 1 - n = n + 1 from by omega]
  have hβ : β n n = γ n := by unfold β γ; rw [show 2 * n - n = n from by omega]; ring
  have h1 : deform_spec n 1 n = 1 := by unfold deform_spec; split_ifs <;> omega <;> rfl
  have h2 : deform_spec n 1 (2 * n + 1 - n) = -1 := by
    rw [show 2 * n + 1 - n = n + 1 from by omega]; unfold deform_spec; split_ifs <;> omega
  have h3 : deform_spec n 1 (n + 1) = -1 := by unfold deform_spec; split_ifs <;> omega
  have h4 : deform_spec n 1 (2 * n - n) = 1 := by
    rw [show 2 * n - n = n from by omega]; unfold deform_spec; split_ifs <;> omega <;> rfl
  rw [h1, h2, h3, h4, hα, hβ]; ring

/-! ### k=1 off-center and center excess contributions -/

/-- The k=1 off-center contribution: R_off_k1 = f_B_k1(n-2) + f_B_k1(n+2). -/
private def R_off_k1 (n : ℕ) : ℤ :=
  f_B_k1 n (n - 2) + f_B_k1 n (n + 2)

/-- The center excess: sum of f_B_k1 at i=n-1 and i=n+1. -/
private def B_center_excess_k1 (n : ℕ) : ℤ :=
  f_B_k1 n (n - 1) + f_B_k1 n (n + 1)

/-- B_eval = -2u + B_center_excess + R_off for k=1. -/
private lemma B_eval_k1_decomp (n : ℕ) (hn : 3 ≤ n) :
    B_eval n (deform_spec n 1) =
    -2 * u_val n + B_center_excess_k1 n + R_off_k1 n := by
  have hB : B_eval n (deform_spec n 1) =
    ∑ i ∈ ({n - 2, n - 1, n, n + 1, n + 2} : Finset ℕ), f_B_k1 n i := by
    unfold B_eval; show _ = _; symm
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hx ⊢; omega
    · intro x hx hxA
      apply f_B_k1_zero n x hn <;> (intro heq; exact hxA (by simp [heq]))
  rw [hB]
  have hmem1 : n - 2 ∉ ({n - 1, n, n + 1, n + 2} : Finset ℕ) := by simp; omega
  have hmem2 : n - 1 ∉ ({n, n + 1, n + 2} : Finset ℕ) := by simp; omega
  have hmem3 : n ∉ ({n + 1, n + 2} : Finset ℕ) := by simp
  have hmem4 : n + 1 ≠ n + 2 := by omega
  rw [Finset.sum_insert hmem1, Finset.sum_insert hmem2,
      Finset.sum_insert hmem3, Finset.sum_pair hmem4,
      f_B_k1_at_n n hn]
  unfold B_center_excess_k1 R_off_k1
  ring

/-- Bplus = B + 2u = B_center_excess + R_off for k=1. -/
private lemma Bplus_k1_formula (n : ℕ) (hn : 3 ≤ n) :
    B_eval n (deform_spec n 1) + 2 * u_val n =
    B_center_excess_k1 n + R_off_k1 n := by
  have := B_eval_k1_decomp n hn; linarith

/-! ### k=1 valuation helper lemmas -/

/-- v_p(B_center_excess_k1) = e_central for the k=1 case.
    B_center_excess = -8*u_val/n, which has v_p = e since v_p(8) = v_p(n) = 0. -/
private lemma f_B_k1_at_nm1 (n : ℕ) (hn : 3 ≤ n) :
    f_B_k1 n (n - 1) =
    (-1 : ℤ) ^ (n - 1) * (Nat.choose (2 * n) (n - 1) : ℤ) *
      ((α n (n - 1) : ℤ) ^ 2 - (γ n : ℤ) ^ 2) := by
  unfold f_B_k1
  have hc1 : deform_spec n 1 (n - 1) = 1 := by unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc2 : deform_spec n 1 (2 * n + 1 - (n - 1)) = 1 := by
    rw [show 2 * n + 1 - (n - 1) = n + 2 from by omega]
    unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc3 : deform_spec n 1 (n - 1 + 1) = 1 := by
    rw [show n - 1 + 1 = n from by omega]
    unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc4 : deform_spec n 1 (2 * n - (n - 1)) = -1 := by
    rw [show 2 * n - (n - 1) = n + 1 from by omega]
    unfold deform_spec; split_ifs <;> omega
  have hβ : β n (n - 1) = γ n := by
    unfold β γ
    rw [show 2 * n - (n - 1) = n + 1 from by omega, show n - 1 + 1 = n from by omega]
  rw [hc1, hc2, hc3, hc4, hβ]; ring

private lemma f_B_k1_at_np1 (n : ℕ) (hn : 3 ≤ n) :
    f_B_k1 n (n + 1) =
    (-1 : ℤ) ^ (n + 1) * (Nat.choose (2 * n) (n + 1) : ℤ) *
      (-(γ n : ℤ) ^ 2 + (β n (n + 1) : ℤ) ^ 2) := by
  unfold f_B_k1
  have hc1 : deform_spec n 1 (n + 1) = -1 := by unfold deform_spec; split_ifs <;> omega
  have hc2 : deform_spec n 1 (2 * n + 1 - (n + 1)) = 1 := by
    rw [show 2 * n + 1 - (n + 1) = n from by omega]
    unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc3 : deform_spec n 1 (n + 1 + 1) = 1 := by
    rw [show n + 1 + 1 = n + 2 from by omega]
    unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc4 : deform_spec n 1 (2 * n - (n + 1)) = 1 := by
    rw [show 2 * n - (n + 1) = n - 1 from by omega]
    unfold deform_spec; split_ifs <;> omega <;> rfl
  have hα : α n (n + 1) = γ n := by
    unfold α γ; rw [show 2 * n + 1 - (n + 1) = n from by omega]; ring
  rw [hc1, hc2, hc3, hc4, hα]; ring

/-- α(n, n-1) = β(n, n+1). -/
private lemma alpha_nm1_eq_beta_np1 (n : ℕ) (hn : 1 ≤ n) :
    α n (n - 1) = β n (n + 1) := by
  unfold α β
  rw [show 2 * n + 1 - (n - 1) = n + 2 from by omega,
      show 2 * n - (n + 1) = n - 1 from by omega,
      show n + 1 + 1 = n + 2 from by omega]
  ring

/-- B_center_excess_k1 = 2*(-1)^(n-1) * C(2n,n-1) * (α(n,n-1)² - γ²). -/
private lemma B_center_excess_k1_formula (n : ℕ) (hn : 3 ≤ n) :
    B_center_excess_k1 n =
    2 * (-1 : ℤ) ^ (n - 1) * (Nat.choose (2 * n) (n - 1) : ℤ) *
      ((α n (n - 1) : ℤ) ^ 2 - (γ n : ℤ) ^ 2) := by
  unfold B_center_excess_k1
  rw [f_B_k1_at_nm1 n hn, f_B_k1_at_np1 n hn]
  have hsymm : (Nat.choose (2 * n) (n + 1) : ℤ) = (Nat.choose (2 * n) (n - 1) : ℤ) :=
    choose_symm' n (by omega)
  have hαβ : (α n (n - 1) : ℤ) = (β n (n + 1) : ℤ) := by
    exact_mod_cast alpha_nm1_eq_beta_np1 n (by omega)
  have hpow : (-1 : ℤ) ^ (n + 1) = (-1 : ℤ) ^ (n - 1) := by
    rw [show n + 1 = n - 1 + 2 from by omega, pow_add]; simp
  rw [hsymm, hαβ, hpow]; ring

/-- α(n,n-1)² - γ² = 4*(n+1) * ((n+1)! * (n-1)!)². -/
private lemma alpha_sq_minus_gamma_sq (n : ℕ) (hn : 1 ≤ n) :
    (α n (n - 1) : ℤ) ^ 2 - (γ n : ℤ) ^ 2 =
    (((n + 2 : ℤ) ^ 2 - (n : ℤ) ^ 2) * ((Nat.factorial (n + 1) : ℤ) * (Nat.factorial (n - 1) : ℤ)) ^ 2) := by
  have hα : α n (n - 1) = Nat.factorial (n + 2) * Nat.factorial (n - 1) := by
    unfold α; rw [show 2 * n + 1 - (n - 1) = n + 2 from by omega]
  have hγ : γ n = Nat.factorial (n + 1) * Nat.factorial n := by unfold γ; ring
  have hfact_n2 : (Nat.factorial (n + 2) : ℤ) = (n + 2 : ℤ) * (Nat.factorial (n + 1) : ℤ) := by
    rw [show n + 2 = (n + 1) + 1 from by omega, Nat.factorial_succ]; push_cast; ring
  have hfact_n : (Nat.factorial n : ℤ) = (n : ℤ) * (Nat.factorial (n - 1) : ℤ) := by
    rw [show n = (n - 1) + 1 from by omega, Nat.factorial_succ]; push_cast; ring
  rw [hα, hγ]; push_cast; rw [hfact_n2, hfact_n]; ring

/-- (n+2)² - n² = 4*(n+1). -/
private lemma sq_diff_identity (n : ℕ) :
    (n + 2 : ℤ) ^ 2 - (n : ℤ) ^ 2 = 4 * ((n : ℤ) + 1) := by ring

/-- n * ((n+1)! * (n-1)!)² = γ(n)². -/
private lemma gamma_sq_factor (n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ^ 2 * ((Nat.factorial (n + 1) : ℤ) * (Nat.factorial (n - 1) : ℤ)) ^ 2 =
    (γ n : ℤ) ^ 2 := by
  have hγ : γ n = Nat.factorial (n + 1) * Nat.factorial n := by unfold γ; ring
  have hfact_n : (Nat.factorial n : ℤ) = (n : ℤ) * (Nat.factorial (n - 1) : ℤ) := by
    rw [show n = (n - 1) + 1 from by omega, Nat.factorial_succ]; push_cast; ring
  rw [hγ]; push_cast; rw [hfact_n]; ring

/-- B_center_excess_k1 n * n² = 8*(n+1)*(-1)^(n-1)*C(2n,n-1)*γ². -/
private lemma B_center_excess_k1_mul_nsq (n : ℕ) (hn : 3 ≤ n) :
    (B_center_excess_k1 n) * (n : ℤ) ^ 2 =
    8 * ((n : ℤ) + 1) * (-1 : ℤ) ^ (n - 1) * (Nat.choose (2 * n) (n - 1) : ℤ) * ((γ n : ℤ) ^ 2) := by
  rw [B_center_excess_k1_formula n hn, alpha_sq_minus_gamma_sq n (by omega), sq_diff_identity]
  rw [← gamma_sq_factor n (by omega)]; ring

/-- B_center_excess_k1 n * n = -8 * u_val n. Uses C(2n,n-1)*(n+1) = C(2n,n)*n. -/
private lemma B_center_excess_k1_mul_n (n : ℕ) (hn : 3 ≤ n) :
    (B_center_excess_k1 n) * (n : ℤ) =
    -8 * u_val n := by
  -- From B_center_excess_k1_mul_nsq: ce * n² = 8*(n+1)*(-1)^(n-1)*C(2n,n-1)*γ²
  -- Using C(2n,n-1)*(n+1) = C(2n,n)*n:
  -- ce * n² = 8*(-1)^(n-1)*C(2n,n)*n*γ² = -8*(-1)^n*C(2n,n)*n*γ² = -8*n*u_val
  -- So ce * n = -8*u_val (dividing by n, which is nonzero)
  have hn_ne : (n : ℤ) ≠ 0 := by omega
  have h := B_center_excess_k1_mul_nsq n hn
  -- h : ce * n² = 8*(n+1)*(-1)^(n-1)*C(2n,n-1)*γ²
  -- Rewrite n² = n * n and cancel one n
  have hsq : (n : ℤ) ^ 2 = (n : ℤ) * (n : ℤ) := sq (n : ℤ)
  rw [hsq] at h
  -- h : ce * (n * n) = 8*(n+1)*(-1)^(n-1)*C(2n,n-1)*γ²
  -- Use hident to replace C(2n,n-1)*(n+1) with C(2n,n)*n
  have hident := choose_identity n (by omega)
  have hident_int : (Nat.choose (2 * n) (n - 1) : ℤ) * ((n : ℤ) + 1) =
      (Nat.choose (2 * n) n : ℤ) * (n : ℤ) := by exact_mod_cast hident
  have hpow : (-1 : ℤ) ^ (n - 1) = -(-1 : ℤ) ^ n := by
    conv_rhs => rw [show n = n - 1 + 1 from by omega, pow_succ]; ring
  -- RHS = 8*(-1)^(n-1) * (C(2n,n-1)*(n+1)) * γ² = 8*(-1)^(n-1)*C(2n,n)*n*γ²
  -- = 8*(-(-1)^n)*C(2n,n)*n*γ² = -8*n*(-1)^n*C(2n,n)*γ² = -8*n*u_val
  unfold u_val
  -- Need: ce * n = -8 * ((-1)^n * C(2n,n) * γ²)
  -- From h: ce * n * n = 8*(n+1)*(-1)^(n-1)*C(2n,n-1)*γ²
  -- = 8*(-(-1)^n)*(C(2n,n-1)*(n+1))*γ² [rearranging]
  -- = 8*(-(-1)^n)*C(2n,n)*n*γ² [by hident_int]
  -- = -8*(-1)^n*C(2n,n)*n*γ² = -8*n * ((-1)^n * C(2n,n) * γ²)
  -- So ce * n * n = (-8 * ((-1)^n * C(2n,n) * γ²)) * n
  -- Dividing by n: ce * n = -8 * ((-1)^n * C(2n,n) * γ²)
  -- After rw [hpow] in h, we get:
  -- h : ce * (n * n) = 8 * (↑n + 1) * -(-1)^n * C(2n,n-1) * γ²
  rw [hpow] at h
  -- Use hident_int: C(2n,n-1) * (n+1) = C(2n,n) * n
  -- So (n+1) * C(2n,n-1) = C(2n,n) * n
  -- h : ce * n * n = -8 * (-1)^n * (n+1) * C(2n,n-1) * γ²
  --               = -8 * (-1)^n * C(2n,n) * n * γ²
  --               = (-8 * (-1)^n * C(2n,n) * γ²) * n
  -- So (ce * n - (-8 * (-1)^n * C(2n,n) * γ²)) * n = 0
  -- Since n ≠ 0, ce * n = -8 * (-1)^n * C(2n,n) * γ²
  have hmul : (B_center_excess_k1 n * (n : ℤ) + 8 * ((-1 : ℤ) ^ n * ↑(Nat.choose (2 * n) n) * ↑(γ n) ^ 2)) * (n : ℤ) = 0 := by
    linear_combination h - 8 * (-1 : ℤ) ^ n * ↑(γ n) ^ 2 * hident_int
  have := mul_eq_zero.mp hmul
  cases this with
  | inl h => linarith
  | inr h => exact absurd h hn_ne

private lemma B_center_excess_k1_val (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (hp5 : 5 ≤ p) (n : ℕ) (hn : n + 2 = p) (hn_pos : 1 ≤ n) :
    B_center_excess_k1 n ≠ 0 ∧
    padicValNat p (Int.natAbs (B_center_excess_k1 n)) = e_central p n := by
  have hn3 : 3 ≤ n := by omega
  have hce_mul := B_center_excess_k1_mul_n n hn3
  -- hce_mul : B_center_excess_k1 n * ↑n = -8 * u_val n
  -- First show u_val n ≠ 0
  have hu_ne : u_val n ≠ 0 := by
    unfold u_val
    apply mul_ne_zero
    apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega))
    · exact pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt (by unfold γ; positivity))
  -- Therefore -8*u_val ≠ 0
  have h8u_ne : -8 * u_val n ≠ 0 := by
    intro h; apply hu_ne; linarith
  -- Therefore ce * n ≠ 0, and since n ≠ 0, ce ≠ 0
  have hn_ne : (n : ℤ) ≠ 0 := by omega
  have hce_ne : B_center_excess_k1 n ≠ 0 := by
    intro h; rw [h, zero_mul] at hce_mul; exact h8u_ne hce_mul.symm
  constructor
  · exact hce_ne
  · -- v_p(ce * n) = v_p(-8 * u_val) = v_p(u_val) = e_central
    -- v_p(ce) + v_p(n) = v_p(ce) + 0 = v_p(ce)
    -- v_p(u_val) = v_p(C(2n,n) * γ²) = e_central
    -- v_p(n) = 0 since p = n+2 doesn't divide n (p odd)
    have hvn : padicValNat p n = 0 := by
      rw [padicValNat.eq_zero_iff]; right; right
      have : n + 2 = p ^ 1 := by rw [pow_one]; exact hn
      exact p_not_dvd_n p hp_odd 1 (by omega) n this
    have hv8 : padicValNat p 8 = 0 := by
      rw [show (8 : ℕ) = 2 ^ 3 from by norm_num]
      rw [padicValNat.pow 3 (by omega)]
      simp [padicValNat_primes hp_odd]
    -- v_p(|u_val|) = e_central
    have hu_abs : Int.natAbs (u_val n) = Nat.choose (2 * n) n * (γ n) ^ 2 := by
      unfold u_val
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow,
          show Int.natAbs (-1 : ℤ) = 1 from by norm_num,
          one_pow, one_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    have hu_val_padic : padicValNat p (Int.natAbs (u_val n)) = e_central p n := by
      rw [hu_abs]; rfl
    -- From ce * n = -8 * u_val, take natAbs:
    -- |ce| * n = 8 * |u_val|
    have habs_eq : Int.natAbs (B_center_excess_k1 n) * n = 8 * Int.natAbs (u_val n) := by
      have h1 := congr_arg Int.natAbs hce_mul
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_mul,
          show Int.natAbs (-8 : ℤ) = 8 from by norm_num] at h1
      exact h1
    -- v_p(|ce| * n) = v_p(8 * |u_val|)
    have hce_abs_ne : Int.natAbs (B_center_excess_k1 n) ≠ 0 :=
      Int.natAbs_ne_zero.mpr hce_ne
    have hu_abs_ne : Int.natAbs (u_val n) ≠ 0 :=
      Int.natAbs_ne_zero.mpr hu_ne
    have hlhs : padicValNat p (Int.natAbs (B_center_excess_k1 n) * n) =
        padicValNat p (Int.natAbs (B_center_excess_k1 n)) + 0 := by
      rw [padicValNat.mul hce_abs_ne (by omega), hvn]
    have hrhs : padicValNat p (8 * Int.natAbs (u_val n)) =
        0 + e_central p n := by
      rw [padicValNat.mul (by omega) hu_abs_ne, hv8, hu_val_padic]
    rw [habs_eq] at hlhs
    simp at hlhs hrhs; linarith

/-- v_p(γ(n)²) = 0 when n+2 = p (all factors of (n+1)!*n! are < p). -/
private lemma gamma_sq_val_k1 (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n + 2 = p) :
    padicValNat p ((γ n) ^ 2) = 0 := by
  have hγ : γ n = (n + 1).factorial * n.factorial := by unfold γ; ring
  rw [hγ]
  rw [show (n + 1).factorial * n.factorial = (n + 1).factorial * n.factorial from rfl]
  rw [mul_pow, padicValNat.mul (by positivity) (by positivity)]
  rw [sq, sq, padicValNat.mul (by positivity) (by positivity),
      padicValNat.mul (by positivity) (by positivity)]
  -- Need v_p((n+1)!) = 0 and v_p(n!) = 0
  -- Since all factors ≤ n+1 < p = n+2
  have h1 : padicValNat p (n + 1).factorial = 0 := by
    rw [padicValNat.eq_zero_iff]; right; right
    intro hdvd
    have := (Fact.out : p.Prime).dvd_factorial.mp hdvd
    omega
  have h2 : padicValNat p n.factorial = 0 := by
    rw [padicValNat.eq_zero_iff]; right; right
    intro hdvd
    have := (Fact.out : p.Prime).dvd_factorial.mp hdvd
    omega
  omega

/-- e_central p n = v_p(C(2n,n)) when n+2 = p (since v_p(γ²) = 0). -/
private lemma e_central_k1_eq (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n + 2 = p) :
    e_central p n = padicValNat p (Nat.choose (2 * n) n) := by
  unfold e_central
  rw [padicValNat.mul (by exact Nat.ne_of_gt (Nat.choose_pos (by omega)))
      (by exact Nat.ne_of_gt (by unfold γ; positivity))]
  rw [gamma_sq_val_k1 p n hn, add_zero]

/-- e_central p n = 1 when n + 2 = p ≥ 5. -/
private lemma e_central_k1_val (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (n : ℕ)
    (hn : n + 2 = p) :
    e_central p n = 1 := by
  rw [e_central_k1_eq p n hn]
  -- v_p(C(2n, n)) where n = p-2, so C(2(p-2), p-2) = C(2p-4, p-2)
  -- Use Kummer: carries in (p-2) + (p-2) base p
  -- p-2 < p, so it's a single digit. (p-2)+(p-2) = 2p-4.
  -- Since p ≥ 5, 2(p-2) = 2p-4 ≥ p, so there's 1 carry.
  -- Use padicValNat_choose with b = 2:
  -- v_p(C(2n, n)) = #{i ∈ [1,2) : p^i ≤ n % p^i + n % p^i}
  -- For i=1: p^1 ≤ n % p + n % p = (p-2)%p + (p-2)%p = (p-2)+(p-2) = 2p-4 ≥ p. Yes.
  -- So the count is 1.
  rw [padicValNat_choose (show n ≤ 2 * n from by omega) (show Nat.log p (2 * n) < 2 from ?_)]
  · -- The filter: #{i ∈ Ico 1 2 : p^i ≤ n % p^i + (2*n - n) % p^i}
    -- = #{i ∈ {1} : p^i ≤ n % p^i + n % p^i}
    -- For i=1: p ≤ (p-2) + (p-2) = 2p-4. True since p ≥ 5 gives 2p-4 ≥ p+1 > p.
    simp only [show 2 * n - n = n from by omega]
    rw [show Finset.Ico 1 2 = {1} from by decide]
    simp only [Finset.filter_singleton]
    rw [if_pos]
    · -- Goal should be #{..} = 1, which is Finset.card {1} = 1
      rfl
    · -- p^1 ≤ n % p^1 + n % p^1
      rw [pow_one]
      rw [show n % p = n from Nat.mod_eq_of_lt (by omega)]
      omega
  · -- Nat.log p (2*n) < 2, i.e., 2n < p²
    -- n = p-2, so 2n = 2p-4 < p² for p ≥ 3
    have hp_pos : 1 < p := (Fact.out : p.Prime).one_lt
    exact Nat.log_lt_of_lt_pow (by omega) (by nlinarith)

/-- p divides (n+2)! (since n+2 = p). -/
private lemma p_dvd_factorial_n2 (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n + 2 = p) :
    p ∣ (n + 2).factorial := by
  rw [hn]; exact (Fact.out : p.Prime).dvd_factorial.mpr le_rfl

private lemma R_off_k1_dvd (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (hp5 : 5 ≤ p) (n : ℕ) (hn : n + 2 = p) (hn_pos : 1 ≤ n) :
    (p : ℤ) ^ (e_central p n + 1) ∣ R_off_k1 n := by
  -- e_central = 1 for k=1, so we need p² | R_off_k1
  rw [e_central_k1_val p hp5 n hn]
  -- R_off_k1 = f_B_k1 n (n-2) + f_B_k1 n (n+2)
  -- Each term has α(n,n+2)² or β(n,n-2)² which contain p²
  -- since α(n,n+2) = (n-1)!*(n+2)! and β(n,n-2) = (n+2)!*(n-1)!, both divisible by p
  have hn3 : 3 ≤ n := by omega
  -- Step 1: Compute f_B_k1 at n-2 and n+2
  have hfnm2 : f_B_k1 n (n - 2) =
      (-1 : ℤ) ^ (n - 2) * (Nat.choose (2 * n) (n - 2) : ℤ) * (β n (n - 2) : ℤ) ^ 2 := by
    unfold f_B_k1
    have hc1 : deform_spec n 1 (n - 2) = 0 := by unfold deform_spec; split_ifs <;> omega
    have hc2 : deform_spec n 1 (2 * n + 1 - (n - 2)) = 0 := by
      rw [show 2 * n + 1 - (n - 2) = n + 3 from by omega]
      unfold deform_spec; split_ifs <;> omega
    have hc3 : deform_spec n 1 (n - 2 + 1) = 1 := by
      rw [show n - 2 + 1 = n - 1 from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc4 : deform_spec n 1 (2 * n - (n - 2)) = 1 := by
      rw [show 2 * n - (n - 2) = n + 2 from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    rw [hc1, hc2, hc3, hc4]; ring
  have hfnp2 : f_B_k1 n (n + 2) =
      (-1 : ℤ) ^ (n + 2) * (Nat.choose (2 * n) (n + 2) : ℤ) * (α n (n + 2) : ℤ) ^ 2 := by
    unfold f_B_k1
    have hc1 : deform_spec n 1 (n + 2) = 1 := by unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc2 : deform_spec n 1 (2 * n + 1 - (n + 2)) = 1 := by
      rw [show 2 * n + 1 - (n + 2) = n - 1 from by omega]
      unfold deform_spec; split_ifs <;> omega <;> rfl
    have hc3 : deform_spec n 1 (n + 2 + 1) = 0 := by
      unfold deform_spec; split_ifs <;> omega
    have hc4 : deform_spec n 1 (2 * n - (n + 2)) = 0 := by
      rw [show 2 * n - (n + 2) = n - 2 from by omega]
      unfold deform_spec; split_ifs <;> omega
    rw [hc1, hc2, hc3, hc4]; ring
  -- Step 2: p | α(n, n+2) and p | β(n, n-2)
  have hα_eq : α n (n + 2) = (n - 1).factorial * (n + 2).factorial := by
    unfold α; rw [show 2 * n + 1 - (n + 2) = n - 1 from by omega]
  have hβ_eq : β n (n - 2) = (n + 2).factorial * (n - 1).factorial := by
    unfold β; rw [show 2 * n - (n - 2) = n + 2 from by omega,
                   show n - 2 + 1 = n - 1 from by omega]
  have hp_dvd_fact : p ∣ (n + 2).factorial := p_dvd_factorial_n2 p n hn
  have hp_dvd_α : (p : ℤ) ∣ (α n (n + 2) : ℤ) := by
    rw [hα_eq]; push_cast
    exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hp_dvd_fact) _
  have hp_dvd_β : (p : ℤ) ∣ (β n (n - 2) : ℤ) := by
    rw [hβ_eq]; push_cast
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hp_dvd_fact) _
  -- Step 3: p² | α² and p² | β²
  have hp2_dvd_α2 : (p : ℤ) ^ 2 ∣ (α n (n + 2) : ℤ) ^ 2 := by
    rw [sq, sq]; exact mul_dvd_mul hp_dvd_α hp_dvd_α
  have hp2_dvd_β2 : (p : ℤ) ^ 2 ∣ (β n (n - 2) : ℤ) ^ 2 := by
    rw [sq, sq]; exact mul_dvd_mul hp_dvd_β hp_dvd_β
  -- Step 4: p² | each term of R_off_k1
  have hd1 : (p : ℤ) ^ 2 ∣ f_B_k1 n (n - 2) := by
    rw [hfnm2]; exact dvd_mul_of_dvd_right hp2_dvd_β2 _
  have hd2 : (p : ℤ) ^ 2 ∣ f_B_k1 n (n + 2) := by
    rw [hfnp2]; exact dvd_mul_of_dvd_right hp2_dvd_α2 _
  -- Step 5: p² | R_off_k1
  unfold R_off_k1
  exact dvd_add hd1 hd2

/-- C(2n,n+2)*(n+1)*(n+2) = C(2n,n)*n*(n-1). -/
private lemma choose_identity2 (n : ℕ) (hn : 2 ≤ n) :
    Nat.choose (2 * n) (n + 2) * (n + 1) * (n + 2) = Nat.choose (2 * n) n * n * (n - 1) := by
  -- C(2n,n+1) = C(2n,n) * (2n-n)/(n+1) = C(2n,n) * n/(n+1)
  -- C(2n,n+2) = C(2n,n+1) * (2n-(n+1))/(n+2) = C(2n,n+1) * (n-1)/(n+2)
  -- So C(2n,n+2)*(n+1)*(n+2) = C(2n,n)*n*(n-1)
  have h1 : Nat.choose (2 * n) (n + 1) * (n + 1) = Nat.choose (2 * n) n * n := by
    have := Nat.choose_succ_right_eq (2 * n) n
    rw [show 2 * n - n = n from by omega] at this; linarith
  have h2 : Nat.choose (2 * n) (n + 2) * (n + 2) = Nat.choose (2 * n) (n + 1) * (n - 1) := by
    have := Nat.choose_succ_right_eq (2 * n) (n + 1)
    rw [show 2 * n - (n + 1) = n - 1 from by omega] at this; linarith
  -- From h2: C(2n,n+2)*(n+2)*(n+1) = C(2n,n+1)*(n-1)*(n+1)
  -- From h1: C(2n,n+1)*(n+1) = C(2n,n)*n
  -- So C(2n,n+2)*(n+2)*(n+1) = (n-1)*C(2n,n)*n
  nlinarith [h1, h2]

/-- R_off_k1 n in explicit form: 2*(-1)^(n+2)*C(2n,n+2)*α(n,n+2)². -/
private lemma R_off_k1_formula (n : ℕ) (hn : 3 ≤ n) :
    R_off_k1 n = 2 * (-1 : ℤ) ^ (n + 2) * (Nat.choose (2 * n) (n + 2) : ℤ) *
      ((α n (n + 2) : ℤ) ^ 2) := by
  unfold R_off_k1 f_B_k1
  have hc1a : deform_spec n 1 (n - 2) = 0 := by unfold deform_spec; split_ifs <;> omega
  have hc1b : deform_spec n 1 (2 * n + 1 - (n - 2)) = 0 := by
    rw [show 2 * n + 1 - (n - 2) = n + 3 from by omega]; unfold deform_spec; split_ifs <;> omega
  have hc1c : deform_spec n 1 (n - 2 + 1) = 1 := by
    rw [show n - 2 + 1 = n - 1 from by omega]; unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc1d : deform_spec n 1 (2 * n - (n - 2)) = 1 := by
    rw [show 2 * n - (n - 2) = n + 2 from by omega]; unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc2a : deform_spec n 1 (n + 2) = 1 := by unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc2b : deform_spec n 1 (2 * n + 1 - (n + 2)) = 1 := by
    rw [show 2 * n + 1 - (n + 2) = n - 1 from by omega]; unfold deform_spec; split_ifs <;> omega <;> rfl
  have hc2c : deform_spec n 1 (n + 2 + 1) = 0 := by unfold deform_spec; split_ifs <;> omega
  have hc2d : deform_spec n 1 (2 * n - (n + 2)) = 0 := by
    rw [show 2 * n - (n + 2) = n - 2 from by omega]; unfold deform_spec; split_ifs <;> omega
  -- β(n, n-2) = α(n, n+2) (they're both (n-1)!*(n+2)!)
  have hβα : β n (n - 2) = α n (n + 2) := by
    unfold β α
    rw [show 2 * n - (n - 2) = n + 2 from by omega,
        show n - 2 + 1 = n - 1 from by omega,
        show 2 * n + 1 - (n + 2) = n - 1 from by omega]; ring
  -- C(2n, n-2) = C(2n, n+2) by symmetry
  have hCsymm : (Nat.choose (2 * n) (n - 2) : ℤ) = (Nat.choose (2 * n) (n + 2) : ℤ) := by
    congr 1
    rw [← Nat.choose_symm (show n + 2 ≤ 2 * n from by omega)]
    congr 1; omega
  -- (-1)^(n-2) = (-1)^(n+2)
  have hpow : (-1 : ℤ) ^ (n - 2) = (-1 : ℤ) ^ (n + 2) := by
    rw [show n + 2 = n - 2 + 4 from by omega, pow_add]; simp
  rw [hc1a, hc1b, hc1c, hc1d, hc2a, hc2b, hc2c, hc2d, hβα, hCsymm, hpow]; ring

/-- The key identity: (B-2u)*n*(n+1) = -2*(-1)^n*p*n*(n+3)*C(2n,n)*((n-1)!*(n+1)!)².
    Here p = n+2 and the identity combines B_center_excess_k1_mul_n with R_off_k1_formula
    and the binomial identity C(2n,n+2)*(n+1)*(n+2) = C(2n,n)*n*(n-1). -/
private lemma Bminus_k1_mul_identity (n : ℕ) (hn : 3 ≤ n) :
    (B_eval n (deform_spec_k1 n) - 2 * u_val n) * (n : ℤ) * ((n : ℤ) + 1) =
    -2 * (-1 : ℤ) ^ n * ((n : ℤ) + 2) * (n : ℤ) ^ 2 * ((n : ℤ) + 3) *
    (Nat.choose (2 * n) n : ℤ) * ((Nat.factorial (n - 1) : ℤ) * (Nat.factorial (n + 1) : ℤ)) ^ 2 := by
  have hdecomp := B_eval_k1_decomp n hn
  have hce_mul := B_center_excess_k1_mul_n n hn
  have hR := R_off_k1_formula n hn
  have hBm_n : (B_eval n (deform_spec_k1 n) - 2 * u_val n) * (n : ℤ) =
      -4 * u_val n * ((n : ℤ) + 2) + (n : ℤ) * R_off_k1 n := by
    rw [B_eval_k1_eq n (by omega)]; nlinarith [hdecomp, hce_mul]
  have hγsq := gamma_sq_factor n (by omega)
  have hα_val : (α n (n + 2) : ℤ) = ((n : ℤ) + 2) * ((Nat.factorial (n - 1) : ℤ) * (Nat.factorial (n + 1) : ℤ)) := by
    unfold α; rw [show 2 * n + 1 - (n + 2) = n - 1 from by omega]; push_cast
    rw [show (Nat.factorial (n + 2) : ℤ) = ((n : ℤ) + 2) * (Nat.factorial (n + 1) : ℤ) from by
      rw [show n + 2 = (n + 1) + 1 from by omega, Nat.factorial_succ]; push_cast; ring]
    ring
  have hpow_eq : (-1 : ℤ) ^ (n + 2) = (-1 : ℤ) ^ n := by rw [pow_add]; simp
  have hident2_int : (Nat.choose (2 * n) (n + 2) : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) =
      (Nat.choose (2 * n) n : ℤ) * (n : ℤ) * ((n : ℤ) - 1) := by
    have h := choose_identity2 n (by omega)
    have : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
    rw [this]; exact_mod_cast h
  set F := (Nat.factorial (n - 1) : ℤ) * (Nat.factorial (n + 1) : ℤ)
  set s := (-1 : ℤ) ^ n
  set C0 := (Nat.choose (2 * n) n : ℤ)
  set C2 := (Nat.choose (2 * n) (n + 2) : ℤ)
  have hu : u_val n = s * C0 * ((n : ℤ) ^ 2 * F ^ 2) := by
    unfold u_val; rw [← hγsq]; ring
  rw [hR, hα_val, hpow_eq, hu] at hBm_n
  -- hBm_n : (B-2u)*n = -4*(s*C0*(n²*F²))*(n+2) + n*(2*s*C2*((n+2)*F)²)
  -- But LHS has u_val replaced too:
  -- (B_eval - 2*(s*C0*(n²*F²)))*n = ...
  -- Hmm, u_val was replaced on the LHS too. Let me re-express the goal.
  rw [hu]
  -- Goal now: (B_eval - 2*(s*C0*(n²*F²)))*n*(n+1) = -2*s*(n+2)*n²*(n+3)*C0*F²
  -- From hBm_n: (B_eval - 2*(s*C0*(n²*F²)))*n = -4*(s*C0*(n²*F²))*(n+2) + n*(2*s*C2*((n+2)*F)²)
  -- So (B_eval - 2*(s*C0*(n²*F²)))*n*(n+1)
  -- = [-4*(s*C0*(n²*F²))*(n+2) + 2*n*s*C2*((n+2)*F)²] * (n+1)
  -- Use hident2_int to relate C2*(n+1)*(n+2) to C0*n*(n-1)
  have h1 : (B_eval n (deform_spec_k1 n) - 2 * (s * C0 * (↑n ^ 2 * F ^ 2))) * ↑n * (↑n + 1) =
    (-4 * (s * C0 * (↑n ^ 2 * F ^ 2)) * (↑n + 2) + ↑n * (2 * s * C2 * ((↑n + 2) * F) ^ 2)) * (↑n + 1) := by
    congr 1
  rw [h1]
  linear_combination 2 * F ^ 2 * s * ((n : ℤ) + 2) * (n : ℤ) * hident2_int

/-- B-2u is nonzero with v_p = e+1 for the k=1 case. -/
private lemma Bminus_k1_val (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (hp5 : 5 ≤ p) (n : ℕ) (hn : n + 2 = p) (hn_pos : 1 ≤ n) :
    B_eval n (deform_spec_k1 n) - 2 * u_val n ≠ 0 ∧
    padicValNat p (Int.natAbs (B_eval n (deform_spec_k1 n) - 2 * u_val n)) =
      e_central p n + 1 := by
  have hn3 : 3 ≤ n := by omega
  have hid := Bminus_k1_mul_identity n hn3
  -- RHS of identity = -2*(-1)^n*(n+2)*n²*(n+3)*C(2n,n)*F²
  -- where F = (n-1)!*(n+1)!
  -- This is nonzero (all factors are nonzero)
  set Bm := B_eval n (deform_spec_k1 n) - 2 * u_val n with hBm_def
  set RHS := -2 * (-1 : ℤ) ^ n * ((n : ℤ) + 2) * (n : ℤ) ^ 2 * ((n : ℤ) + 3) *
    (Nat.choose (2 * n) n : ℤ) * ((Nat.factorial (n - 1) : ℤ) * (Nat.factorial (n + 1) : ℤ)) ^ 2 with hRHS_def
  have hRHS_ne : RHS ≠ 0 := by
    simp only [hRHS_def]
    apply mul_ne_zero; apply mul_ne_zero; apply mul_ne_zero
    apply mul_ne_zero; apply mul_ne_zero; apply mul_ne_zero
    · norm_num
    · exact pow_ne_zero _ (by norm_num)
    · omega
    · exact pow_ne_zero _ (by omega)
    · omega
    · exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega))
    · apply pow_ne_zero; apply mul_ne_zero
      · exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos _)
      · exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos _)
  -- From hid: Bm * n * (n+1) = RHS, so Bm ≠ 0
  have hBm_ne : Bm ≠ 0 := by
    intro h; rw [h, zero_mul, zero_mul] at hid; exact hRHS_ne hid.symm
  -- v_p(Bm * n * (n+1)) = v_p(RHS)
  -- v_p(Bm) + v_p(n) + v_p(n+1) = v_p(RHS)
  -- v_p(n) = 0, v_p(n+1) = 0
  have hvn : padicValNat p n = 0 := by
    rw [padicValNat.eq_zero_iff]; right; right
    exact p_not_dvd_n p hp_odd 1 (by omega) n (by rw [pow_one]; exact hn)
  have hvn1 : padicValNat p (n + 1) = 0 := by
    rw [padicValNat.eq_zero_iff]; right; right
    exact p_not_dvd_n1 p 1 (by omega) n (by rw [pow_one]; exact hn)
  -- v_p(RHS): v_p(2*(-1)^n*(n+2)*n²*(n+3)*C(2n,n)*F²)
  -- = v_p(2) + 0 + v_p(n+2) + 0 + v_p(n+3) + v_p(C(2n,n)) + 0
  -- = 0 + 1 + 0 + e_central + 0 = e_central + 1
  have hvn2 : padicValNat p (n + 2) = 1 := by
    rw [hn]; exact padicValNat.self (Fact.out : p.Prime).one_lt
  have hvn3 : padicValNat p (n + 3) = 0 := by
    rw [padicValNat.eq_zero_iff]; right; right
    rw [show n + 3 = p + 1 from by omega]
    intro hdvd
    have h1 : (p : ℤ) ∣ ((p : ℤ) + 1) := by exact_mod_cast hdvd
    have h2 : (p : ℤ) ∣ (p : ℤ) := dvd_refl _
    have h3 : (p : ℤ) ∣ 1 := by
      have := dvd_sub h1 h2; rwa [show (p : ℤ) + 1 - (p : ℤ) = 1 from by ring] at this
    exact (Fact.out : p.Prime).one_lt.ne'
      (Nat.eq_one_of_dvd_one (Int.ofNat_dvd.mp (by exact_mod_cast h3)))
  have hv_choose := e_central_k1_eq p n hn
  -- Now compute v_p(|RHS|)
  -- |RHS| = 2 * (n+2) * n² * (n+3) * C(2n,n) * F²
  have habs_RHS : Int.natAbs RHS =
      2 * (n + 2) * n ^ 2 * (n + 3) * Nat.choose (2 * n) n *
      (Nat.factorial (n - 1) * Nat.factorial (n + 1)) ^ 2 := by
    -- RHS = -2 * (-1)^n * (n+2) * n² * (n+3) * C(2n,n) * F²
    -- |RHS| = 2 * (n+2) * n² * (n+3) * C(2n,n) * F²
    have : RHS = -((-1 : ℤ) ^ n) *
      (2 * ((n : ℤ) + 2) * (n : ℤ) ^ 2 * ((n : ℤ) + 3) *
      ↑(Nat.choose (2 * n) n) * (↑(Nat.factorial (n - 1)) * ↑(Nat.factorial (n + 1))) ^ 2) := by
      simp only [hRHS_def]; ring
    rw [this, Int.natAbs_mul, Int.natAbs_neg,
        show Int.natAbs ((-1 : ℤ) ^ n) = 1 from by simp, one_mul]
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    rfl
  have hF_ne : (Nat.factorial (n - 1) * Nat.factorial (n + 1)) ^ 2 ≠ 0 := by positivity
  have hC_ne : Nat.choose (2 * n) n ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hvF : padicValNat p ((Nat.factorial (n - 1) * Nat.factorial (n + 1)) ^ 2) = 0 := by
    rw [padicValNat.pow 2 (by positivity)]
    rw [padicValNat.mul (by positivity) (by positivity)]
    have h1 : padicValNat p (Nat.factorial (n - 1)) = 0 := by
      rw [padicValNat.eq_zero_iff]; right; right
      intro hdvd; have := (Fact.out : p.Prime).dvd_factorial.mp hdvd; omega
    have h2 : padicValNat p (Nat.factorial (n + 1)) = 0 := by
      rw [padicValNat.eq_zero_iff]; right; right
      intro hdvd; have := (Fact.out : p.Prime).dvd_factorial.mp hdvd; omega
    simp [h1, h2]
  have hv_RHS : padicValNat p (Int.natAbs RHS) = e_central p n + 1 := by
    rw [habs_RHS]
    -- 2 * (n+2) * n² * (n+3) * C(2n,n) * F²
    rw [padicValNat.mul (by positivity) hF_ne, hvF, add_zero]
    rw [padicValNat.mul (by positivity) hC_ne, hv_choose]
    rw [padicValNat.mul (by positivity) (by omega)]
    rw [padicValNat.mul (by positivity) (by positivity)]
    rw [padicValNat.mul (by omega) (by positivity)]
    rw [show padicValNat p 2 = 0 from padicValNat_primes hp_odd]
    rw [hvn2, padicValNat.pow 2 (by omega), hvn, hvn3]
    ring
  -- From hid: Bm * n * (n+1) = RHS
  -- |Bm * n * (n+1)| = |Bm| * n * (n+1)
  -- v_p(|Bm| * n * (n+1)) = v_p(|Bm|) + v_p(n) + v_p(n+1) = v_p(|Bm|)
  -- = v_p(|RHS|) = e_central + 1
  have habs_prod : Int.natAbs (Bm * (n : ℤ) * ((n : ℤ) + 1)) =
      Int.natAbs Bm * n * (n + 1) := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast,
        show Int.natAbs ((n : ℤ) + 1) = n + 1 from by
          rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) from by push_cast; ring]
          exact Int.natAbs_natCast _]
  have hv_prod : padicValNat p (Int.natAbs (Bm * (n : ℤ) * ((n : ℤ) + 1))) =
      padicValNat p (Int.natAbs Bm) := by
    rw [habs_prod, padicValNat.mul (by exact mul_ne_zero (Int.natAbs_ne_zero.mpr hBm_ne) (by omega)) (by omega)]
    rw [padicValNat.mul (Int.natAbs_ne_zero.mpr hBm_ne) (by omega)]
    rw [hvn, hvn1]; ring
  constructor
  · exact hBm_ne
  · have h_eq_abs : Int.natAbs (Bm * (n : ℤ) * ((n : ℤ) + 1)) = Int.natAbs RHS :=
      congr_arg Int.natAbs hid
    rw [← hv_prod, h_eq_abs, hv_RHS]

/-- A_eval + C_eval = 2*u under deform_spec_k1. The off-diagonal terms cancel:
    at each index i, c_i*c_{2n-i} + c_{i+1}*c_{2n+1-i} = 0 (for i ≠ n) or 2 (for i = n). -/
private lemma AC_sum_k1 (n : ℕ) (hn : 3 ≤ n) :
    A_eval n (deform_spec_k1 n) + C_eval n (deform_spec_k1 n) = 2 * u_val n := by
  -- A+C = Σ_i (-1)^i * C(2n,i) * α_i * β_i * (c_i*c_{2n-i} + c_{i+1}*c_{2n+1-i})
  -- For deform_spec_k1, the inner sum is 2 when i=n and 0 otherwise.
  -- So A+C = 2 * (-1)^n * C(2n,n) * α_n * β_n = 2u.
  unfold A_eval C_eval
  rw [show ∑ i ∈ Finset.range (2 * n + 1),
    (-1 : ℤ) ^ i * ↑((2 * n).choose i) * ↑(α n i) * ↑(β n i) * deform_spec_k1 n i * deform_spec_k1 n (2 * n - i) +
    ∑ i ∈ Finset.range (2 * n + 1),
    (-1 : ℤ) ^ i * ↑((2 * n).choose i) * ↑(α n i) * ↑(β n i) * deform_spec_k1 n (i + 1) * deform_spec_k1 n (2 * n + 1 - i) =
    ∑ i ∈ Finset.range (2 * n + 1),
    (-1 : ℤ) ^ i * ↑((2 * n).choose i) * ↑(α n i) * ↑(β n i) *
    (deform_spec_k1 n i * deform_spec_k1 n (2 * n - i) +
     deform_spec_k1 n (i + 1) * deform_spec_k1 n (2 * n + 1 - i))
    from by rw [← Finset.sum_add_distrib]; congr 1; ext i; ring]
  -- Now use Finset.sum_eq_single n
  rw [Finset.sum_eq_single n]
  · -- i = n term
    have h1 : deform_spec_k1 n n = 1 := by unfold deform_spec_k1; split_ifs <;> omega <;> rfl
    have h2 : deform_spec_k1 n (2 * n - n) = 1 := by
      rw [show 2 * n - n = n from by omega]; exact h1
    have h3 : deform_spec_k1 n (n + 1) = -1 := by unfold deform_spec_k1; split_ifs <;> omega
    have h4 : deform_spec_k1 n (2 * n + 1 - n) = -1 := by
      rw [show 2 * n + 1 - n = n + 1 from by omega]; exact h3
    rw [h1, h2, h3, h4]
    unfold u_val
    have hα : (α n n : ℤ) = (γ n : ℤ) := by
      unfold α γ; rw [show 2 * n + 1 - n = n + 1 from by omega]
    have hβ : (β n n : ℤ) = (γ n : ℤ) := by
      unfold β γ; rw [show 2 * n - n = n from by omega]; push_cast; ring
    rw [hα, hβ]; ring
  · -- i ≠ n: show the combined c-product is 0
    intro i _ hi
    suffices deform_spec_k1 n i * deform_spec_k1 n (2 * n - i) +
      deform_spec_k1 n (i + 1) * deform_spec_k1 n (2 * n + 1 - i) = 0 by
      rw [this]; ring
    unfold deform_spec_k1
    -- For each possible i value, the if-then-else evaluates to make the sum 0
    split_ifs <;> omega
  · -- n ∈ Finset.range (2*n+1)
    intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- u² - AC = (A-u)² when A+C = 2u. -/
private lemma u_sq_minus_AC_eq_sq (A C u : ℤ) (h : A + C = 2 * u) :
    u ^ 2 - A * C = (A - u) ^ 2 := by
  have hC : C = 2 * u - A := by linarith
  rw [hC]; ring

/-- p^(e+1) | (A_eval - u) for the k=1 deformation. -/
private lemma A_minus_u_k1_dvd (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (hp5 : 5 ≤ p) (n : ℕ) (hn : n + 2 = p) (hn_pos : 1 ≤ n) :
    (p : ℤ) ^ (e_central p n + 1) ∣ (A_eval n (deform_spec_k1 n) - u_val n) := by
  -- A - u = off-diagonal terms of A_eval
  -- Each off-diagonal summand has factor C(2n,i) * α_i * β_i
  -- which is divisible by p^(e+1) = p² since:
  -- v_p(C(2n,n-1)) = 1 and v_p(α(n,n-1)) = 1 (contains (n+2)! = p!)
  -- For the k=1 case, e_central = 1, so e+1 = 2.
  rw [e_central_k1_val p hp5 n hn]
  -- Need: p² | (A_eval - u)
  have hn3 : 3 ≤ n := by omega
  -- Step 1: Extract A_eval as sum, isolate i=n term which equals u
  have hA_eq : A_eval n (deform_spec_k1 n) =
    (∑ i ∈ Finset.range (2 * n + 1),
      (-1 : ℤ) ^ i * ↑((2 * n).choose i) * ↑(α n i) * ↑(β n i) *
      deform_spec_k1 n i * deform_spec_k1 n (2 * n - i)) := rfl
  -- The i=n term equals u
  have hterm_n : (-1 : ℤ) ^ n * ↑((2 * n).choose n) * ↑(α n n) * ↑(β n n) *
      deform_spec_k1 n n * deform_spec_k1 n (2 * n - n) = u_val n := by
    have hα : α n n = γ n := by unfold α γ; rw [show 2 * n + 1 - n = n + 1 from by omega]
    have hβ : β n n = γ n := by unfold β γ; rw [show 2 * n - n = n from by omega]; ring
    have h1 : deform_spec_k1 n n = 1 := by unfold deform_spec_k1; split_ifs <;> omega <;> rfl
    have h2 : deform_spec_k1 n (2 * n - n) = 1 := by
      rw [show 2 * n - n = n from by omega]; exact h1
    rw [h1, h2, hα, hβ]; unfold u_val; ring
  -- Step 2: A - u = Σ_{i≠n} f(i)
  -- For i ≠ n in the support, each term has p² | scalar part
  -- The only nonzero i≠n are i=n-1 and i=n+1
  -- At i=n-1: α(n,n-1) contains (n+2)! so p | α. Also C(2n,n-1) has v_p=1. So p² | term.
  -- At i=n+1: β(n,n+1) contains (n+2)! so p | β. Also C(2n,n+1) has v_p=1. So p² | term.
  -- Strategy: show each summand is divisible by p²
  -- We use dvd_sum and show p² | each summand
  have hA_sub : A_eval n (deform_spec_k1 n) - u_val n =
    ∑ i ∈ Finset.range (2 * n + 1),
      (-1 : ℤ) ^ i * ↑((2 * n).choose i) * ↑(α n i) * ↑(β n i) *
      deform_spec_k1 n i * deform_spec_k1 n (2 * n - i) - u_val n := rfl
  -- Rewrite as sum of (f(i) - if i=n then u else 0)
  -- Actually, use Finset.sum_sub to extract the i=n term
  -- A = Σ f(i) = f(n) + Σ_{i≠n} f(i) = u + Σ_{i≠n} f(i)
  -- So A - u = Σ_{i≠n} f(i)
  -- For i≠n, the summand is either 0 (most i) or involves p²
  -- Let's show p² | summand for each i
  -- For i where c_i = 0 or c_{2n-i} = 0: summand is 0, trivially divisible
  -- For i = n-1: p | α(n,n-1) (contains p!) and p | C(2n,n-1) by Kummer
  -- For i = n+1: p | β(n,n+1) (contains p!) and p | C(2n,n+1) by Kummer
  -- Use Finset.sum_eq_single to extract term n, then diff gives rest
  have hA_split : A_eval n (deform_spec_k1 n) = u_val n +
    ∑ i ∈ (Finset.range (2 * n + 1)).erase n,
      (-1 : ℤ) ^ i * ↑((2 * n).choose i) * ↑(α n i) * ↑(β n i) *
      deform_spec_k1 n i * deform_spec_k1 n (2 * n - i) := by
    rw [hA_eq]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (show n < 2 * n + 1 from by omega))]
    rw [hterm_n]
  rw [hA_split, add_sub_cancel_left]
  apply Finset.dvd_sum
  intro i hi
  simp only [Finset.mem_erase, Finset.mem_range] at hi
  -- For each i ≠ n in range, show p² | the summand
  -- Most summands are 0 (when c_i or c_{2n-i} = 0)
  -- For i = n-1, n+1: the scalar has p²
  by_cases hi1 : deform_spec_k1 n i = 0
  · rw [hi1]; ring_nf; exact dvd_zero _
  by_cases hi2 : deform_spec_k1 n (2 * n - i) = 0
  · rw [hi2]; ring_nf; exact dvd_zero _
  -- Now i must be n-1 or n+1 (the only other support values of deform_spec_k1 besides n)
  -- deform_spec_k1 is nonzero at n-1, n, n+1, n+2
  -- Since i ≠ n, the nonzero cases are i = n-1, n+1, n+2
  -- But for i=n+2: 2n-i = n-2, and deform_spec_k1 (n-2) = 0, contradicting hi2
  -- So i = n-1 or i = n+1
  have hi_cases : i = n - 1 ∨ i = n + 1 := by
    have : deform_spec_k1 n i ≠ 0 := hi1
    unfold deform_spec_k1 at this
    by_contra h
    push_neg at h
    have h1 : i ≠ n - 1 := h.1
    have h2 : i ≠ n + 1 := h.2
    -- So deform_spec_k1 n i ≠ 0 means i = n+2 (since i ≠ n, n-1, n+1)
    have : i = n + 2 := by
      simp only [ne_eq, ite_eq_right_iff, not_forall, exists_prop] at this
      by_contra h3
      apply this; split_ifs <;> omega
    -- But then 2n-i = n-2 and deform_spec_k1 (n-2) = 0
    subst this
    apply hi2
    rw [show 2 * n - (n + 2) = n - 2 from by omega]
    unfold deform_spec_k1; split_ifs <;> omega
  -- For i = n-1: p | C(2n,n-1) (v_p = 1) and p | α(n,n-1) (contains (n+2)!)
  -- For i = n+1: p | C(2n,n+1) (v_p = 1) and p | β(n,n+1) (contains (n+2)!)
  -- In both cases, p² | the summand
  rcases hi_cases with rfl | rfl
  · -- i = n-1
    -- p | C(2n,n-1): from e_central_k1_val and choose_identity
    have hp_dvd_choose : (p : ℤ) ∣ (Nat.choose (2 * n) (n - 1) : ℤ) := by
      have hv := e_central_k1_val p hp5 n hn
      -- e_central = 1 = v_p(C(2n,n)). C(2n,n-1) has same v_p by choose_identity.
      -- Actually, v_p(C(2n,n-1)) = v_p(C(2n,n)) = 1 (from e_central_k1_eq)
      -- Need to show p | C(2n,n-1)
      -- From choose_identity: C(2n,n-1)*(n+1) = C(2n,n)*n
      -- v_p(C(2n,n-1)) + v_p(n+1) = v_p(C(2n,n)) + v_p(n)
      -- v_p(C(2n,n-1)) + 0 = 1 + 0, so v_p(C(2n,n-1)) = 1
      have : padicValNat p (Nat.choose (2 * n) (n - 1)) ≥ 1 := by
        have h_id := choose_identity n (by omega)
        have h_cn : padicValNat p (Nat.choose (2 * n) n) = 1 := by
          rwa [← e_central_k1_eq p n hn]
        have h_id_int : Nat.choose (2 * n) (n - 1) * (n + 1) = Nat.choose (2 * n) n * n := h_id
        have hvn : padicValNat p n = 0 := by
          rw [padicValNat.eq_zero_iff]; right; right
          exact p_not_dvd_n p hp_odd 1 (by omega) n (by rw [pow_one]; exact hn)
        have hvn1 : padicValNat p (n + 1) = 0 := by
          rw [padicValNat.eq_zero_iff]; right; right
          exact p_not_dvd_n1 p 1 (by omega) n (by rw [pow_one]; exact hn)
        -- v_p(C(2n,n-1)*(n+1)) = v_p(C(2n,n)*n)
        -- v_p(C(2n,n-1)) + 0 = 1 + 0
        have h_val_eq : padicValNat p (Nat.choose (2 * n) (n - 1) * (n + 1)) =
            padicValNat p (Nat.choose (2 * n) n * n) := congr_arg _ h_id
        rw [padicValNat.mul (by exact Nat.ne_of_gt (Nat.choose_pos (by omega))) (by omega),
            hvn1,
            padicValNat.mul (by exact Nat.ne_of_gt (Nat.choose_pos (by omega))) (by omega),
            h_cn, hvn] at h_val_eq
        omega
      have h := (padicValNat_dvd_iff_le (Nat.ne_of_gt (Nat.choose_pos (by omega)))).mpr this
      rw [pow_one] at h; exact_mod_cast h
    -- p | α(n,n-1) (contains (n+2)! = p!)
    have hp_dvd_α : (p : ℤ) ∣ (α n (n - 1) : ℤ) := by
      unfold α; rw [show 2 * n + 1 - (n - 1) = n + 2 from by omega]; push_cast
      exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr (p_dvd_factorial_n2 p n hn)) _
    -- p² | C(2n,n-1) * α(n,n-1) * ... = p * p * ...
    -- summand = (-1)^(n-1) * C(2n,n-1) * α * β * c * c
    -- p | C(2n,n-1), p | α(n,n-1), so p² | the whole expression
    rw [sq]
    have h_core : (p : ℤ) * (p : ℤ) ∣
      (Nat.choose (2 * n) (n - 1) : ℤ) * (α n (n - 1) : ℤ) :=
      mul_dvd_mul hp_dvd_choose hp_dvd_α
    -- Now the summand = (-1)^(n-1) * (C * α) * β * c1 * c2
    -- Since p*p | C*α, p*p divides the whole thing
    have : (-1 : ℤ) ^ (n - 1) * ↑(Nat.choose (2 * n) (n - 1)) *
        ↑(α n (n - 1)) * ↑(β n (n - 1)) *
        deform_spec_k1 n (n - 1) * deform_spec_k1 n (2 * n - (n - 1)) =
      ((Nat.choose (2 * n) (n - 1) : ℤ) * (α n (n - 1) : ℤ)) *
      ((-1 : ℤ) ^ (n - 1) * ↑(β n (n - 1)) *
        deform_spec_k1 n (n - 1) * deform_spec_k1 n (2 * n - (n - 1))) := by ring
    rw [this]
    exact dvd_mul_of_dvd_left h_core _
  · -- i = n+1
    -- p | C(2n,n+1) (same as C(2n,n-1) by symmetry)
    have hp_dvd_choose : (p : ℤ) ∣ (Nat.choose (2 * n) (n + 1) : ℤ) := by
      have hsymm : Nat.choose (2 * n) (n + 1) = Nat.choose (2 * n) (n - 1) := by
        rw [← Nat.choose_symm (show n - 1 ≤ 2 * n from by omega)]
        congr 1; omega
      rw [hsymm]; push_cast
      -- Same proof as for n-1 case
      have hv := e_central_k1_val p hp5 n hn
      have : padicValNat p (Nat.choose (2 * n) (n - 1)) ≥ 1 := by
        have h_id := choose_identity n (by omega)
        have h_cn : padicValNat p (Nat.choose (2 * n) n) = 1 := by rwa [← e_central_k1_eq p n hn]
        have hvn : padicValNat p n = 0 := by
          rw [padicValNat.eq_zero_iff]; right; right
          exact p_not_dvd_n p hp_odd 1 (by omega) n (by rw [pow_one]; exact hn)
        have hvn1 : padicValNat p (n + 1) = 0 := by
          rw [padicValNat.eq_zero_iff]; right; right
          exact p_not_dvd_n1 p 1 (by omega) n (by rw [pow_one]; exact hn)
        have h_val_eq : padicValNat p (Nat.choose (2 * n) (n - 1) * (n + 1)) =
            padicValNat p (Nat.choose (2 * n) n * n) := congr_arg _ h_id
        rw [padicValNat.mul (by exact Nat.ne_of_gt (Nat.choose_pos (by omega))) (by omega),
            hvn1,
            padicValNat.mul (by exact Nat.ne_of_gt (Nat.choose_pos (by omega))) (by omega),
            h_cn, hvn] at h_val_eq
        omega
      have h := (padicValNat_dvd_iff_le (Nat.ne_of_gt (Nat.choose_pos (by omega)))).mpr this
      rw [pow_one] at h; exact_mod_cast h
    -- p | β(n,n+1) (contains (n+2)! = p!)
    have hp_dvd_β : (p : ℤ) ∣ (β n (n + 1) : ℤ) := by
      unfold β; rw [show 2 * n - (n + 1) = n - 1 from by omega,
                     show n + 1 + 1 = n + 2 from by omega]; push_cast
      exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr (p_dvd_factorial_n2 p n hn)) _
    rw [sq]
    have h_core : (p : ℤ) * (p : ℤ) ∣
      (Nat.choose (2 * n) (n + 1) : ℤ) * (β n (n + 1) : ℤ) :=
      mul_dvd_mul hp_dvd_choose hp_dvd_β
    have : (-1 : ℤ) ^ (n + 1) * ↑(Nat.choose (2 * n) (n + 1)) *
        ↑(α n (n + 1)) * ↑(β n (n + 1)) *
        deform_spec_k1 n (n + 1) * deform_spec_k1 n (2 * n - (n + 1)) =
      ((Nat.choose (2 * n) (n + 1) : ℤ) * (β n (n + 1) : ℤ)) *
      ((-1 : ℤ) ^ (n + 1) * ↑(α n (n + 1)) *
        deform_spec_k1 n (n + 1) * deform_spec_k1 n (2 * n - (n + 1))) := by ring
    rw [this]
    exact dvd_mul_of_dvd_left h_core _

private lemma correction_k1_dvd (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (hp5 : 5 ≤ p) (n : ℕ) (hn : n + 2 = p) (hn_pos : 1 ≤ n) :
    (p : ℤ) ^ (2 * e_central p n + 2) ∣
      ((u_val n) ^ 2 - A_eval n (deform_spec_k1 n) * C_eval n (deform_spec_k1 n)) := by
  have hn3 : 3 ≤ n := by omega
  have hsum := AC_sum_k1 n hn3
  rw [u_sq_minus_AC_eq_sq _ _ _ hsum]
  -- (A - u)² is divisible by p^(2e+2) since p^(e+1) | (A-u)
  have hdvd := A_minus_u_k1_dvd p hp_odd hp5 n hn hn_pos
  rw [show 2 * e_central p n + 2 = (e_central p n + 1) + (e_central p n + 1) from by omega,
      pow_add, sq]
  exact mul_dvd_mul hdvd hdvd

/-! ### Main proof of deformation_k_eq_1 -/

/-- For k = 1 (m = p ≥ 5): v_p(Δ) = 2e+1 under the k=1 specialization. -/
lemma deformation_k_eq_1 (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (hp5 : 5 ≤ p) (n : ℕ) (hn : n + 2 = p) (hn_pos : 1 ≤ n) :
    Δ_eval n (deform_spec_k1 n) ≠ 0 ∧
    padicValNat p (Int.natAbs (Δ_eval n (deform_spec_k1 n))) =
      2 * e_central p n + 1 := by
  set e := e_central p n with he_def
  -- Step 1: Decompose Δ = (B+2u)(B-2u) + 4(u²-AC)
  have hΔ_decomp : Δ_eval n (deform_spec_k1 n) =
      (B_eval n (deform_spec_k1 n) + 2 * u_val n) *
      (B_eval n (deform_spec_k1 n) - 2 * u_val n) +
      4 * ((u_val n) ^ 2 - A_eval n (deform_spec_k1 n) * C_eval n (deform_spec_k1 n)) := by
    unfold Δ_eval; ring
  -- Step 2: Bplus = B_center_excess + R_off, v_p(Bplus) = e
  have hBplus_eq : B_eval n (deform_spec_k1 n) + 2 * u_val n =
    B_center_excess_k1 n + R_off_k1 n := by
    rw [B_eval_k1_eq n hn_pos]; exact Bplus_k1_formula n (by omega)
  obtain ⟨hce_ne, hce_val⟩ := B_center_excess_k1_val p hp_odd hp5 n hn hn_pos
  have hR_dvd := R_off_k1_dvd p hp_odd hp5 n hn hn_pos
  obtain ⟨hBp_ne', hBp_val'⟩ :=
    padic_val_add_of_strict_lt p (B_center_excess_k1 n) (R_off_k1 n) e hce_ne hce_val hR_dvd
  have hBp_ne : B_eval n (deform_spec_k1 n) + 2 * u_val n ≠ 0 := hBplus_eq ▸ hBp_ne'
  have hBp_val : padicValNat p (Int.natAbs
      (B_eval n (deform_spec_k1 n) + 2 * u_val n)) = e := hBplus_eq ▸ hBp_val'
  -- Step 3: v_p(Bminus) = e+1
  obtain ⟨hBm_ne, hBm_val⟩ := Bminus_k1_val p hp_odd hp5 n hn hn_pos
  -- Step 4: v_p((B+2u)(B-2u)) = 2e+1
  have hBpBm_ne := mul_ne_zero hBp_ne hBm_ne
  have hBpBm_val : padicValNat p (Int.natAbs ((B_eval n (deform_spec_k1 n) + 2 * u_val n) *
      (B_eval n (deform_spec_k1 n) - 2 * u_val n))) = 2 * e + 1 := by
    rw [Int.natAbs_mul,
        padicValNat.mul (Int.natAbs_ne_zero.mpr hBp_ne) (Int.natAbs_ne_zero.mpr hBm_ne),
        hBp_val, hBm_val]; omega
  -- Step 5: v_p(4(u²-AC)) ≥ 2e+2
  have hcorr4_dvd : (p : ℤ) ^ (2 * e + 1 + 1) ∣
    4 * ((u_val n) ^ 2 - A_eval n (deform_spec_k1 n) * C_eval n (deform_spec_k1 n)) := by
    apply dvd_mul_of_dvd_right
    exact dvd_trans (pow_dvd_pow _ (by omega)) (correction_k1_dvd p hp_odd hp5 n hn hn_pos)
  -- Step 6: Apply ultrametric to get v_p(Δ) = 2e+1
  rw [hΔ_decomp]
  exact padic_val_add_of_strict_lt p
    ((B_eval n (deform_spec_k1 n) + 2 * u_val n) *
     (B_eval n (deform_spec_k1 n) - 2 * u_val n))
    (4 * ((u_val n) ^ 2 - A_eval n (deform_spec_k1 n) * C_eval n (deform_spec_k1 n)))
    (2 * e + 1) hBpBm_ne hBpBm_val hcorr4_dvd

end QuarticInvariant
