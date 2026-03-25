import Mathlib
import Modular.Defs
import Modular.Deformation
import Modular.Rank1Collapse

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant


/-! ## Proved: A_eval and C_eval for k ≥ 2 -/

lemma A_eval_deform_k_ge_2 (n t : ℕ) (ht : 2 ≤ t) (htn : t + 2 ≤ n) :
    A_eval n (deform_spec n t) = u_val n := by
  unfold A_eval u_val deform_spec
  rw [Finset.sum_eq_single n] <;> norm_num
  · rw [if_pos (Nat.sub_eq_of_eq_add <| by ring)]; unfold α β γ; ring
    rw [show 1 + n * 2 - n = n + 1 by rw [Nat.sub_eq_of_eq_add]; ring,
        show n * 2 - n = n by rw [Nat.sub_eq_of_eq_add]; ring]; push_cast; ring
  · intros b hb hb'; split_ifs <;> norm_num <;> omega
  · intros; linarith

lemma C_eval_deform_k_ge_2 (n t : ℕ) (ht : 2 ≤ t) (htn : t + 2 ≤ n) :
    C_eval n (deform_spec n t) = u_val n := by
  unfold C_eval u_val deform_spec
  rw [Finset.sum_eq_single n]
  · simp +decide [two_mul, add_assoc, α, β, γ]; ring
  · grind +ring
  · exact fun h => False.elim <| h <| Finset.mem_range.mpr <| by linarith

/-! ## Proved: u_val properties -/

lemma u_val_padic_val (p n : ℕ) [Fact p.Prime] (hn : 1 ≤ n) :
    u_val n ≠ 0 ∧
    padicValNat p (Int.natAbs (u_val n)) = e_central p n := by
  unfold u_val e_central
  norm_num [Int.natAbs_mul, Int.natAbs_pow]
  exact ⟨Nat.ne_of_gt <| Nat.choose_pos <| by linarith,
         Nat.ne_of_gt <| Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)⟩

/-! ## Proved: Simple product valuation -/

lemma val_product_eq (p : ℕ) [Fact p.Prime]
    (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (e : ℕ)
    (hva : padicValNat p (Int.natAbs a) = e)
    (hvb : padicValNat p (Int.natAbs b) = e + 1) :
    a * b ≠ 0 ∧
    padicValNat p (Int.natAbs (a * b)) = 2 * e + 1 := by
  simp_all +decide [Int.natAbs_mul, padicValNat.mul]; linarith

/-! ## Hard remaining lemmas -/

/-- For k ≥ 2, the discriminant at deform_spec has v_p = 2e+1.

Proof sketch: Since A = C = u (proved above), Δ = (B+2u)(B-2u).
B+2u has v_p = e: the central terms give 2*(-1)^n*γ²*C(2n,n+1)
  with v_p = e (using v_p(C(2n,n+1)) = v_p(C(2n,n)) since n/(n+1) has v_p=0).
  Off-center terms have v_p ≥ e+1 so don't affect the minimum.
B-2u has v_p = e+1: the central part is (-1)^{n+1}*2*γ²*C(2n,n)*p^k/(n+1)
  with v_p = e+k ≥ e+2. The off-center terms have v_p = e+1 (by Kummer).
  So off-center dominates giving v_p = e+1.
Therefore v_p(Δ) = e + (e+1) = 2e+1. -/
-- Main theorem

theorem deformation_valuation (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 1 ≤ k) (hp5_if_k1 : k = 1 → 5 ≤ p)
    (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    let e := e_central p n
    let c := if k = 1 then deform_spec_k1 n else deform_spec n (p ^ (k - 1))
    Δ_eval n c ≠ 0 ∧
    padicValNat p (Int.natAbs (Δ_eval n c)) = 2 * e + 1 := by
  simp only
  split_ifs with hk1
  · -- k = 1 case
    subst hk1; simp only [pow_one] at hn
    exact deformation_k_eq_1 p hp_odd (hp5_if_k1 rfl) n hn hn_pos
  · -- k ≥ 2 case: Δ = (B+2u)(B-2u) with v_p = e and e+1
    have hk2 : 2 ≤ k := by omega
    have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
    have ht_ge_2 : 2 ≤ p ^ (k - 1) :=
      le_trans (by omega : 2 ≤ p) (Nat.le_self_pow (by omega) p)
    have ht_n : p ^ (k - 1) + 2 ≤ n := by
      have h1 : p ^ k = p * p ^ (k - 1) := by
        cases k with | zero => omega | succ k => simp [pow_succ, mul_comm]
      have h2 : p * p ^ (k - 1) ≥ 3 * p ^ (k - 1) := Nat.mul_le_mul_right _ hp3
      have h3 : 3 * p ^ (k - 1) ≥ 3 * 2 := by
        apply Nat.mul_le_mul_left
        calc 2 ≤ p := by omega
          _ ≤ p ^ (k - 1) := Nat.le_self_pow (by omega) p
      omega
    have hA := A_eval_deform_k_ge_2 n (p ^ (k - 1)) ht_ge_2 ht_n
    have hC := C_eval_deform_k_ge_2 n (p ^ (k - 1)) ht_ge_2 ht_n
    obtain ⟨hBp_ne, hBm_ne, hBp_val, hBm_val⟩ :=
      B_vals_k_ge_2 p hp_odd k hk2 n hn hn_pos
    have hΔ_eq : Δ_eval n (deform_spec n (p ^ (k - 1))) =
        (B_eval n (deform_spec n (p ^ (k - 1))) + 2 * u_val n) *
        (B_eval n (deform_spec n (p ^ (k - 1))) - 2 * u_val n) := by
      unfold Δ_eval; rw [hA, hC]; unfold u_val; ring
    rw [hΔ_eq]
    exact val_product_eq p
      (B_eval n (deform_spec n (p ^ (k - 1))) + 2 * u_val n)
      (B_eval n (deform_spec n (p ^ (k - 1))) - 2 * u_val n)
      hBp_ne hBm_ne (e_central p n) hBp_val hBm_val




/-! ======== Main Theorem Assembly ======== -/


/-! ## Bridge lemmas -/

/-- b_formula and b_k_val have the same definition. -/
lemma b_formula_eq_b_k_val (n k : ℕ) : b_formula n k = b_k_val n k := rfl

/-- The deformation_valuation wrapped as an existential. -/
lemma deformation_valuation_exists (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 1 ≤ k) (hp5_if_k1 : k = 1 → 5 ≤ p)
    (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    ∃ c : ℕ → ℤ,
      Δ_eval n c ≠ 0 ∧
      padicValNat p (Int.natAbs (Δ_eval n c)) = 2 * e_central p n + 1 :=
  ⟨_, deformation_valuation p hp_odd k hk hp5_if_k1 n hn hn_pos⟩

end QuarticInvariant
