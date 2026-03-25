import Mathlib
import Modular.Defs
import Modular.CentralDom
import Modular.CoeffDivPP
import Modular.Rank1Collapse
import Modular.P2CRS
import Modular.P2CarryMax
import Modular.P2Step5

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant

/-! ## Coefficient divisibility for A_n and C_n when p = 2 -/

/-- 2^{e_central} divides every coefficient of A_n when n+2 = 2^K.
    Proof: same as coeff_A_n_dvd_odd — each scalar (-1)^i·C(2n,i)·α·β is
    divisible by p^e via scalar_AB_central_min (no prime constraint) and
    p_pow_dvd_scalar_AB. -/
lemma coeff_A_n_dvd_p2 (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = 2 ^ k) (hn_pos : 1 ≤ n) :
    ∀ m, ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ (A_n n).coeff m := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_scalar_div : ∀ i ∈ Finset.range (2 * n + 1),
      ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
        (α n i : ℤ) * (β n i : ℤ)) := by
    intro i hi
    have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h_dvd_nat : 2 ^ e_central 2 n ∣ scalar_AB n i := by
      by_cases hin : i = n
      · rw [hin]; exact p_pow_dvd_scalar_AB 2 n
      · have h_lt := scalar_AB_central_min 2 k hk n hn i hi' hin
        have h_eq : e_central 2 n = padicValNat 2 (scalar_AB n n) := e_central_eq 2 n
        rw [h_eq]
        exact dvd_trans (pow_dvd_pow 2 (by omega)) pow_padicValNat_dvd
    have h_dvd_int : ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ (scalar_AB n i : ℤ) :=
      Int.natCast_dvd_natCast.mpr h_dvd_nat
    convert h_dvd_int.mul_left ((-1 : ℤ) ^ i) using 1
    simp [scalar_AB]; ring
  intro m
  unfold A_n
  have h_coeff_dvd : ∀ i ∈ Finset.range (2 * n + 1),
      ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ MvPolynomial.coeff m
        (MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
          (α n i : ℤ) * (β n i : ℤ)) *
        MvPolynomial.X i * MvPolynomial.X (2 * n - i)) := by
    intro i hi
    have h_div := h_scalar_div i hi
    generalize_proofs at *
    rw [MvPolynomial.coeff_mul]
    refine Finset.dvd_sum fun x _ => ?_
    erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']
    aesop
  erw [MvPolynomial.coeff_sum]
  exact Finset.dvd_sum fun x hx => h_coeff_dvd x hx

/-- 2^{e_central} divides every coefficient of C_n when n+2 = 2^K.
    Same proof as A_n since C_n has the same scalar coefficients. -/
lemma coeff_C_n_dvd_p2 (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = 2 ^ k) (hn_pos : 1 ≤ n) :
    ∀ m, ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ (C_n n).coeff m := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_scalar_div : ∀ i ∈ Finset.range (2 * n + 1),
      ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
        (α n i : ℤ) * (β n i : ℤ)) := by
    intro i hi
    have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h_dvd_nat : 2 ^ e_central 2 n ∣ scalar_AB n i := by
      by_cases hin : i = n
      · rw [hin]; exact p_pow_dvd_scalar_AB 2 n
      · have h_lt := scalar_AB_central_min 2 k hk n hn i hi' hin
        rw [e_central_eq 2 n]
        exact dvd_trans (pow_dvd_pow 2 (by omega)) pow_padicValNat_dvd
    have h_dvd_int : ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ (scalar_AB n i : ℤ) :=
      Int.natCast_dvd_natCast.mpr h_dvd_nat
    convert h_dvd_int.mul_left ((-1 : ℤ) ^ i) using 1
    simp [scalar_AB]; ring
  intro m
  unfold C_n
  have h_coeff_dvd : ∀ i ∈ Finset.range (2 * n + 1),
      ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ MvPolynomial.coeff m
        (MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
          (α n i : ℤ) * (β n i : ℤ)) *
        MvPolynomial.X (i + 1) * MvPolynomial.X (2 * n + 1 - i)) := by
    intro i hi
    have h_div := h_scalar_div i hi
    generalize_proofs at *
    rw [MvPolynomial.coeff_mul]
    refine Finset.dvd_sum fun x _ => ?_
    erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']
    aesop
  erw [MvPolynomial.coeff_sum]
  exact Finset.dvd_sum fun x hx => h_coeff_dvd x hx

/-! ## Rank-1 witnesses (reused from MainP3 definitions) -/

/-- The rank-1 witness for A_n/p^e: μ · X_n². -/
private def p2_r1_a (n : ℕ) (μ : ℤ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.C μ * MvPolynomial.X n * MvPolynomial.X n

/-- The rank-1 witness for C_n/p^e: μ · X_{n+1}². -/
private def p2_r1_c (n : ℕ) (μ : ℤ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.C μ * MvPolynomial.X (n + 1) * MvPolynomial.X (n + 1)

/-! ## Coefficient congruences: A_n/2^e ≡ λ·X_n² (mod 2) -/

/-- A_n/2^e ≡ μ·X_n² (mod 2) when n+2 = 2^K, where μ = (-1)^n · scalar_AB(n,n)/2^e. -/
theorem A_n_coeff_cong_p2 (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = 2 ^ k) (hn_pos : 1 ≤ n) (μ : ℤ)
    (hμ : μ = (-1 : ℤ) ^ n * ↑(scalar_AB n n / 2 ^ e_central 2 n)) :
    ∀ m, (2 : ℤ) ∣ ((A_n n).coeff m / ((2 ^ e_central 2 n : ℕ) : ℤ) - (p2_r1_a n μ).coeff m) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  set e := e_central 2 n
  set d := ((2 ^ e : ℕ) : ℤ)
  intro m
  have hd_ne : d ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
  have hd_dvd : d ∣ (A_n n).coeff m := coeff_A_n_dvd_p2 k hk n hn hn_pos m
  suffices h : d * (2 : ℤ) ∣ ((A_n n).coeff m - d * (p2_r1_a n μ).coeff m) by
    obtain ⟨q, hq⟩ := hd_dvd
    have hq' : (A_n n).coeff m / d = q := by rw [hq, Int.mul_ediv_cancel_left _ hd_ne]
    rw [hq']
    rw [hq, show d * q - d * (p2_r1_a n μ).coeff m = d * (q - (p2_r1_a n μ).coeff m) from by ring] at h
    exact (mul_dvd_mul_iff_left hd_ne).mp h
  -- A_n = Σ_i s_i · X_i · X_{2n-i}, with s_i = (-1)^i · scalar_AB(n,i)
  have hn_mem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  -- The central scalar satisfies d * μ = (-1)^n * scalar_AB(n,n)
  have h_dmu : d * μ = (-1 : ℤ) ^ n * (scalar_AB n n : ℤ) := by
    rw [hμ]
    have h_dvd_nat : 2 ^ e ∣ scalar_AB n n := p_pow_dvd_scalar_AB 2 n
    have h_factor : (scalar_AB n n : ℤ) = d * ↑(scalar_AB n n / 2 ^ e) := by
      rw [show d = ((2 ^ e : ℕ) : ℤ) from rfl]
      push_cast
      exact_mod_cast (Nat.mul_div_cancel' h_dvd_nat).symm
    rw [h_factor]; ring
  -- The i=n summand of A_n equals d * r1_a as polynomials
  have h_central_term :
      MvPolynomial.C ((-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
        (α n n : ℤ) * (β n n : ℤ)) *
      MvPolynomial.X n * MvPolynomial.X (2 * n - n) =
      MvPolynomial.C d * (p2_r1_a n μ) := by
    simp only [p2_r1_a, show 2 * n - n = n from by omega]
    rw [show MvPolynomial.C d * (MvPolynomial.C μ * MvPolynomial.X n * MvPolynomial.X n) =
      MvPolynomial.C (d * μ) * MvPolynomial.X n * MvPolynomial.X n from by
      rw [map_mul]; ring]
    congr 1; congr 1
    rw [h_dmu]
    push_cast [scalar_AB, α, β]; ring
  -- A_n.coeff m = central_term.coeff m + Σ_{i≠n} term_i.coeff m
  set term := fun i => MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ)) *
      MvPolynomial.X i * MvPolynomial.X (2 * n - i) with hterm_def
  have h_A_eq : A_n n = ∑ i ∈ Finset.range (2 * n + 1), term i := by
    unfold A_n; congr
  have h_A_split : (A_n n).coeff m =
      (term n).coeff m +
      ∑ i ∈ (Finset.range (2 * n + 1)).erase n, (term i).coeff m := by
    rw [h_A_eq]
    erw [MvPolynomial.coeff_sum]
    exact (Finset.add_sum_erase (f := fun i => (term i).coeff m) _ hn_mem).symm
  have h_central_coeff : (term n).coeff m = d * (p2_r1_a n μ).coeff m := by
    show (MvPolynomial.C ((-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
        (α n n : ℤ) * (β n n : ℤ)) *
      MvPolynomial.X n * MvPolynomial.X (2 * n - n)).coeff m = d * (p2_r1_a n μ).coeff m
    rw [h_central_term, MvPolynomial.coeff_C_mul]
  have h_diff : (A_n n).coeff m - d * (p2_r1_a n μ).coeff m =
      ∑ i ∈ (Finset.range (2 * n + 1)).erase n, (term i).coeff m := by
    rw [h_A_split, h_central_coeff]; ring
  -- Each i≠n summand has d * 2 | its coefficient
  rw [h_diff]
  apply Finset.dvd_sum
  intro i hi
  have hi_range := (Finset.mem_erase.mp hi).2
  have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
  have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_range)
  -- v_2(scalar_AB(n,i)) > e, so 2^{e+1} | scalar_AB(n,i)
  have h_vp : padicValNat 2 (scalar_AB n i) > e := by
    rw [show e = padicValNat 2 (scalar_AB n n) from e_central_eq 2 n]
    exact scalar_AB_central_min 2 k hk n hn i hi_le hi_ne
  have h_dvd_scalar : (2 ^ (e + 1) : ℕ) ∣ scalar_AB n i :=
    dvd_trans (pow_dvd_pow 2 h_vp) pow_padicValNat_dvd
  have h_dvd_signed : d * (2 : ℤ) ∣ ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ)) := by
    have : d * (2 : ℤ) = ((2 ^ (e + 1) : ℕ) : ℤ) := by
      simp only [d]; push_cast; ring
    rw [this]
    have h_int : ((2 ^ (e + 1) : ℕ) : ℤ) ∣ (scalar_AB n i : ℤ) :=
      Int.natCast_dvd_natCast.mpr h_dvd_scalar
    convert h_int.mul_left ((-1 : ℤ) ^ i) using 1
    simp [scalar_AB]; ring
  -- Extract the coefficient of term i
  show d * (2 : ℤ) ∣ (term i).coeff m
  simp only [hterm_def]
  rw [MvPolynomial.coeff_mul]
  apply Finset.dvd_sum
  intro x _
  erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_left h_dvd_signed _

/-- C_n/2^e ≡ μ·X_{n+1}² (mod 2) when n+2 = 2^K. -/
theorem C_n_coeff_cong_p2 (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = 2 ^ k) (hn_pos : 1 ≤ n) (μ : ℤ)
    (hμ : μ = (-1 : ℤ) ^ n * ↑(scalar_AB n n / 2 ^ e_central 2 n)) :
    ∀ m, (2 : ℤ) ∣ ((C_n n).coeff m / ((2 ^ e_central 2 n : ℕ) : ℤ) - (p2_r1_c n μ).coeff m) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  set e := e_central 2 n
  set d := ((2 ^ e : ℕ) : ℤ)
  intro m
  have hd_ne : d ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
  have hd_dvd : d ∣ (C_n n).coeff m := coeff_C_n_dvd_p2 k hk n hn hn_pos m
  suffices h : d * (2 : ℤ) ∣ ((C_n n).coeff m - d * (p2_r1_c n μ).coeff m) by
    obtain ⟨q, hq⟩ := hd_dvd
    have hq' : (C_n n).coeff m / d = q := by rw [hq, Int.mul_ediv_cancel_left _ hd_ne]
    rw [hq']
    rw [hq, show d * q - d * (p2_r1_c n μ).coeff m = d * (q - (p2_r1_c n μ).coeff m) from by ring] at h
    exact (mul_dvd_mul_iff_left hd_ne).mp h
  have hn_mem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  have h_dmu : d * μ = (-1 : ℤ) ^ n * (scalar_AB n n : ℤ) := by
    rw [hμ]
    have h_dvd_nat : 2 ^ e ∣ scalar_AB n n := p_pow_dvd_scalar_AB 2 n
    have h_factor : (scalar_AB n n : ℤ) = d * ↑(scalar_AB n n / 2 ^ e) := by
      rw [show d = ((2 ^ e : ℕ) : ℤ) from rfl]
      push_cast
      exact_mod_cast (Nat.mul_div_cancel' h_dvd_nat).symm
    rw [h_factor]; ring
  have h_central_term :
      MvPolynomial.C ((-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
        (α n n : ℤ) * (β n n : ℤ)) *
      MvPolynomial.X (n + 1) * MvPolynomial.X (2 * n + 1 - n) =
      MvPolynomial.C d * (p2_r1_c n μ) := by
    simp only [p2_r1_c, show 2 * n + 1 - n = n + 1 from by omega]
    rw [show MvPolynomial.C d * (MvPolynomial.C μ * MvPolynomial.X (n + 1) * MvPolynomial.X (n + 1)) =
      MvPolynomial.C (d * μ) * MvPolynomial.X (n + 1) * MvPolynomial.X (n + 1) from by
      rw [map_mul]; ring]
    congr 1; congr 1
    rw [h_dmu]
    push_cast [scalar_AB, α, β]; ring
  set cterm := fun i => MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ)) *
      MvPolynomial.X (i + 1) * MvPolynomial.X (2 * n + 1 - i) with hcterm_def
  have h_C_eq : C_n n = ∑ i ∈ Finset.range (2 * n + 1), cterm i := by unfold C_n; congr
  have h_C_split : (C_n n).coeff m =
      (cterm n).coeff m +
      ∑ i ∈ (Finset.range (2 * n + 1)).erase n, (cterm i).coeff m := by
    rw [h_C_eq]
    erw [MvPolynomial.coeff_sum]
    exact (Finset.add_sum_erase (f := fun i => (cterm i).coeff m) _ hn_mem).symm
  have h_central_coeff : (cterm n).coeff m = d * (p2_r1_c n μ).coeff m := by
    show (MvPolynomial.C ((-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
        (α n n : ℤ) * (β n n : ℤ)) *
      MvPolynomial.X (n + 1) * MvPolynomial.X (2 * n + 1 - n)).coeff m = d * (p2_r1_c n μ).coeff m
    rw [h_central_term, MvPolynomial.coeff_C_mul]
  have h_diff : (C_n n).coeff m - d * (p2_r1_c n μ).coeff m =
      ∑ i ∈ (Finset.range (2 * n + 1)).erase n, (cterm i).coeff m := by
    rw [h_C_split, h_central_coeff]; ring
  rw [h_diff]
  apply Finset.dvd_sum
  intro i hi
  have hi_range := (Finset.mem_erase.mp hi).2
  have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
  have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_range)
  have h_vp : padicValNat 2 (scalar_AB n i) > e := by
    rw [show e = padicValNat 2 (scalar_AB n n) from e_central_eq 2 n]
    exact scalar_AB_central_min 2 k hk n hn i hi_le hi_ne
  have h_dvd_scalar : (2 ^ (e + 1) : ℕ) ∣ scalar_AB n i :=
    dvd_trans (pow_dvd_pow 2 h_vp) pow_padicValNat_dvd
  have h_dvd_signed : d * (2 : ℤ) ∣ ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ)) := by
    have : d * (2 : ℤ) = ((2 ^ (e + 1) : ℕ) : ℤ) := by simp only [d]; push_cast; ring
    rw [this]
    have h_int : ((2 ^ (e + 1) : ℕ) : ℤ) ∣ (scalar_AB n i : ℤ) :=
      Int.natCast_dvd_natCast.mpr h_dvd_scalar
    convert h_int.mul_left ((-1 : ℤ) ^ i) using 1
    simp [scalar_AB]; ring
  show d * (2 : ℤ) ∣ (cterm i).coeff m
  simp only [hcterm_def]
  rw [MvPolynomial.coeff_mul]
  apply Finset.dvd_sum
  intro x _
  erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_left h_dvd_signed _

/-! ## B_n off-center coefficient divisibility for p = 2 -/

/-- The exact remaining combinatorial input behind `B_sharp_even_p2`.

    In the power-of-two case, the off-center `B_n` coefficients are even
    after dividing by `2^(e_central 2 n + 1)` because the corresponding
    `b_formula(n,j)` valuations are strictly larger than the center.

    The only genuinely new input needed here is the power-of-two
    strict-max theorem for `padicValNat 2 (Nat.choose (2*n+1) j)`.
    Once `P2CarryMax` exports that theorem, this lemma should collapse to
    a one-line `have h_choose := ...; simpa [v2_b_formula_eq, v2_b_center]`.
    -/
private lemma b_formula_offcenter_gt_center_p2_of_choose
    (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = 2 ^ k) (hn_pos : 1 ≤ n)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j < n)
    (h_choose :
      padicValNat 2 (Nat.choose (2 * n + 1) j) <
        padicValNat 2 (Nat.choose (2 * n + 1) n)) :
    padicValNat 2 (Int.natAbs (b_formula n j)) >
      padicValNat 2 (Int.natAbs (b_formula n n)) := by
  have hj2 : j ≤ 2 * n := by omega
  have hn2 : n ≤ 2 * n := by omega
  have hk2 : 2 ≤ k := by
    cases k with
    | zero =>
        simp at hn
    | succ k =>
        cases k with
        | zero =>
            have : n = 0 := by
              omega
            omega
        | succ k =>
            omega
  have h_j := v2_b_formula_eq n j hn_pos hj1 hj2
  have h_n := v2_b_formula_eq n n hn_pos (by omega : 1 ≤ n) hn2
  have h_center_pos : 1 ≤ padicValNat 2 (Int.natAbs (b_formula n n)) := by
    rw [v2_b_center k hk2 n hn]
    omega
  have h_choose_center_bound :
      padicValNat 2 (Nat.choose (2 * n + 1) n) <
        1 + padicValNat 2 (2 * n).factorial + padicValNat 2 (2 * n + 1).factorial := by
    have h := h_n
    omega
  have h_choose_off_bound :
      padicValNat 2 (Nat.choose (2 * n + 1) j) <
        1 + padicValNat 2 (2 * n).factorial + padicValNat 2 (2 * n + 1).factorial := by
    exact lt_trans h_choose h_choose_center_bound
  rw [h_j, h_n]
  exact Nat.sub_lt_sub_left h_choose_off_bound h_choose

/-- The exact remaining combinatorial input behind `B_sharp_even_p2`.

    This is the statement that should become a short import-and-apply step
    once `P2CarryMax` exports the power-of-two strict-max theorem. -/
private lemma b_formula_offcenter_gt_center_p2 (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = 2 ^ k) (hn_pos : 1 ≤ n)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j < n) :
    padicValNat 2 (Int.natAbs (b_formula n j)) >
      padicValNat 2 (Int.natAbs (b_formula n n)) := by
  have hk2 : 2 ≤ k := by
    cases k with
    | zero => simp at hn
    | succ k => cases k with
      | zero => omega
      | succ k => omega
  have h_choose := choose_center_strict_max_pow2 n k hk2 hn j hj
  exact b_formula_offcenter_gt_center_p2_of_choose k hk n hn hn_pos j hj1 hj h_choose

theorem B_sharp_even_p2 (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = 2 ^ k) (hn_pos : 1 ≤ n)
    (m : ℕ →₀ ℕ)
    (hm : m ≠ Finsupp.single n 1 + Finsupp.single (n + 1) 1) :
    (2 : ℤ) ∣ (B_n n).coeff m / ((2 ^ (e_central 2 n + 1) : ℕ) : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  set e := e_central 2 n
  set d := ((2 ^ (e + 1) : ℕ) : ℤ)
  have hd_ne : d ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
  have hk2 : 2 ≤ k := by
    cases k with
    | zero => simp at hn
    | succ k => cases k with
      | zero => omega
      | succ k => omega
  -- It suffices to show 2^{e+2} | (B_n n).coeff m for off-center m
  suffices h_dvd_e2 : ((2 ^ (e + 2) : ℕ) : ℤ) ∣ (B_n n).coeff m by
    have hd2 : ((2 ^ (e + 2) : ℕ) : ℤ) = d * 2 := by simp only [d]; push_cast; ring
    rw [hd2] at h_dvd_e2
    have h_dvd_d : d ∣ (B_n n).coeff m := dvd_trans (dvd_mul_right d 2) h_dvd_e2
    obtain ⟨q, hq⟩ := h_dvd_d
    rw [hq, Int.mul_ediv_cancel_left _ hd_ne]
    rw [hq] at h_dvd_e2
    exact (mul_dvd_mul_iff_left hd_ne).mp h_dvd_e2
  -- Rewrite B_n = B_n_alt
  rw [B_n_eq_alt n (by omega)]
  -- B_n_alt = boundary + Σ_{j ∈ Icc 1 n} b_formula(n,j) · X_j · X_{2n+1-j}
  -- For off-center m, the j=n term contributes 0, so only boundary + off-center terms
  -- All off-center scalars are divisible by 2^{e+2}
  unfold B_n_alt
  -- Coefficient of (f + g) = coeff f + coeff g
  rw [MvPolynomial.coeff_add]
  apply dvd_add
  · -- Boundary term: 2^{e+2} | coefficient of 2*((2n+1)!)² * X_0 * X_{2n+1} at m
    have h_bdy_scalar_dvd : ((2 ^ (e + 2) : ℕ) : ℤ) ∣ (2 * ((2 * n + 1).factorial : ℤ) ^ 2) := by
      -- v₂(2*((2n+1)!)²) = 1 + 2*v₂((2n)!) ≥ e + 2
      -- since e = v₂((2n)!) + 2*v₂(n!) and v₂(C(2n,n)) = v₂((2n)!) - 2*v₂(n!) ≥ 1
      have h_n_succ_odd : ¬ (2 ∣ (n + 1)) := n_succ_odd k hk2 n hn
      have h_v2_n1 : padicValNat 2 (n + 1) = 0 :=
        padicValNat.eq_zero_of_not_dvd h_n_succ_odd
      have h_v2_n1_fact : padicValNat 2 (n + 1).factorial = padicValNat 2 n.factorial := by
        rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_pos _).ne',
            h_v2_n1, zero_add]
      -- C(2n,n) is even for n ≥ 1
      have h_choose_even : 2 ∣ Nat.choose (2 * n) n := by
        -- C(2n, n) = C(2n-1, n-1) + C(2n-1, n) and C(2n-1, n-1) = C(2n-1, n)
        -- so C(2n, n) = 2 * C(2n-1, n)
        have h1 : Nat.choose (2 * n) n = Nat.choose (2 * n - 1) (n - 1) + Nat.choose (2 * n - 1) n := by
          have := Nat.choose_succ_succ (2 * n - 1) (n - 1)
          simp only [Nat.succ_eq_add_one] at this
          rwa [show n - 1 + 1 = n from by omega, show 2 * n - 1 + 1 = 2 * n from by omega] at this
        have h2 : Nat.choose (2 * n - 1) (n - 1) = Nat.choose (2 * n - 1) n := by
          have h_symm := Nat.choose_symm (show n - 1 ≤ 2 * n - 1 by omega)
          rw [show 2 * n - 1 - (n - 1) = n from by omega] at h_symm
          exact h_symm.symm
        rw [h1, h2, ← two_mul]; exact dvd_mul_right 2 _
      have h_v2_choose : 1 ≤ padicValNat 2 (Nat.choose (2 * n) n) := by
        have h_ne := (Nat.choose_pos (by omega : n ≤ 2 * n)).ne'
        exact (padicValNat_dvd_iff_le h_ne).mp h_choose_even
      have h_dvd_fact : n.factorial * n.factorial ∣ (2 * n).factorial := by
        have := Nat.factorial_mul_factorial_dvd_factorial (show n ≤ 2 * n by omega)
        rwa [show 2 * n - n = n from by omega] at this
      have h_v2_choose_add : padicValNat 2 (Nat.choose (2 * n) n) +
          padicValNat 2 n.factorial + padicValNat 2 n.factorial =
          padicValNat 2 (2 * n).factorial := by
        have h_eq : Nat.choose (2 * n) n * (n.factorial * n.factorial) = (2 * n).factorial := by
          have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
          rw [show 2 * n - n = n from by omega] at this
          rw [mul_assoc] at this; exact this
        have h_v1 : padicValNat 2 n.factorial + padicValNat 2 n.factorial =
            padicValNat 2 (n.factorial * n.factorial) :=
          (padicValNat.mul (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne').symm
        have h_v2 : padicValNat 2 (Nat.choose (2 * n) n) +
            padicValNat 2 (n.factorial * n.factorial) =
            padicValNat 2 (Nat.choose (2 * n) n * (n.factorial * n.factorial)) :=
          (padicValNat.mul (Nat.choose_pos (by omega)).ne'
            (mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')).symm
        rw [add_assoc, h_v1, h_v2, h_eq]
      -- Compute v₂ of the boundary
      have h_bdy_val : e + 2 ≤ padicValNat 2 (Int.natAbs (2 * ((2 * n + 1).factorial : ℤ) ^ 2)) := by
        rw [show Int.natAbs (2 * ((2 * n + 1).factorial : ℤ) ^ 2) =
            2 * (2 * n + 1).factorial ^ 2 from by
          simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]]
        rw [show (2 * n + 1).factorial = (2 * n + 1) * (2 * n).factorial from
          Nat.factorial_succ (2 * n)]
        rw [show 2 * ((2 * n + 1) * (2 * n).factorial) ^ 2 =
            2 * (2 * n + 1) ^ 2 * (2 * n).factorial ^ 2 from by ring]
        have h_odd : ¬ (2 ∣ (2 * n + 1) ^ 2) := by
          intro h
          have h2 : 2 ∣ 2 * n + 1 := by
            rw [sq] at h; exact (Nat.prime_two.dvd_mul.mp h).elim id id
          omega
        rw [padicValNat.mul (by positivity) (by positivity),
            padicValNat.mul (by norm_num) (by positivity),
            padicValNat.eq_zero_of_not_dvd h_odd, add_zero,
            padicValNat.pow 2 ((2 * n).factorial_pos).ne',
            show padicValNat 2 2 = 1 from by native_decide]
        rw [show e = e_central 2 n from rfl, e_central_eq 2 n,
            scalar_AB_formula n n (by omega),
            show 2 * n + 1 - n = n + 1 from by omega,
            padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
            padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
            h_v2_n1_fact]
        -- Goal: 1 + 2*v₂((2n)!) ≥ v₂((2n)!) + v₂(n!) + v₂(n!) + 2
        -- i.e., v₂((2n)!) - 2*v₂(n!) ≥ 1, i.e., v₂(C(2n,n)) ≥ 1
        -- From h_v2_choose_eq and h_v2_choose
        have h_ge : padicValNat 2 (2 * n).factorial ≥ 2 * padicValNat 2 n.factorial + 1 := by
          linarith [h_v2_choose_add, h_v2_choose]
        omega
      exact_mod_cast dvd_trans (Nat.pow_dvd_pow 2 h_bdy_val) pow_padicValNat_dvd
    -- Extract coefficient of C(s) * X_0 * X_{2n+1} at m
    rw [MvPolynomial.coeff_mul]
    apply Finset.dvd_sum
    intro x _
    erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']
    apply dvd_mul_of_dvd_left
    exact dvd_mul_of_dvd_left h_bdy_scalar_dvd _
  · -- Sum term: Σ_{j ∈ Icc 1 n} b_formula(n,j) * X_j * X_{2n+1-j}
    erw [MvPolynomial.coeff_sum]
    apply Finset.dvd_sum
    intro j hj
    have hj_bounds := Finset.mem_Icc.mp hj
    -- Each term: C(b_formula n j) * X_j * X_{2n+1-j}
    -- For j = n: the monomial is X_n * X_{n+1} = single n 1 + single (n+1) 1
    -- which equals the excluded monomial, so we need to show the coefficient at m is 0
    -- For j < n: b_formula_offcenter_gt_center_p2 gives v₂ > e+1, so 2^{e+2} | b_formula
    by_cases hjn : j = n
    · -- j = n: coefficient at off-center m is 0
      rw [hjn, show 2 * n + 1 - n = n + 1 from by omega]
      rw [MvPolynomial.coeff_mul]
      apply Finset.dvd_sum
      intro x hx_mem
      erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']
      -- The product of indicators is 0 unless m = single n 1 + single (n+1) 1
      by_cases hx1 : Finsupp.single n 1 = x.1
      · by_cases hx2 : Finsupp.single (n + 1) 1 = x.2
        · -- x = (single n 1, single (n+1) 1), so x.1 + x.2 = m, contradicting hm
          exfalso; apply hm
          have hx_anti := (Finset.mem_antidiagonal.mp hx_mem)
          rw [← hx_anti, ← hx1, ← hx2]
        · simp only [hx2, ↓reduceIte]; ring_nf; exact dvd_zero _
      · simp only [hx1, ↓reduceIte]; ring_nf; exact dvd_zero _
    · -- j < n: off-center, so 2^{e+2} | b_formula(n,j)
      have hj_lt : j < n := lt_of_le_of_ne hj_bounds.2 hjn
      have h_vp : padicValNat 2 (Int.natAbs (b_formula n j)) > e + 1 := by
        have h_center := v2_b_center k hk2 n hn
        have h_off := b_formula_offcenter_gt_center_p2 k hk n hn hn_pos j hj_bounds.1 hj_lt
        rw [h_center] at h_off
        rw [show e = e_central 2 n from rfl, e_central_eq 2 n]
        omega
      have h_dvd_b : ((2 ^ (e + 2) : ℕ) : ℤ) ∣ b_formula n j := by
        have h_le : e + 2 ≤ padicValNat 2 (Int.natAbs (b_formula n j)) := by omega
        have h_nat : 2 ^ (e + 2) ∣ Int.natAbs (b_formula n j) :=
          dvd_trans (Nat.pow_dvd_pow 2 h_le) pow_padicValNat_dvd
        exact Int.natCast_dvd.mpr h_nat
      rw [MvPolynomial.coeff_mul]
      apply Finset.dvd_sum
      intro x _
      erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']
      apply dvd_mul_of_dvd_left
      exact dvd_mul_of_dvd_left h_dvd_b _

end QuarticInvariant
