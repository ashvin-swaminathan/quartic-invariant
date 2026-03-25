import Mathlib
import Modular.Defs
import Modular.CentralDom
import Modular.ScalarBounds
import Modular.Rank1Collapse
import Modular.ContentBasics

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant

private lemma int_pow_dvd_natAbs {p : ℕ} {e : ℕ} {a : ℤ}
    (h : (p : ℤ) ^ e ∣ a) : p ^ e ∣ a.natAbs := by
  have := Int.natAbs_dvd_natAbs.mpr h
  simpa [Int.natAbs_pow, Int.natAbs_natCast] using this

/-! ## Scalar divisibility (general, no prime-power hypothesis) -/

/-! ## Coefficient divisibility for A_n and C_n (prime-power case) -/

/-- p^{e_central} divides every coefficient of A_n when n+2 = p^k and p is odd.
    Proof: A_n = Σ_i scalar_i · X_i · X_{2n-i}. Each coefficient of A_n at monomial m
    is a sum of scalar_i's (for matching i). Since p^e | scalar_i for each i
    (from scalar_dvd_pe / Legendre formula), p^e | the sum. -/
lemma coeff_A_n_dvd_odd (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    ∀ m, ((p ^ e_central p n : ℕ) : ℤ) ∣ (A_n n).coeff m := by
  -- Each scalar (-1)^i·C(2n,i)·α(n,i)·β(n,i) is divisible by p^{e_central}
  have h_scalar_div : ∀ i ∈ Finset.range (2 * n + 1),
      ((p ^ e_central p n : ℕ) : ℤ) ∣ ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
        (α n i : ℤ) * (β n i : ℤ)) := by
    intro i hi
    have hi' : i ≤ 2 * n := by
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h_dvd_nat : p ^ e_central p n ∣ scalar_AB n i := by
      by_cases hin : i = n
      · rw [hin]; exact p_pow_dvd_scalar_AB p n
      · have h_lt := scalar_AB_central_min p k hk n hn i hi' hin
        have h_eq : e_central p n = padicValNat p (scalar_AB n n) := e_central_eq p n
        rw [h_eq]
        exact dvd_trans (pow_dvd_pow p (by omega)) pow_padicValNat_dvd
    have h_dvd_int : ((p ^ e_central p n : ℕ) : ℤ) ∣ (scalar_AB n i : ℤ) :=
      Int.natCast_dvd_natCast.mpr h_dvd_nat
    convert h_dvd_int.mul_left ((-1 : ℤ) ^ i) using 1
    simp [scalar_AB]; push_cast; ring
  intro m
  unfold A_n
  have h_coeff_dvd : ∀ i ∈ Finset.range (2 * n + 1),
      ((p ^ e_central p n : ℕ) : ℤ) ∣ MvPolynomial.coeff m
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

/-- p^{e_central} divides every coefficient of C_n when n+2 = p^k and p is odd.
    Same proof as A_n since C_n has the same scalar coefficients. -/
lemma coeff_C_n_dvd_odd (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    ∀ m, ((p ^ e_central p n : ℕ) : ℤ) ∣ (C_n n).coeff m := by
  have h_scalar_div : ∀ i ∈ Finset.range (2 * n + 1),
      ((p ^ e_central p n : ℕ) : ℤ) ∣ ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
        (α n i : ℤ) * (β n i : ℤ)) := by
    intro i hi
    have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h_dvd_nat : p ^ e_central p n ∣ scalar_AB n i := by
      by_cases hin : i = n
      · rw [hin]; exact p_pow_dvd_scalar_AB p n
      · have h_lt := scalar_AB_central_min p k hk n hn i hi' hin
        rw [e_central_eq p n]
        exact dvd_trans (pow_dvd_pow p (by omega)) pow_padicValNat_dvd
    have h_dvd_int : ((p ^ e_central p n : ℕ) : ℤ) ∣ (scalar_AB n i : ℤ) :=
      Int.natCast_dvd_natCast.mpr h_dvd_nat
    convert h_dvd_int.mul_left ((-1 : ℤ) ^ i) using 1
    simp [scalar_AB]; push_cast; ring
  intro m
  unfold C_n
  have h_coeff_dvd : ∀ i ∈ Finset.range (2 * n + 1),
      ((p ^ e_central p n : ℕ) : ℤ) ∣ MvPolynomial.coeff m
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

/-! ## B_n coefficient divisibility in the prime-power case -/

/-- e_central ≤ v_p(|b_formula(n,j)|) for all j ∈ [1,2n] when n+2 = p^k.
    This follows from scalar_AB_central_min: the central scalar has MINIMUM v_p,
    and b_j = scalar_AB(n,j) * 2 * |2n+1-2j| / (j+1), so
    v_p(b_j) = v_p(scalar_AB(n,j)) + v_p(2|2n+1-2j|) - v_p(j+1)
    ≥ v_p(scalar_AB(n,n)) = e_central (the extra factors only help for odd p). -/
lemma b_formula_factored (n j : ℕ) (hj : j ≤ 2 * n) :
    b_formula n j = 2 * (-1 : ℤ) ^ j *
      (((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * j) *
       ((2 * n + 1 - j).factorial : ℤ) * (j.factorial : ℤ)) := by
  have hchoose_pos : (0 : ℤ) < (Nat.choose (2 * n) j : ℤ) := by
    exact_mod_cast Nat.choose_pos hj
  have hchoose_ne : (Nat.choose (2 * n) j : ℤ) ≠ 0 := hchoose_pos.ne'
  have h_choose_dvd : (Nat.choose (2 * n) j : ℤ) ∣
      2 * (-1 : ℤ) ^ j * ((2 * n).factorial : ℤ) ^ 2 *
      ((2 * n : ℤ) + 1 - j) * ((2 * n : ℤ) + 1 - 2 * j) := by
    have : (Nat.choose (2 * n) j : ℤ) ∣ ((2 * n).factorial : ℤ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj ▸
        dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
      (dvd_pow this two_ne_zero) _) _) _
  -- C(2n,j) * b_formula = numerator (from definition + ediv_mul_cancel)
  have h_cb : (Nat.choose (2 * n) j : ℤ) * b_formula n j =
      2 * (-1 : ℤ) ^ j * ((2 * n).factorial : ℤ) ^ 2 *
      ((2 * n : ℤ) + 1 - j) * ((2 * n : ℤ) + 1 - 2 * j) := by
    unfold b_formula
    rw [show (Nat.choose (2 * n) j : ℤ) * (2 * (-1 : ℤ) ^ j * ((2 * n).factorial : ℤ) ^ 2 *
      ((2 * n : ℤ) + 1 - j) * ((2 * n : ℤ) + 1 - 2 * j) / (Nat.choose (2 * n) j : ℤ)) =
      2 * (-1 : ℤ) ^ j * ((2 * n).factorial : ℤ) ^ 2 *
      ((2 * n : ℤ) + 1 - j) * ((2 * n : ℤ) + 1 - 2 * j) / (Nat.choose (2 * n) j : ℤ) *
      (Nat.choose (2 * n) j : ℤ) from by ring]
    rw [Int.ediv_mul_cancel h_choose_dvd]
  -- C(2n,j) * RHS = same numerator (algebraic identity)
  -- Prove by showing both sides equal when multiplied out
  have h_cr : (Nat.choose (2 * n) j : ℤ) * (2 * (-1 : ℤ) ^ j *
      (((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * j) *
       ((2 * n + 1 - j).factorial : ℤ) * (j.factorial : ℤ))) =
      2 * (-1 : ℤ) ^ j * ((2 * n).factorial : ℤ) ^ 2 *
      ((2 * n : ℤ) + 1 - j) * ((2 * n : ℤ) + 1 - 2 * j) := by
    -- (2n)! = C(2n,j) * j! * (2n-j)!
    have h1 : (Nat.choose (2 * n) j : ℤ) * (j.factorial : ℤ) * ((2 * n - j).factorial : ℤ) =
        ((2 * n).factorial : ℤ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
    -- (2n+1-j)! = (2n+1-j) * (2n-j)!
    have h2 : ((2 * n + 1 - j).factorial : ℤ) =
        ((2 * n + 1 - j : ℕ) : ℤ) * ((2 * n - j).factorial : ℤ) := by
      rw [show 2 * n + 1 - j = (2 * n - j) + 1 from by omega]
      push_cast [Nat.factorial_succ]; ring
    -- Cast (2n+1-j : ℕ) to ℤ
    have h3 : ((2 * n + 1 - j : ℕ) : ℤ) = (2 * n : ℤ) + 1 - j := by omega
    -- (2n)!^2 = C(2n,j)*j!*(2n-j)! * (2n)!
    have h1' : ((2 * n).factorial : ℤ) ^ 2 =
        (Nat.choose (2 * n) j : ℤ) * (j.factorial : ℤ) * ((2 * n - j).factorial : ℤ) *
        ((2 * n).factorial : ℤ) := by
      rw [sq]; nlinarith [h1]
    -- Substitute into RHS
    rw [h1', h2, h3]; ring
  -- Cancel C(2n,j) from both sides
  exact mul_left_cancel₀ hchoose_ne (h_cb.trans h_cr.symm)

private lemma e_central_le_vp_bk (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (2 * n)) :
    e_central p n ≤ padicValNat p (Int.natAbs (b_formula n j)) := by
  have hj2 : j ≤ 2 * n := (Finset.mem_Icc.mp hj).2
  have h_Bcoeff := B_coeff_dvd p k hk hp_odd n hn hn_pos j (by omega)
  have h_eq := b_formula_factored n j hj2
  have h_dvd : (p : ℤ) ^ e_central p n ∣ b_formula n j := by
    rw [h_eq]
    have : (p : ℤ) ^ e_central p n ∣
        ((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * j) *
         ((2 * n + 1 - j).factorial : ℤ) * (j.factorial : ℤ) := h_Bcoeff
    exact dvd_mul_of_dvd_right this _
  have h_dvd_nat : p ^ e_central p n ∣ Int.natAbs (b_formula n j) :=
    int_pow_dvd_natAbs h_dvd
  have hb : Int.natAbs (b_formula n j) ≠ 0 := by
    rw [Int.natAbs_ne_zero, h_eq]
    apply mul_ne_zero
    · apply mul_ne_zero; norm_num
      exact pow_ne_zero _ (by norm_num)
    · apply mul_ne_zero; apply mul_ne_zero; apply mul_ne_zero
      · exact_mod_cast Nat.factorial_pos _  |>.ne'
      · -- (2n+1-2j) might be 0 as integer? No: 2n+1 is odd and 2j is even
        -- But as ℤ, (2*n+1-2*j) could be negative but not zero
        -- Actually 2n+1-2j ≠ 0 since 2n+1 is odd
        omega
      · exact_mod_cast Nat.factorial_pos _ |>.ne'
      · exact_mod_cast Nat.factorial_pos _ |>.ne'
  exact (padicValNat_dvd_iff_le hb).mp h_dvd_nat

/-- p^{e_central} divides every coefficient of B_n in the prime-power case. -/
lemma coeff_B_n_dvd_prime_power (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    ∀ m, ((p ^ e_central p n : ℕ) : ℤ) ∣ (B_n n).coeff m := by
  apply coeff_B_n_dvd p n (e_central p n) (by omega)
  exact e_central_le_vp_bk p k hk hp_odd n hn hn_pos

/-! ## Eval-to-coeff transfer infrastructure -/

/-- The degree of X_j in a monomial product C(a) * X_i * X_k is at most 2. -/
private lemma degreeOf_C_mul_X_mul_X (a : ℤ) (i k j : ℕ) :
    (MvPolynomial.C a * MvPolynomial.X i * MvPolynomial.X k : MvPolynomial ℕ ℤ).degreeOf j ≤ 2 := by
  calc (MvPolynomial.C a * MvPolynomial.X i * MvPolynomial.X k).degreeOf j
      ≤ (MvPolynomial.C a * MvPolynomial.X i).degreeOf j + (MvPolynomial.X k).degreeOf j :=
        MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ ((MvPolynomial.C a).degreeOf j + (MvPolynomial.X i).degreeOf j) +
        (MvPolynomial.X k).degreeOf j :=
        Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) _
    _ ≤ (0 + 1) + 1 := by
        apply Nat.add_le_add
        · apply Nat.add_le_add
          · exact le_of_eq (MvPolynomial.degreeOf_C _ _)
          · simp only [MvPolynomial.degreeOf_X]; split <;> omega
        · simp only [MvPolynomial.degreeOf_X]; split <;> omega
    _ = 2 := by omega

/-- Each summand of A_n has degreeOf ≤ 2 in every variable. -/
private lemma degreeOf_A_n_summand (n i j : ℕ) :
    (MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ)) *
    MvPolynomial.X i * MvPolynomial.X (2 * n - i) : MvPolynomial ℕ ℤ).degreeOf j ≤ 2 :=
  degreeOf_C_mul_X_mul_X _ _ _ _

/-- degreeOf j (A_n n) ≤ 2 -/
lemma degreeOf_A_n_le (n j : ℕ) : (A_n n).degreeOf j ≤ 2 := by
  unfold A_n
  refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) ?_
  exact Finset.sup_le (fun i _ => degreeOf_A_n_summand n i j)

/-- Each summand of B_n has degreeOf ≤ 2 in every variable. -/
private lemma degreeOf_B_n_summand (n i j : ℕ) :
    (MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ)) *
    (MvPolynomial.C ((α n i : ℤ) ^ 2) *
      MvPolynomial.X i * MvPolynomial.X (2 * n + 1 - i) +
     MvPolynomial.C ((β n i : ℤ) ^ 2) *
      MvPolynomial.X (i + 1) * MvPolynomial.X (2 * n - i)) : MvPolynomial ℕ ℤ).degreeOf j ≤ 2 := by
  calc _ ≤ (MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ))).degreeOf j +
          (MvPolynomial.C ((α n i : ℤ) ^ 2) *
            MvPolynomial.X i * MvPolynomial.X (2 * n + 1 - i) +
           MvPolynomial.C ((β n i : ℤ) ^ 2) *
            MvPolynomial.X (i + 1) * MvPolynomial.X (2 * n - i)).degreeOf j :=
        MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ 0 + max ((MvPolynomial.C ((α n i : ℤ) ^ 2) *
            MvPolynomial.X i * MvPolynomial.X (2 * n + 1 - i)).degreeOf j)
          ((MvPolynomial.C ((β n i : ℤ) ^ 2) *
            MvPolynomial.X (i + 1) * MvPolynomial.X (2 * n - i)).degreeOf j) := by
        apply Nat.add_le_add
        · exact le_of_eq (MvPolynomial.degreeOf_C _ _)
        · exact MvPolynomial.degreeOf_add_le _ _ _
    _ ≤ 0 + max 2 2 := by
        apply Nat.add_le_add_left
        exact max_le_max (degreeOf_C_mul_X_mul_X _ _ _ _) (degreeOf_C_mul_X_mul_X _ _ _ _)
    _ = 2 := by omega

/-- degreeOf j (B_n n) ≤ 2 -/
lemma degreeOf_B_n_le (n j : ℕ) : (B_n n).degreeOf j ≤ 2 := by
  unfold B_n
  refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) ?_
  exact Finset.sup_le (fun i _ => degreeOf_B_n_summand n i j)

/-- Each summand of C_n has degreeOf ≤ 2 in every variable. -/
private lemma degreeOf_C_n_summand (n i j : ℕ) :
    (MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ)) *
    MvPolynomial.X (i + 1) * MvPolynomial.X (2 * n + 1 - i) : MvPolynomial ℕ ℤ).degreeOf j ≤ 2 :=
  degreeOf_C_mul_X_mul_X _ _ _ _

/-- degreeOf j (C_n n) ≤ 2 -/
lemma degreeOf_C_n_le (n j : ℕ) : (C_n n).degreeOf j ≤ 2 := by
  unfold C_n
  refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) ?_
  exact Finset.sup_le (fun i _ => degreeOf_C_n_summand n i j)

/-- degreeOf j (Δ_n n) ≤ 4 -/
lemma degreeOf_Δ_n_le (n j : ℕ) : (Δ_n n).degreeOf j ≤ 4 := by
  unfold Δ_n
  calc (B_n n ^ 2 - 4 * A_n n * C_n n).degreeOf j
      ≤ max ((B_n n ^ 2).degreeOf j) ((4 * A_n n * C_n n).degreeOf j) :=
        MvPolynomial.degreeOf_sub_le _ _ _
    _ ≤ max (2 * (B_n n).degreeOf j)
          ((4 : MvPolynomial ℕ ℤ).degreeOf j + (A_n n).degreeOf j + (C_n n).degreeOf j) := by
        apply max_le_max
        · exact MvPolynomial.degreeOf_pow_le _ _ _
        · calc (4 * A_n n * C_n n).degreeOf j
              ≤ (4 * A_n n).degreeOf j + (C_n n).degreeOf j :=
                MvPolynomial.degreeOf_mul_le _ _ _
            _ ≤ ((4 : MvPolynomial ℕ ℤ).degreeOf j + (A_n n).degreeOf j) + (C_n n).degreeOf j :=
                Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) _
    _ ≤ max (2 * 2) (0 + 2 + 2) := by
        apply max_le_max
        · exact Nat.mul_le_mul_left _ (degreeOf_B_n_le n j)
        · apply Nat.add_le_add
          · apply Nat.add_le_add
            · have : (4 : MvPolynomial ℕ ℤ) = MvPolynomial.C 4 := by simp [map_ofNat]
              rw [this]; exact le_of_eq (MvPolynomial.degreeOf_C _ _)
            · exact degreeOf_A_n_le n j
          · exact degreeOf_C_n_le n j
    _ = 4 := by omega

/-- Quotient polynomial: divide each coefficient by d.
    Well-defined when d divides every coefficient. -/
private noncomputable def mvPolyDiv (f : MvPolynomial ℕ ℤ) (d : ℤ) : MvPolynomial ℕ ℤ :=
  f.support.sum (fun m => MvPolynomial.monomial m (f.coeff m / d))

/-- The quotient polynomial has the expected coefficients on support. -/
private lemma mvPolyDiv_coeff_of_mem (f : MvPolynomial ℕ ℤ) (d : ℤ) (hd : d ≠ 0)
    (hdvd : ∀ m, d ∣ f.coeff m) (m : ℕ →₀ ℕ) (hm : m ∈ f.support) :
    (mvPolyDiv f d).coeff m = f.coeff m / d := by
  have key : (mvPolyDiv f d).coeff m =
      ∑ m' ∈ f.support, MvPolynomial.coeff m (MvPolynomial.monomial m' (f.coeff m' / d)) :=
    MvPolynomial.coeff_sum f.support _ m
  rw [key, Finset.sum_eq_single m]
  · simp [MvPolynomial.coeff_monomial]
  · intro b _ hbm; simp [MvPolynomial.coeff_monomial, hbm]
  · intro habs; exact absurd hm habs

/-- The quotient polynomial has zero coefficients off support. -/
private lemma mvPolyDiv_coeff_of_not_mem (f : MvPolynomial ℕ ℤ) (d : ℤ)
    (m : ℕ →₀ ℕ) (hm : m ∉ f.support) :
    (mvPolyDiv f d).coeff m = 0 := by
  have key : (mvPolyDiv f d).coeff m =
      ∑ m' ∈ f.support, MvPolynomial.coeff m (MvPolynomial.monomial m' (f.coeff m' / d)) :=
    MvPolynomial.coeff_sum f.support _ m
  rw [key]
  apply Finset.sum_eq_zero
  intro b hb
  simp only [MvPolynomial.coeff_monomial]
  split
  · next heq => rw [heq] at hb; exact absurd hb hm
  · rfl

/-- f = C(d) * mvPolyDiv f d when d divides every coefficient. -/
private lemma mul_mvPolyDiv_eq (f : MvPolynomial ℕ ℤ) (d : ℤ) (hd : d ≠ 0)
    (hdvd : ∀ m, d ∣ f.coeff m) :
    MvPolynomial.C d * mvPolyDiv f d = f := by
  ext m
  rw [MvPolynomial.coeff_C_mul]
  by_cases hm : m ∈ f.support
  · rw [mvPolyDiv_coeff_of_mem f d hd hdvd m hm, mul_comm]
    exact Int.ediv_mul_cancel (hdvd m)
  · rw [mvPolyDiv_coeff_of_not_mem f d m hm, mul_zero]
    exact (MvPolynomial.notMem_support_iff.mp hm).symm

/-- Support of the quotient polynomial is contained in support of f. -/
private lemma mvPolyDiv_support_subset (f : MvPolynomial ℕ ℤ) (d : ℤ) :
    (mvPolyDiv f d).support ⊆ f.support := by
  intro m hm
  by_contra h
  have h1 := mvPolyDiv_coeff_of_not_mem f d m h
  have h2 := MvPolynomial.mem_support_iff.mp hm
  exact h2 h1

/-- degreeOf of the quotient polynomial is bounded by degreeOf of f. -/
private lemma degreeOf_mvPolyDiv_le (f : MvPolynomial ℕ ℤ) (d : ℤ) (j : ℕ) :
    (mvPolyDiv f d).degreeOf j ≤ f.degreeOf j := by
  simp only [MvPolynomial.degreeOf_eq_sup]
  exact Finset.sup_mono (mvPolyDiv_support_subset f d)

/-- A polynomial over ZMod p that vanishes on all of (ZMod p)^ℕ and has degreeOf < p
    in every variable is zero. Uses the combinatorial Nullstellensatz. -/
private lemma MvPolynomial_ZMod_vanish (p : ℕ) [hp : Fact p.Prime]
    (f : MvPolynomial ℕ (ZMod p))
    (hdeg : ∀ i, f.degreeOf i < p)
    (heval : ∀ c : ℕ → ZMod p, MvPolynomial.eval c f = 0) :
    f = 0 := by
  -- Rename to finitely many variables
  obtain ⟨k, g, hg_inj, q, hfq⟩ := MvPolynomial.exists_fin_rename f
  -- q : MvPolynomial (Fin k) (ZMod p) with f = rename g q
  -- Show q = 0 using eq_zero_of_eval_zero_at_prod_finset
  suffices hq : q = 0 by rw [hfq, hq, map_zero]
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset q (fun _ => Finset.univ)
  · intro i
    simp only [Finset.card_univ, ZMod.card]
    rw [← MvPolynomial.degreeOf_rename_of_injective hg_inj i]
    rw [← hfq]
    exact hdeg (g i)
  · intro x _
    -- f = rename g q, so eval c (rename g q) = eval (c ∘ g) q
    -- Choose c : ℕ → ZMod p extending x along g
    let c : ℕ → ZMod p := fun j =>
      if h : ∃ i, g i = j then x (h.choose) else 0
    have hcg : c ∘ g = x := by
      ext i
      simp only [Function.comp_apply, c]
      have : ∃ i', g i' = g i := ⟨i, rfl⟩
      rw [dif_pos this]
      congr 1
      exact hg_inj this.choose_spec
    have : MvPolynomial.eval x q = MvPolynomial.eval c f := by
      rw [hfq, MvPolynomial.eval_rename, hcg]
    rw [this]
    exact heval c

/-- Transfer: if (p : ℤ) divides eval c f for all c : ℕ → ℤ, and degreeOf < p,
    then p divides every coefficient of f. -/
private lemma coeff_dvd_of_eval_dvd (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (f : MvPolynomial ℕ ℤ)
    (hdeg : ∀ i, f.degreeOf i < p)
    (heval : ∀ c : ℕ → ℤ, (p : ℤ) ∣ MvPolynomial.eval c f) :
    ∀ m, (p : ℤ) ∣ f.coeff m := by
  -- Map f to MvPolynomial ℕ (ZMod p) via the canonical map π : ℤ →+* ZMod p
  -- Show map π f = 0, then extract coefficient divisibility.
  suffices h : MvPolynomial.map (Int.castRingHom (ZMod p)) f = 0 by
    intro m
    have := congr_arg (MvPolynomial.coeff m) h
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, Int.coe_castRingHom] at this
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  -- Show map π f vanishes on all of (ZMod p)^ℕ
  apply MvPolynomial_ZMod_vanish p
  · -- Degree bound
    intro i
    calc (MvPolynomial.map (Int.castRingHom (ZMod p)) f).degreeOf i
        ≤ f.degreeOf i := by
          simp only [MvPolynomial.degreeOf_eq_sup]
          exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
      _ < p := hdeg i
  · -- Eval vanishing
    intro c
    haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
    -- Lift c : ℕ → ZMod p to c' : ℕ → ℤ
    set c' : ℕ → ℤ := fun i => (ZMod.val (c i) : ℤ) with hc'_def
    -- c = π ∘ c' where π = Int.castRingHom (ZMod p)
    have hcc' : c = (Int.castRingHom (ZMod p)) ∘ c' := by
      ext i; simp only [Function.comp_apply, hc'_def, Int.coe_castRingHom,
        Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [MvPolynomial.eval_map, hcc', ← MvPolynomial.eval₂_comp, Int.coe_castRingHom]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (heval c')

/-! ## Full coefficient divisibility of Δ_n (prime-power case) -/

/-- In the prime-power case, p^{2e+1} divides every coefficient of Δ_n.

    Step 1: p^e divides every coefficient of A_n, B_n, C_n
      (from coeff_A_n_dvd_odd, coeff_B_n_dvd_prime_power, coeff_C_n_dvd_odd)
    Step 2: p^{2e} divides every coefficient of Δ_n (from coeff_Δ_n_dvd_sq)
    Step 3: The extra factor of p comes from rank-1 collapse at eval level +
      transfer from eval to coeff. -/
lemma coeff_Δ_n_dvd_prime_power (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) :
    ∀ m ∈ (Δ_n n).support,
      p ^ (2 * e_central p n + 1) ∣ Int.natAbs ((Δ_n n).coeff m) := by
  have hp_odd : p ≠ 2 := by omega
  -- Step 1-2: p^{2e} | every coefficient
  have hA := coeff_A_n_dvd_odd p k hk hp_odd n hn hn_pos
  have hB := coeff_B_n_dvd_prime_power p k hk hp_odd n hn hn_pos
  have hC := coeff_C_n_dvd_odd p k hk hp_odd n hn hn_pos
  have h_2e := coeff_Δ_n_dvd_sq p n (e_central p n) hA hB hC
  -- Step 3: upgrade from p^{2e} to p^{2e+1}
  set e := e_central p n
  set d := (p ^ (2 * e) : ℤ) with hd_def
  have hd_ne : d ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))
  -- Coerce h_2e: d | every coefficient of Δ_n
  have h_2e_int : ∀ m, d ∣ (Δ_n n).coeff m := by
    intro m; exact_mod_cast h_2e m
  -- Build the quotient polynomial
  set f_sharp := mvPolyDiv (Δ_n n) d
  -- rank1_collapse gives p^{2e+1} | eval c (Δ_n n) for all c
  have h_eval_Δ : ∀ c : ℕ → ℤ, (p : ℤ) ^ (2 * e + 1) ∣
      MvPolynomial.eval c (Δ_n n) := by
    intro c; rw [eval_Δ_eq_Δ_eval]; exact rank1_collapse p k hk hp_odd n hn hn_pos c
  -- So p | eval c f_sharp for all c
  have h_eval_sharp : ∀ c : ℕ → ℤ, (p : ℤ) ∣ MvPolynomial.eval c f_sharp := by
    intro c
    have hΔ := mul_mvPolyDiv_eq (Δ_n n) d hd_ne h_2e_int
    have h1 := h_eval_Δ c
    rw [← hΔ] at h1
    simp only [map_mul, MvPolynomial.eval_C] at h1
    rw [show (p : ℤ) ^ (2 * e + 1) = d * (p : ℤ) from by
      rw [hd_def]; push_cast; ring] at h1
    exact (mul_dvd_mul_iff_left hd_ne).mp h1
  -- degreeOf bound for f_sharp
  have h_deg_sharp : ∀ i, (f_sharp).degreeOf i < p := by
    intro i
    calc f_sharp.degreeOf i ≤ (Δ_n n).degreeOf i := degreeOf_mvPolyDiv_le _ _ _
      _ ≤ 4 := degreeOf_Δ_n_le n i
      _ < p := by omega
  -- Apply eval-to-coeff transfer
  have h_p_dvd_coeff_sharp : ∀ m, (p : ℤ) ∣ f_sharp.coeff m :=
    coeff_dvd_of_eval_dvd p hp5 f_sharp h_deg_sharp h_eval_sharp
  -- Conclude: p^{2e+1} | coeff m of Δ_n
  intro m hm
  have h_dvd_int : (p : ℤ) ^ (2 * e + 1) ∣ (Δ_n n).coeff m := by
    rw [show (p : ℤ) ^ (2 * e + 1) = d * (p : ℤ) from by
      rw [hd_def]; push_cast; ring]
    have h1 := h_2e_int m
    obtain ⟨q, hq⟩ := h1
    rw [hq]
    apply mul_dvd_mul_left
    have : q = f_sharp.coeff m := by
      rw [mvPolyDiv_coeff_of_mem (Δ_n n) d hd_ne h_2e_int m hm]
      rw [hq, Int.mul_ediv_cancel_left _ hd_ne]
    rw [this]
    exact h_p_dvd_coeff_sharp m
  rw [show (p : ℤ) ^ (2 * e + 1) = ((p ^ (2 * e + 1) : ℕ) : ℤ) from by push_cast; ring] at h_dvd_int
  exact Int.natCast_dvd.mp h_dvd_int

end QuarticInvariant
