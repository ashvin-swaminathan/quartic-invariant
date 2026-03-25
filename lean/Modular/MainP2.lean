import Mathlib
import Modular.Defs
import Modular.ContentBasics
import Modular.PairSpec
import Modular.ScalarBounds
import Modular.CentralDom
import Modular.MainP5
import Modular.Mod4Lift
import Modular.CoeffCongP2
import Modular.GaussMV
import Modular.CaseB
import Modular.P2Step5
import Modular.P2CaseB

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## Step 1: Define G = B/2

Since every coefficient of B_n is even (the b_k formula has an explicit
factor of 2), we define G = B/2 as a polynomial with integer coefficients.
-/

/-- G_poly n is B_n / 2 as an integer polynomial.
    Every coefficient of B_n is divisible by 2 (the leading factor in b_k_val),
    so dividing each coefficient by 2 stays in ℤ[x₀,…]. -/
private def G_poly (n : ℕ) : MvPolynomial ℕ ℤ :=
  Finsupp.mapRange (· / 2) (by simp) (B_n n)

@[simp]
private lemma G_poly_coeff (n : ℕ) (m : ℕ →₀ ℕ) :
    (G_poly n).coeff m = (B_n n).coeff m / 2 :=
  Finsupp.mapRange_apply (hf := by simp)

/-- Every coefficient of B_n is divisible by 2. -/
private lemma two_dvd_B_n_coeff (n : ℕ) :
    ∀ m, (2 : ℤ) ∣ (B_n n).coeff m := by
  by_cases hn : n = 0
  · -- n = 0: B_0 = sum over range 1 = single term with i=0
    subst hn; intro m; unfold B_n
    erw [Finset.sum_range_one]
    -- The single term has coefficient involving α(0,0)^2 and β(0,0)^2
    -- α(0,0) = 1! * 0! = 1, β(0,0) = 0! * 1! = 1
    -- Term = C(1) * (C(1) * X_0 * X_1 + C(1) * X_1 * X_0) = 2 * C(1) * X_0 * X_1 coeffwise
    have : (MvPolynomial.C ((-1 : ℤ) ^ 0 * (Nat.choose (2 * 0) 0 : ℤ)) *
      (MvPolynomial.C ((α 0 0 : ℤ) ^ 2) * MvPolynomial.X 0 * MvPolynomial.X (2 * 0 + 1 - 0) +
       MvPolynomial.C ((β 0 0 : ℤ) ^ 2) * MvPolynomial.X (0 + 1) * MvPolynomial.X (2 * 0 - 0))) =
      MvPolynomial.C 2 * (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial ℕ ℤ) := by
      simp [α, β, Nat.factorial]; ring
    rw [this, MvPolynomial.coeff_C_mul]
    exact dvd_mul_right 2 _
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    -- Use coeff_B_n_dvd with p=2, e=1
    have h_vp : ∀ k ∈ Finset.Icc 1 (2 * n),
        1 ≤ padicValNat 2 (Int.natAbs (b_formula n k)) := by
      intro k hk
      have hk2 : k ≤ 2 * n := (Finset.mem_Icc.mp hk).2
      -- b_formula_factored: b_formula n k = 2 * (-1)^k * (stuff)
      -- So 2 | b_formula n k, hence padicValNat 2 |b_formula n k| ≥ 1
      have h_factored := b_formula_factored n k hk2
      have h_dvd : (2 : ℤ) ∣ b_formula n k := by
        rw [h_factored]
        exact dvd_mul_of_dvd_left (dvd_mul_right (2 : ℤ) ((-1 : ℤ) ^ k)) _
      have h_ne : b_formula n k ≠ 0 := by
        rw [h_factored]
        apply mul_ne_zero
        · apply mul_ne_zero; norm_num
          exact pow_ne_zero _ (by norm_num)
        · apply mul_ne_zero; apply mul_ne_zero; apply mul_ne_zero
          · exact_mod_cast (Nat.factorial_pos _).ne'
          · omega
          · exact_mod_cast (Nat.factorial_pos _).ne'
          · exact_mod_cast (Nat.factorial_pos _).ne'
      rw [← Int.natAbs_dvd_natAbs] at h_dvd
      simp at h_dvd
      exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr h_ne)).mp h_dvd
    have h_cast : ((2 ^ 1 : ℕ) : ℤ) = (2 : ℤ) := by norm_num
    intro m
    have := coeff_B_n_dvd 2 n 1 hn' h_vp m
    rwa [h_cast] at this

/-- B_n = 2 * G_poly n as polynomials. -/
private lemma B_eq_two_G (n : ℕ) : B_n n = 2 * G_poly n := by
  have h2 : (2 : MvPolynomial ℕ ℤ) = MvPolynomial.C 2 := by simp [map_ofNat]
  ext m
  rw [h2, MvPolynomial.coeff_C_mul, G_poly_coeff]
  exact (Int.mul_ediv_cancel' (two_dvd_B_n_coeff n m)).symm

/-! ## Step 2: Δ = 4(G² - AC)

From B = 2G we get B² = 4G², so Δ = B² - 4AC = 4G² - 4AC = 4(G² - AC).
-/

/-- The "half-discriminant" H = G² - AC. -/
private def H_poly (n : ℕ) : MvPolynomial ℕ ℤ :=
  G_poly n ^ 2 - A_n n * C_n n

/-- Δ_n = 4 * (G² - AC). -/
private lemma Delta_eq_four_H (n : ℕ) :
    Δ_n n = 4 * H_poly n := by
  unfold Δ_n H_poly
  rw [B_eq_two_G]
  ring

/-- content(Δ_n) = 4 * content(G² - AC), i.e. content(4f) = 4 * content(f). -/
private lemma content_Delta_eq (n : ℕ) :
    mvContent (Δ_n n) = 4 * mvContent (H_poly n) := by
  rw [Delta_eq_four_H]
  -- content(4 * f) = |4| * content(f) by mvContent_C_mul from GaussMV
  have h4 : (4 : MvPolynomial ℕ ℤ) = MvPolynomial.C 4 := by simp [map_ofNat]
  rw [show (4 : MvPolynomial ℕ ℤ) * H_poly n = MvPolynomial.C (4 : ℤ) * H_poly n from by rw [← h4]]
  rw [mvContent_C_mul]
  norm_num

/-! ## Step 3: Gauss's lemma consequences

By Gauss's lemma for multivariate polynomials, content(fg) = content(f) * content(g).
This gives content(G²) = content(G)² and content(AC) = content(A) * content(C).
-/

/-- content(G²) = content(G)² by Gauss's lemma. -/
private lemma content_G_sq (n : ℕ) :
    mvContent (G_poly n ^ 2) = mvContent (G_poly n) ^ 2 := by
  rw [sq, mvContent_mul, sq]

/-- content(A_n) = content(C_n). This follows from the symmetry
    A_n(f₀,…,f_{2n+1}) = C_n(f_{2n+1},…,f₀) under variable reversal. -/
private lemma mvContent_rename (f : ℕ → ℕ) (hf : Function.Injective f)
    (p : MvPolynomial ℕ ℤ) :
    mvContent (MvPolynomial.rename f p) = mvContent p := by
  unfold mvContent
  rw [MvPolynomial.support_rename_of_injective hf]
  rw [Finset.gcd_image]
  congr 1
  ext d
  simp [Function.comp, MvPolynomial.coeff_rename_mapDomain f hf]

private lemma content_A_eq_C (n : ℕ) :
    mvContent (A_n n) = mvContent (C_n n) := by
  -- C_n n = MvPolynomial.rename (· + 1) (A_n n), and rename by an injective
  -- function preserves content.
  have h_rename : C_n n = MvPolynomial.rename (· + 1) (A_n n) := by
    unfold A_n C_n
    simp only [map_sum, MvPolynomial.rename_C, MvPolynomial.rename_X, map_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    congr 2
    omega
  rw [h_rename, mvContent_rename _ (fun a b h => by omega)]

/-- content(A_n * C_n) = content(A_n)² by Gauss + content_A_eq_C. -/
private lemma content_AC (n : ℕ) :
    mvContent (A_n n * C_n n) = mvContent (A_n n) ^ 2 := by
  rw [mvContent_mul, content_A_eq_C, sq]

/-! ## Step 4: v₂(S) = 2 + v₂(content(H))

From content_Delta_eq: S(n) = 4 * content(H).
So v₂(S) = 2 + v₂(content(H)).
To show v₂(S) is even, it suffices to show v₂(content(H)) is even.
-/

private lemma vp2_S_eq (n : ℕ) (hH : mvContent (H_poly n) ≠ 0) :
    padicValNat 2 (S n) = 2 + padicValNat 2 (mvContent (H_poly n)) := by
  unfold S
  rw [content_Delta_eq]
  rw [padicValNat.mul (by norm_num) (by exact hH)]
  have : padicValNat 2 4 = 2 := by native_decide
  omega

/-! ## Step 5: Ultrametric analysis for content

H = G² - AC. By the ultrametric property for content (or direct analysis),
if v₂(content(G²)) ≠ v₂(content(AC)), then
v₂(content(H)) = min(v₂(content(G²)), v₂(content(AC))),
which is min of two even numbers (from Steps 3), hence even.

If v₂(content(G²)) = v₂(content(AC)), i.e. content(G)² and content(A)²
have the same 2-adic valuation (which means v₂(content(G)) = v₂(content(A))),
then we need the mod-4 analysis from the paper.
-/

/-- In Case A (unequal valuations), v₂(content(H)) is even.
    When v₂(content(G²)) ≠ v₂(content(AC)), the ultrametric
    property gives v₂(content(H)) = min of two even numbers. -/
-- Helper: if d | every coeff of f, then d | mvContent f
private lemma dvd_mvContent_of_dvd_coeffs (d : ℕ) (f : MvPolynomial ℕ ℤ)
    (h : ∀ m, (d : ℤ) ∣ f.coeff m) :
    d ∣ mvContent f := by
  unfold mvContent
  apply Finset.dvd_gcd
  intro m _
  exact Int.natAbs_dvd_natAbs.mpr (h m)

-- Helper: content(f - g) is divisible by gcd(content(f), content(g))
private lemma gcd_content_dvd_content_sub (f g : MvPolynomial ℕ ℤ) :
    Nat.gcd (mvContent f) (mvContent g) ∣ mvContent (f - g) := by
  apply dvd_mvContent_of_dvd_coeffs
  intro m
  rw [MvPolynomial.coeff_sub]
  apply dvd_sub
  · exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) (mvContent_dvd_coeff f m)
  · exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)) (mvContent_dvd_coeff g m)

private lemma even_vp_H_of_neq_val (n : ℕ)
    (hne : padicValNat 2 (mvContent (G_poly n ^ 2)) ≠
           padicValNat 2 (mvContent (A_n n * C_n n)))
    (hH : mvContent (H_poly n) ≠ 0) :
    Even (padicValNat 2 (mvContent (H_poly n))) := by
  -- Both v_2(content(G^2)) and v_2(content(AC)) are even
  have ha_even : Even (padicValNat 2 (mvContent (G_poly n ^ 2))) := by
    rw [content_G_sq, sq]
    by_cases h0 : mvContent (G_poly n) = 0
    · simp [h0]
    · exact ⟨_, padicValNat.mul h0 h0⟩
  have hb_even : Even (padicValNat 2 (mvContent (A_n n * C_n n))) := by
    rw [content_AC, sq]
    by_cases h0 : mvContent (A_n n) = 0
    · simp [h0]
    · exact ⟨_, padicValNat.mul h0 h0⟩
  -- Edge cases: if G^2 = 0 then H = -AC, content(H) = content(AC), v_2(content(H)) = b even
  by_cases hg0 : G_poly n ^ 2 = 0
  · have hcH : mvContent (H_poly n) = mvContent (A_n n * C_n n) := by
      have : H_poly n = -(A_n n * C_n n) := by unfold H_poly; rw [hg0]; ring
      rw [this]; unfold mvContent; congr 1
      · ext m; simp [MvPolynomial.support_neg]
      · ext m; simp [MvPolynomial.coeff_neg, Int.natAbs_neg]
    rw [hcH]; exact hb_even
  by_cases hac0 : A_n n * C_n n = 0
  · have : H_poly n = G_poly n ^ 2 := by unfold H_poly; rw [hac0]; ring
    rw [show mvContent (H_poly n) = mvContent (G_poly n ^ 2) from by rw [this]]; exact ha_even
  have hG2_ne : mvContent (G_poly n ^ 2) ≠ 0 := by rwa [ne_eq, mvContent_eq_zero_iff]
  have hAC_ne : mvContent (A_n n * C_n n) ≠ 0 := by rwa [ne_eq, mvContent_eq_zero_iff]
  -- Let c = min(a,b), which is even. Show v_2(content(H)) = c.
  set a := padicValNat 2 (mvContent (G_poly n ^ 2))
  set b := padicValNat 2 (mvContent (A_n n * C_n n))
  set c := min a b
  have hc_even : Even c := by
    simp only [c, min_def]; split_ifs <;> assumption
  -- The gap: since a ≠ b and both even, min and max differ by ≥ 2
  have hgap : c + 2 ≤ max a b := by
    obtain ⟨k, hk⟩ := ha_even; obtain ⟨j, hj⟩ := hb_even
    simp only [c]; omega
  -- Lower bound: c ≤ v₂(content(H))
  have h_lower : c ≤ padicValNat 2 (mvContent (H_poly n)) := by
    have hc_dvd_G2 : 2 ^ c ∣ mvContent (G_poly n ^ 2) :=
      dvd_trans (Nat.pow_dvd_pow 2 (min_le_left a b)) pow_padicValNat_dvd
    have hc_dvd_AC : 2 ^ c ∣ mvContent (A_n n * C_n n) :=
      dvd_trans (Nat.pow_dvd_pow 2 (min_le_right a b)) pow_padicValNat_dvd
    exact (padicValNat_dvd_iff_le hH).mp
      (dvd_trans (Nat.dvd_gcd hc_dvd_G2 hc_dvd_AC) (gcd_content_dvd_content_sub _ _))
  -- Upper bound: v₂(content(H)) ≤ c
  -- If v₂(content(H)) ≥ c+1, then 2^{c+1} | H and 2^{c+1} | (the one with larger v₂),
  -- so 2^{c+1} | (the one with smaller v₂), contradicting v₂ = c.
  have h_upper : padicValNat 2 (mvContent (H_poly n)) ≤ c := by
    by_contra h_contra
    push_neg at h_contra
    have h_dvd_H : 2 ^ (c + 1) ∣ mvContent (H_poly n) :=
      (padicValNat_dvd_iff_le hH).mpr (by omega)
    -- 2^{c+1} | the one with larger v₂ (since max ≥ c+2 > c+1)
    have h_dvd_G2 : 2 ^ (c + 1) ∣ mvContent (G_poly n ^ 2) := by
      by_cases hab : a ≤ b
      · -- a = c, b is larger. G^2 = H + AC.
        -- 2^{c+1} | H (above) and 2^{c+1} | AC (since b ≥ c+2 > c+1)
        have h_dvd_AC : 2 ^ (c + 1) ∣ mvContent (A_n n * C_n n) :=
          dvd_trans (Nat.pow_dvd_pow 2 (by simp [c, hab]; omega)) pow_padicValNat_dvd
        exact dvd_mvContent_of_dvd_coeffs _ _ (fun m => by
          have : G_poly n ^ 2 = H_poly n + A_n n * C_n n := by unfold H_poly; ring
          rw [this, MvPolynomial.coeff_add]
          exact dvd_add
            (dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd_H) (mvContent_dvd_coeff _ m))
            (dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd_AC) (mvContent_dvd_coeff _ m)))
      · -- b < a, so c = b, a is larger. 2^{c+1} | G^2 since a ≥ c+2
        push_neg at hab
        exact dvd_trans (Nat.pow_dvd_pow 2 (by simp [c]; omega)) pow_padicValNat_dvd
    have h_dvd_AC : 2 ^ (c + 1) ∣ mvContent (A_n n * C_n n) := by
      by_cases hab : b ≤ a
      · have h_dvd_G2' : 2 ^ (c + 1) ∣ mvContent (G_poly n ^ 2) :=
          dvd_trans (Nat.pow_dvd_pow 2 (by simp [c, hab]; omega)) pow_padicValNat_dvd
        exact dvd_mvContent_of_dvd_coeffs _ _ (fun m => by
          have : A_n n * C_n n = G_poly n ^ 2 - H_poly n := by unfold H_poly; ring
          rw [this, MvPolynomial.coeff_sub]
          exact dvd_sub
            (dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd_G2') (mvContent_dvd_coeff _ m))
            (dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd_H) (mvContent_dvd_coeff _ m)))
      · push_neg at hab
        exact dvd_trans (Nat.pow_dvd_pow 2 (by simp [c]; omega)) pow_padicValNat_dvd
    -- Now 2^{c+1} | both, but c = min(a,b), so 2^{c+1} ∤ the smaller one
    rcases le_total a b with hab | hab
    · -- c = a, contradiction with hG2_ne
      exact absurd ((padicValNat_dvd_iff_le hG2_ne).mp h_dvd_G2) (by simp [c, hab]; omega)
    · -- c = b, contradiction with hAC_ne
      exact absurd ((padicValNat_dvd_iff_le hAC_ne).mp h_dvd_AC) (by simp [c, hab]; omega)
  exact (le_antisymm h_upper h_lower) ▸ hc_even

/-! ## Steps 5–7: Case A characterization + Case B + Conclusion
   These are implemented in P2Step5.lean and P2CaseB.lean.
   The final theorem assembles everything. -/
/-! ## Base case -/

/-- v₂(S(1)) is even. Direct computation. -/
private theorem even_vp_S_one : Even (padicValNat 2 (S 1)) := by
  -- Evaluate Δ₁ at the specialization c(j) = [j=1 ∨ j=2]
  set c : ℕ → ℤ := fun j => if j = 1 ∨ j = 2 then 1 else 0 with c_def
  have h_eval : Δ_eval 1 c = -192 := by
    unfold Δ_eval B_eval A_eval C_eval α β
    simp [Finset.sum_range_succ, c_def, Nat.choose]
  have h_eval' : MvPolynomial.eval c (Δ_n 1) = -192 := by
    rw [eval_Δ_eq_Δ_eval]; exact h_eval
  have h_ne : MvPolynomial.eval c (Δ_n 1) ≠ 0 := by rw [h_eval']; norm_num
  have hS_ne : S 1 ≠ 0 := S_ne_zero_of_eval_ne_zero 1 c h_ne
  -- Upper bound: v₂(S(1)) ≤ v₂(|-192|) = 6
  have h_upper := vp_S_le_eval 2 1 c h_ne
  rw [h_eval'] at h_upper
  have h_vp_eval : padicValNat 2 (Int.natAbs (-192 : ℤ)) = 6 := by native_decide
  rw [h_vp_eval] at h_upper
  -- Lower bound: all b_formula(1,k) for k ∈ [1,2] have v₂ ≥ 3
  -- so 2^3 | B₁ coeff, 2^2 | A₁,C₁ coeff, giving 2^6 | Δ₁ coeff
  have he_b : ∀ k ∈ Finset.Icc 1 (2 * 1),
      3 ≤ padicValNat 2 (Int.natAbs (b_formula 1 k)) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    obtain ⟨h1, h2⟩ := hk
    interval_cases k <;> native_decide
  have hB : ∀ m, ((2 ^ 3 : ℕ) : ℤ) ∣ (B_n 1).coeff m :=
    coeff_B_n_dvd 2 1 3 (by omega) he_b
  -- For A₁, C₁: use scalar_AB divisibility
  -- scalar_AB(1,i) for all i ≤ 2 is divisible by 2^2 = 4
  have h_scalar_dvd : ∀ i, i ≤ 2 * 1 → (2 ^ 2) ∣ scalar_AB 1 i := by
    intro i hi
    interval_cases i <;> native_decide
  have hA : ∀ m, ((2 ^ 2 : ℕ) : ℤ) ∣ (A_n 1).coeff m := by
    intro m; unfold A_n; erw [MvPolynomial.coeff_sum]
    exact Finset.dvd_sum fun i hi => by
      have hi' : i ≤ 2 * 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h_dvd : ((2 ^ 2 : ℕ) : ℤ) ∣
          ((-1 : ℤ) ^ i * (Nat.choose (2 * 1) i : ℤ) * (α 1 i : ℤ) * (β 1 i : ℤ)) := by
        have := Int.natCast_dvd_natCast.mpr (h_scalar_dvd i hi')
        convert this.mul_left ((-1 : ℤ) ^ i) using 1; simp [scalar_AB]; ring
      rw [MvPolynomial.coeff_mul]; exact Finset.dvd_sum fun x _ => by
        erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']; aesop
  have hC : ∀ m, ((2 ^ 2 : ℕ) : ℤ) ∣ (C_n 1).coeff m := by
    intro m; unfold C_n; erw [MvPolynomial.coeff_sum]
    exact Finset.dvd_sum fun i hi => by
      have hi' : i ≤ 2 * 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h_dvd : ((2 ^ 2 : ℕ) : ℤ) ∣
          ((-1 : ℤ) ^ i * (Nat.choose (2 * 1) i : ℤ) * (α 1 i : ℤ) * (β 1 i : ℤ)) := by
        have := Int.natCast_dvd_natCast.mpr (h_scalar_dvd i hi')
        convert this.mul_left ((-1 : ℤ) ^ i) using 1; simp [scalar_AB]; ring
      generalize_proofs at *
      rw [MvPolynomial.coeff_mul]; exact Finset.dvd_sum fun x _ => by
        erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']; aesop
  -- 2^6 | Δ₁ coefficients via B² - 4AC decomposition
  have h_coeff : ∀ m ∈ (Δ_n 1).support,
      2 ^ 6 ∣ Int.natAbs ((Δ_n 1).coeff m) := by
    intro m _
    -- B^2 term: 2^6 | B^2 since 2^3 | B
    have h_B2 : ((2 ^ 6 : ℕ) : ℤ) ∣ (B_n 1 ^ 2).coeff m := by
      have : ((2 ^ 6 : ℕ) : ℤ) = ((2 ^ 3 : ℕ) : ℤ) * ((2 ^ 3 : ℕ) : ℤ) := by norm_num
      rw [this, sq, MvPolynomial.coeff_mul]
      exact Finset.dvd_sum fun x _ => mul_dvd_mul (hB _) (hB _)
    -- 4AC term: 2^6 | 4AC since 2^2 | A, 2^2 | C, and 4 = 2^2
    have h_4AC : ((2 ^ 6 : ℕ) : ℤ) ∣ (4 * A_n 1 * C_n 1).coeff m := by
      have h4 : (4 : MvPolynomial ℕ ℤ) = MvPolynomial.C 4 := by simp [map_ofNat]
      rw [show (4 : MvPolynomial ℕ ℤ) * A_n 1 * C_n 1 = MvPolynomial.C 4 * (A_n 1 * C_n 1) by
        rw [h4]; ring]
      rw [MvPolynomial.coeff_C_mul]
      have h_AC : ((2 ^ 2 : ℕ) : ℤ) * ((2 ^ 2 : ℕ) : ℤ) ∣ (A_n 1 * C_n 1).coeff m := by
        rw [MvPolynomial.coeff_mul]
        exact Finset.dvd_sum fun x _ => mul_dvd_mul (hA _) (hC _)
      have : (4 : ℤ) * (((2 ^ 2 : ℕ) : ℤ) * ((2 ^ 2 : ℕ) : ℤ)) ∣
          (4 : ℤ) * (A_n 1 * C_n 1).coeff m := mul_dvd_mul_left 4 h_AC
      refine dvd_trans ?_ this
      show ((2 ^ 6 : ℕ) : ℤ) ∣ (4 : ℤ) * (((2 ^ 2 : ℕ) : ℤ) * ((2 ^ 2 : ℕ) : ℤ))
      norm_num
    unfold Δ_n at *
    have h_sub : ((2 ^ 6 : ℕ) : ℤ) ∣ (B_n 1 ^ 2 - 4 * A_n 1 * C_n 1).coeff m := by
      rw [MvPolynomial.coeff_sub]; exact dvd_sub h_B2 h_4AC
    exact Int.natCast_dvd.mp h_sub
  have h_lower : 6 ≤ padicValNat 2 (S 1) :=
    vp_S_ge_of_coeff_dvd 2 1 6 hS_ne h_coeff
  -- v₂(S(1)) = 6, which is even
  exact ⟨3, by omega⟩

/-! ## Steps 5–7: Case A characterization + Case B + Conclusion

The full proof of main_theorem_p2 is assembled here from:
- Steps 1–4 above (Setup, Gauss, Case A ultrametric)
- Step 5 (Case A characterization): proved in P2Step5.lean
- Steps 6–7 (Case B + Conclusion): proved in P2CaseB.lean
-/

-- TODO: Import P2Step5 and P2CaseB, then assemble main_theorem_p2.
-- The final theorem will be:
-- theorem main_theorem_p2 (n : ℕ) (hn : 1 ≤ n) : Even (padicValNat 2 (S n))
-- Proof:
--   n = 1: even_vp_S_one
--   n ≥ 2: v₂(S) = 2 + v₂(cont(H)) by vp2_S_eq
--     Case A (≠): even_vp_H_of_neq_val
--     Case B (=): even_vp_H_of_eq_val_new (from P2CaseB)

theorem main_theorem_p2 (n : ℕ) (hn : 1 ≤ n) :
    Even (padicValNat 2 (S n)) := by
  -- Base case
  by_cases hn1 : n = 1
  · subst hn1; exact even_vp_S_one
  -- Inductive step: n ≥ 2
  have hn2 : 2 ≤ n := by omega
  -- Need content(H) ≠ 0 (H_poly is nonzero since Δ is nonzero)
  have hH : mvContent (H_poly n) ≠ 0 := by
    rw [ne_eq, mvContent_eq_zero_iff]
    intro h
    have hDelta : Δ_n n = 0 := by rw [Delta_eq_four_H]; rw [h]; ring
    have hphi := eval_Delta_n_phi_eq_sq n 1 (by omega) (by omega) (by omega) (by omega)
    rw [hDelta] at hphi; simp at hphi
    have heval := eval_B_phi_eq_bk n 1 (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [heval] at hphi
    exact b_k_val_ne_zero n 1 (by omega) (by omega) (by omega) (sq_eq_zero_iff.mp hphi.symm)
  -- v₂(S) = 2 + v₂(content(H))
  rw [vp2_S_eq n hH]
  -- Suffices: v₂(content(H)) is even
  suffices heven : Even (padicValNat 2 (mvContent (H_poly n))) by
    obtain ⟨k, hk⟩ := heven; exact ⟨k + 1, by omega⟩
  -- Handle edge case: if content(A) = 0 then H = G², v₂(content(H)) is even trivially
  by_cases hA_ne : mvContent (A_n n) = 0
  · have hA_zero : A_n n = 0 := by
      ext m; have := mvContent_dvd_coeff (A_n n) m
      rw [hA_ne, Nat.cast_zero, zero_dvd_iff] at this; exact this
    have hC_zero : C_n n = 0 := by
      have hcac := content_A_eq_C n
      have hC0 : mvContent (C_n n) = 0 := by rw [← content_A_eq_C n, hA_ne]
      ext m; have := mvContent_dvd_coeff (C_n n) m
      rw [hC0, Nat.cast_zero, zero_dvd_iff] at this; exact this
    have : H_poly n = G_poly n ^ 2 := by unfold H_poly; rw [hA_zero, hC_zero]; ring
    rw [this, content_G_sq, sq]
    by_cases hG0 : mvContent (G_poly n) = 0
    · simp [hG0]
    · exact ⟨_, padicValNat.mul hG0 hG0⟩
  -- Handle edge case: if content(G_poly_loc) = 0, contradiction via B evaluation
  by_cases hG_ne : mvContent (G_poly_loc n) = 0
  · exfalso
    have hG_zero : G_poly_loc n = 0 := by
      ext m; have := mvContent_dvd_coeff (G_poly_loc n) m
      rw [hG_ne, Nat.cast_zero, zero_dvd_iff] at this; exact this
    have h_B_eq_2G : B_n n = 2 * G_poly_loc n := by
      ext m
      rw [show (2 : MvPolynomial ℕ ℤ) = MvPolynomial.C 2 from by simp [map_ofNat]]
      rw [MvPolynomial.coeff_C_mul, G_poly_loc_coeff]
      exact (Int.mul_ediv_cancel' (two_dvd_B_n_coeff n m)).symm
    have hB_zero : B_n n = 0 := by rw [h_B_eq_2G, hG_zero, mul_zero]
    have h_eval_B : MvPolynomial.eval (phi n 1) (B_n n) = 0 := by rw [hB_zero, map_zero]
    have heval := eval_B_phi_eq_bk n 1 (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [heval] at h_eval_B
    exact b_k_val_ne_zero n 1 (by omega) (by omega) (by omega) h_eval_B
  -- Main case split: is n+2 a power of 2?
  -- H_poly_loc from P2Step5 is definitionally equal to our H_poly
  have hH' : mvContent (H_poly_loc n) ≠ 0 := hH
  by_cases h_pow2 : ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K
  · -- Case B: n+2 = 2^K, use P2CaseB
    obtain ⟨K, hK, hnK⟩ := h_pow2
    exact even_vp_H_of_eq_val_new n hn2 K hK hnK hH
  · -- Case A: n+2 is not a power of 2, use P2Step5
    exact even_vp_H_of_case_A n hn hA_ne hG_ne hH' h_pow2

end QuarticInvariant
