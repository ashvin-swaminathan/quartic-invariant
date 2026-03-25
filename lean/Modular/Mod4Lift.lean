import Mathlib

set_option maxHeartbeats 800000
noncomputable section

/-- If 2 | (f.coeff m - a.coeff m) for all m, then 4 | (f²coeff m - a².coeff m) for all m.
    Proof: f = a + 2r, so f² = a² + 4ar + 4r² = a² + 4(ar + r²). -/
lemma sq_congr_mod4 (f a : MvPolynomial ℕ ℤ)
    (h : ∀ m, (2 : ℤ) ∣ (f.coeff m - a.coeff m)) (m : ℕ →₀ ℕ) :
    (4 : ℤ) ∣ ((f ^ 2).coeff m - (a ^ 2).coeff m) := by
  -- f² - a² = (f - a) * (f + a) = (f - a) * (2*a + (f - a))
  -- = 2*a*(f-a) + (f-a)², so 4 | every coeff since 2 | every coeff of (f-a).
  set r := f - a with hr_def
  have hr : ∀ m, (2 : ℤ) ∣ r.coeff m := by
    intro m; rw [hr_def, MvPolynomial.coeff_sub]; exact h m
  have key : f ^ 2 - a ^ 2 = r * (2 * a + r) := by ring
  rw [show (f ^ 2).coeff m - (a ^ 2).coeff m = (f ^ 2 - a ^ 2).coeff m by
    rw [MvPolynomial.coeff_sub]]
  rw [key]
  -- r * (2*a + r) = 2*(a*r) + r^2, and we show 4 | each term's coefficients
  have expand : r * (2 * a + r) = 2 * a * r + r ^ 2 := by ring
  rw [expand]
  rw [show (2 * a * r + r ^ 2) = MvPolynomial.C 2 * (a * r) + r ^ 2 by
    rw [show (2 : MvPolynomial ℕ ℤ) = MvPolynomial.C 2 from by simp [map_ofNat]]; ring]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul]
  apply dvd_add
  · -- 4 | 2 * (a*r).coeff m, since 2 | every coeff of r
    rw [show (4 : ℤ) = 2 * 2 from by norm_num]
    apply mul_dvd_mul_left
    rw [MvPolynomial.coeff_mul]
    exact Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right (hr _) _
  · -- 4 | (r²).coeff m since 2 | each coeff of r, and 2*2 = 4
    rw [sq, MvPolynomial.coeff_mul]
    exact Finset.dvd_sum fun x _ => by
      rw [show (4 : ℤ) = 2 * 2 from by norm_num]
      exact mul_dvd_mul (hr _) (hr _)

/-- If 2 | (f - a) and 2 | (g - b) coefficient-wise, then 2 | (fg - ab) coefficient-wise.
    Proof: fg - ab = (f-a)g + a(g-b). Each term has 2 | every coefficient. -/
lemma mul_congr_mod2 (f g a b : MvPolynomial ℕ ℤ)
    (hf : ∀ m, (2 : ℤ) ∣ (f.coeff m - a.coeff m))
    (hg : ∀ m, (2 : ℤ) ∣ (g.coeff m - b.coeff m)) (m : ℕ →₀ ℕ) :
    (2 : ℤ) ∣ ((f * g).coeff m - (a * b).coeff m) := by
  -- fg - ab = (f - a) * g + a * (g - b)
  have key : f * g - a * b = (f - a) * g + a * (g - b) := by ring
  rw [show (f * g).coeff m - (a * b).coeff m = (f * g - a * b).coeff m by
    rw [MvPolynomial.coeff_sub]]
  rw [key, MvPolynomial.coeff_add]
  apply dvd_add
  · -- 2 | ((f-a)*g).coeff m since 2 | every coeff of (f-a)
    rw [MvPolynomial.coeff_mul]
    exact Finset.dvd_sum fun x _ => dvd_mul_of_dvd_left (by
      rw [show f - a = f - a from rfl, MvPolynomial.coeff_sub]; exact hf _) _
  · -- 2 | (a*(g-b)).coeff m since 2 | every coeff of (g-b)
    rw [MvPolynomial.coeff_mul]
    exact Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right (by
      rw [show g - b = g - b from rfl, MvPolynomial.coeff_sub]; exact hg _) _
