import Mathlib
import Modular.Defs

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant

open MvPolynomial Finset

/-! ## Gauss's lemma for MvPolynomial ℕ ℤ

We prove `mvContent (f * g) = mvContent f * mvContent g`.
-/

-- § Basic properties of mvContent

theorem mvContent_dvd_natAbs_coeff (p : MvPolynomial ℕ ℤ) (m : ℕ →₀ ℕ) :
    mvContent p ∣ Int.natAbs (coeff m p) := by
  unfold mvContent
  by_cases hm : m ∈ p.support
  · exact Finset.gcd_dvd hm
  · rw [mem_support_iff, not_not] at hm; simp [hm]

theorem mvContent_dvd_coeff (p : MvPolynomial ℕ ℤ) (m : ℕ →₀ ℕ) :
    (↑(mvContent p) : ℤ) ∣ coeff m p := by
  rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast]
  exact mvContent_dvd_natAbs_coeff p m

theorem mvContent_eq_zero_iff {p : MvPolynomial ℕ ℤ} :
    mvContent p = 0 ↔ p = 0 := by
  unfold mvContent; rw [Finset.gcd_eq_zero_iff]; constructor
  · intro h; ext m
    by_cases hm : m ∈ p.support
    · exact (Int.natAbs_eq_zero.mp (h m hm)).symm ▸ (MvPolynomial.coeff_zero m).symm
    · rw [mem_support_iff, not_not] at hm; simp [hm]
  · intro h; simp [h]

-- § Scalar multiplication

theorem mvContent_C_mul (a : ℤ) (p : MvPolynomial ℕ ℤ) :
    mvContent (C a * p) = Int.natAbs a * mvContent p := by
  by_cases ha : a = 0
  · simp [ha, mvContent]
  unfold mvContent
  have hsup : (C a * p).support = p.support := by
    ext m; simp only [mem_support_iff, coeff_C_mul]
    exact ⟨fun h heq => h (by simp [heq]),
           fun h => mul_ne_zero ha h⟩
  rw [hsup]
  conv_lhs => arg 2; ext m; rw [coeff_C_mul, Int.natAbs_mul]
  rw [Finset.gcd_mul_left]; simp

-- § Easy direction

theorem mvContent_mul_dvd (f g : MvPolynomial ℕ ℤ) :
    mvContent f * mvContent g ∣ mvContent (f * g) := by
  unfold mvContent
  apply Finset.dvd_gcd
  intro m _
  rw [coeff_mul, ← Int.natCast_dvd_natCast, Int.dvd_natAbs]; push_cast
  apply Finset.dvd_sum
  intro ⟨m₁, m₂⟩ _
  apply mul_dvd_mul
  · rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast]; exact mvContent_dvd_natAbs_coeff f m₁
  · rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast]; exact mvContent_dvd_natAbs_coeff g m₂

-- § Primitive part

/-- The primitive part of f: divide each coefficient by the content. -/
noncomputable def primPartMV (f : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℤ :=
  (f : (ℕ →₀ ℕ) →₀ ℤ).mapRange (· / ↑(mvContent f)) (by simp)

theorem coeff_primPartMV (f : MvPolynomial ℕ ℤ) (m : ℕ →₀ ℕ) :
    coeff m (primPartMV f) = coeff m f / ↑(mvContent f) := by
  unfold primPartMV coeff; exact Finsupp.mapRange_apply

theorem eq_C_content_mul_primPart (f : MvPolynomial ℕ ℤ) :
    f = C (↑(mvContent f) : ℤ) * primPartMV f := by
  ext m
  rw [coeff_C_mul, coeff_primPartMV]
  exact (Int.mul_ediv_cancel' (mvContent_dvd_coeff f m)).symm

theorem support_primPartMV (f : MvPolynomial ℕ ℤ) :
    (primPartMV f).support = f.support := by
  ext m; simp only [mem_support_iff]; rw [coeff_primPartMV]
  exact ⟨fun h heq => h (by simp [heq]),
    fun h heq => h ((Int.ediv_mul_cancel (mvContent_dvd_coeff f m)).symm ▸
      by rw [heq, zero_mul])⟩

theorem mvContent_primPartMV (f : MvPolynomial ℕ ℤ) (hf : f ≠ 0) :
    mvContent (primPartMV f) = 1 := by
  unfold mvContent; rw [support_primPartMV]
  have hconv : ∀ m, Int.natAbs (coeff m (primPartMV f)) =
      Int.natAbs (coeff m f) / mvContent f := by
    intro m; rw [coeff_primPartMV, Int.natAbs_ediv _ (mvContent f)]
    simp [mvContent_dvd_coeff f m, Int.natAbs_natCast]
  conv_lhs => arg 2; ext m; rw [hconv m]
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hf
  exact Finset.gcd_div_eq_one hm
    (by rwa [ne_eq, Int.natAbs_eq_zero, ← ne_eq, ← mem_support_iff])

-- § Primitivity lemma (hard direction core)

/-- Product of primitive polynomials is primitive. -/
theorem primitive_mul (f g : MvPolynomial ℕ ℤ)
    (hf : mvContent f = 1) (hg : mvContent g = 1) :
    mvContent (f * g) = 1 := by
  by_contra h
  have hf0 : f ≠ 0 := by intro heq; simp [heq, mvContent] at hf
  have hg0 : g ≠ 0 := by intro heq; simp [heq, mvContent] at hg
  have hfg0 : f * g ≠ 0 := mul_ne_zero hf0 hg0
  have hne0 : mvContent (f * g) ≠ 0 := by
    rw [ne_eq, mvContent_eq_zero_iff]; exact hfg0
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (by omega : mvContent (f * g) ≠ 1)
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hfg_map0 : MvPolynomial.map (Int.castRingHom (ZMod q)) (f * g) = 0 := by
    ext m; simp only [coeff_map, coeff_zero]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    have : q ∣ Int.natAbs (coeff m (f * g)) :=
      dvd_trans hqdvd (mvContent_dvd_natAbs_coeff (f * g) m)
    rwa [← Int.natCast_dvd_natCast, Int.dvd_natAbs] at this
  have hfne : MvPolynomial.map (Int.castRingHom (ZMod q)) f ≠ 0 := by
    intro heq
    have hall : ∀ m ∈ f.support, q ∣ Int.natAbs (coeff m f) := fun m _ => by
      have := MvPolynomial.ext_iff.mp heq m
      simp [coeff_map] at this
      rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    exact hq.not_dvd_one (hf ▸ Finset.dvd_gcd hall)
  have hgne : MvPolynomial.map (Int.castRingHom (ZMod q)) g ≠ 0 := by
    intro heq
    have hall : ∀ m ∈ g.support, q ∣ Int.natAbs (coeff m g) := fun m _ => by
      have := MvPolynomial.ext_iff.mp heq m
      simp [coeff_map] at this
      rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    exact hq.not_dvd_one (hg ▸ Finset.dvd_gcd hall)
  exact mul_ne_zero hfne hgne (by rw [← map_mul]; exact hfg_map0)

-- § Main theorem

theorem mvContent_mul (f g : MvPolynomial ℕ ℤ) :
    mvContent (f * g) = mvContent f * mvContent g := by
  by_cases hf : f = 0
  · simp [hf, mvContent]
  by_cases hg : g = 0
  · simp [hg, mvContent]
  -- Use Nat.dvd_antisymm with both directions
  apply Nat.dvd_antisymm
  · -- Hard direction: mvContent(f*g) ∣ mvContent f * mvContent g
    -- Rewrite f*g using primitive factorization
    have heq : f * g = C ((↑(mvContent f) : ℤ) * ↑(mvContent g)) *
        (primPartMV f * primPartMV g) := by
      conv_lhs => rw [eq_C_content_mul_primPart f, eq_C_content_mul_primPart g]
      rw [show C (↑(mvContent f) : ℤ) * primPartMV f *
          (C (↑(mvContent g) : ℤ) * primPartMV g) =
        C (↑(mvContent f) : ℤ) * C (↑(mvContent g) : ℤ) *
          (primPartMV f * primPartMV g) from by ring,
        ← map_mul (MvPolynomial.C : ℤ →+* MvPolynomial ℕ ℤ)]
    rw [heq, mvContent_C_mul,
      primitive_mul _ _ (mvContent_primPartMV f hf) (mvContent_primPartMV g hg),
      mul_one, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  · -- Easy direction: mvContent f * mvContent g ∣ mvContent(f*g)
    exact mvContent_mul_dvd f g

end QuarticInvariant
