import Mathlib

open MvPolynomial

/-- The coefficient of C(c) * X_a * X_b at monomial m equals c if m = Finsupp.single a 1 + Finsupp.single b 1, and 0 otherwise. -/
lemma coeff_C_mul_X_mul_X (c : ℤ) (a b : ℕ) (m : ℕ →₀ ℕ) :
    (MvPolynomial.C c * MvPolynomial.X a * MvPolynomial.X b : MvPolynomial ℕ ℤ).coeff m =
      if m = Finsupp.single a 1 + Finsupp.single b 1 then c else 0 := by
  have hxa : MvPolynomial.X b = monomial (Finsupp.single b 1) (1 : ℤ) := rfl
  rw [C_mul_X_eq_monomial, hxa, monomial_mul, mul_one, coeff_monomial]
  simp [eq_comm]

/-- If d | c, then d | (C(c) * X_a * X_b).coeff m for any m. -/
lemma dvd_coeff_C_mul_X_mul_X (d c : ℤ) (hdc : d ∣ c) (a b : ℕ) (m : ℕ →₀ ℕ) :
    d ∣ (MvPolynomial.C c * MvPolynomial.X a * MvPolynomial.X b : MvPolynomial ℕ ℤ).coeff m := by
  rw [coeff_C_mul_X_mul_X]
  split_ifs with h
  · exact hdc
  · exact dvd_zero d

/-- If d | scalar_i for every i in a finset, then d divides every coefficient of
    ∑ i in s, C(scalar_i) * X_{a i} * X_{b i}. -/
lemma dvd_coeff_sum_C_mul_X_mul_X {s : Finset ℕ} {scalar : ℕ → ℤ} {a b : ℕ → ℕ}
    (d : ℤ) (hd : ∀ i ∈ s, d ∣ scalar i) (m : ℕ →₀ ℕ) :
    d ∣ (∑ i ∈ s, MvPolynomial.C (scalar i) * MvPolynomial.X (a i) * MvPolynomial.X (b i) :
      MvPolynomial ℕ ℤ).coeff m := by
  have : coeff m (∑ i ∈ s, MvPolynomial.C (scalar i) * MvPolynomial.X (a i) * MvPolynomial.X (b i) :
      MvPolynomial ℕ ℤ) = ∑ i ∈ s, (MvPolynomial.C (scalar i) * MvPolynomial.X (a i) * MvPolynomial.X (b i) :
      MvPolynomial ℕ ℤ).coeff m :=
    coeff_sum s _ m
  rw [this]
  exact Finset.dvd_sum fun i hi => dvd_coeff_C_mul_X_mul_X d (scalar i) (hd i hi) (a i) (b i) m

/-- If an involution pairs terms in a sum such that paired terms sum to a multiple of d,
    and fixed points are individually multiples of d, then d divides the whole sum. -/
lemma dvd_sum_involution {s : Finset ℕ} {f : ℕ → ℤ} {g : ℕ → ℕ} {d : ℤ}
    (hg_mem : ∀ i ∈ s, g i ∈ s)
    (hg_inv : ∀ i ∈ s, g (g i) = i)
    (hg_pair : ∀ i ∈ s, g i ≠ i → d ∣ (f i + f (g i)))
    (hg_fix : ∀ i ∈ s, g i = i → d ∣ f i) :
    d ∣ ∑ i ∈ s, f i := by
  -- We proceed by strong induction on the cardinality of s
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : s = ∅
    · simp [hs]
    · obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty hs
      by_cases hga : g a = a
      · -- a is a fixed point; remove it and apply IH
        rw [← Finset.add_sum_erase s _ ha]
        apply dvd_add (hg_fix a ha hga)
        apply ih (s.erase a) (Finset.erase_ssubset ha)
        · intro i hi
          have hi' := Finset.mem_erase.mp hi
          have hgi := hg_mem i (Finset.mem_of_mem_erase hi)
          refine Finset.mem_erase.mpr ⟨?_, hgi⟩
          intro hgia
          have : g (g i) = g a := by rw [hgia]
          rw [hg_inv i (Finset.mem_of_mem_erase hi)] at this
          rw [hga] at this
          exact hi'.1 this
        · intro i hi; exact hg_inv i (Finset.mem_of_mem_erase hi)
        · intro i hi; exact hg_pair i (Finset.mem_of_mem_erase hi)
        · intro i hi; exact hg_fix i (Finset.mem_of_mem_erase hi)
      · -- a is not a fixed point; remove both a and g a, use that f a + f (g a) is divisible
        have hga_mem : g a ∈ s := hg_mem a ha
        have hga_ne : g a ≠ a := hga
        have hag : a ≠ g a := fun h => hga (h.symm)
        -- Erase g a first, then a
        set s' := (s.erase a).erase (g a) with hs'_def
        have ha_erase : a ∈ s.erase (g a) :=
          Finset.mem_erase.mpr ⟨hag, ha⟩
        have hga_erase : g a ∈ s.erase a :=
          Finset.mem_erase.mpr ⟨hga_ne, hga_mem⟩
        rw [← Finset.add_sum_erase s _ ha,
            ← Finset.add_sum_erase _ _ hga_erase]
        -- Now goal: d ∣ (f a + (f (g a) + ∑ i in s', f i))
        rw [← add_assoc]
        apply dvd_add (hg_pair a ha hga)
        have hs'_sub : s' ⊂ s := by
          exact (Finset.erase_subset _ _).trans_ssubset (Finset.erase_ssubset ha)
        apply ih s' hs'_sub
        · intro i hi
          have hi_s : i ∈ s := by
            exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
          have hi_ne_a : i ≠ a := by
            intro h; rw [h] at hi
            simp [hs'_def] at hi
          have hi_ne_ga : i ≠ g a := by
            intro h; rw [h] at hi; rw [hs'_def] at hi
            exact absurd hi (Finset.notMem_erase (g a) (s.erase a))
          have hgi_ne_a : g i ≠ a := by
            intro h
            have : g (g i) = g a := by rw [h]
            rw [hg_inv i hi_s] at this
            exact hi_ne_ga this
          have hgi_ne_ga : g i ≠ g a := by
            intro h
            have : g (g i) = g (g a) := by rw [h]
            rw [hg_inv i hi_s, hg_inv a ha] at this
            exact hi_ne_a this
          exact Finset.mem_erase.mpr ⟨hgi_ne_ga,
            Finset.mem_erase.mpr ⟨hgi_ne_a, hg_mem i hi_s⟩⟩
        · intro i hi; exact hg_inv i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
        · intro i hi; exact hg_pair i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
        · intro i hi; exact hg_fix i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))

/-- Paired coefficient extraction with additive pairing.
    For P = ∑ i in range(N+1), C(c_i) * X_i * X_{N-i}:
    if c_i = c_{N-i} (symmetry) and d | c_i for all i,
    plus (2*d) | c_{N/2} when N is even (the centre term),
    then (2*d) divides every coefficient of P.

    At off-centre pairs (i ≠ N-i), the contributions c_i and c_{N-i} to
    the same monomial sum to 2*c_i by symmetry, giving a factor of 2*d.
    At the centre (i = N/2 when N is even), the extra hypothesis is needed. -/
lemma dvd_coeff_paired_sum (N : ℕ) (c : ℕ → ℤ) (d : ℤ)
    (h_symm : ∀ i, i ≤ N → c i = c (N - i))
    (h_dvd : ∀ i, i ≤ N → d ∣ c i)
    (h_center : Even N → (2 * d) ∣ c (N / 2))
    (m : ℕ →₀ ℕ) :
    (2 * d) ∣ (∑ i ∈ Finset.range (N + 1),
      MvPolynomial.C (c i) * MvPolynomial.X i * MvPolynomial.X (N - i) :
      MvPolynomial ℕ ℤ).coeff m := by
  -- Step 1: distribute coeff over the sum, then simplify each term
  have h_coeff_eq : MvPolynomial.coeff m (∑ i ∈ Finset.range (N + 1),
      MvPolynomial.C (c i) * MvPolynomial.X i * MvPolynomial.X (N - i)) =
    ∑ i ∈ Finset.range (N + 1), (MvPolynomial.C (c i) * MvPolynomial.X i *
      MvPolynomial.X (N - i) : MvPolynomial ℕ ℤ).coeff m := coeff_sum _ _ _
  rw [h_coeff_eq]
  simp only [coeff_C_mul_X_mul_X]
  -- Now the goal is: (2*d) ∣ ∑ i in range(N+1), if m = single i 1 + single (N-i) 1 then c i else 0
  -- Step 3: Apply dvd_sum_involution with the involution i ↦ N - i
  apply dvd_sum_involution (g := fun i => N - i)
  · -- g maps range(N+1) to itself
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · -- g is an involution
    intro i hi
    simp only [Finset.mem_range] at hi
    omega
  · -- For non-fixed points, d divides f(i) + f(g(i))
    intro i hi hne
    simp only [Finset.mem_range] at hi
    have hi' : i ≤ N := by omega
    -- Need to show (2*d) ∣ (ite ... + ite ...)
    -- Case analysis on whether the ite's are c i / c (N-i) or 0
    by_cases h1 : m = Finsupp.single i 1 + Finsupp.single (N - i) 1
    · -- First term is c i
      -- For the second term at index N-i: need m = single (N-i) 1 + single (N-(N-i)) 1
      -- N-(N-i) = i (since i ≤ N), so this is single (N-i) 1 + single i 1 = m
      have hi_le : i ≤ N := by omega
      have h2 : m = Finsupp.single (N - i) 1 + Finsupp.single (N - (N - i)) 1 := by
        rw [Nat.sub_sub_self hi_le, h1, add_comm]
      have h2' : (Finsupp.single i 1 + Finsupp.single (N - i) 1 : ℕ →₀ ℕ) =
          Finsupp.single (N - i) 1 + Finsupp.single (N - (N - i)) 1 := by
        rw [Nat.sub_sub_self hi_le, add_comm]
      simp only [h1, ite_true, h2', ite_true]
      -- Now need (2*d) ∣ (c i + c (N - i))
      rw [h_symm i hi']
      have : c (N - i) + c (N - i) = 2 * c (N - i) := by ring
      rw [this]
      exact mul_dvd_mul_left 2 (h_dvd (N - i) (Nat.sub_le N i))
    · by_cases h2 : m = Finsupp.single (N - i) 1 + Finsupp.single (N - (N - i)) 1
      · -- This case is contradictory: h2 implies h1
        exfalso; apply h1
        rw [h2, Nat.sub_sub_self hi', add_comm]
      · -- Both terms are 0
        simp only [h1, ite_false, h2]
        simp only [add_zero]
        exact dvd_zero _
  · -- For fixed points (i = N - i, i.e. N = 2*i), (2*d) divides f(i)
    intro i hi hfix
    simp only [Finset.mem_range] at hi
    have hi' : i ≤ N := by omega
    have hNi : N - i = i := hfix
    have hN_even : Even N := by
      refine ⟨i, ?_⟩; omega
    have hi_half : i = N / 2 := by omega
    by_cases h1 : m = Finsupp.single i 1 + Finsupp.single (N - i) 1
    · simp only [h1, ite_true]
      rw [hi_half]
      exact h_center hN_even
    · simp only [h1, ite_false]
      exact dvd_zero _

-- `centre_not_max` was previously an axiom here.
-- It is now proved as a theorem in `Modular.P2CarryMax`.
