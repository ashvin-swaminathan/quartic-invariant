import Mathlib
import Modular.Defs
import Modular.ScalarBounds
import Modular.CentralDom
import Modular.GaussMV
import Modular.MainP5
import Modular.Rank1Collapse
import Modular.CoeffDivPP
import Modular.P2CRS
import Modular.P2CarryMax

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant

/-! ## Step 5: Case A Characterization (paper lines 1297–1341)

This proves v₂(cont(A_n)) = v₂(cont(G)) + 1 when n+2 is not a power of 2,
establishing that Case B ⟺ n+2 = 2^k.

We work with B_n, b_formula, scalar_AB from Defs.lean directly.
G_poly and H_poly are defined locally here (they are private in MainP2.lean).
-/

/-! ### Local G_poly definition (B_n / 2 as integer polynomial) -/

/-- G_poly n is B_n / 2 as an integer polynomial. -/
def G_poly_loc (n : ℕ) : MvPolynomial ℕ ℤ :=
  Finsupp.mapRange (· / 2) (by simp) (B_n n)

@[simp]
lemma G_poly_loc_coeff (n : ℕ) (m : ℕ →₀ ℕ) :
    (G_poly_loc n).coeff m = (B_n n).coeff m / 2 :=
  Finsupp.mapRange_apply (hf := by simp)

/-- H_poly n = G² - A·C -/
def H_poly_loc (n : ℕ) : MvPolynomial ℕ ℤ :=
  G_poly_loc n ^ 2 - A_n n * C_n n

/-! ### Abbreviations -/

/-- N = 2n (the degree parameter). -/
abbrev N_val (n : ℕ) : ℕ := 2 * n

/-- M = 2n + 1 (= N + 1). -/
abbrev M_val (n : ℕ) : ℕ := 2 * n + 1

/-- c_max n = max_{0 ≤ j ≤ 2n} v₂(C(M, j)) where M = 2n+1.
    This is the maximum 2-adic valuation of a binomial coefficient C(2n+1, j). -/
def c_max (n : ℕ) : ℕ :=
  (Finset.range (2 * n + 2)).sup (fun j => padicValNat 2 (Nat.choose (2 * n + 1) j))

/-- The coefficient of `C(c) * X_a * X_b` at monomial `m` is `c` if `m` is
    exactly that monomial and `0` otherwise. -/
private lemma coeff_C_mul_X_mul_X (c : ℤ) (a b : ℕ) (m : ℕ →₀ ℕ) :
    (MvPolynomial.C c * MvPolynomial.X a * MvPolynomial.X b : MvPolynomial ℕ ℤ).coeff m =
      if m = Finsupp.single a 1 + Finsupp.single b 1 then c else 0 := by
  have hxa : MvPolynomial.X b = MvPolynomial.monomial (Finsupp.single b 1) (1 : ℤ) := rfl
  rw [MvPolynomial.C_mul_X_eq_monomial, hxa, MvPolynomial.monomial_mul, mul_one,
    MvPolynomial.coeff_monomial]
  simp [eq_comm]

/-- If an involution pairs terms in a sum such that paired terms sum to a multiple of d,
    and fixed points are individually multiples of d, then d divides the whole sum. -/
private lemma dvd_sum_involution {s : Finset ℕ} {f : ℕ → ℤ} {g : ℕ → ℕ} {d : ℤ}
    (hg_mem : ∀ i ∈ s, g i ∈ s)
    (hg_inv : ∀ i ∈ s, g (g i) = i)
    (hg_pair : ∀ i ∈ s, g i ≠ i → d ∣ (f i + f (g i)))
    (hg_fix : ∀ i ∈ s, g i = i → d ∣ f i) :
    d ∣ ∑ i ∈ s, f i := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : s = ∅
    · simp [hs]
    · obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty hs
      by_cases hga : g a = a
      · rw [← Finset.add_sum_erase s _ ha]
        apply dvd_add (hg_fix a ha hga)
        apply ih (s.erase a) (Finset.erase_ssubset ha)
        · intro i hi
          have hi' := Finset.mem_erase.mp hi
          have hgi := hg_mem i (Finset.mem_of_mem_erase hi)
          refine Finset.mem_erase.mpr ⟨?_, hgi⟩
          intro h
          have : g (g i) = g a := by rw [h]
          rw [hg_inv i (Finset.mem_of_mem_erase hi)] at this
          rw [hga] at this
          exact hi'.1 this
        · intro i hi; exact hg_inv i (Finset.mem_of_mem_erase hi)
        · intro i hi; exact hg_pair i (Finset.mem_of_mem_erase hi)
        · intro i hi; exact hg_fix i (Finset.mem_of_mem_erase hi)
      · have hga_mem : g a ∈ s := hg_mem a ha
        have hga_ne : g a ≠ a := hga
        have hag : a ≠ g a := fun h => hga (h.symm)
        set s' := (s.erase a).erase (g a) with hs'_def
        have ha_erase : a ∈ s.erase (g a) :=
          Finset.mem_erase.mpr ⟨hag, ha⟩
        have hga_erase : g a ∈ s.erase a :=
          Finset.mem_erase.mpr ⟨hga_ne, hga_mem⟩
        rw [← Finset.add_sum_erase s _ ha,
            ← Finset.add_sum_erase _ _ hga_erase]
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
    then (2*d) divides every coefficient of P. -/
private lemma dvd_coeff_paired_sum (N : ℕ) (c : ℕ → ℤ) (d : ℤ)
    (h_symm : ∀ i, i ≤ N → c i = c (N - i))
    (h_dvd : ∀ i, i ≤ N → d ∣ c i)
    (h_center : Even N → (2 * d) ∣ c (N / 2))
    (m : ℕ →₀ ℕ) :
    (2 * d) ∣ (∑ i ∈ Finset.range (N + 1),
      MvPolynomial.C (c i) * MvPolynomial.X i * MvPolynomial.X (N - i) :
      MvPolynomial ℕ ℤ).coeff m := by
  have h_coeff_eq : MvPolynomial.coeff m (∑ i ∈ Finset.range (N + 1),
      MvPolynomial.C (c i) * MvPolynomial.X i * MvPolynomial.X (N - i)) =
    ∑ i ∈ Finset.range (N + 1), (MvPolynomial.C (c i) * MvPolynomial.X i *
      MvPolynomial.X (N - i) : MvPolynomial ℕ ℤ).coeff m := MvPolynomial.coeff_sum _ _ _
  rw [h_coeff_eq]
  simp only [coeff_C_mul_X_mul_X]
  apply dvd_sum_involution (g := fun i => N - i)
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    omega
  · intro i hi hne
    simp only [Finset.mem_range] at hi
    have hi' : i ≤ N := by omega
    by_cases h1 : m = Finsupp.single i 1 + Finsupp.single (N - i) 1
    · have hi_le : i ≤ N := by omega
      have h2 : m = Finsupp.single (N - i) 1 + Finsupp.single (N - (N - i)) 1 := by
        rw [Nat.sub_sub_self hi_le, h1, add_comm]
      have h2' : (Finsupp.single i 1 + Finsupp.single (N - i) 1 : ℕ →₀ ℕ) =
          Finsupp.single (N - i) 1 + Finsupp.single (N - (N - i)) 1 := by
        rw [Nat.sub_sub_self hi_le, add_comm]
      simp only [h1, ite_true, h2', ite_true]
      rw [h_symm i hi']
      have : c (N - i) + c (N - i) = 2 * c (N - i) := by ring
      rw [this]
      exact mul_dvd_mul_left 2 (h_dvd (N - i) (Nat.sub_le N i))
    · by_cases h2 : m = Finsupp.single (N - i) 1 + Finsupp.single (N - (N - i)) 1
      · exfalso; apply h1
        rw [h2, Nat.sub_sub_self hi', add_comm]
      · simp only [h1, ite_false, h2]
        simp only [add_zero]
        exact dvd_zero _
  · intro i hi hfix
    simp only [Finset.mem_range] at hi
    have hi' : i ≤ N := by omega
    have hN_even : Even N := by
      refine ⟨i, ?_⟩
      omega
    have hi_half : i = N / 2 := by omega
    by_cases h1 : m = Finsupp.single i 1 + Finsupp.single (N - i) 1
    · simp only [h1, ite_true]
      rw [hi_half]
      exact h_center hN_even
    · simp only [h1, ite_false]
      exact dvd_zero _

/-! ## Step 5.1: Every A_n coefficient is even (L1299–1307)

Paper: Off-centre monomials get factor 2 from additive pairing (α_i·β_i symmetry);
centre coefficient has C(2n,n) = 2·C(2n-1,n-1).
-/

/-- The scalar_AB symmetry: C(N,i)·α(n,i)·β(n,i) = C(N,N-i)·α(n,N-i)·β(n,N-i). -/
theorem alpha_beta_symm (n i : ℕ) (hi : i ≤ 2 * n) :
    scalar_AB n i = scalar_AB n (2 * n - i) := by
  rw [scalar_AB_formula n i hi, scalar_AB_formula n (2 * n - i) (Nat.sub_le _ _)]
  rw [show 2 * n + 1 - (2 * n - i) = i + 1 from by omega,
      show 2 * n - i + 1 = 2 * n + 1 - i from by omega]
  ring

/-- C(2n, n) = 2 * C(2n-1, n-1) for n ≥ 1.
    Paper line 1305–1307: "This is even because C(2n,n) = 2·C(2n−1,n−1)." -/
theorem centralBinom_even (n : ℕ) (hn : 1 ≤ n) :
    Nat.choose (2 * n) n = 2 * Nat.choose (2 * n - 1) (n - 1) := by
  -- Use (n+1) * C(n, k) = (n+1-k) * C(n+1, k) rearranged:
  -- Nat.add_one_mul_choose_eq: (n+1) * C(n, k) = C(n+1, k+1) * (k+1)
  -- With n := 2n-1, k := n-1:
  -- (2n) * C(2n-1, n-1) = C(2n, n) * n
  have h_eq : Nat.choose (2 * n) n * n = (2 * n) * Nat.choose (2 * n - 1) (n - 1) := by
    have := Nat.add_one_mul_choose_eq (2 * n - 1) (n - 1)
    rw [show (2 * n - 1) + 1 = 2 * n from by omega,
        show (n - 1) + 1 = n from by omega] at this
    linarith
  have hn_pos : 0 < n := by omega
  -- From h_eq: C(2n,n) * n = 2n * C(2n-1,n-1)
  -- Dividing both sides by n: C(2n,n) = 2 * C(2n-1,n-1)
  have : Nat.choose (2 * n) n * n / n = 2 * Nat.choose (2 * n - 1) (n - 1) :=
    Nat.div_eq_of_eq_mul_right hn_pos (by linarith)
  rwa [Nat.mul_div_cancel _ hn_pos] at this

/-- The A_n coefficient at the centre monomial f_n² is even.
    Paper: "At the centre i = n, the coefficient is (-1)^n C(2n,n) γ².
    This is even because C(2n,n) = 2·C(2n-1,n-1)." -/
theorem A_center_coeff_even (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) ∣ ((-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
      (α n n : ℤ) * (β n n : ℤ)) := by
  have h := centralBinom_even n hn
  have hcast : (Nat.choose (2 * n) n : ℤ) = 2 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) := by
    exact_mod_cast h
  rw [hcast]
  exact ⟨(-1) ^ n * ↑(Nat.choose (2 * n - 1) (n - 1)) * ↑(α n n) * ↑(β n n), by ring⟩

/-- Every A_n coefficient is divisible by 2.
    Paper lines 1299–1307: off-centre by pairing, centre by centralBinom_even. -/
theorem two_dvd_A_n_coeff (n : ℕ) (hn : 1 ≤ n) :
    ∀ m, (2 : ℤ) ∣ (A_n n).coeff m := by
  -- The proof proceeds by showing that the scalar coefficient
  -- 2 * scalar_AB(n, i) arises from the additive pairing for off-centre terms,
  -- and centralBinom_even gives the factor of 2 at the centre.
  -- We use the fact that scalar_AB(n,i) = scalar_AB(n, 2n-i) (alpha_beta_symm)
  -- to pair terms i and 2n-i.
  --
  -- Each scalar (-1)^i * C(2n,i) * α(n,i) * β(n,i) is divisible by 2
  -- because scalar_AB(n,i) = (2n)! * (2n+1-i)! * (i+1)! and (2n)! is even for n ≥ 1.
  have h_scalar_div : ∀ i ∈ Finset.range (2 * n + 1),
      (2 : ℤ) ∣ ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
        (α n i : ℤ) * (β n i : ℤ)) := by
    intro i hi
    have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h_dvd_nat : 2 ∣ scalar_AB n i := by
      rw [scalar_AB_formula n i hi']
      -- 2 ∣ (2n)! since (2n)! = (2n) * (2n-1)! and 2 ∣ 2n for n ≥ 1
      have h2_dvd_fac : 2 ∣ (2 * n).factorial := by
        rw [show 2 * n = (2 * n - 1) + 1 from by omega, Nat.factorial_succ]
        exact dvd_mul_of_dvd_left (show 2 ∣ (2 * n - 1 + 1) by omega) _
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2_dvd_fac _) _
    have h_dvd_int : (2 : ℤ) ∣ (scalar_AB n i : ℤ) :=
      Int.natCast_dvd_natCast.mpr h_dvd_nat
    have : ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
        (α n i : ℤ) * (β n i : ℤ)) = (-1 : ℤ) ^ i * (scalar_AB n i : ℤ) := by
      simp [scalar_AB]; ring
    rw [this]
    exact h_dvd_int.mul_left _
  intro m
  unfold A_n
  have h_coeff_dvd : ∀ i ∈ Finset.range (2 * n + 1),
      (2 : ℤ) ∣ MvPolynomial.coeff m
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

/-! ## Step 5.2: v₂ formula for G-coefficients (L1317–1325)

Paper says: |G-coeff at f_j f_{M-j}| = N! · |M-2j| · (M-j)! · j!
(from b_formula_factored + G = B/2).
-/

/-- M - 2j is always odd (since M = 2n+1 is odd). -/
theorem M_sub_two_j_odd (n j : ℕ) (hj : j ≤ n) :
    ¬ (2 ∣ (2 * n + 1 - 2 * j)) := by omega

/-- v₂(a! · b!) = v₂((a+b)!) - v₂(C(a+b, a)).
    Paper line 1323: "the last step uses v₂(a!·b!) = v₂((a+b)!) − v₂(C(a+b,a))."
    This is essentially padicValNat_factorial_sum rearranged. -/
theorem v2_factorial_mul (a b : ℕ) :
    padicValNat 2 a.factorial + padicValNat 2 b.factorial =
    padicValNat 2 (a + b).factorial - padicValNat 2 (Nat.choose (a + b) a) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h := padicValNat_factorial_sum 2 a b
  omega

/-- v₂(|b_formula(n,k)|) = 1 + v₂(N!) + v₂(M!) - v₂(C(M,k)) for k ∈ [1, 2n].
    This follows from b_formula_factored: b = 2·(-1)^k·N!·(M-2k)·(M-k)!·k!.
    Since M-2k = 2n+1-2k is always odd, v₂(|M-2k|) = 0.
    And v₂(N!·(M-k)!·k!) = v₂(N!) + v₂((M-k)!) + v₂(k!)
                           = v₂(N!) + v₂(M!) - v₂(C(M,k))
    by the factorial identity v₂(a!·b!) = v₂((a+b)!) - v₂(C(a+b,a)). -/
theorem v2_b_formula_eq (n k : ℕ) (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * n) :
    padicValNat 2 (Int.natAbs (b_formula n k)) =
      1 + padicValNat 2 (2 * n).factorial + padicValNat 2 (2 * n + 1).factorial -
        padicValNat 2 (Nat.choose (2 * n + 1) k) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  -- Step 1: Rewrite using b_formula_factored
  have h_eq := b_formula_factored n k hk2
  -- Step 2: Compute natAbs of the product
  -- b_formula n k = 2 * (-1)^k * (N! * (2n+1-2k) * (2n+1-k)! * k!)
  have h_natabs : Int.natAbs (b_formula n k) =
      2 * Int.natAbs (((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * k) *
       ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ)) := by
    rw [h_eq]
    rw [show (2 : ℤ) * (-1 : ℤ) ^ k *
      (((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * ↑k) *
       ((2 * n + 1 - k).factorial : ℤ) * (↑k.factorial : ℤ)) =
      (2 : ℤ) * ((-1 : ℤ) ^ k *
      (((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * ↑k) *
       ((2 * n + 1 - k).factorial : ℤ) * (↑k.factorial : ℤ))) from by ring]
    rw [Int.natAbs_mul, Int.natAbs_mul]
    simp [Int.natAbs_pow, one_pow]
  -- Step 3: The inner product is nonneg, so natAbs = the natural number product
  -- Actually, let's just work with the absolute value directly.
  -- The key factors are: N!, |2n+1-2k| (as Nat), (2n+1-k)!, k!
  have h_inner_natabs : Int.natAbs (((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * k) *
       ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ)) =
      (2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * k) *
       (2 * n + 1 - k).factorial * k.factorial := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]
    simp [Int.natAbs_natCast]
  rw [h_natabs, h_inner_natabs]
  -- Step 4: v₂(2 * X) = 1 + v₂(X) when X ≠ 0
  have h_natabs_ne : Int.natAbs ((2 * n : ℤ) + 1 - 2 * k) ≠ 0 := by
    simp only [ne_eq, Int.natAbs_eq_zero]; omega
  have h_prod_ne : (2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * k) *
       (2 * n + 1 - k).factorial * k.factorial ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · exact Nat.factorial_ne_zero _
    · exact h_natabs_ne
    · exact Nat.factorial_ne_zero _
    · exact Nat.factorial_ne_zero _
  rw [padicValNat.mul (by norm_num) h_prod_ne]
  -- v₂(2) = 1
  have h_v2_two : padicValNat 2 2 = 1 := by native_decide
  rw [h_v2_two]
  -- Now we need: v₂(N! * |2n+1-2k| * (2n+1-k)! * k!) =
  --   v₂(N!) + v₂(M!) - v₂(C(M,k))
  -- Step 5: v₂(|2n+1-2k|) = 0 since it's odd
  have h_odd_factor : ¬ (2 ∣ Int.natAbs ((2 * n : ℤ) + 1 - 2 * k)) := by
    intro ⟨m, hm⟩
    have : (Int.natAbs ((2 * n : ℤ) + 1 - 2 * k) : ℤ) = 2 * m := by exact_mod_cast hm
    have h1 : ((2 * n : ℤ) + 1 - 2 * k) = 2 * m ∨ ((2 * n : ℤ) + 1 - 2 * k) = -(2 * m) := by
      rcases Int.natAbs_eq ((2 * n : ℤ) + 1 - 2 * k) with h | h <;> [left; right] <;> linarith
    rcases h1 with h | h <;> omega
  have h_odd_val : padicValNat 2 (Int.natAbs ((2 * n : ℤ) + 1 - 2 * k)) = 0 :=
    padicValNat.eq_zero_of_not_dvd h_odd_factor
  -- Step 6: Split the product valuation
  have h_split1 : padicValNat 2 ((2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * k) *
       (2 * n + 1 - k).factorial * k.factorial) =
    padicValNat 2 ((2 * n).factorial) + padicValNat 2 (Int.natAbs ((2 * n : ℤ) + 1 - 2 * k)) +
    padicValNat 2 ((2 * n + 1 - k).factorial) + padicValNat 2 (k.factorial) := by
    rw [padicValNat.mul (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) h_natabs_ne)
        (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)]
    rw [padicValNat.mul (mul_ne_zero (Nat.factorial_ne_zero _) h_natabs_ne)
        (Nat.factorial_ne_zero _)]
    rw [padicValNat.mul (Nat.factorial_ne_zero _) h_natabs_ne]
  rw [h_split1, h_odd_val, add_zero]
  -- Step 7: Use v2_factorial_mul to relate (2n+1-k)! * k! to (2n+1)! and C(2n+1,k)
  have h_sum_eq : (2 * n + 1 - k) + k = 2 * n + 1 := by omega
  have h_fac_sum := v2_factorial_mul (2 * n + 1 - k) k
  rw [h_sum_eq] at h_fac_sum
  -- h_fac_sum : v₂((2n+1-k)!) + v₂(k!) = v₂((2n+1)!) - v₂(C(2n+1, 2n+1-k))
  -- We need C(2n+1, 2n+1-k) = C(2n+1, k)
  have h_choose_symm : Nat.choose (2 * n + 1) (2 * n + 1 - k) = Nat.choose (2 * n + 1) k := by
    rw [Nat.choose_symm (by omega : k ≤ 2 * n + 1)]
  rw [h_choose_symm] at h_fac_sum
  -- Now combine: 1 + v₂(N!) + v₂((2n+1-k)!) + v₂(k!)
  --            = 1 + v₂(N!) + v₂(M!) - v₂(C(M,k))
  -- From v2_factorial_mul, we know v₂(C(M,k)) ≤ v₂(M!)
  have h_choose_le : padicValNat 2 (Nat.choose (2 * n + 1) k) ≤
      padicValNat 2 (2 * n + 1).factorial := by
    have h := padicValNat_factorial_sum 2 (2 * n + 1 - k) k
    rw [h_sum_eq, h_choose_symm] at h; omega
  omega

/-- v₂(cont(G)) = v₂(N!) + v₂(M!) - c_max, where
    c_max = max_{0≤j≤2n} v₂(C(M,j)).
    Paper lines 1324–1325. -/
-- This requires showing content = min of coeff v₂, and min of (K - f(j)) = K - max f(j).
-- Stated but proof deferred.
theorem v2_content_G (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 (mvContent (G_poly_loc n)) =
      padicValNat 2 (N_val n).factorial + padicValNat 2 (M_val n).factorial -
        c_max n := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  set target := padicValNat 2 (N_val n).factorial + padicValNat 2 (M_val n).factorial -
    c_max n with h_target_def
  -- Helper: c_max ≤ v₂(M!) so that the Nat subtraction doesn't underflow
  have h_cmax_le_M : c_max n ≤ padicValNat 2 (2 * n + 1).factorial := by
    unfold c_max
    apply Finset.sup_le
    intro j hj
    have hj_lt := Finset.mem_range.mp hj
    have h := padicValNat_factorial_sum 2 j (2 * n + 1 - j)
    rw [show j + (2 * n + 1 - j) = 2 * n + 1 from by omega] at h
    -- h : v₂((2n+1)!) = v₂(j!) + v₂((2n+1-j)!) + v₂(C(2n+1,j))
    -- so v₂(C(2n+1,j)) ≤ v₂((2n+1)!)
    omega
  -- Helper: 2 | every B_n coefficient
  have h_two_dvd_B : ∀ m, (2 : ℤ) ∣ (B_n n).coeff m := by
    have he_b : ∀ k ∈ Finset.Icc 1 (2 * n),
        1 ≤ padicValNat 2 (Int.natAbs (b_formula n k)) := by
      intro k hk
      have hk_le : k ≤ 2 * n := (Finset.mem_Icc.mp hk).2
      have h2_dvd : (2 : ℤ) ∣ b_formula n k := by
        rw [b_formula_factored n k hk_le]
        exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) _
      have hbf_ne : b_formula n k ≠ 0 :=
        b_k_val_ne_zero n k (by omega) (Finset.mem_Icc.mp hk).1 hk_le
      exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hbf_ne)).mp
        (Int.natAbs_dvd_natAbs.mpr h2_dvd)
    intro m
    have h := coeff_B_n_dvd 2 n 1 (by omega) he_b m
    rwa [show ((2 ^ 1 : ℕ) : ℤ) = (2 : ℤ) from by norm_num] at h
  -- Helper: B = 2 * G coefficient-wise
  have h_B_eq_2G : ∀ m, (B_n n).coeff m = 2 * (G_poly_loc n).coeff m := by
    intro m; rw [G_poly_loc_coeff]
    exact (Int.mul_ediv_cancel' (h_two_dvd_B m)).symm
  -- Helper: B = C(2) * G as MvPolynomials
  have h_B_eq_2G_poly : B_n n = MvPolynomial.C (2 : ℤ) * G_poly_loc n := by
    ext m; simp only [MvPolynomial.coeff_C_mul]; exact h_B_eq_2G m
  -- ** Find witness jw ∈ [1, n] with v₂(C(M, jw)) = c_max **
  -- c_max is the sup over range(2n+2), achieved at some j_max.
  have hne_range : (Finset.range (2 * n + 2)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨j_max, hj_mem, hj_max⟩ := Finset.exists_max_image (Finset.range (2 * n + 2))
    (fun j => padicValNat 2 (Nat.choose (2 * n + 1) j)) hne_range
  rw [Finset.mem_range] at hj_mem
  set f := (fun j => padicValNat 2 (Nat.choose (2 * n + 1) j)) with hf_def
  have hj_eq : (Finset.range (2 * n + 2)).sup f = f j_max := by
    apply le_antisymm
    · exact Finset.sup_le (fun j hj => hj_max j hj)
    · exact Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))
  -- Derive jw ∈ [1, n] with v₂(C(M, jw)) = c_max
  have h_cmax_eq_fmax : c_max n = f j_max := by
    exact (show c_max n = (Finset.range (2 * n + 2)).sup f from rfl).trans hj_eq
  have h_witness : ∃ jw, 1 ≤ jw ∧ jw ≤ n ∧
      padicValNat 2 (Nat.choose (2 * n + 1) jw) = c_max n := by
    by_cases hj_max_zero : j_max = 0
    · -- c_max = v₂(C(M, 0)) = v₂(1) = 0
      refine ⟨1, le_refl 1, hn, ?_⟩
      have : f 0 = 0 := by simp [f, Nat.choose_zero_right]
      rw [h_cmax_eq_fmax, hj_max_zero, this, Nat.choose_one_right]
      exact padicValNat.eq_zero_of_not_dvd (by omega)
    · by_cases hj_max_last : j_max = 2 * n + 1
      · -- c_max = v₂(C(M, M)) = v₂(1) = 0
        refine ⟨1, le_refl 1, hn, ?_⟩
        have : f (2 * n + 1) = 0 := by simp [f, Nat.choose_self]
        rw [h_cmax_eq_fmax, hj_max_last, this, Nat.choose_one_right]
        exact padicValNat.eq_zero_of_not_dvd (by omega)
      · -- j_max ∈ [1, 2n]
        by_cases hj_le_n : j_max ≤ n
        · exact ⟨j_max, by omega, hj_le_n, h_cmax_eq_fmax.symm⟩
        · -- j_max > n, use jw = 2n+1 - j_max
          push_neg at hj_le_n
          refine ⟨2 * n + 1 - j_max, by omega, by omega, ?_⟩
          rw [h_cmax_eq_fmax]; simp only [f]
          exact congr_arg (padicValNat 2) (Nat.choose_symm (by omega : j_max ≤ 2 * n + 1))
  obtain ⟨jw, hjw_lo, hjw_hi, hjw_eq⟩ := h_witness
  -- Prove content ≠ 0 (G is nonzero since b_formula(n, jw) ≠ 0 and eval(B, phi(n,jw)) = b_formula)
  have hG_ne : mvContent (G_poly_loc n) ≠ 0 := by
    intro h_zero
    -- If content = 0, then all coefficients of G are 0, hence G = 0.
    -- Then B = 2G = 0, so eval(B, any point) = 0.
    -- But eval(B, phi(n, jw)) = b_formula n jw ≠ 0, contradiction.
    have hG_zero : G_poly_loc n = 0 := by
      ext m; have := mvContent_dvd_coeff (G_poly_loc n) m
      rw [h_zero, Nat.cast_zero, zero_dvd_iff] at this; exact this
    have hB_zero : B_n n = 0 := by
      rw [h_B_eq_2G_poly, hG_zero, mul_zero]
    have h_bf_ne : b_formula n jw ≠ 0 :=
      b_k_val_ne_zero n jw (by omega) hjw_lo (by omega)
    have h_eval_B : MvPolynomial.eval (phi n jw) (B_n n) = 0 := by
      rw [hB_zero, map_zero]
    -- But also eval(B, phi(n,jw)) = b_formula n jw
    have h_eval_B' : MvPolynomial.eval (phi n jw) (B_n n) = b_formula n jw := by
      rw [B_n_eq_alt n (by omega)]
      simp only [B_n_alt, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      have hph_0 : phi n jw 0 = 0 := by
        simp only [phi]; rw [if_neg]; push_neg; constructor <;> omega
      have h_bdy : (2 * ((2 * n + 1).factorial : ℤ) ^ 2) * phi n jw 0 * phi n jw (2 * n + 1) = 0 := by
        rw [hph_0, mul_zero, zero_mul]
      rw [h_bdy, zero_add]
      rw [Finset.sum_eq_single jw]
      · simp only [phi]; simp
      · intro j hj hj_ne
        have hj_mem := Finset.mem_Icc.mp hj
        have : phi n jw j = 0 := by
          simp only [phi]; rw [if_neg]; push_neg; exact ⟨hj_ne, by omega⟩
        rw [this]; ring
      · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hjw_lo, hjw_hi⟩) h
    exact h_bf_ne (h_eval_B ▸ h_eval_B'.symm ▸ rfl)
  apply Nat.le_antisymm
  · -- *** Upper bound: v₂(content(G)) ≤ target ***
    -- Evaluate B_n at phi(n, jw).
    set ph := phi n jw
    -- Step 1: content divides evaluation
    have h_cont_dvd_eval : (mvContent (G_poly_loc n) : ℤ) ∣
        MvPolynomial.eval ph (G_poly_loc n) := by
      rw [MvPolynomial.eval_eq]
      exact Finset.dvd_sum fun d _ =>
        dvd_mul_of_dvd_left (mvContent_dvd_coeff _ d) _
    -- Step 2: 2 * eval(G, ph) = eval(B, ph)
    have h_eval_2G : MvPolynomial.eval ph (B_n n) =
        2 * MvPolynomial.eval ph (G_poly_loc n) := by
      rw [h_B_eq_2G_poly, map_mul, MvPolynomial.eval_C]
    -- Step 3: eval(B, ph) = b_formula n jw
    -- Since jw ∈ [1, n], the boundary term vanishes and only j = jw survives.
    have h_eval_B : MvPolynomial.eval ph (B_n n) = b_formula n jw := by
      rw [B_n_eq_alt n (by omega)]
      simp only [B_n_alt, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      -- Boundary term vanishes: ph 0 = 0 since jw ≥ 1
      have hph_0 : ph 0 = 0 := by
        simp only [ph, phi]
        rw [if_neg]; push_neg; constructor <;> omega
      have h_bdy : (2 * ((2 * n + 1).factorial : ℤ) ^ 2) * ph 0 * ph (2 * n + 1) = 0 := by
        rw [hph_0, mul_zero, zero_mul]
      -- Sum: only j = jw contributes
      have h_sum : ∑ j ∈ Finset.Icc 1 n,
          (b_formula n j : ℤ) * ph j * ph (2 * n + 1 - j) =
          b_formula n jw := by
        rw [Finset.sum_eq_single jw]
        · have hph_jw : ph jw = 1 := by
            simp only [ph, phi]; split <;> simp_all
          have hph_jw' : ph (2 * n + 1 - jw) = 1 := by
            simp only [ph, phi]; split <;> simp_all
          rw [hph_jw, hph_jw', mul_one, mul_one]
        · intro j hj hj_ne
          have hj_mem := Finset.mem_Icc.mp hj
          have hph_j : ph j = 0 := by
            simp only [ph, phi]
            rw [if_neg]; push_neg; exact ⟨hj_ne, by omega⟩
          rw [hph_j]; ring
        · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hjw_lo, hjw_hi⟩) h
      rw [h_bdy, zero_add, h_sum]
    -- Step 4: b_formula n jw ≠ 0
    have h_bf_ne : b_formula n jw ≠ 0 :=
      b_k_val_ne_zero n jw (by omega) hjw_lo (by omega)
    -- eval(G, ph) ≠ 0
    have h_eval_ne : MvPolynomial.eval ph (G_poly_loc n) ≠ 0 := by
      intro h; rw [h, mul_zero] at h_eval_2G; exact h_bf_ne (h_eval_B ▸ h_eval_2G)
    have h_natabs_ne : Int.natAbs (MvPolynomial.eval ph (G_poly_loc n)) ≠ 0 := by
      rwa [Int.natAbs_ne_zero]
    -- Step 5: b_formula n jw = 2 * eval(G, ph)
    have h_bf_eq_2eval : b_formula n jw = 2 * MvPolynomial.eval ph (G_poly_loc n) := by
      linarith [h_eval_2G, h_eval_B]
    -- Step 6: v₂(|b_formula|) = 1 + v₂(|eval(G)|)
    have h_v2_bf_2eval : padicValNat 2 (Int.natAbs (b_formula n jw)) =
        1 + padicValNat 2 (Int.natAbs (MvPolynomial.eval ph (G_poly_loc n))) := by
      rw [h_bf_eq_2eval, Int.natAbs_mul, show Int.natAbs 2 = 2 from rfl,
          padicValNat.mul (by norm_num) h_natabs_ne,
          show padicValNat 2 2 = 1 from padicValNat.self (by norm_num)]
    -- Step 7: v₂(|b_formula(n, jw)|) = 1 + v₂(N!) + v₂(M!) - v₂(C(M, jw))
    have h_v2_bf := v2_b_formula_eq n jw hn hjw_lo (by omega : jw ≤ 2 * n)
    -- Step 8: v₂(|eval(G)|) = target
    have h_v2_eval : padicValNat 2 (Int.natAbs (MvPolynomial.eval ph (G_poly_loc n))) =
        target := by
      -- v₂(C(M,jw)) ≤ v₂(M!)
      have h_choose_le : padicValNat 2 (Nat.choose (2 * n + 1) jw) ≤
          padicValNat 2 (2 * n + 1).factorial := by
        have h := padicValNat_factorial_sum 2 jw (2 * n + 1 - jw)
        rw [show jw + (2 * n + 1 - jw) = 2 * n + 1 from by omega] at h; omega
      show padicValNat 2 (Int.natAbs (MvPolynomial.eval ph (G_poly_loc n))) =
        padicValNat 2 (2 * n).factorial + padicValNat 2 (2 * n + 1).factorial - c_max n
      rw [hjw_eq] at h_v2_bf h_choose_le; omega
    -- Step 8: content | |eval| implies v₂(content) ≤ v₂(|eval|) = target
    have h_dvd_nat : mvContent (G_poly_loc n) ∣
        Int.natAbs (MvPolynomial.eval ph (G_poly_loc n)) :=
      Int.natAbs_dvd_natAbs.mpr h_cont_dvd_eval
    exact ((padicValNat_dvd_iff_le h_natabs_ne).mp
      (dvd_trans pow_padicValNat_dvd h_dvd_nat)).trans h_v2_eval.le
  · -- *** Lower bound: target ≤ v₂(content(G)) ***
    -- Show 2^(target+1) | every B_n coefficient, hence 2^target | every G coefficient.
    have he_b_all : ∀ k ∈ Finset.Icc 1 (2 * n),
        target + 1 ≤ padicValNat 2 (Int.natAbs (b_formula n k)) := by
      intro k hk
      have hk_lo := (Finset.mem_Icc.mp hk).1
      have hk_hi := (Finset.mem_Icc.mp hk).2
      have h_v2_bk := v2_b_formula_eq n k hn hk_lo hk_hi
      -- v₂(C(M, k)) ≤ c_max
      have h_cmax_ge : padicValNat 2 (Nat.choose (2 * n + 1) k) ≤ c_max n := by
        unfold c_max
        exact Finset.le_sup (f := fun j => padicValNat 2 (Nat.choose (2 * n + 1) j))
          (Finset.mem_range.mpr (by omega))
      -- v₂(C(M,k)) ≤ v₂(M!) (ensures Nat subtraction doesn't underflow)
      have h_choose_le : padicValNat 2 (Nat.choose (2 * n + 1) k) ≤
          padicValNat 2 (2 * n + 1).factorial := by
        have h := padicValNat_factorial_sum 2 k (2 * n + 1 - k)
        rw [show k + (2 * n + 1 - k) = 2 * n + 1 from by omega] at h; omega
      -- target + 1 ≤ v₂(|b_formula(n,k)|) since c_max ≥ v₂(C(M,k))
      show padicValNat 2 (2 * n).factorial + padicValNat 2 (2 * n + 1).factorial -
        c_max n + 1 ≤ _
      omega
    have h_B_dvd : ∀ m, ((2 ^ (target + 1) : ℕ) : ℤ) ∣ (B_n n).coeff m :=
      coeff_B_n_dvd 2 n (target + 1) (by omega) he_b_all
    -- Therefore 2^target | every G coefficient
    have h_G_dvd : ∀ m, ((2 ^ target : ℕ) : ℤ) ∣ (G_poly_loc n).coeff m := by
      intro m
      rw [G_poly_loc_coeff]
      have hB := h_B_dvd m
      have h2B := h_two_dvd_B m
      have h_exact : (B_n n).coeff m = 2 * ((B_n n).coeff m / 2) :=
        (Int.mul_ediv_cancel' h2B).symm
      have h_pow_cast : ((2 ^ (target + 1) : ℕ) : ℤ) = 2 * ((2 ^ target : ℕ) : ℤ) := by
        push_cast; ring
      rw [h_pow_cast] at hB
      rw [h_exact] at hB
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hB
    -- 2^target | content(G)
    have h_dvd_cont : 2 ^ target ∣ mvContent (G_poly_loc n) := by
      unfold mvContent
      apply Finset.dvd_gcd
      intro m _
      exact Int.natAbs_dvd_natAbs.mpr (h_G_dvd m)
    exact (padicValNat_dvd_iff_le hG_ne).mp h_dvd_cont

/-! ## Step 5.3: v₂ formula for off-centre A_n coefficients (L1326–1330)

Paper: off-centre A coeff = 2·(-1)^i · C(N,i)·α_i·β_i = 2·(-1)^i · scalar_AB(n,i).
v₂ = 1 + v₂(N!) + v₂((M-i)!) + v₂((i+1)!).
For even i, M-i is odd, so v₂ = 1 + v₂(N!) + v₂(M!) - v₂(C(M,i+1)).
-/

/-- scalar_AB(n,i) = N! * (M-i)! * (i+1)! where N = 2n, M = 2n+1.
    This is scalar_AB_formula specialized. -/
theorem scalar_AB_factorial_form (n i : ℕ) (hi : i ≤ 2 * n) :
    scalar_AB n i = (2 * n).factorial * (2 * n + 1 - i).factorial * (i + 1).factorial :=
  scalar_AB_formula n i hi

/-- For even i, the quantity M - i = 2n+1-i is odd (when i ≤ 2n+1). -/
theorem M_sub_i_odd_of_even (n i : ℕ) (hi_even : Even i) (hi_le : i ≤ 2 * n + 1) :
    ¬ (2 ∣ (2 * n + 1 - i)) := by
  obtain ⟨k, rfl⟩ := hi_even; omega

/-- v₂ of the off-centre A_n coefficient at even index i:
    v₂ = 1 + v₂(N!) + v₂(M!) - v₂(C(M, i+1)).
    Paper line 1330. -/
theorem v2_A_offcenter_even (n i : ℕ) (hn : 1 ≤ n) (hi : i < n) (hi_even : Even i) :
    padicValNat 2 (2 * scalar_AB n i) =
      1 + padicValNat 2 (N_val n).factorial + padicValNat 2 (M_val n).factorial -
        padicValNat 2 (Nat.choose (M_val n) (i + 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hi_le : i ≤ 2 * n := by omega
  -- Step 1: scalar_AB(n,i) = N! * (M-i)! * (i+1)!
  rw [scalar_AB_factorial_form n i hi_le]
  -- Step 2: v₂(2 * N! * (M-i)! * (i+1)!) = 1 + v₂(N!) + v₂((M-i)!) + v₂((i+1)!)
  have hN_pos : 0 < (2 * n).factorial := Nat.factorial_pos _
  have hMi_pos : 0 < (2 * n + 1 - i).factorial := Nat.factorial_pos _
  have hi1_pos : 0 < (i + 1).factorial := Nat.factorial_pos _
  have h_prod_ne : (2 * n).factorial * (2 * n + 1 - i).factorial * (i + 1).factorial ≠ 0 := by
    positivity
  rw [padicValNat.mul (by norm_num) h_prod_ne]
  rw [show padicValNat 2 2 = 1 from padicValNat.self (by norm_num)]
  -- Now need: v₂(N! * (M-i)! * (i+1)!) = v₂(N!) + v₂((M-i)!) + v₂((i+1)!)
  rw [padicValNat.mul (by positivity) (by positivity),
      padicValNat.mul (by positivity) (by positivity)]
  -- Step 3: For even i, M-i = 2n+1-i is odd.
  -- v₂((M-i)!) + v₂((i+1)!) = v₂(M!) - v₂(C(M,i+1))
  -- by v2_factorial_mul with a = M-i-1, ... no, we use: (M-i)! * (i+1)! relates to M! / C(M,i+1)
  -- Actually: C(M, i+1) = M! / ((i+1)! * (M-i-1)!)
  -- So v₂((i+1)!) + v₂((M-i-1)!) = v₂(M!) - v₂(C(M,i+1))
  -- And (M-i)! = (M-i) * (M-i-1)!. For even i, M-i = 2n+1-i is odd, so v₂((M-i)!) = v₂((M-i-1)!).
  have h_Mi_odd : ¬ (2 ∣ (2 * n + 1 - i)) := M_sub_i_odd_of_even n i hi_even (by omega)
  -- v₂((M-i)!) = v₂((M-i) * (M-i-1)!) = v₂(M-i) + v₂((M-i-1)!) = 0 + v₂((M-i-1)!)
  have h_Mi_sub : (2 * n + 1 - i).factorial = (2 * n + 1 - i) * (2 * n + 1 - i - 1).factorial := by
    set k := 2 * n + 1 - i - 1
    have hk : 2 * n + 1 - i = k + 1 := by omega
    rw [hk, Nat.factorial_succ]
  rw [h_Mi_sub, padicValNat.mul (by omega) (by positivity)]
  have h_v2_Mi : padicValNat 2 (2 * n + 1 - i) = 0 :=
    padicValNat.eq_zero_of_not_dvd h_Mi_odd
  rw [h_v2_Mi, zero_add]
  -- Now we need: v₂((M-i-1)!) + v₂((i+1)!) = v₂(M!) - v₂(C(M,i+1))
  -- Use padicValNat_factorial_sum directly (it gives the additive form)
  have h_sum : i + 1 + (2 * n + 1 - i - 1) = 2 * n + 1 := by omega
  have h_fac_sum := padicValNat_factorial_sum 2 (i + 1) (2 * n + 1 - i - 1)
  simp only [h_sum] at h_fac_sum
  -- h_fac_sum: v₂((2n+1)!) = v₂((i+1)!) + v₂((M-i-1)!) + v₂(C(2n+1,i+1))
  -- The goal after all rewrites should be:
  -- 1 + v₂((2n)!) + v₂((M-i-1)!) + v₂((i+1)!)
  --   = 1 + v₂((2n)!) + v₂((2n+1)!) - v₂(C(2n+1,i+1))
  -- Suffices to show: v₂((M-i-1)!) + v₂((i+1)!) + v₂(C(2n+1,i+1)) = v₂((2n+1)!)
  -- which is exactly h_fac_sum.
  -- The difficulty is that the goal uses ℕ subtraction on the RHS.
  -- Let's convert to a form without subtraction.
  -- h_fac_sum should give: v₂((2n+1)!) = v₂((i+1)!) + v₂((M-i-1)!) + v₂(C(2n+1,i+1))
  -- Let's just use it directly. The Nat.choose (M_val n) (i+1) in the goal
  -- should be the same as Nat.choose (2*n+1) (i+1).
  -- After all rewrites, the goal should reduce to: a + c + b = a + d where d = b + c
  -- which is h_fac_sum rearranged.
  -- Since omega struggles with matching, let's extract and rewrite explicitly.
  -- h_fac_sum: v₂((2n+1)!) = v₂((i+1)!) + v₂((M-i-1)!) + v₂(C(2n+1,i+1))
  -- The goal reduces to showing LHS = RHS where the RHS uses ℕ subtraction.
  -- Since h_fac_sum gives v₂(C) ≤ v₂(M!), the subtraction is valid.
  -- omega should handle this once N_val and M_val are unfolded.
  simp only [N_val, M_val] at *
  omega

/-! ## Step 5.4: Consecutive-pair identity for M odd (L1331–1335)

Paper: C(M,2r) / C(M,2r+1) = (2r+1) / (M-2r), both odd.
Therefore v₂(C(M,2r)) = v₂(C(M,2r+1)).
-/

/-- Standard binomial identity: C(M, 2r) * (M - 2r) = C(M, 2r+1) * (2r+1).
    Paper line 1332. -/
theorem consec_pair_ratio (M r : ℕ) (_hr : 2 * r + 1 ≤ M) :
    Nat.choose M (2 * r) * (M - 2 * r) = Nat.choose M (2 * r + 1) * (2 * r + 1) := by
  -- Nat.choose_succ_right_eq says C(n, k+1) * (k+1) = C(n, k) * (n - k)
  have h := Nat.choose_succ_right_eq M (2 * r)
  -- h : C(M, 2r+1) * (2r+1) = C(M, 2r) * (M - 2r)
  linarith

/-- Since M = 2n+1 is odd and 2r is even, both M-2r and 2r+1 are odd.
    Therefore v₂(C(M,2r)) = v₂(C(M,2r+1)).
    Paper lines 1333–1335. -/
theorem v2_consec_pair (n r : ℕ) (hr : 2 * r + 1 ≤ 2 * n + 1) :
    padicValNat 2 (Nat.choose (2 * n + 1) (2 * r)) =
    padicValNat 2 (Nat.choose (2 * n + 1) (2 * r + 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  -- From consec_pair_ratio: C(M, 2r) * (M - 2r) = C(M, 2r+1) * (2r+1)
  have h_ratio := consec_pair_ratio (2 * n + 1) r hr
  -- Taking v₂ of both sides:
  -- v₂(C(M,2r)) + v₂(M-2r) = v₂(C(M,2r+1)) + v₂(2r+1)
  -- M - 2r = 2n+1-2r is odd (since M odd, 2r even), so v₂(M-2r) = 0.
  -- 2r+1 is odd, so v₂(2r+1) = 0.
  -- Therefore v₂(C(M,2r)) = v₂(C(M,2r+1)).
  have h_odd1 : ¬ (2 ∣ (2 * n + 1 - 2 * r)) := by omega
  have h_odd2 : ¬ (2 ∣ (2 * r + 1)) := by omega
  -- Need: if a * b = c * d, and v₂(b) = 0, v₂(d) = 0, then v₂(a) = v₂(c)
  -- Both C(M, 2r) and C(M, 2r+1) are positive since 2r+1 ≤ M
  have h0 : 0 < Nat.choose (2 * n + 1) (2 * r) :=
    Nat.choose_pos (by omega)
  have h1 : 0 < Nat.choose (2 * n + 1) (2 * r + 1) :=
    Nat.choose_pos hr
  -- Take padicValNat of both sides of h_ratio
  have v_b : padicValNat 2 (2 * n + 1 - 2 * r) = 0 :=
    padicValNat.eq_zero_of_not_dvd h_odd1
  have v_d : padicValNat 2 (2 * r + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd h_odd2
  have := congr_arg (padicValNat 2) h_ratio
  rw [padicValNat.mul (by omega) (by omega), padicValNat.mul (by omega) (by omega),
      v_b, v_d] at this
  omega

/-! ## Step 5.5: c_max is achieved at some even j₀ (L1336–1341)

Paper: "Therefore c_max is achieved at some even index j₀."
If max is at odd j, by consec-pair it's also at j−1 (which is even).
-/

/-- c_max is achieved at some even index j₀ ≤ 2n.
    Paper line 1336. -/
theorem c_max_at_even (n : ℕ) (hn : 1 ≤ n) :
    ∃ j₀, j₀ ≤ 2 * n ∧ Even j₀ ∧
      padicValNat 2 (Nat.choose (2 * n + 1) j₀) = c_max n := by
  -- c_max is the sup over range(2n+2), achieved at some j_max.
  -- If j_max is even, we're done.
  -- If j_max is odd, write j_max = 2r+1. By v2_consec_pair,
  -- v₂(C(M, 2r)) = v₂(C(M, 2r+1)) = c_max. Take j₀ = 2r.
  unfold c_max
  -- The sup over a nonempty finite set is achieved at some element.
  -- We use Finset.exists_max_image to find the witness.
  have hne : (Finset.range (2 * n + 2)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨j_max, hj_mem, hj_max⟩ := Finset.exists_max_image (Finset.range (2 * n + 2))
    (fun j => padicValNat 2 (Nat.choose (2 * n + 1) j)) hne
  rw [Finset.mem_range] at hj_mem
  -- The sup equals the value at j_max
  set f := (fun j => padicValNat 2 (Nat.choose (2 * n + 1) j)) with hf_def
  have hj_eq : (Finset.range (2 * n + 2)).sup f = f j_max := by
    apply le_antisymm
    · exact Finset.sup_le (fun j hj => hj_max j hj)
    · exact Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))
  by_cases hj_even : Even j_max
  · -- j_max is even, use it directly
    obtain ⟨r, hr⟩ := hj_even
    exact ⟨j_max, by omega, ⟨r, hr⟩, hj_eq.symm⟩
  · -- j_max is odd, write j_max = 2r+1
    rw [Nat.not_even_iff_odd] at hj_even
    obtain ⟨r, rfl⟩ := hj_even
    -- Use j₀ = 2r (which is even)
    refine ⟨2 * r, by omega, ⟨r, by omega⟩, ?_⟩
    -- v₂(C(M, 2r)) = v₂(C(M, 2r+1)) by v2_consec_pair
    rw [v2_consec_pair n r (by omega)]
    exact hj_eq.symm

/-- The off-center coefficient of `A_n` at the paired monomial
    `X_i * X_{2n-i}` is exactly `(-1)^i * 2 * scalar_AB(n,i)` for `i < n`. -/
private theorem A_n_offcenter_coeff (n i : ℕ) (hi : i < n) :
    (A_n n).coeff (Finsupp.single i 1 + Finsupp.single (2 * n - i) 1) =
      (-1 : ℤ) ^ i * (2 * (scalar_AB n i : ℤ)) := by
  have hi_le : i ≤ 2 * n := by omega
  have hcomp_le : 2 * n - i ≤ 2 * n := by omega
  have hneq : i ≠ 2 * n - i := by
    intro h
    omega
  have hi_mem : i ∈ Finset.range (2 * n + 1) := by
    exact Finset.mem_range.mpr (by omega)
  have hcomp_mem : 2 * n - i ∈ Finset.range (2 * n + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
  set m : ℕ →₀ ℕ := Finsupp.single i 1 + Finsupp.single (2 * n - i) 1
  have hm : m = Finsupp.single i 1 + Finsupp.single (2 * n - i) 1 := rfl
  have hcomp_mem' : 2 * n - i ∈ (Finset.range (2 * n + 1)).erase i :=
    Finset.mem_erase.mpr ⟨by simpa [eq_comm] using hneq, hcomp_mem⟩
  have hsum_split :
      (A_n n).coeff m =
        (((MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
          (α n i : ℤ) * (β n i : ℤ)) *
        MvPolynomial.X i * MvPolynomial.X (2 * n - i)) : MvPolynomial ℕ ℤ).coeff m) +
        (((MvPolynomial.C ((-1 : ℤ) ^ (2 * n - i) * (Nat.choose (2 * n) (2 * n - i) : ℤ) *
          (α n (2 * n - i) : ℤ) * (β n (2 * n - i) : ℤ)) *
        MvPolynomial.X (2 * n - i) * MvPolynomial.X (2 * n - (2 * n - i))) :
          MvPolynomial ℕ ℤ).coeff m) +
        ∑ t ∈ ((Finset.range (2 * n + 1)).erase i).erase (2 * n - i),
          ((MvPolynomial.C ((-1 : ℤ) ^ t * (Nat.choose (2 * n) t : ℤ) *
            (α n t : ℤ) * (β n t : ℤ)) *
          MvPolynomial.X t * MvPolynomial.X (2 * n - t)) : MvPolynomial ℕ ℤ).coeff m := by
    unfold A_n
    erw [MvPolynomial.coeff_sum]
    rw [← Finset.add_sum_erase _ _ hi_mem]
    rw [← Finset.add_sum_erase _ _ hcomp_mem']
    simp [m, coeff_C_mul_X_mul_X, hm, Nat.sub_sub_self hi_le, hneq, add_assoc]
  have h_rest_zero :
      ∑ t ∈ ((Finset.range (2 * n + 1)).erase i).erase (2 * n - i),
        ((MvPolynomial.C ((-1 : ℤ) ^ t * (Nat.choose (2 * n) t : ℤ) *
          (α n t : ℤ) * (β n t : ℤ)) *
        MvPolynomial.X t * MvPolynomial.X (2 * n - t)) : MvPolynomial ℕ ℤ).coeff m = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [coeff_C_mul_X_mul_X]
    by_cases hpair : m = Finsupp.single t 1 + Finsupp.single (2 * n - t) 1
    · exfalso
      have ht_mem1 : t ∈ (Finset.range (2 * n + 1)).erase i := by
        exact (Finset.mem_erase.mp ht).2
      have ht_ne_comp : t ≠ 2 * n - i := by
        exact (Finset.mem_erase.mp ht).1
      have ht_ne_i : t ≠ i := by
        exact (Finset.mem_erase.mp ht_mem1).1
      have ht_le : t ≤ 2 * n := by
        have ht' : t ∈ Finset.range (2 * n + 1) := (Finset.mem_erase.mp ht_mem1).2
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp ht')
      have ht_comp_ne_i : 2 * n - t ≠ i := by omega
      have h_at_i := congrArg (fun f : ℕ →₀ ℕ => f i) hpair
      simp [m, hi, ht_ne_i, ht_comp_ne_i] at h_at_i
    · simp [hpair]
  have h_i :
      ((MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
        (α n i : ℤ) * (β n i : ℤ)) *
      MvPolynomial.X i * MvPolynomial.X (2 * n - i)) : MvPolynomial ℕ ℤ).coeff m =
        (-1 : ℤ) ^ i * (scalar_AB n i : ℤ) := by
    rw [coeff_C_mul_X_mul_X]
    simp [m, scalar_AB, hm, Nat.sub_sub_self hi_le]
    ring
  have h_comp :
      ((MvPolynomial.C ((-1 : ℤ) ^ (2 * n - i) * (Nat.choose (2 * n) (2 * n - i) : ℤ) *
      (α n (2 * n - i) : ℤ) * (β n (2 * n - i) : ℤ)) *
      MvPolynomial.X (2 * n - i) * MvPolynomial.X (2 * n - (2 * n - i))) :
        MvPolynomial ℕ ℤ).coeff m =
        (-1 : ℤ) ^ i * (scalar_AB n i : ℤ) := by
    have hm_swap : m = Finsupp.single (2 * n - i) 1 + Finsupp.single i 1 := by
      dsimp [m]
      simp [add_comm, add_left_comm, add_assoc]
    have hsymm : scalar_AB n (2 * n - i) = scalar_AB n i := by
      simpa [scalar_AB, mul_assoc, mul_left_comm, mul_comm] using
        (alpha_beta_symm n i hi_le).symm
    have hsymmZ : (scalar_AB n (2 * n - i) : ℤ) = (scalar_AB n i : ℤ) := by
      exact_mod_cast hsymm
    rw [coeff_C_mul_X_mul_X, Nat.sub_sub_self hi_le, if_pos hm_swap]
    -- Goal: (-1)^(2n-i) * C(2n,2n-i) * α(n,2n-i) * β(n,2n-i) = (-1)^i * scalar_AB(n,i)
    -- Use alpha_beta_symm: scalar_AB(n, 2n-i) = scalar_AB(n, i)
    -- scalar_AB = choose * alpha * beta, so the RHS is (-1)^i * scalar_AB(n,i)
    -- and the LHS is (-1)^(2n-i) * scalar_AB(n, 2n-i)
    -- LHS = (-1)^(2n-i) * scalar_AB(n, 2n-i), RHS = (-1)^i * scalar_AB(n, i)
    have hpow : (-1 : ℤ) ^ (2 * n - i) = (-1 : ℤ) ^ i := by
      have hni : (-1 : ℤ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
      apply mul_right_cancel₀ hni
      rw [← pow_add, show 2 * n - i + i = 2 * n from Nat.sub_add_cancel hi_le,
          ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
          pow_mul, neg_one_sq, one_pow]
    have hlhs : (-1 : ℤ) ^ (2 * n - i) * ↑(Nat.choose (2 * n) (2 * n - i)) *
        ↑(α n (2 * n - i)) * ↑(β n (2 * n - i)) =
      (-1 : ℤ) ^ (2 * n - i) * ↑(scalar_AB n (2 * n - i)) := by
      simp only [scalar_AB]; push_cast; ring
    rw [hlhs, hpow, hsymmZ]
  rw [hsum_split, h_rest_zero, h_i, h_comp]
  ring

private lemma v2_factorial_le_succ (n : ℕ) :
    padicValNat 2 n.factorial ≤ padicValNat 2 (n + 1).factorial := by
  have h_dvd : n.factorial ∣ (n + 1).factorial := by
    simpa [Nat.factorial_succ, Nat.mul_comm] using
      (dvd_mul_right (n.factorial) (n + 1))
  have h_pow : (2 : ℕ) ^ padicValNat 2 n.factorial ∣ n.factorial := by
    simpa using (pow_padicValNat_dvd (p := 2) (n := n.factorial))
  exact (padicValNat_dvd_iff_le (Nat.factorial_pos _).ne').mp
    (dvd_trans h_pow h_dvd)

private lemma v2_factorial_succ_add_one (n : ℕ) (h2 : 2 ∣ n + 1) :
    padicValNat 2 n.factorial + 1 ≤ padicValNat 2 (n + 1).factorial := by
  have hpow0 : (2 : ℕ) ^ padicValNat 2 n.factorial ∣ n.factorial := by
    simpa using (pow_padicValNat_dvd (p := 2) (n := n.factorial))
  have hpow : (2 : ℕ) ^ (padicValNat 2 n.factorial + 1) ∣ 2 * n.factorial := by
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.mul_dvd_mul_left 2 hpow0)
  have hmul : 2 * n.factorial ∣ (n + 1).factorial := by
    simpa [Nat.factorial_succ, Nat.mul_comm] using
      (Nat.mul_dvd_mul_right h2 n.factorial)
  exact (padicValNat_dvd_iff_le (Nat.factorial_pos _).ne').mp
    (dvd_trans hpow hmul)

private lemma center_even_arith (u t c v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
    (htc : t + 1 ≤ c) :
    u + t - c + 1 ≤ v := by
  have h_u : u + t - c + 1 ≤ u := by
    omega
  exact le_trans h_u huv

private lemma center_odd_arith (u t c v : ℕ) (huv : u + 1 ≤ v) (htc : t ≤ c) :
    u + t - c + 1 ≤ v := by
  have h_u : u + t - c + 1 ≤ u + 1 := by
    omega
  exact le_trans h_u huv

/-! ## Step 5.6: Forward reference / ≥ direction (L1308–1313)

Paper: "each A_n-coefficient divided by 2 has v₂ ≥ v₂(N!) + v₂(M!) − c_max
= v₂(cont(G))."
-/

/-- Each A_n/2 coefficient has v₂ ≥ v₂(cont(G)).
    Paper lines 1308–1312. -/
theorem v2_A_half_ge_content_G (n : ℕ) (hn : 1 ≤ n) :
    ∀ i, i ≤ 2 * n →
      padicValNat 2 (scalar_AB n i) ≥
        padicValNat 2 (N_val n).factorial + padicValNat 2 (M_val n).factorial -
          c_max n := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro i hi
  -- Step 1: scalar_AB(n,i) = N! * (M-i)! * (i+1)!
  rw [scalar_AB_factorial_form n i hi]
  rw [padicValNat.mul (by positivity) (by positivity : (i + 1).factorial ≠ 0),
      padicValNat.mul (by positivity : (2 * n).factorial ≠ 0)
        (by positivity : (2 * n + 1 - i).factorial ≠ 0)]
  -- Need: v₂(N!) + v₂((M-i)!) + v₂((i+1)!) ≥ v₂(N!) + v₂(M!) - c_max
  -- i.e., v₂((M-i)!) + v₂((i+1)!) ≥ v₂(M!) - c_max
  -- By v2_factorial_mul: v₂((i+1)!) + v₂((M-i-1)!) = v₂(M!) - v₂(C(M,i+1))
  -- And v₂((M-i)!) ≥ v₂((M-i-1)!) (since (M-i)! = (M-i) * (M-i-1)!)
  -- So v₂((M-i)!) + v₂((i+1)!) ≥ v₂((M-i-1)!) + v₂((i+1)!)
  --    = v₂(M!) - v₂(C(M,i+1)) ≥ v₂(M!) - c_max.
  -- The last step: v₂(C(M,i+1)) ≤ c_max since i+1 ∈ range(2n+2).
  have h_sum : i + 1 + (2 * n + 1 - i - 1) = 2 * n + 1 := by omega
  have h_v2fm := v2_factorial_mul (i + 1) (2 * n + 1 - i - 1)
  rw [h_sum] at h_v2fm
  -- v₂((M-i)!) ≥ v₂((M-i-1)!)
  have h_Mi_ge : padicValNat 2 (2 * n + 1 - i).factorial ≥
      padicValNat 2 (2 * n + 1 - i - 1).factorial := by
    set k := 2 * n + 1 - i - 1 with hk_def
    have hk_succ : 2 * n + 1 - i = k + 1 := by omega
    rw [hk_succ, Nat.factorial_succ, padicValNat.mul (by omega) (by positivity)]
    omega
  -- v₂(C(M,i+1)) ≤ c_max
  have h_cmax_ge : padicValNat 2 (Nat.choose (2 * n + 1) (i + 1)) ≤ c_max n := by
    unfold c_max
    exact Finset.le_sup (f := fun j => padicValNat 2 (Nat.choose (2 * n + 1) j))
      (Finset.mem_range.mpr (by omega))
  -- From h_v2fm (which uses ℕ subtraction), we need the subtraction doesn't underflow.
  -- h_v2fm says: v₂((i+1)!) + v₂((M-i-1)!) = v₂(M!) - v₂(C(M,i+1))
  -- This was proved by v2_factorial_mul which rearranges padicValNat_factorial_sum,
  -- so the subtraction is valid (v₂(C(M,i+1)) ≤ v₂(M!)).
  -- We need: v₂((M-i)!) + v₂((i+1)!) ≥ v₂(M!) - c_max
  -- From h_Mi_ge: v₂((M-i)!) ≥ v₂((M-i-1)!)
  -- From h_v2fm: v₂((i+1)!) + v₂((M-i-1)!) = v₂(M!) - v₂(C(M,i+1))
  -- So v₂((M-i)!) + v₂((i+1)!) ≥ v₂((M-i-1)!) + v₂((i+1)!) = v₂(M!) - v₂(C(M,i+1))
  -- And from h_cmax_ge: v₂(C(M,i+1)) ≤ c_max, so v₂(M!) - v₂(C(M,i+1)) ≥ v₂(M!) - c_max
  -- Also need: v₂(C(M,i+1)) ≤ v₂(M!) so the ℕ subtraction in h_v2fm doesn't underflow.
  have h_no_underflow : padicValNat 2 ((i + 1).factorial) + padicValNat 2 ((2 * n + 1 - i - 1).factorial) ≤ padicValNat 2 (2 * n + 1).factorial := by
    have := padicValNat_factorial_sum 2 (i + 1) (2 * n + 1 - i - 1)
    rw [h_sum] at this; omega
  -- Unfold abbreviations for omega
  change padicValNat 2 (2 * n).factorial + padicValNat 2 (2 * n + 1 - i).factorial +
    padicValNat 2 (i + 1).factorial ≥
    padicValNat 2 (2 * n).factorial + padicValNat 2 (2 * n + 1).factorial - c_max n
  omega

/-- v₂(cont(A_n)) ≥ v₂(cont(G)) + 1.
    Paper line 1313: all A coefficients even + each A/2 ≥ cont(G).
    Proof: Factor A_n = C(2)·A_half (every A_n coeff is even by two_dvd_A_n_coeff).
    Then mvContent(A_n) = 2·mvContent(A_half) by mvContent_C_mul.
    Show 2^target | A_half.coeff m for all m where target = v₂(cont(G)).
    Each A_half coefficient equals (A_n coeff)/2. Since each scalar_AB(n,i)
    is divisible by 2^(target+1) — using v₂(2n+1−i) ≥ 1 for odd i, the
    non-power-of-2 hypothesis for the centre i = n, and the pairing structure
    for even i ≠ n — we get 2^(target+1) | A_n.coeff m, hence
    2^target | (A_n.coeff m)/2 = A_half.coeff m. -/
theorem v2_content_A_ge (n : ℕ) (hn : 1 ≤ n)
    (hA_ne : mvContent (A_n n) ≠ 0)
    (h_not_pow2 : ¬ ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K) :
    padicValNat 2 (mvContent (G_poly_loc n)) + 1 ≤
      padicValNat 2 (mvContent (A_n n)) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [v2_content_G n hn]
  set target := padicValNat 2 (N_val n).factorial + padicValNat 2 (M_val n).factorial -
    c_max n with h_target_def
  suffices h_dvd : 2 ^ (target + 1) ∣ mvContent (A_n n) by
    exact (padicValNat_dvd_iff_le hA_ne).mp h_dvd
  -- Factor: A_n = C(2) · A_half, content = 2 · content(A_half)
  set A_half : MvPolynomial ℕ ℤ := Finsupp.mapRange (· / 2) (by simp) (A_n n)
  have hA_half_coeff : ∀ m, A_half.coeff m = (A_n n).coeff m / 2 :=
    fun m => Finsupp.mapRange_apply (hf := by simp)
  have hA_eq : A_n n = MvPolynomial.C 2 * A_half := by
    ext m; rw [MvPolynomial.coeff_C_mul, hA_half_coeff]
    exact (Int.mul_ediv_cancel' (two_dvd_A_n_coeff n hn m)).symm
  have h_content_eq : mvContent (A_n n) = 2 * mvContent A_half := by
    rw [hA_eq, mvContent_C_mul]; simp
  rw [h_content_eq, show 2 ^ (target + 1) = 2 * 2 ^ target from by ring]
  apply Nat.mul_dvd_mul_left
  -- Show 2^target | every A_half coefficient
  -- (Inline the argument of dvd_mvContent_of_dvd_coeffs' since it's defined later in the file.)
  suffices h_coeff_dvd : ∀ m, ((2 ^ target : ℕ) : ℤ) ∣ A_half.coeff m by
    unfold mvContent
    apply Finset.dvd_gcd
    intro m _
    exact Int.natAbs_dvd_natAbs.mpr (h_coeff_dvd m)
  intro m; rw [hA_half_coeff]
  -- Suffices: 2^(target+1) | (A_n n).coeff m, then dividing by 2 gives our goal.
  suffices h_strong : ((2 ^ (target + 1) : ℕ) : ℤ) ∣ (A_n n).coeff m by
    have h2 := two_dvd_A_n_coeff n hn m
    have h_exact : (A_n n).coeff m = 2 * ((A_n n).coeff m / 2) :=
      (Int.mul_ediv_cancel' h2).symm
    rw [show ((2 ^ (target + 1) : ℕ) : ℤ) = 2 * ((2 ^ target : ℕ) : ℤ) from by push_cast; ring]
      at h_strong
    rw [h_exact] at h_strong
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h_strong
  -- 2^(target+1) | (A_n n).coeff m via the scalar bounds + pairing argument.
  -- Each scalar s_i = (-1)^i · scalar_AB(n,i) satisfies 2^target | s_i
  -- (from v2_A_half_ge_content_G). The A_n coeff at m is Σ_i s_i · δ(mono(i), m).
  -- Off-centre pairs (i, 2n-i) contribute s_i + s_{2n-i} = 2·s_i (by alpha_beta_symm),
  -- so 2^(target+1) | paired contribution. The centre term s_n satisfies
  -- 2^(target+1) | s_n by the following argument:
  --   scalar_AB(n,n) = (2n)!·((n+1)!)² has v₂ = v₂(N!) + 2·v₂((n+1)!).
  --   Need 2·v₂((n+1)!) ≥ v₂(M!) - c_max + 1 = v₂((n+1)!) + v₂(n!) + v₂(C(M,n+1)) - c_max + 1.
  --   This reduces to v₂(n+1) ≥ v₂(C(M,n+1)) - c_max + 1, which holds because:
  --   • For odd n: v₂(n+1) ≥ 1 and v₂(C(M,n+1)) ≤ c_max.
  --   • For even n with n+2 not a power of 2: c_max > v₂(C(M,n+1))
  --     (a combinatorial fact about binary carry counts, using h_not_pow2).
  -- Apply the pairing lemma from CoeffExtract.lean.
  -- Rewrite 2^(target+1) = 2 * 2^target for the paired-sum lemma.
  have h_cast : ((2 ^ (target + 1) : ℕ) : ℤ) = 2 * ((2 ^ target : ℕ) : ℤ) := by
    push_cast; ring
  rw [h_cast]
  -- A_n n unfolds to the exact sum form expected by dvd_coeff_paired_sum.
  exact dvd_coeff_paired_sum (2 * n)
    (fun i => (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) * (β n i : ℤ))
    ((2 ^ target : ℕ) : ℤ)
    -- Goal 1 (symmetry): c i = c (2n - i).
    -- Uses alpha_beta_symm, Nat.choose_symm, and (-1)^(2n-i) = (-1)^i.
    (by
      intro i hi
      -- (-1)^(2n-i) = (-1)^i because 2n is even.
      have h_neg1 : (-1 : ℤ) ^ (2 * n - i) = (-1 : ℤ) ^ i := by
        have hni : (-1 : ℤ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
        apply mul_right_cancel₀ hni
        rw [← pow_add, show 2 * n - i + i = 2 * n from Nat.sub_add_cancel hi,
            ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
            pow_mul, neg_one_sq, one_pow]
      -- scalar_AB(n,i) = scalar_AB(n, 2n-i) by alpha_beta_symm.
      have h_sc : (scalar_AB n i : ℤ) = (scalar_AB n (2 * n - i) : ℤ) := by
        exact_mod_cast alpha_beta_symm n i hi
      -- Rewrite both sides as (-1)^· * ↑(scalar_AB n ·) and conclude.
      -- h_neg1 : (-1)^i = (-1)^(2n-i), h_sc : scalar_AB(n,i) = scalar_AB(n,2n-i)
      -- scalar_AB n i = C(2n,i) * α(n,i) * β(n,i) (definition)
      -- So (-1)^i * scalar_AB(n,i) = (-1)^(2n-i) * scalar_AB(n,2n-i)
      -- which unfolds to the goal.
      have : (-1 : ℤ) ^ i * ↑(scalar_AB n i) =
             (-1 : ℤ) ^ (2 * n - i) * ↑(scalar_AB n (2 * n - i)) := by
        rw [h_neg1, h_sc]
      simp only [scalar_AB] at this
      push_cast [Nat.cast_mul] at this ⊢
      linarith)
    -- Goal 2 (base divisibility): (2^target : ℤ) ∣ c i.
    -- Uses v2_A_half_ge_content_G: v₂(scalar_AB(n,i)) ≥ target.
    (by
      intro i hi
      have hv2 := v2_A_half_ge_content_G n hn i hi
      -- v₂(scalar_AB n i) ≥ target ⟹ 2^target ∣ scalar_AB n i.
      have h_dvd_nat : 2 ^ target ∣ scalar_AB n i := by
        have h_pos : 0 < scalar_AB n i := by
          rw [scalar_AB_formula n i hi]; positivity
        exact (padicValNat_dvd_iff_le h_pos.ne').mpr hv2
      -- Lift to ℤ and factor out the (-1)^i unit.
      have h_dvd_int : ((2 ^ target : ℕ) : ℤ) ∣ (scalar_AB n i : ℤ) :=
        Int.natCast_dvd_natCast.mpr h_dvd_nat
      -- c i = (-1)^i * ↑(scalar_AB n i), and (-1)^i is a unit.
      show ((2 ^ target : ℕ) : ℤ) ∣
        (-1 : ℤ) ^ i * ↑(Nat.choose (2 * n) i) * ↑(α n i) * ↑(β n i)
      have : ((-1 : ℤ) ^ i * ↑(Nat.choose (2 * n) i) * ↑(α n i) * ↑(β n i)) =
        (-1 : ℤ) ^ i * ↑(scalar_AB n i) := by
        simp [scalar_AB]; push_cast; ring
      rw [this]
      exact dvd_mul_of_dvd_right h_dvd_int _)
    -- Goal 3 (centre): (2 * 2^target : ℤ) ∣ c (n) when 2*n is even.
    (by
      intro _
      have h_sab_ne : scalar_AB n n ≠ 0 := by
        unfold scalar_AB α β
        exact Nat.mul_ne_zero
          (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne'
            (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne'))
          (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      have h_choose_center : padicValNat 2 (Nat.choose (M_val n) n) ≤ c_max n := by
        unfold c_max
        exact Finset.le_sup
          (f := fun j => padicValNat 2 (Nat.choose (2 * n + 1) j))
          (Finset.mem_range.mpr (by omega))
      have h_M_fact :
          padicValNat 2 (M_val n).factorial =
            padicValNat 2 n.factorial + padicValNat 2 (n + 1).factorial +
              padicValNat 2 (Nat.choose (M_val n) n) := by
        have hsum : n + (n + 1) = 2 * n + 1 := by
          simp [Nat.two_mul, add_comm, add_left_comm, add_assoc]
        simpa [M_val, hsum, add_comm, add_left_comm, add_assoc] using
          (padicValNat_factorial_sum 2 n (n + 1)).symm
      have h_sab_v2 :
          padicValNat 2 (scalar_AB n n) =
            padicValNat 2 (N_val n).factorial + 2 * padicValNat 2 (n + 1).factorial := by
        have h_sab_form : scalar_AB n n =
            (2 * n).factorial * (n + 1).factorial * (n + 1).factorial := by
          rw [scalar_AB_formula n n (by omega)]
          rw [show 2 * n + 1 - n = n + 1 by omega]
        calc
          padicValNat 2 (scalar_AB n n) =
              padicValNat 2 ((2 * n).factorial * (n + 1).factorial * (n + 1).factorial) := by
                rw [h_sab_form]
          _ = padicValNat 2 ((2 * n).factorial * (n + 1).factorial) +
                padicValNat 2 (n + 1).factorial := by
                rw [show (2 * n).factorial * (n + 1).factorial * (n + 1).factorial =
                    ((2 * n).factorial * (n + 1).factorial) * (n + 1).factorial by ring]
                rw [padicValNat.mul (by positivity) (Nat.factorial_pos _).ne']
          _ = padicValNat 2 (N_val n).factorial + 2 * padicValNat 2 (n + 1).factorial := by
                rw [padicValNat.mul (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne']
                ring
      have h_center_val : target + 1 ≤ padicValNat 2 (scalar_AB n n) := by
        unfold target
        rw [h_sab_v2]
        rw [h_M_fact]
        have h_cmax_le_fact : c_max n ≤ padicValNat 2 (M_val n).factorial := by
          unfold c_max
          refine Finset.sup_le ?_
          intro j hj
          have hj_le : j ≤ M_val n := by
            have hj' : j < 2 * n + 2 := Finset.mem_range.mp hj
            simpa [M_val] using Nat.lt_succ_iff.mp hj'
          have hchoose_div : Nat.choose (M_val n) j ∣ (M_val n).factorial := by
            refine ⟨j.factorial * (M_val n - j).factorial, ?_⟩
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (Nat.choose_mul_factorial_mul_factorial hj_le).symm
          have hpow_choose : (2 : ℕ) ^ padicValNat 2 (Nat.choose (M_val n) j) ∣
              Nat.choose (M_val n) j := by
            simpa using (pow_padicValNat_dvd (p := 2) (n := Nat.choose (M_val n) j))
          have hpow_fact : (2 : ℕ) ^ padicValNat 2 (Nat.choose (M_val n) j) ∣
              (M_val n).factorial := dvd_trans hpow_choose hchoose_div
          exact (padicValNat_dvd_iff_le (Nat.factorial_pos _).ne').mp hpow_fact
        by_cases hn_even : Even n
        · have h_choose_strict : padicValNat 2 (Nat.choose (M_val n) n) + 1 ≤ c_max n := by
            exact Nat.succ_le_of_lt (centre_not_max n hn hn_even h_not_pow2)
          have h_u_pos : 1 ≤ padicValNat 2 n.factorial := by
            have h2_le_n : 2 ≤ n := by
              rcases hn_even with ⟨k, rfl⟩
              omega
            have h2_dvd : (2 : ℕ) ∣ n.factorial := by
              exact Nat.dvd_factorial (by decide : 0 < 2) h2_le_n
            have hpow : (2 : ℕ) ^ 1 ∣ n.factorial := by
              simpa using h2_dvd
            exact (padicValNat_dvd_iff_le (Nat.factorial_pos _).ne').mp hpow
          have h_mono : padicValNat 2 n.factorial ≤ padicValNat 2 (n + 1).factorial :=
            v2_factorial_le_succ n
          have h_core :
              padicValNat 2 n.factorial + padicValNat 2 (Nat.choose (M_val n) n) -
                  c_max n + 1 ≤
                padicValNat 2 (n + 1).factorial :=
            center_even_arith _ _ _ _ h_u_pos h_mono h_choose_strict
          omega
        · have hn_odd : Odd n := by
            rcases Nat.even_or_odd n with h | h
            · exact False.elim (hn_even h)
            · exact h
          have h_n1_dvd : (2 : ℕ) ∣ n + 1 := by
            rcases hn_odd with ⟨k, hk⟩
            refine ⟨k + 1, ?_⟩
            rw [hk]
            omega
          have h_mono' : padicValNat 2 n.factorial + 1 ≤ padicValNat 2 (n + 1).factorial :=
            v2_factorial_succ_add_one n h_n1_dvd
          have h_choose : padicValNat 2 (Nat.choose (M_val n) n) ≤ c_max n := h_choose_center
          have h_core :
              padicValNat 2 n.factorial + padicValNat 2 (Nat.choose (M_val n) n) -
                  c_max n + 1 ≤
                padicValNat 2 (n + 1).factorial :=
            center_odd_arith _ _ _ _ h_mono' h_choose
          omega
      have h_dvd_nat : 2 ^ (target + 1) ∣ scalar_AB n n :=
        (padicValNat_dvd_iff_le h_sab_ne).mpr h_center_val
      have h_dvd_int : ((2 ^ (target + 1) : ℕ) : ℤ) ∣ (scalar_AB n n : ℤ) :=
        Int.natCast_dvd_natCast.mpr h_dvd_nat
      have h_coeff_eq :
          ((fun i => (-1 : ℤ) ^ i * ↑((2 * n).choose i) * ↑(α n i) * ↑(β n i)) (2 * n / 2)) =
            (-1 : ℤ) ^ n * (scalar_AB n n : ℤ) := by
        have h_idx : 2 * n / 2 = n := by omega
        have h_scalar : (scalar_AB n n : ℤ) =
            ↑((2 * n).choose n) * ↑(α n n) * ↑(β n n) := by
          rfl
        rw [h_idx]
        rw [h_scalar]
        ring
      rw [h_coeff_eq]
      have h_pow : ((2 ^ (target + 1) : ℕ) : ℤ) = 2 * ((2 ^ target : ℕ) : ℤ) := by
        push_cast
        omega
      rw [← h_pow]
      exact h_dvd_int.mul_left ((-1 : ℤ) ^ n))
    m

/-! ## Step 5.5 continued: Reverse inequality and equality (L1337–1341)

Paper: "the corresponding off-centre A_n-coefficient at i = j₀ has
v₂ = 1 + v₂(N!) + v₂(M!) − v₂(C(M,j₀+1))
   = 1 + v₂(N!) + v₂(M!) − v₂(C(M,j₀))    [consec pair]
   = 1 + v₂(cont(G))."
Showing v₂(cont(A_n)) ≤ v₂(cont(G)) + 1.
Combined with ≥: v₂(cont(A_n)) = v₂(cont(G)) + 1.
-/

/-- v₂(cont(A_n)) ≤ v₂(cont(G)) + 1 (via witness j₀).
    Paper lines 1337–1340.
    The A_n-coefficient at the even witness j₀ (from c_max_at_even)
    has v₂ = 1 + v₂(cont(G)), providing the upper bound on cont(A_n). -/
theorem v2_content_A_le (n : ℕ) (hn : 1 ≤ n)
    (hA_ne : mvContent (A_n n) ≠ 0)
    (h_not_pow2 : ¬ ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K) :
    padicValNat 2 (mvContent (A_n n)) ≤
      padicValNat 2 (mvContent (G_poly_loc n)) + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  rcases c_max_at_even n hn with ⟨j, hj_le, hj_even, hj_eq⟩
  have hj_ne_n : j ≠ n := by
    intro hjn
    have hn_even : Even n := by
      simpa [hjn] using hj_even
    have hlt : padicValNat 2 (Nat.choose (M_val n) n) < c_max n := by
      have hlt0 := centre_not_max n hn hn_even h_not_pow2
      simpa [c_max, M_val] using hlt0
    have heq : padicValNat 2 (Nat.choose (M_val n) n) = c_max n := by
      simpa [M_val, hjn] using hj_eq
    have hbad : padicValNat 2 (Nat.choose (M_val n) n) <
        padicValNat 2 (Nat.choose (M_val n) n) := by
      simpa [heq] using hlt
    exact Nat.lt_irrefl _ hbad
  have hchoose_center :
      padicValNat 2 (Nat.choose (M_val n) n) ≤ c_max n := by
    exact le_of_lt_or_eq (lt_or_eq_of_le (Finset.le_sup
      (f := fun j => padicValNat 2 (Nat.choose (2 * n + 1) j))
      (Finset.mem_range.mpr (by omega))))
  let i : ℕ := if j < n then j else 2 * n - j
  have hi_lt : i < n := by
    dsimp [i]
    by_cases hjlt : j < n
    · simpa [hjlt]
    · have hjge : n ≤ j := le_of_not_gt hjlt
      have hjgt : n < j := lt_of_le_of_ne hjge (by simpa [eq_comm] using hj_ne_n)
      have hlt : 2 * n - j < n := by omega
      simpa [hjlt] using hlt
  have hi_even : Even i := by
    dsimp [i]
    by_cases hjlt : j < n
    · simpa [hjlt] using hj_even
    · have hjge : n ≤ j := le_of_not_gt hjlt
      have hjgt : n < j := lt_of_le_of_ne hjge (by simpa [eq_comm] using hj_ne_n)
      rcases hj_even with ⟨r, rfl⟩
      have hr_le : r ≤ n := by
        have : 2 * r ≤ 2 * n := by simpa [Nat.two_mul] using hj_le
        omega
      refine ⟨n - r, ?_⟩
      have h_if : (if r + r < n then r + r else 2 * n - (r + r)) = 2 * n - (r + r) := by
        simp [hjlt, Nat.two_mul]
      rw [h_if]
      simpa [Nat.two_mul] using (Nat.mul_sub_left_distrib 2 n r).symm
  have hchoose_eq :
      padicValNat 2 (Nat.choose (M_val n) (i + 1)) = c_max n := by
    dsimp [i]
    by_cases hjlt : j < n
    · rcases hj_even with ⟨r, rfl⟩
      have hjlt' : r + r < n := by simpa [Nat.two_mul] using hjlt
      have hpair := v2_consec_pair n r (by omega)
      have hpair' :
          padicValNat 2 (Nat.choose (M_val n) (r + r + 1)) =
            padicValNat 2 (Nat.choose (M_val n) (r + r)) := by
        simpa [M_val, Nat.two_mul, add_comm, add_left_comm, add_assoc] using hpair.symm
      have hj_eq' : padicValNat 2 (Nat.choose (M_val n) (r + r)) = c_max n := by
        simpa [M_val, Nat.two_mul] using hj_eq
      simpa [Nat.two_mul, hjlt'] using hpair'.trans hj_eq'
    · have hjgt : n < j := by omega
      have hsymm : Nat.choose (M_val n) (2 * n - j + 1) = Nat.choose (M_val n) j := by
        have hleM : j ≤ M_val n := by exact le_trans hj_le (Nat.le_succ _)
        have hcomp : M_val n - j = 2 * n - j + 1 := by
          unfold M_val; omega
        rw [← hcomp]
        exact Nat.choose_symm hleM
      have hj_eq' : padicValNat 2 (Nat.choose (M_val n) j) = c_max n := by
        simpa [M_val, Nat.two_mul] using hj_eq
      simpa [hjlt, hsymm] using hj_eq'
  have hcoeff_eq :
      (A_n n).coeff (Finsupp.single i 1 + Finsupp.single (2 * n - i) 1) =
        (-1 : ℤ) ^ i * (2 * (scalar_AB n i : ℤ)) := by
    exact A_n_offcenter_coeff n i hi_lt
  have hcoeff_val :
      padicValNat 2 (Int.natAbs
        ((A_n n).coeff (Finsupp.single i 1 + Finsupp.single (2 * n - i) 1))) =
      padicValNat 2 (2 * scalar_AB n i) := by
    rw [hcoeff_eq]
    simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, Int.natAbs_natCast]
  have hcoeff_ne :
      Int.natAbs ((A_n n).coeff (Finsupp.single i 1 + Finsupp.single (2 * n - i) 1)) ≠ 0 := by
    have hpos : 0 < 2 * scalar_AB n i := by
      have hsc : 0 < scalar_AB n i := by
        rw [scalar_AB_formula n i (by omega)]
        positivity
      omega
    have h2ne_nat : 2 * scalar_AB n i ≠ 0 := Nat.ne_of_gt hpos
    have h2ne_int : (2 : ℤ) * (scalar_AB n i : ℤ) ≠ 0 := by
      exact_mod_cast h2ne_nat
    rw [hcoeff_eq]
    have hsign_ne : ((-1 : ℤ) ^ i) ≠ 0 := by norm_num
    exact Int.natAbs_ne_zero.mpr (mul_ne_zero hsign_ne h2ne_int)
  have hA_bound :
      padicValNat 2 (mvContent (A_n n)) ≤
        padicValNat 2 (Int.natAbs ((A_n n).coeff (Finsupp.single i 1 + Finsupp.single (2 * n - i) 1))) := by
    exact (padicValNat_dvd_iff_le hcoeff_ne).mp
      (dvd_trans (pow_padicValNat_dvd (p := 2) (n := mvContent (A_n n)))
        (Int.natAbs_dvd_natAbs.mpr (mvContent_dvd_coeff (A_n n)
          (Finsupp.single i 1 + Finsupp.single (2 * n - i) 1))))
  have htarget :
      padicValNat 2 (Int.natAbs ((A_n n).coeff (Finsupp.single i 1 + Finsupp.single (2 * n - i) 1))) =
        padicValNat 2 (mvContent (G_poly_loc n)) + 1 := by
    rw [hcoeff_val]
    have h_off :=
      v2_A_offcenter_even n i hn hi_lt hi_even
    rw [hchoose_eq] at h_off
    have h_cmax_le : c_max n ≤ padicValNat 2 (N_val n).factorial +
        padicValNat 2 (M_val n).factorial := by
      have h_sup : c_max n ≤ padicValNat 2 (M_val n).factorial := by
        unfold c_max
        refine Finset.sup_le ?_
        intro j hj
        have hj_le : j ≤ M_val n := by
          change j ≤ 2 * n + 1
          have hj_lt : j < 2 * n + 2 := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (Finset.mem_range.mp hj)
          exact Nat.le_of_lt_succ hj_lt
        have h_choose_dvd : Nat.choose (M_val n) j ∣ (M_val n).factorial := by
          refine ⟨j.factorial * (M_val n - j).factorial, ?_⟩
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (Nat.choose_mul_factorial_mul_factorial hj_le).symm
        have h_pow_choose : 2 ^ padicValNat 2 (Nat.choose (M_val n) j) ∣ Nat.choose (M_val n) j := by
          simpa using (pow_padicValNat_dvd (p := 2) (n := Nat.choose (M_val n) j))
        have h_dvd : 2 ^ padicValNat 2 (Nat.choose (M_val n) j) ∣ (M_val n).factorial := by
          exact dvd_trans h_pow_choose h_choose_dvd
        exact (padicValNat_dvd_iff_le (Nat.factorial_pos _).ne').mp h_dvd
      exact le_trans h_sup (Nat.le_add_left _ _)
    have h_assoc :
        1 + (padicValNat 2 (N_val n).factorial + padicValNat 2 (M_val n).factorial) -
          c_max n =
        1 + (padicValNat 2 (N_val n).factorial + padicValNat 2 (M_val n).factorial -
          c_max n) := by
      simpa using (Nat.add_sub_assoc h_cmax_le 1)
    have h_off' :
        padicValNat 2 (2 * scalar_AB n i) =
          1 + (padicValNat 2 (N_val n).factorial + padicValNat 2 (M_val n).factorial -
            c_max n) := by
      have h_off'' :
          padicValNat 2 (2 * scalar_AB n i) =
            1 + (padicValNat 2 (N_val n).factorial + padicValNat 2 (M_val n).factorial) -
              c_max n := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_off
      exact h_off''.trans h_assoc
    simpa [v2_content_G n hn, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_off'
  exact le_trans hA_bound htarget.le

/-- Main equality: v₂(cont(A_n)) = v₂(cont(G)) + 1.
    Paper line 1341: combining ≥ and ≤. -/
theorem v2_content_A_eq_G_plus_one (n : ℕ) (hn : 1 ≤ n)
    (hA_ne : mvContent (A_n n) ≠ 0)
    (h_not_pow2 : ¬ ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K) :
    padicValNat 2 (mvContent (A_n n)) =
      padicValNat 2 (mvContent (G_poly_loc n)) + 1 := by
  exact Nat.le_antisymm (v2_content_A_le n hn hA_ne h_not_pow2)
    (v2_content_A_ge n hn hA_ne h_not_pow2)

/-! ## Step 5.7: Case characterization (L1297, used at L1344)

Paper: "This case [A] occurs whenever n+2 is not a power of 2."
If n+2 ≠ 2^k: v₂(cont(A)) = v₂(cont(G))+1, so cont(G)² ≠ cont(A)².
Contrapositive for Case B.
-/

/-- When n+2 is not a power of 2, the 2-adic valuations of cont(G)² and cont(A)²
    are distinct. Paper: "This case [A] occurs whenever n+2 is not a power of 2."

    Specifically, v₂(cont(A)²) = 2*(v₂(cont(G))+1) = 2*v₂(cont(G)) + 2
    while v₂(cont(G)²) = 2*v₂(cont(G)), so they differ by 2. -/
theorem case_A_of_not_pow2 (n : ℕ) (hn : 1 ≤ n)
    (hA_ne : mvContent (A_n n) ≠ 0)
    (hG_ne : mvContent (G_poly_loc n) ≠ 0)
    (_h_not_pow2 : ¬ ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K) :
    padicValNat 2 (mvContent (G_poly_loc n) ^ 2) ≠
      padicValNat 2 (mvContent (A_n n) ^ 2) := by
  -- Note: _h_not_pow2 is needed to ensure v2_content_A_eq_G_plus_one applies
  -- (the equality v₂(cont(A)) = v₂(cont(G)) + 1 holds when n+2 ≠ 2^k).
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [sq, sq, padicValNat.mul hG_ne hG_ne, padicValNat.mul hA_ne hA_ne]
  rw [v2_content_A_eq_G_plus_one n hn hA_ne _h_not_pow2]
  omega

/-- Forward direction of Case B characterization:
    if v₂(cont(G)²) = v₂(cont(A)²), then n+2 is a power of 2.
    Paper: contrapositive of case_A_of_not_pow2. -/
theorem case_B_forward (n : ℕ) (hn : 1 ≤ n)
    (hA_ne : mvContent (A_n n) ≠ 0)
    (hG_ne : mvContent (G_poly_loc n) ≠ 0)
    (h_eq : padicValNat 2 (mvContent (G_poly_loc n) ^ 2) =
      padicValNat 2 (mvContent (A_n n) ^ 2)) :
    ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K := by
  by_contra h_contra
  exact case_A_of_not_pow2 n hn hA_ne hG_ne h_contra h_eq

/-- Helper: v₂(content(A_n)) = v₂(scalar_AB(n,n)) when n+2 = 2^K.
    The centre A coefficient (at monomial X_n²) has v₂ = v₂(scalar_AB(n,n)),
    which is the minimum among all A coefficients. Off-centre coefficients
    are 2 * scalar_AB(n,i) with v₂(scalar_AB(n,i)) > v₂(scalar_AB(n,n))
    by scalar_AB_central_min, so they have strictly higher v₂. -/
theorem v2_content_A_eq_scalar_AB (n K : ℕ) (hK : 2 ≤ K) (hn : n + 2 = 2 ^ K)
    (hA_ne : mvContent (A_n n) ≠ 0) :
    padicValNat 2 (mvContent (A_n n)) = padicValNat 2 (scalar_AB n n) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hn_pos : 1 ≤ n := by
    rcases K, hK with ⟨_ | _ | K, hK⟩ <;> omega
  apply Nat.le_antisymm
  · -- Upper bound: v₂(cont(A)) ≤ v₂(scalar_AB(n,n))
    -- Use evaluation: eval(A_n, δ_n) = (-1)^n * scalar_AB(n,n)
    -- where δ_n(j) = if j = n then 1 else 0.
    set δ_n : ℕ → ℤ := fun j => if j = n then 1 else 0
    -- Step 1: Content divides evaluation (general fact for any MvPolynomial)
    have h_cont_dvd_eval : (mvContent (A_n n) : ℤ) ∣ MvPolynomial.eval δ_n (A_n n) := by
      rw [MvPolynomial.eval_eq]
      exact Finset.dvd_sum fun d _ =>
        dvd_mul_of_dvd_left (mvContent_dvd_coeff _ d) _
    -- Step 2: Compute eval(A_n, δ_n) = (-1)^n * scalar_AB(n,n)
    have h_eval : MvPolynomial.eval δ_n (A_n n) = (-1 : ℤ) ^ n * (scalar_AB n n : ℤ) := by
      simp only [A_n, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      -- After simp, the goal should be a sum where each term involves δ_n(i) * δ_n(2n-i).
      -- Only the i=n term survives. Use Finset.sum_eq_single.
      rw [Finset.sum_eq_single n]
      · -- The i=n term: (-1)^n * C(2n,n) * α(n,n) * β(n,n) * δ_n(n) * δ_n(n)
        simp only [δ_n, if_pos rfl, mul_one, show 2 * n - n = n from by omega,
          scalar_AB]; push_cast; ring
      · -- For i ≠ n: term = 0 (since δ_n(i) = 0 or δ_n(2n-i) = 0)
        intro i _ hi_ne
        simp only [δ_n, hi_ne, if_false, zero_mul, mul_zero]
      · -- n ∉ range: contradiction
        intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    -- Step 3: |eval| = scalar_AB(n,n)
    have h_eval_abs : Int.natAbs (MvPolynomial.eval δ_n (A_n n)) = scalar_AB n n := by
      rw [h_eval, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
          one_pow, one_mul, Int.natAbs_natCast]
    -- Step 4: scalar_AB(n,n) ≠ 0
    have h_sAB_ne : scalar_AB n n ≠ 0 := by
      unfold scalar_AB α β
      exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne'
        (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne'))
        (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
    -- Step 5: content | scalar_AB, so v₂(content) ≤ v₂(scalar_AB)
    have h_dvd_nat : mvContent (A_n n) ∣ scalar_AB n n := by
      rw [← h_eval_abs]
      exact Int.natAbs_dvd_natAbs.mpr h_cont_dvd_eval
    exact (padicValNat_dvd_iff_le h_sAB_ne).mp
      (dvd_trans pow_padicValNat_dvd h_dvd_nat)
  · -- Lower bound: v₂(scalar_AB(n,n)) ≤ v₂(cont(A))
    -- Every A_n coefficient is divisible by 2^(e_central 2 n) = 2^v₂(scalar_AB(n,n)).
    -- Same proof as coeff_A_n_dvd_odd but for p=2.
    have h_scalar_div : ∀ i ∈ Finset.range (2 * n + 1),
        ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
          (α n i : ℤ) * (β n i : ℤ)) := by
      intro i hi
      have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h_dvd_nat : 2 ^ e_central 2 n ∣ scalar_AB n i := by
        by_cases hin : i = n
        · rw [hin]; exact p_pow_dvd_scalar_AB 2 n
        · have h_lt := scalar_AB_central_min 2 K (by omega) n hn i hi' hin
          rw [e_central_eq 2 n]
          exact dvd_trans (pow_dvd_pow 2 (by omega)) pow_padicValNat_dvd
      have h_dvd_int : ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ (scalar_AB n i : ℤ) :=
        Int.natCast_dvd_natCast.mpr h_dvd_nat
      convert h_dvd_int.mul_left ((-1 : ℤ) ^ i) using 1
      simp [scalar_AB]; ring
    have h_coeff_dvd : ∀ m, ((2 ^ e_central 2 n : ℕ) : ℤ) ∣ (A_n n).coeff m := by
      intro m; unfold A_n
      have h_each : ∀ i ∈ Finset.range (2 * n + 1),
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
      exact Finset.dvd_sum fun x hx => h_each x hx
    have h_dvd_cont : 2 ^ e_central 2 n ∣ mvContent (A_n n) := by
      unfold mvContent
      apply Finset.dvd_gcd
      intro m _
      exact Int.natAbs_dvd_natAbs.mpr (h_coeff_dvd m)
    rw [show e_central 2 n = padicValNat 2 (scalar_AB n n) from e_central_eq 2 n] at h_dvd_cont
    exact (padicValNat_dvd_iff_le hA_ne).mp h_dvd_cont

/-- v₂(C(2n+1, k)) ≤ K-1 when n+2 = 2^K and k ≤ 2n+1.
    Proof: by Kummer (carry counting), position i=1 never contributes since 2n+1 is odd. -/
private lemma v2_choose_M_le (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K)
    (k : ℕ) (hk : k ≤ 2 * n + 1) :
    padicValNat 2 (Nat.choose (2 * n + 1) k) ≤ K - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  -- Use padicValNat_choose with b = K + 1
  have h_log : Nat.log 2 (2 * n + 1) < K + 1 := by
    apply Nat.log_lt_of_lt_pow (by norm_num)
    -- 2 * n + 1 < 2^(K+1) since n + 2 = 2^K, so 2n+1 = 2^(K+1) - 3
    have : 2 * n + 1 = 2 ^ (K + 1) - 3 := by
      have : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
      omega
    omega
  rw [padicValNat_choose hk h_log]
  -- The filter is a subset of Ico 2 (K+1) since i=1 never satisfies the carry condition
  -- (because 2n+1 is odd, k % 2 + (2n+1-k) % 2 = 1 < 2)
  have h_no_carry_1 : ¬ (2 ^ 1 ≤ k % 2 ^ 1 + (2 * n + 1 - k) % 2 ^ 1) := by
    simp only [pow_one]
    omega
  have h_subset : (Finset.Ico 1 (K + 1)).filter
      (fun i => 2 ^ i ≤ k % 2 ^ i + (2 * n + 1 - k) % 2 ^ i) ⊆
      Finset.Ico 2 (K + 1) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
    constructor
    · -- i ≥ 2: since i ≥ 1 (from Ico) and i ≠ 1 (since i=1 violates the carry condition)
      rcases eq_or_lt_of_le hi.1.1 with rfl | hgt
      · exact absurd hi.2 h_no_carry_1
      · exact hgt
    · exact hi.1.2
  exact le_trans (Finset.card_le_card h_subset) (by
    show (Finset.Ico 2 (K + 1)).card ≤ K - 1
    rw [show (Finset.Ico 2 (K + 1)).card = K + 1 - 2 from by simp]
    omega)

/-- v₂(C(2n+1, n)) = K - 1 when n+2 = 2^K.
    Uses C(2n+2, n+1) = 2 * C(2n+1, n) and v₂(C(2n+2, n+1)) = K. -/
private lemma v2_choose_M_center (K : ℕ) (hK : 2 ≤ K) (n : ℕ) (hn : n + 2 = 2 ^ K) :
    padicValNat 2 (Nat.choose (2 * n + 1) n) = K - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  -- C(2n+2, n+1) = C(2n+1, n+1) + C(2n+1, n) by Pascal
  -- C(2n+1, n+1) = C(2n+1, n) by symmetry (since (2n+1)-(n+1) = n)
  -- So C(2n+2, n+1) = 2 * C(2n+1, n)
  have h_sym : Nat.choose (2 * n + 1) (n + 1) = Nat.choose (2 * n + 1) n := by
    conv_lhs => rw [← Nat.choose_symm (show n + 1 ≤ 2 * n + 1 from by omega)]
    congr 1; omega
  have h_pascal : Nat.choose (2 * n + 2) (n + 1) =
      Nat.choose (2 * n + 1) (n + 1) + Nat.choose (2 * n + 1) n := by
    have := Nat.choose_succ_succ (2 * n + 1) n
    simp only [Nat.succ_eq_add_one] at this
    linarith
  have h_double : Nat.choose (2 * n + 2) (n + 1) = 2 * Nat.choose (2 * n + 1) n := by
    rw [h_pascal, h_sym]; ring
  -- v₂(C(2n+2, n+1)) = K
  have h_v2_central : padicValNat 2 (Nat.choose (2 * n + 2) (n + 1)) = K := by
    rw [show 2 * n + 2 = 2 * (2 ^ K - 1) from by omega,
        show n + 1 = 2 ^ K - 1 from by omega]
    exact padicValNat_choose_central 2 K (by omega)
  -- v₂(2 * C(2n+1, n)) = 1 + v₂(C(2n+1, n))
  have h_ne : Nat.choose (2 * n + 1) n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [h_double] at h_v2_central
  rw [padicValNat.mul (by norm_num) h_ne,
      show padicValNat 2 2 = 1 from padicValNat.self (by norm_num)] at h_v2_central
  omega

/-- Helper: v₂(content(G_poly_loc)) = v₂(scalar_AB(n,n)) when n+2 = 2^K.
    The centre G coefficient (at monomial X_n · X_{n+1}, i.e. b_formula(n,n)/2)
    has v₂ = v₂(scalar_AB(n,n)) by v2_b_center.
    Off-centre G coefficients have strictly higher v₂ by the central
    dominance of scalar_A2 and scalar_B2. -/
theorem v2_content_G_eq_scalar_AB (n K : ℕ) (hK : 2 ≤ K) (hn : n + 2 = 2 ^ K)
    (hG_ne : mvContent (G_poly_loc n) ≠ 0) :
    padicValNat 2 (mvContent (G_poly_loc n)) = padicValNat 2 (scalar_AB n n) := by
  -- G_poly_loc = B_n / 2. The B_n coefficient at monomial (k, 2n+1-k) for
  -- k ∈ [1, 2n] is b_formula(n,k). So G coefficient = b_formula(n,k) / 2.
  --
  -- By v2_b_center: v₂(|b_formula(n,n)|) = 1 + v₂(scalar_AB(n,n)).
  -- So v₂(G centre coeff) = v₂(|b_formula(n,n)|) - 1 = v₂(scalar_AB(n,n)).
  --
  -- For off-centre k ≠ n (and k ≠ n+1): scalar_A2 and scalar_B2 central
  -- dominance (scalar_A2_central_min, scalar_B2_central_min) gives
  -- v₂(|b_formula(n,k)|) > 1 + v₂(scalar_AB(n,n)), so
  -- v₂(G off-centre coeff) > v₂(scalar_AB(n,n)).
  --
  -- For k = n+1: by v2_b_k0 (with k₀ = n + 2^{K-1}), when K ≥ 2
  -- the k₀ = n+1 case (only when K=2, giving 2^{K-1}=2, k₀=n+2... actually
  -- k = n+1 needs separate treatment but central_val_eq shows
  -- scalar_AB(n,n) = scalar_A2(n,n) = scalar_B2(n,n), and the n+1 term
  -- has the same structure).
  --
  -- Therefore v₂(content(G)) = v₂(scalar_AB(n,n)).
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hn_pos : 1 ≤ n := by
    rcases K, hK with ⟨_ | _ | K, hK⟩ <;> omega
  apply Nat.le_antisymm
  · -- Upper bound: v₂(cont(G)) ≤ v₂(scalar_AB(n,n))
    -- Evaluate G at phi(n,n): f_n = 1, f_{n+1} = 1, rest = 0.
    -- eval(B_n, phi(n,n)) = b_formula(n,n) (only the center term survives in B_n_alt).
    -- Since B = 2*G (coeff-wise), eval(G, phi(n,n)) = b_formula(n,n) / 2.
    -- Content divides eval, so v₂(content) ≤ v₂(|b_formula(n,n)/2|) = v₂(scalar_AB(n,n)).
    set ph := phi n n
    -- Step 1: content divides evaluation
    have h_cont_dvd_eval : (mvContent (G_poly_loc n) : ℤ) ∣
        MvPolynomial.eval ph (G_poly_loc n) := by
      rw [MvPolynomial.eval_eq]
      exact Finset.dvd_sum fun d _ =>
        dvd_mul_of_dvd_left (mvContent_dvd_coeff _ d) _
    -- Step 2: eval(B_n, phi(n,n)) relates to b_formula via B_n_eq_alt.
    -- eval(G, phi(n,n)) = eval(B_n, phi(n,n)) / 2 since every B coeff is even.
    -- We use: 2 * eval(G, ph) = eval(B_n, ph).
    have h_two_dvd_B : ∀ m, (2 : ℤ) ∣ (B_n n).coeff m := by
      have he_b : ∀ k ∈ Finset.Icc 1 (2 * n),
          1 ≤ padicValNat 2 (Int.natAbs (b_formula n k)) := by
        intro k hk
        have hk_le : k ≤ 2 * n := (Finset.mem_Icc.mp hk).2
        have h2_dvd : (2 : ℤ) ∣ b_formula n k := by
          rw [b_formula_factored n k hk_le]
          exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) _
        have hbf_ne : b_formula n k ≠ 0 :=
          b_k_val_ne_zero n k (by omega) (Finset.mem_Icc.mp hk).1 hk_le
        exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hbf_ne)).mp
          (Int.natAbs_dvd_natAbs.mpr h2_dvd)
      intro m
      have h := coeff_B_n_dvd 2 n 1 (by omega) he_b m
      rwa [show ((2 ^ 1 : ℕ) : ℤ) = (2 : ℤ) from by norm_num] at h
    have h_B_eq_2G : ∀ m, (B_n n).coeff m = 2 * (G_poly_loc n).coeff m := by
      intro m
      rw [G_poly_loc_coeff]
      exact (Int.mul_ediv_cancel' (h_two_dvd_B m)).symm
    have h_eval_2G : MvPolynomial.eval ph (B_n n) =
        2 * MvPolynomial.eval ph (G_poly_loc n) := by
      have h2G : B_n n = MvPolynomial.C (2 : ℤ) * G_poly_loc n := by
        ext m; simp only [MvPolynomial.coeff_C_mul]; exact h_B_eq_2G m
      rw [h2G, map_mul, MvPolynomial.eval_C]
    -- Step 3: compute eval(B_n, phi(n,n)) = b_formula(n,n)
    -- From B_n_eq_alt, B_n = boundary_term + Σ_{j∈[1,n]} b_formula(n,j) * X_j * X_{2n+1-j}
    -- At phi(n,n): boundary term = 0 (needs f_0 = 0), and only j=n survives.
    have h_eval_B : MvPolynomial.eval ph (B_n n) = b_formula n n := by
      rw [B_n_eq_alt n (by omega)]
      simp only [B_n_alt, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      -- Boundary term: 2*((2n+1)!)^2 * ph(0) * ph(2n+1) = 0
      have h_bdy : (2 * ((2 * n + 1).factorial : ℤ) ^ 2) * ph 0 * ph (2 * n + 1) = 0 := by
        have hph_0 : ph 0 = 0 := by
          simp only [ph, phi]; rw [if_neg]; push_neg; exact ⟨by omega, by omega⟩
        rw [hph_0, mul_zero, zero_mul]
      -- Sum: only j=n contributes
      have h_sum : ∑ j ∈ Finset.Icc 1 n,
          (b_formula n j : ℤ) * ph j * ph (2 * n + 1 - j) =
          b_formula n n := by
        rw [Finset.sum_eq_single n]
        · have hph_n : ph n = 1 := by simp only [ph, phi]; simp
          have hph_n1 : ph (2 * n + 1 - n) = 1 := by simp only [ph, phi]; simp
          rw [hph_n, hph_n1, mul_one, mul_one]
        · intro j hj hj_ne
          have hj_bounds := Finset.mem_Icc.mp hj
          have hph_j : ph j = 0 := by
            simp only [ph, phi]; rw [if_neg]; push_neg; exact ⟨hj_ne, by omega⟩
          rw [hph_j, mul_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_Icc.mpr ⟨by omega, le_refl n⟩) h
      rw [h_bdy, zero_add, h_sum]
    -- Step 4: derive v₂(content(G)) ≤ v₂(scalar_AB(n,n))
    have h_eval_G : 2 * MvPolynomial.eval ph (G_poly_loc n) = b_formula n n := by
      linarith [h_eval_2G, h_eval_B]
    -- v₂(|b_formula(n,n)|) = 1 + v₂(scalar_AB(n,n)) by v2_b_center
    have h_v2_bf := v2_b_center K hK n hn
    -- |b_formula(n,n)| ≠ 0
    have h_bf_ne : b_formula n n ≠ 0 :=
      b_k_val_ne_zero n n (by omega) (by omega) (by omega)
    -- scalar_AB(n,n) ≠ 0
    have h_sAB_ne : scalar_AB n n ≠ 0 := by
      unfold scalar_AB α β
      exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne'
        (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne'))
        (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
    -- content(G) ∣ |eval(G, ph)| = |b_formula(n,n)/2|
    -- Since content(G) ∣ eval(G, ph) (in ℤ), content(G) ∣ |eval(G, ph)| (in ℕ)
    have h_dvd_nat : mvContent (G_poly_loc n) ∣ Int.natAbs (MvPolynomial.eval ph (G_poly_loc n)) :=
      Int.natAbs_dvd_natAbs.mpr h_cont_dvd_eval
    -- v₂(eval(G)) = v₂(|b_formula(n,n)|) - 1 = v₂(scalar_AB(n,n))
    -- Since 2 * eval(G) = b_formula(n,n) and b_formula(n,n) ≠ 0,
    -- eval(G) = b_formula(n,n) / 2 ≠ 0
    have h_eval_ne : MvPolynomial.eval ph (G_poly_loc n) ≠ 0 := by
      intro h; rw [h, mul_zero] at h_eval_G; exact h_bf_ne h_eval_G.symm
    have h_natabs_ne : Int.natAbs (MvPolynomial.eval ph (G_poly_loc n)) ≠ 0 := by
      rwa [Int.natAbs_ne_zero]
    -- v₂(2 * eval(G)) = 1 + v₂(eval(G))
    have h_v2_2eval : padicValNat 2 (Int.natAbs (2 * MvPolynomial.eval ph (G_poly_loc n))) =
        1 + padicValNat 2 (Int.natAbs (MvPolynomial.eval ph (G_poly_loc n))) := by
      rw [Int.natAbs_mul, show Int.natAbs 2 = 2 from rfl,
          padicValNat.mul (by norm_num) h_natabs_ne,
          show padicValNat 2 2 = 1 from padicValNat.self (by norm_num)]
    rw [h_eval_G] at h_v2_2eval
    -- So v₂(|eval(G)|) = v₂(|b_formula(n,n)|) - 1 = v₂(scalar_AB(n,n))
    have h_v2_eval : padicValNat 2 (Int.natAbs (MvPolynomial.eval ph (G_poly_loc n))) =
        padicValNat 2 (scalar_AB n n) := by omega
    -- Since content | |eval|, v₂(content) ≤ v₂(|eval|) = v₂(scalar_AB(n,n))
    exact (padicValNat_dvd_iff_le h_natabs_ne).mp
      (dvd_trans pow_padicValNat_dvd h_dvd_nat) |>.trans h_v2_eval.le
  · -- Lower bound: v₂(scalar_AB(n,n)) ≤ v₂(cont(G))
    -- Every B_n coefficient is divisible by 2^(1 + v₂(scalar_AB(n,n))) = 2^(1 + e_central 2 n).
    -- Hence every G coefficient = B coeff / 2 is divisible by 2^(v₂(scalar_AB(n,n))).
    -- So 2^(v₂(scalar_AB(n,n))) | content(G).
    --
    -- Use coeff_B_n_dvd with e = 1 + e_central 2 n.
    -- Need: for all k ∈ [1,2n], 1 + e_central 2 n ≤ v₂(|b_formula(n,k)|).
    -- v₂(|b_formula(n,n)|) = 1 + v₂(scalar_AB(n,n)) = 1 + e_central 2 n ✓
    -- For k ≠ n, k ≠ n+1: scalar_AB_central_min gives v₂(scalar_AB(n,k)) > v₂(scalar_AB(n,n)).
    --   b_formula_factored gives |b_formula(n,k)| = 2 * ... with v₂ ≥ 1 + v₂(scalar_AB(n,k))
    --   > 1 + v₂(scalar_AB(n,n)) = 1 + e_central 2 n. ✓ (but we need v₂(|b_formula|) not v₂(scalar_AB))
    -- For k = n+1: by symmetry b_formula(n,n+1) = ±b_formula(n,n), so same v₂. ✓
    --
    -- Actually we directly show 2^(e_central 2 n) | every G coeff.
    -- G coeff = B coeff / 2. We need 2^(e_central 2 n) | B coeff / 2,
    -- i.e., 2^(1 + e_central 2 n) | B coeff.
    -- Use coeff_B_n_dvd: need 1 + e_central 2 n ≤ v₂(|b_formula(n,k)|) for all k ∈ [1,2n].
    set e := e_central 2 n
    have he_eq : e = padicValNat 2 (scalar_AB n n) := e_central_eq 2 n
    have h_two_dvd_B : ∀ m, (2 : ℤ) ∣ (B_n n).coeff m := by
      have he_b : ∀ k ∈ Finset.Icc 1 (2 * n),
          1 ≤ padicValNat 2 (Int.natAbs (b_formula n k)) := by
        intro k hk
        have hk_le : k ≤ 2 * n := (Finset.mem_Icc.mp hk).2
        have h2_dvd : (2 : ℤ) ∣ b_formula n k := by
          rw [b_formula_factored n k hk_le]
          exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) _
        have hbf_ne : b_formula n k ≠ 0 :=
          b_k_val_ne_zero n k (by omega) (Finset.mem_Icc.mp hk).1 hk_le
        exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hbf_ne)).mp
          (Int.natAbs_dvd_natAbs.mpr h2_dvd)
      intro m
      have h := coeff_B_n_dvd 2 n 1 (by omega) he_b m
      rwa [show ((2 ^ 1 : ℕ) : ℤ) = (2 : ℤ) from by norm_num] at h
    -- Show 2^(e+1) | every B coeff
    have he_b_all : ∀ k ∈ Finset.Icc 1 (2 * n),
        e + 1 ≤ padicValNat 2 (Int.natAbs (b_formula n k)) := by
      intro k hk
      have hk_le : k ≤ 2 * n := (Finset.mem_Icc.mp hk).2
      rw [show e + 1 = 1 + e from by omega]
      -- v₂(|b_formula(n,k)|) = 1 + v₂(scalar_AB(n,k)) via b_formula_factored
      -- (when 2n+1-2k is odd, which it always is since M=2n+1)
      -- Step 1: Factor b_formula
      have hk_lo : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have h_fact := b_formula_factored n k hk_le
      -- Step 2: Compute |b_formula| = 2 * |P| where P = (2n)! * (2n+1-2k) * (2n+1-k)! * k!
      -- |2 * (-1)^k * z| = 2 * |z|
      rw [h_fact]
      rw [show Int.natAbs (2 * (-1 : ℤ) ^ k * (((2 * n).factorial : ℤ) * ((2 * ↑n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ))) =
          2 * Int.natAbs (((2 * n).factorial : ℤ) * ((2 * ↑n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ)) from by
        rw [Int.natAbs_mul, Int.natAbs_mul]
        simp [show Int.natAbs (2 : ℤ) = 2 from rfl,
              show Int.natAbs ((-1 : ℤ) ^ k) = 1 from by simp]]
      -- Now goal: 1 + e ≤ padicValNat 2 (2 * Int.natAbs (...))
      have h_P_ne : Int.natAbs (((2 * n).factorial : ℤ) * ((2 * ↑n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ)) ≠ 0 := by
        rw [Int.natAbs_ne_zero]
        apply mul_ne_zero; apply mul_ne_zero; apply mul_ne_zero
        · exact_mod_cast (Nat.factorial_pos _).ne'
        · omega  -- 2n+1-2k ≠ 0 since 2n+1 is odd
        · exact_mod_cast (Nat.factorial_pos _).ne'
        · exact_mod_cast (Nat.factorial_pos _).ne'
      rw [padicValNat.mul (by norm_num) h_P_ne,
          show padicValNat 2 2 = 1 from padicValNat.self (by norm_num)]
      -- Goal: 1 + e ≤ 1 + v₂(|P|), i.e., e ≤ v₂(|P|)
      -- Step 3: v₂(|P|) = v₂((2n)!) + v₂((2n+1-k)!) + v₂(k!) since 2n+1-2k is odd
      -- Work with divisibility directly instead of natAbs computation.
      -- We need: 2^e ∣ (2n)! * (2n+1-2k) * (2n+1-k)! * k! (as integers).
      -- Then v₂(|2 * (-1)^k * that|) = 1 + v₂(|that|) ≥ 1 + e.
      suffices h : e ≤ padicValNat 2 (Int.natAbs (((2 * n).factorial : ℤ) * ((2 * ↑n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ))) by omega
      -- The padicValNat of the natAbs equals that of the product of nat factorials
      -- since the only potentially negative factor is (2n+1-2k), and |a*b| shares v₂ with |a|*|b|.
      -- v₂(|P|) = v₂((2n)!) + v₂(|2n+1-2k|) + v₂((2n+1-k)!) + v₂(k!)
      -- = v₂((2n)!) + 0 + v₂((2n+1-k)!) + v₂(k!) since |2n+1-2k| is odd
      have h_v2_odd : padicValNat 2 (Int.natAbs ((2 * ↑n : ℤ) + 1 - 2 * ↑k)) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        by_cases hle : k ≤ n
        · -- k ≤ n: 2n+1-2k ≥ 1, so Int.natAbs = 2n+1-2k (natural)
          have : (2 * ↑n : ℤ) + 1 - 2 * ↑k = ((2 * n + 1 - 2 * k : ℕ) : ℤ) := by omega
          rw [this, Int.natAbs_natCast]; omega
        · -- k > n: 2n+1-2k < 0, so Int.natAbs = 2k-(2n+1)
          push_neg at hle
          have : (2 * ↑n : ℤ) + 1 - 2 * ↑k = -((2 * k - (2 * n + 1) : ℕ) : ℤ) := by omega
          rw [this, Int.natAbs_neg, Int.natAbs_natCast]; omega
      rw [show Int.natAbs (((2 * n).factorial : ℤ) * ((2 * ↑n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ)) =
          (2 * n).factorial * Int.natAbs ((2 * ↑n : ℤ) + 1 - 2 * ↑k) * (2 * n + 1 - k).factorial * k.factorial from by
        rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]
        simp [Int.natAbs_natCast]]
      have h_abs_ne : Int.natAbs ((2 * ↑n : ℤ) + 1 - 2 * ↑k) ≠ 0 := by
        intro h; simp [Int.natAbs_eq_zero] at h; omega
      rw [padicValNat.mul (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_pos _).ne' h_abs_ne) (Nat.factorial_pos _).ne') (Nat.factorial_pos _).ne']
      rw [padicValNat.mul (Nat.mul_ne_zero (Nat.factorial_pos _).ne' h_abs_ne) (Nat.factorial_pos _).ne']
      rw [padicValNat.mul (Nat.factorial_pos _).ne' h_abs_ne]
      rw [h_v2_odd, add_zero]
      -- Goal: e ≤ v₂((2n)!) + v₂((2n+1-k)!) + v₂(k!)
      -- e = v₂(scalar_AB(n,n)) = v₂((2n)!) + v₂((n+1)!) + v₂((n+1)!)
      rw [he_eq, scalar_AB_factorial_form n n (by omega)]
      rw [show 2 * n + 1 - n = n + 1 from by omega]
      rw [padicValNat.mul (by positivity) (by positivity : (n + 1).factorial ≠ 0)]
      rw [padicValNat.mul (by positivity : (2 * n).factorial ≠ 0) (by positivity : (n + 1).factorial ≠ 0)]
      -- Goal: v₂((2n)!) + v₂((n+1)!) + v₂((n+1)!) ≤ v₂((2n)!) + v₂((2n+1-k)!) + v₂(k!)
      -- Suffices: v₂((n+1)!) + v₂((n+1)!) ≤ v₂((2n+1-k)!) + v₂(k!)
      -- i.e., 2*v₂((n+1)!) ≤ v₂((2n+1-k)!) + v₂(k!)
      -- Use padicValNat_factorial_sum twice.
      -- First: v₂(k!) + v₂((2n+1-k)!) = v₂((2n+1)!) - v₂(C(2n+1,k))
      have h_fs_k := padicValNat_factorial_sum 2 k (2 * n + 1 - k)
      rw [show k + (2 * n + 1 - k) = 2 * n + 1 from by omega] at h_fs_k
      -- h_fs_k: v₂((2n+1)!) = v₂(k!) + v₂((2n+1-k)!) + v₂(C(2n+1,k))
      -- Second: v₂(n!) + v₂((n+1)!) = v₂((2n+1)!) - v₂(C(2n+1,n))
      have h_fs_n := padicValNat_factorial_sum 2 n (n + 1)
      rw [show n + (n + 1) = 2 * n + 1 from by omega] at h_fs_n
      -- h_fs_n: v₂((2n+1)!) = v₂(n!) + v₂((n+1)!) + v₂(C(2n+1,n))
      -- v₂(n+1) = 0 since n+1 = 2^K - 1 is odd
      have h_n1_odd : ¬ (2 ∣ (n + 1)) := by
        intro ⟨m, hm⟩
        -- n + 1 = 2m, n + 2 = 2m + 1. But n + 2 = 2^K (even for K ≥ 2).
        -- So 2m + 1 = 2^K, but 2^K is even, contradiction.
        have h2K_even : 2 ∣ 2 ^ K := dvd_pow_self 2 (show K ≠ 0 by omega)
        have : 2 ∣ n + 2 := hn ▸ h2K_even
        omega
      have h_v2_n1 : padicValNat 2 (n + 1) = 0 := padicValNat.eq_zero_of_not_dvd h_n1_odd
      -- v₂((n+1)!) = v₂(n+1) + v₂(n!) = v₂(n!)
      have h_n1_fac : padicValNat 2 (n + 1).factorial =
          padicValNat 2 n.factorial := by
        rw [Nat.factorial_succ, padicValNat.mul (by omega : n + 1 ≠ 0) (Nat.factorial_pos _).ne', h_v2_n1, zero_add]
      -- So 2*v₂((n+1)!) = v₂(n!) + v₂((n+1)!) = v₂((2n+1)!) - v₂(C(2n+1,n))
      -- And v₂(k!) + v₂((2n+1-k)!) = v₂((2n+1)!) - v₂(C(2n+1,k))
      -- Need: v₂(C(2n+1,k)) ≤ v₂(C(2n+1,n))
      have h_choose_k := v2_choose_M_le K hK n hn k (by omega)
      have h_choose_n := v2_choose_M_center K hK n hn
      -- h_choose_k: v₂(C(2n+1,k)) ≤ K-1
      -- h_choose_n: v₂(C(2n+1,n)) = K-1
      rw [h_n1_fac]
      omega
    have h_B_dvd : ∀ m, ((2 ^ (e + 1) : ℕ) : ℤ) ∣ (B_n n).coeff m :=
      coeff_B_n_dvd 2 n (e + 1) (by omega) he_b_all
    -- Therefore 2^e | every G coeff
    have h_G_dvd : ∀ m, ((2 ^ e : ℕ) : ℤ) ∣ (G_poly_loc n).coeff m := by
      intro m
      rw [G_poly_loc_coeff]
      have hB := h_B_dvd m
      have h2B := h_two_dvd_B m
      -- B.coeff m = 2 * (B.coeff m / 2) since 2 | B.coeff m
      have h_exact : (B_n n).coeff m = 2 * ((B_n n).coeff m / 2) :=
        (Int.mul_ediv_cancel' h2B).symm
      -- 2^(e+1) | B.coeff m = 2 * G.coeff m, so 2^e | G.coeff m
      have h_pow_cast : ((2 ^ (e + 1) : ℕ) : ℤ) = 2 * ((2 ^ e : ℕ) : ℤ) := by
        push_cast; ring
      rw [h_pow_cast] at hB
      rw [h_exact] at hB
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hB
    have h_dvd_cont : 2 ^ e ∣ mvContent (G_poly_loc n) := by
      unfold mvContent
      apply Finset.dvd_gcd
      intro m _
      exact Int.natAbs_dvd_natAbs.mpr (h_G_dvd m)
    rw [he_eq] at h_dvd_cont
    exact (padicValNat_dvd_iff_le hG_ne).mp h_dvd_cont

/-- Reverse direction of Case B characterization:
    if n+2 = 2^K (K ≥ 2), then v₂(cont(G)) = v₂(cont(A_n)).
    Paper line 1344–1345. Both contents equal v₂(scalar_AB(n,n)). -/
theorem case_B_reverse (n K : ℕ) (hK : 2 ≤ K) (hn : n + 2 = 2 ^ K)
    (hA_ne : mvContent (A_n n) ≠ 0)
    (hG_ne : mvContent (G_poly_loc n) ≠ 0) :
    padicValNat 2 (mvContent (G_poly_loc n)) =
      padicValNat 2 (mvContent (A_n n)) := by
  -- Both contents have v₂ equal to v₂(scalar_AB(n,n)), so they're equal.
  rw [v2_content_G_eq_scalar_AB n K hK hn hG_ne,
      v2_content_A_eq_scalar_AB n K hK hn hA_ne]

/-- Full Case B characterization:
    v₂(cont(G)²) = v₂(cont(A)²) ↔ ∃ K ≥ 2, n + 2 = 2^K.
    Paper line 1297 + line 1344. -/
theorem case_B_iff_pow2 (n : ℕ) (hn : 1 ≤ n)
    (hA_ne : mvContent (A_n n) ≠ 0)
    (hG_ne : mvContent (G_poly_loc n) ≠ 0) :
    padicValNat 2 (mvContent (G_poly_loc n) ^ 2) =
      padicValNat 2 (mvContent (A_n n) ^ 2) ↔
    ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  constructor
  · exact case_B_forward n hn hA_ne hG_ne
  · intro ⟨K, hK, hKn⟩
    rw [sq, sq, padicValNat.mul hG_ne hG_ne, padicValNat.mul hA_ne hA_ne]
    rw [case_B_reverse n K hK hKn hA_ne hG_ne]

/-! ## Auxiliary lemmas for the ultrametric argument -/

/-- Helper: if d | every coeff of f, then d | mvContent f -/
private lemma dvd_mvContent_of_dvd_coeffs' (d : ℕ) (f : MvPolynomial ℕ ℤ)
    (h : ∀ m, (d : ℤ) ∣ f.coeff m) :
    d ∣ mvContent f := by
  unfold mvContent
  apply Finset.dvd_gcd
  intro m _
  exact Int.natAbs_dvd_natAbs.mpr (h m)

/-- Helper: content(f - g) is divisible by gcd(content(f), content(g)) -/
private lemma gcd_content_dvd_content_sub' (f g : MvPolynomial ℕ ℤ) :
    Nat.gcd (mvContent f) (mvContent g) ∣ mvContent (f - g) := by
  apply dvd_mvContent_of_dvd_coeffs'
  intro m
  rw [MvPolynomial.coeff_sub]
  apply dvd_sub
  · exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) (mvContent_dvd_coeff f m)
  · exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)) (mvContent_dvd_coeff g m)

/-- content(G_loc²) = content(G_loc)² by Gauss's lemma. -/
private lemma content_G_loc_sq (n : ℕ) :
    mvContent (G_poly_loc n ^ 2) = mvContent (G_poly_loc n) ^ 2 := by
  rw [sq, mvContent_mul, sq]

/-- mvContent is preserved by injective renaming. -/
private lemma mvContent_rename' (f : ℕ → ℕ) (hf : Function.Injective f)
    (p : MvPolynomial ℕ ℤ) :
    mvContent (MvPolynomial.rename f p) = mvContent p := by
  unfold mvContent
  rw [MvPolynomial.support_rename_of_injective hf, Finset.gcd_image]
  congr 1; ext d
  simp [Function.comp, MvPolynomial.coeff_rename_mapDomain f hf]

/-- content(A_n) = content(C_n) by variable renaming. -/
private lemma content_A_eq_C' (n : ℕ) :
    mvContent (A_n n) = mvContent (C_n n) := by
  have h_rename : C_n n = MvPolynomial.rename (· + 1) (A_n n) := by
    unfold A_n C_n
    simp only [map_sum, MvPolynomial.rename_C, MvPolynomial.rename_X, map_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    congr 2
    omega
  rw [h_rename, mvContent_rename' _ (fun a b h => by omega)]

/-- content(A_n * C_n) = content(A_n)² -/
private lemma content_AC' (n : ℕ) :
    mvContent (A_n n * C_n n) = mvContent (A_n n) ^ 2 := by
  rw [mvContent_mul, content_A_eq_C', sq]

/-! ## Auxiliary lemmas connecting to the overall proof structure

These lemmas relate the local definitions to the main proof flow.
They state the key consequences needed by Steps 4 and 6.
-/

/-- When n+2 is not a power of 2 and the relevant polynomials are nonzero,
    the ultrametric case (Case A) applies and v₂(cont(H)) is even.
    This is used in Step 4 of the main proof. -/
theorem even_vp_H_of_case_A (n : ℕ) (hn : 1 ≤ n)
    (hA_ne : mvContent (A_n n) ≠ 0)
    (hG_ne : mvContent (G_poly_loc n) ≠ 0)
    (hH_ne : mvContent (H_poly_loc n) ≠ 0)
    (h_not_pow2 : ¬ ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K) :
    Even (padicValNat 2 (mvContent (H_poly_loc n))) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  -- Step 1: Get the key inequality from case_A_of_not_pow2
  have hne : padicValNat 2 (mvContent (G_poly_loc n) ^ 2) ≠
      padicValNat 2 (mvContent (A_n n) ^ 2) :=
    case_A_of_not_pow2 n hn hA_ne hG_ne h_not_pow2
  -- Step 2: Both v₂(cont(G²)) and v₂(cont(AC)) are even
  have ha_even : Even (padicValNat 2 (mvContent (G_poly_loc n ^ 2))) := by
    rw [content_G_loc_sq, sq]
    by_cases h0 : mvContent (G_poly_loc n) = 0
    · simp [h0]
    · exact ⟨_, padicValNat.mul h0 h0⟩
  have hb_even : Even (padicValNat 2 (mvContent (A_n n * C_n n))) := by
    rw [content_AC', sq]
    by_cases h0 : mvContent (A_n n) = 0
    · simp [h0]
    · exact ⟨_, padicValNat.mul h0 h0⟩
  -- Convert the inequality on squares to content inequality
  have hne' : padicValNat 2 (mvContent (G_poly_loc n ^ 2)) ≠
      padicValNat 2 (mvContent (A_n n * C_n n)) := by
    rwa [content_G_loc_sq, content_AC']
  -- Edge cases
  by_cases hg0 : G_poly_loc n ^ 2 = 0
  · have hcH : mvContent (H_poly_loc n) = mvContent (A_n n * C_n n) := by
      have : H_poly_loc n = -(A_n n * C_n n) := by unfold H_poly_loc; rw [hg0]; ring
      rw [this]; unfold mvContent; congr 1
      · ext m; simp [MvPolynomial.support_neg]
      · ext m; simp [MvPolynomial.coeff_neg, Int.natAbs_neg]
    rw [hcH]; exact hb_even
  by_cases hac0 : A_n n * C_n n = 0
  · have : H_poly_loc n = G_poly_loc n ^ 2 := by unfold H_poly_loc; rw [hac0]; ring
    rw [show mvContent (H_poly_loc n) = mvContent (G_poly_loc n ^ 2) from by rw [this]]
    exact ha_even
  have hG2_ne : mvContent (G_poly_loc n ^ 2) ≠ 0 := by rwa [ne_eq, mvContent_eq_zero_iff]
  have hAC_ne : mvContent (A_n n * C_n n) ≠ 0 := by rwa [ne_eq, mvContent_eq_zero_iff]
  -- Let c = min(a,b), which is even. Show v₂(content(H)) = c.
  set a := padicValNat 2 (mvContent (G_poly_loc n ^ 2))
  set b := padicValNat 2 (mvContent (A_n n * C_n n))
  set c := min a b
  have hc_even : Even c := by
    simp only [c, min_def]; split_ifs <;> assumption
  -- The gap: since a ≠ b and both even, min and max differ by ≥ 2
  have hgap : c + 2 ≤ max a b := by
    obtain ⟨k, hk⟩ := ha_even; obtain ⟨j, hj⟩ := hb_even
    simp only [c]; omega
  -- Lower bound: c ≤ v₂(content(H))
  have h_lower : c ≤ padicValNat 2 (mvContent (H_poly_loc n)) := by
    have hc_dvd_G2 : 2 ^ c ∣ mvContent (G_poly_loc n ^ 2) :=
      dvd_trans (Nat.pow_dvd_pow 2 (min_le_left a b)) pow_padicValNat_dvd
    have hc_dvd_AC : 2 ^ c ∣ mvContent (A_n n * C_n n) :=
      dvd_trans (Nat.pow_dvd_pow 2 (min_le_right a b)) pow_padicValNat_dvd
    exact (padicValNat_dvd_iff_le hH_ne).mp
      (dvd_trans (Nat.dvd_gcd hc_dvd_G2 hc_dvd_AC) (gcd_content_dvd_content_sub' _ _))
  -- Upper bound: v₂(content(H)) ≤ c
  have h_upper : padicValNat 2 (mvContent (H_poly_loc n)) ≤ c := by
    by_contra h_contra
    push_neg at h_contra
    have h_dvd_H : 2 ^ (c + 1) ∣ mvContent (H_poly_loc n) :=
      (padicValNat_dvd_iff_le hH_ne).mpr (by omega)
    have h_dvd_G2 : 2 ^ (c + 1) ∣ mvContent (G_poly_loc n ^ 2) := by
      by_cases hab : a ≤ b
      · have h_dvd_AC : 2 ^ (c + 1) ∣ mvContent (A_n n * C_n n) :=
          dvd_trans (Nat.pow_dvd_pow 2 (by simp [c, hab]; omega)) pow_padicValNat_dvd
        exact dvd_mvContent_of_dvd_coeffs' _ _ (fun m => by
          have : G_poly_loc n ^ 2 = H_poly_loc n + A_n n * C_n n := by unfold H_poly_loc; ring
          rw [this, MvPolynomial.coeff_add]
          exact dvd_add
            (dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd_H) (mvContent_dvd_coeff _ m))
            (dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd_AC) (mvContent_dvd_coeff _ m)))
      · push_neg at hab
        exact dvd_trans (Nat.pow_dvd_pow 2 (by simp [c]; omega)) pow_padicValNat_dvd
    have h_dvd_AC : 2 ^ (c + 1) ∣ mvContent (A_n n * C_n n) := by
      by_cases hab : b ≤ a
      · exact dvd_mvContent_of_dvd_coeffs' _ _ (fun m => by
          have : A_n n * C_n n = G_poly_loc n ^ 2 - H_poly_loc n := by unfold H_poly_loc; ring
          rw [this, MvPolynomial.coeff_sub]
          exact dvd_sub
            (dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd_G2) (mvContent_dvd_coeff _ m))
            (dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd_H) (mvContent_dvd_coeff _ m)))
      · push_neg at hab
        exact dvd_trans (Nat.pow_dvd_pow 2 (by simp [c]; omega)) pow_padicValNat_dvd
    rcases le_total a b with hab | hab
    · exact absurd ((padicValNat_dvd_iff_le hG2_ne).mp h_dvd_G2) (by simp [c, hab]; omega)
    · exact absurd ((padicValNat_dvd_iff_le hAC_ne).mp h_dvd_AC) (by simp [c, hab]; omega)
  exact (le_antisymm h_upper h_lower) ▸ hc_even

end QuarticInvariant
