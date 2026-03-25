import Mathlib
import Modular.Defs
import Modular.CentralDom
import Modular.BEvalDiv
import Modular.KummerCarry
import Modular.ScalarBounds

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant


/-- α(n,n) = γ(n) -/
lemma α_eq_γ (n : ℕ) : α n n = γ n := by
  unfold α γ; show (2 * n + 1 - n).factorial * n.factorial = (n + 1).factorial * n.factorial
  congr 1; congr 1; omega

/-- β(n,n) = γ(n) -/
lemma β_eq_γ (n : ℕ) : β n n = γ n := by
  unfold β γ; show (2 * n - n).factorial * (n + 1).factorial = (n + 1).factorial * n.factorial
  rw [show 2 * n - n = n from by omega]; ring

/-- C(2n,n-1) * (n+1) = C(2n,n) * n -/
lemma choose_shift (n : ℕ) (hn : 1 ≤ n) :
    Nat.choose (2 * n) (n - 1) * (n + 1) = Nat.choose (2 * n) n * n := by
  have h := Nat.choose_succ_right_eq (2 * n) (n - 1)
  rw [show n - 1 + 1 = n from by omega] at h
  rw [show 2 * n - (n - 1) = n + 1 from by omega] at h
  linarith

/-- C(2n,n+1) = C(2n,n-1) -/
lemma choose_symm_n (n : ℕ) (hn : 1 ≤ n) :
    Nat.choose (2 * n) (n + 1) = Nat.choose (2 * n) (n - 1) := by
  have h := Nat.choose_symm (show n + 1 ≤ 2 * n by omega)
  rw [show 2 * n - (n + 1) = n - 1 from by omega] at h
  exact h.symm

/-- α(n,n-1) = (n+2) · (n-1)! · (n+1)! -/
lemma alpha_n_minus_one_eq (n : ℕ) (hn : 1 ≤ n) :
    α n (n - 1) = (n + 2) * (n - 1).factorial * (n + 1).factorial := by
  unfold α
  rw [show 2 * n + 1 - (n - 1) = n + 2 from by omega, Nat.factorial_succ (n + 1)]
  ring

/-- β(n,n-1) = γ(n) -/
lemma beta_n_minus_one_eq (n : ℕ) (hn : 1 ≤ n) :
    β n (n - 1) = γ n := by
  unfold β γ
  rw [show 2 * n - (n - 1) = n + 1 from by omega, show n - 1 + 1 = n from by omega]

/-- α(n,n+1) = γ(n) -/
lemma alpha_n_plus_one_eq (n : ℕ) :
    α n (n + 1) = γ n := by
  unfold α γ
  rw [show 2 * n + 1 - (n + 1) = n from by omega]
  ring

/-- β(n,n+1) = (n-1)! · (n+2)! -/
lemma beta_n_plus_one_eq (n : ℕ) (hn : 1 ≤ n) :
    β n (n + 1) = (n - 1).factorial * (n + 2).factorial := by
  unfold β
  rw [show 2 * n - (n + 1) = n - 1 from by omega, show n + 1 + 1 = n + 2 from by omega]

lemma scalar_AB_eq (n : ℕ) : scalar_AB n n = Nat.choose (2 * n) n * (γ n) ^ 2 := by
  unfold scalar_AB; rw [α_eq_γ, β_eq_γ]; ring

lemma scalar_A2_eq (n : ℕ) : scalar_A2 n n = Nat.choose (2 * n) n * (γ n) ^ 2 := by
  unfold scalar_A2; rw [α_eq_γ]

lemma scalar_B2_eq (n : ℕ) : scalar_B2 n n = Nat.choose (2 * n) n * (γ n) ^ 2 := by
  unfold scalar_B2; rw [β_eq_γ]

lemma e_central_eq (p n : ℕ) : e_central p n = padicValNat p (scalar_AB n n) := by
  unfold e_central; rw [← scalar_AB_eq]

lemma p_pow_dvd_scalar_AB (p n : ℕ) : p ^ e_central p n ∣ scalar_AB n n := by
  rw [e_central_eq]; exact pow_padicValNat_dvd

/-- p^{e+1} | scalar_A2(n,i) for i ∉ {n, n+1} -/
lemma p_pow_succ_dvd_scalar_A2 (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k)
    (i : ℕ) (hi : i ≤ 2 * n) (hi_ne_n : i ≠ n) (hi_ne_n1 : i ≠ n + 1) :
    p ^ (e_central p n + 1) ∣ scalar_A2 n i := by
  have h := scalar_A2_central_min p k hk n hn i hi hi_ne_n hi_ne_n1
  have h_eq : e_central p n = padicValNat p (scalar_A2 n n) := by
    unfold e_central; rw [← scalar_A2_eq]
  exact Nat.dvd_trans (pow_dvd_pow p (by rw [h_eq]; omega)) pow_padicValNat_dvd

/-- p^{e+1} | scalar_B2(n,i) for i ∉ {n, n-1} -/
lemma p_pow_succ_dvd_scalar_B2 (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n)
    (i : ℕ) (hi : i ≤ 2 * n) (hi_ne_n : i ≠ n) (hi_ne_nm1 : i ≠ n - 1) :
    p ^ (e_central p n + 1) ∣ scalar_B2 n i := by
  have h := scalar_B2_central_min p k hk n hn hn_pos i hi hi_ne_n hi_ne_nm1
  have h_eq : e_central p n = padicValNat p (scalar_B2 n n) := by
    unfold e_central; rw [← scalar_B2_eq]
  exact Nat.dvd_trans (pow_dvd_pow p (by rw [h_eq]; omega)) pow_padicValNat_dvd

/-- p does not divide n+1 when n+2 = p^k -/
lemma p_not_dvd_n_plus_one (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) :
    ¬ (p : ℤ) ∣ (n + 1 : ℤ) := by
  intro ⟨q, hq⟩
  have h1 : (p : ℤ) ∣ (n + 2 : ℤ) := ⟨p ^ (k - 1), by
    have hk' : k - 1 + 1 = k := by omega
    push_cast; rw [← pow_succ', hk']; exact_mod_cast hn⟩
  have h2 : (p : ℤ) ∣ 1 := by
    have := dvd_sub h1 ⟨q, hq⟩
    simp at this; exact this
  have h3 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h2
  have h4 : 1 < p := Nat.Prime.one_lt (Fact.out)
  omega

/-- Cross terms at i=n±1 have extra factor (n+2)² = p^{2k},
    making n · C(2n,n) · α_{n-1}² divisible by p^{e+1}. -/
lemma cross_term_dvd (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) (hp_odd : p ≠ 2) (hn_pos : 1 ≤ n) :
    (↑(p ^ (e_central p n + 1)) : ℤ) ∣
      ↑n * ↑(Nat.choose (2 * n) n) * (↑(α n (n - 1)) : ℤ) ^ 2 := by
  have h_factor : n * (Nat.choose (2 * n) n) * ((α n (n - 1)) : ℤ) ^ 2 =
      (p ^ (2 * k) : ℤ) * (n * (Nat.choose (2 * n) n) *
        ((n - 1).factorial * (n + 1).factorial) ^ 2) := by
    rw [show α n (n - 1) = (n + 2) * (n - 1).factorial * (n + 1).factorial
      from alpha_n_minus_one_eq n hn_pos]
    push_cast [hn]; ring
  suffices h_div : (p ^ (e_central p n + 1) : ℤ) ∣
      (p ^ (2 * k) : ℤ) * (n * (Nat.choose (2 * n) n) *
        ((n - 1).factorial * (n + 1).factorial) ^ 2) by aesop
  suffices h_div : (p ^ (e_central p n - 1) : ℤ) ∣
      (n * (Nat.choose (2 * n) n) * ((n - 1).factorial * (n + 1).factorial) ^ 2) by
    refine dvd_trans ?_ (mul_dvd_mul_left _ h_div)
    rw [← pow_add]; exact pow_dvd_pow _ (by omega)
  have h_div_scalar_AB : (p : ℤ) ^ (e_central p n) ∣
      (n ^ 2 * (Nat.choose (2 * n) n) * ((n - 1).factorial * (n + 1).factorial) ^ 2 : ℤ) := by
    have h : (p : ℤ) ^ (e_central p n) ∣ (Nat.choose (2 * n) n * (γ n) ^ 2 : ℤ) :=
      Int.natCast_dvd_natCast.mpr (by rw [← scalar_AB_eq]; exact p_pow_dvd_scalar_AB p n)
    convert h using 1; norm_cast; simp [γ]; ring
    cases n <;> norm_num [Nat.factorial_succ] at *; linarith
  have h_coprime : Nat.gcd p n = 1 := by
    refine (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 ?_
    rintro ⟨c, rfl⟩
    replace hn := congr_arg (· % p) hn
    rcases k with (_ | _ | k) <;>
      simp_all [Nat.add_mod, Nat.pow_mod, Nat.mul_mod,
        Nat.mod_eq_of_lt (show 2 < p from
          lt_of_le_of_ne (Nat.Prime.two_le Fact.out) (Ne.symm hp_odd))]
  rcases x : e_central p n with (_ | e)
  · simp_all
  · rw [show Nat.succ e - 1 = e from by omega]
    rw [x] at h_div_scalar_AB
    -- h_div_scalar_AB : p^(e+1) | n^2 * choose * (...)^2
    -- First get: p^e | n^2 * choose * (...)^2
    have h1 : (p : ℤ) ^ e ∣ (n : ℤ) ^ 2 *
        ↑((2 * n).choose n) * (↑(n - 1)! * ↑(n + 1)!) ^ 2 :=
      dvd_trans (pow_dvd_pow _ (Nat.le_succ _)) h_div_scalar_AB
    -- Rewrite as p^e | n * (n * choose * (...)^2)
    have h2 : (p : ℤ) ^ e ∣ (n : ℤ) *
        ((n : ℤ) * ↑((2 * n).choose n) * (↑(n - 1)! * ↑(n + 1)!) ^ 2) := by
      convert h1 using 1; ring
    -- gcd(p^e, n) = 1
    have hp_cop_n : Int.gcd ((p : ℤ) ^ e) (n : ℤ) = 1 := by
      exact_mod_cast Nat.Coprime.pow_left _ h_coprime
    exact Int.dvd_of_dvd_mul_right_of_gcd_one (b := (n : ℤ)) h2 hp_cop_n

/-- Main intermediate: (n+1) · B_eval ≡ 2(-1)ⁿ · scalar_AB · cₙ · c_{n+1} (mod p^{e+1}).

The proof splits B_eval into i=n, i=n-1, i=n+1, and the rest.
Non-central terms vanish mod p^{e+1} by central dominance.
Central terms combine via choose_shift to give the result. -/
lemma n_plus_one_mul_B_eval_cong (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n)
    (c : ℕ → ℤ) :
    ↑(n + 1) * B_eval n c ≡
      2 * (-1 : ℤ) ^ n * ↑(scalar_AB n n) * c n * c (n + 1)
      [ZMOD ↑p ^ (e_central p n + 1)] := by
  have h_split : (n + 1) * B_eval n c = (n + 1) * (∑ i ∈ Finset.range (2 * n + 1),
      (-1 : ℤ) ^ i * Nat.choose (2 * n) i * ((α n i : ℤ) ^ 2 * c i * c (2 * n + 1 - i) +
        (β n i : ℤ) ^ 2 * c (i + 1) * c (2 * n - i))) := rfl
  -- Step 1: Non-central terms vanish mod p^{e+1}
  have h_mod : (n + 1) * B_eval n c ≡
      (n + 1) * ((-1 : ℤ) ^ n * Nat.choose (2 * n) n *
        ((α n n : ℤ) ^ 2 * c n * c (n + 1) + (β n n : ℤ) ^ 2 * c (n + 1) * c n)) +
      (n + 1) * ((-1 : ℤ) ^ (n - 1) * Nat.choose (2 * n) (n - 1) *
        ((α n (n - 1) : ℤ) ^ 2 * c (n - 1) * c (n + 2) +
         (β n (n - 1) : ℤ) ^ 2 * c n * c (n + 1))) +
      (n + 1) * ((-1 : ℤ) ^ (n + 1) * Nat.choose (2 * n) (n + 1) *
        ((α n (n + 1) : ℤ) ^ 2 * c (n + 1) * c n +
         (β n (n + 1) : ℤ) ^ 2 * c (n + 2) * c (n - 1)))
      [ZMOD p ^ (e_central p n + 1)] := by
    have h_vanish : ∀ i ∈ Finset.range (2 * n + 1), i ≠ n ∧ i ≠ n - 1 ∧ i ≠ n + 1 →
        (n + 1) * ((-1 : ℤ) ^ i * Nat.choose (2 * n) i *
          ((α n i : ℤ) ^ 2 * c i * c (2 * n + 1 - i) +
           (β n i : ℤ) ^ 2 * c (i + 1) * c (2 * n - i))) ≡ 0
        [ZMOD p ^ (e_central p n + 1)] := by
      intros i hi hi_ne
      have h_div : p ^ (e_central p n + 1) ∣ Nat.choose (2 * n) i * (α n i) ^ 2 ∧
          p ^ (e_central p n + 1) ∣ Nat.choose (2 * n) i * (β n i) ^ 2 :=
        ⟨p_pow_succ_dvd_scalar_A2 p k hk n hn i (Finset.mem_range_succ_iff.mp hi) hi_ne.1 hi_ne.2.2,
         p_pow_succ_dvd_scalar_B2 p k hk n hn hn_pos i (Finset.mem_range_succ_iff.mp hi) hi_ne.1 hi_ne.2.1⟩
      rw [Int.modEq_zero_iff_dvd]
      convert dvd_mul_of_dvd_right
        (dvd_add (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h_div.1)
            (c i * c (2 * n + 1 - i)))
          (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h_div.2)
            (c (i + 1) * c (2 * n - i))))
        ((-1) ^ i * (n + 1)) using 1
      · push_cast; ring
    have h_central : (n + 1) * B_eval n c ≡
        (n + 1) * (∑ i ∈ ({n, n - 1, n + 1} : Finset ℕ),
          (-1 : ℤ) ^ i * Nat.choose (2 * n) i *
            ((α n i : ℤ) ^ 2 * c i * c (2 * n + 1 - i) +
             (β n i : ℤ) ^ 2 * c (i + 1) * c (2 * n - i)))
        [ZMOD p ^ (e_central p n + 1)] := by
      rw [h_split]
      rw [← Finset.sum_sdiff (show {n, n - 1, n + 1} ⊆ Finset.range (2 * n + 1) from ?_)]
      · simp_all [mul_add, Int.modEq_iff_dvd]
        rw [Finset.mul_sum]
        exact Finset.dvd_sum fun i hi => by
          convert dvd_neg.mpr (h_vanish i
            (by linarith [Finset.mem_range.mp (Finset.mem_sdiff.mp hi |>.1)])
            (by aesop) (by aesop) (by aesop)) using 1; ring
      · simp [Finset.insert_subset_iff, Finset.mem_range]; omega
    rcases n with (_ | n) <;> simp [Finset.sum_pair, Nat.succ_eq_add_one] at *
    convert h_central using 1; norm_num [two_mul, add_assoc]; ring
    rw [show 2 + n * 2 - (1 + n) = n + 1 by rw [Nat.sub_eq_of_eq_add]; ring,
        show 3 + n * 2 - (2 + n) = n + 1 by rw [Nat.sub_eq_of_eq_add]; ring,
        show 2 + n * 2 - (2 + n) = n by rw [Nat.sub_eq_of_eq_add]; ring]; ring
  -- Step 2: Substitute α_n = β_n = γ, β_{n-1} = γ, α_{n+1} = γ, β_{n+1}² = α_{n-1}²
  have h_mod_simplified : (n + 1) * B_eval n c ≡
      (n + 1) * ((-1 : ℤ) ^ n * Nat.choose (2 * n) n *
        ((γ n : ℤ) ^ 2 * c n * c (n + 1) + (γ n : ℤ) ^ 2 * c (n + 1) * c n)) +
      (n + 1) * ((-1 : ℤ) ^ (n - 1) * Nat.choose (2 * n) (n - 1) *
        ((α n (n - 1) : ℤ) ^ 2 * c (n - 1) * c (n + 2) + (γ n : ℤ) ^ 2 * c n * c (n + 1))) +
      (n + 1) * ((-1 : ℤ) ^ (n + 1) * Nat.choose (2 * n) (n + 1) *
        ((γ n : ℤ) ^ 2 * c (n + 1) * c n + (α n (n - 1) : ℤ) ^ 2 * c (n + 2) * c (n - 1)))
      [ZMOD p ^ (e_central p n + 1)] := by
    convert h_mod using 3 <;>
      norm_num [α_eq_γ, β_eq_γ, beta_n_minus_one_eq, alpha_n_plus_one_eq, beta_n_plus_one_eq]
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| beta_n_minus_one_eq n hn_pos ▸ rfl
    · rcases n <;> simp_all [α, β]; grind
  -- Step 3: Cross terms (α_{n-1}² parts) are divisible by p^{e+1}
  have h_cross_terms :
      (n + 1) * ((-1 : ℤ) ^ (n - 1) * Nat.choose (2 * n) (n - 1) *
        ((α n (n - 1) : ℤ) ^ 2 * c (n - 1) * c (n + 2))) +
      (n + 1) * ((-1 : ℤ) ^ (n + 1) * Nat.choose (2 * n) (n + 1) *
        ((α n (n - 1) : ℤ) ^ 2 * c (n + 2) * c (n - 1))) ≡ 0
      [ZMOD p ^ (e_central p n + 1)] := by
    have h1 : (p : ℤ) ^ (e_central p n + 1) ∣
        (n + 1) * ((-1 : ℤ) ^ (n - 1) * Nat.choose (2 * n) (n - 1) *
          ((α n (n - 1) : ℤ) ^ 2 * c (n - 1) * c (n + 2))) := by
      have hct : (p : ℤ) ^ (e_central p n + 1) ∣
          (n + 1) * Nat.choose (2 * n) (n - 1) * (α n (n - 1) : ℤ) ^ 2 := by
        convert cross_term_dvd p k hk n hn hp_odd hn_pos using 1
        exact congr_arg₂ _ (by linarith [choose_shift n hn_pos]) rfl
      convert hct.mul_left ((-1) ^ (n - 1) * c (n - 1) * c (n + 2)) using 1; ring
    have h2 : (p : ℤ) ^ (e_central p n + 1) ∣
        (n + 1) * ((-1 : ℤ) ^ (n + 1) * Nat.choose (2 * n) (n + 1) *
          ((α n (n - 1) : ℤ) ^ 2 * c (n + 2) * c (n - 1))) := by
      convert h1 using 1; ring
      rw [show 1 + n = n + 1 by ring, show n * 2 = 2 * n by ring]
      rcases n with (_ | n) <;> simp_all [Nat.choose_symm_add]; ring
      rw [show 2 + n * 2 = 2 * (n + 1) by ring, show 2 + n = n + 2 by ring]
      rw [Nat.choose_symm_of_eq_add]; ring; ring
    exact Int.modEq_zero_iff_dvd.mpr (dvd_add h1 h2)
  -- Step 4: Central γ² terms combine to give the result
  have h_central_terms :
      (n + 1) * ((-1 : ℤ) ^ n * Nat.choose (2 * n) n *
        ((γ n : ℤ) ^ 2 * c n * c (n + 1) + (γ n : ℤ) ^ 2 * c (n + 1) * c n)) +
      (n + 1) * ((-1 : ℤ) ^ (n - 1) * Nat.choose (2 * n) (n - 1) *
        ((γ n : ℤ) ^ 2 * c n * c (n + 1))) +
      (n + 1) * ((-1 : ℤ) ^ (n + 1) * Nat.choose (2 * n) (n + 1) *
        ((γ n : ℤ) ^ 2 * c (n + 1) * c n)) ≡
      2 * (-1 : ℤ) ^ n * Nat.choose (2 * n) n * (γ n : ℤ) ^ 2 * c n * c (n + 1)
      [ZMOD p ^ (e_central p n + 1)] := by
    rw [show (Nat.choose (2 * n) (n - 1) : ℤ) = (Nat.choose (2 * n) n : ℤ) * n / (n + 1) from ?_,
        show (Nat.choose (2 * n) (n + 1) : ℤ) = (Nat.choose (2 * n) n : ℤ) * n / (n + 1) from ?_]
    · rw [show (-1 : ℤ) ^ (n - 1) = (-1 : ℤ) ^ n / (-1 : ℤ) from ?_,
          show (-1 : ℤ) ^ (n + 1) = (-1 : ℤ) ^ n * (-1 : ℤ) from ?_]
      · ring_nf; norm_num [Int.ModEq]
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]; ring_nf; norm_num [Int.ModEq]
        rw [show (n * Nat.choose (n * 2) n : ℤ) =
            (1 + n) * (n * Nat.choose (n * 2) n / (1 + n)) by
          rw [Int.mul_ediv_cancel']
          exact ⟨Nat.choose (n * 2) n - Nat.choose (n * 2) n / (1 + n), by
            linarith [Nat.div_mul_cancel (show 1 + n ∣ Nat.choose (n * 2) n from by
              have h := Nat.add_one_mul_choose_eq (n * 2) n
              simp_all [Nat.choose_succ_succ, mul_comm]
              exact ⟨Nat.choose (n * 2) n - Nat.choose (n * 2) (n + 1), by
                rw [Nat.mul_sub_left_distrib, eq_tsub_iff_add_eq_of_le] <;> nlinarith⟩)]⟩]
        ring_nf
        rw [show (n * (n * Nat.choose (n * 2) n / (1 + n)) +
            n * Nat.choose (n * 2) n / (1 + n) : ℤ) =
            (1 + n) * (n * Nat.choose (n * 2) n / (1 + n)) by ring]
        norm_num [Int.mul_ediv_cancel_left, show (1 + n : ℤ) ≠ 0 by positivity]
        ring_nf; norm_num [Int.ModEq]
      · ring
      · cases n <;> norm_num [pow_succ'] at *
    · rw [Int.ediv_eq_of_eq_mul_left] <;> norm_cast
      rw [Nat.choose_succ_right_eq]
      rw [two_mul, add_tsub_cancel_left]
    · rw [Int.ediv_eq_of_eq_mul_left] <;> norm_cast
      rcases n with (_ | n) <;> simp [Nat.add_one_mul_choose_eq] at *
      have h4 := Nat.choose_succ_right_eq (2 * (n + 1)) n
      rw [show 2 * (n + 1) - n = n + 2 from by omega] at h4
      nlinarith
  -- Combine all parts
  convert h_mod_simplified.trans ?_ using 1
  convert h_central_terms.add h_cross_terms using 1 <;> ring!
  unfold scalar_AB; ring
  rw [show α n n = γ n from α_eq_γ n, show β n n = γ n from β_eq_γ n]; push_cast; ring

/-- B' ≡ -2μ c_n c_{n+1} (mod p).

The proof multiplies by (n+1) and uses n+2 = p^k ≡ 0 (mod p) to show
(n+1)(B' + 2μ c_n c_{n+1}) ≡ 0 (mod p), then divides by the unit (n+1). -/
theorem B_eval_cong (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (c : ℕ → ℤ)
    (B' : ℤ) (hB : B_eval n c = (p : ℤ) ^ e_central p n * B') :
    (p : ℤ) ∣ B' + 2 * ((-1 : ℤ) ^ n * ↑(scalar_AB n n / p ^ e_central p n)) *
      (c n) * (c (n + 1)) := by
  -- Step 1: From n_plus_one_mul_B_eval_cong, derive (n+1)·B' ≡ 2μ·c_n·c_{n+1} (mod p)
  have h_cong : (n + 1) * B' ≡
      2 * ((-1 : ℤ) ^ n * (scalar_AB n n / p ^ e_central p n)) * c n * c (n + 1)
      [ZMOD p] := by
    have h_div : (n + 1) * p ^ e_central p n * B' ≡
        2 * (-1 : ℤ) ^ n * p ^ e_central p n *
          (scalar_AB n n / p ^ e_central p n) * c n * c (n + 1)
        [ZMOD p ^ (e_central p n + 1)] := by
      convert n_plus_one_mul_B_eval_cong p k hk hp_odd n hn hn_pos c using 1
      · rw [hB]; push_cast; ring
      · simp [mul_assoc,
          Int.mul_ediv_cancel' (show (p : ℤ) ^ e_central p n ∣ scalar_AB n n from
            mod_cast p_pow_dvd_scalar_AB p n)]
    rw [Int.modEq_iff_dvd] at *
    obtain ⟨k', hk'⟩ := h_div
    refine ⟨k', ?_⟩
    have hpe_pos : (0 : ℤ) < (p : ℤ) ^ e_central p n :=
      pow_pos (Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out) _
    rw [pow_succ'] at hk'
    nlinarith
  -- Step 2: Show (n+1)·(B' + 2μ·c_n·c_{n+1}) ≡ 0 (mod p), using n+1 ≡ -1 (mod p)
  have h_inv : (n + 1) * (B' + 2 * ((-1 : ℤ) ^ n * (scalar_AB n n / p ^ e_central p n)) *
      c n * c (n + 1)) ≡ 0 [ZMOD p] := by
    simp_all [mul_add, ← ZMod.intCast_eq_intCast_iff]
    rw [show (n + 1 : ZMod p) = -1 from ?_]; ring
    rw [eq_neg_iff_add_eq_zero]; norm_cast; aesop
  -- Step 3: Since p ∤ (n+1), conclude p | (B' + 2μ·c_n·c_{n+1})
  simp_all [Int.modEq_zero_iff_dvd]
  exact Or.resolve_left (Int.Prime.dvd_mul' Fact.out h_inv) (p_not_dvd_n_plus_one p k hk n hn)



/-! ======== BinomialGCD ======== -/

namespace BinomialGCD


def g (m : ℕ) : ℕ := (Finset.Ioo 0 m).gcd (Nat.choose m)

/-
g(m) = p if m = p^k for some prime p and k >= 1, and g(m) = 1 otherwise.
-/
theorem g_val (m : ℕ) (hm : 2 ≤ m) : g m = if IsPrimePow m then m.minFac else 1 := by
  split_ifs with h_prime_pow;
  · -- Let $p$ be the minimal prime factor of $m$.
    set p := Nat.minFac m
    have hp_prime : Nat.Prime p := by
      exact Nat.minFac_prime ( by linarith )
    have hm_eq : ∃ k, m = p ^ k := by
      rw [ isPrimePow_nat_iff ] at *;
      norm_num +zetaDelta at *;
      obtain ⟨ p, hp, x, hx, rfl ⟩ := h_prime_pow; rw [ Nat.Prime.pow_minFac ] <;> aesop;
    obtain ⟨k, hk⟩ : ∃ k, m = p ^ k := hm_eq
    have hk_pos : 1 ≤ k := by
      exact Nat.pos_of_ne_zero ( by rintro rfl; linarith )
    have h_gcd : g m = p := by
      -- By Lucas' theorem, $p$ divides every interior binomial coefficient of $p^k$, and $p^2$ does not divide $\binom{p^k}{p^{k-1}}$.
      have h_divides : ∀ r ∈ Finset.Ioo 0 m, p ∣ Nat.choose m r := by
        intro r hr; rw [ hk ] ; exact hp_prime.dvd_choose_pow ( by linarith [ Finset.mem_Ioo.mp hr ] ) ( by linarith [ Finset.mem_Ioo.mp hr ] ) ;
      have h_not_divides : ¬(p ^ 2 ∣ Nat.choose m (p ^ (k - 1))) := by
        -- Using Kummer's theorem, we know that the exponent of $p$ in $\binom{p^k}{p^{k-1}}$ is $1$.
        have h_exp : Nat.factorization (Nat.choose (p ^ k) (p ^ (k - 1))) p = 1 := by
          rw [ Nat.factorization_def ];
          · haveI := Fact.mk hp_prime; rw [ padicValNat_choose ] ;
            any_goals exact Nat.lt_succ_self _;
            · rcases k with ( _ | k ) <;> norm_num [ Nat.log_pow hp_prime.one_lt ] at *;
              rw [ Finset.card_eq_one ] ; use k + 1 ; ext i ; norm_num [ Nat.pow_succ', Nat.mul_mod_mul_left ] ; ring_nf ; (
              constructor <;> intro hi <;> rcases hi with ⟨ ⟨ hi₁, hi₂ ⟩, hi₃ ⟩ <;> norm_num [ show p * p ^ k - p ^ k = p ^ k * ( p - 1 ) by rw [ Nat.mul_sub_left_distrib ] ; ring ] at *;
              · contrapose! hi₃;
                rw [ Nat.mod_eq_zero_of_dvd ( pow_dvd_pow _ ( show i ≤ k from Nat.le_of_lt_succ ( lt_of_le_of_ne ( by linarith ) ( by omega ) ) ) ), Nat.mod_eq_zero_of_dvd ( dvd_mul_of_dvd_left ( pow_dvd_pow _ ( show i ≤ k from Nat.le_of_lt_succ ( lt_of_le_of_ne ( by linarith ) ( by omega ) ) ) ) _ ) ] ; norm_num [ hp_prime.pos ];
              · rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> norm_num [ pow_add, pow_one, hp_prime.one_lt ];
                · nlinarith [ Nat.sub_add_cancel hp_prime.pos, pow_pos hp_prime.pos k ];
                · nlinarith [ Nat.sub_add_cancel hp_prime.pos, pow_pos hp_prime.pos k ];
                · exact lt_mul_of_one_lt_left ( pow_pos hp_prime.pos _ ) hp_prime.one_lt);
            · exact pow_le_pow_right₀ hp_prime.one_lt.le ( Nat.pred_le _ );
          · exact hp_prime;
        rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num [ hp_prime.ne_zero ];
        · intro H; have := H p; norm_num [ hp_prime ] at this; linarith [ show Nat.factorization ( Nat.choose m ( p ^ ( k - 1 ) ) ) p = 1 from hk ▸ h_exp ] ;
        · exact Nat.ne_of_gt <| Nat.choose_pos <| hk.symm ▸ Nat.pow_le_pow_right hp_prime.pos ( Nat.pred_le _ )
      have h_gcd : g m ∣ p := by
        have h_gcd : g m ∣ Nat.choose m (p ^ (k - 1)) := by
          exact Finset.gcd_dvd ( Finset.mem_Ioo.mpr ⟨ pow_pos hp_prime.pos _, hk.symm ▸ pow_lt_pow_right₀ hp_prime.one_lt ( Nat.pred_lt ( ne_bot_of_gt hk_pos ) ) ⟩ )
        have h_gcd_le : g m ∣ p ^ k := by
          exact hk ▸ Nat.dvd_trans ( Finset.gcd_dvd ( Finset.mem_Ioo.mpr ⟨ Nat.one_pos, hm ⟩ ) ) ( by simp +decide [ Nat.choose_one_right ] ) ;
        have h_gcd_le_p : g m ∣ p := by
          rw [ Nat.dvd_prime_pow hp_prime ] at h_gcd_le ; rcases h_gcd_le with ⟨ x, hx ⟩ ; simp +decide [ hx ] at *; (
          exact dvd_trans ( pow_dvd_pow _ ( show x ≤ 1 from Nat.le_of_not_lt fun h => h_not_divides <| dvd_trans ( pow_dvd_pow _ h ) h_gcd ) ) ( by norm_num ) ;)
        exact h_gcd_le_p
      have h_gcd_ge : p ∣ g m := by
        exact Finset.dvd_gcd h_divides
      have h_gcd_eq : g m = p := by
        exact Nat.dvd_antisymm h_gcd h_gcd_ge
      exact h_gcd_eq
    exact h_gcd;
  · -- If $m$ is not a prime power, then for any prime $p$ dividing $m$, there exists $r$ such that $p$ does not divide $\binom{m}{r}$.
    have h_not_div : ∀ p, Nat.Prime p → p ∣ m → ∃ r, 1 ≤ r ∧ r < m ∧ ¬(p ∣ Nat.choose m r) := by
      -- Let $p$ be a prime divisor of $m$. Since $m$ is not a prime power, we can write $m = p^k \cdot q$ where $q$ is not divisible by $p$.
      intro p hp hpm
      obtain ⟨k, q, hq⟩ : ∃ k q, m = p^k * q ∧ ¬p ∣ q := by
        exact ⟨ Nat.factorization m p, m / p ^ Nat.factorization m p, by rw [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ], Nat.not_dvd_ordCompl ( by aesop ) ( by aesop ) ⟩;
      -- Choose $r = p^k$.
      use p^k;
      -- By Lucas' theorem, $\binom{p^k \cdot q}{p^k} \equiv q \pmod{p}$.
      have h_lucas : Nat.choose (p^k * q) (p^k) ≡ q [MOD p] := by
        haveI := Fact.mk hp; simp +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
        -- Using the polynomial expansion, we can see that $(1 + X)^{p^k \cdot q}$ modulo $p$ simplifies to $(1 + X^{p^k})^q$ modulo $p$.
        have h_poly_expand : (1 + Polynomial.X : Polynomial (ZMod p)) ^ (p ^ k * q) = (1 + Polynomial.X ^ (p ^ k)) ^ q := by
          rw [ pow_mul ];
          simp +decide [ add_pow_char_pow ];
        replace h_poly_expand := congr_arg ( fun f => Polynomial.coeff f ( p ^ k ) ) h_poly_expand ; simp_all +decide [ Polynomial.coeff_one_add_X_pow ] ;
        rw [ add_comm, add_pow ];
        norm_num [ ← pow_mul, Polynomial.coeff_sum, Polynomial.coeff_X_pow ];
        rcases p with ( _ | _ | p ) <;> rcases q with ( _ | _ | q ) <;> simp_all +decide [ Finset.sum_range_succ', pow_succ' ];
      rcases k with ( _ | k ) <;> simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ];
      rcases q with ( _ | _ | q ) <;> simp_all +decide [ pow_succ' ];
      · exact h_prime_pow ( by rw [ ← pow_succ' ] ; exact hp.isPrimePow.pow ( by linarith ) );
      · exact ⟨ Nat.mul_pos hp.pos ( pow_pos hp.pos _ ), lt_mul_of_one_lt_right ( Nat.mul_pos hp.pos ( pow_pos hp.pos _ ) ) ( by linarith ) ⟩;
    -- Therefore, $g(m)$ cannot have any prime factors, so $g(m) = 1$.
    have h_no_prime_factors : ∀ p, Nat.Prime p → ¬(p ∣ g m) := by
      intro p pp dp; obtain ⟨ r, hr₁, hr₂, hr₃ ⟩ := h_not_div p pp ( dvd_trans dp <| Finset.gcd_dvd ( Finset.mem_Ioo.mpr ⟨ show 1 ≤ m - 1 from Nat.sub_pos_of_lt hm, Nat.sub_lt ( by linarith ) ( by linarith ) ⟩ ) |> fun x => x.trans <| by simp +decide [ Nat.choose_symm ( show 1 ≤ m from by linarith ) ] ) ; exact hr₃ <| dvd_trans dp <| Finset.gcd_dvd <| Finset.mem_Ioo.mpr ⟨ hr₁, hr₂ ⟩ ;
    exact Classical.not_not.1 fun h => h_no_prime_factors _ ( Nat.minFac_prime h ) ( Nat.minFac_dvd _ )


end BinomialGCD


/-! ======== CancellationFreeBn ======== -/

namespace CancellationFreeBn


def alpha (N i : Nat) : Int := (Nat.factorial (N + 1 - i) * Nat.factorial i)

def beta (N i : Nat) : Int := (Nat.factorial (N - i) * Nat.factorial (i + 1))

/-
The coefficient of f_k * f_{N+1-k} in B_n is given by b_k.
-/
def coeff_k (N k : Nat) : Int :=
  let T1 := (-1 : Int)^k * Nat.choose N k * (alpha N k)^2
  let T2 := (-1 : Int)^(N+1-k) * Nat.choose N (N+1-k) * (alpha N (N+1-k))^2
  let T3 := (-1 : Int)^(k-1) * Nat.choose N (k-1) * (beta N (k-1))^2
  let T4 := (-1 : Int)^(N-k) * Nat.choose N (N-k) * (beta N (N-k))^2
  T1 + T2 + T3 + T4

def b_k (N k : Nat) : Int :=
  (2 * (-1 : Int)^k * (Nat.factorial N : Int)^2 * ((N : Int) + 1 - k) * ((N : Int) + 1 - 2*k)) / (Nat.choose N k)

theorem cancellation_free_Bn_coefficient (n k : Nat) (h_n : n ≥ 1) (h_k_ge : k ≥ 1) (h_k_le : k ≤ 2*n) :
  let N := 2*n
  coeff_k N k = b_k N k := by
    unfold coeff_k b_k;
    -- Let's simplify the expression using the definitions of $T1$, $T2$, $T3$, and $T4$.
    have h_simp : 2 * (-1 : ℤ) ^ k * (Nat.factorial (2 * n)) ^ 2 * (2 * n + 1 - k) * (2 * n + 1 - 2 * k) / (Nat.choose (2 * n) k : ℤ) = 2 * (-1 : ℤ) ^ k * (Nat.factorial (2 * n + 1 - k) * Nat.factorial k) ^ 2 * (Nat.choose (2 * n) k : ℤ) - 2 * (-1 : ℤ) ^ k * (Nat.factorial (2 * n + 1 - k) * Nat.factorial k) ^ 2 * (Nat.choose (2 * n) (k - 1) : ℤ) := by
      rw [ Int.ediv_eq_of_eq_mul_left ];
      · exact ne_of_gt <| Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith;
      · rcases k with ( _ | k ) <;> simp_all +decide [ Nat.succ_mul_choose_eq ];
        rw [ ← Nat.choose_mul_factorial_mul_factorial ( by linarith : k + 1 ≤ 2 * n ) ] ; ring;
        rw [ show n * 2 - k = ( n * 2 - ( 1 + k ) ) + 1 by omega ] ; norm_num [ Nat.factorial_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub ( by linarith : k ≤ n * 2 ), Nat.cast_sub ( by linarith : 1 + k ≤ n * 2 ) ] ; ring;
        rw [ show ( Nat.choose ( n * 2 ) ( 1 + k ) : ℤ ) = ( Nat.choose ( n * 2 ) k : ℤ ) * ( n * 2 - k ) / ( 1 + k ) from ?_ ] ; ring;
        · rw [ ← @Int.cast_inj ℚ ] ; push_cast ; ring;
          rw [ Int.cast_div ] <;> norm_num ; ring;
          · -- Combine like terms and simplify the expression.
            field_simp
            ring;
          · have h_div : (1 + k : ℤ) ∣ (Nat.choose (n * 2) k : ℤ) * (n * 2 - k) := by
              have h_eq : (Nat.choose (n * 2) k : ℤ) * (n * 2 - k) = (Nat.choose (n * 2) (k + 1) : ℤ) * (k + 1) := by
                rw_mod_cast [ Nat.choose_succ_right_eq ];
                rw [ Int.subNatNat_of_le ( by linarith ) ] ; push_cast ; ring
              exact h_eq.symm ▸ ⟨ Nat.choose ( n * 2 ) ( k + 1 ), by ring ⟩;
            convert h_div using 1 ; ring;
          · linarith;
        · rw [ Int.ediv_eq_of_eq_mul_left ] <;> norm_cast <;> try linarith;
          rw [ Int.subNatNat_of_le ( by linarith ) ] ; push_cast [ Nat.add_comm 1 k, Nat.choose_succ_right_eq ] ; ring;
    rcases k with ( _ | k ) <;> simp_all +decide [ Nat.succ_eq_add_one, Nat.choose_succ_succ, pow_add ];
    unfold alpha beta; simp +decide [ Nat.choose_symm ( by linarith : k ≤ 2 * n ), Nat.choose_symm ( by linarith : k + 1 ≤ 2 * n ), pow_add ] ; ring;
    rw [ show n * 2 - k = 2 * n - k by ring, show n * 2 - ( 1 + k ) = 2 * n - ( 1 + k ) by ring ] ; rw [ show 1 + ( 2 * n - ( 1 + k ) ) = 2 * n - k by omega ] ; ring;
    rw [ show n * 2 - ( 1 + k ) = n * 2 - k - 1 by omega, show n * 2 - k = n * 2 - ( 1 + k ) + 1 by omega ] ; norm_num [ Nat.factorial_succ, pow_add ] ; ring;
    rw [ show n * 2 - ( n * 2 - ( 1 + k ) ) = 1 + k by omega, show 1 + n * 2 - ( 1 + ( n * 2 - ( 1 + k ) ) ) = 1 + k by omega ] ; ring;
    rw [ show n * 2 - ( 1 + k ) = 2 * n - ( 1 + k ) by ring ] ; rw [ show ( -1 : ℤ ) ^ ( 2 * n - ( 1 + k ) ) = ( -1 : ℤ ) ^ ( 2 * n ) / ( -1 : ℤ ) ^ ( 1 + k ) by
                                                                      rw [ eq_comm, Int.ediv_eq_of_eq_mul_left ] <;> norm_num [ ← pow_add, Nat.sub_add_cancel h_k_le ];
                                                                      rw [ Nat.sub_add_cancel ( by linarith ) ] ; norm_num [ pow_mul ] ] ; norm_num [ pow_add, pow_mul ] ; ring;
    by_cases h : Even k <;> simp_all +decide [ Nat.even_add_one ] <;> ring


end CancellationFreeBn


/-! ======== Rank1 Collapse Assembly ======== -/


-- The central valuation e_p = v_p(C(2n,n) · γ²).

-- Helper lemmas for rank-1 collapse

/-
PROBLEM
Algebraic discriminant factoring: if p divides the reduced discriminant,
    then p^{2e+1} divides the full discriminant.

PROVIDED SOLUTION
The expression (p^e * B')^2 - 4*(p^e * A')*(p^e * C') = p^{2e} * (B'^2 - 4*A'*C') by ring. Then p^{2e+1} = p^{2e} * p by pow_succ. Since p | B'^2 - 4*A'*C', we get p^{2e} * p | p^{2e} * (B'^2 - 4*A'*C') by mul_dvd_mul_left.
-/
lemma disc_dvd_step (p : ℤ) (e : ℕ) (A' B' C' : ℤ)
    (hdisc : p ∣ B' ^ 2 - 4 * A' * C') :
    p ^ (2 * e + 1) ∣ (p ^ e * B') ^ 2 - 4 * (p ^ e * A') * (p ^ e * C') := by
  obtain ⟨ k, hk ⟩ := hdisc; exact ⟨ k, by rw [ pow_add, pow_mul' ] ; linear_combination hk * p ^ ( 2 * e ) ⟩ ;

/-
PROBLEM
Central dominance: p^e divides each scalar coefficient C(2n,i)·α_i·β_i.
    This is equivalent to v_p(C(2(n+1), i+1)) ≤ v_p(C(2(n+1), n+1)) for all i,
    which holds when n+1 = p^k - 1 because adding (n+1)+(n+1) in base p
    produces carries at every position (maximum k carries).
    Hence p^e | A_eval(n,c) for all c.

PROVIDED SOLUTION
We need ∃ A', A_eval n c = p^e * A' where e = e_central p n = padicValNat p (C(2n,n) * γ(n)^2).

A_eval = Σ_i (-1)^i * C(2n,i) * α(n,i) * β(n,i) * c_i * c_{2n-i}.

It suffices to show p^e | each summand, i.e., p^e | C(2n,i)*α(n,i)*β(n,i) for each i ∈ range(2n+1).

Use dvd_sum: if p^e divides each summand, then p^e divides the sum. Factor out the c values and signs.

For the scalar divisibility: C(2n,i)*α(n,i)*β(n,i) = C(2n,i) * (2n+1-i)!*i! * (2n-i)!*(i+1)!.

By the Nat.choose formula: C(2n,i) * i! * (2n-i)! = (2n)!. So C(2n,i)*α_i*β_i = (2n)! * (2n+1-i)! * (i+1)!.

And C(2n,n)*γ^2 = C(2n,n) * ((n+1)!*n!)^2 = (2n)! / (n!)^2 * (n+1)!^2 * (n!)^2 = (2n)! * (n+1)!^2.

So we need p^e | (2n)!*(2n+1-i)!*(i+1)! where e = v_p((2n)!*(n+1)!^2).

Equivalently: v_p((2n+1-i)!*(i+1)!) ≥ v_p((n+1)!^2) = 2*v_p((n+1)!).

Setting a = i+1, b = 2n+1-i, a+b = 2(n+1). We need v_p(b!) + v_p(a!) ≥ 2*v_p((n+1)!).

By Legendre: v_p(a!) + v_p(b!) = Σ_l floor(a/p^l) + floor(b/p^l). And 2*v_p(m!) = Σ_l 2*floor(m/p^l) where m=n+1.

We need: for each l ≥ 1, floor(a/p^l) + floor(b/p^l) ≥ 2*floor(m/p^l) where a+b=2m.

This follows from: if a+b=2m, then floor(a/q) + floor((2m-a)/q) ≥ 2*floor(m/q) for any q ≥ 1.

Proof of this claim: Let m = q*d + r, 0 ≤ r < q. Then 2m = q*(2d) + 2r.
If a = q*a_d + a_r and 2m-a = q*b_d + b_r (with 0 ≤ a_r, b_r < q):
- If a_r + b_r < q: then a_d + b_d = 2d (no carry), so floor(a/q)+floor(b/q) = 2d = 2*floor(m/q). ✓
- If a_r + b_r ≥ q: then a_d + b_d = 2d-1 (with carry), but also 2r could be ≥ q or < q.
  Actually a_r + b_r ≡ 2r (mod q). If a_r+b_r ≥ q then a_r+b_r = 2r+q (if 2r < q) or 2r-q+q=2r (impossible since a_r+b_r ≥ q and a_r+b_r ≡ 2r).
  Case 2r < q: a_r+b_r = 2r+q ≥ q. a_d+b_d+1 = 2d+floor(2r/q) = 2d+0 = 2d. So a_d+b_d = 2d-1, floor(a/q)+floor(b/q) = 2d-1 < 2d = 2*floor(m/q).
  Wait, this breaks the inequality!

Hmm, the inequality floor(a/q)+floor(b/q) ≥ 2*floor(m/q) is NOT always true when a+b=2m. I was wrong.

Let me reconsider. The correct approach uses the SPECIFIC structure when n+1 = p^k - 1.

When m = n+1 = p^k - 1, m in base p is (p-1)(p-1)...(p-1) (k digits). For any l ≤ k: floor(m/p^l) = p^{k-l} - 1.

For l ≤ k: 2*floor(m/p^l) = 2(p^{k-l}-1).
floor(2m/p^l) = floor((2p^k-2)/p^l) = 2p^{k-l} - 1 for 1 ≤ l ≤ k.

So floor(a/p^l)+floor(b/p^l) ≥ floor((a+b)/p^l) - 1 = floor(2m/p^l) - 1 = 2p^{k-l} - 2 = 2*floor(m/p^l).

So for each l: floor(a/p^l)+floor(b/p^l) ≥ floor(2m/p^l) - 1 ≥ 2*floor(m/p^l) since floor(2m/p^l) = 2p^{k-l}-1 ≥ 2(p^{k-l}-1) + 1 > 2*floor(m/p^l).

Summing: v_p(a!)+v_p(b!) ≥ 2*v_p(m!). ✓

The key step uses: floor(a/q)+floor(b/q) ≥ floor((a+b)/q) - 1 (standard). And for m = p^k-1: floor(2m/p^l) ≥ 2*floor(m/p^l) + 1 for 1 ≤ l ≤ k (because 2m mod p^l = 2(p^k-1) mod p^l = p^l - 2 ≥ p^l/2 when p ≥ 3... actually 2r = 2(p^l-1) = 2p^l - 2 ≥ p^l for p ≥ 2 and l ≥ 1). So floor(2m/p^l) = 2*floor(m/p^l) + 1, and therefore floor(a/p^l)+floor(b/p^l) ≥ 2*floor(m/p^l)+1-1 = 2*floor(m/p^l). ✓

So the proof is:
1. Use dvd_sum to reduce to showing p^e | each summand's scalar coefficient
2. Show the scalar is (2n)!*(2n+1-i)!*(i+1)! and e = v_p((2n)!*(n+1)!^2)
3. Use Legendre + the p^k-1 structure of m to get the inequality

This is quite involved for the subagent. Try using Finset.dvd_sum and the p-adic valuation machinery from Mathlib.
-/
lemma A_eval_dvd_pe (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (c : ℕ → ℤ) :
    ∃ A' : ℤ, A_eval n c = (p : ℤ) ^ e_central p n * A' := by
  have h_scalar_div : ∀ i ∈ Finset.range (2 * n + 1), (p : ℤ) ^ (padicValNat p (Nat.choose (2 * n) n * (γ n) ^ 2)) ∣ (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) * (β n i : ℤ) := by
    intro i hi
    have h_div : (p : ℕ) ^ (padicValNat p (Nat.choose (2 * n) n * (γ n) ^ 2)) ∣ Nat.choose (2 * n) i * (α n i) * (β n i) := by
      -- By the properties of p-adic valuations, we can show that the p-adic valuation of the product is at least e.
      have h_val : padicValNat p (Nat.factorial (2 * n) * Nat.factorial (2 * n + 1 - i) * Nat.factorial (i + 1)) ≥ padicValNat p (Nat.factorial (2 * n) * Nat.factorial (n + 1) * Nat.factorial (n + 1)) := by
        -- By the properties of p-adic valuations, we can show that the p-adic valuation of the product is at least e. We'll use the fact that $a + b = 2(n+1)$.
        have h_val : ∀ l ≥ 1, (Nat.floor ((n + 1) / p ^ l) * 2) ≤ (Nat.floor ((2 * n + 1 - i) / p ^ l) + Nat.floor ((i + 1) / p ^ l)) := by
          intro l hl
          have h_floor : (Nat.floor ((n + 1) / p ^ l)) * 2 ≤ (Nat.floor ((2 * n + 1 - i) / p ^ l)) + (Nat.floor ((i + 1) / p ^ l)) := by
            have h_div : (n + 1) = p ^ k - 1 := by
              omega
            by_cases hl_le_k : l ≤ k <;> simp_all +decide [ Nat.div_eq_of_lt ];
            · -- Since $p^k - 1$ is divisible by $p^l - 1$, we have $(p^k - 1) / p^l = p^{k-l} - 1$.
              have h_div : (p ^ k - 1) / p ^ l = p ^ (k - l) - 1 := by
                have h_div : (p ^ k - 1) = p ^ l * (p ^ (k - l) - 1) + (p ^ l - 1) := by
                  zify [ hl_le_k ] ; ring; norm_num [ Nat.one_le_iff_ne_zero, show p ≠ 0 from Nat.Prime.ne_zero Fact.out ] ; ring;
                  rw [ ← pow_add, Nat.add_sub_of_le hl_le_k ];
                rw [ h_div, Nat.add_div ] <;> norm_num [ Nat.div_eq_of_lt, Nat.sub_lt ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) zero_lt_one ];
                · rw [ Nat.mul_div_cancel_left _ ( pow_pos ( Nat.Prime.pos Fact.out ) _ ), if_neg ( Nat.not_le_of_gt ( Nat.sub_lt ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) zero_lt_one ) ) ] ; norm_num;
                · exact pow_pos ( Nat.Prime.pos Fact.out ) _;
              have h_div : (2 * n + 1 - i) / p ^ l + (i + 1) / p ^ l ≥ (2 * (p ^ k - 1)) / p ^ l - 1 := by
                have h_div : (2 * n + 1 - i) / p ^ l + (i + 1) / p ^ l ≥ ((2 * n + 1 - i) + (i + 1)) / p ^ l - 1 := by
                  norm_num [ Nat.add_div ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) ];
                  split_ifs <;> norm_num;
                grind +ring;
              have h_div : 2 * (p ^ k - 1) / p ^ l = 2 * (p ^ (k - l) - 1) + 2 * (p ^ l - 1) / p ^ l := by
                have h_div : 2 * (p ^ k - 1) = 2 * (p ^ (k - l) - 1) * p ^ l + 2 * (p ^ l - 1) := by
                  zify [ pow_add, pow_sub ] ; ring;
                  cases le_iff_exists_add'.mp hl_le_k ; simp_all +decide [ pow_add, pow_mul ] ; ring;
                  cases p <;> cases ‹ℕ› <;> norm_num at * ; linarith;
                rw [ h_div, Nat.add_div ] <;> norm_num [ Nat.pow_pos ( Nat.Prime.pos Fact.out ) ];
                exact Nat.mod_lt _ ( pow_pos ( Nat.Prime.pos Fact.out ) _ );
              have h_div : 2 * (p ^ l - 1) / p ^ l ≥ 1 := by
                exact Nat.div_pos ( by linarith [ Nat.sub_add_cancel ( Nat.one_le_pow l p ( Nat.Prime.pos Fact.out ) ), show p ^ l > 1 from one_lt_pow₀ ( Nat.Prime.one_lt Fact.out ) ( by linarith ) ] ) ( pow_pos ( Nat.Prime.pos Fact.out ) _ );
              omega;
            · rw [ Nat.div_eq_of_lt ( show p ^ k - 1 < p ^ l from lt_of_lt_of_le ( Nat.sub_lt ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) zero_lt_one ) ( pow_le_pow_right₀ ( Nat.Prime.pos Fact.out ) hl_le_k.le ) ) ] ; norm_num;
          exact h_floor;
        -- Applying the formula for the p-adic valuation of factorials, we can rewrite the inequality in terms of sums of floor functions.
        have h_floor_sum : ∑ l ∈ Finset.Ico 1 (Nat.log p (2 * n + 1) + 1), (Nat.floor ((2 * n) / p ^ l) + Nat.floor ((2 * n + 1 - i) / p ^ l) + Nat.floor ((i + 1) / p ^ l)) ≥ ∑ l ∈ Finset.Ico 1 (Nat.log p (2 * n + 1) + 1), (Nat.floor ((2 * n) / p ^ l) + Nat.floor ((n + 1) / p ^ l) + Nat.floor ((n + 1) / p ^ l)) := by
          exact Finset.sum_le_sum fun x hx => by linarith [ h_val x ( Finset.mem_Ico.mp hx |>.1 ) ] ;
        have h_floor_sum : padicValNat p ((2 * n)! * (2 * n + 1 - i)! * (i + 1)!) = ∑ l ∈ Finset.Ico 1 (Nat.log p (2 * n + 1) + 1), (Nat.floor ((2 * n) / p ^ l) + Nat.floor ((2 * n + 1 - i) / p ^ l) + Nat.floor ((i + 1) / p ^ l)) := by
          rw [ padicValNat.mul, padicValNat.mul ] <;> simp_all +decide [ Nat.factorial_ne_zero ];
          haveI := Fact.mk ( Fact.out : Nat.Prime p ) ; rw [ padicValNat_factorial, padicValNat_factorial, padicValNat_factorial ] ; simp +decide [ Finset.sum_add_distrib ] ;
          congr! 1;
          · exact Nat.lt_succ_of_le ( Nat.log_mono_right ( by linarith ) );
          · exact Nat.lt_succ_of_le ( Nat.log_mono_right <| Nat.sub_le _ _ );
          · exact Nat.lt_succ_of_le ( Nat.log_mono_right ( Nat.le_succ _ ) );
        have h_floor_sum : padicValNat p ((2 * n)! * (n + 1)! * (n + 1)!) = ∑ l ∈ Finset.Ico 1 (Nat.log p (2 * n + 1) + 1), (Nat.floor ((2 * n) / p ^ l) + Nat.floor ((n + 1) / p ^ l) + Nat.floor ((n + 1) / p ^ l)) := by
          rw [ padicValNat.mul, padicValNat.mul ] <;> norm_num [ Nat.factorial_ne_zero ];
          haveI := Fact.mk ( Fact.out : Nat.Prime p ) ; rw [ padicValNat_factorial, padicValNat_factorial ] ; simp +decide [ Finset.sum_add_distrib ] ; ring;
          · exact Nat.lt_succ_of_le ( Nat.log_mono_right <| by linarith );
          · exact Nat.lt_succ_of_le ( Nat.log_mono_right ( Nat.le_succ _ ) );
        grind;
      -- By the properties of p-adic valuations, we can show that the p-adic valuation of the product is at least e. Hence, $p^e$ divides the product.
      have h_div : p ^ (padicValNat p (Nat.factorial (2 * n) * Nat.factorial (n + 1) * Nat.factorial (n + 1))) ∣ Nat.factorial (2 * n) * Nat.factorial (2 * n + 1 - i) * Nat.factorial (i + 1) := by
        refine' dvd_trans ( pow_dvd_pow _ h_val ) _;
        convert Nat.ordProj_dvd _ _ using 1;
        rw [ Nat.factorization_def ];
        exact Fact.out;
      convert h_div using 1;
      · unfold γ; rw [ Nat.choose_eq_factorial_div_factorial ( by linarith ) ] ; ring;
        rw [ show n * 2 - n = n by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring;
        rw [ show n ! ^ 2 * ( ( n * 2 ) ! / n ! ^ 2 ) = ( n * 2 ) ! from Nat.mul_div_cancel' <| by rw [ sq ] ; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| by ring_nf; norm_num ] ; ring;
      · unfold α β; simp +decide [ Nat.choose_eq_factorial_div_factorial ( show i ≤ 2 * n from Finset.mem_range_succ_iff.mp hi ) ] ; ring;
        rw [ Nat.mul_div_cancel' ( Nat.factorial_mul_factorial_dvd_factorial ( by linarith [ Finset.mem_range.mp hi ] ) ) ] ; ring!;
    convert Int.natCast_dvd_natCast.mpr h_div |> fun x => x.mul_left ( ( -1 : ℤ ) ^ i ) using 1 ; push_cast ; ring;
  exact Finset.dvd_sum fun i hi => dvd_mul_of_dvd_left ( h_scalar_div i hi ) _ |> dvd_mul_of_dvd_left <| _

/-
PROBLEM
Same as A_eval_dvd_pe but for C_eval. Identical proof since A and C
    have the same scalar coefficients.

PROVIDED SOLUTION
The proof is essentially the same as A_eval_dvd_pe. C_eval has the same scalar coefficients C(2n,i)*α(n,i)*β(n,i) as A_eval. The only difference is which c values are multiplied. Since we need p^e to divide the scalar part (not the c values), the same divisibility argument applies.

Use dvd_sum to reduce to showing p^e divides each summand. Each summand has scalar factor C(2n,i)*α(n,i)*β(n,i) which is divisible by p^e by the same central dominance argument as for A_eval.
-/
lemma C_eval_dvd_pe (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (c : ℕ → ℤ) :
    ∃ C' : ℤ, C_eval n c = (p : ℤ) ^ e_central p n * C' := by
  convert A_eval_dvd_pe p k hk hp_odd n hn hn_pos ( fun i => -c ( i + 1 ) ) using 1 ; ring;
  unfold C_eval A_eval; ring;
  exact funext fun x => by rw [ Finset.sum_congr rfl ] ; intros; rw [ Nat.add_sub_assoc ( by linarith [ Finset.mem_range.mp ‹_› ] ) ] ;

/-
PROBLEM
Rank-1 collapse: p^{2e+1} divides Δ_eval(n,c) for all c,
where e = e_central = v_p(C(2n,n) · γ²).

Proof outline:
1. Split the sums in A_eval, B_eval, C_eval into i ∈ {n-1,n,n+1} and the rest.
2. The "rest" contributes at valuation ≥ e+1, so modulo p^{e+1} only central terms survive.
3. Compute A^# = A_eval/p^e ≡ λ f_n² c_n c_n (mod p), etc.
4. The discriminant (B^#)² - 4A^#C^# ≡ 4λ²(f_n f_{n+1})² - 4λ²(f_n f_{n+1})² = 0 (mod p).
5. Therefore p | Δ_eval/p^{2e}, i.e., p^{2e+1} | Δ_eval.

PROVIDED SOLUTION
Use the helper lemmas:
1. Obtain A' from A_eval_dvd_pe, B' from B_eval_dvd_pe, C' from C_eval_dvd_pe
2. Get hmod from reduced_disc_dvd_p applied to A', B', C' with their defining equations
3. Unfold Δ_eval, rewrite using hA, hB, hC
4. Apply disc_dvd_step with hmod

Concretely:
  obtain ⟨A', hA⟩ := A_eval_dvd_pe p k hk hp_odd n hn hn_pos c
  obtain ⟨B', hB⟩ := B_eval_dvd_pe p k hk hp_odd n hn hn_pos c
  obtain ⟨C', hC⟩ := C_eval_dvd_pe p k hk hp_odd n hn hn_pos c
  have hmod := reduced_disc_dvd_p p k hk hp_odd n hn hn_pos c A' B' C' hA hB hC
  unfold Δ_eval
  rw [hA, hB, hC]
  exact disc_dvd_step (↑p) (e_central p n) A' B' C' hmod
-/


/-! ReducedDisc helpers -/


/-
PROBLEM
============================================================
Helper lemmas about α, β, γ
============================================================

α(n, n) = γ(n).

PROVIDED SOLUTION
α(n, n) = (2n+1-n)! * n! = (n+1)! * n! = γ(n). Just unfold definitions.
-/
/-
PROBLEM
β(n, n) = γ(n).

PROVIDED SOLUTION
β(n, n) = (2n-n)! * (n+1)! = n! * (n+1)! = γ(n). Unfold and use mul_comm.
-/
/-
PROBLEM
β(n, n-1) = γ(n) for n ≥ 1.

PROVIDED SOLUTION
β(n, n-1) = (2n-(n-1))! * ((n-1)+1)! = (n+1)! * n! = γ(n). Use omega to simplify 2n-(n-1) = n+1 and (n-1)+1 = n.
-/
/-
PROBLEM
α(n, n+1) = γ(n).

PROVIDED SOLUTION
α(n, n+1) = (2n+1-(n+1))! * (n+1)! = n! * (n+1)! = γ(n). Use omega and mul_comm.
-/
/-
PROBLEM
α(n, n-1) · n = (n+2) · γ(n) for n ≥ 1.

PROVIDED SOLUTION
α(n, n-1) = (2n+1-(n-1))! * (n-1)! = (n+2)! * (n-1)!. And γ(n) = (n+1)! * n!. So α(n,n-1) * n = (n+2)! * (n-1)! * n = (n+2)! * n!. And (n+2) * γ(n) = (n+2) * (n+1)! * n! = (n+2)! * n!. Use: unfold α γ, then show 2*n+1-(n-1) = n+2 (by omega), (n-1)! * n = n!/1... actually (n-1)! * n = n! and (n+2) * (n+1)! = (n+2)!. These are instances of Nat.factorial_succ.
-/
/-
PROBLEM
β(n, n+1) · n = (n+2) · γ(n) for n ≥ 1.

PROVIDED SOLUTION
β(n, n+1) = (2n-(n+1))! * (n+2)! = (n-1)! * (n+2)!. And γ(n) = (n+1)! * n!. So β(n,n+1)*n = (n-1)!*(n+2)!*n. And (n+2)*γ(n) = (n+2)*(n+1)!*n! = (n+2)!*n!. We need (n-1)!*(n+2)!*n = (n+2)!*n!. This follows from (n-1)!*n = n! (Nat.factorial_succ). Unfold β, γ. Need 2*n-(n+1) = n-1 by omega. Then use mul_comm and Nat.factorial_succ.
-/
/-
PROBLEM
============================================================
Binomial coefficient identities
============================================================

C(2n, n-1) · (n+1) = C(2n, n) · n.

PROVIDED SOLUTION
Use Nat.choose_succ_right_eq: C(2n, n) = C(2n, n-1) + C(2n-1, n). But actually, the standard identity is C(m, k+1) = C(m, k) * (m-k) / (k+1). With m=2n, k=n-1: C(2n, n) = C(2n, n-1) * (2n-(n-1)) / n = C(2n, n-1) * (n+1) / n. So C(2n, n-1) * (n+1) = C(2n, n) * n. Alternatively, use Nat.choose_succ_right_eq to relate C(2n, n) and C(2n, n-1), then multiply through.
-/
/-
PROBLEM
C(2n, n+1) = C(2n, n-1).

PROVIDED SOLUTION
C(2n, n+1) = C(2n, 2n-(n+1)) = C(2n, n-1) by Nat.choose_symm. Note 2n - (n+1) = n-1 when n ≥ 1.
-/
/-
PROBLEM
============================================================
Algebraic lemma: approximate square ⟹ discriminant divisibility
============================================================

If A' ≡ μa², B' ≡ 2μab, C' ≡ μb² (mod p), then p | B'²-4A'C'.

PROVIDED SOLUTION
Write A' = μa² + p·r₁, B' = 2μab + p·r₂, C' = μb² + p·r₃. Then B'² - 4A'C' = (2μab + p·r₂)² - 4(μa² + p·r₁)(μb² + p·r₃) = 4μ²a²b² + 4pμab·r₂ + p²r₂² - 4μ²a²b² - 4pμa²r₃ - 4pμb²r₁ - 4p²r₁r₃ = p(4μab·r₂ - 4μa²r₃ - 4μb²r₁ + p(r₂² - 4r₁r₃)). Extract r₁, r₂, r₃ from hA, hB, hC using dvd_iff, then compute the ring identity.
-/
lemma disc_of_approx_square (p : ℤ) (A' B' C' μ a b : ℤ)
    (hA : p ∣ A' - μ * a ^ 2)
    (hB : p ∣ B' - 2 * μ * a * b)
    (hC : p ∣ C' - μ * b ^ 2) :
    p ∣ B' ^ 2 - 4 * A' * C' := by
  -- Using the congruences for A', B', and C', substitute them into B'²-4A'C'.
  have h_sub : B' ^ 2 - 4 * A' * C' ≡ (2 * μ * a * b) ^ 2 - 4 * (μ * a ^ 2) * (μ * b ^ 2) [ZMOD p] := by
    gcongr <;> simp_all +decide [ Int.modEq_iff_dvd ];
    · rwa [ dvd_sub_comm ];
    · rwa [ dvd_sub_comm ];
    · rwa [ dvd_sub_comm ];
  exact Int.dvd_of_emod_eq_zero ( h_sub.symm ▸ by ring_nf; norm_num )

-- ============================================================
-- Central dominance (from Sub04_CentralDominance.lean)
-- These are proved in Sub04; we state them here as local lemmas.
-- ============================================================


/-
PROBLEM
The central valuations are all equal.

PROVIDED SOLUTION
Unfold scalar_AB, scalar_A2, scalar_B2, α, β, γ. At i=n: α(n,n) = γ(n) and β(n,n) = γ(n). So scalar_AB(n,n) = C(2n,n) * γ * γ = C(2n,n) * γ², scalar_A2(n,n) = C(2n,n) * γ², scalar_B2(n,n) = C(2n,n) * γ². They're all equal (after using α_eq_γ and β_eq_γ and ring).
-/
/-
PROBLEM
============================================================
Key valuation equalities at non-excluded boundary indices
============================================================

scalar_A2(n, n+1) has the same p-adic valuation as scalar_A2(n, n).

PROVIDED SOLUTION
scalar_A2(n,n+1) = C(2n,n+1) * α(n,n+1)² = C(2n,n+1) * γ² (by alpha_n_plus_one_eq). scalar_A2(n,n) = C(2n,n) * γ² (by α_eq_γ). So their ratio is C(2n,n+1)/C(2n,n) = C(2n,n-1)/C(2n,n) (by choose_symm_n). And C(2n,n-1)*(n+1) = C(2n,n)*n (by choose_n_minus_one). Since p ∤ n and p ∤ (n+1) (because n+2 = p^k implies n = p^k-2, n+1 = p^k-1, and p ∤ (p^k-1) and p ∤ (p^k-2) for odd p ≥ 3), the p-adic valuation is the same.
-/
lemma scalar_A2_n_plus_one_val (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (hp_odd : p ≠ 2) :
    padicValNat p (scalar_A2 n (n + 1)) = padicValNat p (scalar_A2 n n) := by
  unfold scalar_A2;
  -- Using the identity $\binom{2n}{n+1} = \binom{2n}{n-1}$ and $\binom{2n}{n-1} \cdot (n+1) = \binom{2n}{n} \cdot n$, we can simplify the ratio.
  have h_ratio : Nat.choose (2 * n) (n + 1) * (n + 1) = Nat.choose (2 * n) n * n := by
    nlinarith [ Nat.add_one_mul_choose_eq ( 2 * n ) n, Nat.choose_succ_succ ( 2 * n ) n ];
  -- Since $p$ is odd, $p \nmid n$ and $p \nmid (n+1)$, so their $p$-adic valuations are zero.
  have h_p_not_div_n : ¬(p ∣ n) := by
    intro h;
    obtain ⟨ m, hm ⟩ := h; replace hn := congr_arg ( · % p ) hn; norm_num [ Nat.add_mod, Nat.pow_mod, Nat.mul_mod, hm, Nat.mod_eq_of_lt ( show p > 1 from Fact.out ), show k ≠ 0 from ne_of_gt hk ] at hn;
    rcases p with ( _ | _ | _ | p ) <;> trivial
  have h_p_not_div_n_plus_one : ¬(p ∣ (n + 1)) := by
    intro h;
    have := Nat.dvd_sub ( dvd_pow_self p ( by linarith : k ≠ 0 ) ) h; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
    simp_all +decide [ ← hn ];
  -- Using the equality from h_ratio and the fact that p doesn't divide n or n+1, we can conclude that the p-adic valuations are equal.
  have h_val_eq : padicValNat p ((Nat.choose (2 * n) (n + 1)) * (n + 1)) = padicValNat p ((Nat.choose (2 * n) n) * n) := by
    rw [h_ratio];
  rw [ padicValNat.mul, padicValNat.mul ] at h_val_eq <;> simp_all +decide [ Nat.factorial_ne_zero ];
  · rw [ padicValNat.mul, padicValNat.mul ] <;> simp_all +decide [ Nat.factorial_ne_zero, padicValNat.eq_zero_of_not_dvd ];
    · rw [ alpha_n_plus_one_eq, α_eq_γ ];
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
    · exact Nat.ne_of_gt ( Nat.mul_pos ( Nat.factorial_pos _ ) ( Nat.factorial_pos _ ) );
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
    · exact Nat.ne_of_gt ( Nat.mul_pos ( Nat.factorial_pos _ ) ( Nat.factorial_pos _ ) );
  · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
  · linarith;
  · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;

/-
PROBLEM
scalar_B2(n, n-1) has the same p-adic valuation as scalar_B2(n, n).

PROVIDED SOLUTION
scalar_B2(n,n-1) = C(2n,n-1) * β(n,n-1)² = C(2n,n-1) * γ² (by beta_n_minus_one_eq). scalar_B2(n,n) = C(2n,n) * γ² (by β_eq_γ). Their ratio is C(2n,n-1)/C(2n,n). From choose_n_minus_one: C(2n,n-1)*(n+1) = C(2n,n)*n. Since p ∤ n and p ∤ (n+1) (because n+2=p^k, p odd ≥ 3), their p-adic valuations are equal.
-/
lemma scalar_B2_n_minus_one_val (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (hp_odd : p ≠ 2) :
    padicValNat p (scalar_B2 n (n - 1)) = padicValNat p (scalar_B2 n n) := by
  simp +decide [ scalar_B2 ];
  -- Since $p \nmid n$ and $p \nmid (n+1)$, their p-adic valuations are equal.
  have h_val_eq : padicValNat p (Nat.choose (2 * n) (n - 1)) = padicValNat p (Nat.choose (2 * n) n) := by
    have h_ratio : Nat.choose (2 * n) (n - 1) * (n + 1) = Nat.choose (2 * n) n * n := by
      exact?;
    have h_val_eq : ¬(p ∣ n) ∧ ¬(p ∣ (n + 1)) := by
      constructor <;> intro h <;> have := Nat.dvd_sub ( show p ∣ n + 2 from hn.symm ▸ dvd_pow_self _ ( by linarith ) ) h <;> norm_num at this;
      · have := Nat.le_of_dvd ( by decide ) this; interval_cases p <;> simp_all +decide ;
      · norm_num [ Nat.succ_sub ] at this ; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime Fact.out ];
    apply_fun fun x => x.factorization p at h_ratio ; simp_all +decide [ Nat.factorization_mul, ne_of_gt ( Nat.choose_pos ( show n ≤ 2 * n by linarith ) ), ne_of_gt ( Nat.choose_pos ( show n - 1 ≤ 2 * n by omega ) ) ] ;
    rw [ Nat.factorization_mul ( Nat.ne_of_gt ( Nat.choose_pos ( by linarith ) ) ) ( by linarith ) ] at h_ratio ; simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
    rw [ ← Nat.factorization_def, ← Nat.factorization_def, h_ratio ];
    · exact Fact.out;
    · exact Fact.out;
  rw [ padicValNat.mul, padicValNat.mul ] <;> simp_all +decide [ Nat.choose_eq_zero_iff ];
  · rw [ beta_n_minus_one_eq n hn_pos, β_eq_γ ];
  · linarith;
  · exact mul_ne_zero ( Nat.factorial_ne_zero _ ) ( Nat.factorial_ne_zero _ );
  · linarith;
  · exact mul_ne_zero ( Nat.factorial_ne_zero _ ) ( Nat.factorial_ne_zero _ )

/-
PROBLEM
============================================================
Sum extraction lemma
============================================================

If a sum = p^e * X, one term = p^e * Y, and all other terms ≡ 0 (mod p^{e+1}),
then p | X - Y.

PROVIDED SOLUTION
Rewrite the sum as f(j) + Σ_{i≠j} f(i) using Finset.add_sum_erase. Then Σ_{i≠j} f(i) is divisible by p^(e+1) (by Finset.dvd_sum and hrest). So p^e * X = p^e * Y + p^(e+1) * R for some R. Dividing by p^e: X = Y + p * R, so p | X - Y.
-/
lemma sum_extract_mod (p : ℕ) [Fact p.Prime] (e : ℕ) (S : Finset ℕ) (j : ℕ) (hj : j ∈ S)
    (f : ℕ → ℤ) (X Y : ℤ)
    (hsum : ∑ i ∈ S, f i = (p : ℤ) ^ e * X)
    (hj_val : f j = (p : ℤ) ^ e * Y)
    (hrest : ∀ i ∈ S, i ≠ j → (p : ℤ) ^ (e + 1) ∣ f i) :
    (p : ℤ) ∣ X - Y := by
  -- Rewrite the sum as f(j) + Σ_{i≠j} f(i) using Finset.add_sum_erase.
  have hsum_rewrite : (p : ℤ) ^ e * X = (p : ℤ) ^ e * Y + ∑ i ∈ S.erase j, f i := by
    rw [ ← hsum, ← hj_val, ← Finset.sum_erase_add _ _ hj, add_comm ];
  -- Since $p^{e+1}$ divides $\sum_{i \in S \setminus \{j\}} f(i)$, we can write $\sum_{i \in S \setminus \{j\}} f(i) = p^{e+1} \cdot R$ for some integer $R$.
  obtain ⟨R, hR⟩ : ∃ R : ℤ, ∑ i ∈ S.erase j, f i = (p : ℤ) ^ (e + 1) * R := by
    exact Finset.dvd_sum fun i hi => hrest i ( Finset.mem_of_mem_erase hi ) ( Finset.ne_of_mem_erase hi );
  exact ⟨ R, by rw [ pow_succ' ] at hR; nlinarith [ pow_pos ( show 0 < ( p : ℤ ) by exact Nat.cast_pos.mpr ( Nat.Prime.pos Fact.out ) ) e ] ⟩

/-
PROBLEM
============================================================
Relating e_central to scalar_AB
============================================================

PROVIDED SOLUTION
By definition, e_central p n = padicValNat p (C(2n,n) * γ(n)^2). And scalar_AB(n,n) = C(2n,n) * α(n,n) * β(n,n) = C(2n,n) * γ * γ = C(2n,n) * γ². Use α_eq_γ and β_eq_γ to rewrite, then the definitions match.
-/
lemma e_central_eq_scalar_AB (p : ℕ) [Fact p.Prime] (n : ℕ) :
    e_central p n = padicValNat p (scalar_AB n n) := by
  unfold e_central scalar_AB;
  rw [ show α n n = γ n from α_eq_γ n, show β n n = γ n from β_eq_γ n, pow_two ];
  rw [ mul_assoc ]

/-
PROBLEM
scalar_AB(n,n) = p^e * (scalar_AB n n / p^e) with p^e dividing.

PROVIDED SOLUTION
By definition of padicValNat, p^(padicValNat p m) divides m (when m ≠ 0 and p is prime). Since scalar_AB n n = C(2n,n)*γ² > 0 (as products of factorials and binomial coefficients), we have p^e | scalar_AB n n. Then scalar_AB n n = p^e * (scalar_AB n n / p^e) by Nat.div_mul_cancel. Use e_central_eq to relate e to padicValNat p (scalar_AB n n), then use Nat.ord_proj_dvd or pow_padicValNat_dvd.
-/
lemma scalar_AB_factor (p : ℕ) [Fact p.Prime] (n : ℕ) :
    scalar_AB n n = p ^ (e_central p n) * (scalar_AB n n / p ^ (e_central p n)) := by
  rw [ Nat.mul_div_cancel' ];
  convert Nat.ordProj_dvd ( scalar_AB n n ) p using 1;
  unfold scalar_AB e_central;
  unfold α β γ;
  norm_num [ two_mul, add_assoc, Nat.factorial_ne_zero, Nat.factorization ] ; ring;
  rw [ if_pos Fact.out ]

/-
PROBLEM
============================================================
A' congruence
============================================================

A' ≡ μ * c_n² (mod p) where μ = (-1)^n * (scalar_AB n n / p^e).

PROVIDED SOLUTION
Apply sum_extract_mod with j = n, f(i) = (-1)^i * C(2n,i) * α_i * β_i * c_i * c_{2n-i}, X = A', Y = (-1)^n * μ₀ * c_n², where μ₀ = scalar_AB n n / p^e.

Step 1: Show j ∈ S. n ∈ Finset.range(2n+1) since n < 2n+1 for n ≥ 1.

Step 2: Show hsum. By definition of A_eval, Σ f(i) = A_eval = p^e * A'.

Step 3: Show hj_val. f(n) = (-1)^n * C(2n,n) * α_n * β_n * c_n * c_n = (-1)^n * scalar_AB(n,n) * c_n². Since scalar_AB(n,n) = p^e * μ₀ (by scalar_AB_factor), f(n) = p^e * (-1)^n * μ₀ * c_n² = p^e * Y.

Step 4: Show hrest. For i ≠ n with i ∈ range(2n+1): f(i) = (-1)^i * scalar_AB(n,i) * c_i * c_{2n-i}. By scalar_AB_central_min, padicValNat p (scalar_AB(n,i)) > e, so p^(e+1) | scalar_AB(n,i), hence p^(e+1) | f(i).
-/
lemma A_eval_cong (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (c : ℕ → ℤ)
    (A' : ℤ) (hA : A_eval n c = (p : ℤ) ^ e_central p n * A') :
    (p : ℤ) ∣ A' - (-1 : ℤ) ^ n * ↑(scalar_AB n n / p ^ e_central p n) * (c n) ^ 2 := by
  convert sum_extract_mod p ( e_central p n ) ( Finset.range ( 2 * n + 1 ) ) ( n : ℕ ) _ _ _ _ _ _ _ using 1;
  case convert_2 => exact fun i => ( -1 : ℤ ) ^ i * ( Nat.choose ( 2 * n ) i : ℤ ) * α n i * β n i * c i * c ( 2 * n - i );
  · simp +arith +decide;
  · convert hA using 1;
  · rw [ ← Nat.mul_div_cancel' ( show p ^ e_central p n ∣ scalar_AB n n from by
                                  convert Nat.ordProj_dvd ( scalar_AB n n ) p using 1;
                                  rw [ e_central_eq ] ; norm_num [ Nat.factorization ] ; ring;
                                  exact fun h => False.elim <| h <| Fact.out ) ] ; ring!;
    rw [ Nat.mul_div_cancel_left _ ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) ] ; norm_num [ show n * 2 - n = n by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring;
    rw [ ← Int.mul_ediv_assoc ];
    · exact Eq.symm ( Int.ediv_eq_of_eq_mul_left ( pow_ne_zero _ ( Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero Fact.out ) ) <| by push_cast [ scalar_AB ] ; ring );
    · norm_cast;
      convert Nat.ordProj_dvd ( scalar_AB n n ) p using 1;
      rw [ e_central_eq ] ; norm_num [ Nat.factorization ] ; ring;
      exact fun h => False.elim <| h <| Fact.out;
  · intro i hi hne
    have h_div : padicValNat p (scalar_AB n i) > e_central p n := by
      rw [ e_central_eq ];
      apply scalar_AB_central_min p k hk n hn i (Finset.mem_range_succ_iff.mp hi) hne;
    have h_div : (p : ℤ) ^ (e_central p n + 1) ∣ scalar_AB n i := by
      norm_cast;
      refine' Nat.dvd_trans ( pow_dvd_pow _ h_div ) _;
      exact?;
    convert h_div.mul_left ( ( -1 : ℤ ) ^ i * c i * c ( 2 * n - i ) ) using 1 ; push_cast [ scalar_AB ] ; ring

/-
PROBLEM
C' ≡ μ * c_{n+1}² (mod p).

PROVIDED SOLUTION
Same approach as A_eval_cong, using sum_extract_mod with j=n. The only difference is that C_eval uses c(i+1)*c(2n+1-i) instead of c(i)*c(2n-i). At i=n: c(n+1)*c(n+1) = c(n+1)². The scalar_AB central dominance argument is identical.
-/
lemma C_eval_cong (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (c : ℕ → ℤ)
    (C' : ℤ) (hC : C_eval n c = (p : ℤ) ^ e_central p n * C') :
    (p : ℤ) ∣ C' - (-1 : ℤ) ^ n * ↑(scalar_AB n n / p ^ e_central p n) * (c (n + 1)) ^ 2 := by
  by_contra h_contra';
  convert A_eval_cong p k hk n hn hn_pos ( fun i => c ( i + 1 ) ) _ _ using 1;
  rotate_left;
  exact C';
  · convert hC using 1;
    unfold A_eval C_eval; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    exact Finset.sum_congr rfl fun x hx => by rw [ tsub_add_eq_add_tsub ( by linarith [ Finset.mem_range.mp hx ] ) ] ;
  · aesop

/-
PROBLEM
Helper: scalar_A2(n,n) = scalar_AB(n,n) = scalar_B2(n,n)

PROVIDED SOLUTION
Unfold scalar_A2 and scalar_AB. scalar_A2(n,n) = C(2n,n)*α(n,n)^2 = C(2n,n)*γ^2. scalar_AB(n,n) = C(2n,n)*α(n,n)*β(n,n) = C(2n,n)*γ*γ = C(2n,n)*γ^2. Use α_eq_γ, β_eq_γ, sq.
-/
/-
PROVIDED SOLUTION
Same as scalar_A2_n_eq but with β. Unfold, use β_eq_γ, α_eq_γ.
-/
/-
PROBLEM
scalar_A2(n,n+1) = C(2n,n-1) * γ² (for n ≥ 1)

PROVIDED SOLUTION
scalar_A2(n,n+1) = C(2n,n+1)*α(n,n+1)^2 = C(2n,n+1)*γ^2 (by alpha_n_plus_one_eq). Then C(2n,n+1) = C(2n,n-1) by choose_symm_n.
-/
lemma scalar_A2_n_plus_one (n : ℕ) (hn : 1 ≤ n) :
    scalar_A2 n (n + 1) = Nat.choose (2 * n) (n - 1) * (γ n) ^ 2 := by
  -- Substitute the definition of scalar_A2 and use alpha_n_plus_one_eq.
  have h_subst : scalar_A2 n (n + 1) = Nat.choose (2 * n) (n + 1) * (γ n) ^ 2 := by
    -- Substitute the definition of scalar_A2 and use alpha_n_plus_one_eq to simplify.
    simp [scalar_A2, alpha_n_plus_one_eq];
  rw [ h_subst, choose_symm_n ];
  linarith

/-
PROBLEM
scalar_B2(n,n-1) = C(2n,n-1) * γ² (for n ≥ 1)

PROVIDED SOLUTION
scalar_B2(n,n-1) = C(2n,n-1)*β(n,n-1)^2 = C(2n,n-1)*γ^2 (by beta_n_minus_one_eq).
-/
lemma scalar_B2_n_minus_one (n : ℕ) (hn : 1 ≤ n) :
    scalar_B2 n (n - 1) = Nat.choose (2 * n) (n - 1) * (γ n) ^ 2 := by
  -- By definition of scalar_B2, we have:
  simp [scalar_B2, γ];
  exact Or.inl ( beta_n_minus_one_eq n hn )

/-
PROBLEM
(n+1) divides C(2n,n): the Catalan number is an integer

PROVIDED SOLUTION
This is the Catalan number identity: C(2n,n)/(n+1) is the Catalan number. In Mathlib, try Nat.choose_central_dvd or the identity C(2n,n) = (n+1) * Nat.centralBinom n / (2n+1)... Actually, use the fact that C(2n+1,n+1) = C(2n,n) + C(2n,n+1) and C(2n+1,n+1) = (2n+1)!/(n!(n+1)!) while C(2n,n) = (2n)!/(n!n!). So C(2n+1,n+1)*(n+1) = (2n+1)!/(n!n!) = (2n+1)*C(2n,n). Hence C(2n,n)*(n+1) divides... hmm this is circular. Actually, just use Nat.succ_dvd_choose_two_mul_self or search for the right Mathlib lemma.
-/
lemma n_plus_one_dvd_choose (n : ℕ) : (n + 1) ∣ Nat.choose (2 * n) n := by
  have h := Nat.succ_mul_choose_eq ( 2 * n ) n;
  rw [ Nat.choose_succ_succ ] at h;
  exact ⟨ Nat.choose ( 2 * n ) n - Nat.choose ( 2 * n ) ( n + 1 ), by rw [ Nat.mul_sub_left_distrib, eq_tsub_iff_add_eq_of_le ] <;> nlinarith ⟩

/-
PROBLEM
Key bracket identity: (n+1)*(2s - s1 - s2) = 2s where
s = scalar_AB(n,n), s1 = scalar_A2(n,n+1), s2 = scalar_B2(n,n-1)

PROVIDED SOLUTION
Rewrite scalar_A2_n_plus_one and scalar_B2_n_minus_one: both equal C(2n,n-1)*γ². And scalar_AB(n,n) = C(2n,n)*γ² (since α_n = β_n = γ, use scalar_AB def and α_eq_γ, β_eq_γ). So:
2*scalar_AB - scalar_A2(n,n+1) - scalar_B2(n,n-1) = 2*C(2n,n)*γ² - 2*C(2n,n-1)*γ² = 2γ²*(C(2n,n) - C(2n,n-1)).
And (n+1)*(C(2n,n) - C(2n,n-1)) = (n+1)*C(2n,n) - (n+1)*C(2n,n-1). By choose_n_minus_one: C(2n,n-1)*(n+1) = C(2n,n)*n. So (n+1)*C(2n,n) - C(2n,n)*n = C(2n,n). Hence (n+1)*bracket = 2γ²*C(2n,n) = 2*scalar_AB(n,n).
-/
lemma bracket_eq (n : ℕ) (hn : 1 ≤ n) :
    (n + 1) * (2 * scalar_AB n n - scalar_A2 n (n + 1) - scalar_B2 n (n - 1))
      = 2 * scalar_AB n n := by
  -- By definition of scalar_AB, scalar_A2, and scalar_B2.
  unfold scalar_AB scalar_A2 scalar_B2
  simp [α_eq_γ, β_eq_γ] at *;
  rw [ Nat.sub_sub, mul_tsub ];
  rw [ Nat.sub_eq_of_eq_add ];
  rw [ show α n ( n + 1 ) = γ n from alpha_n_plus_one_eq n, show β n ( n - 1 ) = γ n from beta_n_minus_one_eq n hn ] ; ring;
  rw [ show 1 + n = n + 1 by ring ] ; rcases n with ( _ | _ | n ) <;> norm_num [ Nat.add_one_mul_choose_eq ] at * ; ring;
  have := Nat.add_one_mul_choose_eq ( ( n + 1 + 1 ) * 2 ) ( n + 1 ) ; have := Nat.add_one_mul_choose_eq ( ( n + 1 + 1 ) * 2 ) ( n + 1 + 1 ) ; norm_num [ Nat.choose_succ_succ, mul_assoc ] at * ; nlinarith;

/-
PROBLEM
D + 2s = (n+2)*D from bracket_eq

PROVIDED SOLUTION
From bracket_eq: (n+1)*D = 2s where D = 2s - s1 - s2 and s = scalar_AB n n. So D + 2s = D + (n+1)*D = (n+2)*D. Use nlinarith with bracket_eq.
-/
lemma D_plus_2s (n : ℕ) (hn : 1 ≤ n) :
    (2 * scalar_AB n n - scalar_A2 n (n + 1) - scalar_B2 n (n - 1)) + 2 * scalar_AB n n
      = (n + 2) * (2 * scalar_AB n n - scalar_A2 n (n + 1) - scalar_B2 n (n - 1)) := by
  -- Substitute D from bracket_eq into the equation.
  have h_sub_D : 2 * scalar_AB n n - scalar_A2 n (n + 1) - scalar_B2 n (n - 1) = 2 * scalar_AB n n / (n + 1) := by
    rw [ Nat.div_eq_of_eq_mul_left ] <;> try linarith;
    convert bracket_eq n hn |> Eq.symm using 1 ; ring;
  rw [ h_sub_D ];
  -- Since $(n + 1)$ divides $2 * scalar_AB n n$, we can apply the division algorithm.
  have h_div : (n + 1) ∣ 2 * scalar_AB n n := by
    have h_div : (n + 1) ∣ 2 * scalar_AB n n := by
      have := bracket_eq n hn
      exact Dvd.intro _ this;
    assumption;
  linarith [ Nat.div_mul_cancel h_div ]

/-
PROBLEM
p^e divides D

PROVIDED SOLUTION
From bracket_eq: (n+1)*D = 2*s where D = 2s - s1 - s2, s = scalar_AB n n. So D = 2s/(n+1). Now p^e | s (by e_central_eq and padicValNat definition). So p^e | 2s. And p^e | (n+1)*D. Since p ∤ (n+1) [because n+1 = p^k - 1 ≡ -1 mod p, and -1 ≢ 0 mod p for p ≥ 2], we can conclude p^e | D.

To show p ∤ (n+1): n+2 = p^k, so n+1 = p^k - 1. If p | (n+1) then p | (p^k - 1). But p | p^k, so p | 1, contradiction since p ≥ 2.

For the divisibility: from (n+1)*D = 2s and p^e | 2s (since p^e | s and p ∤ 2 since p is odd), and gcd(p^e, n+1) = 1 (since p ∤ (n+1)), by Nat.Coprime.dvd_of_dvd_mul_right we get p^e | D.
-/
lemma p_e_dvd_D (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (hp_odd : p ≠ 2) :
    p ^ e_central p n ∣ (2 * scalar_AB n n - scalar_A2 n (n + 1) - scalar_B2 n (n - 1)) := by
  -- By definition of $e_central$, we know that $p^e \mid \text{scalar\_AB}_n n$.
  have h_div : p ^ (e_central p n) ∣ scalar_AB n n := by
    rw [ e_central_eq ];
    exact?;
  -- By Lemma~\ref{lem:bracket_eq}, $(n+1)*D = 2s$.
  have h_bracket : (n + 1) * (2 * scalar_AB n n - scalar_A2 n (n + 1) - scalar_B2 n (n - 1)) = 2 * scalar_AB n n := by
    exact?;
  -- Since $p \nmid (n+1)$, we can conclude that $p^e \mid D$.
  have h_not_div : ¬(p ∣ (n + 1)) := by
    rw [ ← Nat.modEq_zero_iff_dvd ] ; haveI := Fact.mk ( Fact.out : Nat.Prime p ) ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
    rw [ show ( n : ZMod p ) = -2 by { exact eq_neg_of_add_eq_zero_left <| by rw [ ← eq_comm ] ; replace hn := congr_arg ( ( ↑ ) : ℕ → ZMod p ) hn ; norm_num at * ; cases k <;> simp_all +decide [ pow_succ' ] } ] ; ring_nf ; aesop;
  refine' Nat.Coprime.dvd_of_dvd_mul_left _ ( h_bracket.symm ▸ dvd_mul_of_dvd_right h_div _ );
  exact Nat.Coprime.pow_left _ ( Nat.Prime.coprime_iff_not_dvd Fact.out |>.2 h_not_div )

-- ============================================================
-- Sum analysis: combining the three congruences
-- ============================================================

/-- The sum analysis: modulo p, A' ≡ μ·c_n², B' ≡ -2μ·c_n·c_{n+1},
C' ≡ μ·c_{n+1}² for some μ. -/
lemma sum_approx_square (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (c : ℕ → ℤ)
    (A' B' C' : ℤ)
    (hA : A_eval n c = (p : ℤ) ^ e_central p n * A')
    (hB : B_eval n c = (p : ℤ) ^ e_central p n * B')
    (hC : C_eval n c = (p : ℤ) ^ e_central p n * C') :
    ∃ μ : ℤ, ((p : ℤ) ∣ A' - μ * (c n) ^ 2) ∧
              ((p : ℤ) ∣ B' + 2 * μ * (c n) * (c (n + 1))) ∧
              ((p : ℤ) ∣ C' - μ * (c (n + 1)) ^ 2) := by
  refine ⟨(-1 : ℤ) ^ n * ↑(scalar_AB n n / p ^ e_central p n),
    A_eval_cong p k hk n hn hn_pos c A' hA,
    ?_, C_eval_cong p k hk n hn hn_pos c C' hC⟩
  convert B_eval_cong p k hk hp_odd n hn hn_pos c B' hB using 1; try ring

-- ============================================================
-- Main theorem
-- ============================================================

/--
The rank-1 cancellation: if A_eval = p^e · A', B_eval = p^e · B',
C_eval = p^e · C', then p | B'² - 4A'C'.
-/
theorem reduced_disc_dvd_p (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (c : ℕ → ℤ)
    (A' B' C' : ℤ)
    (hA : A_eval n c = (p : ℤ) ^ e_central p n * A')
    (hB : B_eval n c = (p : ℤ) ^ e_central p n * B')
    (hC : C_eval n c = (p : ℤ) ^ e_central p n * C') :
    (p : ℤ) ∣ B' ^ 2 - 4 * A' * C' := by
  obtain ⟨μ, hAμ, hBμ, hCμ⟩ := sum_approx_square p k hk hp_odd n hn hn_pos c A' B' C' hA hB hC
  have hBμ' : (p : ℤ) ∣ B' - 2 * μ * c n * (-(c (n + 1))) := by ring_nf; ring_nf at hBμ; exact hBμ
  have hCμ' : (p : ℤ) ∣ C' - μ * (-(c (n + 1))) ^ 2 := by ring_nf; ring_nf at hCμ; exact hCμ
  exact disc_of_approx_square (p : ℤ) A' B' C' μ (c n) (-(c (n + 1))) hAμ hBμ' hCμ'


private lemma disc_dvd_step_asm (p : ℤ) (e : ℕ) (A' B' C' : ℤ)
    (hdisc : p ∣ B' ^ 2 - 4 * A' * C') :
    p ^ (2 * e + 1) ∣ (p ^ e * B') ^ 2 - 4 * (p ^ e * A') * (p ^ e * C') := by
  obtain ⟨k, hk⟩ := hdisc
  exact ⟨k, by rw [pow_add, pow_mul']; linear_combination hk * p ^ (2 * e)⟩

theorem rank1_collapse (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n)
    (c : ℕ → ℤ) :
    (p : ℤ) ^ (2 * e_central p n + 1) ∣ Δ_eval n c := by
  obtain ⟨A', hA⟩ := A_eval_dvd_pe p k hk hp_odd n hn hn_pos c
  obtain ⟨B', hB⟩ := B_eval_dvd_pe p k hk hp_odd n hn hn_pos c
  obtain ⟨C', hC⟩ := C_eval_dvd_pe p k hk hp_odd n hn hn_pos c
  have hmod := reduced_disc_dvd_p p k hk hp_odd n hn hn_pos c A' B' C' hA hB hC
  unfold Δ_eval; rw [hA, hB, hC]
  exact disc_dvd_step_asm (p : ℤ) (e_central p n) A' B' C' hmod

end QuarticInvariant
