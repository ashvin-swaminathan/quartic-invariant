import Mathlib
import Modular.Defs
import Modular.ContentBasics
import Modular.PairSpec
import Modular.ScalarBounds
import Modular.CentralDom
import Modular.DeformAssembly
import Modular.CoeffDivPP
import Modular.MainP5
import Modular.P3Witness

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant

/-! ## Infrastructure: divide every coefficient by a scalar -/

private def p3_mvDivScalar (f : MvPolynomial ℕ ℤ) (d : ℤ) : MvPolynomial ℕ ℤ :=
  Finsupp.mapRange (· / d) (by simp) f

@[simp]
private lemma p3_mvDivScalar_coeff (f : MvPolynomial ℕ ℤ) (d : ℤ) (m : ℕ →₀ ℕ) :
    (p3_mvDivScalar f d).coeff m = f.coeff m / d :=
  Finsupp.mapRange_apply (hf := by simp)

private lemma p3_smul_mvDivScalar (f : MvPolynomial ℕ ℤ) (d : ℤ)
    (hdvd : ∀ m, d ∣ f.coeff m) :
    MvPolynomial.C d * p3_mvDivScalar f d = f := by
  ext m
  simp only [MvPolynomial.coeff_C_mul, p3_mvDivScalar_coeff]
  exact Int.mul_ediv_cancel' (hdvd m)

/-! ## Rank-1 coefficient divisibility -/

private lemma p3_mvpoly_eq_of_coeff_congr (p : ℕ) [hp : Fact p.Prime]
    (f g : MvPolynomial ℕ ℤ)
    (h : ∀ m, (p : ℤ) ∣ (f.coeff m - g.coeff m)) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) f =
    MvPolynomial.map (Int.castRingHom (ZMod p)) g := by
  ext m
  simp only [MvPolynomial.coeff_map]
  rw [← sub_eq_zero, ← map_sub]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (h m)

private theorem p3_rank1_coeff_dvd (p : ℕ) [hp : Fact p.Prime]
    (A B C a b c : MvPolynomial ℕ ℤ)
    (hA : ∀ m, (p : ℤ) ∣ (A.coeff m - a.coeff m))
    (hB : ∀ m, (p : ℤ) ∣ (B.coeff m - b.coeff m))
    (hC : ∀ m, (p : ℤ) ∣ (C.coeff m - c.coeff m))
    (hdisc : b ^ 2 = 4 * a * c)
    (m : ℕ →₀ ℕ) :
    (p : ℤ) ∣ (B ^ 2 - 4 * A * C).coeff m := by
  let phi := Int.castRingHom (ZMod p)
  have hAbar := p3_mvpoly_eq_of_coeff_congr p A a hA
  have hBbar := p3_mvpoly_eq_of_coeff_congr p B b hB
  have hCbar := p3_mvpoly_eq_of_coeff_congr p C c hC
  have key : MvPolynomial.map phi (B ^ 2 - 4 * A * C) = 0 := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [hAbar, hBbar, hCbar]
    rw [show MvPolynomial.map phi b ^ 2 = 4 * MvPolynomial.map phi a * MvPolynomial.map phi c from by
      have := congr_arg (MvPolynomial.map phi) hdisc
      simp only [map_mul, map_pow, map_ofNat] at this; exact this]
    rw [sub_self]
  have := congr_arg (MvPolynomial.coeff m) key
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this

/-! ## Disc coeff upgrade -/

private theorem p3_disc_coeff_upgrade (p : ℕ) [hp : Fact p.Prime] (e : ℕ)
    (A B C : MvPolynomial ℕ ℤ)
    (hA : ∀ m, ((p ^ e : ℕ) : ℤ) ∣ A.coeff m)
    (hB : ∀ m, ((p ^ e : ℕ) : ℤ) ∣ B.coeff m)
    (hC : ∀ m, ((p ^ e : ℕ) : ℤ) ∣ C.coeff m)
    (a b c : MvPolynomial ℕ ℤ)
    (hAa : ∀ m, (p : ℤ) ∣ (A.coeff m / ((p ^ e : ℕ) : ℤ) - a.coeff m))
    (hBb : ∀ m, (p : ℤ) ∣ (B.coeff m / ((p ^ e : ℕ) : ℤ) - b.coeff m))
    (hCc : ∀ m, (p : ℤ) ∣ (C.coeff m / ((p ^ e : ℕ) : ℤ) - c.coeff m))
    (hdisc : b ^ 2 = 4 * a * c)
    (m : ℕ →₀ ℕ) :
    ((p ^ (2 * e + 1) : ℕ) : ℤ) ∣ (B ^ 2 - 4 * A * C).coeff m := by
  set d : ℤ := ((p ^ e : ℕ) : ℤ)
  set A' := p3_mvDivScalar A d
  set B' := p3_mvDivScalar B d
  set C' := p3_mvDivScalar C d
  have hA_eq : A = MvPolynomial.C d * A' := (p3_smul_mvDivScalar A d hA).symm
  have hB_eq : B = MvPolynomial.C d * B' := (p3_smul_mvDivScalar B d hB).symm
  have hC_eq : C = MvPolynomial.C d * C' := (p3_smul_mvDivScalar C d hC).symm
  have disc_factor : B ^ 2 - 4 * A * C =
      MvPolynomial.C (d ^ 2) * (B' ^ 2 - 4 * A' * C') := by
    conv_lhs => rw [hA_eq, hB_eq, hC_eq]
    simp only [map_pow]; ring
  have hA'a : ∀ m, (p : ℤ) ∣ (A'.coeff m - a.coeff m) := by
    intro m'; simp only [A', p3_mvDivScalar_coeff]; exact hAa m'
  have hB'b : ∀ m, (p : ℤ) ∣ (B'.coeff m - b.coeff m) := by
    intro m'; simp only [B', p3_mvDivScalar_coeff]; exact hBb m'
  have hC'c : ∀ m, (p : ℤ) ∣ (C'.coeff m - c.coeff m) := by
    intro m'; simp only [C', p3_mvDivScalar_coeff]; exact hCc m'
  have h_rank1 : (p : ℤ) ∣ (B' ^ 2 - 4 * A' * C').coeff m :=
    p3_rank1_coeff_dvd p A' B' C' a b c hA'a hB'b hC'c hdisc m
  rw [disc_factor, MvPolynomial.coeff_C_mul]
  rw [show ((p ^ (2 * e + 1) : ℕ) : ℤ) = d ^ 2 * (p : ℤ) from by
    simp only [d]; push_cast [Nat.cast_pow]; ring]
  exact mul_dvd_mul_left _ h_rank1

/-! ## Nullstellensatz helper for p = 3 -/

private lemma p3_MvPolynomial_ZMod_vanish (p : ℕ) [hp : Fact p.Prime]
    (f : MvPolynomial ℕ (ZMod p))
    (hdeg : ∀ i, f.degreeOf i < p)
    (heval : ∀ c : ℕ → ZMod p, MvPolynomial.eval c f = 0) :
    f = 0 := by
  obtain ⟨k, g, hg_inj, q, hfq⟩ := MvPolynomial.exists_fin_rename f
  suffices hq : q = 0 by rw [hfq, hq, map_zero]
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset q (fun _ => Finset.univ)
  · intro i
    simp only [Finset.card_univ, ZMod.card]
    rw [← MvPolynomial.degreeOf_rename_of_injective hg_inj i, ← hfq]
    exact hdeg (g i)
  · intro x _
    let c : ℕ → ZMod p := fun j =>
      if h : ∃ i, g i = j then x (h.choose) else 0
    have hcg : c ∘ g = x := by
      ext i; simp only [Function.comp_apply, c]
      have : ∃ i', g i' = g i := ⟨i, rfl⟩
      rw [dif_pos this]; congr 1; exact hg_inj this.choose_spec
    have : MvPolynomial.eval x q = MvPolynomial.eval c f := by
      rw [hfq, MvPolynomial.eval_rename, hcg]
    rw [this]; exact heval c

private lemma p3_coeff_dvd_of_eval_dvd (p : ℕ) [hp : Fact p.Prime]
    (f : MvPolynomial ℕ ℤ)
    (hdeg : ∀ i, f.degreeOf i < p)
    (heval : ∀ c : ℕ → ℤ, (p : ℤ) ∣ MvPolynomial.eval c f) :
    ∀ m, (p : ℤ) ∣ f.coeff m := by
  suffices h : MvPolynomial.map (Int.castRingHom (ZMod p)) f = 0 by
    intro m
    have := congr_arg (MvPolynomial.coeff m) h
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, Int.coe_castRingHom] at this
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  apply p3_MvPolynomial_ZMod_vanish p
  · intro i
    calc (MvPolynomial.map (Int.castRingHom (ZMod p)) f).degreeOf i
        ≤ f.degreeOf i := by
          simp only [MvPolynomial.degreeOf_eq_sup]
          exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
      _ < p := hdeg i
  · intro c
    haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
    set c' : ℕ → ℤ := fun i => (ZMod.val (c i) : ℤ) with hc'_def
    have hcc' : c = (Int.castRingHom (ZMod p)) ∘ c' := by
      ext i; simp only [Function.comp_apply, hc'_def, Int.coe_castRingHom,
        Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [MvPolynomial.eval_map, hcc', ← MvPolynomial.eval₂_comp, Int.coe_castRingHom]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (heval c')

/-! ## Rank-1 witnesses and congruences for A_n, B_n, C_n -/

/-- The rank-1 witness for A_n/p^e: the central term μ * X_n². -/
private def r1_a (n : ℕ) (μ : ℤ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.C μ * MvPolynomial.X n * MvPolynomial.X n

/-- The rank-1 witness for C_n/p^e: the central term μ * X_{n+1}². -/
private def r1_c (n : ℕ) (μ : ℤ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.C μ * MvPolynomial.X (n + 1) * MvPolynomial.X (n + 1)

/-- The rank-1 witness for B_n/p^e: the central term -2μ * X_n * X_{n+1}. -/
private def r1_b (n : ℕ) (μ : ℤ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.C (-2 * μ) * MvPolynomial.X n * MvPolynomial.X (n + 1)

private lemma r1_disc (n : ℕ) (μ : ℤ) :
    (r1_b n μ) ^ 2 = 4 * (r1_a n μ) * (r1_c n μ) := by
  simp only [r1_a, r1_b, r1_c]
  simp only [map_neg, map_mul, map_ofNat]
  ring

/-- Central dominance gives the coefficient congruences.
    For A_n: all non-central scalars scalar_AB(n,i) for i ≠ n have v_p > e,
    so dividing by p^e and subtracting the rank-1 witness still leaves a
    result divisible by p. -/
private lemma A_n_coeff_cong (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (μ : ℤ)
    (hμ : μ = (-1 : ℤ) ^ n * ↑(scalar_AB n n / p ^ e_central p n)) :
    ∀ m, (p : ℤ) ∣ ((A_n n).coeff m / ((p ^ e_central p n : ℕ) : ℤ) - (r1_a n μ).coeff m) := by
  set e := e_central p n
  set d := ((p ^ e : ℕ) : ℤ)
  intro m
  have hd_ne : d ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))
  have hd_dvd : d ∣ (A_n n).coeff m := coeff_A_n_dvd_odd p k hk hp_odd n hn hn_pos m
  suffices h : d * (p : ℤ) ∣ ((A_n n).coeff m - d * (r1_a n μ).coeff m) by
    obtain ⟨q, hq⟩ := hd_dvd
    have hq' : (A_n n).coeff m / d = q := by rw [hq, Int.mul_ediv_cancel_left _ hd_ne]
    rw [hq']
    rw [hq, show d * q - d * (r1_a n μ).coeff m = d * (q - (r1_a n μ).coeff m) from by ring] at h
    exact (mul_dvd_mul_iff_left hd_ne).mp h
  -- A_n = Σ_i s_i · X_i · X_{2n-i}, with s_i = (-1)^i · scalar_AB(n,i)
  -- We need d * p | (A_n.coeff m - d * r1_a.coeff m)
  -- Step 1: n ∈ range(2n+1)
  have hn_mem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  -- Step 2: The central scalar satisfies d * μ = (-1)^n * scalar_AB(n,n)
  have h_dmu : d * μ = (-1 : ℤ) ^ n * (scalar_AB n n : ℤ) := by
    rw [hμ]
    have h_dvd_nat : p ^ e ∣ scalar_AB n n := p_pow_dvd_scalar_AB p n
    have h_factor : (scalar_AB n n : ℤ) = d * ↑(scalar_AB n n / p ^ e) := by
      rw [show d = ((p ^ e : ℕ) : ℤ) from rfl]
      push_cast
      exact_mod_cast (Nat.mul_div_cancel' h_dvd_nat).symm
    rw [h_factor]; ring
  -- Step 3: The i=n summand of A_n equals d * r1_a as polynomials
  have h_central_term :
      MvPolynomial.C ((-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
        (α n n : ℤ) * (β n n : ℤ)) *
      MvPolynomial.X n * MvPolynomial.X (2 * n - n) =
      MvPolynomial.C d * (r1_a n μ) := by
    simp only [r1_a, show 2 * n - n = n from by omega]
    rw [show MvPolynomial.C d * (MvPolynomial.C μ * MvPolynomial.X n * MvPolynomial.X n) =
      MvPolynomial.C (d * μ) * MvPolynomial.X n * MvPolynomial.X n from by
      rw [map_mul]; ring]
    congr 1; congr 1
    rw [h_dmu]
    push_cast [scalar_AB, α, β]; ring
  -- Step 4: A_n.coeff m = central_term.coeff m + Σ_{i≠n} term_i.coeff m
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
  -- Step 5: central term coeff = d * r1_a.coeff m
  have h_central_coeff : (term n).coeff m = d * (r1_a n μ).coeff m := by
    show (MvPolynomial.C ((-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
        (α n n : ℤ) * (β n n : ℤ)) *
      MvPolynomial.X n * MvPolynomial.X (2 * n - n)).coeff m = d * (r1_a n μ).coeff m
    rw [h_central_term, MvPolynomial.coeff_C_mul]
  -- Step 6: difference = Σ_{i≠n} term_i.coeff m
  have h_diff : (A_n n).coeff m - d * (r1_a n μ).coeff m =
      ∑ i ∈ (Finset.range (2 * n + 1)).erase n, (term i).coeff m := by
    rw [h_A_split, h_central_coeff]; ring
  -- Step 7: Each i≠n summand has d * p | its coefficient
  rw [h_diff]
  apply Finset.dvd_sum
  intro i hi
  have hi_range := (Finset.mem_erase.mp hi).2
  have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
  have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_range)
  -- v_p(scalar_AB(n,i)) > e, so p^{e+1} | scalar_AB(n,i)
  have h_vp : padicValNat p (scalar_AB n i) > e := by
    rw [show e = padicValNat p (scalar_AB n n) from e_central_eq p n]
    exact scalar_AB_central_min p k hk n hn i hi_le hi_ne
  have h_dvd_scalar : (p ^ (e + 1) : ℕ) ∣ scalar_AB n i :=
    dvd_trans (pow_dvd_pow p h_vp) pow_padicValNat_dvd
  have h_dvd_signed : d * (p : ℤ) ∣ ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ)) := by
    have : d * (p : ℤ) = ((p ^ (e + 1) : ℕ) : ℤ) := by
      simp only [d]; push_cast; ring
    rw [this]
    have h_int : ((p ^ (e + 1) : ℕ) : ℤ) ∣ (scalar_AB n i : ℤ) :=
      Int.natCast_dvd_natCast.mpr h_dvd_scalar
    convert h_int.mul_left ((-1 : ℤ) ^ i) using 1
    simp [scalar_AB]; push_cast; ring
  -- Extract the coefficient of term i
  show d * (p : ℤ) ∣ (term i).coeff m
  simp only [hterm_def]
  rw [MvPolynomial.coeff_mul]
  apply Finset.dvd_sum
  intro x _
  erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_left h_dvd_signed _

private lemma C_n_coeff_cong (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (μ : ℤ)
    (hμ : μ = (-1 : ℤ) ^ n * ↑(scalar_AB n n / p ^ e_central p n)) :
    ∀ m, (p : ℤ) ∣ ((C_n n).coeff m / ((p ^ e_central p n : ℕ) : ℤ) - (r1_c n μ).coeff m) := by
  set e := e_central p n
  set d := ((p ^ e : ℕ) : ℤ)
  intro m
  have hd_ne : d ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))
  have hd_dvd : d ∣ (C_n n).coeff m := coeff_C_n_dvd_odd p k hk hp_odd n hn hn_pos m
  suffices h : d * (p : ℤ) ∣ ((C_n n).coeff m - d * (r1_c n μ).coeff m) by
    obtain ⟨q, hq⟩ := hd_dvd
    have hq' : (C_n n).coeff m / d = q := by rw [hq, Int.mul_ediv_cancel_left _ hd_ne]
    rw [hq']
    rw [hq, show d * q - d * (r1_c n μ).coeff m = d * (q - (r1_c n μ).coeff m) from by ring] at h
    exact (mul_dvd_mul_iff_left hd_ne).mp h
  have hn_mem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  have h_dmu : d * μ = (-1 : ℤ) ^ n * (scalar_AB n n : ℤ) := by
    rw [hμ]
    have h_dvd_nat : p ^ e ∣ scalar_AB n n := p_pow_dvd_scalar_AB p n
    have h_factor : (scalar_AB n n : ℤ) = d * ↑(scalar_AB n n / p ^ e) := by
      rw [show d = ((p ^ e : ℕ) : ℤ) from rfl]
      push_cast
      exact_mod_cast (Nat.mul_div_cancel' h_dvd_nat).symm
    rw [h_factor]; ring
  have h_central_term :
      MvPolynomial.C ((-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
        (α n n : ℤ) * (β n n : ℤ)) *
      MvPolynomial.X (n + 1) * MvPolynomial.X (2 * n + 1 - n) =
      MvPolynomial.C d * (r1_c n μ) := by
    simp only [r1_c, show 2 * n + 1 - n = n + 1 from by omega]
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
  have h_central_coeff : (cterm n).coeff m = d * (r1_c n μ).coeff m := by
    show (MvPolynomial.C ((-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
        (α n n : ℤ) * (β n n : ℤ)) *
      MvPolynomial.X (n + 1) * MvPolynomial.X (2 * n + 1 - n)).coeff m = d * (r1_c n μ).coeff m
    rw [h_central_term, MvPolynomial.coeff_C_mul]
  have h_diff : (C_n n).coeff m - d * (r1_c n μ).coeff m =
      ∑ i ∈ (Finset.range (2 * n + 1)).erase n, (cterm i).coeff m := by
    rw [h_C_split, h_central_coeff]; ring
  rw [h_diff]
  apply Finset.dvd_sum
  intro i hi
  have hi_range := (Finset.mem_erase.mp hi).2
  have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
  have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_range)
  have h_vp : padicValNat p (scalar_AB n i) > e := by
    rw [show e = padicValNat p (scalar_AB n n) from e_central_eq p n]
    exact scalar_AB_central_min p k hk n hn i hi_le hi_ne
  have h_dvd_scalar : (p ^ (e + 1) : ℕ) ∣ scalar_AB n i :=
    dvd_trans (pow_dvd_pow p h_vp) pow_padicValNat_dvd
  have h_dvd_signed : d * (p : ℤ) ∣ ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ)) := by
    have : d * (p : ℤ) = ((p ^ (e + 1) : ℕ) : ℤ) := by simp only [d]; push_cast; ring
    rw [this]
    have h_int : ((p ^ (e + 1) : ℕ) : ℤ) ∣ (scalar_AB n i : ℤ) :=
      Int.natCast_dvd_natCast.mpr h_dvd_scalar
    convert h_int.mul_left ((-1 : ℤ) ^ i) using 1
    simp [scalar_AB]; push_cast; ring
  show d * (p : ℤ) ∣ (cterm i).coeff m
  simp only [hcterm_def]
  rw [MvPolynomial.coeff_mul]
  apply Finset.dvd_sum
  intro x _
  erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_left h_dvd_signed _

private lemma B_n_coeff_cong (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (μ : ℤ)
    (hμ : μ = (-1 : ℤ) ^ n * ↑(scalar_AB n n / p ^ e_central p n)) :
    ∀ m, (p : ℤ) ∣ ((B_n n).coeff m / ((p ^ e_central p n : ℕ) : ℤ) - (r1_b n μ).coeff m) := by
  set e := e_central p n
  set d := ((p ^ e : ℕ) : ℤ)
  have hd_ne : d ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))
  have hp_ge3 : 3 ≤ p := by
    have hp := (Fact.out : Nat.Prime p)
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact absurd h2 hp_odd
    · have := hp.two_le; omega
  -- Build the difference polynomial f = B_n/d - r1_b
  set f := p3_mvDivScalar (B_n n) d - r1_b n μ
  have hf_coeff : ∀ m, f.coeff m = (B_n n).coeff m / d - (r1_b n μ).coeff m := by
    intro m'; simp [f, MvPolynomial.coeff_sub, p3_mvDivScalar_coeff]
  intro m; rw [← hf_coeff]; clear hf_coeff
  -- Apply Nullstellensatz
  apply p3_coeff_dvd_of_eval_dvd p f
  · -- Degree bound: degreeOf(f, i) ≤ 2 < p
    intro i
    have h1 : (p3_mvDivScalar (B_n n) d).degreeOf i ≤ 2 := by
      calc (p3_mvDivScalar (B_n n) d).degreeOf i
          ≤ (B_n n).degreeOf i := by
            simp only [MvPolynomial.degreeOf_eq_sup, p3_mvDivScalar]
            exact Finset.sup_mono (Finsupp.support_mapRange (hf := by simp))
        _ ≤ 2 := degreeOf_B_n_le n i
    have h2 : (r1_b n μ).degreeOf i ≤ 2 := by
      simp only [r1_b]
      calc (MvPolynomial.C (-2 * μ) * MvPolynomial.X n * MvPolynomial.X (n + 1) :
              MvPolynomial ℕ ℤ).degreeOf i
          ≤ (MvPolynomial.C (-2 * μ) * MvPolynomial.X n : MvPolynomial ℕ ℤ).degreeOf i +
            (MvPolynomial.X (n + 1) : MvPolynomial ℕ ℤ).degreeOf i :=
            MvPolynomial.degreeOf_mul_le _ _ _
        _ ≤ ((MvPolynomial.C (-2 * μ) : MvPolynomial ℕ ℤ).degreeOf i +
            (MvPolynomial.X n : MvPolynomial ℕ ℤ).degreeOf i) +
            (MvPolynomial.X (n + 1) : MvPolynomial ℕ ℤ).degreeOf i :=
            Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) _
        _ ≤ (0 + 1) + 1 := by
            apply Nat.add_le_add
            · apply Nat.add_le_add
              · exact le_of_eq (MvPolynomial.degreeOf_C _ _)
              · simp only [MvPolynomial.degreeOf_X]; split <;> omega
            · simp only [MvPolynomial.degreeOf_X]; split <;> omega
        _ = 2 := by omega
    have h3 := MvPolynomial.degreeOf_sub_le i (p3_mvDivScalar (B_n n) d) (r1_b n μ)
    exact lt_of_le_of_lt (le_trans h3 (max_le h1 h2)) (by omega)
  · -- Eval divisibility: ∀ c, p | eval c f
    intro c
    simp only [f, map_sub]
    -- d | every coeff of B_n, so C(d) * mvDivScalar(B_n, d) = B_n
    have hB_dvd : ∀ m', d ∣ (B_n n).coeff m' :=
      coeff_B_n_dvd_prime_power p k hk hp_odd n hn hn_pos
    have hB_eq : MvPolynomial.C d * p3_mvDivScalar (B_n n) d = B_n n :=
      p3_smul_mvDivScalar (B_n n) d hB_dvd
    -- eval c (B_n n) = d * eval c (mvDivScalar)
    set B' := MvPolynomial.eval c (p3_mvDivScalar (B_n n) d)
    have hB_factor : MvPolynomial.eval c (B_n n) = d * B' := by
      have := congr_arg (MvPolynomial.eval c) hB_eq.symm
      simp only [map_mul, MvPolynomial.eval_C] at this; exact this
    -- Connect MvPolynomial.eval to B_eval
    have hB_eval_eq : MvPolynomial.eval c (B_n n) = B_eval n c := by
      unfold B_n B_eval
      simp [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_add, map_pow]
    -- So B_eval n c = d * B'
    have hB_eval : B_eval n c = d * B' := by rw [← hB_eval_eq]; exact hB_factor
    -- Apply B_eval_cong
    have hd_eq : (p : ℤ) ^ e = d := by simp [d]
    have h_cong := B_eval_cong p k hk hp_odd n hn hn_pos c B'
      (by rw [hd_eq]; exact hB_eval)
    -- eval c (r1_b) = -2μ * c(n) * c(n+1)
    have h_r1_eval : MvPolynomial.eval c (r1_b n μ) = -2 * μ * c n * c (n + 1) := by
      simp [r1_b, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    rw [h_r1_eval, hμ]
    convert h_cong using 1; ring

/-! ## Full coefficient divisibility of Δ_n for p=3 -/

private lemma coeff_Δ_n_dvd_p3 (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = 3 ^ k) (hn_pos : 1 ≤ n) :
    ∀ m ∈ (Δ_n n).support,
      3 ^ (2 * e_central 3 n + 1) ∣ Int.natAbs ((Δ_n n).coeff m) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp_odd : (3 : ℕ) ≠ 2 := by norm_num
  set e := e_central 3 n
  -- Step 1: 3^e | every coefficient of A_n, B_n, C_n
  have hA := coeff_A_n_dvd_odd 3 k hk hp_odd n hn hn_pos
  have hB := coeff_B_n_dvd_prime_power 3 k hk hp_odd n hn hn_pos
  have hC := coeff_C_n_dvd_odd 3 k hk hp_odd n hn hn_pos
  -- Rank-1 witnesses
  set μ : ℤ := (-1) ^ n * ↑(scalar_AB n n / 3 ^ e)
  have hμ : μ = (-1 : ℤ) ^ n * ↑(scalar_AB n n / 3 ^ e) := rfl
  -- Coefficient congruences
  have hAa := A_n_coeff_cong 3 k hk hp_odd n hn hn_pos μ hμ
  have hBb := B_n_coeff_cong 3 k hk hp_odd n hn hn_pos μ hμ
  have hCc := C_n_coeff_cong 3 k hk hp_odd n hn hn_pos μ hμ
  -- Apply disc_coeff_upgrade
  intro m hm
  have h_dvd_int : ((3 ^ (2 * e + 1) : ℕ) : ℤ) ∣ (Δ_n n).coeff m := by
    change ((3 ^ (2 * e + 1) : ℕ) : ℤ) ∣ ((B_n n) ^ 2 - 4 * (A_n n) * (C_n n)).coeff m
    exact p3_disc_coeff_upgrade 3 e (A_n n) (B_n n) (C_n n)
      hA hB hC (r1_a n μ) (r1_b n μ) (r1_c n μ)
      hAa hBb hCc (r1_disc n μ) m
  exact Int.natCast_dvd.mp h_dvd_int

/-! ## Backward direction: prime power → odd -/

private lemma natAbs_dvd_int_pow' {p : ℕ} {e : ℕ} {a : ℤ}
    (h : p ^ e ∣ a.natAbs) : (p : ℤ) ^ e ∣ a :=
  Int.natAbs_dvd_natAbs.mp (by simpa [Int.natAbs_pow, Int.natAbs_natCast] using h)

private theorem odd_of_prime_power_p3 (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) (hpow : n + 2 = 3 ^ k) :
    Odd (padicValNat 3 (S n)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp_odd : (3 : ℕ) ≠ 2 := by norm_num
  have hn_pos : 1 ≤ n := by omega
  -- Since n ≥ 2, n+2 ≥ 4 > 3 = 3^1, so k ≥ 2, making hp5_if_k1 vacuous.
  have hk2 : 2 ≤ k := by
    by_contra h; push_neg at h
    interval_cases k <;> omega
  have hp5_if_k1 : k = 1 → 5 ≤ 3 := by omega
  -- Get deformation witness
  obtain ⟨c, hc_ne, hc_val⟩ := deformation_valuation_exists 3 hp_odd k hk hp5_if_k1 n hpow hn_pos
  -- Translate to MvPolynomial evaluation
  have hc_ne' : MvPolynomial.eval c (Δ_n n) ≠ 0 := by
    rw [eval_Δ_eq_Δ_eval]; exact hc_ne
  have hc_val' : padicValNat 3 (Int.natAbs (MvPolynomial.eval c (Δ_n n))) =
      2 * e_central 3 n + 1 := by
    rw [eval_Δ_eq_Δ_eval]; exact hc_val
  -- S is nonzero
  have hS : S n ≠ 0 := S_ne_zero_of_eval_ne_zero n c hc_ne'
  -- Upper bound: v_3(S) ≤ 2e+1
  have h_upper : padicValNat 3 (S n) ≤ 2 * e_central 3 n + 1 :=
    hc_val' ▸ vp_S_le_eval 3 n c hc_ne'
  -- Lower bound: v_3(S) ≥ 2e+1 from coefficient divisibility
  have h_lower : 2 * e_central 3 n + 1 ≤ padicValNat 3 (S n) :=
    vp_S_ge_of_coeff_dvd 3 n (2 * e_central 3 n + 1) hS
      (coeff_Δ_n_dvd_p3 k hk n hpow hn_pos)
  exact ⟨e_central 3 n, by omega⟩

/-! ## Forward direction: non-prime-power → even (for p=3) -/

/-- For p = 3 (odd prime, p ∤ 2): scalar_AB_dvd_of_vp_b_min.
    This is a copy of the p ≥ 5 version from MainP5.lean,
    but only needing p ≠ 2 (which holds for p = 3). -/
private lemma scalar_AB_dvd_of_vp_b_min_p3 (n : ℕ) (hn : 0 < n)
    (e : ℕ) (he : ∀ k ∈ Finset.Icc 1 (2 * n), e ≤ padicValNat 3 (Int.natAbs (b_formula n k))) :
    ∀ i, i ≤ 2 * n → (3 ^ e) ∣ scalar_AB n i := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- The proof is identical to scalar_AB_dvd_of_vp_b_min in MainP5.lean
  -- with p = 3, using only p ≠ 2 (not p ≥ 5).
  have hp_not_dvd_2 : ¬(3 ∣ 2) := by omega
  have hcop2 : Nat.Coprime (3 ^ e) 2 :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hp_not_dvd_2)
  have he_dvd : ∀ k, k ∈ Finset.Icc 1 (2 * n) →
      3 ^ e ∣ Int.natAbs (b_formula n k) := by
    intro k hk
    have hk_ne : Int.natAbs (b_formula n k) ≠ 0 := by
      rw [Int.natAbs_ne_zero, b_formula_eq_b_k_val]
      exact b_k_val_ne_zero n k (by omega) (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    exact (padicValNat_dvd_iff_le hk_ne).mpr (he k hk)
  -- Extract p^e from b_formula, removing coprime factors
  have factor_out (k : ℕ) (hk_lo : 1 ≤ k) (hk_hi : k ≤ 2 * n)
      (hcop : ¬(3 ∣ Int.natAbs ((2 * n : ℤ) + 1 - 2 * k))) :
      3 ^ e ∣ (2 * n).factorial * (2 * n + 1 - k).factorial * k.factorial := by
    have hk_mem : k ∈ Finset.Icc 1 (2 * n) := Finset.mem_Icc.mpr ⟨hk_lo, hk_hi⟩
    have h_dvd := he_dvd k hk_mem
    have h_eq := b_formula_factored n k hk_hi
    have h_natabs : Int.natAbs (b_formula n k) =
        2 * (2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * k) *
        (2 * n + 1 - k).factorial * k.factorial := by
      rw [h_eq]
      rw [show 2 * (-1 : ℤ) ^ k *
          (((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ)) =
          (2 * (-1 : ℤ) ^ k) *
          (((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ)) from by ring]
      rw [Int.natAbs_mul]
      have h_unit : Int.natAbs (2 * (-1 : ℤ) ^ k) = 2 := by
        rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;> simp
      rw [h_unit]
      rw [show ((2 * n).factorial : ℤ) * ((2 * n : ℤ) + 1 - 2 * ↑k) *
          ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ) =
          ((2 * n).factorial : ℤ) * ((2 * n + 1 - k).factorial : ℤ) * (k.factorial : ℤ) *
          ((2 * n : ℤ) + 1 - 2 * ↑k) from by ring]
      rw [Int.natAbs_mul]
      rw [show Int.natAbs (((2 * n).factorial : ℤ) * ((2 * n + 1 - k).factorial : ℤ) *
          (k.factorial : ℤ)) = (2 * n).factorial * (2 * n + 1 - k).factorial * k.factorial from by
        simp [Int.natAbs_mul, Int.natAbs_natCast]]
      ring
    rw [h_natabs] at h_dvd
    have h_no2 : 3 ^ e ∣ (2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * k) *
        (2 * n + 1 - k).factorial * k.factorial := by
      have h_rearr2 : 2 * (2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * ↑k) *
          (2 * n + 1 - k).factorial * k.factorial =
          2 * ((2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * ↑k) *
          (2 * n + 1 - k).factorial * k.factorial) := by ring
      rw [h_rearr2] at h_dvd
      exact hcop2.dvd_of_dvd_mul_left h_dvd
    have hcop_abs : Nat.Coprime (3 ^ e) (Int.natAbs ((2 * n : ℤ) + 1 - 2 * k)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hcop)
    have h_rearr : (2 * n).factorial * Int.natAbs ((2 * n : ℤ) + 1 - 2 * ↑k) *
        (2 * n + 1 - k).factorial * k.factorial =
        Int.natAbs ((2 * n : ℤ) + 1 - 2 * ↑k) *
        ((2 * n).factorial * (2 * n + 1 - k).factorial * k.factorial) := by ring
    rw [h_rearr] at h_no2
    exact hcop_abs.dvd_of_dvd_mul_left h_no2
  intro i hi
  -- Boundary cases
  have boundary_case (i : ℕ) (hi_le : i ≤ 2 * n) (hi_bdy : i = 0 ∨ i = 2 * n) :
      3 ^ e ∣ scalar_AB n i := by
    have h_not_dvd_one : ¬(3 ∣ Int.natAbs ((2 * n : ℤ) + 1 - 2 * n)) := by
      have : (2 * n : ℤ) + 1 - 2 * n = 1 := by omega
      rw [this]; simp [Int.natAbs_one]
    have h_factor := factor_out n hn (by omega) h_not_dvd_one
    rw [show 2 * n + 1 - n = n + 1 from by omega] at h_factor
    have h_scalar_bdy : scalar_AB n i = (2 * n).factorial * (2 * n + 1).factorial := by
      rw [scalar_AB_formula n i hi_le]
      rcases hi_bdy with rfl | rfl
      · simp only [Nat.sub_zero, Nat.zero_add, Nat.factorial_one]; ring
      · rw [show 2 * n + 1 - 2 * n = 1 from by omega]
        simp only [Nat.factorial_one]; ring
    have h_choose_fact : Nat.choose (2 * n + 1) (n + 1) * (n + 1).factorial * n.factorial =
        (2 * n + 1).factorial := by
      have h := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 2 * n + 1 from by omega)
      rw [show 2 * n + 1 - (n + 1) = n from by omega] at h; linarith
    have h_rearrange : (2 * n).factorial * (2 * n + 1).factorial =
        Nat.choose (2 * n + 1) (n + 1) * ((2 * n).factorial * (n + 1).factorial * n.factorial) := by
      nlinarith [h_choose_fact]
    rw [h_scalar_bdy, h_rearrange]
    exact dvd_mul_of_dvd_right h_factor _
  by_cases hi0 : i = 0
  · exact boundary_case i (by omega) (Or.inl hi0)
  · by_cases hi2n : i = 2 * n
    · exact boundary_case i hi (Or.inr hi2n)
    · have hi_pos : 1 ≤ i := by omega
      have h_scalar := scalar_AB_formula n i hi
      by_cases hdvd : 3 ∣ Int.natAbs ((2 * n : ℤ) + 1 - 2 * i)
      · -- 3 | (2n+1-2i), so 3 ∤ (2n-1-2i) since difference is 2 and 3 ∤ 2
        have hcop_other : ¬(3 ∣ Int.natAbs ((2 * n : ℤ) - 1 - 2 * i)) := by
          intro h_other
          have h1 : (3 : ℤ) ∣ ((2 * n : ℤ) + 1 - 2 * i) :=
            Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdvd)
          have h2 : (3 : ℤ) ∣ ((2 * n : ℤ) - 1 - 2 * i) :=
            Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h_other)
          have h3 : (3 : ℤ) ∣ 2 := by
            have := Int.dvd_sub h1 h2
            rwa [show (2 * n + 1 - 2 * i : ℤ) - (2 * n - 1 - 2 * i : ℤ) = 2 from by omega] at this
          exact hp_not_dvd_2 (by exact_mod_cast h3)
        have h_eq_idx : (2 * n : ℤ) + 1 - 2 * (↑(i + 1)) = (2 * n : ℤ) - 1 - 2 * i := by
          push_cast; ring
        have h_factor := factor_out (i + 1) (by omega) (by omega) (by rwa [h_eq_idx])
        rw [h_scalar]
        have h_fact_split : (2 * n + 1 - i).factorial = (2 * n + 1 - i) * (2 * n - i).factorial := by
          rw [show 2 * n + 1 - i = (2 * n - i) + 1 from by omega]
          exact Nat.factorial_succ (2 * n - i)
        have h_rearrange : (2 * n).factorial * (2 * n + 1 - i).factorial * (i + 1).factorial =
            (2 * n + 1 - i) * ((2 * n).factorial * (2 * n - i).factorial * (i + 1).factorial) := by
          rw [h_fact_split]; ring
        have h_idx : 2 * n + 1 - (i + 1) = 2 * n - i := by omega
        rw [h_idx] at h_factor
        rw [h_rearrange]
        exact dvd_mul_of_dvd_right h_factor _
      · -- 3 ∤ (2n+1-2i)
        have h_factor := factor_out i hi_pos hi hdvd
        rw [h_scalar]
        have h_fact_split : (i + 1).factorial = (i + 1) * i.factorial :=
          Nat.factorial_succ i
        have h_rearrange : (2 * n).factorial * (2 * n + 1 - i).factorial * (i + 1).factorial =
            (i + 1) * ((2 * n).factorial * (2 * n + 1 - i).factorial * i.factorial) := by
          rw [h_fact_split]; ring
        rw [h_rearrange]
        exact dvd_mul_of_dvd_right h_factor _

/-- Symmetry of b_formula: b_formula(n, 2n+1-k) = b_formula(n, k). -/
private lemma p3_b_formula_symm_index (n k : ℕ) (hk : 1 ≤ k) (hk2 : k ≤ 2 * n) :
    b_formula n (2 * n + 1 - k) = b_formula n k := by
  have hk2n1 : 2 * n + 1 - k ≤ 2 * n := by omega
  rw [b_formula_factored n (2 * n + 1 - k) hk2n1, b_formula_factored n k hk2]
  have h_neg1 : (-1 : ℤ) ^ (2 * n + 1 - k) = -(-1 : ℤ) ^ k := by
    have key : (-1 : ℤ) ^ (2 * n + 1 - k) * (-1) ^ k = -1 := by
      rw [← pow_add, show 2 * n + 1 - k + k = 2 * n + 1 from by omega]
      have : ∀ m, (-1 : ℤ) ^ (2 * m + 1) = -1 := by
        intro m; induction m with
        | zero => simp
        | succ t ih => rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 2 from by ring, pow_add, ih]; ring
      exact this n
    have sq_one : ((-1 : ℤ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, show k * 2 = 2 * k from by ring, pow_mul, neg_one_sq, one_pow]
    have := mul_right_cancel₀ (pow_ne_zero k (show (-1 : ℤ) ≠ 0 from by norm_num))
      (show (-1 : ℤ) ^ (2 * n + 1 - k) * (-1) ^ k = -(-1) ^ k * (-1) ^ k from by
        rw [key]; rw [show ((-1 : ℤ) ^ k) ^ 2 = (-1) ^ k * (-1) ^ k from sq ((-1 : ℤ) ^ k)] at sq_one
        linarith)
    linarith
  have h_sub : ((2 * n : ℤ) + 1 - 2 * (2 * n + 1 - k : ℕ)) = -((2 * n : ℤ) + 1 - 2 * k) := by
    zify [show k ≤ 2 * n + 1 from by omega]; ring
  have h_fact1 : ((2 * n + 1 - (2 * n + 1 - k)).factorial : ℤ) = (k.factorial : ℤ) := by
    rw [Nat.sub_sub_self (by omega : k ≤ 2 * n + 1)]
  rw [h_neg1, h_sub, h_fact1]; ring

/-- vp_b is symmetric: vp_b(n, n) = vp_b(n, n+1). -/
private lemma p3_vp_b_symm_n_n1 (p n : ℕ) (hn : 1 ≤ n) :
    vp_b p n n = vp_b p n (n + 1) := by
  unfold vp_b
  rw [← b_formula_eq_b_k_val, ← b_formula_eq_b_k_val]
  congr 1
  rw [show n + 1 = 2 * n + 1 - n from by omega]
  rw [p3_b_formula_symm_index n n (by omega) (by omega)]

/-- Recurrence: n * b_formula(n, n-1) + 3*(n+2) * b_formula(n, n) = 0. -/
private lemma p3_b_formula_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (n : ℤ) * b_formula n (n - 1) + 3 * (↑(n + 2)) * b_formula n n = 0 := by
  have hn1 : n - 1 ≤ 2 * n := by omega
  have hn2 : n ≤ 2 * n := by omega
  rw [b_formula_factored n (n - 1) hn1, b_formula_factored n n hn2]
  have h1 : ((2 * n + 1 - (n - 1)).factorial : ℤ) = ((n + 2).factorial : ℤ) := by
    have heq : 2 * n + 1 - (n - 1) = n + 2 := by omega
    rw [heq]
  have h3 : ((2 * n + 1 - n).factorial : ℤ) = ((n + 1).factorial : ℤ) := by
    have heq : 2 * n + 1 - n = n + 1 := by omega
    rw [heq]
  have h4 : ((2 * n : ℤ) + 1 - 2 * (n - 1 : ℕ)) = 3 := by omega
  have h5 : ((2 * n : ℤ) + 1 - 2 * n) = 1 := by omega
  rw [h1, h3, h4, h5]
  have h6 : ((n + 2).factorial : ℤ) = (↑(n + 2)) * ((n + 1).factorial : ℤ) := by
    push_cast [Nat.factorial_succ]; ring
  have h7 : (n.factorial : ℤ) = (↑n) * ((n - 1).factorial : ℤ) := by
    rcases n with _ | n
    · omega
    · push_cast [Nat.factorial_succ]; ring
  have h8 : (-1 : ℤ) ^ (n - 1) = -(-1 : ℤ) ^ n := by
    rcases n with _ | n
    · omega
    · simp only [show n + 1 - 1 = n from by omega, pow_succ]; ring
  rw [h6, h7, h8]; ring

/-- Two-step recurrence: n*(n-1)*b(n-2) = 5*(n+3)*(n+2)*b(n). -/
private lemma p3_b_formula_two_step (n : ℕ) (hn : 4 ≤ n) :
    (↑n : ℤ) * ↑(n - 1) * b_formula n (n - 2) = 5 * ↑(n + 3) * ↑(n + 2) * b_formula n n := by
  have hn1 : n - 2 ≤ 2 * n := by omega
  have hn2 : n ≤ 2 * n := by omega
  rw [b_formula_factored n (n - 2) hn1, b_formula_factored n n hn2]
  have h1 : ((2 * n + 1 - (n - 2)).factorial : ℤ) = ((n + 3).factorial : ℤ) := by
    have heq : 2 * n + 1 - (n - 2) = n + 3 := by omega
    rw [heq]
  have h3 : ((2 * n + 1 - n).factorial : ℤ) = ((n + 1).factorial : ℤ) := by
    have heq : 2 * n + 1 - n = n + 1 := by omega
    rw [heq]
  have h4 : ((2 * n : ℤ) + 1 - 2 * (n - 2 : ℕ)) = 5 := by omega
  have h5 : ((2 * n : ℤ) + 1 - 2 * n) = 1 := by omega
  rw [h1, h3, h4, h5]
  have h6 : ((n + 3).factorial : ℤ) = ↑(n + 3) * ↑(n + 2) * ((n + 1).factorial : ℤ) := by
    push_cast [Nat.factorial_succ]; ring
  have h7 : (n.factorial : ℤ) = ↑n * ↑(n - 1) * ((n - 2).factorial : ℤ) := by
    rcases n with _ | _ | _ | _ | n
    · omega
    · omega
    · omega
    · omega
    · push_cast [Nat.factorial_succ]; ring
  have h8 : (-1 : ℤ) ^ (n - 2) = (-1 : ℤ) ^ n := by
    rcases n with _ | _ | n
    · omega
    · omega
    · simp only [show n + 2 - 2 = n from by omega, pow_succ]; ring
  rw [h6, h7, h8]; ring

/-- When 3 ∤ n, 3 ∤ (n+2), and n ≥ 5: vp_b(n-2) ≤ vp_b(n). -/
private lemma p3_vp_b_n_minus_two_le_n (n : ℕ)
    (hn : 5 ≤ n) (hpm : ¬ (3 ∣ (n + 2))) (h3n : ¬ (3 ∣ n)) :
    vp_b 3 n (n - 2) ≤ vp_b 3 n n := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h_rec := p3_b_formula_two_step n (by omega)
  -- n*(n-1)*|b(n-2)| = 5*(n+3)*(n+2)*|b(n)|
  have h_abs : n * (n - 1) * Int.natAbs (b_formula n (n - 2)) =
      5 * (n + 3) * (n + 2) * Int.natAbs (b_formula n n) := by
    have := congr_arg Int.natAbs h_rec
    simp only [Int.natAbs_mul] at this
    push_cast at this ⊢; exact this
  have hbn_ne : Int.natAbs (b_formula n n) ≠ 0 := by
    rw [Int.natAbs_ne_zero, b_formula_eq_b_k_val]
    exact b_k_val_ne_zero n n (by omega) (by omega) (by omega)
  have hbn2_ne : Int.natAbs (b_formula n (n - 2)) ≠ 0 := by
    rw [Int.natAbs_ne_zero, b_formula_eq_b_k_val]
    exact b_k_val_ne_zero n (n - 2) (by omega) (by omega) (by omega)
  have h_vp : padicValNat 3 (n * (n - 1) * Int.natAbs (b_formula n (n - 2))) =
      padicValNat 3 (5 * (n + 3) * (n + 2) * Int.natAbs (b_formula n n)) := by rw [h_abs]
  have hnn1_ne : n * (n - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h53_ne : 5 * (n + 3) * (n + 2) ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega)
  rw [padicValNat.mul hnn1_ne hbn2_ne,
      padicValNat.mul h53_ne hbn_ne] at h_vp
  -- v_3(n*(n-1)) = 0 since 3 ∤ n and n ≡ 2 mod 3 means n-1 ≡ 1 mod 3
  have h_vpn : ¬ (3 ∣ n * (n - 1)) := by
    intro h; rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 3)).mp h with h1 | h1
    · exact h3n h1
    · have : n - 1 ≡ 1 [MOD 3] := by omega
      exact absurd h1 (by omega)
  have h_vpn0 : padicValNat 3 (n * (n - 1)) = 0 :=
    padicValNat.eq_zero_of_not_dvd h_vpn
  -- v_3(5*(n+3)*(n+2)) = 0 since 3 ∤ (n+2) and n+3 ≡ 2 mod 3
  have h_vp530 : ¬ (3 ∣ 5 * (n + 3) * (n + 2)) := by
    intro h; rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 3)).mp h with h1 | h1
    · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 3)).mp h1 with h2 | h2
      · omega
      · have : n + 3 ≡ 2 [MOD 3] := by omega
        exact absurd h2 (by omega)
    · exact hpm h1
  have h_vp5 : padicValNat 3 (5 * (n + 3) * (n + 2)) = 0 :=
    padicValNat.eq_zero_of_not_dvd h_vp530
  unfold vp_b; rw [← b_formula_eq_b_k_val, ← b_formula_eq_b_k_val]; omega

/-- When 3 ∤ (n+2) and 3 | n, vp_b(n-1) ≤ vp_b(n). -/
private lemma p3_vp_b_n_minus_one_le_n (n : ℕ)
    (hn : 2 ≤ n) (hpm : ¬ (3 ∣ (n + 2))) (h3n : 3 ∣ n) :
    vp_b 3 n (n - 1) ≤ vp_b 3 n n := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h_rec := p3_b_formula_recurrence n hn
  have h_eq : (↑n : ℤ) * b_formula n (n - 1) = -(3 * ↑(n + 2) * b_formula n n) := by linarith
  have h_abs : n * Int.natAbs (b_formula n (n - 1)) =
      3 * (n + 2) * Int.natAbs (b_formula n n) := by
    have := congr_arg Int.natAbs h_eq
    simp only [Int.natAbs_neg, Int.natAbs_mul] at this
    push_cast at this ⊢; exact this
  have hbn_ne : Int.natAbs (b_formula n n) ≠ 0 := by
    rw [Int.natAbs_ne_zero, b_formula_eq_b_k_val]
    exact b_k_val_ne_zero n n (by omega) (by omega) (by omega)
  have hbn1_ne : Int.natAbs (b_formula n (n - 1)) ≠ 0 := by
    rw [Int.natAbs_ne_zero, b_formula_eq_b_k_val]
    exact b_k_val_ne_zero n (n - 1) (by omega) (by omega) (by omega)
  have h_vp : padicValNat 3 (n * Int.natAbs (b_formula n (n - 1))) =
      padicValNat 3 (3 * (n + 2) * Int.natAbs (b_formula n n)) := by rw [h_abs]
  rw [padicValNat.mul (by omega : n ≠ 0) hbn1_ne,
      padicValNat.mul (by positivity) hbn_ne] at h_vp
  rw [padicValNat.mul (by norm_num) (by omega : n + 2 ≠ 0)] at h_vp
  have h_vp3 : padicValNat 3 3 = 1 := by simp [padicValNat.self]
  have h_vpn2 : padicValNat 3 (n + 2) = 0 := padicValNat.eq_zero_of_not_dvd hpm
  have h_vpn : 1 ≤ padicValNat 3 n := one_le_padicValNat_of_dvd (by omega) h3n
  unfold vp_b; rw [← b_formula_eq_b_k_val, ← b_formula_eq_b_k_val]; omega

/-- When 3 | (n+2) and n+2 is not a 3-power, vp_b(n - 3^a) ≤ vp_b(n).
    This is the p=3 case of vp_b_witness_bound from OffCenter.lean.
    The original has hp5 : 5 ≤ p in its signature but never uses it. -/
private lemma p3_vp_b_witness_bound (n : ℕ)
    (hn : 2 ≤ n)
    (hpm : 3 ∣ (n + 2)) (h_not_pp : ∀ k : ℕ, 1 ≤ k → n + 2 ≠ 3 ^ k) :
    vp_b 3 n (n - 3 ^ padicValNat 3 (n + 2)) ≤ vp_b 3 n n := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [ vp_b_eq, vp_b_eq ]
  · have h_denom_div_num : padicValNat 3 (Nat.choose (2 * n) (n - 3 ^ padicValNat 3 (n + 2))) ≥ padicValNat 3 (Nat.choose (2 * n) n) := by
      have h_binom_ratio : (Nat.choose (2 * n) n : ℚ) / (Nat.choose (2 * n) (n - 3 ^ padicValNat 3 (n + 2)) : ℚ) = (∏ j ∈ Finset.range (3 ^ padicValNat 3 (n + 2)), (n + j + 1 : ℚ)) / (∏ j ∈ Finset.range (3 ^ padicValNat 3 (n + 2)), (n - j : ℚ)) := by
        have h_binom_def : (Nat.choose (2 * n) n : ℚ) = (Nat.factorial (2 * n)) / (Nat.factorial n * Nat.factorial n) ∧ (Nat.choose (2 * n) (n - 3 ^ padicValNat 3 (n + 2)) : ℚ) = (Nat.factorial (2 * n)) / (Nat.factorial (n - 3 ^ padicValNat 3 (n + 2)) * Nat.factorial (n + 3 ^ padicValNat 3 (n + 2))) := by
          constructor <;> rw [ Nat.cast_choose ]
          · rw [ two_mul, add_tsub_cancel_left ]
          · linarith
          · rw [ show 2 * n - ( n - 3 ^ padicValNat 3 ( n + 2 ) ) = n + 3 ^ padicValNat 3 ( n + 2 ) by rw [ Nat.sub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( show 3 ^ padicValNat 3 ( n + 2 ) ≤ n from by exact Nat.le_of_lt_succ <| by { have := pa_le_n 3 n hn hpm h_not_pp; linarith } ) ] ]
          · exact le_trans ( Nat.sub_le _ _ ) ( by linarith )
        have h_factorial_def : (Nat.factorial n : ℚ) = (∏ j ∈ Finset.range (3 ^ padicValNat 3 (n + 2)), (n - j : ℚ)) * (Nat.factorial (n - 3 ^ padicValNat 3 (n + 2)) : ℚ) ∧ (Nat.factorial (n + 3 ^ padicValNat 3 (n + 2)) : ℚ) = (∏ j ∈ Finset.range (3 ^ padicValNat 3 (n + 2)), (n + j + 1 : ℚ)) * (Nat.factorial n : ℚ) := by
          constructor
          · have h_factorial_def : ∀ m ≤ n, (Nat.factorial n : ℚ) = (∏ j ∈ Finset.range m, (n - j : ℚ)) * (Nat.factorial (n - m) : ℚ) := by
              intro m hm; induction' m with m ih <;> simp_all +decide [ Finset.prod_range_succ, Nat.factorial ] ; ring;
              rw [ ih ( Nat.le_of_lt hm ) ] ; rw [ show n - m = n - ( 1 + m ) + 1 by omega ] ; push_cast [ Nat.factorial_succ ] ; ring;
              rw [ Nat.cast_sub ( by linarith ) ] ; push_cast ; ring
            exact h_factorial_def _ ( by linarith [ pa_le_n 3 n hn hpm h_not_pp ] )
          · induction' 3 ^ padicValNat 3 ( n + 2 ) with k hk <;> simp_all +decide [ Nat.factorial, Finset.prod_range_succ ] ; ring
        rw [ h_binom_def.1, h_binom_def.2, div_div_eq_mul_div ]
        rw [ div_mul_eq_mul_div, div_div, div_eq_div_iff ] <;> first | positivity | push_cast [ h_factorial_def ] ; ring
        exact Finset.prod_ne_zero_iff.mpr fun x hx => sub_ne_zero_of_ne <| by norm_cast; linarith [ Finset.mem_range.mp hx, show 3 ^ padicValNat 3 ( 2 + n ) ≤ n from by simpa only [ add_comm ] using pa_le_n 3 n ( by simpa only [ add_comm ] using hn ) ( by simpa only [ add_comm ] using hpm ) ( by simpa only [ add_comm ] using h_not_pp ) ]
      have h_padic_val : padicValRat 3 ((∏ j ∈ Finset.range (3 ^ padicValNat 3 (n + 2)), (n + j + 1 : ℚ)) / (∏ j ∈ Finset.range (3 ^ padicValNat 3 (n + 2)), (n - j : ℚ))) ≤ 0 := by
        have h_padic_val : (∏ j ∈ Finset.range (3 ^ padicValNat 3 (n + 2)), (n + j + 1 : ℕ)).factorization 3 ≤ (∏ j ∈ Finset.range (3 ^ padicValNat 3 (n + 2)), (n - j : ℕ)).factorization 3 := by
          convert binom_ratio_vp_le 3 ( padicValNat 3 ( n + 2 ) ) ( by linarith [ a_ge_one 3 n hpm ] ) ( ( n + 2 ) / 3 ^ padicValNat 3 ( n + 2 ) ) ( by linarith [ r_ge_two 3 n hn hpm h_not_pp ] ) ( by exact p_not_dvd_r 3 n hpm ) using 1
          · rw [ ← n_eq_par_minus_two 3 n hpm ]; rw [ Nat.factorization_def ]; exact Fact.out
          · rw [ ← n_eq_par_minus_two 3 n hpm ]; rw [ Nat.factorization_def ]; exact Fact.out
        have h_padic_val : padicValRat 3 ((∏ j ∈ Finset.range (3 ^ padicValNat 3 (n + 2)), (n + j + 1 : ℕ)) : ℚ) ≤ padicValRat 3 ((∏ j ∈ Finset.range (3 ^ padicValNat 3 (n + 2)), (n - j : ℕ)) : ℚ) := by
          exact_mod_cast h_padic_val
        convert sub_nonpos_of_le h_padic_val using 1
        convert padicValRat.div _ _ using 1
        · norm_cast
          rw [ Int.subNatNat_eq_coe ] ; norm_num [ padicValRat.of_nat ]
          rw [ ← padicValRat.of_nat ]; rw [ Nat.cast_prod ]
          exact congr_arg _ ( Finset.prod_congr rfl fun x hx => by rw [ Nat.cast_sub ( show x ≤ n from le_trans ( Finset.mem_range_le hx ) ( Nat.le_of_lt_succ ( by linarith [ show 3 ^ padicValNat 3 ( n + 2 ) ≤ n from pa_le_n 3 n hn hpm h_not_pp ] ) ) ) ] )
        · exact ⟨ Fact.out ⟩
        · exact Finset.prod_ne_zero_iff.mpr fun _ _ => by positivity
        · exact Finset.prod_ne_zero_iff.mpr fun x hx => sub_ne_zero_of_ne <| by norm_cast; linarith [ Finset.mem_range.mp hx, show 3 ^ padicValNat 3 ( n + 2 ) ≤ n from pa_le_n 3 n hn hpm h_not_pp ]
      contrapose! h_padic_val
      rw [ ← h_binom_ratio, padicValRat.div ] <;> norm_num
      · convert h_padic_val using 1
      · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith
      · exact Nat.ne_of_gt <| Nat.choose_pos <| Nat.sub_le_of_le_add <| by linarith [ Nat.pow_le_pow_right (show 1 ≤ 3 from by norm_num) <| show padicValNat 3 ( n + 2 ) ≥ 1 from a_ge_one 3 n hpm ]
    have h_num_eq : padicValNat 3 (bk_num n (n - 3 ^ padicValNat 3 (n + 2))) = padicValNat 3 (bk_num n n) := by
      have h_linear_factors : padicValNat 3 (n + 1 + 3 ^ padicValNat 3 (n + 2)) = 0 ∧ padicValNat 3 (2 * 3 ^ padicValNat 3 (n + 2) + 1) = 0 ∧ padicValNat 3 (n + 1) = 0 := by
        exact ⟨ vp_n_plus_one_plus_pa_eq_zero 3 n ( by simpa using hpm ), vp_two_pa_plus_one_eq_zero 3 ( by linarith ) _ ( a_ge_one 3 n ( by simpa using hpm ) ), vp_n_plus_one_eq_zero 3 n ( by simpa using hpm ) ⟩
      have h_num_eq : bk_num n (n - 3 ^ padicValNat 3 (n + 2)) = 2 * ((2 * n).factorial) ^ 2 * (n + 1 + 3 ^ padicValNat 3 (n + 2)) * (2 * 3 ^ padicValNat 3 (n + 2) + 1) := by
        unfold bk_num
        rw [ Nat.cast_sub ] <;> push_cast <;> ring
        · norm_cast ; ring
        · convert pa_le_n 3 n hn ( by simpa only [ add_comm ] using hpm ) ( by simpa only [ add_comm ] using h_not_pp ) using 1 ; ring
      simp_all +decide [ mul_assoc, padicValNat.mul, Nat.factorial_ne_zero ]
      unfold bk_num; simp +decide [ *, padicValNat.mul, Nat.factorial_ne_zero ]
      rw [ show ( 2 * n + 1 - n : ℤ ) = n + 1 by ring ] ; norm_cast ; simp +decide [ *, padicValNat.mul, Nat.factorial_ne_zero ]
      rw [ padicValNat.eq_zero_of_not_dvd ( show ¬ 3 ∣ n + 1 + 3 ^ padicValNat 3 ( n + 2 ) from by aesop ), padicValNat.eq_zero_of_not_dvd ( show ¬ 3 ∣ 2 * 3 ^ padicValNat 3 ( n + 2 ) + 1 from by aesop ), padicValNat.eq_zero_of_not_dvd ( show ¬ 3 ∣ n + 1 from by aesop ) ] ; ring
    exact h_num_eq.symm ▸ Nat.sub_le_sub_left h_denom_div_num _
  · linarith
  · exact le_trans ( Nat.sub_le _ _ ) ( by linarith )

/-- Off-center minimizer for p = 3 (requires n ≥ 3). -/
private lemma exists_valid_min_vp_b_p3 (n : ℕ) (hn : 3 ≤ n)
    (h_not_pp : ∀ k : ℕ, 1 ≤ k → n + 2 ≠ 3 ^ k) :
    ∃ k₀, 1 ≤ k₀ ∧ k₀ ≤ 2 * n ∧ k₀ ≠ n ∧ k₀ ≠ n + 1 ∧
    ∀ k ∈ Finset.Icc 1 (2 * n), vp_b 3 n k₀ ≤ vp_b 3 n k := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- Find the overall minimizer
  have hne : (Finset.Icc 1 (2 * n)).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩⟩
  obtain ⟨k_min, hk_min_mem, hk_min_le⟩ :=
    Finset.exists_min_image (Finset.Icc 1 (2 * n)) (vp_b 3 n) hne
  have hk_min_bounds := Finset.mem_Icc.mp hk_min_mem
  -- Find an off-center index with vp_b ≤ vp_b(n)
  have h_off_center : ∃ w, 1 ≤ w ∧ w ≤ 2 * n ∧ w ≠ n ∧ w ≠ n + 1 ∧
      vp_b 3 n w ≤ vp_b 3 n n := by
    by_cases h_div : 3 ∣ (n + 2)
    · -- Case: 3 | (n+2), use p3_vp_b_witness_bound
      have h_wit := p3_vp_b_witness_bound n (by omega) h_div h_not_pp
      have h_pa_le := pa_le_n 3 n (by omega) h_div h_not_pp
      have ha_pos := a_ge_one 3 n h_div
      have h_2pa : n + 2 ≥ 2 * 3 ^ padicValNat 3 (n + 2) := by
        have hr := r_ge_two 3 n (by omega) h_div h_not_pp
        set a := padicValNat 3 (n + 2)
        set r := (n + 2) / 3 ^ a
        have h_pa_dvd : 3 ^ a ∣ (n + 2) := pow_padicValNat_dvd
        have h_eq : n + 2 = 3 ^ a * r := by rw [Nat.mul_div_cancel' h_pa_dvd]
        nlinarith [pow_pos (show 0 < 3 from by norm_num) a]
      have h_pa_pos : 0 < 3 ^ padicValNat 3 (n + 2) := pow_pos (by norm_num) _
      exact ⟨n - 3 ^ padicValNat 3 (n + 2), by omega, by omega, by omega, by omega, h_wit⟩
    · -- Case: 3 ∤ (n+2)
      by_cases h3n : 3 ∣ n
      · exact ⟨n - 1, by omega, by omega, by omega, by omega,
          p3_vp_b_n_minus_one_le_n n (by omega) h_div h3n⟩
      · -- Sub-case: 3 ∤ n, 3 ∤ (n+2). Then n ≡ 2 mod 3, so n ≥ 5.
        -- Use two-step recurrence: vp_b(n, n-2) = vp_b(n, n).
        have hn5 : 5 ≤ n := by omega
        exact ⟨n - 2, by omega, by omega, by omega, by omega,
          p3_vp_b_n_minus_two_le_n n hn5 h_div h3n⟩
  obtain ⟨w, hw1, hw2, hwn, hwn1, hw_le⟩ := h_off_center
  have h_symm := p3_vp_b_symm_n_n1 3 n (by omega)
  by_cases hkn : k_min = n ∨ k_min = n + 1
  · refine ⟨w, hw1, hw2, hwn, hwn1, fun k hk => ?_⟩
    calc vp_b 3 n w ≤ vp_b 3 n n := hw_le
      _ ≤ vp_b 3 n k_min := by rcases hkn with rfl | rfl <;> [exact le_refl _; exact h_symm.le]
      _ ≤ vp_b 3 n k := hk_min_le k hk
  · push_neg at hkn
    exact ⟨k_min, hk_min_bounds.1, hk_min_bounds.2, hkn.1, hkn.2, fun k hk => hk_min_le k hk⟩

private theorem even_of_not_prime_power_p3 (n : ℕ) (hn : 2 ≤ n)
    (h_not_pp : ∀ k : ℕ, 1 ≤ k → n + 2 ≠ 3 ^ k) :
    Even (padicValNat 3 (S n)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hn_pos : 0 < n := by omega
  -- n = 2 requires separate treatment: the off-center minimizer lemma needs n ≥ 3,
  -- because for n = 2 (with n ≡ 2 mod 3) the center {n, n+1} is the strict global
  -- minimum of vp_b, so no off-center global minimizer exists.
  -- For n = 2: v₃(S(2)) is even by direct computation.
  by_cases hn2 : n = 2
  · subst hn2
    -- n = 2, n + 2 = 4, not a power of 3.
    -- For n = 2: the center {2,3} is the strict global minimum of vp_b
    -- (vp_b = 2 at center, vp_b = 3 off-center), so no off-center global
    -- minimizer exists. The sandwich argument needs a different approach.
    -- v₃(S(2)) = 4, which is even.
    -- Upper bound: evaluate Δ_2 at c(j) = [j=2 ∨ j=3] to get -2654208 = -(2^15 · 3^4).
    set c : ℕ → ℤ := fun j => if j = 2 ∨ j = 3 then 1 else 0 with c_def
    have h_eval : Δ_eval 2 c = -2654208 := by
      unfold Δ_eval B_eval A_eval C_eval α β
      simp [Finset.sum_range_succ, c_def, Nat.choose]
      norm_num
    have h_eval' : MvPolynomial.eval c (Δ_n 2) = -2654208 := by
      rw [eval_Δ_eq_Δ_eval]; exact h_eval
    have h_ne : MvPolynomial.eval c (Δ_n 2) ≠ 0 := by rw [h_eval']; norm_num
    have hS_ne : S 2 ≠ 0 := S_ne_zero_of_eval_ne_zero 2 c h_ne
    have h_upper := vp_S_le_eval 3 2 c h_ne
    rw [h_eval'] at h_upper
    -- v_3(|-2654208|) = v_3(2654208) = 4
    have h_vp : padicValNat 3 (Int.natAbs (-2654208 : ℤ)) = 4 := by native_decide
    rw [h_vp] at h_upper
    -- Lower bound: all b_formula(2,k) for k ∈ [1,4] have v_3 ≥ 2
    have he : ∀ k ∈ Finset.Icc 1 (2 * 2),
        2 ≤ padicValNat 3 (Int.natAbs (b_formula 2 k)) := by
      intro k hk
      simp only [Finset.mem_Icc, Nat.reduceAdd, Nat.reduceMul] at hk
      obtain ⟨h1, h2⟩ := hk
      interval_cases k <;> native_decide
    have hB : ∀ m, ((3 ^ 2 : ℕ) : ℤ) ∣ (B_n 2).coeff m :=
      coeff_B_n_dvd 3 2 2 (by omega) he
    have hA : ∀ m, ((3 ^ 2 : ℕ) : ℤ) ∣ (A_n 2).coeff m := by
      have h_scalar := scalar_AB_dvd_of_vp_b_min_p3 2 (by omega) 2 he
      intro m; unfold A_n; erw [MvPolynomial.coeff_sum]
      exact Finset.dvd_sum fun i hi => by
        have hi' : i ≤ 2 * 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h_dvd : ((3 ^ 2 : ℕ) : ℤ) ∣
            ((-1 : ℤ) ^ i * (Nat.choose (2 * 2) i : ℤ) * (α 2 i : ℤ) * (β 2 i : ℤ)) := by
          have := Int.natCast_dvd_natCast.mpr (h_scalar i hi')
          convert this.mul_left ((-1 : ℤ) ^ i) using 1; simp [scalar_AB]; push_cast; ring
        rw [MvPolynomial.coeff_mul]; exact Finset.dvd_sum fun x _ => by
          erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']; aesop
    have hC : ∀ m, ((3 ^ 2 : ℕ) : ℤ) ∣ (C_n 2).coeff m := by
      have h_scalar := scalar_AB_dvd_of_vp_b_min_p3 2 (by omega) 2 he
      intro m; unfold C_n; erw [MvPolynomial.coeff_sum]
      exact Finset.dvd_sum fun i hi => by
        have hi' : i ≤ 2 * 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h_dvd : ((3 ^ 2 : ℕ) : ℤ) ∣
            ((-1 : ℤ) ^ i * (Nat.choose (2 * 2) i : ℤ) * (α 2 i : ℤ) * (β 2 i : ℤ)) := by
          have := Int.natCast_dvd_natCast.mpr (h_scalar i hi')
          convert this.mul_left ((-1 : ℤ) ^ i) using 1; simp [scalar_AB]; push_cast; ring
        generalize_proofs at *
        rw [MvPolynomial.coeff_mul]; exact Finset.dvd_sum fun x _ => by
          erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']; aesop
    have h_coeff : ∀ m ∈ (Δ_n 2).support,
        3 ^ (2 * 2) ∣ Int.natAbs ((Δ_n 2).coeff m) := by
      intro m _
      have h2e := coeff_Δ_n_dvd_sq 3 2 2 hA hB hC m
      exact Int.natCast_dvd.mp h2e
    have h_lower : 2 * 2 ≤ padicValNat 3 (S 2) :=
      vp_S_ge_of_coeff_dvd 3 2 (2 * 2) hS_ne h_coeff
    -- v₃(S(2)) = 4, which is even
    exact ⟨2, by omega⟩
  -- Get a valid specialization index achieving the minimum vp_b
  obtain ⟨k₀, hk₀_lo, hk₀_hi, hk₀_ne_n, hk₀_ne_n1, hk₀_min⟩ :=
    exists_valid_min_vp_b_p3 n (by omega) h_not_pp
  set e_min := vp_b 3 n k₀
  -- Step 1: Δ(φ_{k₀}) = b_{k₀}²
  have h_delta_sq : MvPolynomial.eval (phi n k₀) (Δ_n n) = (b_k_val n k₀) ^ 2 := by
    rw [eval_Delta_n_phi_eq_sq n k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1,
        eval_B_phi_eq_bk n k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1 hn_pos]
  have hb_ne : b_k_val n k₀ ≠ 0 := b_k_val_ne_zero n k₀ (by omega) hk₀_lo hk₀_hi
  have h_eval_ne : MvPolynomial.eval (phi n k₀) (Δ_n n) ≠ 0 := by
    rw [h_delta_sq]; exact pow_ne_zero 2 hb_ne
  have hS_ne : S n ≠ 0 := S_ne_zero_of_eval_ne_zero n (phi n k₀) h_eval_ne
  -- Upper bound: v_3(S) ≤ 2 · e_min
  have h_upper : padicValNat 3 (S n) ≤ 2 * e_min := by
    have h1 := vp_S_le_eval 3 n (phi n k₀) h_eval_ne
    rw [h_delta_sq] at h1
    simp only [Int.natAbs_pow] at h1
    rw [padicValNat.pow 2 (show Int.natAbs (b_k_val n k₀) ≠ 0 from by
      rwa [Int.natAbs_ne_zero])] at h1
    exact h1
  -- Lower bound from coefficient divisibility
  have he_bformula : ∀ k ∈ Finset.Icc 1 (2 * n),
      e_min ≤ padicValNat 3 (Int.natAbs (b_formula n k)) := by
    intro k hk; rw [b_formula_eq_b_k_val]; exact hk₀_min k hk
  have hB : ∀ m, ((3 ^ e_min : ℕ) : ℤ) ∣ (B_n n).coeff m :=
    coeff_B_n_dvd 3 n e_min hn_pos he_bformula
  have hA : ∀ m, ((3 ^ e_min : ℕ) : ℤ) ∣ (A_n n).coeff m := by
    have h_scalar := scalar_AB_dvd_of_vp_b_min_p3 n hn_pos e_min he_bformula
    intro m; unfold A_n; erw [MvPolynomial.coeff_sum]
    exact Finset.dvd_sum fun i hi => by
      have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h_dvd : ((3 ^ e_min : ℕ) : ℤ) ∣
          ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) * (β n i : ℤ)) := by
        have := Int.natCast_dvd_natCast.mpr (h_scalar i hi')
        convert this.mul_left ((-1 : ℤ) ^ i) using 1; simp [scalar_AB]; push_cast; ring
      rw [MvPolynomial.coeff_mul]; exact Finset.dvd_sum fun x _ => by
        erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']; aesop
  have hC : ∀ m, ((3 ^ e_min : ℕ) : ℤ) ∣ (C_n n).coeff m := by
    have h_scalar := scalar_AB_dvd_of_vp_b_min_p3 n hn_pos e_min he_bformula
    intro m; unfold C_n; erw [MvPolynomial.coeff_sum]
    exact Finset.dvd_sum fun i hi => by
      have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h_dvd : ((3 ^ e_min : ℕ) : ℤ) ∣
          ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) * (β n i : ℤ)) := by
        have := Int.natCast_dvd_natCast.mpr (h_scalar i hi')
        convert this.mul_left ((-1 : ℤ) ^ i) using 1; simp [scalar_AB]; push_cast; ring
      generalize_proofs at *
      rw [MvPolynomial.coeff_mul]; exact Finset.dvd_sum fun x _ => by
        erw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X']; aesop
  have h_coeff : ∀ m ∈ (Δ_n n).support,
      3 ^ (2 * e_min) ∣ Int.natAbs ((Δ_n n).coeff m) := by
    intro m _
    have h2e := coeff_Δ_n_dvd_sq 3 n e_min hA hB hC m
    exact Int.natCast_dvd.mp h2e
  have h_lower : 2 * e_min ≤ padicValNat 3 (S n) :=
    vp_S_ge_of_coeff_dvd 3 n (2 * e_min) hS_ne h_coeff
  exact ⟨e_min, by omega⟩

/-! ## Main theorem for p = 3 -/

theorem main_theorem_p3 (n : ℕ) (hn : 2 ≤ n) :
    @Odd ℕ _ (padicValNat 3 (S n)) ↔ ∃ k : ℕ, 1 ≤ k ∧ n + 2 = 3 ^ k := by
  constructor
  · -- Forward: Odd → ∃ k, n+2 = 3^k (by contrapositive)
    intro hodd
    by_contra h_not
    push_neg at h_not
    exact absurd hodd (by rw [Nat.not_odd_iff_even]; exact even_of_not_prime_power_p3 n hn h_not)
  · -- Backward: ∃ k, n+2 = 3^k → Odd
    rintro ⟨k, hk, hpow⟩
    exact odd_of_prime_power_p3 n (by omega) k hk hpow

end QuarticInvariant
