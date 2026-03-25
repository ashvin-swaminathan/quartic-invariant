import Mathlib
import Modular.Defs
import Modular.ContentBasics
import Modular.PairSpec
import Modular.ScalarBounds
import Modular.CentralDom
import Modular.GaussMV
import Modular.Mod4Lift
import Modular.CoeffCongP2
import Modular.CoeffDivPP
import Modular.MainP5
import Modular.Rank1Collapse
import Modular.P2CRS
import Modular.P2Step5
import Modular.P2CarryMax
import Modular.CoeffExtract

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ====================================================================
    P2CaseB: Steps 6.1-6.5 and 6.10 of the p=2 proof
    Case B: v_2(cont(G^2)) = v_2(cont(AC)), i.e. equal content valuations
    ==================================================================== -/

/-! ## Step 6.1 -- Setup

  Redefinitions (G_poly, H_poly are private in MainP2.lean). -/

/-- G_poly n = B_n / 2 as an integer MvPolynomial. -/
private def G_poly (n : ℕ) : MvPolynomial ℕ ℤ :=
  Finsupp.mapRange (· / 2) (by simp) (B_n n)

/-- H_poly n = G^2 - AC. -/
private def H_poly (n : ℕ) : MvPolynomial ℕ ℤ :=
  G_poly n ^ 2 - A_n n * C_n n

@[simp]
private lemma G_poly_coeff (n : ℕ) (m : ℕ →₀ ℕ) :
    (G_poly n).coeff m = (B_n n).coeff m / 2 :=
  Finsupp.mapRange_apply (hf := by simp)

/-- Every coefficient of B_n is divisible by 2. -/
private lemma two_dvd_B_coeff (n : ℕ) (hn : 0 < n) :
    ∀ m, (2 : ℤ) ∣ (B_n n).coeff m := by
  intro m
  have he_b : ∀ k ∈ Finset.Icc 1 (2 * n),
      1 ≤ padicValNat 2 (Int.natAbs (b_formula n k)) := by
    intro k hk
    have hk2 : k ≤ 2 * n := (Finset.mem_Icc.mp hk).2
    have h_factored := b_formula_factored n k hk2
    have h_dvd : (2 : ℤ) ∣ b_formula n k := by
      rw [h_factored]; exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) _
    have h_ne : b_formula n k ≠ 0 := by
      rw [h_factored]; apply mul_ne_zero
      · apply mul_ne_zero; norm_num; exact pow_ne_zero _ (by norm_num)
      · apply mul_ne_zero; apply mul_ne_zero; apply mul_ne_zero
        · exact_mod_cast (Nat.factorial_pos _).ne'
        · omega
        · exact_mod_cast (Nat.factorial_pos _).ne'
        · exact_mod_cast (Nat.factorial_pos _).ne'
    exact one_le_padicValNat_of_dvd
      (Int.natAbs_ne_zero.mpr h_ne)
      (Int.natAbs_dvd_natAbs.mpr h_dvd)
  exact coeff_B_n_dvd 2 n 1 hn he_b m

/-- B_n = 2 * G_poly. -/
private lemma B_eq_two_G (n : ℕ) (hn : 0 < n) : B_n n = 2 * G_poly n := by
  ext m
  rw [show (2 : MvPolynomial ℕ ℤ) = MvPolynomial.C 2 from by simp [map_ofNat]]
  rw [MvPolynomial.coeff_C_mul, G_poly_coeff]
  exact (Int.mul_ediv_cancel' (two_dvd_B_coeff n hn m)).symm

/-- content(A_n) = content(C_n). -/
private lemma content_A_eq_C (n : ℕ) :
    mvContent (A_n n) = mvContent (C_n n) := by
  have h_rename : C_n n = MvPolynomial.rename (· + 1) (A_n n) := by
    unfold A_n C_n
    simp only [map_sum, MvPolynomial.rename_C, MvPolynomial.rename_X, map_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    congr 2; omega
  have hinj : Function.Injective (fun x : ℕ => x + 1) := by
    intro a b h
    exact Nat.succ.inj h
  rw [h_rename]
  unfold mvContent
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.gcd_image]
  congr 1; ext dd
  simp [Function.comp, MvPolynomial.coeff_rename_mapDomain _ hinj]

/-- content(AC) = content(A)^2. -/
private lemma content_AC (n : ℕ) :
    mvContent (A_n n * C_n n) = mvContent (A_n n) ^ 2 := by
  rw [mvContent_mul, content_A_eq_C, sq]

/-! ### Step 6.1: Define d, quotient polynomials G', A', C'

  d = v_2(content(G_poly n))
  The quotient polynomials are obtained by dividing each coefficient by 2^d.
  We work abstractly: we need that 2^d divides every coefficient of G, A, C. -/

/-- d = padicValNat 2 (mvContent (G_poly n)). -/
private def d (n : ℕ) : ℕ := padicValNat 2 (mvContent (G_poly n))

/-- 2^d divides every coefficient of G_poly (by definition of content). -/
private lemma pow_d_dvd_G_coeff (n : ℕ) (m : ℕ →₀ ℕ) :
    (↑(2 ^ d n) : ℤ) ∣ (G_poly n).coeff m :=
  dvd_trans (Int.natCast_dvd_natCast.mpr pow_padicValNat_dvd)
    (mvContent_dvd_coeff (G_poly n) m)

/-- G_poly and G_poly_loc are definitionally the same polynomial. -/
private lemma G_poly_eq_G_poly_loc (n : ℕ) : G_poly n = G_poly_loc n := by
  unfold G_poly G_poly_loc; rfl

/-- Content of G_poly_loc is nonzero when n ≥ 1, since B_n has nonzero evaluations. -/
private lemma mvContent_G_poly_loc_ne (n : ℕ) (hn : 1 ≤ n) :
    mvContent (G_poly_loc n) ≠ 0 := by
  intro hG0
  have hG_zero : G_poly_loc n = 0 := by
    ext m; have := mvContent_dvd_coeff (G_poly_loc n) m
    rw [hG0, Nat.cast_zero, zero_dvd_iff] at this; exact this
  have h_B_eq_2G : B_n n = 2 * G_poly_loc n := by
    ext m
    rw [show (2 : MvPolynomial ℕ ℤ) = MvPolynomial.C 2 from by simp [map_ofNat]]
    rw [MvPolynomial.coeff_C_mul, G_poly_loc_coeff]
    exact (Int.mul_ediv_cancel' (two_dvd_B_coeff n hn m)).symm
  have hB_zero : B_n n = 0 := by rw [h_B_eq_2G, hG_zero, mul_zero]
  have h_b_ne : b_formula n 1 ≠ 0 := b_k_val_ne_zero n 1 hn le_rfl (by omega)
  have h_eval_B : MvPolynomial.eval (phi n 1) (B_n n) = 0 := by rw [hB_zero, map_zero]
  have h_eval_B' : MvPolynomial.eval (phi n 1) (B_n n) = b_formula n 1 := by
    rw [B_n_eq_alt n (by omega)]
    simp only [B_n_alt, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    have hph_0 : phi n 1 0 = 0 := by simp only [phi]; rw [if_neg]; push_neg; constructor <;> omega
    rw [show (2 * ((2 * n + 1).factorial : ℤ) ^ 2) * phi n 1 0 * phi n 1 (2 * n + 1) = 0 from by
      rw [hph_0, mul_zero, zero_mul], zero_add]
    rw [Finset.sum_eq_single 1]
    · simp only [phi]; simp
    · intro j hj hj_ne
      have hj_bounds := Finset.mem_Icc.mp hj
      have : phi n 1 j = 0 := by
        simp only [phi]; rw [if_neg]; push_neg; exact ⟨hj_ne, by omega⟩
      rw [this]; ring
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) h
  exact h_b_ne (h_eval_B ▸ h_eval_B'.symm ▸ rfl)

/-- Content of A_n is nonzero when n ≥ 1. -/
private lemma mvContent_A_ne (n : ℕ) (hn : 1 ≤ n) :
    mvContent (A_n n) ≠ 0 := by
  intro hA0
  set δ_n : ℕ → ℤ := fun j => if j = n then 1 else 0
  have h_eval : MvPolynomial.eval δ_n (A_n n) = (-1 : ℤ) ^ n * (scalar_AB n n : ℤ) := by
    simp only [A_n, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [Finset.sum_eq_single n]
    · simp only [δ_n, if_pos rfl, mul_one, show 2 * n - n = n from by omega, scalar_AB]; push_cast; ring
    · intro i _ hi_ne; simp only [δ_n, hi_ne, if_false, zero_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have h_sAB_ne : scalar_AB n n ≠ 0 := by
    unfold scalar_AB α β
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne'
      (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne'))
      (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
  have h_eval_ne : MvPolynomial.eval δ_n (A_n n) ≠ 0 := by
    rw [h_eval]; exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Int.natCast_ne_zero.mpr h_sAB_ne)
  have h_cont_dvd : (↑(mvContent (A_n n)) : ℤ) ∣ MvPolynomial.eval δ_n (A_n n) := by
    rw [MvPolynomial.eval_eq]
    exact Finset.dvd_sum fun m _ => dvd_mul_of_dvd_left (mvContent_dvd_coeff (A_n n) m) _
  rw [hA0, Nat.cast_zero, zero_dvd_iff] at h_cont_dvd
  exact h_eval_ne h_cont_dvd

/-- In Case B (equal valuations), v_2(cont(A)) = d.
    Proof: Both v₂(cont(A)) and v₂(cont(G)) equal v₂(scalar_AB(n,n))
    by P2Step5.v2_content_A_eq_scalar_AB and P2Step5.v2_content_G_eq_scalar_AB.
    Since d = v₂(cont(G)), we get v₂(cont(A)) = d. -/
private lemma v2_content_A_eq_d (n : ℕ) (K : ℕ) (hK : 2 ≤ K)
    (hnK : n + 2 = 2 ^ K) :
    padicValNat 2 (mvContent (A_n n)) = d n := by
  unfold d
  rw [G_poly_eq_G_poly_loc]
  have hn_pos : 1 ≤ n := by rcases K, hK with ⟨_ | _ | K, hK⟩ <;> omega
  rw [v2_content_A_eq_scalar_AB n K hK hnK (mvContent_A_ne n hn_pos),
      v2_content_G_eq_scalar_AB n K hK hnK (mvContent_G_poly_loc_ne n hn_pos)]

/-- 2^d divides every coefficient of A_n (in Case B). -/
private lemma pow_d_dvd_A_coeff (n : ℕ) (K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (m : ℕ →₀ ℕ) :
    (↑(2 ^ d n) : ℤ) ∣ (A_n n).coeff m := by
  have h := v2_content_A_eq_d n K hK hnK
  have : 2 ^ d n ∣ mvContent (A_n n) := h ▸ pow_padicValNat_dvd
  exact dvd_trans (Int.natCast_dvd_natCast.mpr this) (mvContent_dvd_coeff _ m)

/-- 2^d divides every coefficient of C_n (in Case B), since cont(C) = cont(A). -/
private lemma pow_d_dvd_C_coeff (n : ℕ) (K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (m : ℕ →₀ ℕ) :
    (↑(2 ^ d n) : ℤ) ∣ (C_n n).coeff m := by
  have h := v2_content_A_eq_d n K hK hnK
  have hcac := content_A_eq_C n
  have : 2 ^ d n ∣ mvContent (C_n n) := by rw [← hcac, ← h]; exact pow_padicValNat_dvd
  exact dvd_trans (Int.natCast_dvd_natCast.mpr this) (mvContent_dvd_coeff _ m)

/-- Define the quotient polynomial G' = G / 2^d. -/
private def G' (n : ℕ) : MvPolynomial ℕ ℤ :=
  Finsupp.mapRange (· / (2 ^ d n : ℤ)) (by simp) (G_poly n)

/-- Define the quotient polynomial A' = A / 2^d. -/
private def A' (n K : ℕ) : MvPolynomial ℕ ℤ :=
  Finsupp.mapRange (· / (2 ^ d n : ℤ)) (by simp) (A_n n)

/-- Define the quotient polynomial C' = C / 2^d. -/
private def C' (n K : ℕ) : MvPolynomial ℕ ℤ :=
  Finsupp.mapRange (· / (2 ^ d n : ℤ)) (by simp) (C_n n)

private lemma G'_coeff (n : ℕ) (m : ℕ →₀ ℕ) :
    (G' n).coeff m = (G_poly n).coeff m / (2 ^ d n : ℤ) :=
  Finsupp.mapRange_apply (hf := by simp)

private lemma A'_coeff (n K : ℕ) (m : ℕ →₀ ℕ) :
    (A' n K).coeff m = (A_n n).coeff m / (2 ^ d n : ℤ) :=
  Finsupp.mapRange_apply (hf := by simp)

private lemma C'_coeff (n K : ℕ) (m : ℕ →₀ ℕ) :
    (C' n K).coeff m = (C_n n).coeff m / (2 ^ d n : ℤ) :=
  Finsupp.mapRange_apply (hf := by simp)

/-- G = 2^d * G'. -/
private lemma G_eq_scaled_G' (n : ℕ) :
    G_poly n = MvPolynomial.C (2 ^ d n : ℤ) * G' n := by
  ext m; rw [MvPolynomial.coeff_C_mul, G'_coeff]
  exact (Int.mul_ediv_cancel' (pow_d_dvd_G_coeff n m)).symm

/-- A = 2^d * A'. -/
private lemma A_eq_scaled_A' (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K) :
    A_n n = MvPolynomial.C (2 ^ d n : ℤ) * A' n K := by
  ext m; rw [MvPolynomial.coeff_C_mul, A'_coeff]
  exact (Int.mul_ediv_cancel' (pow_d_dvd_A_coeff n K hK hnK m)).symm

/-- C = 2^d * C'. -/
private lemma C_eq_scaled_C' (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K) :
    C_n n = MvPolynomial.C (2 ^ d n : ℤ) * C' n K := by
  ext m; rw [MvPolynomial.coeff_C_mul, C'_coeff]
  exact (Int.mul_ediv_cancel' (pow_d_dvd_C_coeff n K hK hnK m)).symm

/-- H = (2^d)^2 * (G'^2 - A'C'). -/
private lemma H_eq_scaled (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K) :
    H_poly n = MvPolynomial.C ((2 ^ d n : ℤ) ^ 2) * (G' n ^ 2 - A' n K * C' n K) := by
  unfold H_poly
  rw [G_eq_scaled_G' n, A_eq_scaled_A' n K hK hnK, C_eq_scaled_C' n K hK hnK]
  simp only [map_pow, map_mul, MvPolynomial.C_pow]
  ring

/-- v_2(cont(H)) = 2d + v_2(cont(G'^2 - A'C')). -/
private lemma v2_H_eq (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hprim_ne : mvContent (G' n ^ 2 - A' n K * C' n K) ≠ 0) :
    padicValNat 2 (mvContent (H_poly n)) =
      2 * d n + padicValNat 2 (mvContent (G' n ^ 2 - A' n K * C' n K)) := by
  rw [H_eq_scaled n K hK hnK, mvContent_C_mul]
  rw [padicValNat.mul (by positivity) hprim_ne]
  congr 1
  simp only [Int.natAbs_pow, Int.natAbs_ofNat']
  rw [padicValNat.pow 2 (by positivity)]
  simp [padicValNat.self]

/-! ## Step 6.2 -- Off-centre divisibility

  Uses central dominance: scalar_AB_central_min gives
  v_2(scalar_AB(n,i)) > v_2(scalar_AB(n,n)) = d for i != n.
  These results depend on the G-coefficient analysis from P2Step5. -/

/-- v_2(scalar_AB(n,n)) = d.
    From P2Step5: v₂(cont(G_poly_loc)) = v₂(scalar_AB(n,n)), and G_poly = G_poly_loc. -/
private lemma v2_scalar_AB_center_eq_d (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K) :
    padicValNat 2 (scalar_AB n n) = d n := by
  unfold d; rw [G_poly_eq_G_poly_loc]
  have hn_pos : 1 ≤ n := by rcases K, hK with ⟨_ | _ | K, hK⟩ <;> omega
  exact (v2_content_G_eq_scalar_AB n K hK hnK (mvContent_G_poly_loc_ne n hn_pos)).symm

/-- Off-centre G' coefficients are divisible by 2.
    Uses B_sharp_even_p2 from CoeffCongP2. -/
private lemma G'_offcenter_even (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hn : 2 ≤ n) (m : ℕ →₀ ℕ)
    (hm : ∀ (j : ℕ), j ≤ 2 * n → j = n →
      m ≠ Finsupp.single j 1 + Finsupp.single (2 * n + 1 - j) 1) :
    (2 : ℤ) ∣ (G' n).coeff m := by
  -- G'(m) = G(m) / 2^d = (B(m)/2) / 2^d.
  -- B_sharp_even_p2 gives: 2 | B(m) / 2^(e+1) for off-centre m.
  -- Since e = d, this means 2^(e+2) | B(m), so 2^(e+1) | B(m)/2, so 2 | (B(m)/2)/2^e.
  rw [G'_coeff, G_poly_coeff]
  have hd_eq_e : d n = e_central 2 n := by
    have h := v2_scalar_AB_center_eq_d n K hK hnK
    rw [e_central_eq 2 n]; exact h.symm
  have hm_ne : m ≠ Finsupp.single n 1 + Finsupp.single (n + 1) 1 := by
    intro heq
    exact hm n (by omega) rfl (by rw [show 2 * n + 1 - n = n + 1 from by omega]; exact heq)
  have hB_sharp := B_sharp_even_p2 K (by omega) n hnK (by omega) m hm_ne
  -- hB_sharp : (2 : ℤ) ∣ (B_n n).coeff m / ↑(2 ^ (e_central 2 n + 1))
  -- This means: 2^(e+2) | B(m), hence 2^(d+2) | B(m)
  -- So 2^(d+1) | B(m)/2 and 2 | (B(m)/2)/2^d
  set e := e_central 2 n with he_def
  set Bm := (B_n n).coeff m with hBm_def
  -- From B_sharp: 2 | Bm / 2^(e+1)
  -- We need: 2 | (Bm / 2) / 2^d, where d = e
  rw [hd_eq_e]
  -- Need: 2 | (Bm / 2) / (2^e : ℤ)
  -- From hB_sharp: 2 | Bm / (2^(e+1) : ℕ)
  -- Note: (2^(e+1) : ℕ : ℤ) = 2 * 2^e, and (Bm / 2) / 2^e = Bm / (2 * 2^e) = Bm / 2^(e+1)
  -- when 2 | Bm (which we know since two_dvd_B_coeff).
  have h_2_dvd_B : (2 : ℤ) ∣ Bm := two_dvd_B_coeff n (by omega) m
  -- Bm / 2 / (2^e : ℤ) = Bm / (2 * 2^e) = Bm / 2^(e+1)
  -- when 2 | Bm
  obtain ⟨q, hq⟩ := h_2_dvd_B
  rw [hq, show (2 : ℤ) * q / 2 = q from Int.mul_ediv_cancel_left q (by norm_num)]
  -- Now need: 2 | q / (2^e : ℤ)
  -- hB_sharp: 2 | Bm / ((2^(e+1) : ℕ) : ℤ)
  -- Bm / ((2^(e+1) : ℕ) : ℤ) = 2*q / (2 * 2^e) = q / 2^e (when 2^e | q... need more care)
  -- Actually Bm / ((2^(e+1) : ℕ) : ℤ) = (2*q) / (2^(e+1)) = (2*q) / (2 * 2^e) = q / 2^e
  -- since 2^(e+1) | 2*q iff 2^e | q
  -- We know 2^(e+1) | Bm = 2*q from the B_n divisibility
  -- From coeff_B_n_dvd: B coefficients divisible by 2^(e+1) when all b_formula have v₂ ≥ e+1
  -- Actually, let's just convert the statement
  have h_cast : ((2 ^ (e + 1) : ℕ) : ℤ) = 2 * (2 ^ e : ℤ) := by push_cast; ring
  rw [hq, h_cast, show (2 : ℤ) * q / (2 * (2 ^ e : ℤ)) = q / (2 ^ e : ℤ) from
    Int.mul_ediv_mul_of_pos q (2 ^ e : ℤ) (by norm_num)] at hB_sharp
  exact hB_sharp

/-- Off-centre A' coefficients have v_2 >= 2.
    Proof sketch: A_n = Σ_{i=0}^{2n} (-1)^i scalar_AB(n,i) X_i X_{2n-i}.
    For off-centre m ≠ single n + single n, only terms with i ≠ n contribute.
    Terms pair up via i ↔ 2n-i: scalar_AB(n,i) = scalar_AB(n,2n-i) and
    (-1)^i = (-1)^(2n-i), so each pair contributes 2·(-1)^i·scalar_AB(n,i).
    Since v₂(scalar_AB(n,i)) ≥ e+1 for i ≠ n (scalar_AB_central_min), and
    d = e, each pair gives 2^(e+2) | 2·scalar_AB(n,i), hence 4 | A'(m).
    Missing: formalization of the involutive pairing argument for A_n coefficients. -/
private lemma A'_offcenter_even2 (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hn : 2 ≤ n) (m : ℕ →₀ ℕ)
    (hm : m ≠ Finsupp.single n 1 + Finsupp.single n 1) :
    (4 : ℤ) ∣ (A' n K).coeff m := by
  rw [A'_coeff]
  have hd_eq_e : d n = e_central 2 n := by
    rw [e_central_eq 2 n]; exact (v2_scalar_AB_center_eq_d n K hK hnK).symm
  set c := fun i => (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) * (β n i : ℤ)
  -- Suffices: 2^(d+2) | A_n.coeff m.
  suffices h_strong : ((2 ^ (d n + 2) : ℕ) : ℤ) ∣ (A_n n).coeff m by
    have h2d_pos : (0 : ℤ) < 2 ^ d n := by positivity
    have h2d_ne : (2 ^ d n : ℤ) ≠ 0 := ne_of_gt h2d_pos
    -- 2^(d+2) | A_n.coeff m, so A_n.coeff m = 2^(d+2) * q = 2^d * 4 * q.
    -- A_n.coeff m / 2^d = 4*q, hence 4 | that.
    have h_dvd_d : (↑(2 ^ d n) : ℤ) ∣ (A_n n).coeff m :=
      dvd_trans (by exact_mod_cast pow_dvd_pow 2 (by omega : d n ≤ d n + 2)) h_strong
    obtain ⟨q, hq⟩ := h_dvd_d
    rw [hq, Int.mul_ediv_cancel_left _ h2d_ne]
    -- Now show 4 | q. Since 2^(d+2) | 2^d * q, we get 4 | q.
    rw [hq] at h_strong
    have : ((2 ^ (d n + 2) : ℕ) : ℤ) = (2 ^ d n : ℤ) * 4 := by push_cast; ring
    rw [this] at h_strong
    exact (mul_dvd_mul_iff_left h2d_ne).mp h_strong
  -- Split A_n at centre i=n.
  have hn_mem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  have h_split : (A_n n).coeff m =
      (MvPolynomial.C (c n) * MvPolynomial.X n * MvPolynomial.X (2 * n - n) :
        MvPolynomial ℕ ℤ).coeff m +
      ∑ i ∈ (Finset.range (2 * n + 1)).erase n,
        (MvPolynomial.C (c i) * MvPolynomial.X i * MvPolynomial.X (2 * n - i) :
          MvPolynomial ℕ ℤ).coeff m := by
    show (A_n n).coeff m = _
    unfold A_n; erw [MvPolynomial.coeff_sum]
    exact (Finset.add_sum_erase _ _ hn_mem).symm
  have h_center_zero :
      (MvPolynomial.C (c n) * MvPolynomial.X n * MvPolynomial.X (2 * n - n) :
        MvPolynomial ℕ ℤ).coeff m = 0 := by
    rw [coeff_C_mul_X_mul_X, if_neg]
    rwa [show 2 * n - n = n from by omega]
  rw [h_split, h_center_zero, zero_add]
  -- Each off-centre scalar has 2^(d+1) | c(i).
  have h_scalar_dvd : ∀ i ∈ (Finset.range (2 * n + 1)).erase n,
      ((2 ^ (d n + 1) : ℕ) : ℤ) ∣ c i := by
    intro i hi
    have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
    have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
    have h_vp : padicValNat 2 (scalar_AB n i) > d n := by
      rw [hd_eq_e, e_central_eq 2 n]
      exact scalar_AB_central_min 2 K (by omega) n hnK i hi_le hi_ne
    have h_pos : 0 < scalar_AB n i := by rw [scalar_AB_formula n i hi_le]; positivity
    have h_dvd_nat : 2 ^ (d n + 1) ∣ scalar_AB n i :=
      (padicValNat_dvd_iff_le h_pos.ne').mpr h_vp
    have : c i = (-1 : ℤ) ^ i * ↑(scalar_AB n i) := by simp [c, scalar_AB]; push_cast; ring
    rw [this]; exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr h_dvd_nat) _
  -- Rewrite sum coefficients and apply involution.
  rw [show ((2 ^ (d n + 2) : ℕ) : ℤ) = 2 * ((2 ^ (d n + 1) : ℕ) : ℤ) from by push_cast; ring]
  have h_coeff_eq :
      (∑ i ∈ (Finset.range (2 * n + 1)).erase n,
        (MvPolynomial.C (c i) * MvPolynomial.X i * MvPolynomial.X (2 * n - i) :
          MvPolynomial ℕ ℤ).coeff m) =
      ∑ i ∈ (Finset.range (2 * n + 1)).erase n,
        (if m = Finsupp.single i 1 + Finsupp.single (2 * n - i) 1 then c i else 0) := by
    congr 1; ext i; exact coeff_C_mul_X_mul_X _ _ _ _
  rw [h_coeff_eq]
  apply dvd_sum_involution (g := fun i => 2 * n - i)
  · intro i hi
    have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
    have hi_lt : i < 2 * n + 1 := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  · intro i hi
    have hi_lt : i < 2 * n + 1 := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
    omega
  · intro i hi hne
    have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
    have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
    by_cases h1 : m = Finsupp.single i 1 + Finsupp.single (2 * n - i) 1
    · have h2 : m = Finsupp.single (2 * n - i) 1 + Finsupp.single (2 * n - (2 * n - i)) 1 := by
        rw [h1, show 2 * n - (2 * n - i) = i from by omega, add_comm]
      rw [if_pos h1, if_pos h2]
      -- Goal: (2 * 2^(d+1)) | (c i + c(2n-i)).
      obtain ⟨q, hq⟩ := h_scalar_dvd i hi
      -- c i = 2^(d+1) * q, and c(2n-i) = c i, so sum = 2 * 2^(d+1) * q.
      suffices h_symm : c i = c (2 * n - i) by
        refine ⟨q, ?_⟩; linarith
      simp only [c]
      have h_neg1 : (-1 : ℤ) ^ (2 * n - i) = (-1 : ℤ) ^ i := by
        apply mul_right_cancel₀ (pow_ne_zero i (by norm_num : (-1 : ℤ) ≠ 0))
        rw [← pow_add, show 2 * n - i + i = 2 * n from Nat.sub_add_cancel hi_le,
            ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, pow_mul, neg_one_sq, one_pow]
      have h_sc : (scalar_AB n i : ℤ) = (scalar_AB n (2 * n - i) : ℤ) := by
        exact_mod_cast alpha_beta_symm n i hi_le
      have : (-1 : ℤ) ^ i * ↑(scalar_AB n i) =
             (-1 : ℤ) ^ (2 * n - i) * ↑(scalar_AB n (2 * n - i)) := by rw [h_neg1, h_sc]
      simp only [scalar_AB] at this; push_cast [Nat.cast_mul] at this ⊢; linarith
    · by_cases h2 : m = Finsupp.single (2 * n - i) 1 + Finsupp.single (2 * n - (2 * n - i)) 1
      · exfalso; apply h1; rw [h2, show 2 * n - (2 * n - i) = i from by omega, add_comm]
      · simp [h1, h2]
  · intro i hi hfix
    have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
    have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
    exfalso; exact hi_ne (by omega)

/-- Off-centre C' coefficients have v_2 >= 2.
    Same involutive pairing argument as A'_offcenter_even2, applied to C_n. -/
private lemma C'_offcenter_even2 (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hn : 2 ≤ n) (m : ℕ →₀ ℕ)
    (hm : m ≠ Finsupp.single (n + 1) 1 + Finsupp.single (n + 1) 1) :
    (4 : ℤ) ∣ (C' n K).coeff m := by
  rw [C'_coeff]
  have hd_eq_e : d n = e_central 2 n := by
    rw [e_central_eq 2 n]; exact (v2_scalar_AB_center_eq_d n K hK hnK).symm
  set c := fun i => (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) * (β n i : ℤ)
  suffices h_strong : ((2 ^ (d n + 2) : ℕ) : ℤ) ∣ (C_n n).coeff m by
    have h2d_pos : (0 : ℤ) < 2 ^ d n := by positivity
    have h2d_ne : (2 ^ d n : ℤ) ≠ 0 := ne_of_gt h2d_pos
    have h_dvd_d : (↑(2 ^ d n) : ℤ) ∣ (C_n n).coeff m :=
      dvd_trans (by exact_mod_cast pow_dvd_pow 2 (by omega : d n ≤ d n + 2)) h_strong
    obtain ⟨q, hq⟩ := h_dvd_d
    rw [hq, Int.mul_ediv_cancel_left _ h2d_ne]
    rw [hq] at h_strong
    have : ((2 ^ (d n + 2) : ℕ) : ℤ) = (2 ^ d n : ℤ) * 4 := by push_cast; ring
    rw [this] at h_strong
    exact (mul_dvd_mul_iff_left h2d_ne).mp h_strong
  have hn_mem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  have h_split : (C_n n).coeff m =
      (MvPolynomial.C (c n) * MvPolynomial.X (n + 1) * MvPolynomial.X (2 * n + 1 - n) :
        MvPolynomial ℕ ℤ).coeff m +
      ∑ i ∈ (Finset.range (2 * n + 1)).erase n,
        (MvPolynomial.C (c i) * MvPolynomial.X (i + 1) * MvPolynomial.X (2 * n + 1 - i) :
          MvPolynomial ℕ ℤ).coeff m := by
    show (C_n n).coeff m = _
    unfold C_n; erw [MvPolynomial.coeff_sum]
    exact (Finset.add_sum_erase _ _ hn_mem).symm
  have h_center_zero :
      (MvPolynomial.C (c n) * MvPolynomial.X (n + 1) * MvPolynomial.X (2 * n + 1 - n) :
        MvPolynomial ℕ ℤ).coeff m = 0 := by
    rw [coeff_C_mul_X_mul_X, if_neg]
    rwa [show 2 * n + 1 - n = n + 1 from by omega]
  rw [h_split, h_center_zero, zero_add]
  have h_scalar_dvd : ∀ i ∈ (Finset.range (2 * n + 1)).erase n,
      ((2 ^ (d n + 1) : ℕ) : ℤ) ∣ c i := by
    intro i hi
    have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
    have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
    have h_vp : padicValNat 2 (scalar_AB n i) > d n := by
      rw [hd_eq_e, e_central_eq 2 n]
      exact scalar_AB_central_min 2 K (by omega) n hnK i hi_le hi_ne
    have h_pos : 0 < scalar_AB n i := by rw [scalar_AB_formula n i hi_le]; positivity
    have h_dvd_nat : 2 ^ (d n + 1) ∣ scalar_AB n i :=
      (padicValNat_dvd_iff_le h_pos.ne').mpr h_vp
    have : c i = (-1 : ℤ) ^ i * ↑(scalar_AB n i) := by simp [c, scalar_AB]; push_cast; ring
    rw [this]; exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr h_dvd_nat) _
  rw [show ((2 ^ (d n + 2) : ℕ) : ℤ) = 2 * ((2 ^ (d n + 1) : ℕ) : ℤ) from by push_cast; ring]
  have h_coeff_eq :
      (∑ i ∈ (Finset.range (2 * n + 1)).erase n,
        (MvPolynomial.C (c i) * MvPolynomial.X (i + 1) * MvPolynomial.X (2 * n + 1 - i) :
          MvPolynomial ℕ ℤ).coeff m) =
      ∑ i ∈ (Finset.range (2 * n + 1)).erase n,
        (if m = Finsupp.single (i + 1) 1 + Finsupp.single (2 * n + 1 - i) 1 then c i else 0) := by
    congr 1; ext i; exact coeff_C_mul_X_mul_X _ _ _ _
  rw [h_coeff_eq]
  apply dvd_sum_involution (g := fun i => 2 * n - i)
  · intro i hi
    have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
    have hi_lt : i < 2 * n + 1 := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  · intro i hi
    have hi_lt : i < 2 * n + 1 := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
    omega
  · intro i hi hne
    have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
    have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
    by_cases h1 : m = Finsupp.single (i + 1) 1 + Finsupp.single (2 * n + 1 - i) 1
    · have h2 : m = Finsupp.single (2 * n - i + 1) 1 + Finsupp.single (2 * n + 1 - (2 * n - i)) 1 := by
        rw [h1, show 2 * n + 1 - (2 * n - i) = i + 1 from by omega,
            show 2 * n - i + 1 = 2 * n + 1 - i from by omega, add_comm]
      rw [if_pos h1, if_pos h2]
      obtain ⟨q, hq⟩ := h_scalar_dvd i hi
      suffices h_symm : c i = c (2 * n - i) by refine ⟨q, ?_⟩; linarith
      simp only [c]
      have h_neg1 : (-1 : ℤ) ^ (2 * n - i) = (-1 : ℤ) ^ i := by
        apply mul_right_cancel₀ (pow_ne_zero i (by norm_num : (-1 : ℤ) ≠ 0))
        rw [← pow_add, show 2 * n - i + i = 2 * n from Nat.sub_add_cancel hi_le,
            ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, pow_mul, neg_one_sq, one_pow]
      have h_sc : (scalar_AB n i : ℤ) = (scalar_AB n (2 * n - i) : ℤ) := by
        exact_mod_cast alpha_beta_symm n i hi_le
      have : (-1 : ℤ) ^ i * ↑(scalar_AB n i) =
             (-1 : ℤ) ^ (2 * n - i) * ↑(scalar_AB n (2 * n - i)) := by rw [h_neg1, h_sc]
      simp only [scalar_AB] at this; push_cast [Nat.cast_mul] at this ⊢; linarith
    · by_cases h2 : m = Finsupp.single (2 * n - i + 1) 1 + Finsupp.single (2 * n + 1 - (2 * n - i)) 1
      · exfalso; apply h1; rw [h2, show 2 * n + 1 - (2 * n - i) = i + 1 from by omega,
            show 2 * n - i + 1 = 2 * n + 1 - i from by omega, add_comm]
      · simp [h1, h2]
  · intro i hi hfix
    have hi_ne : i ≠ n := (Finset.mem_erase.mp hi).1
    have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
    exfalso; exact hi_ne (by omega)

/-- Centre coefficient of G' is odd.
    G'(centre) = G(centre)/2^d. The centre G coefficient is b_formula(n,n)/2,
    and v₂(b_formula(n,n)) = 1 + d (from v2_b_center), so v₂(G(centre)) = d.
    Hence G'(centre) is odd.
    Missing: computing the exact monomial for the B_n centre coefficient and
    showing it matches single n + single (n+1). -/
private lemma G'_center_odd (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hn : 2 ≤ n) (hG_ne : G_poly n ≠ 0) :
    ¬(2 : ℤ) ∣ (G' n).coeff (Finsupp.single n 1 + Finsupp.single (n + 1) 1) := by
  -- Proof by contradiction using content.
  -- If 2 | centre coeff, then 2 | all G' coeffs (off-centre already even).
  -- Then 2 | mvContent(G'). But mvContent(G_poly) = 2^d * mvContent(G'),
  -- and v₂(mvContent(G_poly)) = d, so v₂(mvContent(G')) = 0. Contradiction.
  intro h_even
  -- All G' coefficients are even.
  have h_all_even : ∀ m, (2 : ℤ) ∣ (G' n).coeff m := by
    intro m
    by_cases hm : ∀ (j : ℕ), j ≤ 2 * n → j = n →
        m ≠ Finsupp.single j 1 + Finsupp.single (2 * n + 1 - j) 1
    · exact G'_offcenter_even n K hK hnK hn m hm
    · push_neg at hm
      obtain ⟨j, hj_le, hj_eq, hm_eq⟩ := hm
      rw [hj_eq] at hm_eq
      rw [show 2 * n + 1 - n = n + 1 from by omega] at hm_eq
      rw [hm_eq]; exact h_even
  -- 2 | mvContent(G')
  have h_two_dvd_content : 2 ∣ mvContent (G' n) := by
    unfold mvContent
    apply Finset.dvd_gcd
    intro m _
    exact Int.natAbs_dvd_natAbs.mpr (h_all_even m)
  -- mvContent(G_poly) = 2^d * mvContent(G')
  have h_content_eq : mvContent (G_poly n) = 2 ^ d n * mvContent (G' n) := by
    rw [G_eq_scaled_G' n, mvContent_C_mul]; simp [Int.natAbs_pow, Int.natAbs_ofNat']
  -- v₂(mvContent(G_poly)) = d
  -- So v₂(2^d * mvContent(G')) = d
  -- v₂(2^d) = d, v₂(mvContent(G')) ≥ 1 since 2 | mvContent(G')
  -- v₂(2^d * mvContent(G')) = d + v₂(mvContent(G')) ≥ d + 1 > d. Contradiction.
  have hG'_ne : G' n ≠ 0 := by
    intro h0
    apply hG_ne
    rw [G_eq_scaled_G' n, h0, mul_zero]
  have hcont_G'_ne : mvContent (G' n) ≠ 0 := by
    intro h0
    apply hG'_ne
    ext m
    have := mvContent_dvd_coeff (G' n) m
    rw [h0, Nat.cast_zero, zero_dvd_iff] at this
    exact this
  have h_v2_d : padicValNat 2 (mvContent (G_poly n)) = d n := rfl
  rw [h_content_eq, padicValNat.mul (by positivity) hcont_G'_ne,
      padicValNat.pow (d n) (by norm_num : (2 : ℕ) ≠ 0),
      padicValNat.self (by norm_num : 1 < 2)] at h_v2_d
  have h_v2_ge : 1 ≤ padicValNat 2 (mvContent (G' n)) :=
    (padicValNat_dvd_iff_le hcont_G'_ne).mp h_two_dvd_content
  omega

/-- Centre coefficient of A' is odd.
    A'(centre) = A(centre)/2^d. The centre A coefficient is (-1)^n * scalar_AB(n,n),
    and v₂(scalar_AB(n,n)) = e = d. So A'(centre) = (-1)^n * scalar_AB(n,n)/2^d is odd.
    Missing: extracting scalar_AB(n,n)/2^e as odd via p_pow_dvd_scalar_AB. -/
private lemma A'_center_odd (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hn : 2 ≤ n) :
    ¬(2 : ℤ) ∣ (A' n K).coeff (Finsupp.single n 1 + Finsupp.single n 1) := by
  -- Proof by contradiction using content.
  -- If 2 | centre coeff, then together with A'_offcenter_even2 (which gives 4 | off-centre,
  -- hence 2 | off-centre), we'd get 2 | all A' coeffs, so 2 | mvContent(A').
  -- But A_n = C(2^d) * A', so mvContent(A_n) = 2^d * mvContent(A'),
  -- and v₂(mvContent(A_n)) = d, so v₂(mvContent(A')) = 0. Contradiction.
  intro h_even
  have h_all_even : ∀ m, (2 : ℤ) ∣ (A' n K).coeff m := by
    intro m
    by_cases hm : m = Finsupp.single n 1 + Finsupp.single n 1
    · rw [hm]; exact h_even
    · exact dvd_trans (dvd_of_eq (by norm_num : (2 : ℤ) = 2)) -- 2 | 4 | A'.coeff m
        (dvd_trans (show (2 : ℤ) ∣ 4 from ⟨2, by ring⟩) (A'_offcenter_even2 n K hK hnK hn m hm))
  have h_two_dvd_content : 2 ∣ mvContent (A' n K) := by
    unfold mvContent
    apply Finset.dvd_gcd
    intro m _
    exact Int.natAbs_dvd_natAbs.mpr (h_all_even m)
  have h_content_eq : mvContent (A_n n) = 2 ^ d n * mvContent (A' n K) := by
    rw [A_eq_scaled_A' n K hK hnK, mvContent_C_mul]; simp [Int.natAbs_pow, Int.natAbs_ofNat']
  have hn_pos : 1 ≤ n := by omega
  have hA_ne : mvContent (A_n n) ≠ 0 := mvContent_A_ne n hn_pos
  have hA'_ne : A' n K ≠ 0 := by
    intro h0
    apply hA_ne
    rw [h_content_eq, show A' n K = 0 from h0]
    simp [mvContent]
  have hcont_A'_ne : mvContent (A' n K) ≠ 0 := by
    intro h0; apply hA'_ne; ext m
    have := mvContent_dvd_coeff (A' n K) m
    rw [h0, Nat.cast_zero, zero_dvd_iff] at this; exact this
  have h_v2_A := v2_content_A_eq_d n K hK hnK
  rw [h_content_eq, padicValNat.mul (by positivity) hcont_A'_ne,
      padicValNat.pow (d n) (by norm_num : (2 : ℕ) ≠ 0),
      padicValNat.self (by norm_num : 1 < 2)] at h_v2_A
  have h_v2_ge : 1 ≤ padicValNat 2 (mvContent (A' n K)) :=
    (padicValNat_dvd_iff_le hcont_A'_ne).mp h_two_dvd_content
  omega

/-! ## Step 6.3 -- Frobenius over F_2

  Over F_2, only centre monomials survive in G', A', C'.
  G'^2 = f_n^2 f_{n+1}^2 = A'C' (mod 2).

  This follows from the off-centre divisibility results of Step 6.2.
  PLACEHOLDER: from P2Step5 (depends on 6.2). -/

/-- G'^2 - A'C' = 0 (mod 2): every coefficient is even.
    Follows from the off-centre divisibility results of Step 6.2:
    Over F₂, G' ≡ g·X_n·X_{n+1}, A' ≡ a·X_n², C' ≡ a·X_{n+1}² (mod 2).
    So G'² ≡ g²·X_n²·X_{n+1}² ≡ A'C' (mod 2) since g² ≡ a² ≡ 1 (mod 2). -/
private lemma two_dvd_prim_diff (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K) (hn : 2 ≤ n) :
    ∀ m, (2 : ℤ) ∣ (G' n ^ 2 - A' n K * C' n K).coeff m := by
  -- Write G' = G'_c + G'_r where G'_c is centre monomial, G'_r has all even coeffs.
  -- Define centre monomials.
  set g := (G' n).coeff (Finsupp.single n 1 + Finsupp.single (n + 1) 1)
  set a := (A' n K).coeff (Finsupp.single n 1 + Finsupp.single n 1)
  set c_val := (C' n K).coeff (Finsupp.single (n + 1) 1 + Finsupp.single (n + 1) 1)
  -- Define centre polynomials.
  set G_c := MvPolynomial.C g * MvPolynomial.X n * MvPolynomial.X (n + 1) with hGc_def
  set A_c := MvPolynomial.C a * MvPolynomial.X n * MvPolynomial.X n with hAc_def
  set C_c := MvPolynomial.C c_val * MvPolynomial.X (n + 1) * MvPolynomial.X (n + 1) with hCc_def
  -- Define remainders.
  set G_r := G' n - G_c with hGr_def
  set A_r := A' n K - A_c with hAr_def
  set C_r := C' n K - C_c with hCr_def
  -- All coefficients of G_r are even.
  have hGr_even : ∀ m, (2 : ℤ) ∣ G_r.coeff m := by
    intro m; show (2 : ℤ) ∣ (G' n - G_c).coeff m
    rw [MvPolynomial.coeff_sub, hGc_def, coeff_C_mul_X_mul_X]
    by_cases hm : m = Finsupp.single n 1 + Finsupp.single (n + 1) 1
    · rw [if_pos hm, hm, sub_self]; exact dvd_zero _
    · rw [if_neg hm, sub_zero]
      exact G'_offcenter_even n K hK hnK hn m (by
        intro j hj hj_eq; rw [hj_eq, show 2 * n + 1 - n = n + 1 from by omega]; exact hm)
  have hAr_even : ∀ m, (2 : ℤ) ∣ A_r.coeff m := by
    intro m; show (2 : ℤ) ∣ (A' n K - A_c).coeff m
    rw [MvPolynomial.coeff_sub, hAc_def, coeff_C_mul_X_mul_X]
    by_cases hm : m = Finsupp.single n 1 + Finsupp.single n 1
    · rw [if_pos hm, hm, sub_self]; exact dvd_zero _
    · rw [if_neg hm, sub_zero]
      exact dvd_trans ⟨2, by ring⟩ (A'_offcenter_even2 n K hK hnK hn m hm)
  have hCr_even : ∀ m, (2 : ℤ) ∣ C_r.coeff m := by
    intro m; show (2 : ℤ) ∣ (C' n K - C_c).coeff m
    rw [MvPolynomial.coeff_sub, hCc_def, coeff_C_mul_X_mul_X]
    by_cases hm : m = Finsupp.single (n + 1) 1 + Finsupp.single (n + 1) 1
    · rw [if_pos hm, hm, sub_self]; exact dvd_zero _
    · rw [if_neg hm, sub_zero]
      exact dvd_trans ⟨2, by ring⟩ (C'_offcenter_even2 n K hK hnK hn m hm)
  -- G' = G_c + G_r, A' = A_c + A_r, C' = C_c + C_r
  have hG_split : G' n = G_c + G_r := by rw [hGr_def]; ring
  have hA_split : A' n K = A_c + A_r := by rw [hAr_def]; ring
  have hC_split : C' n K = C_c + C_r := by rw [hCr_def]; ring
  -- G'^2 - A'C' = (G_c + G_r)^2 - (A_c + A_r)(C_c + C_r)
  --             = G_c^2 - A_c*C_c + (2*G_c*G_r + G_r^2 - A_c*C_r - A_r*C_c - A_r*C_r)
  -- The second group has all even coefficients (each term has at least one even-coeff factor).
  -- For G_c^2 - A_c*C_c: this is (g^2 - a*c_val) * X_n^2 * X_{n+1}^2.
  -- g,a are odd, and by symmetry a = c_val (well, they might not be equal, but both odd).
  -- g^2, a*c_val are both odd, so g^2 - a*c_val is even.
  intro m
  rw [hG_split, hA_split, hC_split]
  -- Expand: (G_c + G_r)^2 - (A_c + A_r)*(C_c + C_r) =
  --   G_c^2 + 2*G_c*G_r + G_r^2 - A_c*C_c - A_c*C_r - A_r*C_c - A_r*C_r
  have h_expand : (G_c + G_r) ^ 2 - (A_c + A_r) * (C_c + C_r) =
      (G_c ^ 2 - A_c * C_c) + (2 * G_c * G_r + G_r ^ 2 - A_c * C_r - A_r * C_c - A_r * C_r) := by
    ring
  rw [h_expand, MvPolynomial.coeff_add]
  apply dvd_add
  · -- G_c^2 - A_c*C_c = (g^2 - a*c_val) * X_n^2 * X_{n+1}^2
    -- g^2 - a*c_val is even since g,a,c_val have the same parity (odd).
    have h_sq_eq : G_c ^ 2 - A_c * C_c =
        MvPolynomial.C (g ^ 2 - a * c_val) *
          (MvPolynomial.X n * MvPolynomial.X n * (MvPolynomial.X (n + 1) * MvPolynomial.X (n + 1))) := by
      simp only [hGc_def, hAc_def, hCc_def, map_sub, map_pow, map_mul]; ring
    rw [h_sq_eq, MvPolynomial.coeff_C_mul]
    -- g^2 - a*c_val is even: g,a,c_val are all odd.
    -- g^2 ≡ 1 mod 2, a*c_val ≡ 1 mod 2 (odd*odd = odd), so diff is even.
    have hG_ne : G_poly n ≠ 0 := by
      intro h0
      have : mvContent (G_poly n) = 0 := by rw [h0]; simp [mvContent]
      exact mvContent_G_poly_loc_ne n (by omega) (G_poly_eq_G_poly_loc n ▸ this)
    have hg_odd := G'_center_odd n K hK hnK hn hG_ne
    have ha_odd := A'_center_odd n K hK hnK hn
    -- Need c_val odd. By content_A_eq_C and the same argument as A'_center_odd.
    -- Actually, A' and C' have the same content (since A_n and C_n do),
    -- so if 2 | c_val, same contradiction as A'_center_odd.
    -- For now, let's show c_val is odd directly.
    have hc_odd : ¬(2 : ℤ) ∣ c_val := by
      -- Same proof as A'_center_odd but for C'.
      intro h_even_c
      have h_all_even_C : ∀ m, (2 : ℤ) ∣ (C' n K).coeff m := by
        intro m
        by_cases hm : m = Finsupp.single (n + 1) 1 + Finsupp.single (n + 1) 1
        · rw [hm]; exact h_even_c
        · exact dvd_trans ⟨2, by ring⟩ (C'_offcenter_even2 n K hK hnK hn m hm)
      have h_two_dvd_C_content : 2 ∣ mvContent (C' n K) := by
        unfold mvContent
        apply Finset.dvd_gcd
        intro m _
        exact Int.natAbs_dvd_natAbs.mpr (h_all_even_C m)
      have h_content_C_eq : mvContent (C_n n) = 2 ^ d n * mvContent (C' n K) := by
        rw [C_eq_scaled_C' n K hK hnK, mvContent_C_mul]; simp [Int.natAbs_pow, Int.natAbs_ofNat']
      have hC'_ne : C' n K ≠ 0 := by
        intro h0
        have hC_zero : C_n n = 0 := by rw [C_eq_scaled_C' n K hK hnK, h0, mul_zero]
        have : mvContent (C_n n) = 0 := by rw [hC_zero]; simp [mvContent]
        rw [← content_A_eq_C] at this
        exact mvContent_A_ne n (by omega) this
      have hcont_C'_ne : mvContent (C' n K) ≠ 0 := by
        intro h0; apply hC'_ne; ext m
        have := mvContent_dvd_coeff (C' n K) m
        rw [h0, Nat.cast_zero, zero_dvd_iff] at this; exact this
      have h_v2_C : padicValNat 2 (mvContent (C_n n)) = d n := by
        rw [← content_A_eq_C]; exact v2_content_A_eq_d n K hK hnK
      rw [h_content_C_eq, padicValNat.mul (by positivity) hcont_C'_ne,
          padicValNat.pow (d n) (by norm_num : (2 : ℕ) ≠ 0),
          padicValNat.self (by norm_num : 1 < 2)] at h_v2_C
      have h_v2_ge : 1 ≤ padicValNat 2 (mvContent (C' n K)) :=
        (padicValNat_dvd_iff_le hcont_C'_ne).mp h_two_dvd_C_content
      omega
    -- g^2 - a*c_val: g,a,c_val odd implies g^2 ≡ a*c_val ≡ 1 (mod 2).
    -- Express g,a,c_val mod 2.
    have hg_mod : g % 2 = 1 ∨ g % 2 = -1 := by
      have : g % 2 ≠ 0 := fun h => hg_odd ⟨g / 2, Int.ediv_add_emod g 2 ▸ by omega⟩
      omega
    have ha_mod : a % 2 = 1 ∨ a % 2 = -1 := by
      have : a % 2 ≠ 0 := fun h => ha_odd ⟨a / 2, Int.ediv_add_emod a 2 ▸ by omega⟩
      omega
    have hc_mod : c_val % 2 = 1 ∨ c_val % 2 = -1 := by
      have : c_val % 2 ≠ 0 := fun h => hc_odd ⟨c_val / 2, Int.ediv_add_emod c_val 2 ▸ by omega⟩
      omega
    have h_diff_even : (2 : ℤ) ∣ (g ^ 2 - a * c_val) := by
      -- g,a,c_val all odd. Write g = 2k+1, a = 2l+1, c_val = 2m+1.
      -- g^2 = 4k^2+4k+1, a*c_val = 4lm+2l+2m+1.
      -- diff = 4k^2+4k - 4lm - 2l - 2m = 2*(2k^2+2k-2lm-l-m).
      have hg_odd2 : ∃ k, g = 2 * k + 1 := by
        rcases hg_mod with h | h <;> [exact ⟨g / 2, by omega⟩; exact ⟨g / 2 - 1, by omega⟩]
      have ha_odd2 : ∃ k, a = 2 * k + 1 := by
        rcases ha_mod with h | h <;> [exact ⟨a / 2, by omega⟩; exact ⟨a / 2 - 1, by omega⟩]
      have hc_odd2 : ∃ k, c_val = 2 * k + 1 := by
        rcases hc_mod with h | h <;> [exact ⟨c_val / 2, by omega⟩; exact ⟨c_val / 2 - 1, by omega⟩]
      obtain ⟨gk, hgk⟩ := hg_odd2
      obtain ⟨ak, hak⟩ := ha_odd2
      obtain ⟨ck, hck⟩ := hc_odd2
      rw [hgk, hak, hck]
      exact ⟨2 * gk ^ 2 + 2 * gk - 2 * ak * ck - ak - ck, by ring⟩
    exact dvd_mul_of_dvd_left h_diff_even _
  · -- The remainder terms all have even coefficients.
    -- 2*G_c*G_r: G_r has even coefficients, so 2 | each coeff of G_c*G_r, hence 2 | 2*G_c*G_r coeff.
    -- Actually, the explicit factor of 2 suffices.
    -- G_r^2: each coeff is Σ G_r(a)*G_r(b), each G_r(a) is even, so product is divisible by 4, sum by 4.
    -- A_c*C_r: C_r has even coefficients.
    -- A_r*C_c: A_r has even coefficients.
    -- A_r*C_r: both have even coefficients, so product divisible by 4.
    -- Actually, we just need 2 | each term's coefficient.
    have h_remainder :
        2 * G_c * G_r + G_r ^ 2 - A_c * C_r - A_r * C_c - A_r * C_r =
        MvPolynomial.C 2 * (G_c * G_r) + G_r ^ 2 - A_c * C_r - A_r * C_c - A_r * C_r := by
      congr 1; rw [show (2 : MvPolynomial ℕ ℤ) = MvPolynomial.C 2 from by simp [map_ofNat]]; ring
    rw [h_remainder]
    -- Each of these terms has all even coefficients.
    -- Term 1: C(2) * (G_c * G_r) -- explicit factor 2
    -- Term 2: G_r^2 -- product of even-coeff polys
    -- Term 3: A_c * C_r -- C_r has even coeffs
    -- Term 4: A_r * C_c -- A_r has even coeffs
    -- Term 5: A_r * C_r -- both have even coeffs
    -- For the coefficient at m, we compute the sum.
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_add]
    -- Show 2 divides each individual term's coefficient.
    -- Term 1: C(2) * (G_c * G_r)
    have h1 : (2 : ℤ) ∣ (MvPolynomial.C 2 * (G_c * G_r)).coeff m := by
      rw [MvPolynomial.coeff_C_mul]; exact dvd_mul_right 2 _
    -- Term 2: G_r^2
    have h2 : (2 : ℤ) ∣ (G_r ^ 2).coeff m := by
      rw [sq, MvPolynomial.coeff_mul]
      apply Finset.dvd_sum; intro x _
      exact dvd_mul_of_dvd_left (hGr_even _) _
    -- Term 3: A_c * C_r
    have h3 : (2 : ℤ) ∣ (A_c * C_r).coeff m := by
      rw [MvPolynomial.coeff_mul]
      apply Finset.dvd_sum; intro x _
      exact dvd_mul_of_dvd_right (hCr_even _) _
    -- Term 4: A_r * C_c
    have h4 : (2 : ℤ) ∣ (A_r * C_c).coeff m := by
      rw [MvPolynomial.coeff_mul]
      apply Finset.dvd_sum; intro x _
      exact dvd_mul_of_dvd_left (hAr_even _) _
    -- Term 5: A_r * C_r
    have h5 : (2 : ℤ) ∣ (A_r * C_r).coeff m := by
      rw [MvPolynomial.coeff_mul]
      apply Finset.dvd_sum; intro x _
      exact dvd_mul_of_dvd_left (hAr_even _) _
    omega

/-! ## Step 6.4 -- Mod-4 six-term expansion (paper L1393-1415)

  *** DO NOT USE four_dvd_primitive_diff *** (requires g^2=ac which FAILS here)

  Write G' = g*f_n*f_{n+1} + 2*R_G, A' = a*f_n^2 + 2*R_A, C' = a*f_{n+1}^2 + 2*R_C.
  g, a odd. R_A, R_C have even coefficients.
  Expand and show 4 divides every coefficient of G'^2 - A'C'. -/

/-- Helper: if g and a are both odd integers, then 4 divides g^2 - a^2. -/
private lemma odd_sq_diff_div4 (g a : ℤ) (hg : ¬(2 : ℤ) ∣ g) (ha : ¬(2 : ℤ) ∣ a) :
    (4 : ℤ) ∣ (g ^ 2 - a ^ 2) := by
  have hg_odd : g % 2 = 1 ∨ g % 2 = -1 := by
    have : g % 2 ≠ 0 := by intro h; exact hg ⟨g / 2, Int.ediv_add_emod g 2 ▸ by omega⟩
    omega
  have ha_odd : a % 2 = 1 ∨ a % 2 = -1 := by
    have : a % 2 ≠ 0 := by intro h; exact ha ⟨a / 2, Int.ediv_add_emod a 2 ▸ by omega⟩
    omega
  have hga_sub : (2 : ℤ) ∣ (g - a) := by
    have : (g - a) % 2 = 0 := by omega
    exact Int.dvd_of_emod_eq_zero this
  have hga_add : (2 : ℤ) ∣ (g + a) := by
    have : (g + a) % 2 = 0 := by omega
    exact Int.dvd_of_emod_eq_zero this
  have : g ^ 2 - a ^ 2 = (g - a) * (g + a) := by ring
  rw [this, show (4 : ℤ) = 2 * 2 from by norm_num]
  exact mul_dvd_mul hga_sub hga_add

/-- Helper: if 2 divides every coefficient of r, then for any f,
    4 divides every coefficient of 2 * f * r (as MvPolynomials). -/
private lemma four_dvd_two_mul_even_coeff
    (f r : MvPolynomial ℕ ℤ)
    (hr : ∀ m, (2 : ℤ) ∣ r.coeff m)
    (m : ℕ →₀ ℕ) :
    (4 : ℤ) ∣ (MvPolynomial.C 2 * f * r).coeff m := by
  rw [show MvPolynomial.C (2 : ℤ) * f * r = MvPolynomial.C 2 * (f * r) from by ring]
  rw [MvPolynomial.coeff_C_mul]
  rw [show (4 : ℤ) = 2 * 2 from by norm_num]
  apply mul_dvd_mul_left
  rw [MvPolynomial.coeff_mul]
  exact Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right (hr _) _

/-- Main Step 6.4 result: 4 divides every coefficient of G'^2 - A'C'.

  The proof uses the six-term expansion from the paper.
  It depends on the off-centre divisibility and centre parity results
  from Step 6.2, which are PLACEHOLDERs from P2Step5.

  The logical structure is:
  1. From Step 6.3: 2 | every coefficient of G'^2 - A'C'
  2. Write G' = g*mono_G + 2*R_G (centre + 2*remainder)
     Write A' = a*mono_A + 2*R_A
     Write C' = a*mono_C + 2*R_C
  3. Expand G'^2 - A'C' into six terms
  4. Term (i): (g^2-a^2)*mono_G^2 has 4 | g^2-a^2 (odd_sq_diff_div4)
  5. Term (ii): -2a*(mono_A*R_C + R_A*mono_C) -- R_A,R_C have even coeffs, so 4 | this
  6. Term (iii): 4g*mono_G*R_G + 4*R_G^2 - 4*R_A*R_C -- explicit factor 4 -/
private lemma four_dvd_prim_diff (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K) (hn : 2 ≤ n)
    (hG_ne : G_poly n ≠ 0) :
    ∀ m, (4 : ℤ) ∣ (G' n ^ 2 - A' n K * C' n K).coeff m := by
  -- The full six-term expansion proof depends on detailed coefficient
  -- decompositions from Steps 6.2 and 6.3 (PLACEHOLDERs from P2Step5).
  -- Here we set up the logical structure assuming those results.
  --
  -- Let g = centre coeff of G', a = centre coeff of A'.
  -- Define remainder polynomials R_G, R_A, R_C by subtracting the centre term
  -- and dividing by 2.
  --
  -- The key facts we use from P2Step5:
  -- (a) Off-centre G' coeffs divisible by 2 (G'_offcenter_even)
  -- (b) Off-centre A',C' coeffs divisible by 4 (A'_offcenter_even2, C'_offcenter_even2)
  -- (c) Centre G' coeff is odd (G'_center_odd)
  -- (d) Centre A' coeff is odd (A'_center_odd)
  --
  -- The expansion proof:
  -- G' = g*X_n*X_{n+1} + 2*R_G
  -- A' = a*X_n^2 + 2*R_A
  -- C' = a*X_{n+1}^2 + 2*R_C
  --
  -- G'^2 - A'C' = (g^2-a^2)*X_n^2*X_{n+1}^2
  --             - 2a*(X_n^2*R_C + R_A*X_{n+1}^2)
  --             + 4g*X_n*X_{n+1}*R_G + 4*R_G^2 - 4*R_A*R_C
  --
  -- Term (i): 4 | (g^2-a^2) by odd_sq_diff_div4
  -- Term (ii): R_A, R_C have even coeffs, so 2*a*(even) = 0 mod 4
  -- Term (iii): explicit factor 4
  --
  -- Since this decomposition requires the P2Step5 PLACEHOLDERs for the
  -- coefficient structure, we mark the full proof as depending on them.
  -- Use the six-term expansion.
  -- Define centre coefficients and monomials.
  set g := (G' n).coeff (Finsupp.single n 1 + Finsupp.single (n + 1) 1)
  set a := (A' n K).coeff (Finsupp.single n 1 + Finsupp.single n 1)
  set c_val := (C' n K).coeff (Finsupp.single (n + 1) 1 + Finsupp.single (n + 1) 1)
  set G_c := MvPolynomial.C g * MvPolynomial.X n * MvPolynomial.X (n + 1)
  set A_c := MvPolynomial.C a * MvPolynomial.X n * MvPolynomial.X n
  set C_c := MvPolynomial.C c_val * MvPolynomial.X (n + 1) * MvPolynomial.X (n + 1)
  set G_r := G' n - G_c
  set A_r := A' n K - A_c
  set C_r := C' n K - C_c
  -- Key parity facts.
  have hg_odd := G'_center_odd n K hK hnK hn hG_ne
  have ha_odd := A'_center_odd n K hK hnK hn
  -- a = c_val: both equal (-1)^n * scalar_AB(n,n) / 2^d.
  -- A_n and C_n have the same scalars at the centre.
  -- A_n centre coeff = (-1)^n * scalar_AB(n,n) (at single n + single n).
  -- C_n centre coeff = (-1)^n * scalar_AB(n,n) (at single (n+1) + single (n+1)).
  -- So A' and C' centre coefficients are both (-1)^n * scalar_AB(n,n) / 2^d.
  have ha_eq_c : a = c_val := by
    rw [show a = (A' n K).coeff (Finsupp.single n 1 + Finsupp.single n 1) from rfl,
        show c_val = (C' n K).coeff (Finsupp.single (n + 1) 1 + Finsupp.single (n + 1) 1) from rfl,
        A'_coeff, C'_coeff]
    -- A_n.coeff(single n + single n) = Σ c(i) * [single i + single (2n-i) = single n + single n]
    -- Only i=n contributes (since single i + single (2n-i) = single n + single n iff i = n).
    -- Similarly for C_n.
    congr 1
    -- A_n.coeff (single n + single n) = (-1)^n * scalar_AB(n,n)
    -- C_n.coeff (single (n+1) + single (n+1)) = (-1)^n * scalar_AB(n,n)
    -- So they are equal.
    have hA_coeff : (A_n n).coeff (Finsupp.single n 1 + Finsupp.single n 1) =
        (-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) * (α n n : ℤ) * (β n n : ℤ) := by
      unfold A_n; erw [MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single n]
      · rw [coeff_C_mul_X_mul_X, if_pos (by rw [show 2 * n - n = n from by omega])]
      · intro i hi hi_ne
        rw [coeff_C_mul_X_mul_X, if_neg]
        intro h_eq
        -- h_eq : single n + single n = single i + single (2n-i)
        -- This forces i = n (since the LHS has value 2 at n and 0 elsewhere,
        -- while RHS has value 1 at i and 1 at 2n-i for i ≠ n).
        have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        by_cases hin : i = 2 * n - i
        · -- i = 2n-i means i = n, contradiction.
          exact hi_ne (by omega)
        · -- i ≠ 2n-i: single i + single (2n-i) has value 1 at i, 1 at 2n-i.
          -- single n + single n has value 2 at n.
          -- For equality, we need i = n or 2n-i = n. Both give i = n, contradiction.
          have h1 := Finsupp.ext_iff.mp h_eq n
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at h1
          by_cases hi_n : i = n
          · exact hi_ne hi_n
          · simp [hi_n] at h1
            by_cases h2ni_n : 2 * n - i = n
            · exact hi_ne (by omega)
            · simp [h2ni_n] at h1
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    have hC_coeff : (C_n n).coeff (Finsupp.single (n + 1) 1 + Finsupp.single (n + 1) 1) =
        (-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) * (α n n : ℤ) * (β n n : ℤ) := by
      unfold C_n; erw [MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single n]
      · rw [coeff_C_mul_X_mul_X, if_pos (by rw [show 2 * n + 1 - n = n + 1 from by omega])]
      · intro i hi hi_ne
        rw [coeff_C_mul_X_mul_X, if_neg]
        intro h_eq
        have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        -- h_eq : single (n+1) + single (n+1) = single (i+1) + single (2n+1-i)
        -- LHS has value 2 at (n+1), 0 elsewhere.
        -- RHS has value 1 at (i+1) and 1 at (2n+1-i) if i+1 ≠ 2n+1-i, i.e., i ≠ n.
        have h1 := Finsupp.ext_iff.mp h_eq (n + 1)
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at h1
        by_cases hi1 : i + 1 = n + 1
        · exact hi_ne (by omega)
        · -- Both i+1 ≠ n+1 and 2n+1-i ≠ n+1, so both ite evaluate to 0.
          -- h1 : 2 = [n+1=i+1] + [n+1=2n+1-i], but both terms are 0. Contradiction.
          exfalso
          have h_ne1 : n + 1 ≠ i + 1 := by omega
          have h_ne2 : n + 1 ≠ 2 * n + 1 - i := by intro heq; exact hi_ne (by omega)
          -- h_eq says the finsupps are equal. Evaluating at n+1:
          -- LHS: (single (n+1) 1 + single (n+1) 1)(n+1) = 2
          -- RHS: (single (i+1) 1 + single (2n+1-i) 1)(n+1) = 0 + 0 = 0
          have h_lhs : (Finsupp.single (n + 1) 1 + Finsupp.single (n + 1) 1 : ℕ →₀ ℕ) (n + 1) = 2 := by
            simp [Finsupp.single_apply]
          have h1_eval := Finsupp.ext_iff.mp h_eq (n + 1)
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at h1_eval
          split_ifs at h1_eval with h3 h4 <;> omega
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hA_coeff, hC_coeff]
  -- G_r has all even coefficients.
  have hGr_even : ∀ m, (2 : ℤ) ∣ G_r.coeff m := by
    intro m; show (2 : ℤ) ∣ (G' n - G_c).coeff m
    rw [MvPolynomial.coeff_sub, coeff_C_mul_X_mul_X]
    by_cases hm : m = Finsupp.single n 1 + Finsupp.single (n + 1) 1
    · rw [if_pos hm, hm, sub_self]; exact dvd_zero _
    · rw [if_neg hm, sub_zero]
      exact G'_offcenter_even n K hK hnK hn m (by
        intro j hj hj_eq; rw [hj_eq, show 2 * n + 1 - n = n + 1 from by omega]; exact hm)
  have hAr_four : ∀ m, (4 : ℤ) ∣ A_r.coeff m := by
    intro m; show (4 : ℤ) ∣ (A' n K - A_c).coeff m
    rw [MvPolynomial.coeff_sub, coeff_C_mul_X_mul_X]
    by_cases hm : m = Finsupp.single n 1 + Finsupp.single n 1
    · rw [if_pos hm, hm, sub_self]; exact dvd_zero _
    · rw [if_neg hm, sub_zero]; exact A'_offcenter_even2 n K hK hnK hn m hm
  have hCr_four : ∀ m, (4 : ℤ) ∣ C_r.coeff m := by
    intro m; show (4 : ℤ) ∣ (C' n K - C_c).coeff m
    rw [MvPolynomial.coeff_sub, coeff_C_mul_X_mul_X]
    by_cases hm : m = Finsupp.single (n + 1) 1 + Finsupp.single (n + 1) 1
    · rw [if_pos hm, hm, sub_self]; exact dvd_zero _
    · rw [if_neg hm, sub_zero]; exact C'_offcenter_even2 n K hK hnK hn m hm
  -- Now expand.
  intro m
  have hG_split : G' n = G_c + G_r := by show G' n = G_c + (G' n - G_c); ring
  have hA_split : A' n K = A_c + A_r := by show A' n K = A_c + (A' n K - A_c); ring
  have hC_split : C' n K = C_c + C_r := by show C' n K = C_c + (C' n K - C_c); ring
  rw [hG_split, hA_split, hC_split]
  -- Expand (G_c + G_r)^2 - (A_c + A_r)(C_c + C_r)
  -- = (G_c^2 - A_c*C_c) + 2*G_c*G_r + G_r^2 - A_c*C_r - A_r*C_c - A_r*C_r
  have h_expand : (G_c + G_r) ^ 2 - (A_c + A_r) * (C_c + C_r) =
      (G_c ^ 2 - A_c * C_c) + (2 * G_c * G_r + G_r ^ 2 - A_c * C_r - A_r * C_c - A_r * C_r) := by
    ring
  rw [h_expand, MvPolynomial.coeff_add]
  apply dvd_add
  · -- Term (i): G_c^2 - A_c*C_c = (g^2 - a*c_val)*mono = (g^2 - a^2)*mono since a=c_val.
    -- 4 | (g^2 - a^2) by odd_sq_diff_div4.
    have h_sq_eq : G_c ^ 2 - A_c * C_c =
        MvPolynomial.C (g ^ 2 - a * c_val) *
          (MvPolynomial.X n * MvPolynomial.X n * (MvPolynomial.X (n + 1) * MvPolynomial.X (n + 1))) := by
      show (MvPolynomial.C g * MvPolynomial.X n * MvPolynomial.X (n + 1)) ^ 2 -
        (MvPolynomial.C a * MvPolynomial.X n * MvPolynomial.X n) *
          (MvPolynomial.C c_val * MvPolynomial.X (n + 1) * MvPolynomial.X (n + 1)) = _
      simp only [map_sub, map_pow, map_mul]; ring
    rw [h_sq_eq, show g ^ 2 - a * c_val = g ^ 2 - a ^ 2 from by rw [ha_eq_c]; ring,
        MvPolynomial.coeff_C_mul]
    exact dvd_mul_of_dvd_left (odd_sq_diff_div4 g a hg_odd ha_odd) _
  · -- Remainder: 2*G_c*G_r + G_r^2 - A_c*C_r - A_r*C_c - A_r*C_r
    -- Each term has 4 | coefficient:
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_add]
    -- Term: 2*G_c*G_r -- 2 * (G_c coeff) * (G_r coeff). G_r has even coeffs.
    -- So each product pair gives 2 * something * even = 4*k.
    have h1 : (4 : ℤ) ∣ (2 * G_c * G_r).coeff m := by
      rw [show 2 * G_c * G_r = MvPolynomial.C 2 * G_c * G_r from by
        rw [show (2 : MvPolynomial ℕ ℤ) = MvPolynomial.C 2 from by simp [map_ofNat]]]
      rw [show MvPolynomial.C (2 : ℤ) * G_c * G_r = MvPolynomial.C 2 * (G_c * G_r) from by ring]
      rw [MvPolynomial.coeff_C_mul, show (4 : ℤ) = 2 * 2 from by norm_num]
      apply mul_dvd_mul_left
      rw [MvPolynomial.coeff_mul]
      exact Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right (hGr_even _) _
    -- Term: G_r^2 -- each summand is G_r(a)*G_r(b), both even, so product div by 4.
    have h2 : (4 : ℤ) ∣ (G_r ^ 2).coeff m := by
      rw [sq, MvPolynomial.coeff_mul, show (4 : ℤ) = 2 * 2 from by norm_num]
      exact Finset.dvd_sum fun x _ => mul_dvd_mul (hGr_even _) (hGr_even _)
    -- Term: A_c*C_r -- C_r has 4 | coeffs.
    have h3 : (4 : ℤ) ∣ (A_c * C_r).coeff m := by
      rw [MvPolynomial.coeff_mul]
      exact Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right (hCr_four _) _
    -- Term: A_r*C_c -- A_r has 4 | coeffs.
    have h4 : (4 : ℤ) ∣ (A_r * C_c).coeff m := by
      rw [MvPolynomial.coeff_mul]
      exact Finset.dvd_sum fun x _ => dvd_mul_of_dvd_left (hAr_four _) _
    -- Term: A_r*C_r -- both have 4 | coeffs, so product has 16 | each summand.
    have h5 : (4 : ℤ) ∣ (A_r * C_r).coeff m := by
      rw [MvPolynomial.coeff_mul]
      exact Finset.dvd_sum fun x _ => dvd_mul_of_dvd_left (hAr_four _) _
    omega

/-- v_2(cont(G'^2 - A'C')) >= 2. -/
private lemma v2_content_prim_ge_2 (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K) (hn : 2 ≤ n)
    (hG_ne : G_poly n ≠ 0)
    (hprim_ne : mvContent (G' n ^ 2 - A' n K * C' n K) ≠ 0) :
    2 ≤ padicValNat 2 (mvContent (G' n ^ 2 - A' n K * C' n K)) := by
  -- 4 = 2^2 divides every coefficient of (G'^2-A'C')
  have h4 := four_dvd_prim_diff n K hK hnK hn hG_ne
  -- Therefore 4 divides gcd of all |coefficients| = content
  have h4_dvd : 4 ∣ mvContent (G' n ^ 2 - A' n K * C' n K) := by
    unfold mvContent
    apply Finset.dvd_gcd
    intro m _
    exact Int.natAbs_dvd_natAbs.mpr (h4 m)
  -- 4 = 2^2 | content implies v_2(content) >= 2
  exact (padicValNat_dvd_iff_le hprim_ne).mp
    (show 2 ^ 2 ∣ _ from by norm_num at h4_dvd ⊢; exact h4_dvd)

/-! ## Step 6.5 -- Upper bound via pair specialization (paper L1417-1421)

  For off-centre k_0 not in {n, n+1}: A(phi_{k_0}) = C(phi_{k_0}) = 0.
  So H(phi_{k_0}) = G(phi_{k_0})^2 = (b_{k_0}/2)^2.
  Content divides any evaluation, so cont(G'^2-A'C') | (b_{k_0}/2^{d+1})^2. -/

/-- H_poly evaluated at phi_{k_0}: since A and C vanish,
    H(phi) = G(phi)^2. -/
private lemma H_eval_eq_G_sq (n : ℕ) (hn : 0 < n) (k₀ : ℕ)
    (hk₀_lo : 1 ≤ k₀) (hk₀_hi : k₀ ≤ 2 * n)
    (hk₀_ne_n : k₀ ≠ n) (hk₀_ne_n1 : k₀ ≠ n + 1) :
    MvPolynomial.eval (phi n k₀) (H_poly n) =
      (MvPolynomial.eval (phi n k₀) (G_poly n)) ^ 2 := by
  unfold H_poly
  simp only [map_sub, map_pow, map_mul]
  rw [eval_A_n_phi_eq_zero n k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1,
      eval_C_n_phi_eq_zero n k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1]
  ring

/-- Evaluation of G_poly at phi_{k_0} equals b_{k_0}/2.
    Since B = 2*G and eval(B, phi) = b_{k_0}, we get eval(G, phi) = b_{k_0}/2. -/
private lemma G_eval_eq_bk_div2 (n : ℕ) (hn : 0 < n) (k₀ : ℕ)
    (hk₀_lo : 1 ≤ k₀) (hk₀_hi : k₀ ≤ 2 * n)
    (hk₀_ne_n : k₀ ≠ n) (hk₀_ne_n1 : k₀ ≠ n + 1) :
    2 * MvPolynomial.eval (phi n k₀) (G_poly n) = b_k_val n k₀ := by
  have hB := eval_B_phi_eq_bk n k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1 hn
  have hBG : MvPolynomial.eval (phi n k₀) (B_n n) =
      2 * MvPolynomial.eval (phi n k₀) (G_poly n) := by
    conv_lhs => rw [B_eq_two_G n hn]
    simp only [map_mul, map_ofNat]
  linarith

/-- Content of any MvPolynomial divides the evaluation at any integer point. -/
private lemma mvContent_dvd_eval (p : MvPolynomial ℕ ℤ) (x : ℕ → ℤ) :
    (↑(mvContent p) : ℤ) ∣ MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq]
  apply Finset.dvd_sum
  intro m _
  exact dvd_mul_of_dvd_left (mvContent_dvd_coeff p m) _

/-- Evaluation of (G'^2 - A'C') at phi_{k_0} equals (b_{k_0})^2 / (2^{d+1})^2,
    since H = 2^{2d} * (G'^2-A'C') and H(phi) = (b_{k_0}/2)^2.
    Thus G'^2-A'C' evaluated at phi = (b_{k_0}/2)^2 / 2^{2d} = (b_{k_0}/(2^{d+1}))^2. -/
private lemma prim_eval_at_phi (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hn : 0 < n) (k₀ : ℕ)
    (hk₀_lo : 1 ≤ k₀) (hk₀_hi : k₀ ≤ 2 * n)
    (hk₀_ne_n : k₀ ≠ n) (hk₀_ne_n1 : k₀ ≠ n + 1) :
    (2 ^ d n : ℤ) ^ 2 * MvPolynomial.eval (phi n k₀) (G' n ^ 2 - A' n K * C' n K) =
      (MvPolynomial.eval (phi n k₀) (G_poly n)) ^ 2 := by
  -- H = (2^d)^2 * (G'^2 - A'C')
  -- H(phi) = (2^d)^2 * (G'^2-A'C')(phi)
  -- Also H(phi) = G(phi)^2
  have hH := H_eq_scaled n K hK hnK
  have hH_eval : MvPolynomial.eval (phi n k₀) (H_poly n) =
      (2 ^ d n : ℤ) ^ 2 * MvPolynomial.eval (phi n k₀) (G' n ^ 2 - A' n K * C' n K) := by
    rw [hH]; simp only [map_mul, MvPolynomial.eval_C]
  have hH_eq_G := H_eval_eq_G_sq n hn k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1
  linarith

/-! ## Step 6.10 -- Combine bounds

  From Step 6.4: v_2(cont(G'^2-A'C')) >= 2
  From Step 6.5: cont(G'^2-A'C') | (b_{k_0}/2^{d+1})^2
  From P2CRS: v_2(b_{k_0}) = d+2 (PLACEHOLDER)
  -> v_2((b_{k_0}/2^{d+1})^2) = 2
  -> v_2(cont(G'^2-A'C')) <= 2
  Combined: v_2(cont(G'^2-A'C')) = 2, which is even.
  v_2(cont(H)) = 2d + 2 = 2(d+1), even. -/

theorem v2_b_k0_eq (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K) :
    ∃ k₀, 1 ≤ k₀ ∧ k₀ ≤ 2 * n ∧ k₀ ≠ n ∧ k₀ ≠ n + 1 ∧
      padicValNat 2 (Int.natAbs (b_k_val n k₀)) = d n + 2 := by
  refine ⟨n + 2 ^ (K - 1), ?_, ?_, ?_, ?_, ?_⟩
  · have hpow : 0 < 2 ^ (K - 1) := Nat.pos_of_ne_zero (by positivity)
    omega
  · exact k0_le_two_n K hK n hnK
  · exact k0_ne_n K hK n hnK
  · exact k0_ne_n_succ K hK n hnK
  · have hb : padicValNat 2 (Int.natAbs (b_formula n (n + 2 ^ (K - 1)))) =
        padicValNat 2 (Int.natAbs (b_formula n n)) + 1 := by
        exact v2_b_k0 K hK n hnK
    calc
      padicValNat 2 (Int.natAbs (b_k_val n (n + 2 ^ (K - 1)))) =
          padicValNat 2 (Int.natAbs (b_formula n (n + 2 ^ (K - 1)))) := by
            rw [← b_formula_eq_b_k_val]
      _ = padicValNat 2 (Int.natAbs (b_formula n n)) + 1 := hb
      _ = padicValNat 2 (scalar_AB n n) + 2 := by
        rw [v2_b_center K hK n hnK]
        omega
      _ = d n + 2 := by
        simpa [v2_scalar_AB_center_eq_d n K hK hnK]

/-- Upper bound: v_2(cont(G'^2-A'C')) <= 2.

  The proof uses: content divides any evaluation. Evaluating at phi_{k_0}:
  (G'^2-A'C')(phi_{k_0}) = (b_{k_0})^2 / (2^{d+1})^2.
  Since v_2(b_{k_0}) = d+2 (from P2CRS), v_2(this evaluation) = 2.
  So v_2(content) <= 2. -/
private lemma v2_content_prim_le_2_of_witness (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hn : 2 ≤ n) (hn0 : 0 < n)
    (k₀ : ℕ)
    (hk₀_lo : 1 ≤ k₀) (hk₀_hi : k₀ ≤ 2 * n)
    (hk₀_ne_n : k₀ ≠ n) (hk₀_ne_n1 : k₀ ≠ n + 1)
    (hv2_bk₀ : padicValNat 2 (Int.natAbs (b_k_val n k₀)) = d n + 2)
    (hprim_ne : mvContent (G' n ^ 2 - A' n K * C' n K) ≠ 0) :
    padicValNat 2 (mvContent (G' n ^ 2 - A' n K * C' n K)) ≤ 2 := by
  -- Get witness k_0 with v_2(b_{k_0}) = d+2
  have h_b_nat_ne : Int.natAbs (b_k_val n k₀) ≠ 0 := by
    intro hb0
    have h0 : padicValNat 2 (Int.natAbs (b_k_val n k₀)) = 0 := by simp [hb0]
    rw [hv2_bk₀] at h0
    omega
  have hG_eval_ne : MvPolynomial.eval (phi n k₀) (G_poly n) ≠ 0 := by
    intro h0
    have hBG := G_eval_eq_bk_div2 n hn0 k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1
    have hb0 : Int.natAbs (b_k_val n k₀) = 0 := by
      rw [Int.natAbs_eq_zero]; linarith
    exact h_b_nat_ne hb0
  have hG_eval_v2 : padicValNat 2 (Int.natAbs (MvPolynomial.eval (phi n k₀) (G_poly n))) =
      d n + 1 := by
    have h2G :
        padicValNat 2 (Int.natAbs (2 * MvPolynomial.eval (phi n k₀) (G_poly n))) =
          1 + padicValNat 2 (Int.natAbs (MvPolynomial.eval (phi n k₀) (G_poly n))) := by
      rw [Int.natAbs_mul, show Int.natAbs (2 : ℤ) = 2 by norm_num,
        padicValNat.mul (by norm_num) (Int.natAbs_ne_zero.mpr hG_eval_ne),
        show padicValNat 2 2 = 1 by exact padicValNat.self (by norm_num)]
    have hBG := G_eval_eq_bk_div2 n hn0 k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1
    rw [hBG] at h2G
    rw [hv2_bk₀] at h2G
    omega
  have hprim_eval_ne : MvPolynomial.eval (phi n k₀) (G' n ^ 2 - A' n K * C' n K) ≠ 0 := by
    intro h0
    have hsq : (MvPolynomial.eval (phi n k₀) (G_poly n)) ^ 2 = 0 := by
      have h := prim_eval_at_phi n K hK hnK hn0 k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1
      rw [h0, mul_zero] at h
      exact h.symm
    have hG0 : MvPolynomial.eval (phi n k₀) (G_poly n) = 0 := by
      exact sq_eq_zero_iff.mp hsq
    exact hG_eval_ne hG0
  have h_natabs_eval :
      padicValNat 2 (Int.natAbs (MvPolynomial.eval (phi n k₀) (G' n ^ 2 - A' n K * C' n K))) =
        2 := by
    have h_prim := prim_eval_at_phi n K hK hnK hn0 k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1
    have h_eq_natabs :
        Int.natAbs (((2 ^ d n : ℤ) ^ 2) * MvPolynomial.eval (phi n k₀)
          (G' n ^ 2 - A' n K * C' n K)) =
          Int.natAbs (MvPolynomial.eval (phi n k₀) (G_poly n)) ^ 2 := by
      rw [h_prim, Int.natAbs_pow]
    have h_lhs :
        padicValNat 2 (Int.natAbs (((2 ^ d n : ℤ) ^ 2) * MvPolynomial.eval (phi n k₀)
          (G' n ^ 2 - A' n K * C' n K))) =
          2 * d n + padicValNat 2
            (Int.natAbs (MvPolynomial.eval (phi n k₀) (G' n ^ 2 - A' n K * C' n K))) := by
      rw [Int.natAbs_mul]
      have hpow :
          Int.natAbs (((2 ^ d n : ℤ) ^ 2)) = 2 ^ (2 * d n) := by
        have : ((2 ^ d n : ℤ) ^ 2) = (2 : ℤ) ^ (d n * 2) := by ring
        rw [this, Int.natAbs_pow]; simp; ring
      rw [hpow, padicValNat.mul (by positivity) (Int.natAbs_ne_zero.mpr hprim_eval_ne)]
      rw [padicValNat.pow (2 * d n) (by norm_num)]
      simp [padicValNat.self]
    have h_rhs :
        padicValNat 2 (Int.natAbs (MvPolynomial.eval (phi n k₀) (G_poly n)) ^ 2) =
          2 * (d n + 1) := by
      rw [padicValNat.pow 2 (Int.natAbs_ne_zero.mpr hG_eval_ne), hG_eval_v2]
    have h_eq := congrArg (padicValNat 2) h_eq_natabs
    rw [h_lhs, h_rhs] at h_eq
    omega
  have h_dvd := mvContent_dvd_eval (G' n ^ 2 - A' n K * C' n K) (phi n k₀)
  have h_dvd_nat : mvContent (G' n ^ 2 - A' n K * C' n K) ∣
      Int.natAbs (MvPolynomial.eval (phi n k₀) (G' n ^ 2 - A' n K * C' n K)) :=
    Int.natAbs_dvd_natAbs.mpr h_dvd
  have h_le := (padicValNat_dvd_iff_le (p := 2) (Int.natAbs_ne_zero.mpr hprim_eval_ne)).mp
    (dvd_trans pow_padicValNat_dvd h_dvd_nat)
  rw [h_natabs_eval] at h_le; exact h_le

private lemma v2_content_prim_le_2 (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hn : 2 ≤ n) (hn0 : 0 < n)
    (hprim_ne : mvContent (G' n ^ 2 - A' n K * C' n K) ≠ 0) :
    padicValNat 2 (mvContent (G' n ^ 2 - A' n K * C' n K)) ≤ 2 := by
  obtain ⟨k₀, hk₀_lo, hk₀_hi, hk₀_ne_n, hk₀_ne_n1, hv2_bk₀⟩ :=
    v2_b_k0_eq n K hK hnK
  exact v2_content_prim_le_2_of_witness n K hK hnK hn hn0 k₀ hk₀_lo hk₀_hi hk₀_ne_n hk₀_ne_n1
    hv2_bk₀ hprim_ne

/-- v_2(cont(G'^2-A'C')) = 2. -/
private lemma v2_content_prim_eq_2 (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hn : 2 ≤ n) (hn0 : 0 < n)
    (hG_ne : G_poly n ≠ 0)
    (hprim_ne : mvContent (G' n ^ 2 - A' n K * C' n K) ≠ 0) :
    padicValNat 2 (mvContent (G' n ^ 2 - A' n K * C' n K)) = 2 :=
  le_antisymm
    (v2_content_prim_le_2 n K hK hnK hn hn0 hprim_ne)
    (v2_content_prim_ge_2 n K hK hnK hn hG_ne hprim_ne)

/-- v_2(cont(H)) is even in Case B. -/
private lemma v2_H_even_case_B (n K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hn : 2 ≤ n) (hn0 : 0 < n)
    (hG_ne : G_poly n ≠ 0)
    (hprim_ne : mvContent (G' n ^ 2 - A' n K * C' n K) ≠ 0)
    (hH_ne : mvContent (H_poly n) ≠ 0) :
    Even (padicValNat 2 (mvContent (H_poly n))) := by
  rw [v2_H_eq n K hK hnK hprim_ne,
      v2_content_prim_eq_2 n K hK hnK hn hn0 hG_ne hprim_ne]
  -- 2 * d n + 2 = 2 * (d n + 1)
  exact ⟨d n + 1, by ring⟩

/-! ## Exported theorem -/

/-- The main theorem for Case B: when n+2 = 2^K (K >= 2),
    v_2(cont(H)) is even. -/
theorem even_vp_H_of_eq_val_new (n : ℕ) (hn : 2 ≤ n)
    (K : ℕ) (hK : 2 ≤ K) (hnK : n + 2 = 2 ^ K)
    (hH_ne : mvContent (H_poly n) ≠ 0) :
    Even (padicValNat 2 (mvContent (H_poly n))) := by
  have hn1 : 1 ≤ n := by omega
  -- Derive G_poly n ≠ 0 from n ≥ 1
  have hG_ne : G_poly n ≠ 0 := by
    intro hG0
    have : G_poly_loc n = 0 := G_poly_eq_G_poly_loc n ▸ hG0
    have : mvContent (G_poly_loc n) = 0 := mvContent_eq_zero_iff.mpr this
    exact mvContent_G_poly_loc_ne n hn1 this
  -- Derive hprim_ne from hH_ne using H_eq_scaled
  have hprim_ne : mvContent (G' n ^ 2 - A' n K * C' n K) ≠ 0 := by
    intro h0
    apply hH_ne
    have h_zero : G' n ^ 2 - A' n K * C' n K = 0 := mvContent_eq_zero_iff.mp h0
    have := H_eq_scaled n K hK hnK
    rw [h_zero, mul_zero] at this
    exact mvContent_eq_zero_iff.mpr this
  exact v2_H_even_case_B n K hK hnK hn (by omega) hG_ne hprim_ne hH_ne

end QuarticInvariant
