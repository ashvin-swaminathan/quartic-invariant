import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical
noncomputable section

/-
Binary combinatorics for the `p = 2` branch.

The goal is the missing `centre_not_max` lemma from `CoeffExtract.lean`, and a
slightly stronger witness theorem.  The proof is organized around the binary
digit sum `s2` and Kummer's digit-sum formula.
-/

def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

lemma s2_two_mul (n : ℕ) : s2 (2 * n) = s2 n := by
  rcases n with _ | n
  · simp [s2]
  · have hdigits : Nat.digits 2 (2 * Nat.succ n) = 0 :: Nat.digits 2 (Nat.succ n) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Nat.digits_base_mul one_lt_two (Nat.succ_pos _))
    simp [s2, hdigits]

lemma s2_two_mul_add_one (n : ℕ) : s2 (2 * n + 1) = s2 n + 1 := by
  have hmod : (2 * n + 1) % 2 = 1 := by
    omega
  have hdiv : (2 * n + 1) / 2 = n := by
    omega
  have hdigits : Nat.digits 2 (2 * n + 1) = 1 :: Nat.digits 2 n := by
    rw [Nat.digits_of_two_le_of_pos (by decide) (by omega)]
    simp [hmod, hdiv]
  calc
    s2 (2 * n + 1) = 1 + s2 ((2 * n + 1) / 2) := by
      simp [s2, hdigits]
    _ = 1 + s2 n := by rw [hdiv]
    _ = s2 n + 1 := by omega

lemma s2_succ_le (n : ℕ) : s2 (n + 1) ≤ s2 n + 1 := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases Nat.even_or_odd n with h_even | h_odd
  · rcases h_even with ⟨m, rfl⟩
    have h := s2_two_mul_add_one m
    have hL : s2 (m + m + 1) = s2 m + 1 := by
      simpa [Nat.two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    have hR : s2 (m + m) = s2 m := by
      simpa [Nat.two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using s2_two_mul m
    rw [hL, hR]
  · rcases h_odd with ⟨m, rfl⟩
    have hm_lt : m < 2 * m + 1 := by omega
    have h := ih m hm_lt
    have h_even : s2 (2 * m + 2) = s2 (m + 1) := by
      simpa [Nat.two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        s2_two_mul (m + 1)
    have h_odd : s2 (2 * m + 1) = s2 m + 1 := s2_two_mul_add_one m
    have h' : s2 (m + 1) ≤ s2 m + 2 := le_trans h (by omega)
    calc
      s2 (2 * m + 2) = s2 (m + 1) := h_even
      _ ≤ s2 m + 2 := h'
      _ = s2 (2 * m + 1) + 1 := by rw [h_odd]

lemma s2_pow_mul_sub_one (a m : ℕ) (hm : 0 < m) :
    s2 (2 ^ a * m - 1) = s2 (m - 1) + a := by
  induction a generalizing m with
  | zero =>
      simp [s2]
  | succ a ih =>
      set x : ℕ := 2 ^ a * m
      have hx : x = 2 ^ a * m := rfl
      have hxpos : 0 < x := by
        dsimp [x]
        positivity
      have hpow : 2 ^ (a + 1) * m - 1 = 2 * (2 ^ a * m - 1) + 1 := by
        have hmul : 2 ^ (a + 1) * m = 2 * x := by
          rw [pow_succ, hx]
          ring_nf
        have hsub : 2 * x - 1 = 2 * (x - 1) + 1 := by
          omega
        rw [hmul]
        simpa [hx] using hsub
      calc
        s2 (2 ^ (a + 1) * m - 1) = s2 (2 * (2 ^ a * m - 1) + 1) := by
          exact congrArg s2 hpow
        _ = s2 (2 ^ a * m - 1) + 1 := by rw [s2_two_mul_add_one]
        _ = s2 (m - 1) + a + 1 := by rw [ih m hm]
        _ = s2 (m - 1) + (a + 1) := by omega

lemma choose_v2_s2 (k n : ℕ) [Fact (Nat.Prime 2)] (hk : k ≤ n) :
    padicValNat 2 (Nat.choose n k) = s2 k + s2 (n - k) - s2 n := by
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := k) (n := n) hk
  simpa [s2] using h

private lemma choose_v2_s2_center (n : ℕ) [Fact (Nat.Prime 2)] :
    padicValNat 2 (Nat.choose (2 * n + 1) n) =
      s2 n + s2 (n + 1) - (s2 n + 1) := by
  have h := choose_v2_s2 n (1 + 2 * n) (by omega)
  have hM : s2 (1 + 2 * n) = s2 n + 1 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using s2_two_mul_add_one n
  have hsub : 1 + 2 * n - n = n + 1 := by omega
  rw [hsub, hM] at h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

private lemma choose_v2_s2_witness (n j : ℕ) [Fact (Nat.Prime 2)] (hj : j ≤ 2 * n + 1) :
    padicValNat 2 (Nat.choose (2 * n + 1) j) =
      s2 j + s2 (2 * n + 1 - j) - (s2 n + 1) := by
  have h := choose_v2_s2 j (1 + 2 * n) (by omega)
  have hM : s2 (1 + 2 * n) = s2 n + 1 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using s2_two_mul_add_one n
  simpa [hM, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

private lemma witness_j0_lt (a r : ℕ) (hr : 0 < r) :
    2 * (2 ^ (a + 1) * r - 1) < 2 * (2 ^ a * (2 * r + 1) - 1) := by
  have hcpos : 0 < 2 ^ a := pow_pos (by decide) _
  have hlt0 : 2 ^ (a + 1) * r < 2 ^ a * (2 * r + 1) := by
    have hmul : 2 ^ a * (2 * r) < 2 ^ a * (2 * r + 1) := by
      exact (Nat.mul_lt_mul_left hcpos).2 (by omega)
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  have h1 : 1 ≤ 2 ^ (a + 1) * r := by
    have hpow : 0 < 2 ^ (a + 1) := pow_pos (by decide) _
    exact Nat.succ_le_of_lt (Nat.mul_pos hpow hr)
  have hlt1 : 2 ^ (a + 1) * r - 1 < 2 ^ a * (2 * r + 1) - 1 := by
    exact Nat.sub_lt_sub_right h1 hlt0
  exact (Nat.mul_lt_mul_left (by decide : 0 < 2)).2 hlt1

private lemma witness_comp_eq (a r : ℕ) (hr : 0 < r) :
    2 * (2 * (2 ^ a * (2 * r + 1) - 1)) + 1 - 2 * (2 ^ (a + 1) * r - 1) =
      2 * (2 ^ (a + 1) * (r + 1) - 1) + 1 := by
  set c : ℕ := 2 ^ a
  set b : ℕ := c * r
  have hcpos : 0 < c := by
    dsimp [c]
    exact pow_pos (by decide) _
  have hbpos : 0 < b := by
    dsimp [b]
    exact Nat.mul_pos hcpos hr
  have hA : 2 ^ a * (2 * r + 1) = 2 * b + c := by
    dsimp [b, c]
    ring_nf
  have hB : 2 ^ (a + 1) * r = 2 * b := by
    dsimp [b, c]
    rw [pow_succ]
    ring_nf
  have hC : 2 ^ (a + 1) * (r + 1) = 2 * b + 2 * c := by
    dsimp [b, c]
    rw [pow_succ]
    ring_nf
  have hb1 : 1 ≤ 2 * b := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 2) hbpos)
  have hbc1 : 1 ≤ 2 * b + c := by
    omega
  have hbc2 : 1 ≤ 2 * b + 2 * c := by
    omega
  rw [hA, hB, hC]
  have hleft : 2 * (2 * (2 * b + c - 1)) + 1 - 2 * (2 * b - 1) =
      2 * (2 * b + 2 * c - 1) + 1 := by
    omega
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hleft

private lemma witness_comp_s2 (a r : ℕ) [Fact (Nat.Prime 2)] :
    s2 (2 * (2 ^ (a + 1) * (r + 1) - 1) + 1) = s2 r + a + 2 := by
  rw [s2_two_mul_add_one, s2_pow_mul_sub_one (a + 1) (r + 1) (by positivity)]
  have hr1 : r + 1 - 1 = r := by omega
  rw [hr1]
  omega

lemma odd_part_decomp (n : ℕ) (hn : 1 ≤ n) (hn_even : Even n)
    (h_not_pow2 : ¬ ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K) :
    ∃ a r : ℕ, 0 < r ∧ n + 2 = 2 ^ (a + 1) * (2 * r + 1) := by
  have hnp2 : n + 2 ≠ 0 := by omega
  rcases Nat.exists_eq_two_pow_mul_odd hnp2 with ⟨k, m, hm_odd, hkm⟩
  have h_even_np2 : Even (n + 2) := by
    rcases hn_even with ⟨t, rfl⟩
    refine ⟨t + 1, by omega⟩
  have hk_pos : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    have hm_eq : n + 2 = m := by
      simpa [hk0'] using hkm
    have hodd_np2 : Odd (n + 2) := by
      simpa [hm_eq] using hm_odd
    exact (Nat.not_odd_iff_even.mpr h_even_np2) hodd_np2
  rcases hm_odd with ⟨r, rfl⟩
  have hr_pos : 0 < r := by
    by_contra hr0
    have hr : r = 0 := by omega
    subst hr
    have hpow : n + 2 = 2 ^ k := by
      simpa using hkm
    have hk_ge2 : 2 ≤ k := by
      by_contra hklt
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · simp at hpow
      · simp at hpow
        omega
    exact h_not_pow2 ⟨k, hk_ge2, hpow⟩
  refine ⟨k - 1, r, hr_pos, ?_⟩
  have hk_eq : k - 1 + 1 = k := by omega
  simpa [hk_eq] using hkm

/-- A stronger witness: for even `n` with `n+2` not a power of `2`, there is an
even off-center index with larger `2`-adic valuation than the center. -/
theorem exists_even_offcenter_maximizer (n : ℕ) (hn : 1 ≤ n) (hn_even : Even n)
    (h_not_pow2 : ¬ ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K) :
    ∃ j₀, j₀ < n ∧ Even j₀ ∧
      padicValNat 2 (Nat.choose (2 * n + 1) j₀) >
        padicValNat 2 (Nat.choose (2 * n + 1) n) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  rcases odd_part_decomp n hn hn_even h_not_pow2 with ⟨a, r, hr_pos, hdecomp⟩
  let u : ℕ := 2 ^ a * (2 * r + 1) - 1
  let j₀ : ℕ := 2 * (2 ^ (a + 1) * r - 1)
  have hmul : 2 ^ (a + 1) * (2 * r + 1) = 2 * (2 ^ a * (2 * r + 1)) := by
    rw [pow_succ]
    ring_nf
  have hn_eq : n = 2 * u := by
    dsimp [u]
    have hplus : n + 2 = 2 * (2 ^ a * (2 * r + 1)) := by
      rw [hdecomp, hmul]
    omega
  have hj0_lt : j₀ < n := by
    rw [hn_eq]
    dsimp [u, j₀]
    exact witness_j0_lt a r hr_pos
  have hj0_even : Even j₀ := by
    dsimp [j₀]
    refine ⟨2 ^ (a + 1) * r - 1, by omega⟩
  have hs2u : s2 u = s2 r + a := by
    dsimp [u]
    rw [s2_pow_mul_sub_one a (2 * r + 1) (by positivity)]
    have hpred : 2 * r + 1 - 1 = 2 * r := by omega
    rw [hpred, s2_two_mul]
  have hs2n : s2 n = s2 r + a := by
    rw [hn_eq, s2_two_mul, hs2u]
  have hs2n1 : s2 (n + 1) = s2 r + a + 1 := by
    rw [hn_eq, s2_two_mul_add_one, hs2u]
  have hcenter_raw :
      padicValNat 2 (Nat.choose (2 * n + 1) n) =
        s2 n + s2 (n + 1) - (s2 n + 1) := by
    exact choose_v2_s2_center n
  have hcenter : padicValNat 2 (Nat.choose (2 * n + 1) n) = s2 r + a := by
    have hcalc : s2 r + a + (s2 r + a + 1) - (s2 r + a + 1) = s2 r + a := by
      omega
    rw [hcenter_raw, hs2n, hs2n1]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcalc
  have hj0_s2 : s2 j₀ = s2 (r - 1) + a + 1 := by
    dsimp [j₀]
    rw [s2_two_mul, s2_pow_mul_sub_one (a + 1) r hr_pos]
    have htmp : s2 (r - 1) + (a + 1) = s2 (r - 1) + a + 1 := by omega
    simpa [Nat.add_assoc] using htmp
  have hcomp_eq : 2 * n + 1 - j₀ = 2 * (2 ^ (a + 1) * (r + 1) - 1) + 1 := by
    rw [hn_eq]
    dsimp [u, j₀]
    exact witness_comp_eq a r hr_pos
  have hs2comp : s2 (2 * n + 1 - j₀) = s2 r + a + 2 := by
    rw [hcomp_eq]
    exact witness_comp_s2 a r
  have hwit_raw :
      padicValNat 2 (Nat.choose (2 * n + 1) j₀) =
        s2 j₀ + s2 (2 * n + 1 - j₀) - (s2 n + 1) := by
    exact choose_v2_s2_witness n j₀ (by omega)
  have hwit : padicValNat 2 (Nat.choose (2 * n + 1) j₀) = s2 (r - 1) + a + 2 := by
    have hcalc : s2 (r - 1) + a + 1 + (s2 r + a + 2) - (s2 r + a + 1) =
        s2 (r - 1) + a + 2 := by
      omega
    rw [hwit_raw, hj0_s2, hs2comp, hs2n]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcalc
  have hs2_gap : s2 (r - 1) + 2 > s2 r := by
    have hr_eq : r - 1 + 1 = r := by omega
    have hle : s2 r ≤ s2 (r - 1) + 1 := by
      simpa [hr_eq] using (s2_succ_le (r - 1))
    omega
  have hgt : padicValNat 2 (Nat.choose (2 * n + 1) j₀) >
      padicValNat 2 (Nat.choose (2 * n + 1) n) := by
    rw [hwit, hcenter]
    omega
  exact ⟨j₀, hj0_lt, hj0_even, hgt⟩

/-- The axiom from `CoeffExtract`: the center is not maximal unless `n+2` is a power of `2`. -/
theorem centre_not_max (n : ℕ) (hn : 1 ≤ n) (hn_even : Even n)
    (h_not_pow2 : ¬ ∃ K, 2 ≤ K ∧ n + 2 = 2 ^ K) :
    padicValNat 2 (Nat.choose (2 * n + 1) n) <
      Finset.sup (Finset.range (2 * n + 2))
        (fun j => padicValNat 2 (Nat.choose (2 * n + 1) j)) := by
  rcases exists_even_offcenter_maximizer n hn hn_even h_not_pow2 with ⟨j₀, hj₀_lt, hj₀_even, hgt⟩
  have hj₀_mem : j₀ ∈ Finset.range (2 * n + 2) := by
    rw [Finset.mem_range]
    omega
  have hle_sup :
      padicValNat 2 (Nat.choose (2 * n + 1) j₀) ≤
        Finset.sup (Finset.range (2 * n + 2))
          (fun j => padicValNat 2 (Nat.choose (2 * n + 1) j)) := by
    exact Finset.le_sup (f := fun j => padicValNat 2 (Nat.choose (2 * n + 1) j)) hj₀_mem
  exact lt_of_lt_of_le hgt hle_sup

/-! ### Strict maximality when `n + 2 = 2 ^ K` -/

private lemma s2_zero : s2 0 = 0 := by simp [s2]

private lemma s2_pow2_sub_one (K : ℕ) (hK : 1 ≤ K) : s2 (2 ^ K - 1) = K := by
  have h : 2 ^ K - 1 = 2 ^ K * 1 - 1 := by ring_nf
  rw [h, s2_pow_mul_sub_one K 1 (by positivity)]
  simp [s2_zero]

private lemma s2_pow2_sub_two (K : ℕ) (hK : 2 ≤ K) : s2 (2 ^ K - 2) = K - 1 := by
  have hK1 : K = (K - 1) + 1 := by omega
  have hpow : 2 ^ K = 2 * 2 ^ (K - 1) := by
    conv_lhs => rw [hK1]
    rw [pow_succ]
    ring
  have h : 2 ^ K - 2 = 2 * (2 ^ (K - 1) - 1) := by
    have hpos : 1 ≤ 2 ^ (K - 1) := Nat.one_le_pow _ _ (by omega)
    omega
  rw [h, s2_two_mul]
  rw [s2_pow2_sub_one (K - 1) (by omega)]

/-- `s2 (2^K + r) = 1 + s2 r` when `r < 2^K`. -/
private lemma s2_pow2_add (K r : ℕ) (hr : r < 2 ^ K) : s2 (2 ^ K + r) = 1 + s2 r := by
  induction K generalizing r with
  | zero =>
    simp at hr; subst hr; decide
  | succ K ih =>
    rcases Nat.even_or_odd r with ⟨r', rfl⟩ | ⟨r', rfl⟩
    · -- r = r' + r' (even case)
      have hrr : r' + r' = 2 * r' := by ring
      rw [hrr]
      have hpow : 2 ^ (K + 1) + 2 * r' = 2 * (2 ^ K + r') := by rw [pow_succ]; ring
      rw [hpow, s2_two_mul, s2_two_mul]
      have hr' : r' < 2 ^ K := by rw [pow_succ, hrr] at hr; omega
      exact ih r' hr'
    · -- r = 2r'+1 (odd case)
      have hpow : 2 ^ (K + 1) + (2 * r' + 1) = 2 * (2 ^ K + r') + 1 := by rw [pow_succ]; ring
      rw [hpow, s2_two_mul_add_one, s2_two_mul_add_one]
      have hr' : r' < 2 ^ K := by rw [pow_succ] at hr; omega
      have := ih r' hr'
      omega

/-- `s2 a + s2 b ≤ 2K - 1` when `a + b = 2^K - 1` (proved mutually with `sub_two` variant). -/
private lemma s2_sum_le_pow2_sub_one (a b K : ℕ) (hK : 1 ≤ K)
    (hab : a + b = 2 ^ K - 1) :
    s2 a + s2 b ≤ 2 * K - 1 := by
  induction K generalizing a b with
  | zero => omega
  | succ K ih =>
    rcases K.eq_zero_or_pos with rfl | hK_pos
    · -- K = 0, K + 1 = 1, a + b = 2^1 - 1 = 1
      have : a ≤ 1 := by norm_num at hab; omega
      have : b ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> (first | omega | decide)
    · -- K ≥ 1. Since 2^(K+1) - 1 is odd, a and b have different parities.
      rcases Nat.even_or_odd a with ⟨a', rfl⟩ | ⟨a', rfl⟩ <;>
        rcases Nat.even_or_odd b with ⟨b', rfl⟩ | ⟨b', rfl⟩
      · -- both even: even + even = odd, contradiction
        exfalso
        have h1 : 1 ≤ 2 ^ (K + 1) := Nat.one_le_pow _ _ (by omega)
        have h2 : 2 ∣ 2 ^ (K + 1) := dvd_pow_self 2 (by omega)
        omega
      · -- a = a'+a' (even), b = 2b'+1 (odd)
        have haa : a' + a' = 2 * a' := by ring
        rw [haa, s2_two_mul, s2_two_mul_add_one]
        have hab' : a' + b' = 2 ^ K - 1 := by
          have h1 : 1 ≤ 2 ^ (K + 1) := Nat.one_le_pow _ _ (by omega)
          have h2 : 2 ∣ 2 ^ (K + 1) := dvd_pow_self 2 (by omega)
          omega
        have := ih a' b' hK_pos hab'
        omega
      · -- a = 2a'+1 (odd), b = b'+b' (even)
        have hbb : b' + b' = 2 * b' := by ring
        rw [s2_two_mul_add_one, hbb, s2_two_mul]
        have hab' : a' + b' = 2 ^ K - 1 := by
          have h1 : 1 ≤ 2 ^ (K + 1) := Nat.one_le_pow _ _ (by omega)
          have h2 : 2 ∣ 2 ^ (K + 1) := dvd_pow_self 2 (by omega)
          omega
        have := ih a' b' hK_pos hab'
        omega
      · -- both odd: odd + odd = odd, contradiction
        exfalso
        have h1 : 1 ≤ 2 ^ (K + 1) := Nat.one_le_pow _ _ (by omega)
        have h2 : 2 ∣ 2 ^ (K + 1) := dvd_pow_self 2 (by omega)
        omega

private lemma s2_sum_le_pow2_sub_two (a b K : ℕ) (hK : 2 ≤ K)
    (hab : a + b = 2 ^ K - 2) :
    s2 a + s2 b ≤ 2 * (K - 1) := by
  induction K generalizing a b with
  | zero => omega
  | succ K ih =>
    rcases Nat.lt_or_ge K 2 with hK_lt | hK_ge2
    · -- K ≤ 1
      interval_cases K
      · omega
      · -- K = 1, K + 1 = 2, a + b = 2^2 - 2 = 2
        have ha : a ≤ 2 := by norm_num at hab; omega
        have hb : b ≤ 2 := by omega
        interval_cases a <;> interval_cases b <;> (first | omega | decide)
    · -- K ≥ 2. Since 2^(K+1)-2 is even, a and b have the same parity.
      have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
      rcases Nat.even_or_odd a with ⟨a', rfl⟩ | ⟨a', rfl⟩ <;>
        rcases Nat.even_or_odd b with ⟨b', rfl⟩ | ⟨b', rfl⟩
      · -- both even: a = 2a', b = 2b'. a' + b' = 2^K - 1.
        have haa : a' + a' = 2 * a' := by ring
        have hbb : b' + b' = 2 * b' := by ring
        rw [haa, hbb, s2_two_mul, s2_two_mul]
        have hab' : a' + b' = 2 ^ K - 1 := by omega
        have := s2_sum_le_pow2_sub_one a' b' K (by omega) hab'
        omega
      · -- even + odd: parity mismatch with even sum. Contradiction.
        omega
      · -- odd + even: same
        omega
      · -- both odd: a = 2a'+1, b = 2b'+1, a' + b' = 2^K - 2.
        rw [s2_two_mul_add_one, s2_two_mul_add_one]
        have hab' : a' + b' = 2 ^ K - 2 := by omega
        have := ih a' b' (by omega) hab'
        omega

/-- When `j + j' = M` and `M` has a zero bit at position `k` (with `k < K` and `M < 2^K`),
    then the carry chain is interrupted and we get a strictly better bound. -/
private lemma s2_add_carries_strict_at_zero_bit (a b : ℕ) (K : ℕ) (hK : 2 ≤ K)
    (hab : a + b = 2 ^ K - 3) :
    s2 a + s2 b < 2 * (K - 1) := by
  induction K generalizing a b with
  | zero => omega
  | succ K ih =>
    rcases Nat.lt_or_ge K 2 with hK_lt | hK_ge2
    · -- K ≤ 1
      interval_cases K
      · omega
      · -- K = 1, so K + 1 = 2, a + b = 2^2 - 3 = 1
        have : a ≤ 1 := by norm_num at hab; omega
        have : b ≤ 1 := by omega
        interval_cases a <;> interval_cases b <;> (first | omega | decide)
    · -- K ≥ 2
      have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
      -- 2^(K+1) - 3 is odd, so a and b have different parities
      rcases Nat.even_or_odd a with ⟨a', rfl⟩ | ⟨a', rfl⟩ <;>
        rcases Nat.even_or_odd b with ⟨b', rfl⟩ | ⟨b', rfl⟩
      · -- both even: even + even = odd, contradiction
        exfalso
        have : 3 ≤ 2 ^ (K + 1) := le_trans (by norm_num : 3 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by omega) (by omega))
        omega
      · -- a even, b odd
        have haa : a' + a' = 2 * a' := by ring
        rw [haa, s2_two_mul, s2_two_mul_add_one]
        have hab' : a' + b' = 2 ^ K - 2 := by
          have : 3 ≤ 2 ^ (K + 1) :=
            le_trans (by norm_num : 3 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by omega) (by omega))
          omega
        have := s2_sum_le_pow2_sub_two a' b' K (by omega) hab'
        omega
      · -- a odd, b even
        have hbb : b' + b' = 2 * b' := by ring
        rw [s2_two_mul_add_one, hbb, s2_two_mul]
        have hab' : a' + b' = 2 ^ K - 2 := by
          have : 3 ≤ 2 ^ (K + 1) :=
            le_trans (by norm_num : 3 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by omega) (by omega))
          omega
        have := s2_sum_le_pow2_sub_two a' b' K (by omega) hab'
        omega
      · -- both odd: contradiction
        omega

theorem choose_center_strict_max_pow2 (n K : ℕ) (hK : 2 ≤ K) (hn : n + 2 = 2 ^ K)
    (j : ℕ) (hj : j < n) :
    padicValNat 2 (Nat.choose (2 * n + 1) j) <
      padicValNat 2 (Nat.choose (2 * n + 1) n) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  -- Compute n = 2^K - 2
  have hn_eq : n = 2 ^ K - 2 := by omega
  -- Compute s2 values
  have hs2n : s2 n = K - 1 := by rw [hn_eq]; exact s2_pow2_sub_two K hK
  have hn1_eq : n + 1 = 2 ^ K - 1 := by omega
  have hs2n1 : s2 (n + 1) = K := by rw [hn1_eq]; exact s2_pow2_sub_one K (by omega)
  -- Center value
  have hcenter : padicValNat 2 (Nat.choose (2 * n + 1) n) =
      s2 n + s2 (n + 1) - (s2 n + 1) := choose_v2_s2_center n
  have hcenter_val : padicValNat 2 (Nat.choose (2 * n + 1) n) = K - 1 := by
    rw [hcenter, hs2n, hs2n1]; omega
  -- Witness value
  have hj_le : j ≤ 2 * n + 1 := by omega
  have hwitness : padicValNat 2 (Nat.choose (2 * n + 1) j) =
      s2 j + s2 (2 * n + 1 - j) - (s2 n + 1) := choose_v2_s2_witness n j hj_le
  -- Decompose 2*n+1 - j = 2^K + (2^K - 3 - j), where (2^K - 3 - j) < 2^K
  set r := 2 ^ K - 3 - j with hr_def
  have hj_lt_pow : j < 2 ^ K - 2 := by omega
  have hr_lt : r < 2 ^ K := by omega
  have hcomp : 2 * n + 1 - j = 2 ^ K + r := by omega
  -- s2(2*n+1 - j) = 1 + s2(r)
  have hs2_comp : s2 (2 * n + 1 - j) = 1 + s2 r := by
    rw [hcomp]; exact s2_pow2_add K r hr_lt
  -- j + r = 2^K - 3
  have hsum : j + r = 2 ^ K - 3 := by omega
  -- By the strict carries bound: s2(j) + s2(r) < 2*(K-1)
  have h_strict := s2_add_carries_strict_at_zero_bit j r K hK hsum
  -- So s2(j) + s2(2*n+1-j) = s2(j) + 1 + s2(r) < 2*(K-1) + 1 = 2K - 1
  -- And v₂(C(2n+1,j)) = s2(j) + s2(2*n+1-j) - K < K - 1 = center
  rw [hwitness, hs2_comp, hcenter_val, hs2n]
  omega
