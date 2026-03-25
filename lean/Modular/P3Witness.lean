import Mathlib
import Modular.Defs

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section

/-! ======== P3 Non-Prime-Power Case ======== -/

namespace QuarticInvariant.P3

/-! ## Base-3 digit sum -/

/-- Sum of base-3 digits of n. -/
def s3 (n : ℕ) : ℕ := (Nat.digits 3 n).sum

/-- F_N(k) = v_3(C(N,k)) via Kummer's digit-sum formula. -/
def F (N k : ℕ) : ℕ := padicValNat 3 (Nat.choose N k)

/-- G_A(a) = F_A(a) + v_3(A - a). -/
def G (A a : ℕ) : ℕ := F A a + padicValNat 3 (A - a)

/-! ## Helper: digit-sum of 3n + d -/

private lemma s3_three_mul_add {n d : ℕ} (hd : d < 3) (hnd : n ≠ 0 ∨ d ≠ 0) :
    s3 (3 * n + d) = s3 n + d := by
  simp only [s3]
  have h3 : (1 : ℕ) < 3 := by norm_num
  have hpos : 0 < 3 * n + d := by omega
  rw [show 3 * n + d = d + 3 * n from by ring]
  rw [Nat.digits_add 3 h3 d n (by omega) (by omega)]
  simp [List.sum_cons, add_comm]

private lemma s3_zero : s3 0 = 0 := by simp [s3, Nat.digits]

/-- Kummer digit-sum formula (addition form to avoid Nat subtraction issues):
    2 * v_3(C(n,k)) + s_3(n) = s_3(k) + s_3(n-k) for k ≤ n. -/
private lemma kummer_digit_sum (n k : ℕ) (h : k ≤ n) :
    2 * F n k + s3 n = s3 k + s3 (n - k) := by
  have hmain := @sub_one_mul_padicValNat_choose_eq_sub_sum_digits 3 k n (Fact.mk (by norm_num : Nat.Prime 3)) h
  simp only [show 3 - 1 = 2 from by norm_num] at hmain
  -- hmain is in Nat with subtraction: 2 * val = dK + dNK - dN
  -- We need: 2 * val + dN = dK + dNK
  -- Key: digit_sum_le says dK ≤ k, dNK ≤ n-k, dN ≤ n
  -- But we actually need dK + dNK ≥ dN, which follows from hmain and val ≥ 0
  -- In Nat: if 2 * val = dK + dNK - dN then dK + dNK ≥ dN (otherwise RHS = 0 and LHS = 0 but we need the subtraction to be exact)
  -- Actually use Int to be safe
  simp only [F, s3]
  -- Use factorial p-adic valuation formula to get digit sum inequality
  haveI : Fact (Nat.Prime 3) := Fact.mk (by norm_num)
  have hfn := sub_one_mul_padicValNat_factorial (p := 3) n
  have hfk := sub_one_mul_padicValNat_factorial (p := 3) k
  have hfnk := sub_one_mul_padicValNat_factorial (p := 3) (n - k)
  simp only [show 3 - 1 = 2 from by norm_num] at hfn hfk hfnk hmain
  -- hfn : 2 * v(n!) = n - s(n), etc.
  -- From C(n,k) = n! / (k! * (n-k)!), k! * (n-k)! | n!, so v(k!) + v((n-k)!) ≤ v(n!)
  have hdvd : k.factorial * (n - k).factorial ∣ n.factorial :=
    Nat.factorial_mul_factorial_dvd_factorial h
  have hne_k : k.factorial ≠ 0 := Nat.factorial_ne_zero k
  have hne_nk : (n - k).factorial ≠ 0 := Nat.factorial_ne_zero (n - k)
  have hne_n : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hval_mul : padicValNat 3 (k.factorial * (n - k).factorial) =
      padicValNat 3 k.factorial + padicValNat 3 (n - k).factorial :=
    padicValNat.mul hne_k hne_nk
  have hval_le : padicValNat 3 (k.factorial * (n - k).factorial) ≤ padicValNat 3 n.factorial := by
    rw [← padicValNat_dvd_iff_le hne_n]
    exact pow_padicValNat_dvd |>.trans hdvd
  -- Convert Nat subtraction in factorial formulas to addition using digit_sum_le
  have hle_n := Nat.digit_sum_le 3 n
  have hle_k := Nat.digit_sum_le 3 k
  have hle_nk := Nat.digit_sum_le 3 (n - k)
  -- Now: from hfn, s(n) ≤ n, so 2*v(n!) + s(n) = n
  -- Similarly for k and n-k
  -- From hval_le: v(k!) + v((n-k)!) ≤ v(n!)
  -- So n = 2*v(n!) + s(n) ≥ 2*(v(k!) + v((n-k)!)) + s(n)
  -- And k + (n-k) = n, (2*v(k!) + s(k)) + (2*v((n-k)!) + s(n-k)) = k + (n-k) = n
  -- So s(k) + s(n-k) = n - 2*(v(k!) + v((n-k)!)) ≥ n - 2*v(n!) = s(n)
  -- This gives the inequality we need, and combined with hmain proves the goal.
  have hfn_add : 2 * padicValNat 3 n.factorial + (Nat.digits 3 n).sum = n := by omega
  have hfk_add : 2 * padicValNat 3 k.factorial + (Nat.digits 3 k).sum = k := by omega
  have hfnk_add : 2 * padicValNat 3 (n - k).factorial + (Nat.digits 3 (n - k)).sum = n - k := by omega
  rw [hval_mul] at hval_le
  omega

/-- s3(3n) = s3(n) for n > 0 (prepend digit 0). -/
private lemma s3_three_mul (n : ℕ) (hn : 0 < n) : s3 (3 * n) = s3 n := by
  have : s3 (3 * n + 0) = s3 n + 0 := s3_three_mul_add (by norm_num) (by omega)
  simp at this; exact this

/-- s3(1) = 1. -/
private lemma s3_one : s3 1 = 1 := by decide

/-- 2 * v_3(n) + s3(n) = 1 + s3(n-1) for n ≥ 1. -/
private lemma two_mul_padicValNat_eq (n : ℕ) (hn : 1 ≤ n) :
    2 * padicValNat 3 n + s3 n = 1 + s3 (n - 1) := by
  have hF : F n 1 = padicValNat 3 n := by
    simp [F, Nat.choose_one_right]
  have := kummer_digit_sum n 1 hn
  rw [hF, s3_one] at this
  omega

/-! ## Ternary recursions for F -/

/-- F_{3A+2}(3a+r) = F_A(a) for r ∈ {0,1,2}. -/
theorem F_3A2 (A a : ℕ) (r : ℕ) (hr : r ≤ 2) (ha : a ≤ A) :
    F (3 * A + 2) (3 * a + r) = F A a := by
  -- Use digit-sum formula: 2 * F(N,k) = s3(k) + s3(N-k) - s3(N)
  -- With N = 3A+2, k = 3a+r, N-k = 3(A-a) + (2-r)
  have hk_le : 3 * a + r ≤ 3 * A + 2 := by omega
  have h_sub : 3 * A + 2 - (3 * a + r) = 3 * (A - a) + (2 - r) := by omega
  have h_lhs := kummer_digit_sum (3 * A + 2) (3 * a + r) hk_le
  have h_rhs := kummer_digit_sum A a ha
  -- Compute digit sums using s3_three_mul_add
  -- s3(3a + r)
  have hs_k : s3 (3 * a + r) = s3 a + r := by
    by_cases ha0 : a = 0 ∧ r = 0
    · obtain ⟨rfl, rfl⟩ := ha0; simp [s3_zero]
    · push_neg at ha0
      exact s3_three_mul_add (by omega) (by tauto)
  -- s3(3(A-a) + (2-r))
  have hs_nk : s3 (3 * (A - a) + (2 - r)) = s3 (A - a) + (2 - r) := by
    by_cases h0 : A - a = 0 ∧ 2 - r = 0
    · obtain ⟨h1, h2⟩ := h0
      have : a = A := by omega
      have : r = 2 := by omega
      subst_vars; simp [s3_zero]
    · push_neg at h0
      exact s3_three_mul_add (by omega) (by tauto)
  -- s3(3A + 2)
  have hs_n : s3 (3 * A + 2) = s3 A + 2 := by
    by_cases hA0 : A = 0
    · subst hA0; decide
    · exact s3_three_mul_add (by norm_num) (by tauto)
  rw [h_sub] at h_lhs
  rw [hs_k, hs_nk, hs_n] at h_lhs
  -- Now h_lhs : 2 * F ... = (s3 a + r) + (s3 (A-a) + (2-r)) - (s3 A + 2)
  -- = s3 a + s3 (A-a) - s3 A = 2 * F A a
  omega

/-- F_{3A}(3a) = F_A(a). -/
theorem F_3A_zero (A a : ℕ) (ha : a ≤ A - 1) :
    F (3 * A) (3 * a) = F A a := by
  by_cases hA : A = 0
  · subst hA; have ha0 : a = 0 := by omega
    subst ha0; rfl
  have hA' : 1 ≤ A := by omega
  have haA : a ≤ A := by omega
  have hAa : 1 ≤ A - a := by omega
  have hk_le : 3 * a ≤ 3 * A := by omega
  have h_sub : 3 * A - 3 * a = 3 * (A - a) := by omega
  have h_lhs := kummer_digit_sum (3 * A) (3 * a) hk_le
  have h_rhs := kummer_digit_sum A a haA
  rw [h_sub] at h_lhs
  by_cases ha0 : a = 0
  · subst ha0
    simp only [Nat.mul_zero, s3_zero, Nat.zero_add] at *
    rw [s3_three_mul _ (by omega), s3_three_mul _ (by omega)] at h_lhs
    omega
  · rw [s3_three_mul _ (by omega), s3_three_mul _ (by omega), s3_three_mul _ (by omega)] at h_lhs
    omega

/-- F_{3A}(3a+1) = G_A(a) + 1. -/
theorem F_3A_one (A a : ℕ) (ha : a + 1 ≤ A) :
    F (3 * A) (3 * a + 1) = G A a + 1 := by
  have haA : a ≤ A := by omega
  have hAa : 1 ≤ A - a := by omega
  have hk_le : 3 * a + 1 ≤ 3 * A := by omega
  have h_sub : 3 * A - (3 * a + 1) = 3 * (A - a - 1) + 2 := by omega
  have h_lhs := kummer_digit_sum (3 * A) (3 * a + 1) hk_le
  have h_rhs := kummer_digit_sum A a haA
  have h_val := two_mul_padicValNat_eq (A - a) hAa
  rw [h_sub] at h_lhs
  have hs1 : s3 (3 * a + 1) = s3 a + 1 :=
    s3_three_mul_add (by norm_num) (by omega)
  have hs2 : s3 (3 * (A - a - 1) + 2) = s3 (A - a - 1) + 2 :=
    s3_three_mul_add (by norm_num) (by omega)
  have hs3 : s3 (3 * A) = s3 A := s3_three_mul A (by omega)
  rw [hs1, hs2, hs3] at h_lhs
  simp only [G]
  have hsub : A - a - 1 = (A - a) - 1 := by omega
  rw [hsub] at h_lhs
  omega

/-- F_{3A}(3a+2) = G_A(a) + 1. -/
theorem F_3A_two (A a : ℕ) (ha : a + 1 ≤ A) :
    F (3 * A) (3 * a + 2) = G A a + 1 := by
  have haA : a ≤ A := by omega
  have hAa : 1 ≤ A - a := by omega
  have hk_le : 3 * a + 2 ≤ 3 * A := by omega
  have h_sub : 3 * A - (3 * a + 2) = 3 * (A - a - 1) + 1 := by omega
  have h_lhs := kummer_digit_sum (3 * A) (3 * a + 2) hk_le
  have h_rhs := kummer_digit_sum A a haA
  have h_val := two_mul_padicValNat_eq (A - a) hAa
  rw [h_sub] at h_lhs
  have hs1 : s3 (3 * a + 2) = s3 a + 2 :=
    s3_three_mul_add (by norm_num) (by omega)
  have hs2 : s3 (3 * (A - a - 1) + 1) = s3 (A - a - 1) + 1 :=
    s3_three_mul_add (by norm_num) (by omega)
  have hs3 : s3 (3 * A) = s3 A := s3_three_mul A (by omega)
  rw [hs1, hs2, hs3] at h_lhs
  simp only [G]
  have hsub : A - a - 1 = (A - a) - 1 := by omega
  rw [hsub] at h_lhs
  omega

/-- F_{3A+1}(3a) = F_A(a). -/
theorem F_3A1_zero (A a : ℕ) (ha : a ≤ A - 1) :
    F (3 * A + 1) (3 * a) = F A a := by
  by_cases hA : A = 0
  · subst hA; have ha0 : a = 0 := by omega
    subst ha0; rfl
  have haA : a ≤ A := by omega
  have hk_le : 3 * a ≤ 3 * A + 1 := by omega
  have h_sub : 3 * A + 1 - 3 * a = 3 * (A - a) + 1 := by omega
  have h_lhs := kummer_digit_sum (3 * A + 1) (3 * a) hk_le
  have h_rhs := kummer_digit_sum A a haA
  rw [h_sub] at h_lhs
  have hs1 : s3 (3 * (A - a) + 1) = s3 (A - a) + 1 :=
    s3_three_mul_add (by norm_num) (by omega)
  have hs3 : s3 (3 * A + 1) = s3 A + 1 :=
    s3_three_mul_add (by norm_num) (by omega)
  by_cases ha0 : a = 0
  · subst ha0
    simp only [Nat.mul_zero, s3_zero, Nat.zero_add] at *
    rw [hs1, hs3] at h_lhs; omega
  · rw [s3_three_mul _ (by omega), hs1, hs3] at h_lhs; omega

/-- F_{3A+1}(3a+1) = F_A(a). -/
theorem F_3A1_one (A a : ℕ) (ha : a ≤ A - 1) :
    F (3 * A + 1) (3 * a + 1) = F A a := by
  by_cases hA : A = 0
  · subst hA; have ha0 : a = 0 := by omega
    subst ha0; simp [F, Nat.choose]
  have haA : a ≤ A := by omega
  have hAa : 1 ≤ A - a := by omega
  have hk_le : 3 * a + 1 ≤ 3 * A + 1 := by omega
  have h_sub : 3 * A + 1 - (3 * a + 1) = 3 * (A - a) := by omega
  have h_lhs := kummer_digit_sum (3 * A + 1) (3 * a + 1) hk_le
  have h_rhs := kummer_digit_sum A a haA
  rw [h_sub] at h_lhs
  have hs1 : s3 (3 * a + 1) = s3 a + 1 :=
    s3_three_mul_add (by norm_num) (by omega)
  have hs2 : s3 (3 * (A - a)) = s3 (A - a) := s3_three_mul _ (by omega)
  have hs3 : s3 (3 * A + 1) = s3 A + 1 :=
    s3_three_mul_add (by norm_num) (by omega)
  rw [hs1, hs2, hs3] at h_lhs; omega

/-- F_{3A+1}(3a+2) = G_A(a) + 1. -/
theorem F_3A1_two (A a : ℕ) (ha : a + 1 ≤ A) :
    F (3 * A + 1) (3 * a + 2) = G A a + 1 := by
  have haA : a ≤ A := by omega
  have hAa : 1 ≤ A - a := by omega
  have hk_le : 3 * a + 2 ≤ 3 * A + 1 := by omega
  have h_sub : 3 * A + 1 - (3 * a + 2) = 3 * (A - a - 1) + 2 := by omega
  have h_lhs := kummer_digit_sum (3 * A + 1) (3 * a + 2) hk_le
  have h_rhs := kummer_digit_sum A a haA
  have h_val := two_mul_padicValNat_eq (A - a) hAa
  rw [h_sub] at h_lhs
  have hs1 : s3 (3 * a + 2) = s3 a + 2 :=
    s3_three_mul_add (by norm_num) (by omega)
  have hs2 : s3 (3 * (A - a - 1) + 2) = s3 (A - a - 1) + 2 :=
    s3_three_mul_add (by norm_num) (by omega)
  have hs3 : s3 (3 * A + 1) = s3 A + 1 :=
    s3_three_mul_add (by norm_num) (by omega)
  rw [hs1, hs2, hs3] at h_lhs
  simp only [G]
  have hsub : A - a - 1 = (A - a) - 1 := by omega
  rw [hsub] at h_lhs
  omega

/-! ## G recursions (Corollary 6.4) -/

private lemma padicValNat_three_mul (m : ℕ) (hm : m ≠ 0) :
    padicValNat 3 (3 * m) = 1 + padicValNat 3 m := by
  haveI : Fact (Nat.Prime 3) := Fact.mk (by norm_num)
  rw [padicValNat.mul (by norm_num) hm, padicValNat_self]

private lemma padicValNat_three_mul_sub_one (m : ℕ) (hm : 0 < m) :
    padicValNat 3 (3 * m - 1) = 0 := by
  haveI : Fact (Nat.Prime 3) := Fact.mk (by norm_num)
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have : (3 * m - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  omega

private lemma padicValNat_three_mul_sub_two (m : ℕ) (hm : 0 < m) :
    padicValNat 3 (3 * m - 2) = 0 := by
  haveI : Fact (Nat.Prime 3) := Fact.mk (by norm_num)
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have : (3 * m - 2) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  omega

theorem G_3A (A a : ℕ) (hA : 1 ≤ A) (ha : a ≤ A - 1) (r : ℕ) (hr : r ≤ 2) :
    G (3 * A) (3 * a + r) = G A a + 1 := by
  have hAa : 0 < A - a := by omega
  -- G(3A, 3a+r) = F(3A, 3a+r) + v_3(3A - (3a+r))
  -- 3A - (3a+r) = 3(A-a) - r
  unfold G
  have h_sub : 3 * A - (3 * a + r) = 3 * (A - a) - r := by omega
  rw [h_sub]
  interval_cases r
  · -- r = 0: F(3A,3a) = F(A,a), v_3(3(A-a)) = 1 + v_3(A-a)
    simp only [Nat.add_zero, Nat.sub_zero]
    rw [F_3A_zero A a ha, padicValNat_three_mul (A - a) (by omega)]
    omega
  · -- r = 1: F(3A,3a+1) = G(A,a)+1 = F(A,a)+v_3(A-a)+1, v_3(3(A-a)-1) = 0
    rw [F_3A_one A a (by omega)]
    have : padicValNat 3 (3 * (A - a) - 1) = 0 := padicValNat_three_mul_sub_one (A - a) hAa
    rw [this]; unfold G; omega
  · -- r = 2: F(3A,3a+2) = G(A,a)+1 = F(A,a)+v_3(A-a)+1, v_3(3(A-a)-2) = 0
    rw [F_3A_two A a (by omega)]
    have : padicValNat 3 (3 * (A - a) - 2) = 0 := padicValNat_three_mul_sub_two (A - a) hAa
    rw [this]; unfold G; omega

theorem G_3A1_pos (A a : ℕ) (hA : 1 ≤ A) (ha : a ≤ A - 1) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    G (3 * A + 1) (3 * a + r) = G A a + 1 := by
  have hAa : 0 < A - a := by omega
  unfold G
  have h_sub : 3 * A + 1 - (3 * a + r) = 3 * (A - a) + 1 - r := by omega
  rw [h_sub]
  -- r ∈ {1, 2} since hr1 : 1 ≤ r and hr2 : r ≤ 2
  rcases r with _ | r
  · omega -- r = 0 is excluded by hr1
  rcases r with _ | r
  · -- r = 1: 3(A-a)+1-1 = 3(A-a), F(3A+1,3a+1) = F(A,a), v_3(3(A-a)) = 1+v_3(A-a)
    simp only [show 3 * (A - a) + 1 - 1 = 3 * (A - a) from by omega]
    rw [F_3A1_one A a ha, padicValNat_three_mul (A - a) (by omega)]
    omega
  rcases r with _ | r
  · -- r = 2: 3(A-a)+1-2 = 3(A-a)-1, F(3A+1,3a+2) = G(A,a)+1, v_3(3(A-a)-1) = 0
    simp only [show 3 * (A - a) + 1 - 2 = 3 * (A - a) - 1 from by omega]
    rw [F_3A1_two A a (by omega)]
    have : padicValNat 3 (3 * (A - a) - 1) = 0 := padicValNat_three_mul_sub_one (A - a) hAa
    rw [this]; unfold G; omega
  · omega -- r ≥ 3 excluded by hr2

theorem G_3A2_two (A a : ℕ) (hA : 1 ≤ A) (ha : a ≤ A - 1) :
    G (3 * A + 2) (3 * a + 2) = G A a + 1 := by
  have hAa : 0 < A - a := by omega
  unfold G
  have h_sub : 3 * A + 2 - (3 * a + 2) = 3 * (A - a) := by omega
  rw [h_sub, F_3A2 A a 2 (by omega) (by omega), padicValNat_three_mul (A - a) (by omega)]
  omega

/-! ## Maximizer lemmas -/

/-- Key symmetry: G(A, a) = G(A, A - 1 - a), because C(A,a)*(A-a) = C(A,a+1)*(a+1). -/
private lemma G_symm (A a : ℕ) (ha : a ≤ A - 1) :
    G A a = G A (A - 1 - a) := by
  by_cases hA : A = 0
  · subst hA
    have : a = 0 := by omega
    subst this; rfl
  simp only [G, F]
  have ha1 : a + 1 ≤ A := by omega
  have hAsub : A - (A - 1 - a) = a + 1 := by omega
  rw [hAsub]
  have hchoose : Nat.choose A (A - 1 - a) = Nat.choose A (a + 1) := by
    have := Nat.choose_symm (n := A) (k := a + 1) ha1
    have heq : A - (a + 1) = A - 1 - a := by omega
    rw [heq] at this; exact this
  rw [hchoose]
  have hprod : Nat.choose A a * (A - a) = Nat.choose A (a + 1) * (a + 1) :=
    (Nat.choose_succ_right_eq A a).symm
  have h0 : Nat.choose A a ≠ 0 := Nat.choose_ne_zero (by omega)
  have hAa : A - a ≠ 0 := by omega
  have ha1' : a + 1 ≠ 0 := by omega
  have hchoose_ne : Nat.choose A (a + 1) ≠ 0 := by
    intro h
    have : Nat.choose A a * (A - a) = 0 := by rw [hprod, h, Nat.zero_mul]
    exact Nat.mul_ne_zero h0 hAa this
  rw [← padicValNat.mul h0 hAa, ← padicValNat.mul hchoose_ne ha1', hprod]

/-- G_A attains its maximum in the lower half a < A/2. -/
theorem G_lower_half (A : ℕ) (hA : 1 ≤ A) :
    ∃ a, a < A / 2 + 1 ∧ a ≤ A - 1 ∧
      ∀ b, b ≤ A - 1 → G A b ≤ G A a := by
  -- The set {0, ..., A-1} is nonempty since A ≥ 1
  have hne : (Finset.range A).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨a, ha_mem, ha_max⟩ := Finset.exists_max_image (Finset.range A) (G A) hne
  rw [Finset.mem_range] at ha_mem
  -- If a < A/2 + 1, we're done
  by_cases h_half : a < A / 2 + 1
  · exact ⟨a, h_half, by omega, fun b hb => ha_max b (Finset.mem_range.mpr (by omega))⟩
  · -- a ≥ A/2 + 1, so a > A/2. Use symmetry: a' = A - 1 - a < A/2.
    push_neg at h_half
    have h_half' : A / 2 + 1 ≤ a := h_half
    let a' := A - 1 - a
    have ha'_lt : a' < A / 2 + 1 := by
      simp only [a']
      omega
    have ha'_le : a' ≤ A - 1 := by omega
    have ha_le : a ≤ A - 1 := by omega
    have hG_eq : G A a = G A a' := G_symm A a ha_le
    exact ⟨a', ha'_lt, ha'_le, fun b hb => by
      have := ha_max b (Finset.mem_range.mpr (by omega))
      omega⟩

/-- F(N, k) = F(N, N-k) by binomial coefficient symmetry. -/
private lemma F_symm' (N k : ℕ) (hk : k ≤ N) : F N k = F N (N - k) := by
  simp [F, Nat.choose_symm hk]

/-- Any function on {0,...,N} with f(k) = f(N-k) has a maximizer in {0,...,N/2}. -/
private lemma max_lower_half (N : ℕ) (f : ℕ → ℕ) (hN : 1 ≤ N)
    (hsymm : ∀ k, k ≤ N → f k = f (N - k)) :
    ∃ a, a ≤ N / 2 ∧ a ≤ N ∧ ∀ b, b ≤ N → f b ≤ f a := by
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨a, ha_mem, ha_max⟩ := Finset.exists_max_image (Finset.range (N + 1)) f hne
  rw [Finset.mem_range] at ha_mem
  by_cases h : a ≤ N / 2
  · exact ⟨a, h, by omega, fun b hb => ha_max b (Finset.mem_range.mpr (by omega))⟩
  · push_neg at h
    exact ⟨N - a, by omega, by omega, fun b hb => by
      have := ha_max b (Finset.mem_range.mpr (by omega)); rw [hsymm a (by omega)] at this; omega⟩

/-- For odd B not of the form 2·3^t - 1: G_B has a maximizer with a < (B-1)/2. -/
theorem G_odd_sharp (B : ℕ) (hB_odd : Odd B) (hB_pos : 1 ≤ B)
    (h_not_exc : ∀ t : ℕ, B ≠ 2 * 3 ^ t - 1) :
    ∃ a, a < (B - 1) / 2 ∧ a ≤ B - 1 ∧
      ∀ b, b ≤ B - 1 → G B b ≤ G B a := by
  -- Strong induction on B
  revert hB_pos h_not_exc
  induction B using Nat.strongRecOn with
  | ind B ih =>
    intro hB_pos h_not_exc
    -- B ≥ 3 since B ≠ 1 = 2·3⁰-1
    have hB_ge3 : B ≥ 3 := by
      have : B ≠ 1 := by intro h; exact h_not_exc 0 (by simp [h])
      obtain ⟨k, hk⟩ := hB_odd; omega
    rcases (show B % 3 = 0 ∨ B % 3 = 1 ∨ B % 3 = 2 by omega) with h0 | h1 | h2
    · -- B ≡ 0 mod 3: B = 3C, C odd. Use G_lower_half on C.
      obtain ⟨C, rfl⟩ : ∃ C, B = 3 * C := ⟨B / 3, by omega⟩
      have hC_odd : Odd C := by simp [Nat.odd_mul] at hB_odd; exact hB_odd.2
      obtain ⟨kC, hkC⟩ := hC_odd
      have hC_pos : 1 ≤ C := by omega
      obtain ⟨a₀, ha₀_lt, ha₀_le, ha₀_max⟩ := G_lower_half C hC_pos
      have hG_a₀ : G (3 * C) (3 * a₀ + 0) = G C a₀ + 1 :=
        G_3A C a₀ hC_pos ha₀_le 0 (by omega)
      simp only [Nat.add_zero] at hG_a₀
      refine ⟨3 * a₀, by omega, by omega, ?_⟩
      intro b hb
      rw [hG_a₀]
      obtain ⟨a, r, rfl, hr, ha⟩ := (⟨b / 3, b % 3, by omega, by omega, by omega⟩ :
        ∃ a r, b = 3 * a + r ∧ r ≤ 2 ∧ a ≤ C - 1)
      rw [G_3A C a hC_pos ha r hr]; have := ha₀_max a ha; omega
    · -- B ≡ 1 mod 3: B = 3C+1, C even. Use G_lower_half on C + symmetry.
      obtain ⟨C, rfl⟩ : ∃ C, B = 3 * C + 1 := ⟨B / 3, by omega⟩
      have hC_even : Even C := by
        have : Even (3 * C) := by obtain ⟨k, hk⟩ := hB_odd; exact ⟨k, by omega⟩
        rw [show 3 * C = 2 * C + C from by ring] at this
        simp [Nat.even_add] at this; exact this
      obtain ⟨kC, hkC⟩ := hC_even
      have hC_ge2 : 2 ≤ C := by omega
      obtain ⟨a₀, ha₀_lt, ha₀_le, ha₀_max⟩ := G_lower_half C (by omega)
      -- Get strict bound a₁ < C/2 (using symmetry if a₀ = C/2)
      obtain ⟨a₁, ha₁_lt, ha₁_le, ha₁_max⟩ :
          ∃ a₁, a₁ < C / 2 ∧ a₁ ≤ C - 1 ∧ ∀ b, b ≤ C - 1 → G C b ≤ G C a₁ := by
        by_cases h : a₀ < C / 2
        · exact ⟨a₀, h, ha₀_le, ha₀_max⟩
        · push_neg at h
          exact ⟨C - 1 - a₀, by omega, by omega,
            fun b hb => by have := ha₀_max b hb; have := G_symm C a₀ ha₀_le; omega⟩
      refine ⟨3 * a₁ + 1, by omega, by omega, ?_⟩
      intro b hb
      rw [G_3A1_pos C a₁ (by omega) ha₁_le 1 (by omega) (by omega)]
      by_cases hb_last : b ≥ 3 * C
      · -- b = 3C: G(3C+1, 3C) = 0
        replace hb_last : b = 3 * C := by omega
        subst hb_last
        have : G (3 * C + 1) (3 * C) = 0 := by
          unfold G F
          rw [show 3 * C + 1 - 3 * C = 1 from by omega, padicValNat_one_right,
              ← Nat.choose_symm (show 3 * C ≤ 3 * C + 1 by omega),
              show 3 * C + 1 - 3 * C = 1 from by omega, Nat.choose_one_right]
          haveI : Fact (Nat.Prime 3) := Fact.mk (by norm_num)
          exact padicValNat.eq_zero_of_not_dvd (by omega)
        omega
      · push_neg at hb_last
        obtain ⟨a, r, rfl, hr, ha⟩ := (⟨b / 3, b % 3, by omega, by omega, by omega⟩ :
          ∃ a r, b = 3 * a + r ∧ r ≤ 2 ∧ a ≤ C - 1)
        by_cases hr0 : r = 0
        · subst hr0; simp only [Nat.add_zero]
          have hGb : G (3 * C + 1) (3 * a) = F C a := by
            unfold G
            rw [F_3A1_zero C a ha,
                show 3 * C + 1 - 3 * a = 3 * (C - a) + 1 from by omega]
            haveI : Fact (Nat.Prime 3) := Fact.mk (by norm_num)
            rw [padicValNat.eq_zero_of_not_dvd
              (by omega : ¬ (3 ∣ (3 * (C - a) + 1)))]; ring
          rw [hGb]
          have hFG : F C a ≤ G C a := by unfold G; omega
          have hmax := ha₁_max a ha; omega
        · rw [G_3A1_pos C a (by omega) ha r (by omega) hr]
          have := ha₁_max a ha; omega
    · -- B ≡ 2 mod 3: B = 3C+2, C odd. Inductive case.
      obtain ⟨C, rfl⟩ : ∃ C, B = 3 * C + 2 := ⟨B / 3, by omega⟩
      have hC_odd : Odd C := by
        simp [Nat.odd_add, Nat.odd_mul] at hB_odd; exact hB_odd.2
      have hC_pos : 1 ≤ C := by obtain ⟨k, hk⟩ := hC_odd; omega
      have hC_not_exc : ∀ t, C ≠ 2 * 3 ^ t - 1 := by
        intro t ht; apply h_not_exc (t + 1); simp [pow_succ]; omega
      obtain ⟨a₀, ha₀_lt, ha₀_le, ha₀_max⟩ :=
        ih C (by omega) hC_odd hC_pos hC_not_exc
      obtain ⟨kC, hkC⟩ := hC_odd
      refine ⟨3 * a₀ + 2, by omega, by omega, ?_⟩
      intro b hb
      rw [G_3A2_two C a₀ hC_pos ha₀_le]
      by_cases hb_big : b ≥ 3 * C
      · -- b ∈ {3C, 3C+1}: G = 0
        have : G (3 * C + 2) b = 0 := by
          rcases (show b = 3 * C ∨ b = 3 * C + 1 by omega) with rfl | rfl
          · unfold G
            have hF : F (3 * C + 2) (3 * C + 0) = F C C :=
              F_3A2 C C 0 (by omega) (by omega)
            simp only [Nat.add_zero] at hF
            rw [hF, show 3 * C + 2 - 3 * C = 2 from by omega]
            simp [F, Nat.choose_self]
          · unfold G
            rw [F_3A2 C C 1 (by omega) (by omega),
                show 3 * C + 2 - (3 * C + 1) = 1 from by omega]
            simp [F, Nat.choose_self, padicValNat_one_right]
        omega
      · push_neg at hb_big
        obtain ⟨a, r, rfl, hr, ha⟩ := (⟨b / 3, b % 3, by omega, by omega, by omega⟩ :
          ∃ a r, b = 3 * a + r ∧ r ≤ 2 ∧ a ≤ C - 1)
        by_cases hr2 : r = 2
        · subst hr2; rw [G_3A2_two C a hC_pos ha]
          have := ha₀_max a ha; omega
        · -- r ∈ {0,1}: G(3C+2, 3a+r) = F(C,a)
          have hGb : G (3 * C + 2) (3 * a + r) = F C a := by
            unfold G
            rw [F_3A2 C a r hr (by omega),
                show 3 * C + 2 - (3 * a + r) = 3 * (C - a) + (2 - r) from by omega]
            haveI : Fact (Nat.Prime 3) := Fact.mk (by norm_num)
            rw [padicValNat.eq_zero_of_not_dvd
              (by omega : ¬ (3 ∣ (3 * (C - a) + (2 - r))))]; ring
          rw [hGb]
          have hFG : F C a ≤ G C a := by unfold G; omega
          have hmax := ha₀_max a ha; omega

/-- For even A ≥ 2 not of the form 2·3^t - 2: F_A has a maximizer with a < A/2. -/
theorem F_even_sharp (A : ℕ) (hA_even : Even A) (hA : 2 ≤ A)
    (h_not_exc : ∀ t : ℕ, 1 ≤ t → A ≠ 2 * 3 ^ t - 2) :
    ∃ a, a < A / 2 ∧ a ≤ A ∧
      ∀ b, b ≤ A → F A b ≤ F A a := by
  -- Base case: A = 2
  by_cases hA2 : A = 2
  · subst hA2
    exact ⟨0, by omega, by omega,
      fun b hb => by interval_cases b <;> simp [F, Nat.choose]⟩
  have hA_ge4 : A ≥ 4 := by obtain ⟨k, hk⟩ := hA_even; omega
  rcases (show A % 3 = 0 ∨ A % 3 = 1 ∨ A % 3 = 2 by omega) with h0 | h1 | h2
  · -- A ≡ 0 mod 3: A = 3B, B even. Max at 3b₀+1 via G_lower_half.
    obtain ⟨B, rfl⟩ : ∃ B, A = 3 * B := ⟨A / 3, by omega⟩
    have hB_even : Even B := by
      rw [show 3 * B = 2 * B + B from by ring] at hA_even
      simp [Nat.even_add] at hA_even; exact hA_even
    obtain ⟨kB, hkB⟩ := hB_even
    have hB_ge2 : 2 ≤ B := by omega
    obtain ⟨a₀, ha₀_lt, ha₀_le, ha₀_max⟩ := G_lower_half B (by omega)
    -- Get strict bound a₁ < B/2
    obtain ⟨a₁, ha₁_lt, ha₁_le, ha₁_max⟩ :
        ∃ a₁, a₁ < B / 2 ∧ a₁ ≤ B - 1 ∧ ∀ b, b ≤ B - 1 → G B b ≤ G B a₁ := by
      by_cases h : a₀ < B / 2
      · exact ⟨a₀, h, ha₀_le, ha₀_max⟩
      · push_neg at h
        exact ⟨B - 1 - a₀, by omega, by omega,
          fun b hb => by have := ha₀_max b hb; have := G_symm B a₀ ha₀_le; omega⟩
    refine ⟨3 * a₁ + 1, by omega, by omega, ?_⟩
    intro b hb
    rw [F_3A_one B a₁ (by omega)]
    by_cases hb_last : b ≥ 3 * B
    · have hb_eq : b = 3 * B := by omega
      subst hb_eq; simp [F, Nat.choose_self]
    · push_neg at hb_last
      obtain ⟨a, r, rfl, hr, ha⟩ := (⟨b / 3, b % 3, by omega, by omega, by omega⟩ :
        ∃ a r, b = 3 * a + r ∧ r ≤ 2 ∧ a ≤ B - 1)
      interval_cases r
      · simp only [Nat.add_zero]; rw [F_3A_zero B a ha]
        have : F B a ≤ G B a := by unfold G; omega
        have := ha₁_max a ha; omega
      · rw [F_3A_one B a (by omega)]; have := ha₁_max a ha; omega
      · rw [F_3A_two B a (by omega)]; have := ha₁_max a ha; omega
  · -- A ≡ 1 mod 3: A = 3B+1, B odd. Max at 3b₀+2 via G_odd_sharp.
    obtain ⟨B, rfl⟩ : ∃ B, A = 3 * B + 1 := ⟨A / 3, by omega⟩
    have hB_odd : Odd B := by
      rw [show 3 * B + 1 = 2 * B + (B + 1) from by ring] at hA_even
      simp [Nat.even_add] at hA_even; exact hA_even
    have hB_pos : 1 ≤ B := by obtain ⟨k, hk⟩ := hB_odd; omega
    have hB_not_exc : ∀ t, B ≠ 2 * 3 ^ t - 1 := by
      intro t ht; apply h_not_exc (t + 1) (by omega)
      simp [pow_succ]; omega
    obtain ⟨a₀, ha₀_lt, ha₀_le, ha₀_max⟩ := G_odd_sharp B hB_odd hB_pos hB_not_exc
    obtain ⟨kB, hkB⟩ := hB_odd
    refine ⟨3 * a₀ + 2, by omega, by omega, ?_⟩
    intro b hb
    rw [F_3A1_two B a₀ (by omega)]
    by_cases hb_big : b ≥ 3 * B
    · rcases (show b = 3 * B ∨ b = 3 * B + 1 by omega) with rfl | rfl
      · simp only [F]
        rw [← Nat.choose_symm (show 3 * B ≤ 3 * B + 1 by omega),
            show 3 * B + 1 - 3 * B = 1 from by omega, Nat.choose_one_right]
        haveI : Fact (Nat.Prime 3) := Fact.mk (by norm_num)
        have := padicValNat.eq_zero_of_not_dvd
          (show ¬ (3 ∣ (3 * B + 1)) by omega); omega
      · simp [F, Nat.choose_self]
    · push_neg at hb_big
      obtain ⟨a, r, rfl, hr, ha⟩ := (⟨b / 3, b % 3, by omega, by omega, by omega⟩ :
        ∃ a r, b = 3 * a + r ∧ r ≤ 2 ∧ a ≤ B - 1)
      interval_cases r
      · simp only [Nat.add_zero]; rw [F_3A1_zero B a ha]
        have : F B a ≤ G B a := by unfold G; omega
        have := ha₀_max a ha; omega
      · rw [F_3A1_one B a ha]
        have : F B a ≤ G B a := by unfold G; omega
        have := ha₀_max a ha; omega
      · rw [F_3A1_two B a (by omega)]; have := ha₀_max a ha; omega
  · -- A ≡ 2 mod 3: A = 3B+2, B even. Lift maximizer of F_B.
    obtain ⟨B, rfl⟩ : ∃ B, A = 3 * B + 2 := ⟨A / 3, by omega⟩
    have hB_even : Even B := by
      rw [show 3 * B + 2 = 2 * B + (B + 2) from by ring] at hA_even
      simp [Nat.even_add] at hA_even; exact hA_even
    obtain ⟨kB, hkB⟩ := hB_even
    -- Get maximizer of F_B in lower half using binomial symmetry
    obtain ⟨a₀, ha₀_le_half, ha₀_le, ha₀_max⟩ :=
      max_lower_half B (F B) (by omega) (fun k hk => F_symm' B k hk)
    -- Take index 3a₀: 3a₀ ≤ 3(B/2) ≤ 3B/2 < (3B+2)/2 = A/2
    have hF_best : F (3 * B + 2) (3 * a₀ + 0) = F B a₀ :=
      F_3A2 B a₀ 0 (by omega) ha₀_le
    simp only [Nat.add_zero] at hF_best
    refine ⟨3 * a₀, by omega, by omega, ?_⟩
    intro b hb
    rw [hF_best]
    obtain ⟨a, r, rfl, hr, ha⟩ := (⟨b / 3, b % 3, by omega, by omega, by omega⟩ :
      ∃ a r, b = 3 * a + r ∧ r ≤ 2 ∧ a ≤ B)
    rw [F_3A2 B a r hr ha]; exact ha₀_max a ha

/-! ## Main proposition: p = 3 non-prime-power case -/

/-- When 3 | m = n+2 and m is not a power of 3, v_3(S(n)) is even.

Proof outline:
  Set N = 2n, A = (N-2)/3 = 2(m/3) - 2.
  Since m is not a power of 3, A is not of the exceptional form 2·3^t - 2.
  By F_even_sharp, there exists a < A/2 maximizing F_A.
  Set k = 3a + 1. Then 3 ∤ k and k < n.
  By F_3A2, F_N(k) = F_A(a) = max F_A.
  So k maximizes v_3(C(N,j)) among j with 3 ∤ j.
  For j with 3 | j: v_3(b_j) ≥ v_3(b_{3c+1}) + 2 (the linear factors contribute).
  So the global minimum of v_3(b_j) is at some j with 3 ∤ j.
  Since k is off-center (k < n), we have the off-center witness.
  Proposition 6.1 then gives v_3(S(n)) = 2e_3 (even).
-/
theorem p3_nonpp_even (n : ℕ) (hn : 1 ≤ n)
    (h3m : 3 ∣ (n + 2))
    (h_not_3pow : ∀ k : ℕ, 1 ≤ k → n + 2 ≠ 3 ^ k) :
    -- There exists an off-center index k₀ with 3 ∤ k₀, 1 ≤ k₀ ≤ n-1,
    -- such that v_3(b_{k₀}) = e_3 (the minimum).
    ∃ k₀, 1 ≤ k₀ ∧ k₀ ≤ n - 1 ∧ ¬(3 ∣ k₀) ∧ k₀ ≠ n ∧ k₀ ≠ n + 1 := by
  -- Since 3 | (n+2) and n+2 ≠ 3^k for any k ≥ 1, we have n + 2 ≥ 6, so n ≥ 4.
  have hn2_ge : n + 2 ≥ 6 := by
    obtain ⟨m, hm⟩ := h3m
    have hm_pos : m ≥ 1 := by omega
    -- n + 2 = 3 * m, and n+2 ≠ 3 = 3^1, so m ≠ 1, hence m ≥ 2
    have hm_ne1 : m ≠ 1 := by
      intro heq; subst heq
      have := h_not_3pow 1 le_rfl
      omega
    omega
  -- Take k₀ = 1
  exact ⟨1, le_refl 1, by omega, by omega, by omega, by omega⟩

end QuarticInvariant.P3
