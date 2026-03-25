import Mathlib
import Modular.Defs
import Modular.CentralDom

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant


def vp_b (p n k : ℕ) : ℕ := padicValNat p (Int.natAbs (b_k_val n k))

/-! ## Key helper: the numerator product has v_p = 0 for the choose part -/

/-- The ascending product equals t! * C(n+t, t). -/
lemma prod_num_eq (n t : ℕ) :
    ∏ j ∈ Finset.range t, (n + j + 1) = t.factorial * (n + t).choose t := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  rw [Nat.descFactorial_eq_prod_range]; ring
  rw [← Finset.prod_range_reflect]
  refine' Finset.prod_congr rfl fun x hx => by cases t <;> norm_num at * ; omega

/-- The descending product equals t! * C(n, t) when t ≤ n. -/
lemma prod_den_eq (n t : ℕ) (ht : t ≤ n) :
    ∏ j ∈ Finset.range t, (n - j) = t.factorial * n.choose t := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]

/-! ## Lucas' theorem chain: C(p^a*m-1, p^a) ≡ m-1 (mod p)

We prove by induction on a that C(p^a*m - 1, p^a) ≡ m - 1 (mod p).

Base case (a=0): C(m-1, 1) = m-1 ✓
Inductive step: By Lucas' theorem,
  C(p^(a+1)*m-1, p^(a+1)) ≡ C(p-1, 0) * C(p^a*m-1, p^a) ≡ 1 * (m-1) (mod p)

Key computations for the step:
  - (p^(a+1)*m - 1) % p = p - 1  (since p^(a+1)*m ≡ 0 mod p)
  - p^(a+1) % p = 0
  - (p^(a+1)*m - 1) / p = p^a*m - 1
  - p^(a+1) / p = p^a
-/

/-
PROBLEM
C(p^a*m - 1, p^a) ≡ m - 1 (mod p) for any a, m with m ≥ 1.

PROVIDED SOLUTION
Induction on a.

Base case (a = 0): C(1*m - 1, 1) = C(m-1, 1) = m-1. And (m-1) ≡ (m-1) [MOD p]. ✓

Inductive step: Assume C(p^a*m - 1, p^a) ≡ m-1 [MOD p]. Prove C(p^(a+1)*m - 1, p^(a+1)) ≡ m-1 [MOD p].

By Lucas' theorem (Choose.choose_modEq_choose_mod_mul_choose_div_nat):
C(p^(a+1)*m - 1, p^(a+1)) ≡ C((p^(a+1)*m-1) % p, p^(a+1) % p) * C((p^(a+1)*m-1)/p, p^(a+1)/p) [MOD p]

Key computations:
- p^(a+1) % p = 0  (since a+1 ≥ 1)
- (p^(a+1)*m - 1) % p = p - 1  (since p | p^(a+1)*m, so p^(a+1)*m - 1 ≡ -1 ≡ p-1 mod p)
- C(p-1, 0) = 1
- (p^(a+1)*m - 1) / p = p^a*m - 1  (since p^(a+1)*m - 1 = p*(p^a*m) - 1, and integer division gives p^a*m - 1 with remainder p-1)
- p^(a+1) / p = p^a

So C(p^(a+1)*m-1, p^(a+1)) ≡ 1 * C(p^a*m-1, p^a) ≡ m-1 [MOD p] by IH.
-/
lemma choose_pow_mul_sub_one_mod (p : ℕ) [hp : Fact p.Prime] (a : ℕ)
    (m : ℕ) (hm : 1 ≤ m) :
    Nat.choose (p ^ a * m - 1) (p ^ a) ≡ (m - 1) [MOD p] := by
  induction' a with a ih generalizing m <;> simp_all +decide [ pow_succ', mul_assoc ];
  · rfl;
  · have h_lucas : Nat.choose (p * (p ^ a * m) - 1) (p * p ^ a) ≡ Nat.choose (p - 1) 0 * Nat.choose (p ^ a * m - 1) (p ^ a) [MOD p] := by
      convert Choose.choose_modEq_choose_mod_mul_choose_div_nat using 1;
      · rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.add_one_mul_choose_eq ];
        rw [ show ( ( p + 1 + 1 ) * ( ( p + 1 + 1 ) ^ a * m ) - 1 ) / ( p + 1 + 1 ) = ( ( p + 1 + 1 ) ^ a * m - 1 ) from Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by rw [ tsub_lt_iff_left ] <;> nlinarith [ Nat.sub_add_cancel <| show 0 < ( p + 1 + 1 ) ^ a * m from Nat.mul_pos ( pow_pos ( Nat.succ_pos _ ) _ ) ( by linarith ) ] ) ( Nat.le_div_iff_mul_le ( Nat.succ_pos _ ) |>.2 <| Nat.le_sub_one_of_lt <| by nlinarith [ Nat.sub_add_cancel <| show 0 < ( p + 1 + 1 ) ^ a * m from Nat.mul_pos ( pow_pos ( Nat.succ_pos _ ) _ ) ( by linarith ) ] ) ];
      · exact hp;
    simpa using h_lucas.trans ( by simpa using ih m hm )

/-
PROBLEM
C(p^a*(r+1)-2, p^a) ≡ r (mod p), using the above lemma and the Lucas step.

PROVIDED SOLUTION
We have p^a*r - 2 + p^a = p^a*(r+1) - 2.

For a ≥ 1, by Lucas' theorem:
C(p^a*(r+1) - 2, p^a) ≡ C((p^a*(r+1)-2) % p, p^a % p) * C((p^a*(r+1)-2)/p, p^a/p) [MOD p]

Key computations (for a ≥ 1):
- p^a % p = 0
- (p^a*(r+1) - 2) % p = p - 2  (since p | p^a*(r+1), so it's -2 mod p = p-2, which works for p ≥ 3; for p = 2, it's 0)
  Wait, for p = 2: (2^a*(r+1) - 2) % 2 = 0. And C(0, 0) = 1. So it still works.
- C(p-2, 0) = 1 (for p ≥ 3). C(0, 0) = 1 (for p = 2).
- (p^a*(r+1) - 2) / p = p^(a-1)*(r+1) - 1  (for p ≥ 3: quotient of p*Q - 2 where Q = p^(a-1)*(r+1) gives Q - 1 with remainder p-2)
  For p = 2: (2^a*(r+1) - 2)/2 = 2^(a-1)*(r+1) - 1. ✓
- p^a / p = p^(a-1)

So C(p^a*(r+1)-2, p^a) ≡ 1 * C(p^(a-1)*(r+1) - 1, p^(a-1)) [MOD p].

By choose_pow_mul_sub_one_mod with m = r+1 ≥ 3:
C(p^(a-1)*(r+1) - 1, p^(a-1)) ≡ (r+1) - 1 = r [MOD p].

So C(p^a*(r+1)-2, p^a) ≡ r [MOD p].
-/
lemma choose_shift_mod (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (r : ℕ) (hr : 2 ≤ r) :
    Nat.choose (p ^ a * r - 2 + p ^ a) (p ^ a) ≡ r [MOD p] := by
  -- By Lucas' theorem, we have:
  have h_lucas : Nat.choose (p ^ a * (r + 1) - 2) (p ^ a) ≡ Nat.choose ((p ^ a * (r + 1) - 2) % p) (p ^ a % p) * Nat.choose ((p ^ a * (r + 1) - 2) / p) (p ^ a / p) [MOD p] := by
    exact?;
  -- By simplifying, we have:
  have h_simp : Nat.choose ((p ^ a * (r + 1) - 2) % p) (p ^ a % p) * Nat.choose ((p ^ a * (r + 1) - 2) / p) (p ^ a / p) ≡ Nat.choose ((p - 2) % p) 0 * Nat.choose (p ^ (a - 1) * (r + 1) - 1) (p ^ (a - 1)) [MOD p] := by
    rcases a with ( _ | a ) <;> simp_all +decide [ pow_succ, mul_assoc ];
    rw [ show p ^ a * ( p * ( r + 1 ) ) - 2 = p * ( p ^ a * ( r + 1 ) - 1 ) + ( p - 2 ) from ?_, Nat.add_div ] <;> norm_num [ hp.1.pos ];
    · rcases p with ( _ | _ | _ | p ) <;> simp_all +arith +decide [ Nat.div_eq_of_lt ];
      · rfl;
      · rfl;
    · zify;
      rw [ Nat.cast_sub, Nat.cast_sub, Nat.cast_sub ] <;> push_cast <;> nlinarith [ hp.1.two_le, pow_pos hp.1.pos a, mul_pos hp.1.pos ( pow_pos hp.1.pos a ) ];
  -- By the lemma choose_pow_mul_sub_one_mod, we have:
  have h_lemma : Nat.choose (p ^ (a - 1) * (r + 1) - 1) (p ^ (a - 1)) ≡ (r + 1) - 1 [MOD p] := by
    apply choose_pow_mul_sub_one_mod p (a - 1) (r + 1) (by linarith);
  simp_all +decide [ mul_add, ← add_assoc ];
  rw [ tsub_add_eq_add_tsub ( by nlinarith [ pow_pos hp.1.pos a ] ) ] ; exact h_lucas.trans ( h_simp.trans h_lemma ) ;

/-
PROBLEM
Key lemma: C(p^a*(r+1)-2, p^a) is not divisible by p.

PROVIDED SOLUTION
By choose_shift_mod, C(p^a*r-2+p^a, p^a) ≡ r [MOD p]. Since p ∤ r (hrp), we have r % p ≠ 0, so C(p^a*r-2+p^a, p^a) % p ≠ 0, hence ¬ p ∣ C(p^a*r-2+p^a, p^a).

Use Nat.ModEq to relate the congruence to divisibility.
-/
lemma choose_not_dvd (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (r : ℕ) (hr : 2 ≤ r) (hrp : ¬ p ∣ r) :
    ¬ (p ∣ Nat.choose (p ^ a * r - 2 + p ^ a) (p ^ a)) := by
  have := @choose_shift_mod p ?_ a ha r hr; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.dvd_iff_mod_eq_zero ] ;
  · simp_all +decide [ ← ZMod.val_natCast ];
  · exact hp

/-- v_p of C(n+t, t) = 0 under our hypotheses. -/
lemma padicValNat_choose_eq_zero (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (r : ℕ) (hr : 2 ≤ r) (hrp : ¬ p ∣ r) :
    padicValNat p (Nat.choose (p ^ a * r - 2 + p ^ a) (p ^ a)) = 0 := by
  rw [padicValNat.eq_zero_of_not_dvd]
  exact choose_not_dvd p a ha r hr hrp

/--
The binomial ratio ∏_{j=0}^{t-1} (n+j+1)/(n-j) has v_p ≤ 0
when n = p^a · r - 2 and t = p^a.
-/
theorem binom_ratio_vp_le (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (r : ℕ) (hr : 2 ≤ r) (hrp : ¬ p ∣ r) :
    let n := p ^ a * r - 2
    let t := p ^ a
    padicValNat p (∏ j ∈ Finset.range t, (n + j + 1)) ≤
    padicValNat p (∏ j ∈ Finset.range t, (n - j)) := by
  have h_prod_num : ∏ j ∈ Finset.range (p ^ a), ((p ^ a * r - 2) + j + 1) =
      (p ^ a).factorial * Nat.choose ((p ^ a * r - 2) + p ^ a) (p ^ a) := by
    apply prod_num_eq
  have h_prod_den : ∏ j ∈ Finset.range (p ^ a), ((p ^ a * r - 2) - j) =
      (p ^ a).factorial * Nat.choose (p ^ a * r - 2) (p ^ a) := by
    rw [← Nat.descFactorial_eq_prod_range]
    rw [Nat.descFactorial_eq_factorial_mul_choose]
  by_cases h : Nat.choose (p ^ a * r - 2) (p ^ a) = 0 <;>
    simp_all +decide [Nat.factorial_ne_zero, padicValNat.mul]
  · exact absurd h <| Nat.ne_of_gt <| Nat.choose_pos <| Nat.le_sub_of_add_le <| by
      nlinarith [pow_le_pow_right₀ hp.1.one_lt.le ha, Nat.Prime.one_lt hp.1]
  · rw [padicValNat.mul (Nat.factorial_ne_zero _)
        (Nat.ne_of_gt (Nat.choose_pos (by
          nlinarith [pow_pos hp.1.pos a,
            Nat.sub_add_cancel (show 2 ≤ p ^ a * r from by nlinarith [pow_pos hp.1.pos a])])))]
    rw [padicValNat_choose_eq_zero p a ha r hr hrp]; norm_num

/-! ## Helpers for vp_b_witness_bound -/

/-
PROBLEM
Extract that a ≥ 1 when p | (n+2).

PROVIDED SOLUTION
Since p | (n+2) and n+2 ≥ 4 > 0, padicValNat p (n+2) ≥ 1. Use padicValNat.one_le_iff or the fact that p ∣ (n+2) implies v_p(n+2) ≥ 1.
-/
lemma a_ge_one (p n : ℕ) [hp : Fact p.Prime] (hpm : p ∣ (n + 2)) :
    1 ≤ padicValNat p (n + 2) := by
  by_contra hp_lt_1;
  simp_all +decide [ padicValNat.eq_zero_of_not_dvd ]

/-
PROBLEM
Extract that r ≥ 2 when n+2 is not a prime power.

PROVIDED SOLUTION
Let a = padicValNat p (n+2), r = (n+2)/p^a. We know p^a | (n+2) and p^(a+1) ∤ (n+2). So n+2 = p^a * r with p ∤ r. If r = 0 then n+2 = 0, impossible. If r = 1 then n+2 = p^a, contradicting h_not_pp (with k = a, which has a ≥ 1). So r ≥ 2.
-/
lemma r_ge_two (p n : ℕ) [hp : Fact p.Prime] (hn : 2 ≤ n)
    (hpm : p ∣ (n + 2)) (h_not_pp : ∀ k : ℕ, 1 ≤ k → n + 2 ≠ p ^ k) :
    2 ≤ (n + 2) / p ^ padicValNat p (n + 2) := by
  by_contra h_contra;
  interval_cases _ : ( n + 2 ) / p ^ padicValNat p ( n + 2 ) <;> simp_all +decide [ Nat.div_eq_iff_eq_mul_left ( pow_pos hp.1.pos _ ) ];
  · rcases ‹_› with ( ⟨ rfl, h ⟩ | h ) <;> simp_all +decide [ Nat.Prime.pow_eq_iff ];
    contrapose! h;
    rw [ ← Nat.factorization_def ];
    · exact Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.ordProj_dvd _ _ );
    · exact hp.1;
  · have := Nat.div_mul_cancel ( show p ^ padicValNat p ( n + 2 ) ∣ n + 2 from ?_ ) ; simp_all +decide [ Nat.pow_succ' ];
    · exact h_not_pp _ ( Nat.pos_of_ne_zero ( by aesop_cat ) ) this.symm;
    · exact?

/-
PROBLEM
p does not divide r = (n+2)/p^a.

PROVIDED SOLUTION
r = (n+2)/p^a where a = v_p(n+2). If p | r, then p^(a+1) | (n+2), so v_p(n+2) ≥ a+1, contradicting the definition of a. Use Nat.not_dvd_div_pow_padicValNat or similar.
-/
lemma p_not_dvd_r (p n : ℕ) [hp : Fact p.Prime] (hpm : p ∣ (n + 2)) :
    ¬ p ∣ (n + 2) / p ^ padicValNat p (n + 2) := by
  -- By definition of p-adic valuation, $p^{padicValNat p (n + 2)}$ is the highest power of $p$ dividing $n + 2$.
  have h_div : p ^ padicValNat p (n + 2) ∣ n + 2 ∧ ¬p ^ (padicValNat p (n + 2) + 1) ∣ n + 2 := by
    rw [ padicValNat_dvd_iff_le ];
    · rw [ padicValNat_dvd_iff ] ; aesop;
    · grind;
  rw [ Nat.dvd_div_iff_mul_dvd ] <;> tauto

/-
PROBLEM
n = p^a * r - 2

PROVIDED SOLUTION
Since p^a | (n+2), we have n+2 = p^a * r, so n = p^a*r - 2. Use Nat.div_mul_cancel and the fact that p^(padicValNat p (n+2)) dvd (n+2).
-/
lemma n_eq_par_minus_two (p n : ℕ) [hp : Fact p.Prime] (hpm : p ∣ (n + 2)) :
    n = p ^ padicValNat p (n + 2) * ((n + 2) / p ^ padicValNat p (n + 2)) - 2 := by
  rw [ Nat.mul_div_cancel' ];
  · rfl;
  · exact?

/-
PROBLEM
p^a ≤ n when a ≥ 1 and n = p^a * r - 2 with r ≥ 2.

PROVIDED SOLUTION
n = p^a * r - 2 with r ≥ 2. So n ≥ 2*p^a - 2 ≥ p^a (since p^a ≥ 2). Use r_ge_two and n_eq_par_minus_two.
-/
lemma pa_le_n (p n : ℕ) [hp : Fact p.Prime] (hn : 2 ≤ n)
    (hpm : p ∣ (n + 2)) (h_not_pp : ∀ k : ℕ, 1 ≤ k → n + 2 ≠ p ^ k) :
    p ^ padicValNat p (n + 2) ≤ n := by
  -- By definition of $a$ and $r$, we know that $n = p^a * r - 2$ where $r \geq 2$.
  have hn_eq : n = p ^ padicValNat p (n + 2) * ((n + 2) / p ^ padicValNat p (n + 2)) - 2 := by
    exact?;
  rw [ eq_tsub_iff_add_eq_of_le ] at hn_eq;
  · by_contra h_contra;
    exact h_not_pp ( padicValNat p ( n + 2 ) ) ( Nat.pos_of_ne_zero fun h => by simp_all +singlePass ) ( by nlinarith [ show ( n + 2 ) / p ^ padicValNat p ( n + 2 ) = 1 by nlinarith ] );
  · exact Nat.le_of_not_lt fun h => by rw [ tsub_eq_zero_iff_le.mpr h.le ] at hn_eq; linarith;

/-- The numerator of b_k_val (before division by C(2n,k)) for p-adic purposes.
We define it as a natural number: 2 * (2n)!^2 * |2n+1-k| * |2n+1-2k|. -/
def bk_num (n k : ℕ) : ℕ :=
  2 * ((2 * n).factorial) ^ 2 * Int.natAbs ((2 * n : ℤ) + 1 - k) *
    Int.natAbs ((2 * n : ℤ) + 1 - 2 * k)

/-
PROBLEM
C(2n, k) divides bk_num n k.

PROVIDED SOLUTION
C(2n, k) divides (2n)! since C(2n, k) * k! * (2n-k)! = (2n)!. Hence C(2n,k) divides (2n)!^2. Therefore C(2n,k) divides 2 * (2n)!^2 * anything.

More precisely: bk_num n k = 2 * (2n)!^2 * |2n+1-k| * |2n+1-2k|. Since C(2n,k) | (2n)!, and (2n)! | (2n)!^2, we get C(2n,k) | (2n)!^2. Then C(2n,k) | 2*(2n)!^2*anything by dvd_mul_right.
-/
lemma choose_dvd_bk_num (n k : ℕ) (hk : k ≤ 2 * n) :
    Nat.choose (2 * n) k ∣ bk_num n k := by
  have h_choose_div : Nat.choose (2 * n) k ∣ Nat.factorial (2 * n) := by
    rw [ Nat.choose_eq_factorial_div_factorial hk ];
    exact Nat.div_dvd_of_dvd <| Nat.factorial_mul_factorial_dvd_factorial hk;
  exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( dvd_pow h_choose_div two_ne_zero ) _ ) _ ) _

/-
PROBLEM
vp_b equals v_p(bk_num) - v_p(C(2n,k)).

PROVIDED SOLUTION
Unfold vp_b and b_k_val.

b_k_val n k = (2 * (-1)^k * (2n)!^2 * (2n+1-k) * (2n+1-2k)) / C(2n,k) as an integer.

The numerator in absolute value is bk_num n k (since |(-1)^k| = 1).

So |b_k_val n k| = bk_num n k / C(2n,k) as natural numbers.

Then vp_b p n k = padicValNat p (bk_num n k / C(2n,k)).

By padicValNat.div_of_dvd (since C(2n,k) | bk_num n k by choose_dvd_bk_num):
= padicValNat p (bk_num n k) - padicValNat p (C(2n,k)).

Key steps:
1. Show Int.natAbs (b_k_val n k) = bk_num n k / C(2n, k)
2. Apply padicValNat.div_of_dvd

For step 1: b_k_val n k = N / D where N = 2*(-1)^k*(2n)!^2*(2n+1-k)*(2n+1-2k) and D = C(2n,k).
|N| = 2*(2n)!^2*|2n+1-k|*|2n+1-2k| = bk_num n k (as integers).
|N/D| = |N|/|D| = bk_num n k / C(2n,k) since D > 0 and D | |N|.
-/
lemma vp_b_eq (p n k : ℕ) [hp : Fact p.Prime] (hk : k ≤ 2 * n) :
    vp_b p n k = padicValNat p (bk_num n k) - padicValNat p (Nat.choose (2 * n) k) := by
  unfold vp_b bk_num b_k_val;
  rw [ Int.natAbs_ediv ];
  split_ifs <;> simp_all +decide [ Int.natAbs_mul, Int.natAbs_pow ];
  · rw [ padicValNat.div_of_dvd ];
    convert choose_dvd_bk_num n k hk using 1;
  · rename_i h;
    refine' False.elim ( h.2.2 _ );
    -- By definition of binomial coefficients, $\binom{2n}{k}$ divides $(2n)!$.
    have h_binom_div : (Nat.choose (2 * n) k : ℤ) ∣ (2 * n)! := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk ▸ dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _;
    exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( h_binom_div.pow two_ne_zero ) _ ) _ ) _

/-
PROBLEM
v_p(n+1) = 0 when p | (n+2) and p ≥ 2. Because n+1 = p^a*r - 1 ≡ -1 mod p.

PROVIDED SOLUTION
n+1 = (n+2) - 1. Since p | (n+2), we have n+2 ≡ 0 mod p, so n+1 ≡ -1 mod p. Since p ≥ 2, -1 mod p ≠ 0, so p ∤ (n+1). Hence padicValNat p (n+1) = 0.

Use Nat.sub_one_not_dvd or show directly: if p | (n+1) and p | (n+2), then p | 1, contradiction since p ≥ 2.
-/
lemma vp_n_plus_one_eq_zero (p n : ℕ) [hp : Fact p.Prime] (hpm : p ∣ (n + 2)) :
    padicValNat p (n + 1) = 0 := by
  by_contra h_contra
  have h_div : p ∣ n + 1 ∧ p ∣ n + 2 := by
    simp_all +decide [ padicValNat.eq_zero_iff ]
  have h_contra' : p ∣ 1 := by
    simpa using Nat.dvd_sub h_div.2 h_div.1
  have h_contra'' : p = 1 := by
    exact Nat.eq_one_of_dvd_one h_contra'
  exact hp.1.ne_one h_contra''

/-
PROBLEM
v_p(n+1+p^a) = 0 when p | (n+2). Because n+1+p^a = p^a*(r+1)-1 ≡ -1 mod p.

PROVIDED SOLUTION
n+1+p^a = (n+2) + p^a - 1 = p^a*r + p^a - 1 = p^a*(r+1) - 1 ≡ -1 mod p. Since p ≥ 2, p ∤ (p^a*(r+1)-1). So padicValNat p (n+1+p^a) = 0.

Key: p | p^a and p | p^a*r, so p | (n+2) = p^a*r. Hence p | (n+1+p^a+1) = (n+2+p^a) = p^a*(r+1). So n+1+p^a = p^a*(r+1) - 1 ≡ -1 mod p.

If p | (n+1+p^a) then p | (n+1+p^a) and p | p^a, so p | (n+1). But we just showed p ∤ (n+1). Contradiction.
-/
lemma vp_n_plus_one_plus_pa_eq_zero (p n : ℕ) [hp : Fact p.Prime] (hpm : p ∣ (n + 2)) :
    padicValNat p (n + 1 + p ^ padicValNat p (n + 2)) = 0 := by
  -- Since $p \mid (n + 2)$, we have $n + 2 = p^a * r$ where $r$ is not divisible by $p$.
  obtain ⟨a, r, ha, hr⟩ : ∃ a r : ℕ, n + 2 = p ^ a * r ∧ ¬p ∣ r := by
    exact ⟨ Nat.factorization ( n + 2 ) p, ( n + 2 ) / p ^ Nat.factorization ( n + 2 ) p, by rw [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ], Nat.not_dvd_ordCompl ( by simp +decide [ hp.1 ] ) ( by simp +decide [ hp.1 ] ) ⟩;
  -- Substitute $n + 2 = p^a * r$ into $n + 1 + p^a$.
  have h_sub : n + 1 + p ^ padicValNat p (n + 2) = p ^ a * (r + 1) - 1 := by
    rw [ show padicValNat p ( n + 2 ) = a from _ ];
    · exact eq_tsub_of_add_eq ( by linarith );
    · rw [ ha, padicValNat.mul ] <;> aesop;
  haveI := Fact.mk hp.1; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Nat.cast_sub ( show 0 < p ^ a * ( r + 1 ) from Nat.mul_pos ( pow_pos hp.1.pos _ ) ( Nat.succ_pos _ ) ) ] ;

/-
PROBLEM
v_p(2*p^a + 1) = 0 when p ≥ 3. Because 2*p^a+1 ≡ 1 mod p.

PROVIDED SOLUTION
2*p^a + 1 ≡ 0 + 1 = 1 mod p (since p | p^a so p | 2*p^a). Since p ≥ 3, 1 mod p = 1 ≠ 0. So p ∤ (2*p^a + 1) and padicValNat p (2*p^a+1) = 0.
-/
lemma vp_two_pa_plus_one_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp3 : 3 ≤ p) (a : ℕ) (ha : 1 ≤ a) :
    padicValNat p (2 * p ^ a + 1) = 0 := by
  rw [ padicValNat.eq_zero_of_not_dvd ];
  rw [ Nat.dvd_add_right ( dvd_mul_of_dvd_right ( dvd_pow_self _ ( by linarith ) ) _ ) ] ; exact Nat.not_dvd_of_pos_of_lt ( by positivity ) ( by linarith ) ;

/-
PROBLEM
The off-center witness k₀ = n - p^a has v_p(b_{k₀}) ≤ v_p(b_n).
This uses binom_ratio_vp_le and the fact that the linear factors
(N+1-k) and (N+1-2k) contribute v_p = 0 at both k = n and k = k₀.

PROVIDED SOLUTION
Let a = padicValNat p (n+2), r = (n+2)/p^a, k₀ = n - p^a.

Step 1: Extract parameters.
- a ≥ 1 by a_ge_one
- r ≥ 2 by r_ge_two
- p ∤ r by p_not_dvd_r
- n = p^a*r - 2 by n_eq_par_minus_two
- p^a ≤ n by pa_le_n

Step 2: Apply vp_b_eq to both sides. For k₀ = n - p^a ≤ n ≤ 2n, and for k = n ≤ 2n:
  vp_b p n k₀ = padicValNat p (bk_num n k₀) - padicValNat p C(2n, k₀)
  vp_b p n n = padicValNat p (bk_num n n) - padicValNat p C(2n, n)

Step 3: Show padicValNat p (bk_num n k₀) = padicValNat p (bk_num n n).
bk_num n k₀ = 2 * (2n)!^2 * |2n+1-k₀| * |2n+1-2k₀|
            = 2 * (2n)!^2 * (n+1+p^a) * (2p^a+1)
bk_num n n = 2 * (2n)!^2 * (n+1) * 1
           = 2 * (2n)!^2 * (n+1)

Since v_p(n+1+p^a) = 0 (by vp_n_plus_one_plus_pa_eq_zero), v_p(2p^a+1) = 0 (by vp_two_pa_plus_one_eq_zero), v_p(n+1) = 0 (by vp_n_plus_one_eq_zero), and v_p(1) = 0:

padicValNat p (bk_num n k₀) = padicValNat p 2 + 2*padicValNat p (2n)! + 0 + 0
                              = padicValNat p 2 + 2*padicValNat p (2n)!
padicValNat p (bk_num n n)  = padicValNat p 2 + 2*padicValNat p (2n)! + 0 + 0
                              = padicValNat p 2 + 2*padicValNat p (2n)!

So they're equal: padicValNat p (bk_num n k₀) = padicValNat p (bk_num n n).

Step 4: Show padicValNat p C(2n, k₀) ≥ padicValNat p C(2n, n).
By binom_ratio_vp_le:
  padicValNat p (∏ j, (n+j+1)) ≤ padicValNat p (∏ j, (n-j))
Using prod_num_eq and prod_den_eq:
  padicValNat p (t! * C(n+t, t)) ≤ padicValNat p (t! * C(n, t))

But we actually need C(2n, k₀) vs C(2n, n). Note that C(2n, n-t) = C(2n, n+t) by symmetry C(2n, k) = C(2n, 2n-k) where 2n - (n-t) = n+t. And C(2n, n)/C(2n, n-t) = ∏(n+j+1)/∏(n-j).

Actually, by binom_ratio_vp_le with the rewritten products:
padicValNat p (t!*C(n+t,t)) ≤ padicValNat p (t!*C(n,t))

Since t! = p^a factorial is common (by padicValNat.mul):
padicValNat p t! + padicValNat p C(n+t,t) ≤ padicValNat p t! + padicValNat p C(n,t)
Hence padicValNat p C(n+t,t) ≤ padicValNat p C(n,t).

But C(n+t,t) = C(2n-2+p^a, p^a) = C(2n-2+p^a, 2n-2), which is NOT the same as C(2n, n). Wait, n+t = n + p^a, and t = p^a.

Actually the connection to C(2n, k) is different. The ratio C(2n, n)/C(2n, n-p^a) = ∏(n+j+1)/∏(n-j). So from binom_ratio_vp_le, v_p(numerator_product) ≤ v_p(denominator_product), meaning v_p(C(2n,n)/C(2n,n-p^a)) ≤ 0, i.e., v_p(C(2n,n)) ≤ v_p(C(2n,n-p^a)).

So padicValNat p C(2n, n) ≤ padicValNat p C(2n, n-p^a) = padicValNat p C(2n, k₀).

Step 5: Combine:
vp_b(k₀) = padicValNat p (bk_num n k₀) - padicValNat p C(2n, k₀)
vp_b(n) = padicValNat p (bk_num n n) - padicValNat p C(2n, n)

Since padicValNat p (bk_num n k₀) = padicValNat p (bk_num n n) (Step 3)
and padicValNat p C(2n, k₀) ≥ padicValNat p C(2n, n) (Step 4):
vp_b(k₀) ≤ vp_b(n). ✓

This uses Nat.sub_le_sub_left for ℕ subtraction.
-/
theorem vp_b_witness_bound (p n : ℕ)
    [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hn : 2 ≤ n)
    (hpm : p ∣ (n + 2)) (h_not_pp : ∀ k : ℕ, 1 ≤ k → n + 2 ≠ p ^ k) :
    vp_b p n (n - p ^ padicValNat p (n + 2)) ≤ vp_b p n n := by
  rw [ vp_b_eq, vp_b_eq ];
  · -- By Lemma 2, the denominator divides the numerator.
    have h_denom_div_num : padicValNat p (Nat.choose (2 * n) (n - p ^ padicValNat p (n + 2))) ≥ padicValNat p (Nat.choose (2 * n) n) := by
      -- By the properties of binomial coefficients, we know that $\frac{\binom{2n}{n}}{\binom{2n}{n-p^a}} = \frac{(n+1)(n+2)\cdots(2n)}{(n-p^a+1)(n-p^a+2)\cdots(2n-p^a)}$.
      have h_binom_ratio : (Nat.choose (2 * n) n : ℚ) / (Nat.choose (2 * n) (n - p ^ padicValNat p (n + 2)) : ℚ) = (∏ j ∈ Finset.range (p ^ padicValNat p (n + 2)), (n + j + 1 : ℚ)) / (∏ j ∈ Finset.range (p ^ padicValNat p (n + 2)), (n - j : ℚ)) := by
        -- By definition of binomial coefficients, we can write
        have h_binom_def : (Nat.choose (2 * n) n : ℚ) = (Nat.factorial (2 * n)) / (Nat.factorial n * Nat.factorial n) ∧ (Nat.choose (2 * n) (n - p ^ padicValNat p (n + 2)) : ℚ) = (Nat.factorial (2 * n)) / (Nat.factorial (n - p ^ padicValNat p (n + 2)) * Nat.factorial (n + p ^ padicValNat p (n + 2))) := by
          constructor <;> rw [ Nat.cast_choose ];
          · rw [ two_mul, add_tsub_cancel_left ];
          · linarith;
          · rw [ show 2 * n - ( n - p ^ padicValNat p ( n + 2 ) ) = n + p ^ padicValNat p ( n + 2 ) by rw [ Nat.sub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( show p ^ padicValNat p ( n + 2 ) ≤ n from by exact Nat.le_of_lt_succ <| by { have := pa_le_n p n hn hpm h_not_pp; linarith } ) ] ];
          · exact le_trans ( Nat.sub_le _ _ ) ( by linarith );
        -- By definition of factorial, we can write
        have h_factorial_def : (Nat.factorial n : ℚ) = (∏ j ∈ Finset.range (p ^ padicValNat p (n + 2)), (n - j : ℚ)) * (Nat.factorial (n - p ^ padicValNat p (n + 2)) : ℚ) ∧ (Nat.factorial (n + p ^ padicValNat p (n + 2)) : ℚ) = (∏ j ∈ Finset.range (p ^ padicValNat p (n + 2)), (n + j + 1 : ℚ)) * (Nat.factorial n : ℚ) := by
          constructor;
          · have h_factorial_def : ∀ m ≤ n, (Nat.factorial n : ℚ) = (∏ j ∈ Finset.range m, (n - j : ℚ)) * (Nat.factorial (n - m) : ℚ) := by
              intro m hm; induction' m with m ih <;> simp_all +decide [ Finset.prod_range_succ, Nat.factorial ] ; ring;
              rw [ ih ( Nat.le_of_lt hm ) ] ; rw [ show n - m = n - ( 1 + m ) + 1 by omega ] ; push_cast [ Nat.factorial_succ ] ; ring;
              rw [ Nat.cast_sub ( by linarith ) ] ; push_cast ; ring;
            exact h_factorial_def _ ( by linarith [ pa_le_n p n hn hpm h_not_pp ] );
          · induction' p ^ padicValNat p ( n + 2 ) with k hk <;> simp_all +decide [ Nat.factorial, Finset.prod_range_succ ] ; ring;
        rw [ h_binom_def.1, h_binom_def.2, div_div_eq_mul_div ];
        rw [ div_mul_eq_mul_div, div_div, div_eq_div_iff ] <;> first | positivity | push_cast [ h_factorial_def ] ; ring;
        exact Finset.prod_ne_zero_iff.mpr fun x hx => sub_ne_zero_of_ne <| by norm_cast; linarith [ Finset.mem_range.mp hx, show p ^ padicValNat p ( 2 + n ) ≤ n from by simpa only [ add_comm ] using pa_le_n p n ( by simpa only [ add_comm ] using hn ) ( by simpa only [ add_comm ] using hpm ) ( by simpa only [ add_comm ] using h_not_pp ) ] ;
      -- By the properties of p-adic valuations, we can separate the p-adic valuations of the numerator and the denominator.
      have h_padic_val : padicValRat p ((∏ j ∈ Finset.range (p ^ padicValNat p (n + 2)), (n + j + 1 : ℚ)) / (∏ j ∈ Finset.range (p ^ padicValNat p (n + 2)), (n - j : ℚ))) ≤ 0 := by
        have h_padic_val : (∏ j ∈ Finset.range (p ^ padicValNat p (n + 2)), (n + j + 1 : ℕ)).factorization p ≤ (∏ j ∈ Finset.range (p ^ padicValNat p (n + 2)), (n - j : ℕ)).factorization p := by
          convert binom_ratio_vp_le p ( padicValNat p ( n + 2 ) ) ( by linarith [ a_ge_one p n hpm ] ) ( ( n + 2 ) / p ^ padicValNat p ( n + 2 ) ) ( by linarith [ r_ge_two p n hn hpm h_not_pp ] ) ( by exact p_not_dvd_r p n hpm ) using 1;
          · rw [ ← n_eq_par_minus_two p n hpm ];
            rw [ Nat.factorization_def ];
            exact hp.1;
          · rw [ ← n_eq_par_minus_two p n hpm ];
            rw [ Nat.factorization_def ];
            exact hp.1;
        have h_padic_val : padicValRat p ((∏ j ∈ Finset.range (p ^ padicValNat p (n + 2)), (n + j + 1 : ℕ)) : ℚ) ≤ padicValRat p ((∏ j ∈ Finset.range (p ^ padicValNat p (n + 2)), (n - j : ℕ)) : ℚ) := by
          norm_cast;
          rw [ Nat.factorization_def, Nat.factorization_def ] at h_padic_val ; aesop;
          · exact hp.1;
          · exact hp.1;
        convert sub_nonpos_of_le h_padic_val using 1;
        convert padicValRat.div _ _ using 1;
        · norm_cast;
          rw [ Int.subNatNat_eq_coe ] ; norm_num [ padicValRat.of_nat ];
          rw [ ← padicValRat.of_nat ];
          rw [ Nat.cast_prod ];
          exact congr_arg _ ( Finset.prod_congr rfl fun x hx => by rw [ Nat.cast_sub ( show x ≤ n from le_trans ( Finset.mem_range_le hx ) ( Nat.le_of_lt_succ ( by linarith [ show p ^ padicValNat p ( n + 2 ) ≤ n from pa_le_n p n hn hpm h_not_pp ] ) ) ) ] );
        · exact ⟨ hp.1 ⟩;
        · exact Finset.prod_ne_zero_iff.mpr fun _ _ => by positivity;
        · exact Finset.prod_ne_zero_iff.mpr fun x hx => sub_ne_zero_of_ne <| by norm_cast; linarith [ Finset.mem_range.mp hx, show p ^ padicValNat p ( n + 2 ) ≤ n from pa_le_n p n hn hpm h_not_pp ] ;
      contrapose! h_padic_val;
      rw [ ← h_binom_ratio, padicValRat.div ] <;> norm_num;
      · convert h_padic_val using 1;
      · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
      · exact Nat.ne_of_gt <| Nat.choose_pos <| Nat.sub_le_of_le_add <| by linarith [ Nat.pow_le_pow_right hp.1.one_lt.le <| show padicValNat p ( n + 2 ) ≥ 1 from a_ge_one p n hpm ] ;
    -- By Lemma 3, the numerator parts are equal.
    have h_num_eq : padicValNat p (bk_num n (n - p ^ padicValNat p (n + 2))) = padicValNat p (bk_num n n) := by
      -- By Lemma 3, the linear factors (N+1-k) and (N+1-2k) contribute v_p = 0 at both k = n and k = k₀.
      have h_linear_factors : padicValNat p (n + 1 + p ^ padicValNat p (n + 2)) = 0 ∧ padicValNat p (2 * p ^ padicValNat p (n + 2) + 1) = 0 ∧ padicValNat p (n + 1) = 0 := by
        exact ⟨ vp_n_plus_one_plus_pa_eq_zero p n ( by simpa using hpm ), vp_two_pa_plus_one_eq_zero p ( by linarith ) _ ( a_ge_one p n ( by simpa using hpm ) ), vp_n_plus_one_eq_zero p n ( by simpa using hpm ) ⟩;
      have h_num_eq : bk_num n (n - p ^ padicValNat p (n + 2)) = 2 * ((2 * n).factorial) ^ 2 * (n + 1 + p ^ padicValNat p (n + 2)) * (2 * p ^ padicValNat p (n + 2) + 1) := by
        unfold bk_num;
        rw [ Nat.cast_sub ] <;> push_cast <;> ring;
        · norm_cast ; ring;
        · convert pa_le_n p n hn ( by simpa only [ add_comm ] using hpm ) ( by simpa only [ add_comm ] using h_not_pp ) using 1 ; ring;
      simp_all +decide [ mul_assoc, padicValNat.mul, Nat.factorial_ne_zero ];
      unfold bk_num; simp +decide [ *, padicValNat.mul, Nat.factorial_ne_zero ] ;
      rw [ show ( 2 * n + 1 - n : ℤ ) = n + 1 by ring ] ; norm_cast ; simp +decide [ *, padicValNat.mul, Nat.factorial_ne_zero ] ;
      rw [ padicValNat.eq_zero_of_not_dvd ( show ¬ p ∣ n + 1 + p ^ padicValNat p ( n + 2 ) from by aesop ), padicValNat.eq_zero_of_not_dvd ( show ¬ p ∣ 2 * p ^ padicValNat p ( n + 2 ) + 1 from by aesop ), padicValNat.eq_zero_of_not_dvd ( show ¬ p ∣ n + 1 from by aesop ) ] ; ring;
    exact h_num_eq.symm ▸ Nat.sub_le_sub_left h_denom_div_num _;
  · linarith;
  · exact le_trans ( Nat.sub_le _ _ ) ( by linarith )

end QuarticInvariant
