import Mathlib
import Modular.Defs

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant


theorem α_at_n (n : ℕ) : α n n = γ n := by
  simp [α, γ, show 2 * n + 1 - n = n + 1 from by omega]

theorem β_at_n (n : ℕ) : β n n = γ n := by
  unfold β γ; rw [show 2 * n - n = n from by omega, mul_comm]

/-! ## Simplified scalar formulas -/

/-
PROVIDED SOLUTION
Unfold scalar_AB, α, β. Rearrange so that C(2n,i) * i! * (2n-i)! appears as a factor; by Nat.choose_mul_factorial_mul_factorial this equals (2n)!. The remaining factors are (2n+1-i)! * (i+1)!.
-/
theorem scalar_AB_formula (n i : ℕ) (hi : i ≤ 2 * n) :
    scalar_AB n i = (2 * n).factorial * (2 * n + 1 - i).factorial * (i + 1).factorial := by
  unfold scalar_AB α β;
  rw [ ← Nat.choose_mul_factorial_mul_factorial hi ] ; ring;

/-
PROVIDED SOLUTION
Unfold scalar_A2, α. Use (2n+1-i)! = (2n+1-i) * (2n-i)! (Nat.factorial_succ applied to 2n-i, noting 2n+1-i = (2n-i)+1 when i ≤ 2n). Then C(2n,i) * i!^2 * (2n-i)!^2 * (2n+1-i)^2 = (2n)! * (2n+1-i)^2 * (2n-i)! * i! using Nat.choose_mul_factorial_mul_factorial.
-/
theorem scalar_A2_formula (n i : ℕ) (hi : i ≤ 2 * n) :
    scalar_A2 n i = (2 * n).factorial * (2 * n + 1 - i) ^ 2 *
      (2 * n - i).factorial * i.factorial := by
  unfold scalar_A2 α;
  rw [ ← Nat.choose_mul_factorial_mul_factorial hi ] ; ring;
  rw [ show 1 + n * 2 - i = ( n * 2 - i ) + 1 by rw [ tsub_add_eq_add_tsub ( by linarith ) ] ; ring ] ; norm_num [ Nat.factorial_succ ] ; ring;

/-
PROVIDED SOLUTION
Unfold scalar_B2, β. Use (i+1)! = (i+1) * i! (Nat.factorial_succ). Then C(2n,i) * (2n-i)!^2 * (i+1)^2 * i!^2 = (2n)! * (i+1)^2 * (2n-i)! * i! using Nat.choose_mul_factorial_mul_factorial.
-/
theorem scalar_B2_formula (n i : ℕ) (hi : i ≤ 2 * n) :
    scalar_B2 n i = (2 * n).factorial * (i + 1) ^ 2 *
      (2 * n - i).factorial * i.factorial := by
  unfold scalar_B2;
  unfold β;
  rw [ ← Nat.choose_mul_factorial_mul_factorial hi ] ; norm_num [ Nat.factorial_succ ] ; ring;

/-! ## Key p-adic lemmas -/

/-
PROVIDED SOLUTION
By Nat.choose_mul_factorial_mul_factorial, C(a+b, a) * a! * b! = (a+b)! (since a ≤ a+b). Using padicValNat.mul to split the product (all factors are nonzero: factorials are positive, C(a+b,a) > 0 by Nat.choose_pos). Rearrange to get the desired equation. Use mul_assoc and mul_comm to match the factorization, then apply padicValNat.mul for each split, handling nonzero conditions via Nat.factorial_ne_zero and Nat.choose_pos.
-/
theorem padicValNat_factorial_sum (p a b : ℕ) [hp : Fact p.Prime] :
    padicValNat p a.factorial + padicValNat p b.factorial +
      padicValNat p (Nat.choose (a + b) a) =
    padicValNat p (a + b).factorial := by
  rw [ ← padicValNat.mul, ← padicValNat.mul ];
  · rw [ ← Nat.choose_mul_factorial_mul_factorial ( Nat.le_add_right a b ) ];
    simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · positivity;
  · exact Nat.ne_of_gt <| Nat.choose_pos <| Nat.le_add_right _ _;
  · positivity;
  · positivity

/-- v_p(C(2m, j)) < k for all j ≠ m, when m = p^k - 1. Works for all primes p. -/
theorem padicValNat_choose_off_center (p k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k)
    (j : ℕ) (hj : j ≤ 2 * (p ^ k - 1)) (hj_ne : j ≠ p ^ k - 1) :
    padicValNat p (Nat.choose (2 * (p ^ k - 1)) j) < k := by
  have h_filter : Finset.filter
      (fun i => p ^ i ≤ j % p ^ i + (2 * (p ^ k - 1) - j) % p ^ i)
      (Finset.Ico 1 (k + 1)) ⊆ Finset.Ico 1 k := by
    intro i hi; simp_all +decide [Finset.mem_Ico]
    refine lt_of_le_of_ne hi.1.2 ?_; rintro rfl
    by_cases hj_lt : j < p ^ i
    · simp_all +decide [Nat.mod_eq_of_lt]
      rw [Nat.mod_eq_sub_mod] at hi <;> [rw [Nat.mod_eq_of_lt] at hi <;> omega; omega]
    · rw [Nat.mod_eq_sub_mod, Nat.mod_eq_of_lt] at hi <;> try omega
      rw [Nat.mod_eq_of_lt] at hi <;> omega
  rw [padicValNat_choose]
  · exact lt_of_le_of_lt (Finset.card_le_card h_filter) (by simpa)
  · linarith
  · refine Nat.log_lt_of_lt_pow ?_ ?_
    · exact mul_ne_zero two_ne_zero
        (Nat.sub_ne_zero_of_lt (one_lt_pow₀ hp.1.one_lt (by linarith)))
    · rw [pow_succ']
      nlinarith [Nat.sub_add_cancel (Nat.one_le_pow k p hp.1.pos), hp.1.two_le]

/-
PROBLEM
v_p(C(2m, m)) = k when m = p^k - 1. Works for all primes p.

PROVIDED SOLUTION
Use the carry-counting version of Kummer's theorem (padicValNat_choose):
v_p(C(2m, m)) = |{i ∈ [1, b) : p^i ≤ m % p^i + m % p^i}| where m = p^k - 1.

Take b = k + 1. For log bound: Nat.log p (2m) < k+1, since 2m = 2(p^k-1) < p^(k+1) for p ≥ 2.

Key claim: EVERY i ∈ [1, k+1) = [1, k] satisfies p^i ≤ m % p^i + m % p^i. So the filter equals Finset.Ico 1 (k+1), which has card k.

Proof of claim: For 1 ≤ i ≤ k:
m = p^k - 1. m % p^i = p^i - 1 (since p^i | p^k and m = p^k - 1, we get (p^k - 1) mod p^i = p^i - 1).
So m % p^i + m % p^i = 2*(p^i - 1) = 2*p^i - 2.
We need p^i ≤ 2*p^i - 2, i.e., p^i ≥ 2. Since p ≥ 2 and i ≥ 1: p^i ≥ 2. ✓

The mod computation: (p^k - 1) % p^i = p^i - 1. This follows from p^i | p^k (since i ≤ k) so p^k ≡ 0 mod p^i, hence p^k - 1 ≡ -1 ≡ p^i - 1 mod p^i. Use Nat.sub_one_mod_eq_pred_of_dvd or similar.
-/
theorem padicValNat_choose_central (p k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k) :
    padicValNat p (Nat.choose (2 * (p ^ k - 1)) (p ^ k - 1)) = k := by
  rw [ padicValNat_choose ];
  any_goals exact k + 1;
  · rw [ Finset.filter_true_of_mem ] <;> norm_num [ two_mul ];
    intro x hx₁ hx₂; rw [ show ( p ^ k - 1 ) % p ^ x = p ^ x - 1 from ?_ ] ;
    · linarith [ Nat.sub_add_cancel ( Nat.one_le_pow x p hp.1.pos ), Nat.Prime.one_lt hp.1, Nat.pow_le_pow_right hp.1.one_lt.le hx₁ ];
    · rw [ Nat.ModEq.symm, Nat.mod_eq_of_lt ];
      · exact Nat.sub_lt ( pow_pos hp.1.pos _ ) zero_lt_one;
      · simp +decide [ Nat.modEq_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
        norm_num [ hp.1.pos ];
        exact pow_dvd_pow _ hx₂;
  · grind +ring;
  · refine' Nat.log_lt_of_lt_pow _ _;
    · exact mul_ne_zero two_ne_zero ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ hp.1.one_lt ( by linarith ) ) );
    · rw [ pow_succ' ] ; nlinarith [ Nat.Prime.one_lt hp.1, Nat.sub_add_cancel ( Nat.one_le_pow k p hp.1.pos ) ] ;

/-! ## Dominance helpers for A2/B2 (odd primes) -/

/-
PROBLEM
When p | j and p | (2m - j), then p | 2m. For p odd and m = p^k-1, this
    gives p | 2, contradiction.

PROVIDED SOLUTION
If p | j and p | (2*(p^k-1) - j), then p divides their sum j + (2*(p^k-1) - j) = 2*(p^k-1) (using Nat.add_sub_cancel with hj). Now 2*(p^k-1) = 2*p^k - 2. Since p | p^k, we have p | 2*p^k. So p | (2*p^k - (2*p^k - 2)) = 2. But p ≥ 3 (since p is prime and p ≠ 2), so p ∤ 2, contradiction.
-/
theorem coprime_complement (p k : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hk : 1 ≤ k)
    (j : ℕ) (hj : j ≤ 2 * (p ^ k - 1)) (hpj : p ∣ j) :
    ¬(p ∣ (2 * (p ^ k - 1) - j)) := by
  intro hdiv
  have hdiv_sum : p ∣ 2 * (p ^ k - 1) := by
    convert dvd_add hpj hdiv using 1 ; rw [ Nat.add_sub_of_le hj ]
  have hdiv_two : p ∣ 2 := by
    haveI := Fact.mk hp.1; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Nat.cast_sub ( show 1 ≤ p ^ k from Nat.one_le_pow _ _ hp.1.pos ) ] ;
    cases k <;> aesop
  exact hp_odd (by
  exact le_antisymm ( Nat.le_of_dvd ( by decide ) hdiv_two ) hp.1.two_le)

/-
PROBLEM
v_p(2m - j) < k for j ≤ 2m, j ≠ m-1, j ≠ m (odd prime p, m = p^k-1).

PROVIDED SOLUTION
We need v_p(2*(p^k-1) - j) < k. This is equivalent to p^k ∤ (2*(p^k-1) - j).

Note that 2*(p^k-1) - j = 2*p^k - 2 - j. For p^k to divide this, we'd need 2*p^k - 2 - j ≡ 0 mod p^k, i.e., j ≡ -2 mod p^k, i.e., j ≡ p^k - 2 mod p^k. Since 0 ≤ j ≤ 2*(p^k-1) = 2*p^k - 2, the solutions are j = p^k - 2 and j = 2*p^k - 2. But j ≠ p^k - 2 (hypothesis hj_ne_n). And j = 2*p^k - 2 = 2*(p^k-1) would give 2*(p^k-1) - j = 0, and v_p(0) = 0 < k. So actually for j = 2*(p^k-1), the result is trivially true.

More carefully: if j < 2*(p^k-1), then 2*(p^k-1) - j ≥ 1 and 2*(p^k-1) - j ≤ 2*p^k - 3 < 2*p^k. If p^k | (2*(p^k-1) - j), then 2*(p^k-1) - j ≥ p^k, so 2*(p^k-1) - j = p^k (the only multiple of p^k in [1, 2*p^k - 3]). This gives j = p^k - 2, contradicting hj_ne_n.

If j = 2*(p^k-1): 2*(p^k-1) - j = 0, v_p(0) = 0 < k. Done.

Use padicValNat_dvd_iff_le (contraposition) or show ¬(p^k ∣ (2*(p^k-1) - j)) directly.
-/
theorem complement_val_bound (p k : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hk : 1 ≤ k)
    (j : ℕ) (hj : j ≤ 2 * (p ^ k - 1))
    (hj_ne_n : j ≠ p ^ k - 2) (hj_ne_m : j ≠ p ^ k - 1) :
    padicValNat p (2 * (p ^ k - 1) - j) < k := by
  by_contra h_contra
  have h_div : p ^ k ∣ (2 * (p ^ k - 1) - j) := by
    simp_all +decide [ padicValNat_dvd_iff ]
  have h_contra' : p ^ k ∣ (2 * (p ^ k - 1) - j) := by
    exact h_div
  have h_contra'' : p ^ k ∣ (2 * (p ^ k - 1) - j) := by
    exact h_contra';
  obtain ⟨ a, ha ⟩ := h_contra''; rcases a with ( _ | _ | a ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ] ;
  · omega;
  · rw [ Nat.sub_eq_iff_eq_add ] at ha <;> try linarith [ Nat.sub_add_cancel ( Nat.one_le_pow k p hp.1.pos ) ] ; ; nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow k p hp.1.pos ), hp.1.two_le ] ;

/-
PROBLEM
When p | (2m-j) and p ∤ j, then v_p(C(2m, j)) = 0 (no carries).

PROVIDED SOLUTION
Use padicValNat_choose (Kummer's carry counting):
v_p(C(2m, j)) = |{i ∈ [1, b) : p^i ≤ j % p^i + (2m-j) % p^i}|.

When p | (2m-j) and p ∤ j: for each position i, the carry condition p^i ≤ j % p^i + (2m-j) % p^i is NEVER satisfied, so the filter is empty and v_p = 0.

Proof: For any i ≥ 1, let t = v_p(2m-j) ≥ 1. Then:
- For i ≤ t: (2m-j) % p^i = 0. So condition is p^i ≤ j % p^i. Since p ∤ j, j % p = j₀ where 1 ≤ j₀ ≤ p-1. For i = 1: j % p ≤ p-1 < p = p^1. Not satisfied.
  For i ≥ 2: j % p^i ≤ p^i - 1 < p^i. Not satisfied.
- For i > t: (2m-j) % p^i ≥ 1 (since (2m-j)/p^t is the remaining part). Then j % p^i + (2m-j) % p^i ≡ 2m mod p^i.
  2m = 2(p^k-1) = 2p^k-2. 2m % p^i:
  For i ≤ k: 2m % p^i = 2p^k - 2 mod p^i. Since p^i | p^k (for i ≤ k): 2p^k mod p^i = 0, so 2m % p^i = p^i - 2 (when p^i > 2) or p^i - 2 + p^i (adjusted). Actually, -2 mod p^i = p^i - 2 for p^i ≥ 3. Since p ≥ 3 and i ≥ 1: p^i ≥ 3, so 2m % p^i = p^i - 2.
  Now j % p^i + (2m-j) % p^i ≡ 2m % p^i = p^i - 2 (mod p^i). So the actual sum ≡ p^i - 2 mod p^i, meaning the sum is either p^i - 2 or 2p^i - 2 (i.e., with or without a carry from lower positions). Since p^i - 2 < p^i, and we showed there are no carries from lower positions (the sum at each position is < p), the sum is exactly p^i - 2 < p^i. Not satisfied.

So the filter is empty for all positions.

For the formal proof: show that for all i in [1, b), p^i > j % p^i + (2m-j) % p^i. This holds because j + (2m-j) = 2m, and 2m % p^i = p^i - 2 < p^i (for p ≥ 3, i ≥ 1). Since there are no carries (j % p^i + (2m-j) % p^i = (j + (2m-j)) % p^i + c * p^i where c is a carry), and the total is 2m, with each digit position producing sum < p (no carry), we get j % p^i + (2m-j) % p^i = 2m % p^i = p^i - 2 < p^i.
-/
theorem choose_val_zero_when_complement_div (p k : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ 2 * (p ^ k - 1))
    (hpb : p ∣ (2 * (p ^ k - 1) - j)) (hpj : ¬(p ∣ j)) :
    padicValNat p (Nat.choose (2 * (p ^ k - 1)) j) = 0 := by
  -- Apply Kummer's theorem to conclude that the p-adic valuation of the binomial coefficient is zero.
  have h_kummer : ∀ i ∈ Finset.Ico 1 (Nat.log p (2 * (p ^ k - 1)) + 1), ¬(p ^ i ≤ j % p ^ i + (2 * (p ^ k - 1) - j) % p ^ i) := by
    intro i hi
    have h_mod : (2 * (p ^ k - 1)) % p ^ i = p ^ i - 2 ∨ (2 * (p ^ k - 1)) % p ^ i = 0 := by
      by_cases h_cases : i ≤ k;
      · -- Since $p^i \mid p^k$, we have $2 * (p^k - 1) \equiv -2 \pmod{p^i}$.
        have h_mod_eq : 2 * (p ^ k - 1) ≡ -2 [ZMOD p ^ i] := by
          exact Int.modEq_iff_dvd.mpr ⟨ -2 * p ^ ( k - i ), by rw [ show ( p : ℤ ) ^ k = p ^ i * p ^ ( k - i ) by rw [ ← pow_add, Nat.add_sub_of_le h_cases ] ] ; ring ⟩;
        -- Since $p^i \mid p^k$, we have $2 * (p^k - 1) \equiv -2 \pmod{p^i}$, which implies $2 * (p^k - 1) \mod p^i = p^i - 2$.
        have h_mod_eq_nat : 2 * (p ^ k - 1) % p ^ i = (p ^ i - 2) % p ^ i := by
          zify at *;
          rw [ Int.ofNat_sub <| Nat.one_le_pow _ _ hp.1.pos, Int.ofNat_sub <| show 2 ≤ p ^ i from le_trans ( Nat.Prime.two_le hp.1 ) ( Nat.le_self_pow ( by linarith [ Finset.mem_Ico.mp hi ] ) _ ) ] ; simp_all +decide [ Int.ModEq ];
        exact Or.inl <| h_mod_eq_nat.trans <| Nat.mod_eq_of_lt <| Nat.sub_lt ( pow_pos hp.1.pos _ ) zero_lt_two;
      · rw [ Nat.mod_eq_of_lt ] <;> norm_num at *;
        · contrapose! hi;
          refine fun _ => Nat.log_lt_of_lt_pow ?_ ?_ <;> norm_num;
          · exact hi.2;
          · refine lt_of_lt_of_le ?_ ( pow_le_pow_right₀ hp.1.one_lt.le h_cases );
            rw [ pow_succ' ] ; nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow k p hp.1.pos ), hp.1.two_le ];
        · refine' lt_of_lt_of_le _ ( pow_le_pow_right₀ hp.1.one_lt.le h_cases );
          rw [ pow_succ' ] ; nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow k p hp.1.pos ), hp.1.two_le ] ;
    cases h_mod <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
    · -- Since $p \nmid j$, we have $j \% p^i + (2 * (p^k - 1) - j) \% p^i \equiv 2 * (p^k - 1) \% p^i \pmod{p^i}$.
      have h_mod_sum : (j % p ^ i + (2 * (p ^ k - 1) - j) % p ^ i) % p ^ i = (2 * (p ^ k - 1)) % p ^ i := by
        simp +decide [ ← ZMod.natCast_eq_natCast_iff', Nat.cast_sub hj ];
      contrapose! h_mod_sum;
      rw [ Nat.mod_eq_sub_mod h_mod_sum ];
      rw [ Nat.mod_eq_of_lt ] <;> norm_num [ * ];
      · intro H; rw [ Nat.sub_eq_iff_eq_add ] at H <;> try linarith [ Nat.sub_add_cancel ( show 2 ≤ p ^ i from Nat.succ_le_of_lt ( one_lt_pow₀ hp.1.one_lt ( by linarith ) ) ) ] ; ; simp_all +decide [ Nat.mod_eq_of_lt ] ;
        have h_contra : (2 * (p ^ k - 1) - j) % p ^ i = p ^ i - 1 := by
          linarith [ Nat.mod_lt j ( pow_pos hp.1.pos i ), Nat.mod_lt ( 2 * ( p ^ k - 1 ) - j ) ( pow_pos hp.1.pos i ), Nat.sub_add_cancel ( show 2 ≤ p ^ i from Nat.succ_le_of_lt ( one_lt_pow₀ hp.1.one_lt ( by linarith ) ) ), Nat.sub_add_cancel ( show 1 ≤ p ^ i from Nat.one_le_pow _ _ hp.1.pos ) ];
        have := Nat.dvd_of_mod_eq_zero ( show ( 2 * ( p ^ k - 1 ) - j ) % p = 0 from Nat.mod_eq_zero_of_dvd hpb ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hp.1.one_lt ] ;
        rw [ ← Nat.mod_mod_of_dvd _ ( dvd_pow_self p ( by linarith : i ≠ 0 ) ), h_contra ] at this ; rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.add_mod, Nat.mul_succ, Nat.mul_mod ] ;
        cases i <;> simp_all +decide [ ← ZMod.val_natCast, Nat.add_mod, Nat.pow_mod ];
      · rw [ tsub_lt_iff_left ] <;> linarith [ Nat.mod_lt j ( pow_pos hp.1.pos i ), Nat.mod_lt ( 2 * ( p ^ k - 1 ) - j ) ( pow_pos hp.1.pos i ) ];
    · rw [ ← Nat.dvd_iff_mod_eq_zero ] at *;
      have := dvd_trans ( dvd_pow_self p ( by linarith ) ) ‹p ^ i ∣ 2 * ( p ^ k - 1 ) ›; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Nat.cast_sub ( show j ≤ 2 * ( p ^ k - 1 ) from hj ) ] ;
      grind;
  rw [ padicValNat_choose ];
  exacts [ Finset.card_eq_zero.mpr <| Finset.filter_eq_empty_iff.mpr h_kummer, hj, Nat.lt_succ_self _ ]

/-
PROBLEM
Combined A2 dominance helper for odd primes:
    v_p(C(2m,j)) + v_p(2m-j) < k + v_p(j) for j ≠ m-1, j ≠ m.

PROVIDED SOLUTION
Three cases:
Case 1 (p | j): By coprime_complement, p ∤ (2m-j). So v_p(2m-j) = 0 (using padicValNat.eq_zero_of_not_dvd since the remainder has its first digit nonzero). By off_center, v_p(C(2m,j)) ≤ k-1. Since v_p(j) ≥ 1: LHS ≤ k-1 + 0 = k-1 < k + 1 ≤ k + v_p(j) = RHS.

Case 2 (p ∤ j, p ∤ (2m-j)): v_p(j) = 0, v_p(2m-j) = 0. LHS = v_p(C(2m,j)) + 0 ≤ k-1 < k = k + 0 = RHS.

Case 3 (p ∤ j, p | (2m-j)): v_p(j) = 0. By choose_val_zero_when_complement_div, v_p(C(2m,j)) = 0. By complement_val_bound, v_p(2m-j) ≤ k-1. LHS = 0 + v_p(2m-j) ≤ k-1 < k = k + 0 = RHS.
-/
theorem A2_dominance_helper (p k : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hk : 1 ≤ k)
    (j : ℕ) (hj : j ≤ 2 * (p ^ k - 1)) (hj_ne_m : j ≠ p ^ k - 1)
    (hj_ne_n : j ≠ p ^ k - 2) :
    padicValNat p (Nat.choose (2 * (p ^ k - 1)) j) +
      padicValNat p (2 * (p ^ k - 1) - j) <
    k + padicValNat p j := by
  by_cases hpj : p ∣ j;
  · by_cases hpj' : p ∣ (2 * (p ^ k - 1) - j);
    · have := coprime_complement p k hp_odd hk j hj hpj; aesop;
    · rw [ padicValNat.eq_zero_of_not_dvd hpj' ] ; simp_all +decide [ padicValNat.eq_zero_of_not_dvd ] ;
      refine' lt_of_lt_of_le ( padicValNat_choose_off_center p k hk j hj hj_ne_m ) _;
      exact Nat.le_add_right _ _;
  · by_cases hpb : p ∣ (2 * (p ^ k - 1) - j);
    · have h_choose_val_zero : padicValNat p (Nat.choose (2 * (p ^ k - 1)) j) = 0 := by
        exact?;
      have h_complement_val_bound : padicValNat p (2 * (p ^ k - 1) - j) < k := by
        apply complement_val_bound p k hp_odd hk j hj hj_ne_n hj_ne_m;
      linarith [ show padicValNat p j = 0 from padicValNat.eq_zero_of_not_dvd hpj ];
    · simp_all +decide [ padicValNat.eq_zero_of_not_dvd ];
      exact?

/-! ## Main theorems -/

/-
PROVIDED SOLUTION
1. By scalar_AB_formula: scalar_AB n i = (2n)! * (2n+1-i)! * (i+1)! and scalar_AB n n = (2n)! * (n+1)! * (n+1)!.

2. Since (2n)! > 0, (2n+1-i)! > 0, (i+1)! > 0, (n+1)! > 0, all scalar values are positive. Use padicValNat.mul to split into sums.

3. The difference v_p(scalar_AB(n,i)) - v_p(scalar_AB(n,n)) = [v_p((2n+1-i)!) + v_p((i+1)!)] - 2*v_p((n+1)!).

4. By padicValNat_factorial_sum:
   v_p((2n+1-i)!) + v_p((i+1)!) + v_p(C(2n+2, 2n+1-i)) = v_p((2n+2)!)
   (since (2n+1-i) + (i+1) = 2n+2 = 2(n+1))
   Also: 2*v_p((n+1)!) + v_p(C(2(n+1), n+1)) = v_p((2(n+1))!)
   (since (n+1) + (n+1) = 2(n+1))

5. Subtracting: [v_p((2n+1-i)!) + v_p((i+1)!)] - 2*v_p((n+1)!) = v_p(C(2(n+1), n+1)) - v_p(C(2(n+1), 2n+1-i)).

6. By padicValNat_choose_central (with m = n+1 = p^k-1): v_p(C(2(n+1), n+1)) = k.

7. By padicValNat_choose_off_center: v_p(C(2(n+1), 2n+1-i)) < k (since 2n+1-i ≠ n+1 because i ≠ n, and 2n+1-i ≤ 2n+1 ≤ 2(n+1) = 2(p^k-1)).

8. So the difference is k - v_p(C(2(n+1), 2n+1-i)) > 0, giving the strict inequality.
-/
theorem scalar_AB_central_min (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k)
    (i : ℕ) (hi : i ≤ 2 * n) (hi_ne : i ≠ n) :
    padicValNat p (scalar_AB n n) < padicValNat p (scalar_AB n i) := by
  -- By padicValNat_factorial_sum, we can split the p-adic valuation into sums of valuations of factorials and binomial coefficients.
  have h_split : padicValNat p (scalar_AB n i) = padicValNat p ((2 * n).factorial) + padicValNat p ((2 * n + 1 - i).factorial) + padicValNat p ((i + 1).factorial) ∧ padicValNat p (scalar_AB n n) = padicValNat p ((2 * n).factorial) + padicValNat p ((n + 1).factorial) + padicValNat p ((n + 1).factorial) := by
    constructor <;> rw [ scalar_AB_formula ];
    · rw [ padicValNat.mul, padicValNat.mul ] <;> positivity;
    · grind;
    · rw [ show 2 * n + 1 - n = n + 1 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; rw [ padicValNat.mul, padicValNat.mul ] <;> positivity;
    · linarith;
  -- By padicValNat_factorial_sum, we can split the p-adic valuation into sums of valuations of factorials and binomial coefficients for the binomial coefficients.
  have h_binom : padicValNat p (Nat.choose (2 * n + 2) (2 * n + 1 - i)) < k ∧ padicValNat p (Nat.choose (2 * n + 2) (n + 1)) = k := by
    apply And.intro;
    · convert padicValNat_choose_off_center p k ( show 1 ≤ k from hk ) ( 2 * n + 1 - i ) _ _ using 1 <;> norm_num [ ← hn ];
      · ring;
      · linarith;
      · omega;
    · convert padicValNat_choose_central p k hk using 1;
      rw [ show 2 * n + 2 = 2 * ( p ^ k - 1 ) by omega, show n + 1 = p ^ k - 1 by omega ];
  have h_binom_eq : padicValNat p (Nat.choose (2 * n + 2) (2 * n + 1 - i)) + padicValNat p ((2 * n + 1 - i).factorial) + padicValNat p ((i + 1).factorial) = padicValNat p ((2 * n + 2).factorial) ∧ padicValNat p (Nat.choose (2 * n + 2) (n + 1)) + padicValNat p ((n + 1).factorial) + padicValNat p ((n + 1).factorial) = padicValNat p ((2 * n + 2).factorial) := by
    have h_binom_eq : ∀ j ≤ 2 * n + 2, padicValNat p (Nat.choose (2 * n + 2) j) + padicValNat p (j.factorial) + padicValNat p ((2 * n + 2 - j).factorial) = padicValNat p ((2 * n + 2).factorial) := by
      intro j hj; have := @padicValNat_factorial_sum p j ( 2 * n + 2 - j ) ; simp_all +decide [ Nat.choose_eq_factorial_div_factorial ( show j ≤ 2 * n + 2 from hj ) ] ;
      linarith;
    constructor
    · have := h_binom_eq (2 * n + 1 - i) (by omega); simp only [show 2 * n + 2 - (2 * n + 1 - i) = i + 1 from by omega] at this; linarith
    · have := h_binom_eq (n + 1) (by omega); simp only [show 2 * n + 2 - (n + 1) = n + 1 from by omega] at this; linarith
  linarith

/-
PROBLEM
Key identity: scalar_A2 * (i+1) = scalar_AB * (2n+1-i)

PROVIDED SOLUTION
Use scalar_A2_formula and scalar_AB_formula, then ring/nlinarith.
scalar_A2(n,i) * (i+1) = [(2n)! * (2n+1-i)^2 * (2n-i)! * i!] * (i+1)
scalar_AB(n,i) * (2n+1-i) = [(2n)! * (2n+1-i)! * (i+1)!] * (2n+1-i)
Key: (2n+1-i)! = (2n+1-i) * (2n-i)! and (i+1)! = (i+1) * i!.
So scalar_AB * (2n+1-i) = (2n)! * (2n+1-i)! * (i+1)! * (2n+1-i) = (2n)! * (2n+1-i) * (2n+1-i)! * (i+1) * i!
And (2n+1-i) * (2n+1-i)! = (2n+1-i) * (2n+1-i) * (2n-i)! = (2n+1-i)^2 * (2n-i)!... wait, no. (2n+1-i)! = (2n+1-i) * (2n-i)!, so (2n+1-i) * (2n+1-i)! ≠ (2n+1-i)^2 * (2n-i)!.

Let me redo:scalar_AB * (2n+1-i) = (2n)! * (2n+1-i)! * (i+1)! * (2n+1-i)
Now (2n+1-i)! = (2n+1-i) * (2n-i)!, so:
= (2n)! * (2n+1-i) * (2n-i)! * (i+1)! * (2n+1-i)
= (2n)! * (2n+1-i)^2 * (2n-i)! * (i+1)!And (i+1)! = (i+1) * i!, so:
= (2n)! * (2n+1-i)^2 * (2n-i)! * (i+1) * i!
And scalar_A2 * (i+1) = (2n)! * (2n+1-i)^2 * (2n-i)! * i! * (i+1). ✓

So just rewrite with the formulas and use ring.
-/
theorem scalar_A2_AB_relation (n i : ℕ) (hi : i ≤ 2 * n) :
    scalar_A2 n i * (i + 1) = scalar_AB n i * (2 * n + 1 - i) := by
  rw [ scalar_A2_formula n i hi, scalar_AB_formula n i hi ];
  rw [ show 2 * n + 1 - i = ( 2 * n - i ) + 1 by omega ] ; push_cast [ Nat.factorial_succ ] ; ring;

/-
PROBLEM
A2 dominance for p = 2 (all carries vanish since 2^k-1 = 111...1 in binary)

PROVIDED SOLUTION
For p = 2 with m = 2^k - 1 (k ≥ 2), j + b = 2m where b = 2m - j.

Case 1 (j odd, b odd): v_2(j) = 0, v_2(b) = 0. By padicValNat_choose_off_center (works for all primes including 2): v_2(C(2m, j)) < k. So LHS = v_2(C(2m,j)) + 0 ≤ k-1 < k = k + 0 = RHS.

Case 2 (j even, b even): Since j + b = 2m is even and both j, b are even: j = 2j', b = 2b', j' + b' = m. Since m = 2^k - 1 is all 1s in binary, by Kummer's theorem (Lucas' theorem), v_2(C(m, j')) = 0 for ALL j' ≤ m (since adding j' and m-j' in base 2 never produces a carry when m has all digits 1). And carries of j + b = carries of 2j' + 2b': digit 0 is 0+0=0 (no carry), digits 1+ are same as carries of j' + b' = 0 carries. So v_2(C(2m, j)) = 0.

Also v_2(b) < k: since b ≤ 2m < 2^{k+1}, v_2(b) ≤ k. And v_2(b) = k iff b = 2^k, which gives j = 2m - 2^k = 2^k - 2 = n, excluded by hj_ne_n. So v_2(b) ≤ k-1.

LHS = 0 + v_2(b) ≤ k-1. RHS = k + v_2(j) ≥ k + 1 (since j is even, v_2(j) ≥ 1). LHS < RHS. ✓
-/
theorem A2_dominance_p2 (k : ℕ) (hk : 2 ≤ k)
    (j : ℕ) (hj : j ≤ 2 * (2 ^ k - 1)) (hj_ne_m : j ≠ 2 ^ k - 1)
    (hj_ne_n : j ≠ 2 ^ k - 2) :
    padicValNat 2 (Nat.choose (2 * (2 ^ k - 1)) j) +
      padicValNat 2 (2 * (2 ^ k - 1) - j) <
    k + padicValNat 2 j := by
  -- Let's split into cases based on whether j is even or odd.
  by_cases hj_even : Even j;
  · -- Since j is even, we can write j = 2j' for some j'.
    obtain ⟨j', rfl⟩ : ∃ j', j = 2 * j' := even_iff_two_dvd.mp hj_even;
    -- Since $j' + b' = m$ and $m = 2^k - 1$ is all 1s in binary, by Kummer's theorem, $v_2(C(m, j')) = 0$.
    have h_kummer : padicValNat 2 (Nat.choose (2 ^ k - 1) j') = 0 := by
      have h_lucas : ∀ j' : ℕ, j' ≤ 2 ^ k - 1 → Nat.choose (2 ^ k - 1) j' % 2 = 1 := by
        intro j' hj'; rw [ ← Nat.odd_iff ] ; induction' j' with j' ih <;> simp_all +decide [ Nat.choose_succ_succ, parity_simps ] ;
        have := Nat.choose_succ_succ ( 2 ^ k - 1 ) j'; simp_all +decide [ Nat.one_le_iff_ne_zero, parity_simps ] ;
        -- By Lucas' theorem, $\binom{2^k}{j'+1}$ is even.
        have h_lucas_even : Even (Nat.choose (2 ^ k) (j' + 1)) := by
          exact even_iff_two_dvd.mpr ( Nat.dvd_trans ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( Nat.mod_eq_zero_of_dvd <| Nat.prime_two.dvd_choose_pow ( by linarith [ Nat.sub_add_cancel ( Nat.one_le_pow k 2 zero_lt_two ) ] ) ( by linarith [ Nat.sub_add_cancel ( Nat.one_le_pow k 2 zero_lt_two ) ] ) ) ) );
        grind;
      rw [ padicValNat.eq_zero_of_not_dvd ] ; specialize h_lucas j' ( by linarith ) ; rw [ Nat.dvd_iff_mod_eq_zero ] ; aesop;
    -- Since $j' + b' = m$ and $m = 2^k - 1$ is all 1s in binary, by Kummer's theorem, $v_2(C(2m, j)) = 0$.
    have h_choose_zero : padicValNat 2 (Nat.choose (2 * (2 ^ k - 1)) (2 * j')) = 0 := by
      -- By Lucas' theorem, we know that $\binom{2m}{2j} \equiv \binom{m}{j} \pmod{2}$.
      have h_lucas : Nat.choose (2 * (2 ^ k - 1)) (2 * j') % 2 = Nat.choose (2 ^ k - 1) j' % 2 := by
        have h_lucas : ∀ (m j : ℕ), Nat.choose (2 * m) (2 * j) % 2 = Nat.choose m j % 2 := by
          intro m j; induction' m with m ih generalizing j <;> induction' j with j ih' <;> simp +arith +decide [ Nat.choose, *, Nat.mul_succ ] ;
          have := ih ( j + 1 ) ; simp_all +arith +decide [ Nat.choose_succ_succ, Nat.add_mod, Nat.mul_succ ] ;
        apply h_lucas;
      simp_all +decide [ Nat.even_iff ];
      exact Or.inr ( h_kummer.resolve_left ( Nat.ne_of_gt ( Nat.choose_pos hj ) ) );
    -- Since $2 * (2 ^ k - 1) - 2 * j' \leq 2 * (2 ^ k - 1)$ and $2 * (2 ^ k - 1) < 2^{k+1}$, we have $padicValNat 2 (2 * (2 ^ k - 1) - 2 * j') \leq k$.
    have h_val_le_k : padicValNat 2 (2 * (2 ^ k - 1) - 2 * j') ≤ k := by
      have h_val_le_k : 2 * (2 ^ k - 1) - 2 * j' < 2 ^ (k + 1) := by
        exact lt_of_le_of_lt ( Nat.sub_le _ _ ) ( by rw [ pow_succ' ] ; linarith [ Nat.sub_add_cancel ( Nat.one_le_pow k 2 zero_lt_two ) ] );
      contrapose! h_val_le_k;
      exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Nat.dvd_trans ( pow_dvd_pow _ h_val_le_k ) ( Nat.ordProj_dvd _ _ ) );
    rcases j' with ( _ | j' ) <;> simp_all +decide [ Nat.factorial_ne_zero, padicValNat.mul ];
    · rw [ padicValNat.mul ] <;> norm_num;
      · rw [ padicValNat.eq_zero_of_not_dvd ] <;> norm_num [ ← even_iff_two_dvd, Nat.one_le_iff_ne_zero, parity_simps ] ; linarith [ Nat.pow_le_pow_right two_pos hk ] ;
        linarith;
      · exact Nat.sub_ne_zero_of_lt ( one_lt_pow₀ one_lt_two ( by linarith ) );
    · cases h_choose_zero <;> simp_all +decide [ Nat.choose_eq_zero_iff ];
      · omega;
      · rw [ padicValNat.eq_zero_of_not_dvd ] <;> norm_num [ Nat.dvd_iff_mod_eq_zero, ‹_› ] ; linarith [ Nat.zero_le ( padicValNat 2 ( j' + 1 ) ) ] ;
  · -- Since $j$ is odd, by Lemma 25, $v_2(C(2m, j)) < k$.
    have h_choose : padicValNat 2 (Nat.choose (2 * (2 ^ k - 1)) j) < k := by
      convert padicValNat_choose_off_center 2 k ( show 1 ≤ k by linarith ) j hj ( ?_ ) using 1 ; aesop;
    simp_all +decide [ padicValNat.eq_zero_of_not_dvd, ← even_iff_two_dvd, parity_simps ]

/-
PROVIDED SOLUTION
Use the identity scalar_A2(n,i) * (i+1) = scalar_AB(n,i) * (2n+1-i) (from scalar_A2_AB_relation).

Taking v_p: v_p(scalar_A2) + v_p(i+1) = v_p(scalar_AB) + v_p(2n+1-i).
So v_p(scalar_A2) = v_p(scalar_AB) + v_p(2n+1-i) - v_p(i+1).

At i=n: v_p(scalar_A2(n,n)) = v_p(scalar_AB(n,n)) + v_p(n+1) - v_p(n+1) = v_p(scalar_AB(n,n)).

So diff = v_p(scalar_A2(n,i)) - v_p(scalar_A2(n,n))
= [v_p(scalar_AB(n,i)) - v_p(scalar_AB(n,n))] + v_p(2n+1-i) - v_p(i+1)

By scalar_AB_central_min and the exact formula:
v_p(scalar_AB(n,i)) - v_p(scalar_AB(n,n)) = v_p(C(2(n+1), n+1)) - v_p(C(2(n+1), 2n+1-i))
= k - v_p(C(2m, j)) where m = n+1 = p^k-1, j = 2n+1-i.

So diff = k + v_p(j) - v_p(C(2m, j)) - v_p(2m - j)
where j = 2n+1-i, 2m-j = i+1.

For i ≠ n, i ≠ n+1: j ≠ m (= p^k-1) and j ≠ m-1 (= p^k-2).

Case p ≠ 2: By A2_dominance_helper: v_p(C(2m,j)) + v_p(2m-j) < k + v_p(j). So diff > 0. ✓
Case p = 2, k = 1: n = 0, 2n = 0, no valid i. Vacuous.
Case p = 2, k ≥ 2: By A2_dominance_p2: v_2(C(2m,j)) + v_2(2m-j) < k + v_2(j). So diff > 0. ✓

For the formal proof: use the multiplicative identity to relate valuations, then split on p = 2 vs p ≠ 2, and apply the appropriate dominance helper.

The key technical point: v_p(scalar_A2) + v_p(i+1) = v_p(scalar_AB) + v_p(2n+1-i) follows from taking v_p of scalar_A2_AB_relation (using padicValNat.mul with all factors positive, since i+1 ≥ 1 and 2n+1-i ≥ 1 for i ≤ 2n).
-/
theorem scalar_A2_central_min (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k)
    (i : ℕ) (hi : i ≤ 2 * n) (hi_ne_n : i ≠ n) (hi_ne_n1 : i ≠ n + 1) :
    padicValNat p (scalar_A2 n n) < padicValNat p (scalar_A2 n i) := by
  -- Using the identity scalar_A2(n,i) * (i+1) = scalar_AB(n,i) * (2n+1-i), we can rewrite the difference in valuations.
  have h_val_diff : padicValNat p (scalar_A2 n i) + padicValNat p (i + 1) = padicValNat p (scalar_AB n i) + padicValNat p (2 * n + 1 - i) := by
    rw [ ← padicValNat.mul, ← padicValNat.mul ] <;> norm_num [ scalar_A2_AB_relation n i hi ];
    · exact ne_of_gt ( Nat.mul_pos ( Nat.mul_pos ( Nat.choose_pos ( by linarith ) ) ( Nat.mul_pos ( Nat.factorial_pos _ ) ( Nat.factorial_pos _ ) ) ) ( Nat.mul_pos ( Nat.factorial_pos _ ) ( Nat.factorial_pos _ ) ) );
    · omega;
    · exact Nat.ne_of_gt ( Nat.mul_pos ( Nat.choose_pos ( by linarith ) ) ( pow_pos ( Nat.mul_pos ( Nat.factorial_pos _ ) ( Nat.factorial_pos _ ) ) 2 ) );
  -- Using the exact formula for the difference in valuations of the scalar AB terms.
  have h_diff_AB : padicValNat p (scalar_AB n i) = padicValNat p (scalar_AB n n) + (k - padicValNat p (Nat.choose (2 * (p ^ k - 1)) (2 * n + 1 - i))) := by
    -- Using the identity scalar_AB(n,i) = (2n)! * (2n+1-i)! * (i+1)! and scalar_AB(n,n) = (2n)! * (n+1)! * (n+1)!, we can simplify the difference.
    have h_scalar_AB_simplified : padicValNat p (scalar_AB n i) = padicValNat p ((2 * n).factorial) + padicValNat p ((2 * n + 1 - i).factorial) + padicValNat p ((i + 1).factorial) ∧ padicValNat p (scalar_AB n n) = padicValNat p ((2 * n).factorial) + 2 * padicValNat p ((n + 1).factorial) := by
      constructor <;> rw [ scalar_AB_formula ] <;> try linarith;
      · rw [ padicValNat.mul, padicValNat.mul ] <;> positivity;
      · rw [ padicValNat.mul, padicValNat.mul ] <;> norm_num [ Nat.factorial_ne_zero ] ; ring;
        rw [ show 1 + n * 2 - n = n + 1 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring;
    -- Using the identity padicValNat_factorial_sum, we can simplify the difference.
    have h_padicValNat_factorial_sum : padicValNat p ((2 * n + 1 - i).factorial) + padicValNat p ((i + 1).factorial) + padicValNat p (Nat.choose (2 * (p ^ k - 1)) (2 * n + 1 - i)) = padicValNat p ((2 * (p ^ k - 1)).factorial) := by
      convert padicValNat_factorial_sum p ( 2 * n + 1 - i ) ( i + 1 ) using 1 ; ring;
      · rw [ show 1 + i + ( 1 + n * 2 - i ) = ( p ^ k - 1 ) * 2 by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ p ^ k ), Nat.sub_add_cancel ( by linarith : i ≤ 1 + n * 2 ) ] ];
      · rw [ show 2 * ( p ^ k - 1 ) = 2 * n + 1 - i + ( i + 1 ) by omega ];
    -- Using the identity padicValNat_factorial_sum, we can simplify the difference further.
    have h_padicValNat_factorial_sum_simplified : padicValNat p ((2 * (p ^ k - 1)).factorial) = 2 * padicValNat p ((n + 1).factorial) + k := by
      have h_padicValNat_factorial_sum_simplified : padicValNat p ((2 * (p ^ k - 1)).factorial) = padicValNat p ((p ^ k - 1).factorial) + padicValNat p ((p ^ k - 1).factorial) + padicValNat p (Nat.choose (2 * (p ^ k - 1)) (p ^ k - 1)) := by
        convert padicValNat_factorial_sum p ( p ^ k - 1 ) ( p ^ k - 1 ) using 1 ; ring;
        · have := padicValNat_factorial_sum p ( p ^ k - 1 ) ( p ^ k - 1 ) ; simp_all +decide [ mul_two, Nat.choose_symm_add ] ;
        · convert padicValNat_factorial_sum p ( p ^ k - 1 ) ( p ^ k - 1 ) using 1 ; ring;
      rw [ show n + 1 = p ^ k - 1 by omega ] ; linarith [ padicValNat_choose_central p k hk ] ;
    linarith [ Nat.sub_add_cancel ( show padicValNat p ( Nat.choose ( 2 * ( p ^ k - 1 ) ) ( 2 * n + 1 - i ) ) ≤ k from by linarith [ show padicValNat p ( Nat.choose ( 2 * ( p ^ k - 1 ) ) ( 2 * n + 1 - i ) ) ≤ k from by exact Nat.le_of_lt ( padicValNat_choose_off_center p k hk _ ( by omega ) ( by omega ) ) ] ) ];
  -- Using the exact formula for the difference in valuations of the scalar AB terms at i=n.
  have h_diff_AB_n : padicValNat p (scalar_A2 n n) = padicValNat p (scalar_AB n n) + padicValNat p (n + 1) - padicValNat p (n + 1) := by
    rw [ ← padicValNat.mul ] <;> simp +decide [ scalar_A2, scalar_AB ];
    · rw [ show α n n = β n n from ?_, mul_comm ];
      · rw [ show β n n ^ 2 * ( 2 * n ).choose n = ( 2 * n ).choose n * β n n * β n n * ( n + 1 ) / ( n + 1 ) by rw [ Nat.mul_div_cancel _ ( Nat.succ_pos _ ) ] ; ring ] ; rw [ padicValNat.div_of_dvd ] ; norm_num;
      · unfold α β; ring;
        norm_num [ add_comm, mul_two, add_tsub_assoc_of_le ] ; ring;
        rw [ show 1 + n * 2 - n = 1 + n by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring;
    · exact ⟨ ⟨ Nat.ne_of_gt <| Nat.choose_pos <| by linarith, Nat.ne_of_gt <| Nat.mul_pos ( Nat.factorial_pos _ ) ( Nat.factorial_pos _ ) ⟩, Nat.ne_of_gt <| Nat.mul_pos ( Nat.factorial_pos _ ) ( Nat.factorial_pos _ ) ⟩;
  -- Using the dominance helper theorem for the central term.
  have h_dom : padicValNat p (Nat.choose (2 * (p ^ k - 1)) (2 * n + 1 - i)) + padicValNat p (i + 1) < k + padicValNat p (2 * n + 1 - i) := by
    by_cases hp : p = 2;
    · by_cases hk2 : k ≥ 2;
      · have := A2_dominance_p2 k hk2 ( 2 * n + 1 - i ) ?_ ?_ ?_ <;> simp_all +decide [ Nat.sub_sub ];
        · convert this using 2 ; rw [ show 2 * ( 2 ^ k - 1 ) - ( 2 * n + 1 - i ) = i + 1 by omega ];
        · omega;
        · omega;
        · omega;
      · interval_cases k ; simp_all +decide;
    · convert A2_dominance_helper p k hp hk ( 2 * n + 1 - i ) _ _ _ using 1 <;> norm_num [ ← hn ];
      · rw [ show 2 * ( n + 1 ) - ( 2 * n + 1 - i ) = i + 1 by omega ];
      · linarith;
      · omega;
      · omega;
  omega

/-
PROVIDED SOLUTION
By symmetry with the A2 family. The B2 family has scalar_B2(n,i) = (2n)! * (i+1)^2 * (2n-i)! * i!, which is symmetric to A2 via the substitution i ↦ 2n-i (swapping α and β).

The proof follows the same structure as scalar_A2_central_min:
v_p(scalar_B2(n,i)) = v_p((2n)!) + 2*v_p(i+1) + v_p((2n-i)!) + v_p(i!)
v_p(scalar_B2(n,n)) = v_p((2n)!) + 2*v_p(n+1) + v_p(n!) + v_p(n!)

Diff = 2*v_p(i+1) + v_p(C(2n,n)) - v_p(C(2n,i)) (since v_p(n+1) = 0).

Setting b = i+1, j = 2n-i = 2n+1-(i+1), so 2n+1-j = i+1 = b.

For i ≠ n and i ≠ n-1: b = i+1 ≠ n+1 (since i ≠ n) and b = i+1 ≠ n (since i ≠ n-1).

In terms of the AB analysis with m = n+1 = p^k-1:
The difference = [k - v_p(C(2m, b))] + v_p(b) - v_p(2m - b) where b = i+1 and 2m-b = 2n+1-i.

Wait, we can relate B2 to AB as: scalar_B2 * (2n+1-i) = scalar_AB * (i+1) (as rationals).
So v_p(scalar_B2(n,i)) = v_p(scalar_AB(n,i)) + v_p(i+1) - v_p(2n+1-i).
And v_p(scalar_B2(n,n)) = v_p(scalar_AB(n,n)) + v_p(n+1) - v_p(n+1) = v_p(scalar_AB(n,n)).

Diff for B2 = [v_p(scalar_AB(n,i)) - v_p(scalar_AB(n,n))] + v_p(i+1) - v_p(2n+1-i)
= [k - v_p(C(2m, 2n+1-i))] + v_p(i+1) - v_p(2n+1-i)

Setting j' = 2n+1-i (the "A2 variable"), b' = i+1 = 2m - j':
Diff = k + v_p(b') - v_p(C(2m, j')) - v_p(j').
This is the SAME as the A2 dominance with j and b roles swapped!

By A2_dominance_helper (or its symmetric version): v_p(C(2m, j')) + v_p(j') < k + v_p(b').
Wait, the A2 helper gives v_p(C(2m, j)) + v_p(2m-j) < k + v_p(j). With j replaced by b' = i+1:
v_p(C(2m, b')) + v_p(2m - b') < k + v_p(b'). And 2m - b' = 2n+1 - i = j'.
So v_p(C(2m, i+1)) + v_p(2n+1-i) < k + v_p(i+1).
Which gives diff = k + v_p(i+1) - v_p(C(2m, i+1)) - v_p(2n+1-i) > 0.

Wait, that's using A2_dominance_helper with j = i+1 (= b'). We need j ≠ m = p^k-1 and j ≠ m-1 = p^k-2.
i+1 ≠ p^k-1 iff i ≠ p^k-2 = n. (excluded by hi_ne_n)
i+1 ≠ p^k-2 iff i ≠ p^k-3 = n-1. (excluded by hi_ne_nm1)

So the conditions match. The proof for B2 uses A2_dominance_helper with j = i+1 instead of j = 2n+1-i.

For p = 2, k = 1: n = 0, hn_pos requires n ≥ 1, so this case doesn't arise.
For p = 2, k ≥ 2: same argument works (for odd p use A2_dominance_helper; for p=2, n ≥ 2 and hn_pos gives n ≥ 1, but k ≥ 2).

Handle p = 2 separately or argue that with hn_pos : 1 ≤ n and hn : n + 2 = p^k:
If p = 2: p^k = n+2 ≥ 3, so k ≥ 2 (since 2^1 = 2 < 3). For k ≥ 2, the proof follows the same structure as for odd p, using the AB central min and carry analysis (without needing A2_dominance_helper for p = 2 specifically).

Actually for the formal proof, split on p = 2 vs p odd. For p odd use A2_dominance_helper. For p = 2 with hn_pos, k ≥ 2, argue directly using scalar formulas and the off-center result.
-/
theorem scalar_B2_central_min (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n)
    (i : ℕ) (hi : i ≤ 2 * n) (hi_ne_n : i ≠ n) (hi_ne_nm1 : i ≠ n - 1) :
    padicValNat p (scalar_B2 n n) < padicValNat p (scalar_B2 n i) := by
  -- By symmetry with the A2 family, we can use the same argument for the B2 family.
  have h_symm : padicValNat p (scalar_B2 n i) = padicValNat p (scalar_A2 n (2 * n - i)) := by
    unfold scalar_B2 scalar_A2 α β; simp +decide [ Nat.factorial_ne_zero, mul_comm, mul_assoc, mul_left_comm, Nat.choose_symm ( show i ≤ 2 * n from hi ), Nat.choose_symm ( show 2 * n - i ≤ 2 * n from Nat.sub_le _ _ ) ] ;
    rw [ Nat.choose_symm ( by linarith ), show n * 2 + 1 - ( n * 2 - i ) = i + 1 by omega ] ; ring;
  have h_symm_n : padicValNat p (scalar_B2 n n) = padicValNat p (scalar_A2 n n) := by
    unfold scalar_B2 scalar_A2 α β; ring;
    rw [ show n * 2 - n = n by rw [ Nat.sub_eq_of_eq_add ] ; ring, show 1 + n * 2 - n = n + 1 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring;
  generalize_proofs at *; (
  rw [ h_symm, h_symm_n ] ; exact ( scalar_A2_central_min p k hk n hn ( 2 * n - i ) ( by omega ) ( by omega ) ( by omega ) ) ;)

theorem central_val_eq (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : n + 2 = p ^ k) :
    padicValNat p (scalar_AB n n) = padicValNat p (scalar_A2 n n) ∧
    padicValNat p (scalar_AB n n) = padicValNat p (scalar_B2 n n) := by
  unfold scalar_AB scalar_A2 scalar_B2; rw [α_at_n, β_at_n]; constructor <;> ring_nf

end QuarticInvariant
