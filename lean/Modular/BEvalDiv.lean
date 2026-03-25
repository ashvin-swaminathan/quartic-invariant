import Mathlib
import Modular.Defs
import Modular.CentralDom

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant


/-- The α²-scalar: C(N,i)·α_i² = N!·(N+1-i)²·(N-i)!·i!. -/
lemma alpha_sq_scalar_eq (n i : ℕ) (hi : i ≤ 2 * n) :
    Nat.choose (2 * n) i * (α n i) ^ 2 =
    (2 * n).factorial * (2 * n + 1 - i) ^ 2 * (2 * n - i).factorial * i.factorial := by
  unfold α; ring;
  rw [ show 1 + n * 2 - i = ( n * 2 - i ) + 1 by rw [ tsub_add_eq_add_tsub ( by linarith ) ] ; ring ] ; norm_num [ Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_sub hi ] ; ring;
  rw [ ← Nat.choose_mul_factorial_mul_factorial ( by linarith : i ≤ n * 2 ) ] ; ring;

/-
PROBLEM
vp_complement_ge was DISPROVED: counterexample p=3, k=2, a=3 gives
v_3(2·8 - 3) = v_3(13) = 0 < 1 = v_3(3). The lemma is false in general.
We use a direct Legendre-based approach for B_eval_dvd_pe instead.

β(n,i) = α(n,i+1) when i ≤ 2n-1

PROVIDED SOLUTION
Unfold β and α. β(n,i) = (2n-i)!·(i+1)! and α(n,i+1) = (2n+1-(i+1))!·(i+1)! = (2n-i)!·(i+1)!. These are equal. The key is showing 2*n+1-(i+1) = 2*n-i, which holds since i+1 ≤ 2*n implies i ≤ 2*n-1 so 2*n+1-(i+1) = 2*n-i in ℕ.
-/
lemma beta_eq_alpha_succ (n i : ℕ) (hi : i + 1 ≤ 2 * n) :
    β n i = α n (i + 1) := by
  unfold β α; ring;
  rw [ mul_comm, Nat.add_sub_add_left ]

/-
PROBLEM
The β²-scalar: C(N,i)·β_i² = N!·(i+1)²·(N-i)!·i!.

PROVIDED SOLUTION
Unfold β. C(2n,i) · β(n,i)² = C(2n,i) · ((2n-i)! · (i+1)!)². Use Nat.choose_mul_factorial_mul_factorial to get C(2n,i)·(2n-i)!·i! = (2n)!, so C(2n,i) = (2n)!/((2n-i)!·i!). Then C(2n,i)·((2n-i)!·(i+1)!)² = (2n)!·(2n-i)!·(i+1)!²/i! = (2n)!·(2n-i)!·(i+1)²·(i+1-1)!·(i+1) ... Actually simpler: C(2n,i)·β² = [C(2n,i)·(2n-i)!·i!] · (2n-i)! · (i+1)!² / ((2n-i)!·i!) = (2n)! · (i+1)!²/i! · (2n-i)!/1... Let me be cleaner. C(2n,i)·(2n-i)!·i! = (2n)!. So C(2n,i) = (2n)!/((2n-i)!·i!). Then β² = (2n-i)!²·(i+1)!². C(2n,i)·β² = (2n)!·(2n-i)!·(i+1)!²/i! = (2n)!·(2n-i)!·(i+1)²·i!/i! = (2n)!·(i+1)²·(2n-i)!·i!. Wait: (i+1)!² / i! = (i+1)² · (i!)² / i! = (i+1)² · i!. And (2n-i)!²/(2n-i)! = (2n-i)!. So C(2n,i)·β² = (2n)! · (2n-i)! · (i+1)² · i!. QED. Key: use Nat.choose_mul_factorial_mul_factorial for hi : i ≤ 2*n.
-/
lemma beta_sq_scalar_eq (n i : ℕ) (hi : i ≤ 2 * n) :
    Nat.choose (2 * n) i * (β n i) ^ 2 =
    (2 * n).factorial * (i + 1) ^ 2 * (2 * n - i).factorial * i.factorial := by
  unfold β;
  norm_num [ Nat.choose_eq_factorial_div_factorial hi ] ; ring;
  norm_num [ Nat.factorial_succ, mul_comm, mul_assoc, mul_left_comm, Nat.mul_div_mul_right, Nat.factorial_pos ] ; ring;
  rw [ ← Nat.mul_div_assoc ] ; ring;
  · exact Nat.div_eq_of_eq_mul_left ( by positivity ) ( by push_cast [ Nat.add_comm 1 i, Nat.factorial_succ ] ; ring );
  · exact Nat.factorial_mul_factorial_dvd_factorial ( by linarith )

/-
PROBLEM
Key Legendre bound: when n+1 = p^k - 1 and a + b = 2n+1,
    v_p(a! · b!) ≥ 2·v_p((n+1)!).
    This uses floor(a/p^l) + floor(b/p^l) ≥ floor((a+b)/p^l) - 1
    and the fact that floor((2p^k-1)/p^l) = 2p^{k-l} - 1 for 1 ≤ l ≤ k,
    so v_p((2n+1)!) = 2·v_p((n+1)!) + k.

PROVIDED SOLUTION
We need: v_p(a!·b!) ≥ 2·v_p((n+1)!) where a+b = 2n+1 and n+1 = p^k - 1 (from hn: n+2 = p^k).

By the Legendre formula: v_p(m!) = Σ_{l≥1} floor(m/p^l).

Step 1: v_p(a!) + v_p(b!) = Σ_l (floor(a/p^l) + floor(b/p^l)).
By the standard inequality floor(x/q) + floor(y/q) ≥ floor((x+y)/q) - 1:
  floor(a/p^l) + floor(b/p^l) ≥ floor((a+b)/p^l) - 1 = floor((2n+1)/p^l) - 1.

Step 2: 2n+1 = 2(p^k-1) - 1 = 2p^k - 3... wait, n+2 = p^k, so n = p^k - 2, 2n+1 = 2p^k - 3.
Hmm actually let me recheck. n + 2 = p^k. So n + 1 = p^k - 1. And 2n + 1 = 2(n+1) - 1 = 2(p^k - 1) - 1 = 2p^k - 3.

Hmm wait, that's 2p^k - 3, not 2p^k - 1. Let me recompute.
n = p^k - 2. 2n = 2p^k - 4. 2n + 1 = 2p^k - 3.
floor((2p^k - 3)/p^l) for 1 ≤ l ≤ k:
  = floor(2p^{k-l} - 3/p^l). Not as clean.

Actually, let me reconsider. For the A_eval case (from Sub05_Rank1Collapse.lean), the sum was a+b = 2(n+1) = 2(p^k-1), and the bound was v_p(a!)+v_p(b!) ≥ 2v_p((n+1)!).

For the B_eval case, we have a+b = 2n+1 = 2(p^k-2)+1 = 2p^k - 3.

Hmm, this is NOT the same as what I computed earlier. Let me recheck...

Earlier I had: n+1 = p^k - 1 (from n+2 = p^k). 2n+1 = 2(n+1) - 1 = 2(p^k-1) - 1 = 2p^k - 3.

But I thought the sum was 2p^k - 1. Let me recheck my earlier analysis...

Oh wait, I think I made an error. Let me recheck:
N = 2n. N+1 = 2n+1. (N+1-j) + j = N+1 = 2n+1.

The "polynomial coefficient" analysis gives a+b = 2n+1, NOT 2(p^k-1). So 2n+1 = 2p^k - 3.

floor((2p^k - 3)/p) = 2p^{k-1} - 1 (when p ≥ 3, since -3/p rounds down to -1).
Actually: 2p^k - 3 = p · (2p^{k-1}) - 3 = p · (2p^{k-1} - 1) + (p - 3).
So floor((2p^k - 3)/p) = 2p^{k-1} - 1 when p ≥ 3 (since p-3 ≥ 0).

For l ≥ 2: 2p^k - 3 = p^l · (2p^{k-l}) - 3. And 2p^{k-l} · p^l - 3 = (2p^{k-l} - 1) · p^l + (p^l - 3).
For p^l ≥ 4 (which holds for p ≥ 3, l ≥ 2, OR p ≥ 5, l ≥ 1):
floor((2p^k-3)/p^l) = 2p^{k-l} - 1 + floor((p^l-3)/p^l) = 2p^{k-l} - 1 (since p^l-3 ≥ 1 > 0 and < p^l).

Wait, (2p^{k-l} - 1) · p^l + (p^l - 3) = 2p^k - p^l + p^l - 3 = 2p^k - 3. ✓
And 0 ≤ p^l - 3 < p^l for p^l ≥ 4.
So floor((2p^k - 3)/p^l) = 2p^{k-l} - 1 for p^l ≥ 4.

For p = 3, l = 1: 3^1 = 3 < 4. floor((2·3^k - 3)/3) = floor(2·3^{k-1} - 1) = 2·3^{k-1} - 1. ✓ (since 2·3^k - 3 = 3·(2·3^{k-1} - 1) + 0).

For p ≥ 5, l = 1: p ≥ 5 ≥ 4. ✓.

So floor((2p^k-3)/p^l) = 2p^{k-l} - 1 for 1 ≤ l ≤ k-1 and p ≥ 3.
For l = k: 2p^{k-k} - 1 = 1. But 2p^k - 3 = 2p^k - 3. floor((2p^k-3)/p^k) = 2 - floor(3/p^k). Since p^k ≥ 3 (p ≥ 3, k ≥ 1), floor(3/p^k) = 1 when p^k = 3, and 0 when p^k > 3.

So for p=3, k=1: floor(3/3) = 1. floor((6-3)/3) = 1. And 2p^{k-k}-1 = 1. ✓.
For p=3, k=2: floor((18-3)/9) = floor(15/9) = 1. And 2·3^0 - 1 = 1. ✓.
For p=5, k=1: floor((10-3)/5) = floor(7/5) = 1. And 2·5^0 - 1 = 1. ✓.
For p=5, k=2: floor((50-3)/25) = floor(47/25) = 1. And 2·5^0 - 1 = 1. ✓.

So floor((2p^k-3)/p^l) = 2p^{k-l} - 1 for ALL 1 ≤ l ≤ k (when p ≥ 3, k ≥ 1).

Therefore: v_p((2n+1)!) = Σ_{l=1}^k floor((2n+1)/p^l) = Σ_{l=1}^k (2p^{k-l} - 1) = 2(p^k-1)/(p-1) - k.

And: v_p((n+1)!) = v_p((p^k-1)!) = Σ_{l=1}^{k-1} floor((p^k-1)/p^l) = Σ_{l=1}^{k-1} (p^{k-l} - 1) = (p^k-p)/(p-1) - (k-1) = (p^k-1)/(p-1) - 1 - (k-1) = (p^k-1)/(p-1) - k.

Wait: Σ_{l=1}^{k-1} (p^{k-l} - 1). For l=1,...,k-1: p^{k-l} goes from p^{k-1} to p^1.
Sum of p^{k-l} = p^{k-1} + p^{k-2} + ... + p = p(p^{k-1}-1)/(p-1).
Number of terms: k-1.
So Σ = p(p^{k-1}-1)/(p-1) - (k-1) = (p^k-p)/(p-1) - (k-1).

And for l=k: floor((p^k-1)/p^k) = 0. So no contribution from l=k.

v_p((n+1)!) = (p^k - p)/(p-1) - (k-1).

2·v_p((n+1)!) = 2(p^k - p)/(p-1) - 2(k-1) = (2p^k - 2p)/(p-1) - 2k + 2.

v_p((2n+1)!) = 2(p^k-1)/(p-1) - k = (2p^k - 2)/(p-1) - k.

Difference: v_p((2n+1)!) - 2·v_p((n+1)!) = (2p^k-2)/(p-1) - k - (2p^k-2p)/(p-1) + 2k - 2
= [(2p^k-2) - (2p^k-2p)]/(p-1) + k - 2
= (2p-2)/(p-1) + k - 2
= 2 + k - 2
= k.

So v_p((2n+1)!) = 2·v_p((n+1)!) + k.

Now: v_p(a!) + v_p(b!) = Σ_l [floor(a/p^l) + floor(b/p^l)]
≥ Σ_{l=1}^k [floor((a+b)/p^l) - 1]   (using floor(x/q)+floor(y/q) ≥ floor((x+y)/q)-1)
= Σ_{l=1}^k [floor((2n+1)/p^l) - 1]
= v_p((2n+1)!) - k
= 2·v_p((n+1)!).

Use padicValNat.prime_pow_self, Nat.Primes, the Legendre formula for padicValNat of factorials. The key Mathlib lemma is `Nat.Prime.floor_div_add` or similar for floor(a/q)+floor(b/q) ≥ floor((a+b)/q)-1. Also use `padicValNat_factorial` from Mathlib.

Actually, this is a tricky formalization. The approach:
1. Use multiplicity/padicValNat for factorials (Legendre's formula).
2. Show the floor sum inequality.
3. Compute v_p((2n+1)!) explicitly.

This is quite involved. The subagent should try to use padicValNat_factorial and Nat.div properties.
-/
lemma legendre_B_bound (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k)
    (a b : ℕ) (hab : a + b = 2 * n + 1) :
    padicValNat p (a.factorial * b.factorial) ≥
    2 * padicValNat p ((n + 1).factorial) := by
  have h_legendre : padicValNat p (Nat.factorial (2 * n + 1)) = 2 * padicValNat p (Nat.factorial (n + 1)) + k := by
    -- Applying Legendre's formula to compute the p-adic valuation of (2n+1)!.
    have h_legendre : padicValNat p ((2 * n + 1)!) = ∑ l ∈ Finset.Ico 1 (k + 1), (2 * p ^ k - 3) / p ^ l := by
      rw [ padicValNat_factorial ];
      congr! 2;
      · omega;
      · refine' Nat.log_lt_of_lt_pow _ _ <;> norm_num [ hn ];
        rw [ pow_succ' ] ; nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ) ];
    -- Applying Legendre's formula to compute the p-adic valuation of (n+1)!.
    have h_legendre_n1 : padicValNat p ((n + 1)!) = ∑ l ∈ Finset.Ico 1 k, (p ^ k - 1) / p ^ l := by
      rw [ padicValNat_factorial ];
      congr! 1;
      · rw [ show n + 1 = p ^ k - 1 by omega ];
      · exact Nat.log_lt_of_lt_pow ( by linarith ) ( by linarith );
    -- Simplify the sum $\sum_{l=1}^{k} \left\lfloor \frac{2p^k - 3}{p^l} \right\rfloor$.
    have h_sum_simplify : ∑ l ∈ Finset.Ico 1 (k + 1), (2 * p ^ k - 3) / p ^ l = ∑ l ∈ Finset.Ico 1 (k + 1), (2 * p ^ (k - l) - 1) := by
      apply Finset.sum_congr rfl
      intro l hl
      have h_div : (2 * p ^ k - 3) = p ^ l * (2 * p ^ (k - l) - 1) + (p ^ l - 3) := by
        zify;
        repeat rw [ Nat.cast_sub ] <;> push_cast <;> repeat nlinarith [ pow_pos ( show 0 < p by exact Nat.Prime.pos Fact.out ) k, pow_pos ( show 0 < p by exact Nat.Prime.pos Fact.out ) l, pow_pos ( show 0 < p by exact Nat.Prime.pos Fact.out ) ( k - l ), Nat.sub_add_cancel ( show l ≤ k from by linarith [ Finset.mem_Ico.mp hl ] ) ] ;
        · rw [ mul_sub, mul_left_comm, ← pow_add, add_tsub_cancel_of_le ( by linarith [ Finset.mem_Ico.mp hl ] ) ] ; ring;
        · exact le_trans ( show 3 ≤ p by exact lt_of_le_of_ne ( Nat.Prime.two_le Fact.out ) ( Ne.symm hp_odd ) ) ( Nat.le_self_pow ( by linarith [ Finset.mem_Ico.mp hl ] ) _ );
      rw [ h_div, Nat.add_div ] <;> norm_num [ Nat.Prime.pos Fact.out ];
      rw [ Nat.div_eq_of_lt, if_neg ] <;> norm_num;
      · exact pow_pos ( Nat.Prime.pos Fact.out ) _;
      · exact pow_pos ( Nat.Prime.pos Fact.out ) _;
    -- Simplify the sum $\sum_{l=1}^{k-1} \left\lfloor \frac{p^k - 1}{p^l} \right\rfloor$.
    have h_sum_simplify_n1 : ∑ l ∈ Finset.Ico 1 k, (p ^ k - 1) / p ^ l = ∑ l ∈ Finset.Ico 1 k, (p ^ (k - l) - 1) := by
      refine Finset.sum_congr rfl fun l hl => ?_;
      -- Let's simplify the expression $(p^k - 1) / p^l$.
      have h_div : p ^ k - 1 = p ^ l * (p ^ (k - l) - 1) + (p ^ l - 1) := by
        zify [ Nat.cast_sub ( show 1 ≤ p ^ k from Nat.one_le_pow _ _ <| Nat.Prime.pos Fact.out ), Nat.cast_sub ( show 1 ≤ p ^ l from Nat.one_le_pow _ _ <| Nat.Prime.pos Fact.out ) ] ; ring;
        rw [ Nat.cast_sub ( Nat.one_le_pow _ _ ( Nat.Prime.pos Fact.out ) ) ] ; push_cast ; rw [ mul_sub, mul_one, ← pow_add, add_tsub_cancel_of_le ( by linarith [ Finset.mem_Ico.mp hl ] ) ] ; ring;
      rw [ h_div, Nat.add_div ] <;> norm_num [ Nat.Prime.pos Fact.out ];
      rw [ Nat.div_eq_of_lt, if_neg ] <;> norm_num [ Nat.sub_lt ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) zero_lt_one ];
    simp_all +decide [ Finset.sum_Ico_succ_top ];
    zify [ Finset.sum_add_distrib ];
    norm_num [ Finset.mul_sum _ _ _, Nat.cast_sub ( show 1 ≤ 2 * p ^ ( k - _ ) from one_le_mul_of_one_le_of_one_le one_le_two ( Nat.one_le_pow _ _ ( Nat.Prime.pos Fact.out ) ) ), Nat.cast_sub ( show 1 ≤ p ^ ( k - _ ) from Nat.one_le_pow _ _ ( Nat.Prime.pos Fact.out ) ) ] ; ring;
    rw [ ← Finset.sum_mul _ _ _ ] ; rw [ Nat.cast_sub hk ] ; ring;
  have h_floor : ∀ l ≥ 1, Nat.floor (a / p ^ l) + Nat.floor (b / p ^ l) ≥ Nat.floor ((2 * n + 1) / p ^ l) - 1 := by
    intro l hl; rw [ ← hab ] ; norm_num [ Nat.add_div ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) ] ;
    split_ifs <;> norm_num;
  have h_legendre : padicValNat p (Nat.factorial a * Nat.factorial b) = ∑ l ∈ Finset.Ico 1 (Nat.log p (2 * n + 1) + 1), (Nat.floor (a / p ^ l) + Nat.floor (b / p ^ l)) := by
    rw [ padicValNat.mul ( by positivity ) ( by positivity ), padicValNat_factorial, padicValNat_factorial ];
    rw [ ← Finset.sum_add_distrib ];
    congr! 1;
    · exact Nat.lt_succ_of_le ( Nat.log_mono_right <| by linarith );
    · exact Nat.lt_succ_of_le ( Nat.log_mono_right <| by linarith );
  have h_legendre : padicValNat p (Nat.factorial (2 * n + 1)) = ∑ l ∈ Finset.Ico 1 (Nat.log p (2 * n + 1) + 1), Nat.floor ((2 * n + 1) / p ^ l) := by
    rw [ padicValNat_factorial ];
    exacts [ Finset.sum_congr rfl fun _ _ => rfl, Nat.lt_succ_self _ ];
  have h_legendre : ∑ l ∈ Finset.Ico 1 (Nat.log p (2 * n + 1) + 1), Nat.floor (a / p ^ l) + ∑ l ∈ Finset.Ico 1 (Nat.log p (2 * n + 1) + 1), Nat.floor (b / p ^ l) ≥ ∑ l ∈ Finset.Ico 1 (Nat.log p (2 * n + 1) + 1), Nat.floor ((2 * n + 1) / p ^ l) - (Nat.log p (2 * n + 1)) := by
    rw [ ← Finset.sum_add_distrib ];
    refine' Nat.sub_le_of_le_add _;
    exact le_trans ( Finset.sum_le_sum fun i hi => show ⌊ ( 2 * n + 1 ) / p ^ i⌋₊ ≤ ⌊a / p ^ i⌋₊ + ⌊b / p ^ i⌋₊ + 1 from by linarith [ h_floor i ( Finset.mem_Ico.mp hi |>.1 ), Nat.sub_add_cancel ( show 1 ≤ ⌊ ( 2 * n + 1 ) / p ^ i⌋₊ from Nat.div_pos ( show p ^ i ≤ 2 * n + 1 from Nat.pow_le_of_le_log ( by linarith ) ( by linarith [ Finset.mem_Ico.mp hi |>.2 ] ) ) ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) ) ] ) ( by simp +arith +decide [ Finset.sum_add_distrib ] );
  have h_log : Nat.log p (2 * n + 1) ≤ k := by
    refine Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ?_ ?_ ) <;> norm_num;
    rw [ pow_succ' ] ; nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ) ];
  simp_all +decide [ Finset.sum_add_distrib ];
  linarith

/-
PROBLEM
The combined polynomial coefficient b_j of c_j·c_{2n+1-j} in B_eval
    is divisible by p^e. This is the core divisibility lemma.
    We show: p^e | (2n)! · (2n+1-2j) · (2n+1-j)! · j! for each j.

PROVIDED SOLUTION
We need p^e | (2n)! · (2n+1-2j) · (2n+1-j)! · j! where e = e_central p n = v_p(C(2n,n)·γ²).

First, e_central p n = padicValNat p (C(2n,n) * γ(n)²).
C(2n,n) * γ(n)² = C(2n,n) * ((n+1)!·n!)² = (2n)!/(n!²) · (n+1)!² · n!² = (2n)! · (n+1)!².
So e = v_p((2n)! · (n+1)!²).

We need: v_p((2n)!) + v_p(|2n+1-2j|) + v_p((2n+1-j)!) + v_p(j!) ≥ v_p((2n)!) + 2·v_p((n+1)!).
Equivalently: v_p(|2n+1-2j|) + v_p((2n+1-j)!) + v_p(j!) ≥ 2·v_p((n+1)!).

From legendre_B_bound: v_p((2n+1-j)!) + v_p(j!) ≥ 2·v_p((n+1)!) (using a = j, b = 2n+1-j, a+b = 2n+1).
And v_p(|2n+1-2j|) ≥ 0 trivially.

So the sum ≥ 2·v_p((n+1)!), which gives the result.

The proof should:
1. Show e_central p n = padicValNat p ((2n)! * (n+1)!²) by unfolding and simplifying C(2n,n)*γ².
2. Use legendre_B_bound to get the factorial valuation bound.
3. Show the product (2n)! * |2n+1-2j| * (2n+1-j)! * j! has v_p ≥ e.
4. Convert the valuation bound to a divisibility statement.

Use Int.natCast_dvd_natCast, pow_padicValNat_dvd, and Dvd.dvd.mul_left/mul_right.
-/
lemma B_coeff_dvd (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n)
    (j : ℕ) (hj : j ≤ 2 * n + 1) :
    (p : ℤ) ^ e_central p n ∣
      ((2 * n).factorial : ℤ) * ((2 * n + 1 : ℤ) - 2 * (j : ℤ)) *
      ((2 * n + 1 - j).factorial : ℤ) * (j.factorial : ℤ) := by
  -- By definition of $e_central$, we know that $p^{e_central p n}$ divides $(Nat.choose (2 * n) n) * (γ n) ^ 2$.
  have h_div : (p : ℤ) ^ e_central p n ∣ (Nat.factorial (2 * n)) * (Nat.factorial (n + 1)) ^ 2 := by
    norm_cast;
    convert Nat.ordProj_dvd _ _ using 1;
    unfold e_central;
    unfold γ; rw [ Nat.factorization_def ] ;
    congr! 1;
    · rw [ Nat.choose_eq_factorial_div_factorial ( by linarith ) ];
      norm_num [ two_mul, Nat.factorial_ne_zero ];
      rw [ show ( n + n ) ! / ( n ! * n ! ) * ( ( n + 1 ) ! * n ! ) ^ 2 = ( n + n ) ! * ( n + 1 ) ! ^ 2 by nlinarith [ Nat.div_mul_cancel ( show n ! * n ! ∣ ( n + n ) ! from Nat.factorial_mul_factorial_dvd_factorial_add _ _ ), Nat.factorial_pos n, Nat.factorial_succ n ] ];
    · exact Fact.out;
  -- From lemma legendre_B_bound, we know that $v_p((2n+1-j)!) + v_p(j!) \geq 2v_p((n+1)!)$.
  have h_val : padicValNat p ((Nat.factorial (2 * n + 1 - j)) * (Nat.factorial j)) ≥ 2 * padicValNat p (Nat.factorial (n + 1)) := by
    exact legendre_B_bound p k hk hp_odd n hn ( 2 * n + 1 - j ) j ( by rw [ Nat.sub_add_cancel hj ] );
  -- Therefore, $p^{e_central p n}$ divides $(Nat.factorial (2 * n)) * (Nat.factorial (2 * n + 1 - j)) * (Nat.factorial j)$.
  have h_div_final : (p : ℤ) ^ e_central p n ∣ (Nat.factorial (2 * n)) * (Nat.factorial (2 * n + 1 - j)) * (Nat.factorial j) := by
    have h_div_final : (p : ℤ) ^ (padicValNat p ((Nat.factorial (2 * n)) * (Nat.factorial (n + 1)) ^ 2)) ∣ (Nat.factorial (2 * n)) * (Nat.factorial (2 * n + 1 - j)) * (Nat.factorial j) := by
      have h_div_final : padicValNat p ((Nat.factorial (2 * n)) * (Nat.factorial (2 * n + 1 - j)) * (Nat.factorial j)) ≥ padicValNat p ((Nat.factorial (2 * n)) * (Nat.factorial (n + 1)) ^ 2) := by
        rw [ mul_assoc, padicValNat.mul, padicValNat.mul ] <;> simp_all +decide [ Nat.factorial_ne_zero ];
        rw [ padicValNat.mul, padicValNat.pow ] <;> simp_all +decide [ Nat.factorial_ne_zero ];
        rwa [ padicValNat.mul ( Nat.factorial_ne_zero _ ) ( Nat.factorial_ne_zero _ ) ] at h_val;
      norm_cast;
      rw [ padicValNat_dvd_iff ] at * ; aesop;
    convert h_div_final using 1;
    unfold e_central; simp +decide [ Nat.choose_eq_factorial_div_factorial ( show n ≤ 2 * n by linarith ) ] ; ring;
    unfold γ; rw [ show n * 2 - n = n by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring;
    rw [ show n ! ^ 2 * ( ( n * 2 ) ! / n ! ^ 2 ) = ( n * 2 ) ! from Nat.mul_div_cancel' ( by rw [ sq ] ; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| by ring_nf; norm_num ) ] ; ring;
  convert h_div_final.mul_left ( 2 * n + 1 - 2 * j : ℤ ) using 1 ; ring

/-
PROBLEM
p^e divides each scalar coefficient of B_n, hence p^e divides B_eval.

PROVIDED SOLUTION
APPROACH: Rewrite B_eval by splitting into α² and β² sums, reindexing the β² sum using β(n,i) = α(n,i+1), then combining.

Step 1: Split B_eval into S_α + S_β where
  S_α = Σ_{i ∈ range(2n+1)} (-1)^i C(2n,i) α(n,i)² c_i c_{2n+1-i}
  S_β = Σ_{i ∈ range(2n+1)} (-1)^i C(2n,i) β(n,i)² c_{i+1} c_{2n-i}

Step 2: In S_β, use beta_eq_alpha_succ: β(n,i) = α(n,i+1) for i ≤ 2n-1. For the i=2n term, β(n,2n) = (0)!·(2n+1)! = α(n,2n+1) directly.

Step 3: Reindex S_β with j = i+1 (so i = j-1, j goes from 1 to 2n+1):
  S_β = Σ_{j=1}^{2n+1} (-1)^{j-1} C(2n,j-1) α(n,j)² c_j c_{2n+1-j}
      = -Σ_{j=1}^{2n+1} (-1)^j C(2n,j-1) α(n,j)² c_j c_{2n+1-j}

Step 4: B_eval = S_α + S_β = Σ_{j=0}^{2n+1} (-1)^j D_j c_j c_{2n+1-j}
where D_j = C(2n,j)α(n,j)² - C(2n,j-1)α(n,j)² = [C(2n,j) - C(2n,j-1)] α(n,j)²
(with C(2n,-1) = 0 handled by the sum range, and C(2n,2n+1) = 0 by Nat.choose).

Step 5: From alpha_sq_scalar_eq, D_j = (2n)! · (2n+1-2j) · (2n+1-j)! · j! (up to sign).
More precisely, the total coefficient (-1)^j D_j c_j c_{2n+1-j} has the scalar part ±(2n)!·(2n+1-2j)·(2n+1-j)!·j!.

Step 6: By B_coeff_dvd, p^e divides this scalar for each j.

Step 7: By Finset.dvd_sum (or dvd_sum), p^e divides B_eval.

HOWEVER, this sum manipulation is complex. A SIMPLER APPROACH for the subagent:

Use `Finset.dvd_sum`. We need to show p^e divides each summand of B_eval. But individual summands involve α² and β² which aren't separately divisible by p^e.

The KEY trick: rewrite each summand using alpha_sq_scalar_eq and beta_sq_scalar_eq:
summand_i = (-1)^i (2n)! (2n-i)! i! [(2n+1-i)² c_i c_{2n+1-i} + (i+1)² c_{i+1} c_{2n-i}]

Factor out (2n)!:
B_eval = (2n)! * Σ_i (-1)^i (2n-i)! i! [(2n+1-i)² c_i c_{2n+1-i} + (i+1)² c_{i+1} c_{2n-i}]

Now e = v_p((2n)! * (n+1)!²). So we need (n+1)!² to divide the inner sum.

The inner sum can be rewritten (by reindexing the (i+1)² part):
Σ_i (-1)^i (2n-i)! i! (2n+1-i)² c_i c_{2n+1-i} + Σ_i (-1)^i (2n-i)! i! (i+1)² c_{i+1} c_{2n-i}

The second sum, with j = i+1:
= Σ_{j=1}^{2n+1} (-1)^{j-1} (2n+1-j)! (j-1)! j² c_j c_{2n+1-j}
= -Σ_{j=1}^{2n+1} (-1)^j (2n+1-j)! (j-1)! j² c_j c_{2n+1-j}

Combined coefficient of (-1)^j c_j c_{2n+1-j} for 1 ≤ j ≤ 2n:
(2n-j)! j! (2n+1-j)² - (2n+1-j)! (j-1)! j²
= (2n-j)! (j-1)! [j(2n+1-j)² - (2n+1-j)j²]   [factor out common terms]
= (2n-j)! (j-1)! j(2n+1-j)(2n+1-2j)
= (2n-j)! j! (2n+1-j)(2n+1-2j)

And (2n+1-j)(2n-j)! = (2n+1-j)!, so:
= (2n+1-j)! j! (2n+1-2j)

And the coefficient of (-1)^j c_j c_{2n+1-j} in B_eval is:
(2n)! * (2n+1-j)! * j! * (2n+1-2j) for 1 ≤ j ≤ 2n.

By B_coeff_dvd, p^e divides this. Similarly for j=0 and j=2n+1.

So B_eval = Σ_{j=0}^{2n+1} (-1)^j (2n)! (2n+1-2j) (2n+1-j)! j! c_j c_{2n+1-j}
and each term is divisible by p^e, so the sum is too.

Use Finset.dvd_sum after proving the rewriting identity.

ALTERNATIVELY, A MUCH SIMPLER approach: just apply Finset.dvd_sum to the COMBINED sum (after rewriting). Since the subagent can work with the full Lean API, it can do the sum manipulation using Finset.sum_add_distrib, Finset.sum_bij, etc.
-/
theorem B_eval_dvd_pe (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k)
    (hp_odd : p ≠ 2) (n : ℕ) (hn : n + 2 = p ^ k) (hn_pos : 1 ≤ n) (c : ℕ → ℤ) :
    ∃ B' : ℤ, B_eval n c = (p : ℤ) ^ e_central p n * B' := by
  -- By definition of $B_{\text{eval}}$, we can write it as a sum of terms involving $c$.
  have h_sum : B_eval n c = (∑ j ∈ Finset.range (2 * n + 2), (-1 : ℤ) ^ j * ((2 * n) ! * (2 * n + 1 - 2 * j) * (2 * n + 1 - j) ! * j !) * c j * c (2 * n + 1 - j)) := by
    unfold B_eval;
    have h_split : ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * ((α n i : ℤ) ^ 2 * c i * c (2 * n + 1 - i) + (β n i : ℤ) ^ 2 * c (i + 1) * c (2 * n - i)) =
      ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((2 * n) ! * (2 * n + 1 - i) ^ 2 * (2 * n - i) ! * i ! : ℤ) * c i * c (2 * n + 1 - i) +
      ∑ j ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ j * ((2 * n) ! * (j + 1) ^ 2 * (2 * n - j) ! * j ! : ℤ) * c (j + 1) * c (2 * n - j) := by
        simp +decide only [mul_add, Finset.sum_add_distrib];
        refine' congrArg₂ ( · + · ) _ _ <;> refine' Finset.sum_congr rfl fun i hi => _ <;> norm_cast <;> norm_num [ Nat.choose_eq_factorial_div_factorial ( show i ≤ 2 * n from by linarith [ Finset.mem_range.mp hi ] ), alpha_sq_scalar_eq, beta_sq_scalar_eq ] ; ring;
        · unfold α; norm_num [ Int.subNatNat_of_le ( by linarith [ Finset.mem_range.mp hi ] : i ≤ 1 + n * 2 ) ] ; ring;
          rw [ show ( 1 + n * 2 - i ) = ( n * 2 - i ) + 1 by rw [ tsub_add_eq_add_tsub ( by linarith [ Finset.mem_range.mp hi ] ) ] ; ring ] ; norm_num [ Nat.factorial_succ ] ; ring;
          rw [ ← Int.mul_ediv_assoc ];
          · rw [ show ( Int.negSucc 0 ^ i * i ! ^ 2 * ( n * 2 - i ) ! ^ 2 * ( n * 2 ) ! : ℤ ) / ( i ! * ( n * 2 - i ) ! ) = Int.negSucc 0 ^ i * i ! * ( n * 2 - i ) ! * ( n * 2 ) ! from Int.ediv_eq_of_eq_mul_left ( by positivity ) <| by ring ] ; ring;
          · exact_mod_cast Nat.factorial_mul_factorial_dvd_factorial ( by linarith [ Finset.mem_range.mp hi ] );
        · rw [ show β n i = ( 2 * n - i ) ! * ( i + 1 ) ! from rfl ] ; ring; norm_cast; simp +decide [ Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm, Nat.div_mul_cancel, Nat.factorial_ne_zero ] ; ring;
          rw [ show ( 1 + i ) ! = ( i ! ) * ( i + 1 ) by rw [ Nat.add_comm, Nat.factorial_succ ] ; ring ] ; ring; norm_cast; simp +decide [ Nat.factorial_ne_zero, Nat.factorial_succ, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel, Nat.factorial_ne_zero, Nat.factorial_succ ] ; ring;
          rw [ show ( n * 2 ) ! = ( n * 2 - i ) ! * i ! * ( Nat.choose ( n * 2 ) i ) by rw [ ← Nat.choose_mul_factorial_mul_factorial ( show i ≤ n * 2 from by linarith [ Finset.mem_range.mp hi ] ) ] ; ring ] ; norm_num [ Nat.factorial_ne_zero, Nat.mul_div_mul_left, Nat.mul_div_assoc ] ; ring;
    have h_reindex : ∑ j ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ j * ((2 * n) ! * (j + 1) ^ 2 * (2 * n - j) ! * j ! : ℤ) * c (j + 1) * c (2 * n - j) =
      ∑ j ∈ Finset.range (2 * n + 2), (-1 : ℤ) ^ (j - 1) * ((2 * n) ! * j ^ 2 * (2 * n + 1 - j) ! * (j - 1) ! : ℤ) * c j * c (2 * n + 1 - j) * (if j = 0 then 0 else 1) := by
        rw [ Finset.sum_range_succ' ];
        rw [ Finset.sum_range_succ' ] ; norm_num [ Finset.sum_range_succ ] ;
        rw [ ← eq_comm ] ; have := Finset.sum_range_sub ( fun x => ( -1 : ℤ ) ^ x * ( ( 2 * n ) ! * ( x + 1 ) ^ 2 * ( 2 * n + 1 - ( x + 1 ) ) ! * x ! : ℤ ) * c ( x + 1 ) * c ( 2 * n + 1 - ( x + 1 ) ) ) ( 2 * n ) ; simp_all +decide [ Finset.sum_range_succ ] ;
        grind;
    rw [ h_split, h_reindex ];
    rw [ Finset.sum_range_succ' ];
    rw [ Finset.sum_range_succ' _ ( 2 * n + 1 ) ] ; norm_num [ Finset.sum_range_succ _ ( 2 * n ) ] ; ring;
    rw [ show 2 + n * 2 = n * 2 + 2 by ring, Finset.sum_range_succ' ] ; norm_num [ Finset.sum_range_succ _ ( n * 2 ) ] ; ring;
    norm_num [ Nat.add_comm 1, Nat.factorial_succ ] ; ring;
    norm_num [ add_comm 1, add_assoc, add_tsub_add_eq_tsub_left, tsub_tsub ] ; ring;
    rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Nat.add_sub_add_left ] ; ring;
    rw [ show n * 2 - x = n * 2 - ( 1 + x ) + 1 by exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 + x ≤ n * 2 from by linarith [ Finset.mem_range.mp hx ] ] ] ; norm_num [ Nat.factorial_succ ] ; ring;
    rw [ Nat.cast_sub ( by linarith [ Finset.mem_range.mp hx ] ) ] ; push_cast ; ring;
  -- Apply the lemma B_coeff_dvd to each term in the sum.
  have h_div : ∀ j ∈ Finset.range (2 * n + 2), (p : ℤ) ^ e_central p n ∣ ((2 * n) ! * (2 * n + 1 - 2 * j) * (2 * n + 1 - j) ! * j !) * c j * c (2 * n + 1 - j) := by
    intro j hj
    have h_div_term : (p : ℤ) ^ e_central p n ∣ ((2 * n) ! * (2 * n + 1 - 2 * j) * (2 * n + 1 - j) ! * j !) := by
      convert B_coeff_dvd p k hk hp_odd n hn hn_pos j ( Finset.mem_range_succ_iff.mp hj ) using 1
    exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left h_div_term _ ) _;
  exact h_sum.symm ▸ Finset.dvd_sum fun i hi => by simpa only [ mul_assoc ] using dvd_mul_of_dvd_right ( h_div i hi ) _;

end QuarticInvariant
