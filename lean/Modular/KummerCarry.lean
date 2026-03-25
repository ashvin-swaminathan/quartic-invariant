import Mathlib
import Modular.Defs
import Modular.CentralDom

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant


/-
PROBLEM
============================================================
Helper lemmas
============================================================

p^{k-1} ≤ n when n + 2 = p^k, p ≥ 3, k ≥ 2.

PROVIDED SOLUTION
p ≥ 3 (odd prime), k ≥ 2, n = p^k - 2.
p^{k-1} ≤ p^k - 2 because p^k - p^{k-1} = p^{k-1}(p-1) ≥ p^{k-1}*2 ≥ 2, so p^{k-1} ≤ p^k - 2 = n.
-/
lemma pk_sub_one_le_n (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) :
    p ^ (k - 1) ≤ n := by
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
  nlinarith [ hp.1.two_le, pow_pos hp.1.pos k ]

/-- n - p^{k-1} ≤ 2*n -/
lemma sub_le_two_mul (n t : ℕ) : n - t ≤ 2 * n := by omega

/-- Key Kummer difference: v_p(C(2n,n)) - v_p(C(2n,n-t)) = 1 when n+2 = p^k, t = p^{k-1}.
This works for ALL odd primes, not just p ≥ 5.

Proof via carry counting (padicValNat_choose):
Both C(2n,n) and C(2n,n-t) count carries when adding their two summands.
For i ≤ k-1: both n%p^i and (n±t)%p^i equal p^i-2 (since p^i | p^{k-1} | p^k).
  So carry condition is the same for both: 2(p^i-2) ≥ p^i iff p^i ≥ 4.
For i = k:
  n+n has 2(n%p^k) = 2(p^k-2) = 2p^k-4 ≥ p^k (carry, since p^k ≥ 4 for p≥3,k≥2).
  (n-t)+(n+t) has (p^k-p^{k-1}-2)+(p^{k-1}-2) = p^k-4 < p^k (no carry).
For i > k: neither carries.
So the difference is exactly 1 (at position k).

PROVIDED SOLUTION
Use `padicValNat_choose` (carry-counting Kummer) for both C(2n,n) and C(2n,n-t) with b = k+1.

For C(2n, n): the carry set is {i ∈ Ico 1 (k+1) : p^i ≤ 2*(n % p^i)}.
For C(2n, n-t): the carry set is {i ∈ Ico 1 (k+1) : p^i ≤ (n-t) % p^i + (n+t) % p^i}.

Key modular arithmetic:
For all i with 1 ≤ i ≤ k: n % p^i = p^i - 2 (since n = p^k - 2 and p^i | p^k).
For all i with 1 ≤ i ≤ k-1: (n-t) % p^i = p^i - 2 and (n+t) % p^i = p^i - 2
  (since p^i | p^{k-1} for i ≤ k-1).

So for i ≤ k-1, both carry conditions are the same: 2(p^i - 2) ≥ p^i.

The difference is at position k:
- For C(2n,n): 2*(n % p^k) = 2*(p^k-2) = 2p^k-4 ≥ p^k (since p^k ≥ 4 for p≥3,k≥2). CARRY.
- For C(2n,n-t): (n-t) % p^k + (n+t) % p^k = (p^k-p^{k-1}-2) + (p^{k-1}-2) = p^k-4 < p^k. NO CARRY.

For i > k: both have no carry (2n < p^{k+1}).

So the carry set for C(2n,n) has exactly one more element (position k) than for C(2n,n-t).

Therefore v_p(C(2n,n)) = v_p(C(2n,n-t)) + 1.

Implementation approach: Show both carry sets explicitly, show the first equals Ico 1 (k+1) filtered by carry ≥ some condition, and the second is the same filter but excluding position k. The key is that at positions 1..k-1 both have the same status, at position k one has carry and the other doesn't.

Alternative cleaner approach: Show the carry set for C(2n,n) = S, and the carry set for C(2n,n-t) = S \ {k}. Then card(S) = card(S \ {k}) + 1 since k ∈ S.

Or use the identity: v_p(C(2n,n)) - v_p(C(2n,n-t)) = v_p((n+t)!) + v_p((n-t)!) - 2*v_p(n!).
This follows from v_p(C(m,j)) = v_p(m!) - v_p(j!) - v_p((m-j)!).
Then use Legendre's formula to compute the factorial difference:
(p-1) * [V(n+t) + V(n-t) - 2*V(n)] = 2*s_p(n) - s_p(n+t) - s_p(n-t)
where s_p is the digit sum.

Using sub_one_mul_padicValNat_factorial: (p-1)*V(m) = m - s_p(m).
So (p-1)*[V(n+t)+V(n-t)-2*V(n)] = (n+t)+(n-t)-2n - [s(n+t)+s(n-t)-2*s(n)] = -[s(n+t)+s(n-t)-2*s(n)].

The digit sums:
s_p(n) = s_p(p^k-2) = (p-2) + (k-1)(p-1) [digits: p-2 at pos 0, p-1 at pos 1..k-1]
s_p(n+t) = s_p(p^k+p^{k-1}-2): digits are p-2 at pos 0, p-1 at pos 1..k-2, 0 at pos k-1, 1 at pos k.
  s_p(n+t) = (p-2) + (k-2)(p-1) + 0 + 1
s_p(n-t) = s_p(p^k-p^{k-1}-2): digits are p-2 at pos 0, p-1 at pos 1..k-2, p-2 at pos k-1.
  s_p(n-t) = (p-2) + (k-2)(p-1) + (p-2)

2*s(n) - s(n+t) - s(n-t) = 2[(p-2)+(k-1)(p-1)] - [(p-2)+(k-2)(p-1)+1] - [(p-2)+(k-2)(p-1)+(p-2)]
= 2(p-2)+2(k-1)(p-1) - 2(p-2) - 2(k-2)(p-1) - 1 - (p-2)
= 2(p-1) - (p-1)
= p-1.

So (p-1)*[V(n+t)+V(n-t)-2*V(n)] = -(p-1), giving V(n+t)+V(n-t)-2*V(n) = -1.
Wait, that gives -1, but we want +1. Let me recheck.

v_p(C(2n,n)) = V(2n) - 2*V(n)
v_p(C(2n,n-t)) = V(2n) - V(n-t) - V(n+t)
v_p(C(2n,n)) - v_p(C(2n,n-t)) = V(n+t) + V(n-t) - 2*V(n)

(p-1)*[V(n+t) + V(n-t) - 2*V(n)] = -[s(n+t) + s(n-t) - 2*s(n)]
= -(s(n+t) + s(n-t) - 2*s(n))
= -(-(p-1)) [from above: 2*s(n) - s(n+t) - s(n-t) = p-1, so s(n+t)+s(n-t)-2*s(n) = -(p-1)]
= p-1.

So V(n+t)+V(n-t)-2*V(n) = 1. ✓ v_p(C(2n,n)) - v_p(C(2n,n-t)) = 1. ✓

Actually, the cleanest approach might be to use sub_one_mul_padicValNat_choose_eq_sub_sum_digits' directly:
(p-1)*v_p(C(2n,n)) = 2*s_p(n) - s_p(2n)
(p-1)*v_p(C(2n,n-t)) = s_p(n-t) + s_p(n+t) - s_p(2n)

Subtracting: (p-1)*[v_p(C(2n,n)) - v_p(C(2n,n-t))] = 2*s_p(n) - s_p(n-t) - s_p(n+t) = p-1.
So the difference is 1.
-/
lemma kummer_difference (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) :
    padicValNat p (Nat.choose (2 * n) n) =
      padicValNat p (Nat.choose (2 * n) (n - p ^ (k - 1))) + 1 := by
  -- Substitute the geometric series sum into the inequality.
  have h_geo_sum : ∑ i ∈ Finset.Ico 1 (k + 1), (p - 1) * p ^ (i - 1) = p ^ k - 1 := by
    exact eq_tsub_of_add_eq <| Nat.recOn k ( by norm_num ) fun n ihn => by cases p <;> simp_all +decide [ Nat.pow_succ', Finset.sum_Ico_succ_top ] ; linarith;
  -- Applying the lemma on padicValNat_choose to both C(2n, n) and C(2n, n-t), we can express the difference in their p-adic valuations as the sum of the differences in their digit sums.
  have h_diff : padicValNat p (Nat.choose (2 * n) n) - padicValNat p (Nat.choose (2 * n) (n - p ^ (k - 1))) = (∑ i ∈ Finset.Ico 1 (k + 1), (if 2 * (n % p ^ i) ≥ p ^ i then 1 else 0)) - (∑ i ∈ Finset.Ico 1 (k + 1), (if (n - p ^ (k - 1)) % p ^ i + (n + p ^ (k - 1)) % p ^ i ≥ p ^ i then 1 else 0)) := by
    rw [ padicValNat_choose, padicValNat_choose ];
    any_goals exact Nat.lt_succ_self _;
    · rw [ show Nat.log p ( 2 * n ) = k from ?_, Finset.card_filter, Finset.card_filter ];
      · simp +decide [ two_mul, add_assoc, add_tsub_assoc_of_le ( show n - p ^ ( k - 1 ) ≤ n from Nat.sub_le _ _ ) ];
        rw [ Nat.sub_sub_self ( show p ^ ( k - 1 ) ≤ n from _ ) ];
        rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
        nlinarith [ show p > 2 from lt_of_le_of_ne ( Nat.Prime.two_le Fact.out ) ( Ne.symm hp_odd ) ];
      · rw [ Nat.log_eq_iff ] <;> norm_num;
        · exact ⟨ by linarith [ show p ^ k ≥ 4 by exact le_trans ( by decide ) ( Nat.pow_le_pow_left ( show p ≥ 2 by exact Nat.Prime.two_le Fact.out ) _ |> le_trans <| Nat.pow_le_pow_right ( Nat.Prime.pos Fact.out ) hk ) ], by rw [ pow_succ' ] ; nlinarith [ show p ≥ 3 by exact lt_of_le_of_ne ( Nat.Prime.two_le Fact.out ) ( Ne.symm hp_odd ) ] ⟩;
        · exact Or.inl ( by linarith );
    · exact le_trans ( Nat.sub_le _ _ ) ( by linarith );
    · grind;
  -- For $i \leq k-1$, both $n \mod p^i$ and $(n - p^{k-1}) \mod p^i$ are equal to $p^i - 2$, so the carry condition is the same.
  have h_carry_same : ∀ i ∈ Finset.Ico 1 k, (2 * (n % p ^ i) ≥ p ^ i) ↔ ((n - p ^ (k - 1)) % p ^ i + (n + p ^ (k - 1)) % p ^ i ≥ p ^ i) := by
    intro i hi
    have h_mod : n % p ^ i = p ^ i - 2 := by
      rw [ show n = p ^ k - 2 by rw [ ← hn, Nat.add_sub_cancel ] ];
      -- Since $p^k \equiv 0 \pmod{p^i}$, we have $p^k - 2 \equiv -2 \pmod{p^i}$.
      have h_mod : (p ^ k - 2) % p ^ i = (p ^ i - 2) % p ^ i := by
        refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_;
        rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num <;> try linarith [ pow_pos ( Fact.out ( p := p.Prime ) |> Nat.Prime.pos ) k, pow_pos ( Fact.out ( p := p.Prime ) |> Nat.Prime.pos ) i ] ;
        · exact pow_dvd_pow _ ( Finset.mem_Ico.mp hi |>.2.le );
        · exact le_trans ( Nat.Prime.two_le Fact.out ) ( Nat.le_self_pow ( by linarith [ Finset.mem_Ico.mp hi ] ) _ );
      rw [ h_mod, Nat.mod_eq_of_lt ( Nat.sub_lt ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) zero_lt_two ) ]
    have h_mod_sub : (n - p ^ (k - 1)) % p ^ i = p ^ i - 2 := by
      have h_mod_sub : (n - p ^ (k - 1)) % p ^ i = (n % p ^ i) := by
        refine Nat.modEq_of_dvd ?_;
        rw [ Nat.cast_sub ] <;> norm_num;
        · exact pow_dvd_pow _ ( Nat.le_pred_of_lt ( Finset.mem_Ico.mp hi |>.2 ) );
        · rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
          nlinarith [ show p > 2 from lt_of_le_of_ne ( Nat.Prime.two_le Fact.out ) ( Ne.symm hp_odd ) ];
      rw [h_mod_sub, h_mod]
    have h_mod_add : (n + p ^ (k - 1)) % p ^ i = p ^ i - 2 := by
      rw [ ← h_mod, Nat.add_mod ];
      norm_num [ Nat.mod_eq_zero_of_dvd ( pow_dvd_pow _ ( Nat.le_sub_one_of_lt ( Finset.mem_Ico.mp hi |>.2 ) ) ) ]
    simp [h_mod, h_mod_sub, h_mod_add];
    constructor <;> intro <;> omega;
  -- For $i = k$, the carry condition for $C(2n, n)$ is true, but for $C(2n, n-t)$ it is false.
  have h_carry_k : (2 * (n % p ^ k) ≥ p ^ k) ∧ ¬((n - p ^ (k - 1)) % p ^ k + (n + p ^ (k - 1)) % p ^ k ≥ p ^ k) := by
    rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
    rw [ show n % ( p * p ^ k ) = p * p ^ k - 2 by rw [ ← hn, Nat.add_sub_cancel, Nat.mod_eq_of_lt ] ; nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ), pow_pos ( Nat.Prime.pos ( Fact.out : Nat.Prime p ) ) k ] ] ; rw [ show n - p ^ k = p * p ^ k - 2 - p ^ k by rw [ ← hn, Nat.add_sub_cancel ] ] ; rw [ show n + p ^ k = p * p ^ k - 2 + p ^ k by rw [ ← hn, Nat.add_sub_cancel ] ] ; ring_nf ; norm_num [ Nat.mod_eq_of_lt, Nat.sub_sub ] ;
    constructor <;> try nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ), pow_le_pow_right₀ ( show 1 ≤ p by exact Nat.Prime.pos ( Fact.out : Nat.Prime p ) ) hk, Nat.sub_add_cancel ( show 2 ≤ p * p ^ k from by nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ), pow_le_pow_right₀ ( show 1 ≤ p by exact Nat.Prime.pos ( Fact.out : Nat.Prime p ) ) hk ] ) ] ;
    rw [ Nat.mod_eq_sub_mod ] <;> norm_num [ Nat.add_comm 2, Nat.add_sub_add_left ];
    · rw [ Nat.mod_eq_of_lt ] <;> norm_num [ Nat.add_sub_add_left, ← hn ];
      · linarith [ Nat.sub_add_cancel ( show p ^ k + 2 ≤ n + 2 from by nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ), pow_le_pow_right₀ ( show 1 ≤ p by exact Nat.Prime.pos ( Fact.out : Nat.Prime p ) ) hk ] ), Nat.sub_add_cancel ( show n + 2 ≤ p ^ k + n from by nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ), pow_le_pow_right₀ ( show 1 ≤ p by exact Nat.Prime.pos ( Fact.out : Nat.Prime p ) ) hk ] ) ];
      · rw [ tsub_lt_iff_left ] <;> nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ), pow_le_pow_right₀ ( show 1 ≤ p by exact Nat.Prime.pos ( Fact.out : Nat.Prime p ) ) hk ] ;
    · nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ), pow_le_pow_right₀ ( show 1 ≤ p by exact Nat.Prime.pos ( Fact.out : Nat.Prime p ) ) hk, Nat.sub_add_cancel ( show 2 ≤ p * p ^ k from by nlinarith [ Nat.Prime.one_lt ( Fact.out : Nat.Prime p ), pow_le_pow_right₀ ( show 1 ≤ p by exact Nat.Prime.pos ( Fact.out : Nat.Prime p ) ) hk ] ) ];
  -- Using the results about the carry conditions, we can simplify the difference in the sums.
  have h_sum_diff : (∑ i ∈ Finset.Ico 1 (k + 1), (if 2 * (n % p ^ i) ≥ p ^ i then 1 else 0)) - (∑ i ∈ Finset.Ico 1 (k + 1), (if (n - p ^ (k - 1)) % p ^ i + (n + p ^ (k - 1)) % p ^ i ≥ p ^ i then 1 else 0)) = 1 := by
    rw [ Finset.sum_Ico_succ_top, Finset.sum_Ico_succ_top ] <;> norm_num [ h_carry_k ];
    · rw [ Finset.filter_congr fun x hx => by aesop ] ; norm_num;
    · linarith;
    · linarith;
  omega

/-
PROBLEM
v_p(n+1) = 0 since n+1 = p^k - 1 ≡ -1 (mod p).

PROVIDED SOLUTION
n + 1 = p^k - 1. We need v_p(p^k - 1) = 0. Since p | p^k, p^k ≡ 0 mod p, so p^k - 1 ≡ -1 mod p. Since p ≥ 3, -1 is not 0 mod p. So p ∤ (n+1), giving v_p(n+1) = 0.
Use `padicValNat.eq_zero_of_not_dvd` and show ¬(p ∣ (n+1)) by showing (n+1) % p = p - 1 ≠ 0.
-/
lemma padicValNat_n_succ (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) :
    padicValNat p (n + 1) = 0 := by
  rw [ padicValNat.eq_zero_of_not_dvd ];
  rw [ ← Int.natCast_dvd_natCast ] ; norm_num; erw [ show ( n + 1 : ℤ ) = p ^ k - 1 by linarith ] ; erw [ dvd_sub_comm ] ; haveI := Fact.mk ( Fact.out : Nat.Prime p ) ; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
  cases k <;> aesop

/-
PROBLEM
v_p(n + p^{k-1} + 1) = 0 since this equals p^k + p^{k-1} - 1 ≡ -1 (mod p).

PROVIDED SOLUTION
n + p^{k-1} + 1 = p^k - 2 + p^{k-1} + 1 = p^k + p^{k-1} - 1. Since p | p^k and p | p^{k-1}, this ≡ -1 (mod p). Since p ≥ 3, -1 ≢ 0 (mod p). So p ∤ (n + p^{k-1} + 1), giving v_p = 0.
Use `padicValNat.eq_zero_of_not_dvd` and show ¬(p ∣ (n + p^{k-1} + 1)) by showing (n + p^{k-1} + 1) % p = p - 1 ≠ 0.
-/
lemma padicValNat_n_add_pk_succ (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) :
    padicValNat p (n + p ^ (k - 1) + 1) = 0 := by
  rw [ show n + p ^ ( k - 1 ) + 1 = p ^ k + p ^ ( k - 1 ) - 1 by omega ];
  rw [ padicValNat.eq_zero_of_not_dvd ];
  rw [ ← ZMod.natCast_eq_zero_iff ] ; rcases p with ( _ | _ | p ) <;> rcases k with ( _ | _ | k ) <;> norm_num [ Nat.succ_eq_add_one, pow_succ' ] at *;
  exact False.elim <| Fact.out

/-
PROBLEM
v_p(n - p^{k-1}) = 0 since n - t = p^{k-1}(p-1) - 2 ≡ -2 (mod p).

PROVIDED SOLUTION
n - p^{k-1} = p^k - 2 - p^{k-1} = p^{k-1}(p-1) - 2 ≡ -2 (mod p). Since p ≥ 3, -2 ≢ 0 (mod p). So p ∤ (n - p^{k-1}), giving v_p = 0.
Use `padicValNat.eq_zero_of_not_dvd` and show ¬(p ∣ (n - p^{k-1})). Key: (n - p^{k-1}) % p = (p^k - 2 - p^{k-1}) % p = (p - 2) % p = p - 2 ≠ 0.
-/
lemma padicValNat_n_sub_pk (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) :
    padicValNat p (n - p ^ (k - 1)) = 0 := by
  rw [ padicValNat.eq_zero_of_not_dvd ];
  rw [ ← Nat.modEq_zero_iff_dvd ];
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
  rw [ Nat.cast_sub ] <;> norm_num [ pow_succ' ] at *;
  · rw [ show n = p * ( p * p ^ k ) - 2 by rw [ ← hn, Nat.add_sub_cancel ] ] ; norm_num [ Nat.cast_sub ( show 2 ≤ p * ( p * p ^ k ) from by nlinarith [ show p > 1 from Fact.out, show p * p ^ k > 0 from mul_pos ( Nat.Prime.pos Fact.out ) ( pow_pos ( Nat.Prime.pos Fact.out ) _ ) ] ) ] ; ring_nf ;
    erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by norm_num ) ( lt_of_le_of_ne ( Nat.Prime.two_le Fact.out ) ( Ne.symm hp_odd ) );
  · nlinarith [ show p > 2 from lt_of_le_of_ne ( Nat.Prime.two_le Fact.out ) ( Ne.symm hp_odd ) ]

/-
PROBLEM
β(n, n-t-1) = α(n, n-t) when t ≤ n-1.
Since β(n,i) = (2n-i)!*(i+1)! and α(n,j) = (2n+1-j)!*j!.
At i = n-t-1: β = (n+t+1)!*(n-t)!
At j = n-t: α = (n+t+1)!*(n-t)!
So they're equal.

PROVIDED SOLUTION
β(n, n-t-1) = (2n - (n-t-1))! * (n-t-1+1)! = (n+t+1)! * (n-t)!
α(n, n-t) = (2n+1-(n-t))! * (n-t)! = (n+t+1)! * (n-t)!
They are equal. Just unfold the definitions of α and β, and show 2*n+1-(n-t) = n+t+1 and 2*n-(n-t-1) = n+t+1 and (n-t-1)+1 = n-t. All arithmetic identities with ht : t+1 ≤ n.
-/
lemma beta_eq_alpha (n : ℕ) (t : ℕ) (ht : t + 1 ≤ n) :
    β n (n - t - 1) = α n (n - t) := by
  unfold β α;
  grind

/-
PROBLEM
============================================================
Main theorems
============================================================

v_p(C(2n, n-t) * α(n, n-t)²) = e_central + 1 when t = p^{k-1} and n+2 = p^k.

Proof sketch:
  Write V(m) = v_p(m!).
  v_p(C(2n,n-t)*α²) = V(2n) + V(n-t) - V(n+t) + 2*V(n+t+1)
  e_central = V(2n) + 2*V(n+1)

  Diff = V(n-t) + V(n+t) + 2*v_p(n+t+1) - 2*V(n) - 2*v_p(n+1)
       = [V(n+t)+V(n-t)-2*V(n)] + 2*(v_p(n+t+1) - v_p(n+1))
       = [v_p(C(2n,n)) - v_p(C(2n,n-t))] + 0
       = 1.

PROVIDED SOLUTION
The proof computes the p-adic valuation of both sides and shows they are equal.

Step 1: Unfold definitions.
  α(n, n-t) = (2n+1-(n-t))! * (n-t)! = (n+t+1)! * (n-t)!
  where t = p^{k-1}, n+t+1 = p^k + p^{k-1} - 1, and 2n+1-(n-t) = n+t+1.

  γ(n) = (n+1)! * n!
  e_central = v_p(C(2n,n) * γ²) = v_p(C(2n,n)) + 2*v_p((n+1)! * n!)
            = v_p(C(2n,n)) + 2*v_p((n+1)!) + 2*v_p(n!)

Step 2: Compute LHS.
  LHS = v_p(C(2n,n-t) * (α(n,n-t))²)
      = v_p(C(2n,n-t)) + 2*v_p((n+t+1)! * (n-t)!)
      = v_p(C(2n,n-t)) + 2*v_p((n+t+1)!) + 2*v_p((n-t)!)

Step 3: Compute RHS = e_central + 1.
  RHS = v_p(C(2n,n)) + 2*v_p((n+1)!) + 2*v_p(n!) + 1

Step 4: Show LHS = RHS.
  LHS - RHS = [v_p(C(2n,n-t)) - v_p(C(2n,n))] + 2*[v_p((n+t+1)!) - v_p((n+1)!)] + 2*[v_p((n-t)!) - v_p(n!)] - 1

  Now: v_p((n+t+1)!) = v_p((n+t)!) + v_p(n+t+1) = v_p((n+t)!) + 0 = v_p((n+t)!)
  [by padicValNat_n_add_pk_succ]

  And: v_p((n+1)!) = v_p(n!) + v_p(n+1) = v_p(n!) + 0 = v_p(n!)
  [by padicValNat_n_succ]

  So: 2*[v_p((n+t+1)!) - v_p((n+1)!)] + 2*[v_p((n-t)!) - v_p(n!)]
    = 2*[v_p((n+t)!) - v_p(n!)] + 2*[v_p((n-t)!) - v_p(n!)]
    = 2*[v_p((n+t)!) + v_p((n-t)!) - 2*v_p(n!)]

  And: v_p((n+t)!) + v_p((n-t)!) - 2*v_p(n!)
     = v_p(C(2n,n)) - v_p(C(2n,n-t))
  [from the identity: v_p(C(m,j)) = v_p(m!) - v_p(j!) - v_p((m-j)!)]

  So: LHS - RHS = [v_p(C(2n,n-t)) - v_p(C(2n,n))] + 2*[v_p(C(2n,n)) - v_p(C(2n,n-t))] - 1
    = v_p(C(2n,n)) - v_p(C(2n,n-t)) - 1
    = 1 - 1 = 0.
  [by kummer_difference]

  Hence LHS = RHS. ✓

IMPLEMENTATION: The key approach is to work with the integer-valued padicValNat sums. Use:
- `padicValNat.mul` for v_p(a*b) = v_p(a) + v_p(b)
- `padicValNat.pow` for v_p(a^k) = k * v_p(a)
- The factorial identity: (n+t+1)! = (n+t+1) * (n+t)!, so v_p((n+t+1)!) = v_p(n+t+1) + v_p((n+t)!)
  Use `Nat.factorial_succ` or `Nat.succ_mul_choose_eq` etc.
- `Nat.choose_mul_factorial_mul_factorial` for C(m,j) * j! * (m-j)! = m!
- `kummer_difference` for v_p(C(2n,n)) = v_p(C(2n,n-t)) + 1
- `padicValNat_n_succ` and `padicValNat_n_add_pk_succ` for the v_p = 0 results

The proof may be cleaner if we avoid trying to unfold everything and instead work directly with the algebraic identity. Try:
1. Show C(2n,n-t)*α² and C(2n,n)*γ² can be related via factorial ratios
2. Show the v_p of the ratio is 1

Or more directly: rewrite both sides as sums of padicValNat of factorials, use kummer_difference and the v_p = 0 lemmas, and do omega/ring.
-/
theorem off_center_alpha_sq_val (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) :
    padicValNat p (Nat.choose (2 * n) (n - p ^ (k-1)) * (α n (n - p ^ (k-1))) ^ 2) =
      e_central p n + 1 := by
  -- By definition of $e_{\text{central}}$, we know that $e_{\text{central}}(p, n) = v_p(\binom{2n}{n} \gamma(n)^2)$.
  have h_e_central : e_central p n = padicValNat p (Nat.choose (2 * n) n) + 2 * padicValNat p ((n + 1).factorial) + 2 * padicValNat p (n.factorial) := by
    rw [ show e_central p n = padicValNat p ( Nat.choose ( 2 * n ) n * ( ( n + 1 ) ! * n ! ) ^ 2 ) from rfl ];
    rw [ padicValNat.mul, padicValNat.pow ] <;> norm_num [ Nat.factorial_ne_zero ] ; ring;
    · rw [ padicValNat.mul ( by positivity ) ( by positivity ) ] ; ring;
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
  -- Now use the given identities to simplify the expression.
  have h_simplify : padicValNat p (Nat.choose (2 * n) (n - p ^ (k - 1)) * (Nat.factorial (n + p ^ (k - 1) + 1) * Nat.factorial (n - p ^ (k - 1))) ^ 2) = padicValNat p (Nat.choose (2 * n) (n - p ^ (k - 1))) + 2 * padicValNat p (Nat.factorial (n + p ^ (k - 1) + 1)) + 2 * padicValNat p (Nat.factorial (n - p ^ (k - 1))) := by
    rw [ padicValNat.mul, padicValNat.pow ] <;> norm_num;
    · rw [ padicValNat.mul ( Nat.factorial_ne_zero _ ) ( Nat.factorial_ne_zero _ ) ] ; ring;
    · exact ⟨ Nat.factorial_ne_zero _, Nat.factorial_ne_zero _ ⟩;
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by omega;
    · exact ⟨ Nat.factorial_ne_zero _, Nat.factorial_ne_zero _ ⟩;
  -- Now use the given identities to simplify the expression further.
  have h_simplify_further : padicValNat p (Nat.factorial (n + p ^ (k - 1) + 1)) = padicValNat p (Nat.factorial (n + p ^ (k - 1))) ∧ padicValNat p (Nat.factorial (n + 1)) = padicValNat p (Nat.factorial n) := by
    have h_simplify_further : padicValNat p (n + p ^ (k - 1) + 1) = 0 ∧ padicValNat p (n + 1) = 0 := by
      exact ⟨ padicValNat_n_add_pk_succ p hp_odd k hk n hn, padicValNat_n_succ p hp_odd k hk n hn ⟩;
    have h_simplify_further : ∀ m : ℕ, padicValNat p (m + 1) = 0 → padicValNat p (Nat.factorial (m + 1)) = padicValNat p (Nat.factorial m) := by
      intro m hm; rw [ Nat.factorial_succ, padicValNat.mul ] <;> simp_all +decide [ Nat.factorial_ne_zero ] ;
    aesop;
  -- Now use the given identities to simplify the expression further, noting that $v_p((n+t)!)$ and $v_p((n-t)!)$ can be expressed in terms of $v_p((2n)!)$.
  have h_factorial_ratio : padicValNat p (Nat.factorial (n + p ^ (k - 1))) + padicValNat p (Nat.factorial (n - p ^ (k - 1))) = padicValNat p (Nat.factorial (2 * n)) - padicValNat p (Nat.choose (2 * n) (n - p ^ (k - 1))) := by
    have h_factorial_ratio : padicValNat p (Nat.factorial (n + p ^ (k - 1))) + padicValNat p (Nat.factorial (n - p ^ (k - 1))) = padicValNat p (Nat.factorial (2 * n)) - padicValNat p (Nat.choose (2 * n) (n - p ^ (k - 1))) := by
      have h_factorial_ratio : Nat.factorial (n + p ^ (k - 1)) * Nat.factorial (n - p ^ (k - 1)) * Nat.choose (2 * n) (n - p ^ (k - 1)) = Nat.factorial (2 * n) := by
        rw [ ← Nat.choose_mul_factorial_mul_factorial ( show n - p ^ ( k - 1 ) ≤ 2 * n from le_trans ( Nat.sub_le _ _ ) ( by linarith ) ) ];
        rw [ show 2 * n - ( n - p ^ ( k - 1 ) ) = n + p ^ ( k - 1 ) by rw [ tsub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( show p ^ ( k - 1 ) ≤ n from by { exact le_of_not_gt fun h => by { have := pk_sub_one_le_n p hp_odd k hk n hn; linarith } } ) ] ] ; ring
      rw [ ← h_factorial_ratio, padicValNat.mul, padicValNat.mul ] <;> norm_num [ Nat.factorial_ne_zero ];
      exact Nat.ne_of_gt <| Nat.choose_pos <| by omega;
    exact h_factorial_ratio;
  -- Now use the given identities to simplify the expression further, noting that $v_p((2n)!)$ can be expressed in terms of $v_p((2n)!)$.
  have h_factorial_ratio_final : padicValNat p (Nat.factorial (2 * n)) = padicValNat p (Nat.choose (2 * n) n) + 2 * padicValNat p (Nat.factorial n) := by
    have h_factorial_ratio_final : padicValNat p (Nat.factorial (2 * n)) = padicValNat p (Nat.choose (2 * n) n * Nat.factorial n * Nat.factorial n) := by
      rw [ Nat.choose_eq_factorial_div_factorial ( by linarith ) ];
      rw [ show 2 * n - n = n by rw [ two_mul, Nat.add_sub_cancel ] ] ; ring;
      rw [ Nat.mul_div_cancel' ( show n ! ^ 2 ∣ ( n * 2 ) ! from by rw [ sq, mul_two ] ; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _ ) ];
    rw [ h_factorial_ratio_final, padicValNat.mul, padicValNat.mul ] <;> norm_num [ Nat.factorial_ne_zero ] ; ring;
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
  -- Now use the given identities to simplify the expression further, noting that $v_p((2n)!)$ can be expressed in terms of $v_p((2n)!)$ and $v_p((n+1)!)$.
  have h_final : padicValNat p ((2 * n).choose n) = padicValNat p ((2 * n).choose (n - p ^ (k - 1))) + 1 := by
    convert kummer_difference p hp_odd k hk n hn using 1;
  convert h_simplify using 1;
  · unfold α; ring;
    rw [ show 1 + n * 2 - ( n - p ^ ( k - 1 ) ) = 1 + n + p ^ ( k - 1 ) by rw [ Nat.sub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( show p ^ ( k - 1 ) ≤ n from by linarith [ pk_sub_one_le_n p hp_odd k hk n hn ] ) ] ] ; ring;
  · omega

/-
PROBLEM
Same for the β² scalar at index n-t-1.
Follows from the alpha theorem because β(n, n-t-1) = α(n, n-t)
and v_p(C(2n, n-t-1)) = v_p(C(2n, n-t)) (since the ratio
C(2n,n-t-1)/C(2n,n-t) = (n-t)/(n+t+1) has v_p = 0).

PROVIDED SOLUTION
The beta theorem follows from the alpha theorem because:

1. β(n, n-t-1) = α(n, n-t) (by beta_eq_alpha with t = p^{k-1}).
   This is because β(n,i) = (2n-i)!*(i+1)! and α(n,j) = (2n+1-j)!*j!.
   At i = n-t-1: 2n-i = n+t+1 and i+1 = n-t. So β = (n+t+1)!*(n-t)!.
   At j = n-t: 2n+1-j = n+t+1 and j = n-t. So α = (n+t+1)!*(n-t)!.

2. v_p(C(2n, n-t-1)) = v_p(C(2n, n-t)).
   C(2n, n-t-1) = C(2n, n-t) * (n-t) / (n+t+1).
   So v_p(C(2n,n-t-1)) = v_p(C(2n,n-t)) + v_p(n-t) - v_p(n+t+1) = v_p(C(2n,n-t)) + 0 - 0.
   Here v_p(n-t) = 0 by padicValNat_n_sub_pk, and v_p(n+t+1) = 0 by padicValNat_n_add_pk_succ.

3. Therefore C(2n,n-t-1)*β(n,n-t-1)² = C(2n,n-t-1)*α(n,n-t)²
   has v_p = v_p(C(2n,n-t-1)) + 2*v_p(α(n,n-t)) = v_p(C(2n,n-t)) + 2*v_p(α(n,n-t))
   = v_p(C(2n,n-t)*α(n,n-t)²) = e_central + 1 (by off_center_alpha_sq_val).

For the formal proof:
- Use `beta_eq_alpha` to rewrite β = α.
- Then show C(2n,n-t-1)*α² = C(2n,n-t)*α² * (n-t)/(n+t+1), or more precisely show the v_p values are equal.

Actually, the simplest approach: rewrite using beta_eq_alpha, then show:
  C(2n, n-t-1) * α(n,n-t)²
  = C(2n, n-t) * α(n,n-t)² * (n-t) / (n+t+1)

And v_p of this = v_p(C(2n,n-t)*α²) + v_p(n-t) - v_p(n+t+1) = (e_central+1) + 0 - 0 = e_central+1.

Or even simpler: show the products are equal as natural numbers:
C(2n, n-t-1) * (n+t+1) = C(2n, n-t) * (n-t)
because C(m, j-1) * (m-j+1) = C(m, j) * j (Pascal's rule variant).
Then v_p(LHS) = v_p(C(2n,n-t-1)) + v_p(n+t+1) = v_p(C(2n,n-t-1)) + 0
And v_p(RHS) = v_p(C(2n,n-t)) + v_p(n-t) = v_p(C(2n,n-t)) + 0
So v_p(C(2n,n-t-1)) = v_p(C(2n,n-t)).

Then C(2n,n-t-1)*β² = C(2n,n-t-1)*α² has v_p = v_p(C(2n,n-t-1)) + 2*v_p(α) = v_p(C(2n,n-t)) + 2*v_p(α) = v_p(C(2n,n-t)*α²) = e_central + 1.

Use `Nat.choose_succ_right_eq` or a similar identity for the Pascal relation.
-/
theorem off_center_beta_sq_val (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) :
    padicValNat p (Nat.choose (2 * n) (n - p ^ (k-1) - 1) * (β n (n - p ^ (k-1) - 1)) ^ 2) =
      e_central p n + 1 := by
  -- Use the fact that $C(2n, n-t-1) * (n+t+1) = C(2n, n-t) * (n-t)$ to relate the $p$-adic valuations.
  have h_ratio : Nat.choose (2 * n) (n - p ^ (k - 1) - 1) * (n + p ^ (k - 1) + 1) = Nat.choose (2 * n) (n - p ^ (k - 1)) * (n - p ^ (k - 1)) := by
    rcases n : n - p ^ (k - 1) with ( _ | _ | n ) <;> simp_all +decide [ Nat.add_one_mul_choose_eq ];
    · rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
      rw [ Nat.sub_eq_zero_iff_le ] at n ; nlinarith [ show p > 2 from lt_of_le_of_ne ( Nat.Prime.two_le Fact.out ) ( Ne.symm hp_odd ), pow_pos ( show 0 < p by exact Nat.Prime.pos Fact.out ) k, pow_pos ( show 0 < p by exact Nat.Prime.pos Fact.out ) 2 ];
    · omega;
    · rw [ Nat.choose_succ_right_eq ];
      exact congrArg _ ( by omega );
  -- Applying the $p$-adic valuation to both sides of the ratio equation.
  have h_val_ratio : padicValNat p (Nat.choose (2 * n) (n - p ^ (k - 1) - 1)) = padicValNat p (Nat.choose (2 * n) (n - p ^ (k - 1))) := by
    -- Applying the p-adic valuation to both sides of the ratio equation, we get:
    have h_val_ratio : padicValNat p (Nat.choose (2 * n) (n - p ^ (k - 1) - 1) * (n + p ^ (k - 1) + 1)) = padicValNat p (Nat.choose (2 * n) (n - p ^ (k - 1)) * (n - p ^ (k - 1))) := by
      rw [h_ratio];
    rw [ padicValNat.mul, padicValNat.mul ] at h_val_ratio;
    · rw [ padicValNat_n_add_pk_succ p hp_odd k hk n hn, padicValNat_n_sub_pk p hp_odd k hk n hn ] at h_val_ratio ; aesop;
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by omega;
    · aesop;
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by omega;
    · positivity;
  convert off_center_alpha_sq_val p hp_odd k hk n hn using 1;
  rw [ padicValNat.mul, padicValNat.mul ] <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ];
  · rw [ beta_eq_alpha ];
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
    nlinarith [ show p > 2 from lt_of_le_of_ne ( Nat.Prime.two_le Fact.out ) ( Ne.symm hp_odd ), pow_pos ( show 0 < p by exact Nat.Prime.pos Fact.out ) k, pow_pos ( show 0 < p by exact Nat.Prime.pos Fact.out ) 2 ];
  · exact Nat.ne_of_gt <| Nat.choose_pos <| by omega;
  · exact mul_ne_zero ( Nat.factorial_ne_zero _ ) ( Nat.factorial_ne_zero _ );
  · exact Nat.ne_of_gt <| Nat.choose_pos <| by omega;
  · exact mul_ne_zero ( Nat.factorial_ne_zero _ ) ( Nat.factorial_ne_zero _ )

-- ============================================================
-- Kummer's theorem (individual values, for p ≥ 5)
-- ============================================================

/-- Kummer's theorem: v_p(C(2n, n)) = k when n+2 = p^k, p ≥ 5.  -/
theorem kummer_central (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2) (hp5 : 5 ≤ p)
    (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) :
    padicValNat p (Nat.choose (2 * n) n) = k := by
  have h_padicValNat_choose : padicValNat p (Nat.choose (2 * n) n) = (Finset.filter (fun i => p ^ i ≤ n % p ^ i + n % p ^ i) (Finset.Ico 1 (k + 1))).card := by
    convert padicValNat_choose ?_ ?_ using 1 <;> norm_num [ two_mul, hn ];
    congr! 1;
    · exact ⟨ Fact.out ⟩;
    · refine' Nat.log_lt_of_lt_pow _ _ <;> norm_num [ ← two_mul, hn ];
      · nlinarith [ Nat.pow_le_pow_right ( show 1 ≤ p by linarith ) hk ];
      · rw [ pow_succ' ] ; nlinarith [ pow_le_pow_right₀ ( by linarith : 1 ≤ p ) hk ] ;
  rw [ h_padicValNat_choose, Finset.card_eq_of_bijective ];
  use fun i hi => i + 1;
  · exact fun a ha => ⟨ a - 1, by cases a <;> aesop ⟩;
  · intro i hi
    have h_mod : n % p ^ (i + 1) = p ^ (i + 1) - 2 := by
      have h_mod : n = p ^ (i + 1) * (p ^ (k - (i + 1)) - 1) + (p ^ (i + 1) - 2) := by
        rw [ mul_tsub, mul_one, ← pow_add, add_tsub_cancel_of_le ( by linarith ) ];
        linarith [ Nat.sub_add_cancel ( show p ^ ( i + 1 ) ≤ p ^ k from pow_le_pow_right₀ ( by linarith ) ( by linarith ) ), Nat.sub_add_cancel ( show 2 ≤ p ^ ( i + 1 ) from le_trans ( by linarith ) ( Nat.le_self_pow ( by linarith ) _ ) ) ];
      norm_num [ h_mod, Nat.add_mod, Nat.mul_mod ];
    simp +zetaDelta at *;
    exact ⟨ hi, by rw [ h_mod ] ; linarith [ Nat.sub_add_cancel ( show 2 ≤ p ^ ( i + 1 ) from le_trans ( by linarith ) ( Nat.le_self_pow ( by linarith ) _ ) ), pow_le_pow_right₀ ( by linarith : 1 ≤ p ) ( show i + 1 ≥ 1 from by linarith ) ] ⟩;
  · aesop

/-- Kummer's theorem: v_p(C(2n, n-t)) = k-1 when t = p^{k-1}, p ≥ 5. -/
theorem kummer_off_center (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2) (hp5 : 5 ≤ p)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : n + 2 = p ^ k) :
    padicValNat p (Nat.choose (2 * n) (n - p ^ (k-1))) = k - 1 := by
  have h_filter : (Finset.filter (fun i => p ^ i ≤ (n - p ^ (k - 1)) % p ^ i + (n + p ^ (k - 1)) % p ^ i) (Finset.Ico 1 (k + 1))).card = k - 1 := by
    have h_mod : ∀ i ∈ Finset.Ico 1 k, (n - p ^ (k - 1)) % p ^ i = p ^ i - 2 ∧ (n + p ^ (k - 1)) % p ^ i = p ^ i - 2 := by
      have h_mod : ∀ i ∈ Finset.Ico 1 k, (n - p ^ (k - 1)) ≡ -2 [ZMOD p ^ i] ∧ (n + p ^ (k - 1)) ≡ -2 [ZMOD p ^ i] := by
        intro i hi
        have h_mod : (n : ℤ) ≡ -2 [ZMOD p ^ i] := by
          exact Int.modEq_iff_dvd.mpr ⟨ -p ^ ( k - i ), by rw [ show ( n : ℤ ) = p ^ k - 2 by linarith ] ; rw [ show ( p ^ k : ℤ ) = p ^ i * p ^ ( k - i ) by rw [ ← pow_add, Nat.add_sub_of_le ( by linarith [ Finset.mem_Ico.mp hi ] ) ] ] ; ring ⟩;
        have h_mod : (p ^ (k - 1) : ℤ) ≡ 0 [ZMOD p ^ i] := by
          exact Int.modEq_zero_iff_dvd.mpr ( pow_dvd_pow _ ( Nat.le_pred_of_lt ( Finset.mem_Ico.mp hi |>.2 ) ) );
        exact ⟨ by simpa using Int.ModEq.sub ‹ ( n : ℤ ) ≡ -2 [ZMOD p ^ i ] › h_mod, by simpa using Int.ModEq.add ‹ ( n : ℤ ) ≡ -2 [ZMOD p ^ i ] › h_mod ⟩;
      intro i hi; specialize h_mod i hi; rcases le_total n ( p ^ ( k - 1 ) ) <;> simp_all +decide [ ← Int.natCast_modEq_iff ] ;
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
        nlinarith [ Nat.mul_le_mul_left p ( Nat.one_le_pow k p ( Nat.Prime.pos Fact.out ) ) ];
      · have h_mod_eq : (n - p ^ (k - 1)) % p ^ i = (p ^ i - 2) % p ^ i ∧ (n + p ^ (k - 1)) % p ^ i = (p ^ i - 2) % p ^ i := by
          zify [ * ];
          rw [ Nat.cast_sub ( show 2 ≤ p ^ i from le_trans ( by linarith ) ( Nat.le_self_pow ( by linarith ) _ ) ) ] ; aesop;
        exact ⟨ h_mod_eq.1.trans ( Nat.mod_eq_of_lt ( Nat.sub_lt ( by positivity ) ( by positivity ) ) ), h_mod_eq.2.trans ( Nat.mod_eq_of_lt ( Nat.sub_lt ( by positivity ) ( by positivity ) ) ) ⟩;
    have h_mod_k : (n - p ^ (k - 1)) % p ^ k = p ^ k - p ^ (k - 1) - 2 ∧ (n + p ^ (k - 1)) % p ^ k = p ^ (k - 1) - 2 := by
      constructor <;> norm_num [ ← hn, Nat.add_mod, Nat.mod_eq_of_lt ];
      · rw [ Nat.mod_eq_of_lt ];
        · omega;
        · exact lt_add_of_le_of_pos ( Nat.sub_le _ _ ) zero_lt_two;
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
        rw [ show n + p * p ^ k = p * ( p * p ^ k ) + ( p * p ^ k - 2 ) by linarith [ Nat.sub_add_cancel ( show 2 ≤ p * p ^ k from by nlinarith [ pow_pos ( zero_lt_two.trans_le ( by linarith : 2 ≤ p ) ) k ] ) ] ] ; norm_num [ Nat.add_mod, Nat.mod_eq_of_lt ( show p * p ^ k - 2 < p * ( p * p ^ k ) from lt_of_le_of_lt ( Nat.sub_le _ _ ) ( by nlinarith [ pow_pos ( zero_lt_two.trans_le ( by linarith : 2 ≤ p ) ) k ] ) ) ];
    have h_filter : ∀ i ∈ Finset.Ico 1 (k + 1), p ^ i ≤ (n - p ^ (k - 1)) % p ^ i + (n + p ^ (k - 1)) % p ^ i ↔ i < k := by
      intro i hi; cases lt_or_eq_of_le ( Finset.mem_Ico.mp hi |>.2 |> Nat.le_of_lt_succ ) <;> simp_all +decide ;
      · linarith [ Nat.sub_add_cancel ( show 2 ≤ p ^ i from le_trans ( by linarith ) ( Nat.pow_le_pow_right ( by linarith ) hi.1 ) ), Nat.pow_le_pow_right ( by linarith : 1 ≤ p ) hi.1 ];
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
        zify;
        rw [ Nat.sub_sub, Nat.cast_sub, Nat.cast_sub ] <;> push_cast <;> nlinarith [ pow_pos ( show 0 < p by linarith ) k, pow_pos ( show 0 < p by linarith ) 2 ];
    rw [ Finset.filter_congr fun i hi => h_filter i hi ] ; aesop;
  rw [ ← h_filter, padicValNat_choose ];
  congr! 2;
  · ext; simp +decide [ two_mul, add_assoc ] ;
    rw [ h_filter ];
    rw [ show n + n - ( n - p ^ ( k - 1 ) ) = n + p ^ ( k - 1 ) by rw [ tsub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( show p ^ ( k - 1 ) ≤ n from by exact Nat.le_of_lt_succ <| by { rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ] ; nlinarith } ) ] ];
  · exact le_trans ( Nat.sub_le _ _ ) ( by linarith );
  · refine' Nat.log_lt_of_lt_pow _ _ <;> norm_num [ hn ];
    · nlinarith [ Nat.pow_le_pow_right ( show 1 ≤ p by linarith ) hk ];
    · rw [ pow_succ' ] ; nlinarith [ pow_le_pow_right₀ ( by linarith : 1 ≤ p ) hk ]

end QuarticInvariant
