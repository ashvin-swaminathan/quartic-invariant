import Mathlib
import Modular.Defs

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant


-- ============================================================
-- Helper: the b_k formula used in the hypothesis
-- ============================================================
def b_formula (n k : ℕ) : ℤ :=
  2 * (-1 : ℤ) ^ k * ((2 * n).factorial : ℤ) ^ 2 *
    ((2 * n : ℤ) + 1 - k) * ((2 * n : ℤ) + 1 - 2 * k) /
    (Nat.choose (2 * n) k : ℤ)

/-
PROBLEM
============================================================
Key algebraic identity (over ℤ):
C(2n,j) * α(n,j)² - C(2n,j-1) * β(n,j-1)²
= (2n)! * j! * (2n+1-j)! * (2n+1-2j)
for 1 ≤ j ≤ 2n
============================================================

First, simplify C(N,j)*α(n,j)²

PROVIDED SOLUTION
Expand the definitions:
- α(n,j) = (2n+1-j)! * j!
- C(2n, j) = (2n)! / ((2n-j)! * j!)

So C(2n,j) * α(n,j)^2 = (2n)! / ((2n-j)! * j!) * ((2n+1-j)!)^2 * (j!)^2
= (2n)! * (2n+1-j)!^2 * j! / (2n-j)!
= (2n)! * ((2n+1-j) * (2n-j)!)^2 * j! / (2n-j)!
= (2n)! * (2n+1-j)^2 * (2n-j)! * j!

So the identity holds. The proof should unfold α and use Nat.choose_eq_factorial_div_factorial to express C(2n,j) = (2n)!/((2n-j)!*j!), then cancel common factors.

Key steps:
1. Cast everything to ℤ
2. Use Nat.choose_mul_factorial_mul_factorial: C(n,k) * k! * (n-k)! = n!
3. Use (2n+1-j)! = (2n+1-j) * (2n-j)! to get (2n+1-j)!^2 / (2n-j)! = (2n+1-j)^2 * (2n-j)!
4. Algebraic simplification
-/
lemma choose_mul_alpha_sq (n j : ℕ) (hj : j ≤ 2 * n) :
    (Nat.choose (2*n) j : ℤ) * ((α n j : ℤ))^2 =
      (2*n).factorial * ((2*n+1-j : ℕ) : ℤ)^2 * ((2*n - j).factorial : ℤ) * (j.factorial : ℤ) := by
  -- By definition of α, we have α n j = (2 * n + 1 - j)! * j!.
  have h_alpha : α n j = (2 * n + 1 - j)! * j ! := by
    rfl;
  push_cast [ h_alpha ];
  rw_mod_cast [ ← Nat.choose_mul_factorial_mul_factorial hj ] ; ring;
  rw [ show 1 + n * 2 - j = ( n * 2 - j ) + 1 by omega, Nat.factorial_succ ] ; ring

/-
PROBLEM
Next, simplify C(N,j-1)*β(n,j-1)²

PROVIDED SOLUTION
Expand the definitions:
- β(n,j-1) = (2n-(j-1))! * j! = (2n-j+1)! * j!  [since (j-1)+1 = j]
- C(2n, j-1) = (2n)! / ((2n-j+1)! * (j-1)!)

So C(2n,j-1) * β(n,j-1)^2 = (2n)! / ((2n-j+1)! * (j-1)!) * ((2n-j+1)!)^2 * (j!)^2
= (2n)! * (2n-j+1)! * j!^2 / (j-1)!
= (2n)! * (2n-j+1)! * j * j!    [since j! / (j-1)! = j... rather j!^2/(j-1)! = j * j!]
= (2n)! * j * (2n+1-j)! * j!

where we used (2n-j+1)! = (2n+1-j)!.

Key steps:
1. Use Nat.choose_mul_factorial_mul_factorial with (n, k) = (2n, j-1)
2. Use β n (j-1) = (2n - (j-1))! * ((j-1)+1)! = (2n-j+1)! * j!
3. Since j ≥ 1, we have j-1 ≤ 2n-1 ≤ 2n, so (j-1) ≤ 2n
4. Algebraic simplification: j!^2 * (2n-j+1)! / (j-1)! = j * j! * (2n+1-j)!
-/
lemma choose_mul_beta_sq (n j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2 * n) :
    (Nat.choose (2*n) (j-1) : ℤ) * ((β n (j-1) : ℤ))^2 =
      (2*n).factorial * (j : ℤ) * ((2*n+1-j : ℕ).factorial : ℤ) * (j.factorial : ℤ) := by
  rcases j <;> simp_all +decide [ Nat.choose_succ_succ, pow_two, mul_assoc, Nat.factorial_ne_zero, Nat.factorial_succ ];
  rw [ show β n _ = Nat.factorial ( 2 * n - _ ) * Nat.factorial ( _ + 1 ) from rfl ] ; norm_cast ; ring!;
  have := Nat.choose_mul_factorial_mul_factorial ( by linarith : ‹_› ≤ n * 2 ) ; simp_all +decide [ Nat.factorial_succ, sq, mul_assoc, mul_comm, mul_left_comm ] ; ring;
  rw [ ← this ] ; push_cast [ Nat.add_comm 1, Nat.factorial_succ ] ; ring;

/-
PROBLEM
The main algebraic identity

PROVIDED SOLUTION
The identity follows from the two helper lemmas choose_mul_alpha_sq and choose_mul_beta_sq.

From choose_mul_alpha_sq: C(2n,j) * α_j^2 = (2n)! * (2n+1-j)^2 * (2n-j)! * j!
From choose_mul_beta_sq: C(2n,j-1) * β_{j-1}^2 = (2n)! * j * (2n+1-j)! * j!

Difference = (2n)! * j! * [(2n+1-j)^2 * (2n-j)! - j * (2n+1-j)!]
= (2n)! * j! * [(2n+1-j)^2 * (2n-j)! - j * (2n+1-j) * (2n-j)!]
= (2n)! * j! * (2n-j)! * (2n+1-j) * [(2n+1-j) - j]
= (2n)! * j! * (2n-j)! * (2n+1-j) * (2n+1-2j)

And (2n-j)! * (2n+1-j) = (2n+1-j)!.

So difference = (2n)! * j! * (2n+1-j)! * (2n+1-2j).

Use choose_mul_alpha_sq and choose_mul_beta_sq, substitute, then use the fact that (2n+1-j)! = (2n+1-j) * (2n-j)! (Nat.factorial_succ) to simplify. The key factoring step is:
(2n+1-j)^2 * (2n-j)! - j * (2n+1-j) * (2n-j)! = (2n-j)! * (2n+1-j) * ((2n+1-j) - j)
= (2n-j)! * (2n+1-j) * (2n+1-2j)
and then (2n-j)! * (2n+1-j) = (2n+1-j)!.
-/
lemma key_identity (n j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2 * n) :
    (Nat.choose (2*n) j : ℤ) * ((α n j : ℤ))^2 -
    (Nat.choose (2*n) (j-1) : ℤ) * ((β n (j-1) : ℤ))^2 =
      ((2*n).factorial : ℤ) * (j.factorial : ℤ) * ((2*n+1-j : ℕ).factorial : ℤ) *
        ((2*n : ℤ) + 1 - 2 * j) := by
  -- Expand the definitions of α and β in the difference.
  have h_expand : ((Nat.choose (2 * n) j : ℤ) * ((α n j : ℤ)) ^ 2) =
    ((2 * n).factorial : ℤ) * ((2 * n + 1 - j : ℕ) : ℤ) ^ 2 * ((2 * n - j).factorial : ℤ) * (j.factorial : ℤ) ∧
    ((Nat.choose (2 * n) (j - 1) : ℤ) * ((β n (j - 1) : ℤ)) ^ 2) =
    ((2 * n).factorial : ℤ) * (j : ℤ) * ((2 * n + 1 - j : ℕ).factorial : ℤ) * (j.factorial : ℤ) := by
      apply And.intro;
      · exact?;
      · exact?;
  rw [ h_expand.1, h_expand.2 ] ; ring;
  rw [ show 1 + n * 2 - j = ( n * 2 - j ) + 1 by omega ] ; norm_num [ Nat.factorial_succ ] ; ring;
  rw [ Nat.cast_sub ( by linarith ) ] ; push_cast ; ring;

/-
PROBLEM
============================================================
The coefficient at position 0 (boundary term) is 2*((2n+1)!)²
============================================================

(n+1) divides C(2n, n), i.e., Catalan numbers are integers

PROVIDED SOLUTION
This is equivalent to saying the Catalan number C_n = C(2n,n)/(n+1) is an integer.

One clean proof: C(2n+1, n+1) = (2n+1)! / ((n+1)! * n!) = C(2n, n) * (2n+1) / (n+1). Since C(2n+1, n+1) is a natural number and gcd(n+1, 2n+1) = 1 (because 2(n+1) - (2n+1) = 1), we get (n+1) | C(2n, n).

Alternatively, use Nat.centralBinom_div_succ_eq_catalan or similar Mathlib lemma about Catalan numbers if available. Or use Nat.choose_prime_pow_mul_pow.
-/
lemma succ_dvd_centralBinom (n : ℕ) : (n + 1) ∣ Nat.choose (2 * n) n := by
  have h := @Nat.succ_mul_choose_eq ( 2 * n ) n;
  rw [ Nat.choose_succ_succ ] at h;
  exact ⟨ Nat.choose ( 2 * n ) n - Nat.choose ( 2 * n ) ( n + 1 ), by rw [ Nat.mul_sub_left_distrib, eq_tsub_iff_add_eq_of_le ] <;> nlinarith ⟩

/-
PROBLEM
The boundary coefficient 2*((2n+1)!)² has v_p ≥ e

PROVIDED SOLUTION
We need to show p^e | 2*((2n+1)!)^2, given that e ≤ v_p(|b_k|) for all k ∈ [1, 2n] and n ≥ 1.

The key idea: compare to b_n (which is in [1, 2n] since n ≥ 1):
b_n = 2*(-1)^n * (2n)!^2 * (n+1) * 1 / C(2n,n)
|b_n| = 2*(2n)!^2*(n+1)/C(2n,n) = 2*(2n)!*(n!)^2*(n+1)

And 2*((2n+1)!)^2 = 2*((2n+1)*(2n)!)^2 = 2*(2n+1)^2*(2n)!^2

We want to show v_p(2*(2n+1)^2*(2n)!^2) ≥ v_p(2*(2n)!*(n!)^2*(n+1)) = v_p(|b_n|) ≥ e.

Equivalently: (2*(2n)!*(n!)^2*(n+1)) | (2*(2n+1)^2*(2n)!^2)

Ratio = (2n+1)^2 * (2n)! / ((n!)^2 * (n+1)) = (2n+1)^2 * C(2n,n) / (n+1)

Since (n+1) | C(2n,n) (by succ_dvd_centralBinom), C(2n,n)/(n+1) is an integer (the Catalan number).
So the ratio = (2n+1)^2 * (Catalan number) is an integer.

Therefore |b_n| | 2*((2n+1)!)^2, hence v_p(2*((2n+1)!)^2) ≥ v_p(|b_n|) ≥ e, so p^e | 2*((2n+1)!)^2.

The proof approach:
1. Use he with k = n (showing n ∈ Finset.Icc 1 (2*n) since n ≥ 1)
2. Show that |b_n| divides 2*((2n+1)!)^2
3. Use dvd_trans

Step 2 requires computing:
b_formula n n = 2*(-1)^n*(2n)!^2*(n+1)*1/C(2n,n)

Actually, let me try a more direct approach:
Show that padicValNat p (Int.natAbs (2 * ((2*n+1)! : ℤ)^2)) ≥ e.

We know e ≤ padicValNat p |b_n|. And we need padicValNat p |2*((2n+1)!)^2| ≥ padicValNat p |b_n|.

This follows from |b_n| | 2*((2n+1)!)^2 as integers, which follows from the computation above.

Alternatively, use multiplicity/padicValNat arithmetic:
v_p(2*((2n+1)!)^2) = v_p(2) + 2*v_p((2n+1)!) = v_p(2) + 2*v_p(2n+1) + 2*v_p((2n)!)
v_p(|b_n|) = v_p(2) + v_p((2n)!) + 2*v_p(n!) + v_p(n+1) [since |b_n| = 2*(2n)!*(n!)^2*(n+1)]

Difference = 2*v_p(2n+1) + v_p((2n)!) - 2*v_p(n!) - v_p(n+1)
= 2*v_p(2n+1) + v_p(C(2n,n)) - v_p(n+1)

Since (n+1) | C(2n,n) (succ_dvd_centralBinom), v_p(C(2n,n)) ≥ v_p(n+1).
So difference ≥ 2*v_p(2n+1) ≥ 0.

So v_p(2*((2n+1)!)^2) ≥ v_p(|b_n|) ≥ e.

The formal proof should:
1. Specialize he to k = n
2. Show n ∈ Finset.Icc 1 (2*n) from hn
3. Show |b_n| divides 2*((2n+1)!)^2 (or use padicValNat comparison)
4. Conclude by transitivity of ≤ and the connection between padicValNat and dvd
-/
lemma coeff0_dvd (p n e : ℕ) [hp : Fact p.Prime] (hn : 0 < n)
    (he : ∀ k ∈ Finset.Icc 1 (2 * n),
      e ≤ padicValNat p (Int.natAbs (b_formula n k))) :
    ((p ^ e : ℕ) : ℤ) ∣ (2 * ((2 * n + 1).factorial : ℤ) ^ 2) := by
  -- From he, we know that e ≤ v_p(|b_n|).
  have h_le : e ≤ padicValNat p (b_formula n n).natAbs := by
    apply he n; simp [Finset.mem_Icc]; omega
  -- We need to show that |b_n| divides 2*((2n+1)!)^2.
  have h_div : Int.natAbs (b_formula n n) ∣ 2 * ((2 * n + 1)! : ℤ).natAbs ^ 2 := by
    -- Using the definition of b_formula, we can rewrite |b_n| as 2*(2n)!*(n!)^2*(n+1).
    have h_abs_b_n : Int.natAbs (b_formula n n) = 2 * ((2 * n)! : ℤ).natAbs * ((n ! : ℤ).natAbs) ^ 2 * (n + 1) := by
      unfold b_formula;
      rw [ show ( Nat.choose ( 2 * n ) n : ℤ ) = ( 2 * n ) ! / ( n ! * n ! ) from ?_ ];
      · rw [ show ( 2 * ( -1 : ℤ ) ^ n * ( 2 * n ) ! ^ 2 * ( 2 * n + 1 - n ) * ( 2 * n + 1 - 2 * n ) : ℤ ) = ( 2 * n ) ! / ( n ! * n ! ) * ( 2 * ( -1 : ℤ ) ^ n * ( 2 * n ) ! * ( n ! * n ! ) * ( n + 1 ) ) by
              rw [ show ( 2 * n ) ! = ( 2 * n ) ! / ( n ! * n ! ) * ( n ! * n ! ) by rw [ Nat.div_mul_cancel ( Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| by ring_nf; norm_num ) ] ] ; ring;
              norm_num [ sq, mul_assoc, Nat.factorial_ne_zero ] ; ring;
              rw [ Int.mul_ediv_cancel_left _ ( by positivity ) ] ; ring ];
        rw [ Int.mul_ediv_cancel_left ];
        · norm_num [ Int.natAbs_mul, Int.natAbs_pow ] ; ring;
          norm_cast ; ring;
        · exact ne_of_gt ( mod_cast Nat.div_pos ( Nat.le_of_dvd ( by positivity ) ( Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| by ring_nf; norm_num ) ) ( by positivity ) );
      · rw [ Nat.choose_eq_factorial_div_factorial ] <;> norm_num [ two_mul ];
    norm_num [ Nat.factorial_succ, h_abs_b_n ];
    -- We can divide both sides by $2 * (2 * n)!$ since it is non-zero.
    suffices h_div : (n ! ^ 2 * (n + 1)) ∣ ((2 * n + 1) * (2 * n)!) ^ 2 / ((2 * n)!) by
      convert mul_dvd_mul_left ( 2 * ( 2 * n ) ! ) h_div using 1 ; ring;
      norm_cast ; norm_num [ Nat.mul_div_assoc, sq, mul_assoc ] ; ring;
      norm_num [ Nat.factorial_pos ];
    norm_num [ mul_pow, Nat.mul_div_assoc ];
    norm_num [ sq, Nat.factorial_pos ];
    -- We can divide both sides by $n! * n!$ since it is non-zero.
    suffices h_div : (n + 1) ∣ (2 * n + 1) * (2 * n + 1) * Nat.choose (2 * n) n by
      convert Nat.mul_dvd_mul_left ( n ! * n ! ) h_div using 1 ; ring;
      rw [ ← Nat.choose_mul_factorial_mul_factorial ( show n ≤ n * 2 by linarith ) ] ; ring;
      rw [ show n * 2 - n = n by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; ring;
    have h_div : (n + 1) ∣ Nat.choose (2 * n) n := by
      have h := Nat.succ_mul_choose_eq ( 2 * n ) n;
      rw [ Nat.choose_succ_succ ] at h;
      exact ⟨ Nat.choose ( 2 * n ) n - Nat.choose ( 2 * n ) ( n + 1 ), by rw [ Nat.mul_sub_left_distrib, eq_tsub_iff_add_eq_of_le ] <;> nlinarith ⟩;
    exact dvd_mul_of_dvd_right h_div _;
  norm_cast at *;
  refine' dvd_trans ( pow_dvd_pow _ h_le ) _;
  convert Nat.ordProj_dvd ( Int.natAbs ( b_formula n n ) ) p |> fun x => x.trans h_div using 1 ; simp +decide [ Nat.factorization ] ; ring;
  exact fun h => False.elim <| h hp.1

-- ============================================================
-- Main theorem: coeff_B_n_dvd
-- ============================================================

/-
Every scalar coefficient in B_n has p-adic valuation ≥ e, where e is a
given lower bound on v_p(b_k) for all k.

Proof idea: B_n can be rearranged as
  B_n = 2·((2n+1)!)² · X₀·X_{2n+1} + Σ_{j=1}^{n} b_j · Xⱼ·X_{2n+1-j}
where each b_j is the formula from the hypothesis. This follows from the
key algebraic identity C(2n,j)·α_j² - C(2n,j-1)·β_{j-1}² = (2n)!·j!·(2n+1-j)!·(2n+1-2j),
combined with the pairing of terms at positions j and 2n+1-j.
Since each b_j has v_p ≥ e (by hypothesis) and 2·((2n+1)!)² also has v_p ≥ e
(shown separately), every coefficient of B_n is divisible by p^e.
-/

/-- The rearranged form of B_n: a sum of monomials with explicit coefficients. -/
def B_n_alt (n : ℕ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.C (2 * ((2 * n + 1).factorial : ℤ) ^ 2) *
    MvPolynomial.X 0 * MvPolynomial.X (2 * n + 1) +
  ∑ j ∈ Finset.Icc 1 n,
    MvPolynomial.C (b_formula n j) * MvPolynomial.X j * MvPolynomial.X (2 * n + 1 - j)

/-
PROBLEM
B_n equals its rearranged form.

PROVIDED SOLUTION
Two MvPolynomials are equal iff they evaluate to the same value at every point. Use MvPolynomial.funext: if ∀ x, MvPolynomial.eval x f = MvPolynomial.eval x g, then f = g.

MvPolynomial.eval x (B_n n) = Σ_{i ∈ range(2n+1)} (-1)^i * C(2n,i) * [α_i^2 * x(i) * x(2n+1-i) + β_i^2 * x(i+1) * x(2n-i)]

MvPolynomial.eval x (B_n_alt n) = 2*((2n+1)!)^2 * x(0) * x(2n+1) + Σ_{j ∈ Icc 1 n} b_j * x(j) * x(2n+1-j)

These are equal for all x : ℕ → ℤ. To show this, we manipulate the sum defining eval(B_n):

1. Split the sum into α² and β² parts:
   = Σ_i s_i * x(i) * x(2n+1-i) + Σ_i t_i * x(i+1) * x(2n-i)
   where s_i = (-1)^i*C(2n,i)*α_i^2 and t_i = (-1)^i*C(2n,i)*β_i^2

2. In the β² sum, note x(i+1)*x(2n-i) = x(i+1)*x(2n+1-(i+1)), so reindex with j=i+1:
   β² sum = Σ_{j=1}^{2n+1} t_{j-1} * x(j) * x(2n+1-j)

3. Pull out the boundary terms (j=0 from α², j=2n+1 from β²) and j=0 is x(0)*x(2n+1):
   = s_0*x(0)*x(2n+1) + t_{2n}*x(2n+1)*x(0) + Σ_{j=1}^{2n} (s_j + t_{j-1})*x(j)*x(2n+1-j)

4. s_0 = α_0^2 = ((2n+1)!)^2 and t_{2n} = (-1)^{2n}*β_{2n}^2 = ((2n+1)!)^2 (since 2n is even)
   So s_0 + t_{2n} = 2*((2n+1)!)^2  (using x(0)*x(2n+1) = x(2n+1)*x(0))

5. For j ∈ [1, 2n]: s_j + t_{j-1} = (-1)^j * [C(2n,j)*α_j^2 - C(2n,j-1)*β_{j-1}^2]
   = (-1)^j * (2n)!*j!*(2n+1-j)!*(2n+1-2j) by key_identity

6. Terms at j and 2n+1-j have the same factor x(j)*x(2n+1-j), and their scalars sum to b_j.

For the evaluation approach, these are just arithmetic identities on integers (no MvPolynomial), so they should be easier to prove. Use ring, omega, and the key_identity lemma.

The key identity that makes this work at the integer level:
Σ_{i=0}^{2n} (-1)^i*C(2n,i)*[α_i^2*x_i*x_{2n+1-i} + β_i^2*x_{i+1}*x_{2n-i}]
= 2*((2n+1)!)^2 * x_0*x_{2n+1} + Σ_{j=1}^{n} b_j * x_j*x_{2n+1-j}

Try: apply MvPolynomial.funext; intro x; simp [B_n, B_n_alt, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_add, b_formula]; ring_nf; ...then use sum manipulation.
-/
lemma B_n_eq_alt (n : ℕ) (hn : 0 < n) : B_n n = B_n_alt n := by
  refine' MvPolynomial.funext _;
  intro x
  simp [B_n, B_n_alt, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_add, b_formula];
  -- Split the sum into two parts: one for α_i^2 and one for β_i^2.
  have h_split : ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((Nat.choose (2 * n) i) : ℤ) * ((α n i) : ℤ) ^ 2 * x i * x (2 * n + 1 - i) +
                 ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((Nat.choose (2 * n) i) : ℤ) * ((β n i) : ℤ) ^ 2 * x (i + 1) * x (2 * n - i) =
                 2 * ((2 * n + 1)! : ℤ) ^ 2 * x 0 * x (2 * n + 1) +
                 ∑ i ∈ Finset.Icc 1 n, 2 * (-1 : ℤ) ^ i * ((2 * n)! : ℤ) ^ 2 * (2 * n + 1 - i) * (2 * n + 1 - 2 * i) / ((Nat.choose (2 * n) i) : ℤ) * x i * x (2 * n + 1 - i) := by
                   -- Apply the key identity to each term in the sum.
                   have h_sum_identity : ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((Nat.choose (2 * n) i) : ℤ) * ((α n i) : ℤ) ^ 2 * x i * x (2 * n + 1 - i) +
                                        ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((Nat.choose (2 * n) i) : ℤ) * ((β n i) : ℤ) ^ 2 * x (i + 1) * x (2 * n - i) =
                                        2 * ((2 * n + 1).factorial : ℤ) ^ 2 * x 0 * x (2 * n + 1) +
                                        ∑ i ∈ Finset.Icc 1 (2 * n), (-1 : ℤ) ^ i * ((2 * n).factorial : ℤ) * (i.factorial : ℤ) * ((2 * n + 1 - i).factorial : ℤ) * (2 * n + 1 - 2 * i) * x i * x (2 * n + 1 - i) := by
                                          have h_split : ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) ^ 2 * x i * x (2 * n + 1 - i) +
                                                                            ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * (β n i : ℤ) ^ 2 * x (i + 1) * x (2 * n - i) =
                                                                            2 * ((2 * n + 1).factorial : ℤ) ^ 2 * x 0 * x (2 * n + 1) +
                                                                            ∑ i ∈ Finset.Icc 1 (2 * n), (-1 : ℤ) ^ i * ((Nat.choose (2 * n) i : ℤ) * (α n i : ℤ) ^ 2 - (Nat.choose (2 * n) (i - 1) : ℤ) * (β n (i - 1) : ℤ) ^ 2) * x i * x (2 * n + 1 - i) := by
                                                                              erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ] ; ring;
                                                                              norm_num [ Finset.sum_add_distrib, add_comm 1, add_comm 2, α, β ] ; ring!;
                                                                              have := Finset.sum_range_sub ( fun i ↦ ( Nat.choose ( n * 2 ) i : ℤ ) * ( n * 2 - i ) ! ^ 2 * ( 1 + i ) ! ^ 2 * x ( 1 + i ) * x ( 1 + n * 2 - ( 1 + i ) ) * ( -1 ) ^ i ) ( n * 2 ) ; simp_all +decide [ add_comm 1, add_comm 2, add_assoc, Nat.choose_succ_succ, pow_succ, mul_assoc, mul_comm, mul_left_comm, Finset.sum_range_succ' ] ; ring; (
                                                                              grind);
                                          convert h_split using 3;
                                          rename_i i hi; rw [ key_identity n i ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2 ) ] ; ring;
                   -- By pairing terms $i$ and $2n+1-i$, we can simplify the sum.
                   have h_pair : ∑ i ∈ Finset.Icc 1 (2 * n), (-1 : ℤ) ^ i * ((2 * n).factorial : ℤ) * (i.factorial : ℤ) * ((2 * n + 1 - i).factorial : ℤ) * (2 * n + 1 - 2 * i) * x i * x (2 * n + 1 - i) =
                                  ∑ i ∈ Finset.Icc 1 n, ((-1 : ℤ) ^ i * ((2 * n).factorial : ℤ) * (i.factorial : ℤ) * ((2 * n + 1 - i).factorial : ℤ) * (2 * n + 1 - 2 * i) * x i * x (2 * n + 1 - i) +
                                                         (-1 : ℤ) ^ (2 * n + 1 - i) * ((2 * n).factorial : ℤ) * ((2 * n + 1 - i).factorial : ℤ) * (i.factorial : ℤ) * (2 * n + 1 - 2 * (2 * n + 1 - i)) * x (2 * n + 1 - i) * x i) := by
                                                           have h_pair : Finset.Icc 1 (2 * n) = Finset.image (fun i => i) (Finset.Icc 1 n) ∪ Finset.image (fun i => 2 * n + 1 - i) (Finset.Icc 1 n) := by
                                                             ext i
                                                             simp [Finset.mem_Icc, Finset.mem_image];
                                                             exact ⟨ fun hi => if hi' : i ≤ n then Or.inl ⟨ hi.1, hi' ⟩ else Or.inr ⟨ 2 * n + 1 - i, ⟨ by omega, by omega ⟩, by omega ⟩, fun hi => by rcases hi with ( ⟨ hi₁, hi₂ ⟩ | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> omega ⟩;
                                                           rw [ h_pair, Finset.sum_union ];
                                                           · norm_num [ Finset.sum_add_distrib ];
                                                             rw [ Finset.sum_image ] <;> norm_num;
                                                             · exact Finset.sum_congr rfl fun i hi => by rw [ Nat.sub_sub_self ( by linarith [ Finset.mem_Icc.mp hi ] ) ] ; rw [ Nat.cast_sub ( by linarith [ Finset.mem_Icc.mp hi ] ) ] ; push_cast ; ring;
                                                             · exact fun a ha b hb hab => by rw [ tsub_right_inj ] at hab <;> linarith [ ha.1, ha.2, hb.1, hb.2 ] ;
                                                           · norm_num [ Finset.disjoint_right ];
                                                             intros; omega;
                   rw [ h_sum_identity, h_pair ];
                   refine' congrArg _ ( Finset.sum_congr rfl fun i hi => _ );
                   rw [ show ( Nat.choose ( 2 * n ) i : ℤ ) = ( 2 * n ) ! / ( i ! * ( 2 * n - i ) ! ) from mod_cast Nat.choose_eq_factorial_div_factorial ( by linarith [ Finset.mem_Icc.mp hi ] ) ] ; rw [ Int.ediv_eq_of_eq_mul_left ];
                   rotate_right;
                   exact 2 * ( -1 ) ^ i * ( 2 * n ) ! * ( 2 * n + 1 - i ) * ( 2 * n + 1 - 2 * i ) * ( i ! * ( 2 * n - i ) ! );
                   · rw [ show ( 2 * n + 1 - i ) = ( 2 * n - i ) + 1 by rw [ tsub_add_eq_add_tsub ( by linarith [ Finset.mem_Icc.mp hi ] ) ] ] ; norm_num [ Nat.factorial_succ, pow_add ] ; ring;
                     rw [ show n * 2 - i = n * 2 - i from rfl, show ( -1 : ℤ ) ^ ( n * 2 - i ) = ( -1 : ℤ ) ^ ( n * 2 ) / ( -1 : ℤ ) ^ i from ?_ ] ; norm_num [ pow_mul', Nat.cast_sub ( show i ≤ n * 2 from by linarith [ Finset.mem_Icc.mp hi ] ) ] ; ring;
                     · by_cases hi' : Even i <;> simp_all +decide [ Nat.even_add_one ] <;> ring;
                     · rw [ eq_comm, Int.ediv_eq_of_eq_mul_left ] <;> norm_num [ ← pow_add, Nat.sub_add_cancel ( show i ≤ n * 2 from by linarith [ Finset.mem_Icc.mp hi ] ) ];
                   · exact ne_of_gt ( mod_cast Nat.div_pos ( Nat.le_of_dvd ( Nat.factorial_pos _ ) ( Nat.factorial_mul_factorial_dvd_factorial ( by linarith [ Finset.mem_Icc.mp hi ] ) ) ) ( Nat.mul_pos ( Nat.factorial_pos _ ) ( Nat.factorial_pos _ ) ) );
                   · rw [ ← Int.mul_ediv_assoc ];
                     · exact Eq.symm ( Int.ediv_eq_of_eq_mul_left ( by positivity ) ( by ring ) );
                     · exact_mod_cast Nat.factorial_mul_factorial_dvd_factorial ( by linarith [ Finset.mem_Icc.mp hi ] );
  simpa only [ mul_add, mul_assoc, Finset.sum_add_distrib ] using h_split

/-
PROBLEM
Every coefficient of B_n_alt is divisible by p^e.

PROVIDED SOLUTION
B_n_alt n is a sum of terms, each of the form C(scalar) * X(a) * X(b).

The coefficient of B_n_alt at monomial m is:
- If m = Finsupp.single 0 1 + Finsupp.single (2n+1) 1: the scalar 2*((2n+1)!)^2 (from the first term)
- If m = Finsupp.single j 1 + Finsupp.single (2n+1-j) 1 for some j ∈ [1, n]: the scalar b_formula n j (from the sum)
- Otherwise: 0

All of these are divisible by p^e:
1. 2*((2n+1)!)^2 is divisible by p^e by coeff0_dvd
2. b_formula n j for j ∈ [1, n] ⊂ [1, 2n] has |b_formula n j| with padicValNat ≥ e by hypothesis he
3. 0 is divisible by anything

Proof approach:
1. intro m
2. Unfold B_n_alt
3. Use MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, and the coeff of X*X
4. Show the resulting expression is divisible by p^e

For step 4, each summand in the coeff_sum is either 0 (if m doesn't match the monomial) or the scalar (if it does). In either case it's divisible by p^e.

Key approach: use dvd_add for the two parts, then dvd_sum for the sum part. For each term C(s)*X(a)*X(b), the coeff at m is s if m matches, 0 otherwise. Show s is divisible in each case.

For the boundary term: use coeff0_dvd
For j ∈ [1, n]: need p^e | b_formula n j. From he, e ≤ padicValNat p |b_formula n j|, which implies p^e | |b_formula n j| (Nat), which implies (p^e : ℤ) | b_formula n j (Int). Use Int.coe_nat_dvd and padicValNat properties.
-/
lemma coeff_B_n_alt_dvd (p n e : ℕ) [Fact p.Prime] (hn : 0 < n)
    (he : ∀ k ∈ Finset.Icc 1 (2 * n),
      e ≤ padicValNat p (Int.natAbs (b_formula n k))) :
    ∀ m, ((p ^ e : ℕ) : ℤ) ∣ (B_n_alt n).coeff m := by
  intro m
  unfold B_n_alt
  simp [MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X] at *;
  -- Apply the fact that each coefficient in the sum is divisible by p^e.
  have h_coeff_dvd : ∀ j ∈ Finset.Icc 1 n, (p ^ e : ℤ) ∣ MvPolynomial.coeff m (MvPolynomial.C (b_formula n j) * MvPolynomial.X j * MvPolynomial.X (2 * n + 1 - j)) := by
    intro j hj
    have h_div : (p ^ e : ℤ) ∣ (b_formula n j) := by
      have := he j ( Finset.mem_Icc.mp hj |>.1 ) ( by linarith [ Finset.mem_Icc.mp hj |>.2 ] ) ; rw [ ← Int.natAbs_dvd_natAbs ] ; simp_all +decide [ padicValNat_dvd_iff ] ;
    generalize_proofs at *; (
    rw [ MvPolynomial.coeff_mul ] ; (
    refine' Finset.dvd_sum fun x hx => _ ; erw [ MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X' ] ; aesop;))
  generalize_proofs at *; (
  -- The coefficient of B_n_alt n at m is either 0 or the boundary term, both of which are divisible by p^e.
  have h_coeff_boundary : (p ^ e : ℤ) ∣ MvPolynomial.coeff m (MvPolynomial.C (2 * ((2 * n + 1).factorial : ℤ) ^ 2) * MvPolynomial.X 0 * MvPolynomial.X (2 * n + 1)) := by
    have h_coeff_boundary : (p ^ e : ℤ) ∣ 2 * ((2 * n + 1).factorial : ℤ) ^ 2 := by
      exact_mod_cast coeff0_dvd p n e hn fun k hk => he k ( Finset.mem_Icc.mp hk |>.1 ) ( Finset.mem_Icc.mp hk |>.2 ) |> le_trans <| by simp +decide [ Int.natAbs_mul ] ; ;
    generalize_proofs at *; (
    rw [ MvPolynomial.coeff_mul ] ; (
    refine' Finset.dvd_sum fun x hx => _ ; erw [ MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', MvPolynomial.coeff_X' ] ; aesop;))
  exact dvd_add (by simpa using h_coeff_boundary) (by erw [MvPolynomial.coeff_sum]; exact Finset.dvd_sum fun x hx => h_coeff_dvd x hx))

theorem coeff_B_n_dvd (p n e : ℕ) [Fact p.Prime] (hn : 0 < n)
    (he : ∀ k ∈ Finset.Icc 1 (2 * n),
      e ≤ padicValNat p (Int.natAbs (b_formula n k))) :
    ∀ m, ((p ^ e : ℕ) : ℤ) ∣ (B_n n).coeff m := by
  rw [B_n_eq_alt n hn]
  exact coeff_B_n_alt_dvd p n e hn he

-- ============================================================
-- coeff_A_n_dvd and coeff_C_n_dvd: COUNTEREXAMPLE
-- ============================================================

/-
The original theorems coeff_A_n_dvd and coeff_C_n_dvd claimed that
every coefficient of A_n (resp. C_n) is divisible by p^e with the
same hypothesis. However, these statements are FALSE.

Counterexample: n = 2, p = 2.
  The b_k values for N = 4 are:
    |b_1| = 3456 = 2^7 × 27,  v_2 = 7
    |b_2| = 576  = 2^6 × 9,   v_2 = 6
    |b_3| = 576  = 2^6 × 9,   v_2 = 6
    |b_4| = 3456 = 2^7 × 27,  v_2 = 7
  So e ≤ 6 from the hypothesis.

  But the coefficient of A_2 at monomial X_2² (the diagonal term)
  comes only from i = 2:
    (-1)^2 × C(4,2) × α(2,2) × β(2,2) = 6 × 12 × 12 = 864 = 2^5 × 27
  which has v_2 = 5 < 6. So 2^6 does NOT divide 864.

  Similarly for C_2 at monomial X_3².

  The issue is that the "diagonal" term (at i = n, where the monomial
  is X_n² for A_n or X_{n+1}² for C_n) has v_p that is v_p(|b_n|) + v_p(n+1) - v_p(2),
  which can be less than e when p = 2 and n is even.

  Note: B_n does NOT have this issue because its monomials have odd
  index sum (2n+1), so there is no diagonal term, and all coefficients
  are exactly b_k values (up to the boundary term 2·((2n+1)!)²).
-/

-- Original false theorem, commented out:
-- theorem coeff_A_n_dvd (p n e : ℕ) [Fact p.Prime]
--     (he : ...) : ∀ m, ((p ^ e : ℕ) : ℤ) ∣ (A_n n).coeff m

-- Original false theorem, commented out:
-- theorem coeff_C_n_dvd (p n e : ℕ) [Fact p.Prime]
--     (he : ...) : ∀ m, ((p ^ e : ℕ) : ℤ) ∣ (C_n n).coeff m

-- ============================================================
-- coeff_Δ_n_dvd_sq: correct as stated (conditional)
-- ============================================================

/--
Consequence: every coefficient of Δ_n has v_p ≥ 2e.
This is correct as stated — it is conditional on hA, hB, hC.
Note that hA and hC cannot be satisfied with the same e as hB
(see the counterexample above), but the conditional statement is valid.
-/
theorem coeff_Δ_n_dvd_sq (p n e : ℕ) [Fact p.Prime]
    (hA : ∀ m, ((p ^ e : ℕ) : ℤ) ∣ (A_n n).coeff m)
    (hB : ∀ m, ((p ^ e : ℕ) : ℤ) ∣ (B_n n).coeff m)
    (hC : ∀ m, ((p ^ e : ℕ) : ℤ) ∣ (C_n n).coeff m) :
    ∀ m, ((p ^ (2 * e) : ℕ) : ℤ) ∣ (Δ_n n).coeff m := by
  intro m
  have cast_eq : ((p ^ (2 * e) : ℕ) : ℤ) = ((p ^ e : ℕ) : ℤ) * ((p ^ e : ℕ) : ℤ) := by
    push_cast; ring
  rw [cast_eq]
  unfold Δ_n
  rw [MvPolynomial.coeff_sub]
  apply dvd_sub
  · rw [sq, MvPolynomial.coeff_mul]
    exact Finset.dvd_sum fun x _ => mul_dvd_mul (hB _) (hB _)
  · have h4 : (4 : MvPolynomial ℕ ℤ) = MvPolynomial.C 4 := by simp [map_ofNat]
    rw [show (4 : MvPolynomial ℕ ℤ) * A_n n * C_n n = MvPolynomial.C 4 * (A_n n * C_n n) by
      rw [h4]; ring]
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul]
    apply dvd_mul_of_dvd_right
    exact Finset.dvd_sum fun x _ => mul_dvd_mul (hA _) (hC _)

end QuarticInvariant
