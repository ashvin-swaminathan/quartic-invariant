import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant


/-! ## Factorial coefficients -/

/-- α(n,i) = (2n+1-i)! · i! -/
def α (n i : ℕ) : ℕ := (2 * n + 1 - i).factorial * i.factorial

/-- β(n,i) = (2n-i)! · (i+1)! -/
def β (n i : ℕ) : ℕ := (2 * n - i).factorial * (i + 1).factorial

/-! ## Quadratic covariant coefficients as multivariate polynomials -/

/-- A_n = Σ (-1)^i C(2n,i) α_i β_i · f_i · f_{2n-i} -/
def A_n (n : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ i ∈ Finset.range (2 * n + 1),
    MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ)) *
    MvPolynomial.X i * MvPolynomial.X (2 * n - i)

/-- B_n = Σ (-1)^i C(2n,i) [α_i² f_i f_{2n+1-i} + β_i² f_{i+1} f_{2n-i}] -/
def B_n (n : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ i ∈ Finset.range (2 * n + 1),
    MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ)) *
    (MvPolynomial.C ((α n i : ℤ) ^ 2) *
      MvPolynomial.X i * MvPolynomial.X (2 * n + 1 - i) +
     MvPolynomial.C ((β n i : ℤ) ^ 2) *
      MvPolynomial.X (i + 1) * MvPolynomial.X (2 * n - i))

/-- C_n = Σ (-1)^i C(2n,i) α_i β_i · f_{i+1} · f_{2n+1-i} -/
def C_n (n : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ i ∈ Finset.range (2 * n + 1),
    MvPolynomial.C ((-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ)) *
    MvPolynomial.X (i + 1) * MvPolynomial.X (2 * n + 1 - i)

/-! ## Discriminant and content -/

/-- Δ_n = B_n² - 4·A_n·C_n -/
def Δ_n (n : ℕ) : MvPolynomial ℕ ℤ :=
  (B_n n) ^ 2 - 4 * (A_n n) * (C_n n)

/-- Content of an integer-coefficient multivariate polynomial:
    gcd of the absolute values of all coefficients. -/
def mvContent (p : MvPolynomial ℕ ℤ) : ℕ :=
  p.support.gcd (fun m => Int.natAbs (p.coeff m))

/-- S(n) = content of Δ_n -/
def S (n : ℕ) : ℕ := mvContent (Δ_n n)

/-! ## Two-point specialization -/

/-- φ(n,k) sets f_k = f_{2n+1-k} = 1, all others 0. -/
def phi (n k : ℕ) : ℕ → ℤ :=
  fun j => if j = k ∨ j = 2 * n + 1 - k then 1 else 0

/-! ## Cancellation-free B_n diagonal coefficient -/

/-- b_k = 2·(-1)^k · (N!)² · (N+1-k) · (N+1-2k) / C(N,k),  where N = 2n.
    This is the coefficient [f_k · f_{N+1-k}] B_n. -/
def b_k_val (n k : ℕ) : ℤ :=
  2 * (-1 : ℤ) ^ k * ((2 * n).factorial : ℤ) ^ 2 *
    ((2 * n : ℤ) + 1 - k) * ((2 * n : ℤ) + 1 - 2 * k) /
    (Nat.choose (2 * n) k : ℤ)



def γ (n : ℕ) : ℕ := (n + 1).factorial * n.factorial
def e_central (p n : ℕ) : ℕ := padicValNat p (Nat.choose (2 * n) n * (γ n) ^ 2)

def A_eval (n : ℕ) (c : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 1),
    (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ) * c i * c (2 * n - i)
def B_eval (n : ℕ) (c : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 1),
    (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      ((α n i : ℤ) ^ 2 * c i * c (2 * n + 1 - i) +
       (β n i : ℤ) ^ 2 * c (i + 1) * c (2 * n - i))
def C_eval (n : ℕ) (c : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 1),
    (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) *
      (α n i : ℤ) * (β n i : ℤ) * c (i + 1) * c (2 * n + 1 - i)
def Δ_eval (n : ℕ) (c : ℕ → ℤ) : ℤ :=
  (B_eval n c) ^ 2 - 4 * (A_eval n c) * (C_eval n c)

def scalar_AB (n i : ℕ) : ℕ := Nat.choose (2 * n) i * α n i * β n i
def scalar_A2 (n i : ℕ) : ℕ := Nat.choose (2 * n) i * (α n i) ^ 2
def scalar_B2 (n i : ℕ) : ℕ := Nat.choose (2 * n) i * (β n i) ^ 2

def deform_spec (n t : ℕ) : ℕ → ℤ :=
  fun j => if j = n then 1 else if j = n + 1 then -1
    else if j = n - t then 1 else if j = n + t + 1 then 1 else 0
def deform_spec_k1 (n : ℕ) : ℕ → ℤ :=
  fun j => if j = n - 1 then 1 else if j = n then 1
    else if j = n + 1 then -1 else if j = n + 2 then 1 else 0
def u_val (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) * ((γ n : ℤ) ^ 2)

end QuarticInvariant
