import Mathlib
import Modular.Defs
import Modular.MainP5
import Modular.MainP3
import Modular.MainP2

set_option linter.mathlibStandardSet false
open scoped BigOperators Nat Classical Pointwise
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
noncomputable section
namespace QuarticInvariant

theorem main_theorem_full (p n : ℕ) [hp : Fact p.Prime] (hn : 2 ≤ n) :
    Odd (padicValNat p (S n)) ↔ (p ≠ 2 ∧ ∃ k : ℕ, 1 ≤ k ∧ n + 2 = p ^ k) := by
  have hp_prime := hp.out
  have hp2_le := hp_prime.two_le
  constructor
  · intro hodd
    refine ⟨?_, ?_⟩
    · intro hp2; subst hp2
      obtain ⟨r, hr⟩ := main_theorem_p2 n (by omega)
      obtain ⟨s, hs⟩ := hodd; omega
    · by_cases hp5 : 5 ≤ p
      · exact ((main_theorem p n hp5 hn).mp hodd)
      · have hp23 : p = 2 ∨ p = 3 := by
          have : p < 5 := by omega
          have : p ≠ 4 := fun h => by subst h; exact absurd hp_prime (by decide)
          omega
        rcases hp23 with rfl | rfl
        · obtain ⟨r, hr⟩ := main_theorem_p2 n (by omega)
          obtain ⟨s, hs⟩ := hodd; omega
        · exact (main_theorem_p3 n hn).mp hodd
  · rintro ⟨hp_odd, k, hk, hpow⟩
    by_cases hp5 : 5 ≤ p
    · exact ((main_theorem p n hp5 hn).mpr ⟨k, hk, hpow⟩)
    · have hp23 : p = 2 ∨ p = 3 := by
        have h5 : p < 5 := by omega
        have h4 : ¬Nat.Prime 4 := by decide
        interval_cases p <;> simp_all
      rcases hp23 with rfl | rfl
      · exact absurd rfl hp_odd
      · exact (main_theorem_p3 n hn).mpr ⟨k, hk, hpow⟩

end QuarticInvariant
