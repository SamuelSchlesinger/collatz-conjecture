import Collatz.Basic
import Mathlib.Tactic.Linarith

namespace Collatz

/-! ## Explicit Iterate Formula

After `k` steps of the Collatz function, the result satisfies
`2^a · T^k(n) = 3^b · n + c` where `a` counts even steps, `b` counts odd steps,
and `c` is an accumulator. This is the algebraic identity underlying all cycle analysis.
-/

theorem iterate_linear_form (n : ℕ) (k : ℕ) :
    ∃ (a b c : ℕ), a + b = k ∧ 2 ^ a * collatz^[k] n = 3 ^ b * n + c := by
  induction k with
  | zero => exact ⟨0, 0, 0, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨a, b, c, hab, heq⟩ := ih
    rw [Function.iterate_succ_apply']
    by_cases hmod : (collatz^[k] n) % 2 = 0
    · -- even step: collatz m = m / 2
      refine ⟨a + 1, b, c, by omega, ?_⟩
      rw [collatz_even hmod, pow_succ]
      have hdvd : 2 ∣ collatz^[k] n := by omega
      obtain ⟨d, hd⟩ := hdvd
      rw [hd] at heq ⊢
      rw [Nat.mul_div_cancel_left d (by omega : 0 < 2)]
      linarith
    · -- odd step: collatz m = 3 * m + 1
      have hmod1 : (collatz^[k] n) % 2 = 1 := by omega
      refine ⟨a, b + 1, 3 * c + 2 ^ a, by omega, ?_⟩
      rw [collatz_odd hmod1, pow_succ]
      nlinarith

end Collatz
