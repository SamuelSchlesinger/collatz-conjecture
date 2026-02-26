import Collatz.Basic
import Mathlib.Tactic.Ring

namespace Collatz

theorem collatz_pow_two_succ (k : ℕ) : collatz (2 ^ (k + 1)) = 2 ^ k := by
  have he : (2 ^ (k + 1)) % 2 = 0 := by
    have h : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h]
    omega
  rw [collatz_even he]
  have h : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  omega

theorem converges_pow_two (k : ℕ) : CollatzConverges (2 ^ k) := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 1, ?_⟩
    change collatz^[m] (collatz (2 ^ (n + 1))) = 1
    rw [collatz_pow_two_succ, hm]

theorem trajectory_pow_two (k : ℕ) : collatz^[k] (2 ^ k) = 1 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    rw [Function.iterate_succ_apply, collatz_pow_two_succ, ih]

end Collatz
