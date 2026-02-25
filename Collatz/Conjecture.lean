import Collatz.Defs
import Mathlib.Dynamics.PeriodicPts.Defs

namespace Collatz

/-- The Collatz conjecture: every positive integer eventually reaches 1. -/
theorem collatz_conjecture : ∀ n : ℕ, 1 ≤ n → CollatzConverges n := by
  sorry

/-- There are no non-trivial cycles: the only cycle reachable from positive
    integers is {1, 4, 2}. -/
theorem collatz_unique_cycle (k : ℕ) :
    ∀ n : ℕ, 1 ≤ n → Function.IsPeriodicPt collatz k n → k > 0 →
      n = 1 ∨ n = 2 ∨ n = 4 := by
  sorry

end Collatz
