import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Find

namespace Collatz

/-- The Collatz function: n/2 if n is even, 3n+1 if n is odd. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- A natural number converges under the Collatz function if some iterate equals 1. -/
def CollatzConverges (n : ℕ) : Prop :=
  ∃ k : ℕ, collatz^[k] n = 1

/-- The stopping time of n: the minimal k such that collatz^[k] n = 1. -/
noncomputable def stoppingTime (n : ℕ) (h : CollatzConverges n) : ℕ :=
  Nat.find h

theorem stoppingTime_spec (n : ℕ) (h : CollatzConverges n) :
    collatz^[stoppingTime n h] n = 1 :=
  Nat.find_spec h

theorem stoppingTime_min (n : ℕ) (h : CollatzConverges n) (k : ℕ)
    (hk : collatz^[k] n = 1) : stoppingTime n h ≤ k :=
  Nat.find_min' h hk

end Collatz
