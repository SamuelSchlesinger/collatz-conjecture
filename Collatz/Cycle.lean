import Collatz.Basic
import Mathlib.Dynamics.PeriodicPts.Defs

namespace Collatz

theorem collatz_cycle : collatz^[3] 1 = 1 := by native_decide

theorem one_isPeriodicPt : Function.IsPeriodicPt collatz 3 1 := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  exact collatz_cycle

theorem collatz_fixedPt_zero (n : ℕ) : collatz n = n ↔ n = 0 := by
  constructor
  · intro h
    unfold collatz at h
    split_ifs at h with he
    · omega
    · omega
  · intro h
    subst h
    simp

theorem converges_one : CollatzConverges 1 :=
  ⟨0, rfl⟩

theorem converges_two : CollatzConverges 2 :=
  ⟨1, by native_decide⟩

theorem converges_four : CollatzConverges 4 :=
  ⟨2, by native_decide⟩

end Collatz
