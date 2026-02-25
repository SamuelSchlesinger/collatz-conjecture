import Collatz.Defs
import Mathlib.Tactic.IntervalCases

namespace Collatz

theorem converges_3 : CollatzConverges 3 := ⟨7, by native_decide⟩
theorem converges_5 : CollatzConverges 5 := ⟨5, by native_decide⟩
theorem converges_6 : CollatzConverges 6 := ⟨8, by native_decide⟩
theorem converges_7 : CollatzConverges 7 := ⟨16, by native_decide⟩
theorem converges_8 : CollatzConverges 8 := ⟨3, by native_decide⟩
theorem converges_9 : CollatzConverges 9 := ⟨19, by native_decide⟩
theorem converges_10 : CollatzConverges 10 := ⟨6, by native_decide⟩
theorem converges_11 : CollatzConverges 11 := ⟨14, by native_decide⟩
theorem converges_12 : CollatzConverges 12 := ⟨9, by native_decide⟩
theorem converges_13 : CollatzConverges 13 := ⟨9, by native_decide⟩
theorem converges_14 : CollatzConverges 14 := ⟨17, by native_decide⟩
theorem converges_15 : CollatzConverges 15 := ⟨17, by native_decide⟩
theorem converges_16 : CollatzConverges 16 := ⟨4, by native_decide⟩
theorem converges_17 : CollatzConverges 17 := ⟨12, by native_decide⟩
theorem converges_18 : CollatzConverges 18 := ⟨20, by native_decide⟩
theorem converges_19 : CollatzConverges 19 := ⟨20, by native_decide⟩
theorem converges_20 : CollatzConverges 20 := ⟨7, by native_decide⟩

theorem converges_le_twenty (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 20) : CollatzConverges n := by
  interval_cases n
  all_goals first
    | exact ⟨0, by native_decide⟩
    | exact ⟨1, by native_decide⟩
    | exact ⟨2, by native_decide⟩
    | exact ⟨3, by native_decide⟩
    | exact ⟨4, by native_decide⟩
    | exact ⟨5, by native_decide⟩
    | exact ⟨6, by native_decide⟩
    | exact ⟨7, by native_decide⟩
    | exact ⟨8, by native_decide⟩
    | exact ⟨9, by native_decide⟩
    | exact ⟨10, by native_decide⟩
    | exact ⟨11, by native_decide⟩
    | exact ⟨12, by native_decide⟩
    | exact ⟨13, by native_decide⟩
    | exact ⟨14, by native_decide⟩
    | exact ⟨15, by native_decide⟩
    | exact ⟨16, by native_decide⟩
    | exact ⟨17, by native_decide⟩
    | exact ⟨18, by native_decide⟩
    | exact ⟨19, by native_decide⟩
    | exact ⟨20, by native_decide⟩

end Collatz
