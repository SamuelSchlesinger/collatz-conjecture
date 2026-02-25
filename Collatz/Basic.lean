import Collatz.Defs

namespace Collatz

@[simp]
theorem collatz_even {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  unfold collatz; simp [h]

@[simp]
theorem collatz_odd {n : ℕ} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz; simp [h]

@[simp]
theorem collatz_zero : collatz 0 = 0 := by
  unfold collatz; simp

@[simp]
theorem collatz_one : collatz 1 = 4 := by
  unfold collatz; simp

@[simp]
theorem collatz_two : collatz 2 = 1 := by
  unfold collatz; simp

@[simp]
theorem collatz_four : collatz 4 = 2 := by
  unfold collatz; simp

theorem collatz_odd_is_even {n : ℕ} (h : n % 2 = 1) : (collatz n) % 2 = 0 := by
  simp [collatz, h]
  omega

end Collatz
