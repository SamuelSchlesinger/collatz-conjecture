import Collatz.Basic

namespace Collatz

theorem collatz_even_lt {n : ℕ} (hn : 0 < n) (he : n % 2 = 0) : collatz n < n := by
  simp [he]
  exact Nat.div_lt_self hn (by omega)

theorem collatz_odd_gt {n : ℕ} (hn : 0 < n) (ho : n % 2 = 1) : collatz n > n := by
  simp [ho]
  omega

end Collatz
