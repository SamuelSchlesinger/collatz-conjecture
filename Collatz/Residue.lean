import Collatz.Structural

namespace Collatz

/-! ## Mod 4 Two-Step Behavior

When `n % 4` is known, the result of two consecutive Collatz steps is fully determined.
This is because `n mod 4` encodes the parity of both `n` and the result of the first step.
-/

theorem collatz_collatz_mod4_0 {n : ℕ} (h : n % 4 = 0) :
    collatz (collatz n) = n / 4 := by
  have he1 : n % 2 = 0 := by omega
  have he2 : (n / 2) % 2 = 0 := by omega
  simp [he1, he2]
  omega

theorem collatz_collatz_mod4_1 {n : ℕ} (h : n % 4 = 1) :
    collatz (collatz n) = (3 * n + 1) / 2 := by
  have ho : n % 2 = 1 := by omega
  rw [← collatzShortcut_odd_eq_collatz_collatz ho, collatzShortcut_odd ho]

theorem collatz_collatz_mod4_2 {n : ℕ} (h : n % 4 = 2) :
    collatz (collatz n) = 3 * (n / 2) + 1 := by
  have he : n % 2 = 0 := by omega
  have ho : (n / 2) % 2 = 1 := by omega
  simp [he, ho]

theorem collatz_collatz_mod4_3 {n : ℕ} (h : n % 4 = 3) :
    collatz (collatz n) = (3 * n + 1) / 2 := by
  have ho : n % 2 = 1 := by omega
  rw [← collatzShortcut_odd_eq_collatz_collatz ho, collatzShortcut_odd ho]

/-! ## Descent -/

theorem collatz_collatz_lt_of_mod4_0 {n : ℕ} (hn : 0 < n) (h : n % 4 = 0) :
    collatz (collatz n) < n := by
  rw [collatz_collatz_mod4_0 h]
  omega

/-! ## Parity of Shortcut Output

These determine whether the third Collatz step is a halving or an odd step.
-/

theorem shortcut_even_of_mod4_1 {n : ℕ} (h : n % 4 = 1) :
    (collatzShortcut n) % 2 = 0 := by
  have ho : n % 2 = 1 := by omega
  simp [ho]
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 1 := ⟨n / 4, by omega⟩
  omega

theorem shortcut_odd_of_mod4_3 {n : ℕ} (h : n % 4 = 3) :
    (collatzShortcut n) % 2 = 1 := by
  have ho : n % 2 = 1 := by omega
  simp [ho]
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  omega

/-! ## Three-Step Closed Form -/

theorem three_step_mod4_1 {n : ℕ} (h : n % 4 = 1) :
    collatz (collatz (collatz n)) = (3 * n + 1) / 4 := by
  rw [collatz_collatz_mod4_1 h]
  have he : ((3 * n + 1) / 2) % 2 = 0 := by
    have ho : n % 2 = 1 := by omega
    rw [← collatzShortcut_odd ho]
    exact shortcut_even_of_mod4_1 h
  rw [collatz_even he]
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 1 := ⟨n / 4, by omega⟩
  omega

end Collatz
