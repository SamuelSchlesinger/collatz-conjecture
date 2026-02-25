import Collatz.Cycle

namespace Collatz

/-! ## Convergence Propagation -/

theorem converges_step {n : ℕ} (h : CollatzConverges n) : CollatzConverges (collatz n) := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero =>
    simp at hk
    subst hk
    exact converges_four
  | succ k' =>
    exact ⟨k', by rwa [Function.iterate_succ_apply] at hk⟩

theorem converges_preimage {n : ℕ} (h : CollatzConverges (collatz n)) : CollatzConverges n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rwa [Function.iterate_succ_apply]⟩

theorem not_converges_zero : ¬CollatzConverges 0 := by
  rintro ⟨k, hk⟩
  have : collatz^[k] 0 = 0 := Function.iterate_fixed collatz_zero k
  omega

theorem converges_iterate {n : ℕ} (h : CollatzConverges n) (k : ℕ) :
    CollatzConverges (collatz^[k] n) := by
  induction k with
  | zero => exact h
  | succ k' ih =>
    rw [Function.iterate_succ_apply']
    exact converges_step ih

/-! ## Syracuse Shortcut -/

/-- The Syracuse shortcut map: for odd n, applies one step of 3n+1 and one step of /2. -/
def collatzShortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

@[simp]
theorem collatzShortcut_even {n : ℕ} (h : n % 2 = 0) : collatzShortcut n = n / 2 := by
  unfold collatzShortcut; simp [h]

@[simp]
theorem collatzShortcut_odd {n : ℕ} (h : n % 2 = 1) : collatzShortcut n = (3 * n + 1) / 2 := by
  unfold collatzShortcut; simp [h]

theorem collatzShortcut_odd_eq_collatz_collatz {n : ℕ} (h : n % 2 = 1) :
    collatzShortcut n = collatz (collatz n) := by
  rw [collatzShortcut_odd h, collatz_odd h]
  have he : (3 * n + 1) % 2 = 0 := by omega
  rw [collatz_even he]

/-! ## Stopping Time -/

theorem stoppingTime_one : stoppingTime 1 converges_one = 0 :=
  le_antisymm (stoppingTime_min 1 converges_one 0 rfl) (Nat.zero_le _)

theorem stoppingTime_step {n : ℕ} (hn : n ≠ 1) (h : CollatzConverges n)
    (h' : CollatzConverges (collatz n)) :
    stoppingTime n h = stoppingTime (collatz n) h' + 1 := by
  apply le_antisymm
  · apply stoppingTime_min
    rw [Function.iterate_succ_apply]
    exact stoppingTime_spec (collatz n) h'
  · have hne : stoppingTime n h ≠ 0 := by
      intro heq
      exact hn (by simpa [heq] using stoppingTime_spec n h)
    suffices stoppingTime (collatz n) h' ≤ stoppingTime n h - 1 by omega
    apply stoppingTime_min
    have key := stoppingTime_spec n h
    have hsplit : stoppingTime n h = (stoppingTime n h - 1) + 1 := by omega
    rw [hsplit, Function.iterate_succ_apply] at key
    exact key

end Collatz
