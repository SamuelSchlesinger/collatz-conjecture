import Collatz.IterateFormula
import Mathlib.Tactic.Ring

namespace Collatz

/-! ## Steiner's No 1-Cycle Theorem (Partial)

A "1-cycle" has all odd steps first, then all even steps. We prove the key
structural lemmas about consecutive steps and the simplest case: the only
1-cycle with exactly one odd step has `n = 1` (the trivial {1,4,2} cycle).
-/

/-! ### Consecutive odd steps -/

/-- After `b` consecutive odd steps starting from `n`, the value is `3^b * n + d`
where `d = (3^b - 1) / 2`, encoded as `2 * d + 1 = 3^b` to avoid division. -/
theorem consecutive_odd_steps (n : ℕ) (b : ℕ)
    (hodd : ∀ (i : ℕ), i < b → (collatz^[i] n) % 2 = 1) :
    ∃ (d : ℕ), collatz^[b] n = 3 ^ b * n + d ∧ 2 * d + 1 = 3 ^ b := by
  induction b with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ b ih =>
    have hodd_b : ∀ i, i < b → (collatz^[i] n) % 2 = 1 :=
      fun i hi => hodd i (Nat.lt_succ_of_lt hi)
    obtain ⟨d, hval, hacc⟩ := ih hodd_b
    have hmod : (collatz^[b] n) % 2 = 1 := hodd b (Nat.lt_succ_iff.mpr le_rfl)
    rw [Function.iterate_succ_apply', collatz_odd hmod, hval]
    refine ⟨3 * d + 1, ?_, ?_⟩
    · nlinarith [pow_succ 3 b]
    · nlinarith [pow_succ 3 b]

/-! ### Consecutive even halvings -/

/-- Repeatedly halving an even number: if all intermediate iterates are even,
then `collatz^[j] m * 2^j = m`. -/
theorem even_halvings_mul (m : ℕ) (j : ℕ)
    (heven : ∀ i, i < j → (collatz^[i] m) % 2 = 0) :
    collatz^[j] m * 2 ^ j = m := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hev' : ∀ i, i < j → (collatz^[i] m) % 2 = 0 := fun i hi => heven i (by omega)
    have hprev := ih hev'
    rw [Function.iterate_succ_apply']
    have hmod : (collatz^[j] m) % 2 = 0 := heven j (by omega)
    rw [collatz_even hmod, pow_succ, ← Nat.mul_assoc]
    have hdvd2 : 2 ∣ collatz^[j] m := by omega
    obtain ⟨d, hd⟩ := hdvd2
    rw [hd, Nat.mul_div_cancel_left d (by omega : 0 < 2)]
    rw [hd] at hprev
    linarith

/-! ### No 1-cycle with b = 1 -/

/-- If `n` is on a 1-cycle with exactly one odd step (n is odd, then all remaining steps
are even), then `n = 1`. The only such cycle is the trivial {1, 4, 2} cycle. -/
theorem no_one_cycle_b_eq_one {n : ℕ} {p : ℕ} (hn : 0 < n)
    (hp : 2 ≤ p) (hcyc : collatz^[p] n = n)
    (hodd_first : n % 2 = 1)
    (heven_rest : ∀ (i : ℕ), 1 ≤ i → i < p → (collatz^[i] n) % 2 = 0) :
    n = 1 := by
  have hstep1 : collatz n = 3 * n + 1 := collatz_odd hodd_first
  have hcyc' : collatz^[p - 1] (3 * n + 1) = n := by
    have : collatz^[p] n = collatz^[p - 1] (collatz n) := by
      conv_lhs => rw [show p = (p - 1) + 1 by omega]
      rw [Function.iterate_succ_apply]
    rw [hstep1] at this; linarith [this, hcyc]
  have h3n1_even : ∀ j, j < p - 1 → (collatz^[j] (3 * n + 1)) % 2 = 0 := by
    intro j hj
    have : collatz^[j] (3 * n + 1) = collatz^[j + 1] n := by
      rw [show j + 1 = j.succ from rfl, Function.iterate_succ_apply, hstep1]
    rw [this]
    exact heven_rest (j + 1) (by omega) (by omega)
  have hdiv := even_halvings_mul (3 * n + 1) (p - 1) h3n1_even
  rw [hcyc'] at hdiv
  -- Now: n * 2^(p-1) = 3n + 1
  -- Introduce k = 2^(p-1) to let omega work
  set k := 2 ^ (p - 1) with hk_def
  -- n * k = 3 * n + 1
  by_cases hp1 : p - 1 = 1
  · have hk2 : k = 2 := by rw [hk_def, hp1]; norm_num
    rw [hk2] at hdiv; omega
  · have hp2 : 2 ≤ p - 1 := by omega
    have hk4 : 4 ≤ k := by
      rw [hk_def]; calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by omega) hp2
    -- n * k = 3n + 1, k ≥ 4 → 4n ≤ n * k = 3n + 1 → n ≤ 1
    nlinarith [Nat.mul_le_mul_right n hk4]

end Collatz
