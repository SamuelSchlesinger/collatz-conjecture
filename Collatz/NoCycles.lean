import Collatz.Structural
import Collatz.SmallCases

namespace Collatz

/-! ## No Nontrivial Small Cycles

If `n` converges to 1, the only cycle `n` can be on is {1, 2, 4}.
Combined with computational verification that all n ≤ 20 converge,
we rule out nontrivial cycles for small values.
-/

/-! ### The orbit of 1 is {1, 4, 2} -/

/-- Every iterate of 1 under collatz is in {1, 4, 2}. Uses the 3-periodicity of 1. -/
theorem collatz_iterate_one (m : ℕ) :
    collatz^[m] 1 = 1 ∨ collatz^[m] 1 = 4 ∨ collatz^[m] 1 = 2 := by
  -- Reduce to m % 3 using the period-3 cycle
  suffices h : collatz^[m % 3] 1 = 1 ∨ collatz^[m % 3] 1 = 4 ∨ collatz^[m % 3] 1 = 2 by
    have hred : collatz^[m] 1 = collatz^[m % 3] 1 := by
      conv_lhs => rw [show m = 3 * (m / 3) + m % 3 from (Nat.div_add_mod m 3).symm]
      induction (m / 3) with
      | zero => simp
      | succ k ih =>
        rw [show 3 * (k + 1) + m % 3 = (3 * k + m % 3) + 3 by omega,
            Function.iterate_add_apply, collatz_cycle]
        exact ih
    rwa [hred]
  have hlt : m % 3 < 3 := Nat.mod_lt m (by omega)
  interval_cases (m % 3) <;> simp_all

/-! ### Periodic + convergent implies trivial cycle -/

/-- If `n` is both periodic and convergent, then `n ∈ {1, 2, 4}`. -/
theorem periodic_of_converges {n : ℕ} {p : ℕ} (hp : 0 < p)
    (hcyc : collatz^[p] n = n) (hconv : CollatzConverges n) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  obtain ⟨k, hk⟩ := hconv
  -- Reduce k modulo p: collatz^[k%p] n = 1
  have hkmod : collatz^[k % p] n = 1 := by
    rw [show k = p * (k / p) + k % p from (Nat.div_add_mod k p).symm] at hk
    revert hk
    induction (k / p) with
    | zero => simp
    | succ q ihq =>
      rw [show p * (q + 1) + k % p = (p * q + k % p) + p from by
            simp [Nat.mul_succ]; omega,
          Function.iterate_add_apply, hcyc]
      exact ihq
  by_cases hk0 : k % p = 0
  · -- collatz^[0] n = 1, so n = 1
    simp [hk0] at hkmod
    exact Or.inl hkmod
  · -- k % p > 0, express n as an iterate of 1
    have hkp_lt : k % p < p := Nat.mod_lt k hp
    -- n = collatz^[p - k%p] 1
    have hn_eq : n = collatz^[p - k % p] 1 := by
      have h1 : collatz^[p - k % p + k % p] n = collatz^[p - k % p] 1 := by
        rw [Function.iterate_add_apply, hkmod]
      rwa [show p - k % p + k % p = p from by omega, hcyc] at h1
    rw [hn_eq]
    rcases collatz_iterate_one (p - k % p) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

/-! ### No nontrivial cycles for n ≤ 20 -/

/-- No nontrivial cycle exists among values 1 through 20. -/
theorem no_nontrivial_cycle_le_twenty {n : ℕ} {p : ℕ} (hp : 0 < p)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 20)
    (hcyc : collatz^[p] n = n) :
    n = 1 ∨ n = 2 ∨ n = 4 :=
  periodic_of_converges hp hcyc (converges_le_twenty n hn1 hn2)

end Collatz
