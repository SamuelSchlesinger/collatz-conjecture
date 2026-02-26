import Collatz.IterateFormula

namespace Collatz

/-! ## Böhm-Sontacchi Cycle Equation

If `n` is periodic under the Collatz function with period `p`, i.e. `collatz^[p] n = n`,
then the iterate formula specializes to `2^a · n = 3^b · n + c`, which rearranges to
`(2^a - 3^b) · n = c` in the integers. This is the fundamental arithmetic constraint
on Collatz cycles.
-/

theorem cycle_linear_constraint {n : ℕ} {p : ℕ}
    (hcyc : collatz^[p] n = n) :
    ∃ (a b c : ℕ), a + b = p ∧ 2 ^ a * n = 3 ^ b * n + c := by
  obtain ⟨a, b, c, hab, heq⟩ := iterate_linear_form n p
  exact ⟨a, b, c, hab, by rw [hcyc] at heq; exact heq⟩

theorem cycle_equation_int {n : ℕ} {p : ℕ}
    (hcyc : collatz^[p] n = n) :
    ∃ (a b c : ℕ), a + b = p ∧
      ((2 : ℤ) ^ a - (3 : ℤ) ^ b) * (n : ℤ) = (c : ℤ) := by
  obtain ⟨a, b, c, hab, heq⟩ := cycle_linear_constraint hcyc
  refine ⟨a, b, c, hab, ?_⟩
  have heqZ : (2 : ℤ) ^ a * (n : ℤ) = (3 : ℤ) ^ b * (n : ℤ) + (c : ℤ) := by
    exact_mod_cast heq
  nlinarith [sub_mul ((2 : ℤ) ^ a) ((3 : ℤ) ^ b) (n : ℤ)]

theorem cycle_two_pow_ge {n : ℕ} {p : ℕ} (hn : 0 < n)
    (hcyc : collatz^[p] n = n) :
    ∃ (a b c : ℕ), a + b = p ∧ 2 ^ a * n = 3 ^ b * n + c ∧ 3 ^ b ≤ 2 ^ a := by
  obtain ⟨a, b, c, hab, heq⟩ := cycle_linear_constraint hcyc
  refine ⟨a, b, c, hab, heq, ?_⟩
  nlinarith

end Collatz
