import Collatz.Structural

namespace Collatz

/-! ## Section 1: Even Preimage -/

theorem collatz_double (n : ℕ) : collatz (2 * n) = n := by
  have h : (2 * n) % 2 = 0 := by omega
  rw [collatz_even h]
  omega

theorem collatz_preimage_of_even {m n : ℕ} (hm : m % 2 = 0) (h : collatz m = n) :
    m = 2 * n := by
  rw [collatz_even hm] at h
  omega

/-! ## Section 2: Odd Preimage Existence -/

theorem odd_preimage_is_odd {n : ℕ} (h : n % 6 = 4) : ((n - 1) / 3) % 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 6 * k + 4 := ⟨n / 6, by omega⟩
  omega

theorem odd_preimage_val {n : ℕ} (h : n % 6 = 4) : collatz ((n - 1) / 3) = n := by
  have hodd := odd_preimage_is_odd h
  rw [collatz_odd hodd]
  obtain ⟨k, rfl⟩ : ∃ k, n = 6 * k + 4 := ⟨n / 6, by omega⟩
  omega

theorem no_odd_preimage {n : ℕ} (h : n % 6 ≠ 4) {m : ℕ} (hm : m % 2 = 1) :
    collatz m ≠ n := by
  intro heq
  rw [collatz_odd hm] at heq
  omega

theorem collatz_preimage_of_odd {m n : ℕ} (hm : m % 2 = 1) (h : collatz m = n) :
    m = (n - 1) / 3 := by
  rw [collatz_odd hm] at h
  omega

/-! ## Section 3: Preimage Properties -/

theorem odd_preimage_lt {n : ℕ} (h : n % 6 = 4) : (n - 1) / 3 < n := by
  omega

theorem preimage_even_ne_odd {n : ℕ} (h : n % 6 = 4) : (n - 1) / 3 ≠ 2 * n := by
  omega

/-! ## Section 4: Injectivity -/

theorem collatz_injective_on_odd {m₁ m₂ : ℕ} (h₁ : m₁ % 2 = 1) (h₂ : m₂ % 2 = 1)
    (h : collatz m₁ = collatz m₂) : m₁ = m₂ := by
  rw [collatz_odd h₁, collatz_odd h₂] at h
  omega

theorem collatz_injective_on_even {m₁ m₂ : ℕ} (h₁ : m₁ % 2 = 0) (h₂ : m₂ % 2 = 0)
    (h : collatz m₁ = collatz m₂) : m₁ = m₂ := by
  rw [collatz_even h₁, collatz_even h₂] at h
  omega

/-! ## Section 5: Convergence Propagation (Backward) -/

theorem converges_double {n : ℕ} (h : CollatzConverges n) : CollatzConverges (2 * n) := by
  exact converges_preimage (by rw [collatz_double]; exact h)

theorem converges_odd_preimage {n : ℕ} (h : CollatzConverges n) (hmod : n % 6 = 4) :
    CollatzConverges ((n - 1) / 3) := by
  exact converges_preimage (by rw [odd_preimage_val hmod]; exact h)

end Collatz
