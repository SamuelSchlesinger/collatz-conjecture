import Collatz.Inverse

namespace Collatz

/-! ## Section 1: Inductive Definition -/

/-- Membership in the Collatz preimage tree rooted at 1.
    Built by iterating preimage operations backward from 1:
    every `n` has even preimage `2n`, and odd preimage `(n-1)/3`
    precisely when `n ≡ 4 (mod 6)`. -/
inductive CollatzTree : ℕ → Prop where
  | base : CollatzTree 1
  | even_child {n : ℕ} : CollatzTree n → CollatzTree (2 * n)
  | odd_child {n : ℕ} : CollatzTree n → n % 6 = 4 → CollatzTree ((n - 1) / 3)

/-! ## Section 2: Basic Members -/

theorem collatzTree_two : CollatzTree 2 :=
  CollatzTree.even_child CollatzTree.base

theorem collatzTree_four : CollatzTree 4 :=
  CollatzTree.even_child collatzTree_two

/-! ## Section 3: Tree → Converges -/

theorem CollatzTree.converges {n : ℕ} : CollatzTree n → CollatzConverges n := by
  intro h
  induction h with
  | base => exact converges_one
  | even_child _ ih => exact converges_double ih
  | odd_child _ hmod ih => exact converges_odd_preimage ih hmod

/-! ## Section 4: Backward Closure -/

/-- If `collatz n` is in the tree, then `n` is in the tree.
    This is the key lemma: it lets us "pull back" tree membership
    through any single Collatz step. -/
theorem collatzTree_of_collatz {n : ℕ} (h : CollatzTree (collatz n)) : CollatzTree n := by
  by_cases hpar : n % 2 = 0
  · -- Even case: collatz n = n / 2, so n = 2 * (n / 2) = 2 * (collatz n)
    rw [collatz_even hpar] at h
    have : n = 2 * (n / 2) := by omega
    rw [this]
    exact CollatzTree.even_child h
  · -- Odd case: collatz n = 3n + 1
    have hodd : n % 2 = 1 := by omega
    rw [collatz_odd hodd] at h
    have hmod : (3 * n + 1) % 6 = 4 := by omega
    have heq : (3 * n + 1 - 1) / 3 = n := by omega
    rw [← heq]
    exact CollatzTree.odd_child h hmod

/-! ## Section 5: Converges → Tree -/

theorem CollatzConverges.collatzTree {n : ℕ} (h : CollatzConverges n) : CollatzTree n := by
  obtain ⟨k, hk⟩ := h
  revert n
  induction k with
  | zero =>
    intro n hk
    simp at hk
    subst hk
    exact CollatzTree.base
  | succ k' ih =>
    intro n hk
    rw [Function.iterate_succ_apply] at hk
    exact collatzTree_of_collatz (ih hk)

/-! ## Section 6: Equivalence -/

theorem collatzTree_iff_converges {n : ℕ} : CollatzTree n ↔ CollatzConverges n :=
  ⟨CollatzTree.converges, CollatzConverges.collatzTree⟩

/-! ## Section 7: Conjecture Reformulation -/

theorem collatz_conjecture_iff_tree :
    (∀ n, 1 ≤ n → CollatzConverges n) ↔ (∀ n, 1 ≤ n → CollatzTree n) :=
  ⟨fun h n hn => (h n hn).collatzTree, fun h n hn => (h n hn).converges⟩

/-- The Collatz conjecture, reformulated: every positive integer belongs
    to the preimage tree rooted at 1. -/
theorem collatz_conjecture_tree : ∀ n, 1 ≤ n → CollatzTree n := by
  sorry

/-! ## Section 8: Tree Structure Properties -/

theorem not_collatzTree_zero : ¬CollatzTree 0 := by
  intro h
  exact not_converges_zero h.converges

theorem CollatzTree.pos {n : ℕ} (h : CollatzTree n) : 0 < n := by
  by_contra hle
  push_neg at hle
  have : n = 0 := by omega
  subst this
  exact not_collatzTree_zero h

theorem CollatzTree.collatz {n : ℕ} (h : CollatzTree n) : CollatzTree (collatz n) :=
  (converges_step h.converges).collatzTree

end Collatz
