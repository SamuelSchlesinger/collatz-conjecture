# Collatz Conjecture

A Lean 4 formalization of the Collatz conjecture and related structural results.

## The Conjecture

For any positive integer n, repeated application of the Collatz function
(n ↦ n/2 if even, n ↦ 3n+1 if odd) eventually reaches 1.

## Structure

| Module | Contents | Sorry count |
|--------|----------|-------------|
| `Collatz.Defs` | Core definitions: `collatz`, `CollatzConverges`, `stoppingTime` | 0 |
| `Collatz.Basic` | Even/odd case lemmas, specific values | 0 |
| `Collatz.Descent` | Descent for even inputs, growth for odd inputs | 0 |
| `Collatz.Cycle` | The {1,4,2} cycle, fixed point analysis, base convergence | 0 |
| `Collatz.Structural` | Convergence propagation, Syracuse shortcut, stopping time | 0 |
| `Collatz.PowersOfTwo` | All powers of 2 converge, trajectory formula | 0 |
| `Collatz.SmallCases` | n = 1..20 converge by computation | 0 |
| `Collatz.Residue` | Mod 4 two-step behavior, parity of shortcut output, three-step closed form | 0 |
| `Collatz.Inverse` | Even/odd preimages, injectivity, backward convergence | 0 |
| `Collatz.Tree` | Preimage tree, equivalence with convergence, conjecture reformulation | 1 |
| `Collatz.IterateFormula` | Explicit iterate formula: `2^a · T^k(n) = 3^b · n + c` | 0 |
| `Collatz.CycleEquation` | Böhm-Sontacchi cycle equation in ℕ and ℤ | 0 |
| `Collatz.Steiner` | Consecutive step lemmas, no 1-cycle with b=1 (Steiner) | 0 |
| `Collatz.NoCycles` | Periodic + convergent ⟹ trivial cycle, no small cycles ≤ 20 | 0 |
| `Collatz.Conjecture` | The open conjecture and unique cycle conjecture | 2 |

Total sorry count: 3 (the main conjecture, the unique cycle conjecture, and the tree reformulation).

## Dependency Graph

```
Defs → Basic → Cycle → Structural → Residue
                                   → Inverse → Tree → Conjecture
             → IterateFormula → CycleEquation
                              → Steiner
       Defs → SmallCases
Structural + SmallCases → NoCycles
Basic → Descent
Basic → PowersOfTwo
```

## Building

```
lake update && lake build
```
