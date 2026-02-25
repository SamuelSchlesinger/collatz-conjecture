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
| `Collatz.Cycle` | The {1,4,2} cycle, fixed point analysis | 0 |
| `Collatz.PowersOfTwo` | All powers of 2 converge | 0 |
| `Collatz.SmallCases` | n = 1..20 converge by computation | 0 |
| `Collatz.Conjecture` | The open conjecture and unique cycle conjecture | 2 |

## Building

```
lake update && lake build
```
