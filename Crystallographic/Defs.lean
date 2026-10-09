module

public import Mathlib

/-!
# Definitions

The definitions of `Challenge.lean`, restated character for character with the same import
(`Mathlib`), so that every definition elaborates to the same term in both files; the registry's
comparator judges the elaborated constants. `scripts/check_definitions.py` compares the two files.
-/

@[expose] public section

namespace Crystallographic

/-- Hiller's additive totient `ψ`: the sum of `φ(pᵏ)` over the prime powers `pᵏ` exactly dividing
`m`, except that the prime power `2` (that is, `p = 2` with exponent `1`) contributes `0`. So
`ψ(0) = ψ(1) = ψ(2) = 0`, `ψ(pᵏ) = φ(pᵏ)` for every other prime power, and `ψ(ab) = ψ(a) + ψ(b)`
for coprime `a`, `b` (OEIS A080737). -/
def psi (m : ℕ) : ℕ :=
  ∑ p ∈ m.primeFactors,
    if p ^ m.factorization p = 2 then 0 else Nat.totient (p ^ m.factorization p)

/-- The finite orders of the elements of `GL(N, ℤ)`: the positive integers `m` that are the order
of some element (`orderOf A = 0` means infinite order and is excluded). -/
def finiteOrders (N : ℕ) : Set ℕ :=
  {m | 0 < m ∧ ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m}

end Crystallographic
