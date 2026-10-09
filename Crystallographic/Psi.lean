module

public import Crystallographic.Defs

/-!
# The arithmetic of `ψ`

Values, additivity on coprime factors, the comparison with `φ`, parity, the divisor-sum form, the
bound `m ≤ 2^(ψ m + 1)`, and the covering inequality `ψ m ≤ ∑_{d ∈ S} φ d` used by necessity.
Lane: **psi**. Every statement below is pinned (name, hypotheses, conclusion); helpers may be added
freely in this file.
-/

@[expose] public section

namespace Crystallographic

theorem psi_zero : psi 0 = 0 := sorry

theorem psi_one : psi 1 = 0 := sorry

theorem psi_two : psi 2 = 0 := sorry

theorem psi_eq_zero_iff_internal (m : ℕ) : psi m = 0 ↔ m ≤ 2 := sorry

theorem psi_prime_pow_internal {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (h2 : p ^ k ≠ 2) :
    psi (p ^ k) = Nat.totient (p ^ k) := sorry

theorem psi_mul_internal {a b : ℕ} (hab : Nat.Coprime a b) : psi (a * b) = psi a + psi b := sorry

theorem psi_le_totient_internal (m : ℕ) : psi m ≤ Nat.totient m := sorry

theorem even_psi_internal (m : ℕ) : Even (psi m) := sorry

theorem psi_eq_sum_divisors_internal (m : ℕ) :
    psi m = ∑ d ∈ m.divisors,
      if IsPrimePow d ∧ Nat.Coprime d (m / d) ∧ d ≠ 2 then Nat.totient d else 0 := sorry

theorem le_two_pow_psi_internal {m : ℕ} (hm : 0 < m) : m ≤ 2 ^ (psi m + 1) := sorry

/-- The covering inequality: if every prime power `p ^ k` exactly dividing `m` divides some
`d ∈ S`, then `ψ m ≤ ∑_{d ∈ S} φ d`. (Group the primes of `m` by a chosen `d`; the terms of `ψ m`
at the primes assigned to `d` are at most the corresponding terms of `ψ d`, and `ψ d ≤ φ d`.) -/
theorem psi_le_sum_totient {m : ℕ} {S : Finset ℕ}
    (hcover : ∀ p ∈ m.primeFactors, ∃ d ∈ S, p ^ m.factorization p ∣ d) :
    psi m ≤ ∑ d ∈ S, Nat.totient d := sorry

end Crystallographic
