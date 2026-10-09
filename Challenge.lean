module

public import Mathlib

/-!
# The crystallographic restriction in every dimension: `GL(N, ℤ)` has an element of order `m` if and only if `ψ(m) ≤ N`

For a positive integer `m`, let `ψ(m)` be the sum of `φ(pᵏ)` over the prime powers `pᵏ` exactly
dividing `m`, except that the prime power `2` contributes `0` (`φ` is Euler's totient). So
`ψ(1) = ψ(2) = 0`, `ψ(3) = ψ(4) = ψ(6) = 2`, `ψ(5) = ψ(8) = ψ(10) = ψ(12) = 4`, `ψ(7) = ψ(9) = 6`, and
`ψ(ab) = ψ(a) + ψ(b)` for coprime `a`, `b` (OEIS A080737). The crystallographic restriction in every
dimension (Vaidyanathaswamy 1928; rediscovered by Hiller 1985; a proof in Kuzmanovich–Pavlichenkov
2002; stated as Theorem 1 of Bamberg–Cairns–Kilminster 2003): for `N ≥ 1`, the group `GL(N, ℤ)` of
invertible integer `N × N` matrices has an element of order `m ≥ 1` if and only if `ψ(m) ≤ N`. In
dimensions two and three this is the classical restriction: the finite orders are `1, 2, 3, 4, 6`.

This file states, and `Solution.lean` proves (kernel-only):

* the arithmetic of `ψ`: `ψ(m) = 0` iff `m ≤ 2`; `ψ(pᵏ) = φ(pᵏ)` for a prime power `pᵏ ≠ 2`;
  additivity on coprime factors; `ψ ≤ φ`; `ψ` is even; `ψ` as a sum over the exact prime-power
  divisors; the bound `m ≤ 2^(ψ(m) + 1)`;
* necessity: `ψ(orderOf A) ≤ N` for every `A : GL(N, ℤ)` (an element of infinite order has
  `orderOf A = 0` and `ψ(0) = 0`, so the statement needs no hypothesis);
* sufficiency: for `N ≥ 1`, `m ≥ 1` and `ψ(m) ≤ N`, an element of `GL(N, ℤ)` of order `m`; the
  equivalence; the set of finite orders of `GL(N, ℤ)` is `{m | 0 < m ∧ ψ(m) ≤ N}`;
* the least dimension carrying an element of order `m`: `ψ(m)`, except `1` for `m = 2`; an element of
  `GL(φ(n), ℤ)` of order `n` for every `n ≥ 1` (multiplication by a primitive `n`-th root of unity on
  `ℤ[X]/(Φₙ)`); the same equivalence over `ℚ`; `GL(N + 1, ℤ)` has the same finite orders as
  `GL(N, ℤ)` for even `N ≥ 2`; the set of finite orders is finite, bounded by `2^(N + 1)`;
* the tables: the finite orders of `GL(N, ℤ)` for `N = 1, …, 12`, and the largest finite order
  `2, 6, 12, 30, 60, 120, 210` in dimensions `1, 2, 4, 6, 8, 10, 12`.

Conventions: `orderOf` is Mathlib's (`0` at infinite order); `Matrix.GeneralLinearGroup (Fin N) ℤ`
is the group of units of the matrix ring `Matrix (Fin N) (Fin N) ℤ`; `Nat.totient` is `φ`;
`m.factorization p` is the exponent of the prime `p` in `m`, and `m.primeFactors` its set of
prime divisors; sets of natural numbers are `Set ℕ` literals.
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

/-! ### The arithmetic of `ψ` -/

/-- `ψ(m) = 0` exactly for `m = 0, 1, 2`. -/
theorem psi_eq_zero_iff (m : ℕ) : psi m = 0 ↔ m ≤ 2 := sorry

/-- On a prime power other than `2`, `ψ` is the totient. -/
theorem psi_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (h2 : p ^ k ≠ 2) :
    psi (p ^ k) = Nat.totient (p ^ k) := sorry

/-- `ψ` is additive on coprime factors. -/
theorem psi_mul {a b : ℕ} (hab : Nat.Coprime a b) : psi (a * b) = psi a + psi b := sorry

/-- `ψ(m) ≤ φ(m)`: a sum of integers `≥ 2` is at most their product. -/
theorem psi_le_totient (m : ℕ) : psi m ≤ Nat.totient m := sorry

/-- `ψ(m)` is even: every term `φ(pᵏ)` with `pᵏ ≠ 2` is even. -/
theorem even_psi (m : ℕ) : Even (psi m) := sorry

/-- `ψ(m)` is the sum of `φ(d)` over the divisors `d ≠ 2` of `m` that are prime powers coprime to
their cofactor `m / d`, that is, over the prime powers exactly dividing `m` other than `2`. -/
theorem psi_eq_sum_divisors (m : ℕ) :
    psi m = ∑ d ∈ m.divisors,
      if IsPrimePow d ∧ Nat.Coprime d (m / d) ∧ d ≠ 2 then Nat.totient d else 0 := sorry

/-- The bounding lemma behind the tables: `m ≤ 2^(ψ(m) + 1)` for `m ≥ 1`, since every prime power
`q ≠ 2` satisfies `q ≤ 2^φ(q)`. -/
theorem le_two_pow_psi {m : ℕ} (hm : 0 < m) : m ≤ 2 ^ (psi m + 1) := sorry

/-! ### The restriction -/

/-- Necessity: the order of every element of `GL(N, ℤ)` satisfies `ψ(orderOf A) ≤ N`. The minimal
polynomial of `A` over `ℚ` divides `X^m − 1`, so it is a product of distinct cyclotomic polynomials
`Φ_d` whose indices `d` have least common multiple `m = orderOf A`, and its degree is at most `N`;
each prime power exactly dividing `m` divides one of the `d`, and `ψ(d) ≤ φ(d)`. For an element of
infinite order, `orderOf A = 0` and `ψ(0) = 0`. -/
theorem psi_orderOf_le {N : ℕ} (A : Matrix.GeneralLinearGroup (Fin N) ℤ) :
    psi (orderOf A) ≤ N := sorry

/-- Sufficiency: for `N ≥ 1`, `m ≥ 1` and `ψ(m) ≤ N`, `GL(N, ℤ)` has an element of order `m`: a
block for each prime power `pᵏ ≠ 2` exactly dividing `m` (multiplication by the root of `Φ_{pᵏ}` on
`ℤ[X]/(Φ_{pᵏ})`, of size `φ(pᵏ)`), the sign `−1` when `m ≡ 2 (mod 4)`, and an identity block. -/
theorem exists_orderOf_eq {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (h : psi m ≤ N) :
    ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m := sorry

/-- The crystallographic restriction in every dimension `N ≥ 1`: `GL(N, ℤ)` has an element of
order `m ≥ 1` if and only if `ψ(m) ≤ N`. Both hypotheses are needed: `GL(0, ℤ)` is trivial while
`ψ(2) = 0`, and `orderOf A = 0` means infinite order. -/
theorem exists_orderOf_eq_iff {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m) ↔ psi m ≤ N := sorry

/-- The finite orders of `GL(N, ℤ)`, `N ≥ 1`, are the positive integers with `ψ(m) ≤ N`. -/
theorem finiteOrders_eq {N : ℕ} (hN : 0 < N) : finiteOrders N = {m | 0 < m ∧ psi m ≤ N} := sorry

/-- The least dimension `N` in which `GL(N, ℤ)` has an element of order `m ≥ 1` is `ψ(m)`, except
that it is `1` for `m = 2` (the dimension `0` carries only the order `1`). -/
theorem isLeast_dimension {m : ℕ} (hm : 0 < m) :
    IsLeast {N | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m}
      (if m = 2 then 1 else psi m) := sorry

/-- For every `n ≥ 1`, `GL(φ(n), ℤ)` has an element of order `n`: multiplication by the root of the
`n`-th cyclotomic polynomial on `ℤ[X]/(Φₙ)` in its power basis (the companion matrix of `Φₙ`). -/
theorem exists_orderOf_eq_totient {n : ℕ} (hn : 0 < n) :
    ∃ A : Matrix.GeneralLinearGroup (Fin (Nat.totient n)) ℤ, orderOf A = n := sorry

/-- The same restriction over `ℚ`: `GL(N, ℚ)` has an element of order `m ≥ 1` iff `ψ(m) ≤ N`, for
`N ≥ 1`. (Necessity is proved over `ℚ`; the integer witnesses are rational.) -/
theorem exists_orderOf_eq_iff_rat {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℚ, orderOf A = m) ↔ psi m ≤ N := sorry

/-- Parity: for even `N ≥ 2`, `GL(N + 1, ℤ)` has the same finite orders as `GL(N, ℤ)`, since `ψ`
is even. (`GL(1, ℤ)` has the order `2`, which `GL(0, ℤ)` lacks, so `N ≥ 1` is needed.) -/
theorem finiteOrders_succ_of_even {N : ℕ} (hN : 0 < N) (hN2 : Even N) :
    finiteOrders (N + 1) = finiteOrders N := sorry

/-- Every finite order of an element of `GL(N, ℤ)` is at most `2^(N + 1)`. -/
theorem le_two_pow_of_mem_finiteOrders {N m : ℕ} (h : m ∈ finiteOrders N) :
    m ≤ 2 ^ (N + 1) := sorry

/-- The set of finite orders of `GL(N, ℤ)` is finite. -/
theorem finiteOrders_finite (N : ℕ) : (finiteOrders N).Finite := sorry

/-! ### The tables

The finite orders of `GL(N, ℤ)` for `N = 1, …, 12` (Hiller's table), by the bounding lemma and a
kernel computation of `ψ` on `m ≤ 2^(N + 1)`. -/

theorem finiteOrders_one : finiteOrders 1 = {1, 2} := sorry

/-- The classical crystallographic restriction in the plane. -/
theorem finiteOrders_two : finiteOrders 2 = {1, 2, 3, 4, 6} := sorry

/-- The classical crystallographic restriction in space. -/
theorem finiteOrders_three : finiteOrders 3 = {1, 2, 3, 4, 6} := sorry

theorem finiteOrders_four : finiteOrders 4 = {1, 2, 3, 4, 5, 6, 8, 10, 12} := sorry

theorem finiteOrders_five : finiteOrders 5 = {1, 2, 3, 4, 5, 6, 8, 10, 12} := sorry

theorem finiteOrders_six :
    finiteOrders 6 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} := sorry

theorem finiteOrders_seven :
    finiteOrders 7 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} := sorry

theorem finiteOrders_eight :
    finiteOrders 8 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40,
      42, 60} := sorry

theorem finiteOrders_nine :
    finiteOrders 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40,
      42, 60} := sorry

theorem finiteOrders_ten :
    finiteOrders 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 28, 30,
      35, 36, 40, 42, 45, 48, 56, 60, 70, 72, 84, 90, 120} := sorry

theorem finiteOrders_eleven :
    finiteOrders 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 28, 30,
      35, 36, 40, 42, 45, 48, 56, 60, 70, 72, 84, 90, 120} := sorry

theorem finiteOrders_twelve :
    finiteOrders 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 26,
      28, 30, 33, 35, 36, 40, 42, 44, 45, 48, 56, 60, 63, 66, 70, 72, 80, 84, 90, 105, 120, 126, 140,
      168, 180, 210} := sorry

/-! The largest finite order in dimensions `1, 2, 4, 6, 8, 10, 12`. -/

theorem isGreatest_finiteOrders_one : IsGreatest (finiteOrders 1) 2 := sorry

theorem isGreatest_finiteOrders_two : IsGreatest (finiteOrders 2) 6 := sorry

theorem isGreatest_finiteOrders_four : IsGreatest (finiteOrders 4) 12 := sorry

theorem isGreatest_finiteOrders_six : IsGreatest (finiteOrders 6) 30 := sorry

theorem isGreatest_finiteOrders_eight : IsGreatest (finiteOrders 8) 60 := sorry

theorem isGreatest_finiteOrders_ten : IsGreatest (finiteOrders 10) 120 := sorry

theorem isGreatest_finiteOrders_twelve : IsGreatest (finiteOrders 12) 210 := sorry

end Crystallographic
