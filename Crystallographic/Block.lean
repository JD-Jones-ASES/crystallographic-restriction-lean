module

public import Crystallographic.Defs

/-!
# The building blocks of the construction

* The cyclotomic block: for `n ≥ 1`, multiplication by `root (cyclotomic n ℤ)` on
  `AdjoinRoot (cyclotomic n ℤ)` is a `ℤ`-linear automorphism of a free module of rank `φ n`
  (`AdjoinRoot.powerBasis'` with `cyclotomic.monic`, `natDegree_cyclotomic`); its matrix in the
  power basis is an element of `GL (Fin (φ n)) ℤ` of order `n` (`root ^ n = 1` as
  `Φₙ ∣ X ^ n − 1`; `root ^ d ≠ 1` for `0 < d < n` as `Φₙ ∤ X ^ d − 1`, by coprimality over `ℚ`
  via `Polynomial.map_dvd_map` for monic polynomials, or by a degree argument for prime powers).
  Route: `Algebra.lmul ℤ _` composed with `LinearMap.toMatrixAlgEquiv pb.basis` is an injective
  ring hom into the matrix ring; `Units.map` and `orderOf_injective` carry the order.
* Block sums: `Matrix.fromBlocks A 0 0 B` reindexed along `finSumFinEquiv`; commuting blocks of
  coprime orders multiply (`Commute.orderOf_mul_eq_mul_orderOf_of_coprime`).
* Padding by an identity block, and the sign: `−A` has order `2u` when `A` has odd order `u` in a
  positive dimension (`orderOf_neg_one`, the two commute, `Nat.Coprime 2 u`).

Lane: **block**. Every statement below is pinned; helpers may be added freely in this file.
-/

@[expose] public section

namespace Crystallographic

/-- The cyclotomic block: an element of `GL (φ n, ℤ)` of order `n`, for every `n ≥ 1`. -/
theorem exists_orderOf_eq_totient_internal {n : ℕ} (hn : 0 < n) :
    ∃ A : Matrix.GeneralLinearGroup (Fin (Nat.totient n)) ℤ, orderOf A = n := sorry

/-- Block sum: elements of coprime orders `u`, `v` in dimensions `a`, `b` give an element of order
`u * v` in dimension `a + b`. -/
theorem exists_orderOf_eq_mul {a b u v : ℕ} (huv : Nat.Coprime u v)
    (hA : ∃ A : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf A = u)
    (hB : ∃ B : Matrix.GeneralLinearGroup (Fin b) ℤ, orderOf B = v) :
    ∃ C : Matrix.GeneralLinearGroup (Fin (a + b)) ℤ, orderOf C = u * v := sorry

/-- Padding: an element of order `u` in dimension `a ≤ N` gives one in dimension `N`. -/
theorem exists_orderOf_eq_of_le {a N u : ℕ} (h : a ≤ N)
    (hA : ∃ A : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf A = u) :
    ∃ C : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf C = u := sorry

/-- The sign: in a positive dimension, `−A` has order `2 * u` when `A` has odd order `u`. -/
theorem exists_orderOf_eq_two_mul {a u : ℕ} (ha : 0 < a) (hu : Odd u)
    (hA : ∃ A : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf A = u) :
    ∃ C : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf C = 2 * u := sorry

/-- `−1` has order `2` in every positive dimension. -/
theorem orderOf_neg_one_gl {N : ℕ} (hN : 0 < N) :
    orderOf (-1 : Matrix.GeneralLinearGroup (Fin N) ℤ) = 2 := sorry

end Crystallographic
