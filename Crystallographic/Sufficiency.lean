module

public import Crystallographic.Psi
public import Crystallographic.Block

/-!
# Sufficiency: an element of order `m` in dimension `ψ m`

By `Nat.recOnPosPrimePosCoprime` on `m`, for `m ≥ 1` with `m` odd or `4 ∣ m`: a prime power
`p ^ k ≠ 2` is the cyclotomic block of size `φ (p ^ k) = ψ (p ^ k)`; coprime factors `a`, `b`
(both odd, or one odd and `4` dividing the other) are block-summed into dimension
`ψ a + ψ b = ψ (a * b)`; `m = 1` is the empty matrix. For `m ≡ 2 (mod 4)`, `m ≠ 2`: `m = 2 * m'`
with `m'` odd, `ψ m = ψ m' ≥ 2`, and `−A` for the element `A` of order `m'`. Then pad to any
`N ≥ ψ m`; for `m = 2` take `−1` in dimension `N ≥ 1`. Lane: **sufficiency**.
-/

@[expose] public section

namespace Crystallographic

/-- An element of order `m` in dimension `ψ m`, for every `m ≥ 1` other than `2`. -/
theorem exists_orderOf_eq_psi {m : ℕ} (hm : 0 < m) (h2 : m ≠ 2) :
    ∃ A : Matrix.GeneralLinearGroup (Fin (psi m)) ℤ, orderOf A = m := sorry

theorem exists_orderOf_eq_internal {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (h : psi m ≤ N) :
    ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m := sorry

end Crystallographic
