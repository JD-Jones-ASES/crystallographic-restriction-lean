module

public import Crystallographic.Main

/-!
# Stretch: the restriction for `SL(N, ℤ)`

For `N ≥ 2`, `SL(N, ℤ)` has an element of order `m ≥ 1` iff `ψ m ≤ N`. Necessity: the inclusion
`SL → GL` (`Matrix.SpecialLinearGroup.toGL`) is an injective hom, so `orderOf` is preserved and
`psi_orderOf_le_internal` applies. Sufficiency: an element of odd order has determinant `1`
automatically (`det A ^ m = 1` with `det A = ±1`); the cyclotomic block of `2 ^ k`, `k ≥ 2`, has
determinant `(−1) ^ φ(2 ^ k) · Φ_{2^k}(0) = 1` (`Algebra.norm ℤ (root) = LinearMap.det`,
`PowerBasis.norm_gen_eq_coeff_zero_minpoly` with `minpoly ℤ root = cyclotomic` by
`minpoly.eq_of_irreducible_of_monic` and `Polynomial.cyclotomic_coeff_zero`); block sums multiply
determinants (`Matrix.det_fromBlocks_zero₂₁`); `det (−A) = det A` in even dimension
(`Matrix.det_neg`), and `ψ m` is even; `−1 ⊕ −1 ⊕ 1` has order `2` and determinant `1` for `N ≥ 2`.
`SL(1, ℤ)` is trivial. Lane: **sl** (stretch; kill at 2 h of lane time; lifted into the Challenge
only if closed).
-/

@[expose] public section

namespace Crystallographic

theorem exists_orderOf_eq_iff_sl {N m : ℕ} (hN : 2 ≤ N) (hm : 0 < m) :
    (∃ A : Matrix.SpecialLinearGroup (Fin N) ℤ, orderOf A = m) ↔ psi m ≤ N := sorry

theorem orderOf_sl_one (A : Matrix.SpecialLinearGroup (Fin 1) ℤ) : orderOf A = 1 := sorry

end Crystallographic
