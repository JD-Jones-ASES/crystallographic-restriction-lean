module

public import Crystallographic.Necessity
public import Crystallographic.Sufficiency

/-!
# The restriction and its corollaries

The equivalence, the set of finite orders, the least dimension, the rational version (necessity is
`psi_orderOf_le_rat`; sufficiency maps the integer witness along
`Units.map (RingHom.mapMatrix (Int.castRingHom ℚ))`, injective, so `orderOf` is preserved), parity
(from `even_psi_internal`), the bound and finiteness (from `le_two_pow_psi_internal`).
Lane: **main**.
-/

@[expose] public section

namespace Crystallographic

theorem exists_orderOf_eq_iff_internal {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m) ↔ psi m ≤ N := sorry

theorem finiteOrders_eq_internal {N : ℕ} (hN : 0 < N) :
    finiteOrders N = {m | 0 < m ∧ psi m ≤ N} := sorry

theorem isLeast_dimension_internal {m : ℕ} (hm : 0 < m) :
    IsLeast {N | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m}
      (if m = 2 then 1 else psi m) := sorry

theorem exists_orderOf_eq_iff_rat_internal {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℚ, orderOf A = m) ↔ psi m ≤ N := sorry

theorem finiteOrders_succ_of_even_internal {N : ℕ} (hN : 0 < N) (hN2 : Even N) :
    finiteOrders (N + 1) = finiteOrders N := sorry

theorem le_two_pow_of_mem_finiteOrders_internal {N m : ℕ} (h : m ∈ finiteOrders N) :
    m ≤ 2 ^ (N + 1) := sorry

theorem finiteOrders_finite_internal (N : ℕ) : (finiteOrders N).Finite := sorry

end Crystallographic
