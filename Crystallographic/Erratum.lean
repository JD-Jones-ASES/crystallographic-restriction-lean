module

public import Crystallographic.Main
public import Crystallographic.Compute

/-!
# Beyond dimension 12: the values missing from Table 1 of Bamberg–Cairns–Kilminster

`ψ(2520) = 20`, `ψ(2310) = 22`, and `ψ = 24` at `2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620,
5040`; by `isLeast_dimension_internal` these are the least dimensions carrying an element of that
order. Each value of `ψ` is a kernel computation of `psiC`.
-/

@[expose] public section

namespace Crystallographic

theorem psi_2520_internal : psi 2520 = 20 := by
  rw [← psiC_eq_psi]; decide +kernel

theorem psi_2310_internal : psi 2310 = 22 := by
  rw [← psiC_eq_psi]; decide +kernel

theorem psi_eq_twentyfour_internal :
    ∀ m ∈ ({2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620, 5040} : Finset ℕ), psi m = 24 := by
  intro m hm
  rw [← psiC_eq_psi]
  revert m
  decide +kernel

theorem isLeast_dimension_2520_internal :
    IsLeast {N | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = 2520} 20 := by
  have h := isLeast_dimension_internal (m := 2520) (by norm_num)
  rwa [ite_eq_right (by norm_num), psi_2520_internal] at h

theorem isLeast_dimension_2310_internal :
    IsLeast {N | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = 2310} 22 := by
  have h := isLeast_dimension_internal (m := 2310) (by norm_num)
  rwa [ite_eq_right (by norm_num), psi_2310_internal] at h

theorem isLeast_dimension_twentyfour_internal :
    ∀ m ∈ ({2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620, 5040} : Finset ℕ),
      IsLeast {N | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m} 24 := by
  intro m hm
  have hm0 : 0 < m := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  have hm2 : m ≠ 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  have h := isLeast_dimension_internal hm0
  rwa [ite_eq_right hm2, psi_eq_twentyfour_internal m hm] at h

end Crystallographic
