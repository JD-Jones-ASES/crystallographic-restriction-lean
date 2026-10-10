module

public import Crystallographic.Block

/-!
# The dimension `0` and monotonicity

`GL(0, ℤ)` is trivial, so its only finite order is `1`; an identity block pads an element of
`GL(N, ℤ)` to `GL(N', ℤ)` for `N ≤ N'`, so the finite orders grow with the dimension. Desk module.
-/

@[expose] public section

namespace Crystallographic

theorem finiteOrders_zero_internal : finiteOrders 0 = {1} := by
  ext m
  simp only [finiteOrders, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, A, hA⟩
    have hA1 : A = 1 := Units.ext (Matrix.ext fun i _ => Fin.elim0 i)
    rw [hA1, orderOf_one] at hA
    exact hA.symm
  · rintro rfl
    exact ⟨Nat.one_pos, 1, orderOf_one⟩

theorem finiteOrders_mono_internal {N N' : ℕ} (h : N ≤ N') :
    finiteOrders N ⊆ finiteOrders N' := by
  rintro m ⟨hm, A, hA⟩
  exact ⟨hm, exists_orderOf_eq_of_le h ⟨A, hA⟩⟩

end Crystallographic
