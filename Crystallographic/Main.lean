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
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m) ↔ psi m ≤ N :=
  ⟨fun ⟨A, hA⟩ => hA ▸ psi_orderOf_le_internal A, exists_orderOf_eq_internal hN hm⟩

theorem finiteOrders_eq_internal {N : ℕ} (hN : 0 < N) :
    finiteOrders N = {m | 0 < m ∧ psi m ≤ N} := by
  ext m
  simp only [finiteOrders, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hm, h⟩
    exact ⟨hm, (exists_orderOf_eq_iff_internal hN hm).1 h⟩
  · rintro ⟨hm, h⟩
    exact ⟨hm, (exists_orderOf_eq_iff_internal hN hm).2 h⟩

theorem isLeast_dimension_internal {m : ℕ} (hm : 0 < m) :
    IsLeast {N | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m}
      (if m = 2 then 1 else psi m) := by
  constructor
  · by_cases h2 : m = 2
    · subst h2
      simp only [ite_true, Set.mem_ofPred_eq]
      exact ⟨-1, orderOf_neg_one_gl Nat.one_pos⟩
    · simp only [h2, ite_false, Set.mem_ofPred_eq]
      exact exists_orderOf_eq_psi hm h2
  · rintro N ⟨A, hA⟩
    have hle : psi m ≤ N := hA ▸ psi_orderOf_le_internal A
    by_cases h2 : m = 2
    · subst h2
      simp only [ite_true]
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0
        exfalso
        have h1 : A = 1 := Subsingleton.elim _ _
        rw [h1, orderOf_one] at hA
        exact absurd hA (by decide)
      · exact h0
    · simp only [h2, ite_false]
      exact hle

theorem exists_orderOf_eq_iff_rat_internal {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℚ, orderOf A = m) ↔ psi m ≤ N := by
  constructor
  · rintro ⟨A, hA⟩
    exact hA ▸ psi_orderOf_le_rat A
  · intro h
    obtain ⟨A, hA⟩ := exists_orderOf_eq_internal hN hm h
    let φ : Matrix.GeneralLinearGroup (Fin N) ℤ →* Matrix.GeneralLinearGroup (Fin N) ℚ :=
      Units.map ((Int.castRingHom ℚ).mapMatrix : Matrix (Fin N) (Fin N) ℤ →+* _).toMonoidHom
    have hφ : Function.Injective φ := by
      apply Units.map_injective
      intro X Y hXY
      exact Matrix.map_injective Int.cast_injective hXY
    exact ⟨φ A, by rw [orderOf_injective φ hφ A, hA]⟩

theorem finiteOrders_succ_of_even_internal {N : ℕ} (hN : 0 < N) (hN2 : Even N) :
    finiteOrders (N + 1) = finiteOrders N := by
  rw [finiteOrders_eq_internal hN, finiteOrders_eq_internal (Nat.succ_pos N)]
  ext m
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    obtain ⟨a, ha⟩ := even_psi_internal m
    obtain ⟨b, hb⟩ := hN2
    omega
  · rintro ⟨hm, h⟩
    exact ⟨hm, Nat.le_succ_of_le h⟩

theorem le_two_pow_of_mem_finiteOrders_internal {N m : ℕ} (h : m ∈ finiteOrders N) :
    m ≤ 2 ^ (N + 1) := by
  obtain ⟨hm, A, hA⟩ := h
  have hle : psi m ≤ N := hA ▸ psi_orderOf_le_internal A
  exact (le_two_pow_psi_internal hm).trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem finiteOrders_finite_internal (N : ℕ) : (finiteOrders N).Finite :=
  (Set.finite_Iic (2 ^ (N + 1))).subset fun _ hm => le_two_pow_of_mem_finiteOrders_internal hm

end Crystallographic
