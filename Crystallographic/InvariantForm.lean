module

public import Crystallographic.Main

/-!
# Integral positive definite forms preserved by finite-order matrices

For a matrix `A` with `A ^ m = 1`, the finite Gram sum

`invariantGram A m = ∑ k < m, (A ^ k)ᵀ * A ^ k`

is symmetric and satisfies `Aᵀ * invariantGram A m * A = invariantGram A m`.
For `m > 0` it is positive definite: its `k = 0` summand is the identity,
and every other summand is positive semidefinite. If `A` is integral then
the sum is integral; its positive definiteness is also proved after casting
to `ℝ`. So `ψ(m) ≤ N` is also the condition for an element of order `m` of
`GL(N, ℤ)` preserving a positive definite integral form.

This is the sum of the transforms of the identity form over the group generated
by `A`, as in Serre, *Bounds for the orders of the finite subgroups of G(k)*,
§1.3.2, for finite subgroups of `GL(n, ℚ)` (where an integer then clears the
denominators); for `A ∈ GL(N, ℤ)` the sum is already integral. Its unimodularity
is not asserted.
-/

@[expose] public section

namespace Crystallographic

open Matrix

/-- The sum of the Gram matrices of the first `m` powers of `A`. -/
def invariantGram {R : Type*} [CommRing R] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (m : ℕ) : Matrix (Fin N) (Fin N) R :=
  ∑ k ∈ Finset.range m, (A ^ k)ᵀ * A ^ k

/-- The finite Gram sum is symmetric over any commutative ring. -/
theorem invariantGram_isSymm {R : Type*} [CommRing R] {N m : ℕ}
    (A : Matrix (Fin N) (Fin N) R) : (invariantGram A m).IsSymm := by
  show (invariantGram A m)ᵀ = invariantGram A m
  simp only [invariantGram, Matrix.transpose_sum, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- A period of `A` makes the finite Gram sum invariant under `A`. -/
theorem invariantGram_invariant {R : Type*} [CommRing R] {N m : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (hA : A ^ m = 1) :
    Aᵀ * invariantGram A m * A = invariantGram A m := by
  have hstep (k : ℕ) : Aᵀ * ((A ^ k)ᵀ * A ^ k) * A =
      (A ^ (k + 1))ᵀ * A ^ (k + 1) := by
    rw [pow_succ, Matrix.transpose_mul]
    simp only [mul_assoc]
  unfold invariantGram
  rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [hstep]
  have hshift := Finset.sum_range_succ' (fun k => (A ^ k)ᵀ * A ^ k) m
  rw [Finset.sum_range_succ, hA, pow_zero, Matrix.transpose_one, one_mul] at hshift
  exact add_right_cancel hshift.symm

/-- The construction commutes with every coefficient-ring homomorphism. -/
theorem invariantGram_map {R S : Type*} [CommRing R] [CommRing S] {N m : ℕ}
    (f : R →+* S) (A : Matrix (Fin N) (Fin N) R) :
    f.mapMatrix (invariantGram A m) = invariantGram (f.mapMatrix A) m := by
  unfold invariantGram
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow]
  have ht : f.mapMatrix ((A ^ k)ᵀ) = (f.mapMatrix (A ^ k))ᵀ := rfl
  rw [ht, map_pow]

/-- The identity summand makes the Gram sum positive definite for `m > 0`.
The star is trivial, as it is on `ℤ`, `ℚ` and `ℝ`. -/
theorem invariantGram_posDef {R : Type*} [CommRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] [TrivialStar R] [NoZeroDivisors R] [AddLeftMono R]
    {N m : ℕ} (A : Matrix (Fin N) (Fin N) R) (hm : 0 < m) :
    (invariantGram A m).PosDef := by
  have hpos : ∀ n : ℕ, (invariantGram A (n + 1)).PosDef := by
    intro n
    induction n with
    | zero => simpa [invariantGram] using (Matrix.PosDef.one (n := Fin N) (R := R))
    | succ n ih =>
      rw [invariantGram, Finset.sum_range_succ]
      apply ih.add_posSemidef
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_conjTranspose_mul_self (A ^ (n + 1))
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact hpos n

/-- An integral Gram sum is positive definite on real vectors, not only on
integer vectors. -/
theorem invariantGram_posDef_real {N m : ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ) (hm : 0 < m) :
    ((Int.castRingHom ℝ).mapMatrix (invariantGram A m)).PosDef := by
  rw [invariantGram_map]
  exact invariantGram_posDef _ hm

/-- Every finite-order integral matrix preserves an explicitly constructed
integral symmetric form that is positive definite also over `ℝ`. -/
theorem exists_integral_invariant_posDef_internal {N m : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin N) ℤ) (hm : 0 < m) (hA : orderOf A = m) :
    ∃ Q : Matrix (Fin N) (Fin N) ℤ,
      Q.IsSymm ∧ Q.PosDef ∧ ((Int.castRingHom ℝ).mapMatrix Q).PosDef ∧
        (A : Matrix (Fin N) (Fin N) ℤ)ᵀ * Q *
          (A : Matrix (Fin N) (Fin N) ℤ) = Q := by
  refine ⟨invariantGram (A : Matrix (Fin N) (Fin N) ℤ) m,
    invariantGram_isSymm _, invariantGram_posDef _ hm, invariantGram_posDef_real _ hm, ?_⟩
  apply invariantGram_invariant
  have hpow : A ^ m = 1 := hA ▸ pow_orderOf_eq_one A
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hpow

/-- The same order criterion is realized by isometries of positive definite
integral lattices: the matrix and a preserved integral Gram matrix both exist. -/
theorem exists_integral_posDef_isometry_iff_internal {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ,
      ∃ Q : Matrix (Fin N) (Fin N) ℤ,
        orderOf A = m ∧ Q.IsSymm ∧ Q.PosDef ∧
          ((Int.castRingHom ℝ).mapMatrix Q).PosDef ∧
          (A : Matrix (Fin N) (Fin N) ℤ)ᵀ * Q *
            (A : Matrix (Fin N) (Fin N) ℤ) = Q) ↔ psi m ≤ N := by
  constructor
  · rintro ⟨A, Q, hA, -⟩
    exact hA ▸ psi_orderOf_le_internal A
  · intro h
    obtain ⟨A, hA⟩ := exists_orderOf_eq_internal hN hm h
    obtain ⟨Q, hQ⟩ := exists_integral_invariant_posDef_internal A hm hA
    exact ⟨A, Q, hA, hQ⟩

end Crystallographic
