module

public import Crystallographic.Defs

/-!
# The building blocks of the construction

* The cyclotomic block: for `n ≥ 1`, multiplication by `root (cyclotomic n ℤ)` on
  `AdjoinRoot (cyclotomic n ℤ)` is a `ℤ`-linear automorphism of a free module of rank `φ n`
  (`AdjoinRoot.powerBasis'` with `cyclotomic.monic`, `natDegree_cyclotomic`); its matrix in the
  power basis (`Algebra.leftMulMatrix pb.basis`, injective by `Algebra.leftMulMatrix_injective`) is
  an element of `GL (Fin (φ n)) ℤ` of order `n`: `root ^ n = 1` as `Φₙ ∣ X ^ n − 1`, and
  `n ∣ orderOf root` because `AdjoinRoot.lift` sends the root to the primitive root `exp (2πi/n)`
  of `ℂ` (`Complex.isPrimitiveRoot_exp`, `IsPrimitiveRoot.isRoot_cyclotomic`, `orderOf_map_dvd`);
  `orderOf_injective` carries the order to the matrix.
* Block sums: the injective monoid homs `P ↦ fromBlocks P 0 0 1` and `Q ↦ fromBlocks 1 0 0 Q`
  (`blk_inl`, `blk_inr`) have commuting images, so coprime orders multiply
  (`Commute.orderOf_mul_eq_mul_orderOf_of_coprime`); the result is reindexed along `finSumFinEquiv`.
* Padding by an identity block, and the sign: `−A` has order `2u` when `A` has odd order `u` in a
  positive dimension (`orderOf_neg_one`, the two commute, `Nat.Coprime 2 u`).
-/

@[expose] public section

namespace Crystallographic

open Matrix Polynomial

/-- Transport along an injective monoid hom of matrix rings. -/
theorem blk_transfer {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : Matrix ι ι ℤ →* Matrix κ κ ℤ) (hf : Function.Injective f) (A : GL ι ℤ) :
    orderOf (Units.map f A) = orderOf A := by
  rw [← orderOf_units, Units.coe_map, ← orderOf_units]
  exact orderOf_injective f hf _

/-- Equal dimensions. -/
theorem blk_cast {d e n : ℕ} (h : d = e) (hA : ∃ A : GL (Fin d) ℤ, orderOf A = n) :
    ∃ A : GL (Fin e) ℤ, orderOf A = n := by
  subst h; exact hA

/-- Reindexing along an equivalence. -/
theorem blk_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) {n : ℕ} (hA : ∃ A : GL ι ℤ, orderOf A = n) :
    ∃ A : GL κ ℤ, orderOf A = n := by
  obtain ⟨A, hA⟩ := hA
  refine ⟨Units.map (Matrix.reindexAlgEquiv ℤ ℤ e).toRingEquiv.toRingHom.toMonoidHom A, ?_⟩
  rw [blk_transfer _ (Matrix.reindexAlgEquiv ℤ ℤ e).injective, hA]

/-- The upper-left block embedding. -/
def blk_inl (a b : ℕ) : Matrix (Fin a) (Fin a) ℤ →* Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℤ where
  toFun P := Matrix.fromBlocks P 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' P Q := by simp [Matrix.fromBlocks_multiply]

/-- The lower-right block embedding. -/
def blk_inr (a b : ℕ) : Matrix (Fin b) (Fin b) ℤ →* Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℤ where
  toFun P := Matrix.fromBlocks 1 0 0 P
  map_one' := Matrix.fromBlocks_one
  map_mul' P Q := by simp [Matrix.fromBlocks_multiply]

theorem blk_inl_injective (a b : ℕ) : Function.Injective (blk_inl a b) := by
  intro P Q h
  exact (Matrix.fromBlocks_inj.mp h).1

theorem blk_inr_injective (a b : ℕ) : Function.Injective (blk_inr a b) := by
  intro P Q h
  exact (Matrix.fromBlocks_inj.mp h).2.2.2

theorem blk_commute (a b : ℕ) (P : Matrix (Fin a) (Fin a) ℤ) (Q : Matrix (Fin b) (Fin b) ℤ) :
    Commute (blk_inl a b P) (blk_inr a b Q) := by
  show Matrix.fromBlocks P 0 0 1 * Matrix.fromBlocks 1 0 0 Q =
    Matrix.fromBlocks 1 0 0 Q * Matrix.fromBlocks P 0 0 1
  simp [Matrix.fromBlocks_multiply]

/-- The cyclotomic block: an element of `GL (φ n, ℤ)` of order `n`, for every `n ≥ 1`. -/
theorem exists_orderOf_eq_totient_internal {n : ℕ} (hn : 0 < n) :
    ∃ A : Matrix.GeneralLinearGroup (Fin (Nat.totient n)) ℤ, orderOf A = n := by
  set g : ℤ[X] := cyclotomic n ℤ with hg_def
  have hmon : g.Monic := cyclotomic.monic n ℤ
  set pb := AdjoinRoot.powerBasis' hmon with hpb
  have hdim : pb.dim = Nat.totient n := by
    rw [AdjoinRoot.powerBasis'_dim]; exact natDegree_cyclotomic n ℤ
  refine blk_cast hdim ?_
  -- the root has order `n`
  set r : AdjoinRoot g := AdjoinRoot.root g with hr
  have hrn : r ^ n = 1 := by
    have h0 : AdjoinRoot.mk g (X ^ n - 1) = 0 :=
      AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one n ℤ)
    rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h0
    exact h0
  have hord : orderOf r = n := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hrn)
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
    have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
    have hev : g.eval₂ (Int.castRingHom ℂ) ζ = 0 := by
      rw [eval₂_eq_eval_map, hg_def, map_cyclotomic_int]
      exact hζ.isRoot_cyclotomic hn
    let L : AdjoinRoot g →+* ℂ := AdjoinRoot.lift (Int.castRingHom ℂ) ζ hev
    have hL : L r = ζ := AdjoinRoot.lift_root hev
    have := orderOf_map_dvd L.toMonoidHom r
    rw [show L.toMonoidHom r = ζ from hL, ← hζ.eq_orderOf] at this
    exact this
  -- the regular representation
  let Φ := Algebra.leftMulMatrix pb.basis
  have hΦ : Function.Injective Φ := Algebra.leftMulMatrix_injective pb.basis
  have hMn : (Φ r) ^ n = 1 := by rw [← map_pow, hrn, map_one]
  have hU : IsUnit (Φ r) := IsUnit.of_pow_eq_one hMn hn.ne'
  refine ⟨hU.unit, ?_⟩
  rw [← orderOf_units, IsUnit.unit_spec, ← hord]
  exact orderOf_injective Φ.toRingHom.toMonoidHom hΦ r

/-- Block sum: elements of coprime orders `u`, `v` in dimensions `a`, `b` give an element of order
`u * v` in dimension `a + b`. -/
theorem exists_orderOf_eq_mul {a b u v : ℕ} (huv : Nat.Coprime u v)
    (hA : ∃ A : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf A = u)
    (hB : ∃ B : Matrix.GeneralLinearGroup (Fin b) ℤ, orderOf B = v) :
    ∃ C : Matrix.GeneralLinearGroup (Fin (a + b)) ℤ, orderOf C = u * v := by
  obtain ⟨A, rfl⟩ := hA
  obtain ⟨B, rfl⟩ := hB
  refine blk_reindex finSumFinEquiv ⟨Units.map (blk_inl a b) A * Units.map (blk_inr a b) B, ?_⟩
  have hc : Commute (Units.map (blk_inl a b) A) (Units.map (blk_inr a b) B) := by
    apply Units.ext
    exact blk_commute a b A B
  rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime, blk_transfer _ (blk_inl_injective a b),
    blk_transfer _ (blk_inr_injective a b)]
  rwa [blk_transfer _ (blk_inl_injective a b), blk_transfer _ (blk_inr_injective a b)]

/-- Padding: an element of order `u` in dimension `a ≤ N` gives one in dimension `N`. -/
theorem exists_orderOf_eq_of_le {a N u : ℕ} (h : a ≤ N)
    (hA : ∃ A : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf A = u) :
    ∃ C : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf C = u := by
  have := exists_orderOf_eq_mul (b := N - a) (Nat.coprime_one_right u) hA ⟨1, orderOf_one⟩
  rw [mul_one] at this
  exact blk_cast (Nat.add_sub_cancel' h) this

/-- `−1` has order `2` in every positive dimension. -/
theorem orderOf_neg_one_gl {N : ℕ} (hN : 0 < N) :
    orderOf (-1 : Matrix.GeneralLinearGroup (Fin N) ℤ) = 2 := by
  apply orderOf_eq_prime
  · simp
  · intro h
    have h1 := congrArg (fun A : Matrix.GeneralLinearGroup (Fin N) ℤ => (A : Matrix (Fin N) (Fin N) ℤ)
      ⟨0, hN⟩ ⟨0, hN⟩) h
    simp at h1

/-- The sign: in a positive dimension, `−A` has order `2 * u` when `A` has odd order `u`. -/
theorem exists_orderOf_eq_two_mul {a u : ℕ} (ha : 0 < a) (hu : Odd u)
    (hA : ∃ A : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf A = u) :
    ∃ C : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf C = 2 * u := by
  obtain ⟨A, rfl⟩ := hA
  refine ⟨-1 * A, ?_⟩
  rw [(Commute.neg_one_left A).orderOf_mul_eq_mul_orderOf_of_coprime, orderOf_neg_one_gl ha]
  rw [orderOf_neg_one_gl ha]
  exact Nat.coprime_two_left.mpr hu

end Crystallographic
