module

public import Crystallographic.Main

/-!
# Stretch: the restriction for `SL(N, ℤ)`

For `N ≥ 2`, `SL(N, ℤ)` has an element of order `m ≥ 1` iff `ψ m ≤ N`. Necessity: the inclusion
`SL → GL` (`Matrix.SpecialLinearGroup.toGL`) is an injective hom, so `orderOf` is preserved and
`psi_orderOf_le_internal` applies. Sufficiency: an element of odd order has determinant `1`
automatically (`det A ^ m = 1` with `det A = ±1`); for `2 ^ (j + 1)`, `j ≥ 1`, multiplication by
the root on `ℤ[X] / (X ^ (2 ^ j) + 1)` in the power basis has order `2 ^ (j + 1)` (its `2 ^ j`-th
power is `−1`) and determinant `(−1) ^ (2 ^ j) · 1 = 1` (`det_eq_sign_charpoly_coeff`,
`charpoly_leftMulMatrix`, and `minpoly ℤ root = X ^ (2 ^ j) + 1` by `minpoly.unique'`); block sums
multiply determinants (`Matrix.det_fromBlocks_zero₂₁`); `det (−A) = det A` in even dimension
(`Matrix.det_neg`), and `ψ m` is even; `−1` in dimension `2` has order `2` and determinant `1`.
`SL(1, ℤ)` is trivial. Lane: **sl** (stretch).
-/

@[expose] public section

namespace Crystallographic

/-- An integer matrix of determinant `1` and order `m` in dimension `n`. -/
def sl_good (n m : ℕ) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) ℤ, M.det = 1 ∧ orderOf M = m

/-- The inclusion of `SL` into the matrix monoid. -/
def sl_coeHom (n : ℕ) : Matrix.SpecialLinearGroup (Fin n) ℤ →* Matrix (Fin n) (Fin n) ℤ where
  toFun A := (A : Matrix (Fin n) (Fin n) ℤ)
  map_one' := Matrix.SpecialLinearGroup.coe_one
  map_mul' A B := Matrix.SpecialLinearGroup.coe_mul A B

theorem sl_coeHom_injective (n : ℕ) : Function.Injective (sl_coeHom n) :=
  fun _ _ h => Subtype.ext h

theorem sl_of_good {n m : ℕ} (h : sl_good n m) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) ℤ, orderOf A = m := by
  obtain ⟨M, hdet, hord⟩ := h
  refine ⟨⟨M, hdet⟩, ?_⟩
  have := orderOf_injective (sl_coeHom n) (sl_coeHom_injective n) ⟨M, hdet⟩
  rw [← this]
  exact hord

/-- Reindexing preserves the determinant and the order. -/
theorem sl_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℤ) :
    (Matrix.reindex e e M).det = M.det ∧ orderOf (Matrix.reindex e e M) = orderOf M := by
  refine ⟨Matrix.det_reindex_self e M, ?_⟩
  exact orderOf_injective (Matrix.reindexAlgEquiv ℤ ℤ e).toRingEquiv.toMonoidHom
    (Matrix.reindexAlgEquiv ℤ ℤ e).injective M

/-- The block-diagonal sum as a monoid hom. -/
def sl_blockHom (a b : ℕ) :
    Matrix (Fin a) (Fin a) ℤ × Matrix (Fin b) (Fin b) ℤ →*
      Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℤ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_one' := Matrix.fromBlocks_one
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]

theorem sl_blockHom_injective (a b : ℕ) : Function.Injective (sl_blockHom a b) := by
  intro p q h
  have h' : Matrix.fromBlocks p.1 0 0 p.2 = Matrix.fromBlocks q.1 0 0 q.2 := h
  rw [Matrix.fromBlocks_inj] at h'
  exact Prod.ext h'.1 h'.2.2.2

/-- Block sum in `SL`: coprime orders multiply, dimensions add. -/
theorem sl_good_mul {a b u v : ℕ} (huv : Nat.Coprime u v) (hA : sl_good a u)
    (hB : sl_good b v) : sl_good (a + b) (u * v) := by
  obtain ⟨A, hA1, hA2⟩ := hA
  obtain ⟨B, hB1, hB2⟩ := hB
  have h := sl_reindex finSumFinEquiv (Matrix.fromBlocks A 0 0 B)
  refine ⟨_, h.1.trans ?_, h.2.trans ?_⟩
  · rw [Matrix.det_fromBlocks_zero₂₁, hA1, hB1, one_mul]
  · have := orderOf_injective (sl_blockHom a b) (sl_blockHom_injective a b) (A, B)
    rw [show Matrix.fromBlocks A 0 0 B = sl_blockHom a b (A, B) from rfl, this, Prod.orderOf,
      hA2, hB2]
    exact huv.lcm_eq_mul

/-- Padding in `SL` by an identity block. -/
theorem sl_good_of_le {a N u : ℕ} (h : a ≤ N) (hA : sl_good a u) : sl_good N u := by
  have h1 : sl_good (N - a) 1 := ⟨1, Matrix.det_one, orderOf_one⟩
  have := sl_good_mul (Nat.coprime_one_right u) hA h1
  have e : a + (N - a) = N := by omega
  rw [mul_one, e] at this
  exact this

theorem sl_neg_one_ne_one {n : ℕ} (hn : 0 < n) : (-1 : Matrix (Fin n) (Fin n) ℤ) ≠ 1 := by
  intro h
  have := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.neg_apply, Matrix.one_apply_eq] at this
  omega

theorem sl_orderOf_neg_one {n : ℕ} (hn : 0 < n) :
    orderOf (-1 : Matrix (Fin n) (Fin n) ℤ) = 2 :=
  orderOf_eq_prime (by rw [neg_one_sq]) (sl_neg_one_ne_one hn)

/-- The sign in even positive dimension: `−A` has order `2 u` and determinant `1`. -/
theorem sl_good_two_mul {a u : ℕ} (ha : 0 < a) (hae : Even a) (hu : Odd u)
    (hA : sl_good a u) : sl_good a (2 * u) := by
  obtain ⟨A, h1, h2⟩ := hA
  refine ⟨-A, ?_, ?_⟩
  · rw [Matrix.det_neg, h1, Fintype.card_fin, hae.neg_one_pow, one_mul]
  · have hc : Nat.Coprime (orderOf (-1 : Matrix (Fin a) (Fin a) ℤ)) (orderOf A) := by
      rw [sl_orderOf_neg_one ha, h2]
      exact Nat.coprime_two_left.mpr hu
    rw [← neg_one_mul, (Commute.neg_one_left A).orderOf_mul_eq_mul_orderOf_of_coprime hc,
      sl_orderOf_neg_one ha, h2]

/-- An element of `GL` of odd order has determinant `1`. -/
theorem sl_good_of_gl_odd {a u : ℕ} (hu : Odd u) (A : Matrix.GeneralLinearGroup (Fin a) ℤ)
    (hA : orderOf A = u) : sl_good a u := by
  refine ⟨(A : Matrix (Fin a) (Fin a) ℤ), ?_, by rw [orderOf_units, hA]⟩
  have hunit : IsUnit (A : Matrix (Fin a) (Fin a) ℤ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
  have hpow : (A : Matrix (Fin a) (Fin a) ℤ).det ^ u = 1 := by
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, ← hA, pow_orderOf_eq_one, Units.val_one,
      Matrix.det_one]
  rcases Int.isUnit_iff.mp hunit with h | h
  · exact h
  · rw [h, hu.neg_one_pow] at hpow
    omega

open Polynomial in
/-- The `2 ^ (j + 1)` block of determinant `1`: multiplication by the root of `X ^ (2 ^ j) + 1`. -/
theorem sl_two_pow_block {j : ℕ} (hj : 1 ≤ j) :
    sl_good (2 ^ j) (2 ^ (j + 1)) := by
  have hd0 : 2 ^ j ≠ 0 := by positivity
  have hdeven : Even (2 ^ j) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hg : (X ^ (2 ^ j) + C (1 : ℤ)).Monic := monic_X_pow_add_C 1 hd0
  have hgdeg : (X ^ (2 ^ j) + C (1 : ℤ)).natDegree = 2 ^ j := natDegree_X_pow_add_C
  set g : ℤ[X] := X ^ (2 ^ j) + C 1 with hgdef
  let pb := AdjoinRoot.powerBasis' hg
  have hdim : pb.dim = 2 ^ j := hgdeg
  have hroot : (AdjoinRoot.root g) ^ (2 ^ j) = -1 := by
    have h0 : AdjoinRoot.mk g g = 0 := AdjoinRoot.mk_self
    rw [hgdef, map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hmin : minpoly ℤ (AdjoinRoot.root g) = g := by
    refine (minpoly.unique' ℤ (AdjoinRoot.root g) hg ?_ ?_).symm
    · rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    · intro q hq
      by_contra hcon
      push Not at hcon
      obtain ⟨hq0, hq1⟩ := hcon
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at hq1
      exact absurd (degree_le_of_dvd hq1 hq0) (not_le.mpr hq)
  let x := Algebra.leftMulMatrix pb.basis (AdjoinRoot.root g)
  have hpos : 0 < pb.dim := by rw [hdim]; positivity
  have hdet : x.det = 1 := by
    rw [Matrix.det_eq_sign_charpoly_coeff]
    have hc := charpoly_leftMulMatrix pb
    rw [AdjoinRoot.powerBasis'_gen] at hc
    rw [hc, hmin, Fintype.card_fin, hdim, hdeven.neg_one_pow, one_mul, hgdef, coeff_add,
      coeff_C_zero, coeff_X_pow, ite_eq_right (by omega), zero_add]
  have hx1 : x ^ (2 ^ j) = -1 := by
    rw [← map_pow, hroot, map_neg, map_one]
  have hord : orderOf x = 2 ^ (j + 1) := by
    apply orderOf_eq_prime_pow
    · rw [hx1]; exact sl_neg_one_ne_one hpos
    · rw [pow_succ, pow_mul, hx1, neg_one_sq]
  have key : ∀ n : ℕ, n = 2 ^ j → sl_good n (2 ^ (j + 1)) →
      sl_good (2 ^ j) (2 ^ (j + 1)) := by
    rintro n rfl h
    exact h
  exact key pb.dim hdim ⟨x, hdet, hord⟩

/-- Sufficiency in `SL`, `N ≥ 2`. -/
theorem sl_suff {N m : ℕ} (hN : 2 ≤ N) (hm : 0 < m) (h : psi m ≤ N) : sl_good N m := by
  obtain ⟨k, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  have hu0 : 0 < u := hu.pos
  have hu2 : u ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hu) even_two
  have hcop : Nat.Coprime (2 ^ k) u := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hu)
  obtain ⟨A, hA⟩ := exists_orderOf_eq_psi hu0 hu2
  have hgu : sl_good (psi u) u := sl_good_of_gl_odd hu A hA
  have hpsi : psi (2 ^ k * u) = psi (2 ^ k) + psi u := psi_mul_internal hcop
  rcases k with _ | _ | j
  · rw [pow_zero, one_mul] at h ⊢
    exact sl_good_of_le h hgu
  · rw [zero_add, pow_one] at h hpsi ⊢
    rw [psi_two, zero_add] at hpsi
    by_cases hu1 : u = 1
    · subst hu1
      exact sl_good_of_le hN
        (sl_good_two_mul (by norm_num) even_two odd_one ⟨1, Matrix.det_one, orderOf_one⟩)
    · have hpos : 0 < psi u := by
        refine Nat.pos_of_ne_zero (fun h0 => ?_)
        have := (psi_eq_zero_iff_internal u).mp h0
        omega
      rw [hpsi] at h
      exact sl_good_of_le h (sl_good_two_mul hpos (even_psi_internal u) hu hgu)
  · have h4 : 4 ≤ 2 ^ (j + 1 + 1) := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2k : psi (2 ^ (j + 1 + 1)) = 2 ^ (j + 1) := by
      rw [psi_prime_pow_internal Nat.prime_two (by omega) (by omega),
        Nat.totient_prime_pow_succ Nat.prime_two, Nat.add_one_sub_one, mul_one]
    rw [hpsi, h2k] at h
    exact sl_good_of_le h (sl_good_mul hcop (sl_two_pow_block (j := j + 1) (by omega)) hgu)

theorem exists_orderOf_eq_iff_sl {N m : ℕ} (hN : 2 ≤ N) (hm : 0 < m) :
    (∃ A : Matrix.SpecialLinearGroup (Fin N) ℤ, orderOf A = m) ↔ psi m ≤ N := by
  constructor
  · rintro ⟨A, rfl⟩
    have := psi_orderOf_le_internal (Matrix.SpecialLinearGroup.toGL A)
    rwa [orderOf_injective _ Matrix.SpecialLinearGroup.toGL_injective A] at this
  · intro h
    exact sl_of_good (sl_suff hN hm h)

theorem orderOf_sl_one (A : Matrix.SpecialLinearGroup (Fin 1) ℤ) : orderOf A = 1 := by
  have hA : A = 1 := by
    ext i j
    have hdet : (A : Matrix (Fin 1) (Fin 1) ℤ).det = 1 := A.prop
    rw [Matrix.det_unique] at hdet
    fin_cases i
    fin_cases j
    simpa using hdet
  rw [hA, orderOf_one]

end Crystallographic
