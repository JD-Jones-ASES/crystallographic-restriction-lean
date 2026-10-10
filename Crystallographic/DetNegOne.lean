module

public import Crystallographic.SL
public import Crystallographic.InvariantForm

/-!
# Determinant `−1`

For `m ≥ 1`, `GL(N, ℤ)` has an element of order `m` and determinant `−1` iff `m` is even and
`ψ m + 1 ≤ N`; so the least dimension of such an element is `ψ m + 1` for even `m`.

* The `ψ`-cover: if every exact prime power of `m` divides a member of `S` (`0 ∉ S`), then
  `ψ m ≤ ∑_{d ∈ S} ψ d` (the proof of `psi_le_sum_totient_of_zero_notMem` stopped one step early).
* Sufficiency: `[−1]` for `m = 2`; for even `m > 2`, `ψ m ≥ 2` and `sl_suff` gives `B` of order `m`
  and determinant `1` in dimension `ψ m`; the block sum of `[−1]` and `B` has determinant `−1` and
  order `lcm 2 m = m` (`Prod.orderOf`, `Matrix.det_fromBlocks_zero₂₁`); identity blocks pad.
* Necessity, over `ℚ`: `det M ^ m = 1` makes `m` even. The Gram sum `Q = invariantGram M m` is
  positive definite, so `det Q ≠ 0`, and `Mᵀ Q M = Q` gives `Mᵀ Q (M + 1) = (M + 1)ᵀ Q`, whence
  `det M · det (M + 1) = det (M + 1)` and `det (M + 1) = 0`. If `Φ₂ = X + 1` did not divide the
  minimal polynomial `f`, a Bézout identity `a Φ₂ + b f = 1` evaluated at `M` would invert `M + 1`;
  so `2` lies in the set `S` of indices `d ∣ m` with `Φ_d ∣ f`. With the facts of `Necessity.lean`
  about `S` (`∑_{d ∈ S} φ d ≤ N` and the cover), `ψ m ≤ ∑_{d ∈ S} ψ d ≤ ∑_{d ∈ S} φ d − 1 ≤ N − 1`,
  the `−1` coming from `ψ 2 = 0 < 1 = φ 2`.
-/

@[expose] public section

namespace Crystallographic

open Matrix Polynomial

/-! ## The `ψ`-cover -/

/-- The covering inequality with `ψ` on the right: if every prime power `p ^ v_p(m)` exactly
dividing `m` divides some member of `S`, and `0 ∉ S`, then `ψ m ≤ ∑_{d ∈ S} ψ d`. -/
theorem dn_psi_le_sum_psi {m : ℕ} {S : Finset ℕ} (hS : 0 ∉ S)
    (hcover : ∀ p ∈ m.primeFactors, ∃ d ∈ S, p ^ m.factorization p ∣ d) :
    psi m ≤ ∑ d ∈ S, psi d := by
  choose! c hcS hcd using hcover
  rw [psi_eq_sum_term, ← Finset.sum_fiberwise_of_maps_to hcS]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd0 : d ≠ 0 := fun h => hS (h ▸ hd)
  calc ∑ p ∈ m.primeFactors with c p = d, psi_term m p
      ≤ ∑ p ∈ m.primeFactors with c p = d, psi_term d p := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpm, hpd⟩ := Finset.mem_filter.mp hp
        have hpr := Nat.prime_of_mem_primeFactors hpm
        have hk := psi_factorization_pos hpm
        have hdv : p ^ m.factorization p ∣ d := hpd ▸ hcd p hpm
        exact psi_term_mono hpr hk ((hpr.pow_dvd_iff_le_factorization hd0).mp hdv)
    _ ≤ ∑ p ∈ d.primeFactors, psi_term d p := by
        apply Finset.sum_le_sum_of_subset
        intro p hp
        obtain ⟨hpm, hpd⟩ := Finset.mem_filter.mp hp
        have hpr := Nat.prime_of_mem_primeFactors hpm
        have hk := psi_factorization_pos hpm
        have hdv : p ^ m.factorization p ∣ d := hpd ▸ hcd p hpm
        exact Nat.mem_primeFactors.mpr ⟨hpr, dvd_trans (dvd_pow_self p hk.ne') hdv, hd0⟩
    _ = psi d := rfl

/-! ## Sufficiency -/

/-- An integer matrix of determinant `−1` and order `m` in dimension `n`. -/
def dn_good (n m : ℕ) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) ℤ, M.det = -1 ∧ orderOf M = m

/-- Block sum of integer matrices: dimensions add, determinants multiply, orders take the lcm. -/
theorem dn_block {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) :
    ∃ C : Matrix (Fin (a + b)) (Fin (a + b)) ℤ,
      C.det = A.det * B.det ∧ orderOf C = Nat.lcm (orderOf A) (orderOf B) := by
  have h := sl_reindex finSumFinEquiv (Matrix.fromBlocks A 0 0 B)
  refine ⟨_, h.1.trans ?_, h.2.trans ?_⟩
  · exact Matrix.det_fromBlocks_zero₂₁ A 0 B
  · have := orderOf_injective (sl_blockHom a b) (sl_blockHom_injective a b) (A, B)
    rw [show Matrix.fromBlocks A 0 0 B = sl_blockHom a b (A, B) from rfl, this, Prod.orderOf]

/-- Padding by an identity block keeps the determinant and the order. -/
theorem dn_good_of_le {a N u : ℕ} (h : a ≤ N) (hA : dn_good a u) : dn_good N u := by
  obtain ⟨A, hA1, hA2⟩ := hA
  obtain ⟨C, hC1, hC2⟩ := dn_block A (1 : Matrix (Fin (N - a)) (Fin (N - a)) ℤ)
  have key : ∀ n : ℕ, n = N → dn_good n u → dn_good N u := by
    rintro n rfl h
    exact h
  refine key _ (by omega) ⟨C, ?_, ?_⟩
  · rw [hC1, hA1, Matrix.det_one, mul_one]
  · rw [hC2, hA2, orderOf_one, Nat.lcm_one_right]

theorem dn_det_neg_one_fin_one : (-1 : Matrix (Fin 1) (Fin 1) ℤ).det = -1 := by
  simp

/-- `[−1]`: order `2`, determinant `−1`, dimension `1`. -/
theorem dn_good_one_two : dn_good 1 2 :=
  ⟨-1, dn_det_neg_one_fin_one, sl_orderOf_neg_one Nat.one_pos⟩

/-- Sufficiency as matrices. -/
theorem dn_good_suff {N m : ℕ} (hme : Even m) (hm : 0 < m) (h : psi m + 1 ≤ N) :
    dn_good N m := by
  by_cases h2 : m = 2
  · subst h2
    exact dn_good_of_le (by omega) dn_good_one_two
  · have hm3 : 2 < m := by
      obtain ⟨k, hk⟩ := hme
      omega
    have hpos : psi m ≠ 0 := fun h0 => by
      have := (psi_eq_zero_iff_internal m).mp h0
      omega
    have hp2 : 2 ≤ psi m := by
      obtain ⟨k, hk⟩ := even_psi_internal m
      omega
    obtain ⟨B, hB1, hB2⟩ := sl_suff hp2 hm (le_refl _)
    obtain ⟨C, hC1, hC2⟩ := dn_block (-1 : Matrix (Fin 1) (Fin 1) ℤ) B
    refine dn_good_of_le (a := 1 + psi m) (by omega) ⟨C, ?_, ?_⟩
    · rw [hC1, hB1, mul_one, dn_det_neg_one_fin_one]
    · rw [hC2, sl_orderOf_neg_one Nat.one_pos, hB2]
      exact Nat.lcm_eq_right (even_iff_two_dvd.mp hme)

/-- From a matrix to a unit, keeping the order and the determinant. -/
theorem dn_gl_of_good {N m : ℕ} (h : dn_good N m) :
    ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ,
      orderOf A = m ∧ (A : Matrix (Fin N) (Fin N) ℤ).det = -1 := by
  obtain ⟨M, hdet, hord⟩ := h
  have hU : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).mpr (by rw [hdet]; exact Int.isUnit_iff.mpr (Or.inr rfl))
  refine ⟨hU.unit, ?_, ?_⟩
  · rw [← orderOf_units, IsUnit.unit_spec, hord]
  · rw [IsUnit.unit_spec, hdet]

/-- Sufficiency: for even `m ≥ 1` and `ψ m + 1 ≤ N`, an element of `GL(N, ℤ)` of order `m` and
determinant `−1`. -/
theorem exists_orderOf_eq_det_neg_one_internal {N m : ℕ} (hme : Even m) (hm : 0 < m)
    (h : psi m + 1 ≤ N) :
    ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ,
      orderOf A = m ∧ (A : Matrix (Fin N) (Fin N) ℤ).det = -1 :=
  dn_gl_of_good (dn_good_suff hme hm h)

/-! ## Necessity -/

/-- A rational matrix of finite order and determinant `−1` has `det (M + 1) = 0`: the invariant
positive definite Gram sum `Q` gives `Mᵀ Q (M + 1) = (M + 1)ᵀ Q`. -/
theorem dn_det_add_one_eq_zero {N m : ℕ} (M : Matrix (Fin N) (Fin N) ℚ) (hm : 0 < m)
    (hpow : M ^ m = 1) (hdet : M.det = -1) : (M + 1).det = 0 := by
  set Q := invariantGram M m with hQ
  have hQpd : Q.PosDef := invariantGram_posDef M hm
  have hQdet : Q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Q).mp hQpd.isUnit).ne_zero
  have hinv : Mᵀ * Q * M = Q := invariantGram_invariant M hpow
  have key : Mᵀ * Q * (M + 1) = (M + 1)ᵀ * Q := by
    rw [mul_add, hinv, mul_one, Matrix.transpose_add, Matrix.transpose_one, add_mul, one_mul]
    exact add_comm _ _
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_transpose, hdet] at hd
  have hz : Q.det * (M + 1).det = 0 := by linear_combination (-1 / 2 : ℚ) * hd
  exact (mul_eq_zero.mp hz).resolve_left hQdet

/-- If `det (M + 1) = 0` then `Φ₂ = X + 1` divides the minimal polynomial of `M`. -/
theorem dn_cyclotomic_two_dvd {N : ℕ} (M : Matrix (Fin N) (Fin N) ℚ) (h : (M + 1).det = 0) :
    cyclotomic 2 ℚ ∣ minpoly ℚ M := by
  by_contra hnd
  have hcop : IsCoprime (cyclotomic 2 ℚ) (minpoly ℚ M) :=
    ((cyclotomic.irreducible_rat (by norm_num : 0 < 2)).coprime_iff_not_dvd).mpr hnd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 := congrArg (aeval M) hab
  simp only [map_add, map_mul, minpoly.aeval, mul_zero, add_zero, map_one, cyclotomic_two,
    aeval_X] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h2
  exact zero_ne_one h2

/-- From the proof of `psi_orderOf_le_rat` in `Necessity.lean`, which keeps these facts internal
(duplicated here): for a rational matrix of order `m > 0` with minimal polynomial `f`, the set `S`
of divisors `d ∣ m` with `Φ_d ∣ f` has `∑_{d ∈ S} φ d ≤ N`, and every exact prime power of `m`
divides a member of `S`. -/
theorem aux_nec_S {N m : ℕ} (M : Matrix (Fin N) (Fin N) ℚ) (hm : 0 < m)
    (hordM : orderOf M = m) :
    ∃ S : Finset ℕ, S ⊆ m.divisors ∧
      (∀ d ∈ m.divisors, cyclotomic d ℚ ∣ minpoly ℚ M → d ∈ S) ∧
      ∑ d ∈ S, Nat.totient d ≤ N ∧
      ∀ p ∈ m.primeFactors, ∃ d ∈ S, p ^ m.factorization p ∣ d := by
  classical
  have hpow : ∀ n, M ^ n = 1 → m ∣ n := fun n h => hordM ▸ orderOf_dvd_of_pow_eq_one h
  set f := minpoly ℚ M with hfdef
  have hint : IsIntegral ℚ M := Matrix.isIntegral M
  have hf0 : f ≠ 0 := minpoly.ne_zero hint
  have hdvdpow : ∀ n, f ∣ (X ^ n - 1 : ℚ[X]) → M ^ n = 1 := by
    intro n h
    have := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero h (minpoly.aeval ℚ M)
    simpa [sub_eq_zero] using this
  have hfm : f ∣ (X ^ m - 1 : ℚ[X]) := by
    apply minpoly.dvd
    have : M ^ m = 1 := hordM ▸ pow_orderOf_eq_one M
    simp [this]
  have hdeg : f.natDegree ≤ N := by
    have h1 := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly M)
      (Matrix.charpoly_monic M).ne_zero
    simpa using h1
  set S := m.divisors.filter (fun d => cyclotomic d ℚ ∣ f) with hS
  refine ⟨S, Finset.filter_subset _ _, fun d hd hdf => Finset.mem_filter.2 ⟨hd, hdf⟩, ?_, ?_⟩
  · have hSdvd : (∏ d ∈ S, cyclotomic d ℚ) ∣ f := by
      apply Finset.prod_dvd_of_coprime
      · intro a _ b _ hab
        exact cyclotomic.isCoprime_rat hab
      · intro d hd
        exact (Finset.mem_filter.1 hd).2
    have h1 := Polynomial.natDegree_le_of_dvd hSdvd hf0
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun d _ => cyclotomic.monic d ℚ)] at h1
    simp only [natDegree_cyclotomic] at h1
    omega
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
  have hmp0 : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hpm) hpp.pos
  by_contra hno
  push Not at hno
  have key : f ∣ (X ^ (m / p) - 1 : ℚ[X]) := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one hmp0, ← nec_divisors_filter hm hpp hpm]
    have hsplit := Finset.prod_filter_mul_prod_filter_not m.divisors
      (fun d => p ^ m.factorization p ∣ d) (fun d => cyclotomic d ℚ)
    rw [prod_cyclotomic_eq_X_pow_sub_one hm] at hsplit
    have hcop : IsCoprime (∏ d ∈ m.divisors.filter (fun d => p ^ m.factorization p ∣ d),
        cyclotomic d ℚ) f := by
      apply IsCoprime.prod_left
      intro d hd
      rw [Finset.mem_filter] at hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd.1
      rw [(cyclotomic.irreducible_rat hd0).coprime_iff_not_dvd]
      intro hdf
      exact hno d (Finset.mem_filter.2 ⟨hd.1, hdf⟩) hd.2
    have hprod : f ∣ (∏ d ∈ m.divisors.filter (fun d => p ^ m.factorization p ∣ d),
        cyclotomic d ℚ) * (∏ d ∈ m.divisors.filter (fun d => ¬ p ^ m.factorization p ∣ d),
        cyclotomic d ℚ) := by
      rw [hsplit]; exact hfm
    exact hcop.symm.dvd_of_dvd_mul_left hprod
  have h1 := hpow _ (hdvdpow _ key)
  have h2 := Nat.le_of_dvd hmp0 h1
  have h3 := Nat.div_lt_self hm hpp.one_lt
  omega

/-- Necessity over `ℚ`. -/
theorem dn_nec_rat {N m : ℕ} (M : Matrix (Fin N) (Fin N) ℚ) (hm : 0 < m)
    (hordM : orderOf M = m) (hdet : M.det = -1) : Even m ∧ psi m + 1 ≤ N := by
  have hpow : M ^ m = 1 := hordM ▸ pow_orderOf_eq_one M
  have heven : Even m := by
    have h1 : M.det ^ m = 1 := by rw [← Matrix.det_pow, hpow, Matrix.det_one]
    rw [hdet] at h1
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h1
  refine ⟨heven, ?_⟩
  have h2 := dn_cyclotomic_two_dvd M (dn_det_add_one_eq_zero M hm hpow hdet)
  obtain ⟨S, hSsub, hSmem, hsum, hcover⟩ := aux_nec_S M hm hordM
  have h2S : 2 ∈ S :=
    hSmem 2 (Nat.mem_divisors.mpr ⟨even_iff_two_dvd.mp heven, hm.ne'⟩) h2
  have hS0 : 0 ∉ S := fun h0 => by
    have := Nat.pos_of_mem_divisors (hSsub h0)
    omega
  have hcov := dn_psi_le_sum_psi hS0 hcover
  have hpt : ∑ d ∈ S, psi d + 1 ≤ ∑ d ∈ S, Nat.totient d := by
    rw [← Finset.add_sum_erase S psi h2S, ← Finset.add_sum_erase S Nat.totient h2S, psi_two,
      Nat.totient_two]
    have := Finset.sum_le_sum (s := S.erase 2) fun d _ => psi_le_totient_internal d
    omega
  omega

/-- Necessity: an element of `GL(N, ℤ)` of order `m ≥ 1` and determinant `−1` has `m` even and
`ψ m + 1 ≤ N`. -/
theorem det_neg_one_imp_internal {N m : ℕ} (A : Matrix.GeneralLinearGroup (Fin N) ℤ)
    (hA : orderOf A = m) (hm : 0 < m) (hdet : (A : Matrix (Fin N) (Fin N) ℤ).det = -1) :
    Even m ∧ psi m + 1 ≤ N := by
  let φ : Matrix (Fin N) (Fin N) ℤ →+* Matrix (Fin N) (Fin N) ℚ := (Int.castRingHom ℚ).mapMatrix
  have hφ : Function.Injective φ := fun a b h =>
    Matrix.map_injective (Int.castRingHom ℚ).injective_int h
  have hord : orderOf (φ (A : Matrix (Fin N) (Fin N) ℤ)) = m := by
    have := orderOf_injective φ.toMonoidHom hφ (A : Matrix (Fin N) (Fin N) ℤ)
    rw [orderOf_units, hA] at this
    exact this
  have hdetQ : (φ (A : Matrix (Fin N) (Fin N) ℤ)).det = -1 := by
    show ((Int.castRingHom ℚ).mapMatrix (A : Matrix (Fin N) (Fin N) ℤ)).det = -1
    rw [← RingHom.map_det, hdet]
    simp
  exact dn_nec_rat _ hm hord hdetQ

/-! ## The classification and the least dimension -/

theorem exists_orderOf_eq_det_neg_one_iff_internal {N m : ℕ} (hm : 0 < m) :
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ,
      orderOf A = m ∧ (A : Matrix (Fin N) (Fin N) ℤ).det = -1) ↔
      Even m ∧ psi m + 1 ≤ N := by
  constructor
  · rintro ⟨A, hA, hdet⟩
    exact det_neg_one_imp_internal A hA hm hdet
  · rintro ⟨he, h⟩
    exact exists_orderOf_eq_det_neg_one_internal he hm h

theorem isLeast_dimension_det_neg_one_internal {m : ℕ} (hm : Even m) (h0 : 0 < m) :
    IsLeast {N : ℕ | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ,
      orderOf A = m ∧ (A : Matrix (Fin N) (Fin N) ℤ).det = -1} (psi m + 1) := by
  constructor
  · exact exists_orderOf_eq_det_neg_one_internal hm h0 le_rfl
  · rintro N ⟨A, hA, hdet⟩
    exact (det_neg_one_imp_internal A hA h0 hdet).2

end Crystallographic
