module

public import Crystallographic.Psi

/-!
# Necessity: `ψ (orderOf A) ≤ N`

Over `ℚ`: for `A : GL (Fin N) ℚ` of finite order `m`, the minimal polynomial `f` of the matrix
divides `X ^ m − 1 = ∏_{d ∣ m} Φ_d`. Let `S = {d ∣ m : Φ_d ∣ f}`. The `Φ_d` are pairwise coprime
irreducibles over `ℚ`, so `∏_{d ∈ S} Φ_d ∣ f`, whence `∑_{d ∈ S} φ d ≤ natDegree f ≤ N`
(`Matrix.minpoly_dvd_charpoly`, `Matrix.charpoly_natDegree_eq_dim`). If some prime power `p ^ k`
exactly dividing `m` divided no `d ∈ S`, then `f` would be coprime to every `Φ_d` with `d ∣ m`,
`p ^ k ∣ d`, hence would divide `∏_{d ∣ m / p} Φ_d = X ^ (m / p) − 1`, so `A ^ (m / p) = 1`,
contradicting `orderOf A = m`. Then `psi_le_sum_totient_of_zero_notMem` gives `ψ m ≤ ∑_{d ∈ S} φ d ≤ N`.
For infinite order `orderOf A = 0` and `ψ 0 = 0`. Over `ℤ`: map to `ℚ` by the injective
hom `Units.map (RingHom.mapMatrix (Int.castRingHom ℚ))`, which preserves `orderOf`.
-/

@[expose] public section

namespace Crystallographic

open Polynomial

/-- The divisors of `m` not divisible by the full power `p ^ m.factorization p` are exactly the
divisors of `m / p`. -/
theorem nec_divisors_filter {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : p ∣ m) :
    m.divisors.filter (fun d => ¬ p ^ m.factorization p ∣ d) = (m / p).divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  have hmp : m / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos).ne'
  constructor
  · rintro ⟨⟨hd, -⟩, hq⟩
    refine ⟨?_, hmp⟩
    have hd0 : d ≠ 0 := by rintro rfl; exact hq (dvd_zero _)
    rw [Nat.dvd_div_iff_mul_dvd hpm, mul_comm,
      ← Nat.factorization_le_iff_dvd (Nat.mul_ne_zero hd0 hp.ne_zero) hm.ne',
      Nat.factorization_mul hd0 hp.ne_zero, hp.factorization]
    intro r
    have hdm := (Nat.factorization_le_iff_dvd hd0 hm.ne').2 hd r
    rw [hp.pow_dvd_iff_le_factorization hd0] at hq
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    by_cases h : p = r
    · subst h
      simp only [ite_true]
      omega
    · simp only [h, ite_false]
      omega
  · rintro ⟨hd, -⟩
    rw [Nat.dvd_div_iff_mul_dvd hpm] at hd
    refine ⟨⟨(Dvd.intro_left p rfl).trans hd, hm.ne'⟩, ?_⟩
    intro hq
    exact Nat.pow_succ_factorization_not_dvd hm.ne' hp (by
      rw [pow_succ, mul_comm]; exact (Nat.mul_dvd_mul_left p hq).trans hd)

/-- Necessity over `ℚ`. -/
theorem psi_orderOf_le_rat {N : ℕ} (A : Matrix.GeneralLinearGroup (Fin N) ℚ) :
    psi (orderOf A) ≤ N := by
  classical
  rcases Nat.eq_zero_or_pos (orderOf A) with h0 | hm
  · rw [h0, psi_zero]; exact Nat.zero_le _
  set m := orderOf A with hmdef
  set M : Matrix (Fin N) (Fin N) ℚ := (A : Matrix (Fin N) (Fin N) ℚ) with hMdef
  have hordM : orderOf M = m := orderOf_units
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
  have hSdvd : (∏ d ∈ S, cyclotomic d ℚ) ∣ f := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      exact cyclotomic.isCoprime_rat hab
    · intro d hd
      exact (Finset.mem_filter.1 hd).2
  have hsum : ∑ d ∈ S, Nat.totient d ≤ N := by
    have h1 := Polynomial.natDegree_le_of_dvd hSdvd hf0
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun d _ => cyclotomic.monic d ℚ)] at h1
    simp only [natDegree_cyclotomic] at h1
    omega
  refine le_trans (psi_le_sum_totient_of_zero_notMem ?_ ?_) hsum
  · intro h0
    exact absurd (Nat.pos_of_mem_divisors (Finset.mem_filter.1 h0).1) (lt_irrefl 0)
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

theorem psi_orderOf_le_internal {N : ℕ} (A : Matrix.GeneralLinearGroup (Fin N) ℤ) :
    psi (orderOf A) ≤ N := by
  let φ : Matrix (Fin N) (Fin N) ℤ →* Matrix (Fin N) (Fin N) ℚ :=
    (RingHom.mapMatrix (Int.castRingHom ℚ)).toMonoidHom
  have hφ : Function.Injective φ := fun a b h =>
    Matrix.map_injective (Int.castRingHom ℚ).injective_int h
  rw [← orderOf_injective (Units.map φ) (Units.map_injective hφ) A]
  exact psi_orderOf_le_rat _

end Crystallographic
