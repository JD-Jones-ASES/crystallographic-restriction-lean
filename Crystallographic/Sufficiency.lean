module

public import Crystallographic.Psi
public import Crystallographic.Block

/-!
# Sufficiency: an element of order `m` in dimension `ψ m`

By `Nat.recOnPosPrimePosCoprime` on `m`, for `m ≥ 1` with `m` odd or `4 ∣ m`: a prime power
`p ^ k ≠ 2` is the cyclotomic block of size `φ (p ^ k) = ψ (p ^ k)`; coprime factors `a`, `b`
(both odd, or one odd and `4` dividing the other) are block-summed into dimension
`ψ a + ψ b = ψ (a * b)`; `m = 1` is the empty matrix. For `m ≡ 2 (mod 4)`, `m ≠ 2`: `m = 2 * m'`
with `m'` odd, `ψ m = ψ m' ≥ 2`, and `−A` for the element `A` of order `m'`. Then pad to any
`N ≥ ψ m`; for `m = 2` take `−1` in dimension `N ≥ 1`. Lane: **sufficiency**.
-/

@[expose] public section

namespace Crystallographic

/-- Transport an element of order `u` along an equality of dimensions. -/
theorem suf_cast {a b u : ℕ} (h : a = b)
    (H : ∃ A : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf A = u) :
    ∃ A : Matrix.GeneralLinearGroup (Fin b) ℤ, orderOf A = u := by
  subst h; exact H

/-- Transport along an equality of orders. -/
theorem suf_cast_order {a u v : ℕ} (h : u = v)
    (H : ∃ A : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf A = u) :
    ∃ A : Matrix.GeneralLinearGroup (Fin a) ℤ, orderOf A = v := by
  subst h; exact H

/-- The parity hypothesis passes to coprime factors. -/
theorem suf_split {a b : ℕ} (hab : Nat.Coprime a b) (h : Odd (a * b) ∨ 4 ∣ a * b) :
    (Odd a ∨ 4 ∣ a) ∧ (Odd b ∨ 4 ∣ b) := by
  rcases h with h | h
  · obtain ⟨ha, hb⟩ := Nat.odd_mul.mp h
    exact ⟨Or.inl ha, Or.inl hb⟩
  · by_cases ha2 : 2 ∣ a
    · have hb2 : ¬ 2 ∣ b := by
        intro hb2
        have h2 : 2 ∣ Nat.gcd a b := Nat.dvd_gcd ha2 hb2
        rw [hab] at h2
        omega
      have hc : Nat.Coprime 2 b := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hb2
      have h4 : Nat.Coprime (2 ^ 2) b := Nat.Coprime.pow_left 2 hc
      have h4a : 4 ∣ a := Nat.Coprime.dvd_of_dvd_mul_right (by simpa using h4) h
      exact ⟨Or.inr h4a, Or.inl (Nat.odd_iff.mpr (by omega))⟩
    · have hc : Nat.Coprime 2 a := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ha2
      have h4 : Nat.Coprime (2 ^ 2) a := Nat.Coprime.pow_left 2 hc
      have h4b : 4 ∣ b := Nat.Coprime.dvd_of_dvd_mul_left (by simpa using h4) h
      exact ⟨Or.inl (Nat.odd_iff.mpr (by omega)), Or.inr h4b⟩

/-- The main induction: order `m` in dimension `ψ m` for `m ≥ 1` odd or divisible by `4`. -/
theorem suf_main (m : ℕ) : 0 < m → (Odd m ∨ 4 ∣ m) →
    ∃ A : Matrix.GeneralLinearGroup (Fin (psi m)) ℤ, orderOf A = m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _
    exact suf_cast psi_one.symm ⟨1, orderOf_one⟩
  | prime_pow p k hp hk =>
    intro hpos hpar
    have h2 : p ^ k ≠ 2 := by
      intro he
      rw [he] at hpar
      rcases hpar with h | h
      · exact absurd h (by decide)
      · omega
    exact suf_cast (psi_prime_pow_internal hp hk h2).symm
      (exists_orderOf_eq_totient_internal hpos)
  | coprime a b ha hb hab iha ihb =>
    intro _ hpar
    obtain ⟨hpa, hpb⟩ := suf_split hab hpar
    exact suf_cast (psi_mul_internal hab).symm
      (exists_orderOf_eq_mul hab (iha (by omega) hpa) (ihb (by omega) hpb))

/-- An element of order `m` in dimension `ψ m`, for every `m ≥ 1` other than `2`. -/
theorem exists_orderOf_eq_psi {m : ℕ} (hm : 0 < m) (h2 : m ≠ 2) :
    ∃ A : Matrix.GeneralLinearGroup (Fin (psi m)) ℤ, orderOf A = m := by
  by_cases hc : Odd m ∨ 4 ∣ m
  · exact suf_main m hm hc
  · have hno : ¬ Odd m := fun h => hc (Or.inl h)
    have hn4 : ¬ 4 ∣ m := fun h => hc (Or.inr h)
    have hmod : m % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · exact h
      · exact absurd (Nat.odd_iff.mpr h) hno
    set m' := m / 2 with hm'
    have hmm : m = 2 * m' := by omega
    have hodd : Odd m' := Nat.odd_iff.mpr (by omega)
    have hm3 : 3 ≤ m' := by omega
    have hpsi : psi m' ≠ 0 := fun h => by
      have := (psi_eq_zero_iff_internal m').mp h
      omega
    have hcop : Nat.Coprime 2 m' :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    have hpm : psi m' = psi m := by
      rw [hmm, psi_mul_internal hcop, psi_two, zero_add]
    have H := exists_orderOf_eq_two_mul (Nat.pos_of_ne_zero hpsi) hodd
      (suf_main m' (by omega) (Or.inl hodd))
    exact suf_cast hpm (suf_cast_order hmm.symm H)

theorem exists_orderOf_eq_internal {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (h : psi m ≤ N) :
    ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m := by
  by_cases h2 : m = 2
  · subst h2
    exact ⟨-1, orderOf_neg_one_gl hN⟩
  · exact exists_orderOf_eq_of_le h (exists_orderOf_eq_psi hm h2)

end Crystallographic
