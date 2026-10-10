module

public import Crystallographic.Psi

/-!
# A kernel-computable `ψ`

`psi` is defined through `Nat.factorization`, which the kernel cannot evaluate. `psiC` computes the
same function by trial division with a fuel argument (structural recursion, so `decide +kernel`
reduces it): `psiAux fuel p m` sums the `ψ`-terms of the prime powers of `m` whose primes are
`≥ p`, under the invariant that `m` has no prime factor below `p` and `m < (p + fuel)²`. If `m ≤ 1`
the sum is `0`; if `1 < m < p²` then `m` is prime and contributes `m − 1` (or `0` when `m = 2`);
otherwise, when `p ∣ m`, `p` is prime, `stripPow` removes it (`m = p ^ k * m'`, `p ∤ m'`), the term
is `φ (p ^ k)` (or `0` when `p ^ k = 2`) and the loop continues at `p + 1` on `m'`; when `p ∤ m`
the loop continues at `p + 1` on `m`. Lane: **compute** (proves `psiC_eq_psi`; the definitions are
the desk's and are shared with the **tables** lane, so change them only by agreement).
-/

@[expose] public section

namespace Crystallographic

/-- `stripPow p fuel m = (k, m')` with `m = p ^ k * m'` and `p ∤ m'`, for `1 < p`, `0 < m ≤ fuel`. -/
def stripPow (p : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, m => (0, m)
  | fuel + 1, m =>
    if 1 < p ∧ 0 < m ∧ p ∣ m then
      match stripPow p fuel (m / p) with
      | (k, r) => (k + 1, r)
    else (0, m)

/-- The trial-division loop; see the module docstring. -/
def psiAux : ℕ → ℕ → ℕ → ℕ
  | fuel, p, m =>
    if m ≤ 1 then 0
    else if m < p * p then (if m = 2 then 0 else m - 1)
    else
      match fuel with
      | 0 => 0
      | fuel + 1 =>
        if p ∣ m then
          match stripPow p m m with
          | (k, r) => (if p ^ k = 2 then 0 else p ^ (k - 1) * (p - 1)) + psiAux fuel (p + 1) r
        else psiAux fuel (p + 1) m

/-- The kernel-computable `ψ`. -/
def psiC (m : ℕ) : ℕ := psiAux m 2 m

theorem stripPow_spec {p fuel m : ℕ} (hp : 1 < p) (hm : 0 < m) (hfuel : m ≤ fuel) :
    m = p ^ (stripPow p fuel m).1 * (stripPow p fuel m).2 ∧ ¬ p ∣ (stripPow p fuel m).2 := by
  induction fuel generalizing m with
  | zero => omega
  | succ n ih =>
    by_cases h : p ∣ m
    · have hpos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm h) (by omega)
      have hlt : m / p < m := Nat.div_lt_self hm hp
      obtain ⟨h1, h2⟩ := ih hpos (by omega)
      rcases hs : stripPow p n (m / p) with ⟨k, r⟩
      rw [hs] at h1 h2
      simp only [stripPow, hp, hm, h, and_self, ite_true, hs]
      refine ⟨?_, h2⟩
      calc m = p * (m / p) := (Nat.mul_div_cancel' h).symm
        _ = p * (p ^ k * r) := by rw [h1]
        _ = p ^ (k + 1) * r := by ring
    · have hc : ¬ (1 < p ∧ 0 < m ∧ p ∣ m) := fun hc => h hc.2.2
      simp only [stripPow, hc, ite_false, pow_zero, one_mul]
      exact ⟨trivial, h⟩

/-- A number `1 < m < p²` with no prime factor below `p` is prime. -/
theorem cmp_prime_of_lt_sq {p m : ℕ} (h1 : 1 < m) (hlt : m < p * p)
    (hmin : ∀ q, q.Prime → q ∣ m → p ≤ q) : m.Prime := by
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < m) hnp
  have hle := hmin _ (Nat.minFac_prime (by omega : m ≠ 1)) (Nat.minFac_dvd m)
  have : p * p ≤ m.minFac * m.minFac := Nat.mul_le_mul hle hle
  rw [sq] at hsq
  omega

theorem cmp_psi_prime {m : ℕ} (hm : m.Prime) : psi m = if m = 2 then 0 else m - 1 := by
  by_cases h2 : m = 2
  · subst h2
    simpa using psi_two
  · have := psi_prime_pow_internal (k := 1) hm one_pos (by simpa using h2)
    rw [pow_one] at this
    rw [this, Nat.totient_prime hm]
    simp [h2]

theorem cmp_psi_le_one {m : ℕ} (h : m ≤ 1) : psi m = 0 := by
  interval_cases m
  · exact psi_zero
  · exact psi_one

theorem psiAux_eq {fuel p m : ℕ} (hp : 2 ≤ p) (hfuel : m < (p + fuel) * (p + fuel))
    (hmin : ∀ q, q.Prime → q ∣ m → p ≤ q) : psiAux fuel p m = psi m := by
  induction fuel generalizing p m with
  | zero =>
    rw [psiAux]
    by_cases h1 : m ≤ 1
    · simp only [h1, ite_true]
      exact (cmp_psi_le_one h1).symm
    · have h2 : m < p * p := by simpa using hfuel
      simp only [h1, h2, ite_true, ite_false]
      exact (cmp_psi_prime (cmp_prime_of_lt_sq (by omega) h2 hmin)).symm
  | succ n ih =>
    rw [psiAux]
    by_cases h1 : m ≤ 1
    · simp only [h1, ite_true]
      exact (cmp_psi_le_one h1).symm
    by_cases h2 : m < p * p
    · simp only [h1, h2, ite_true, ite_false]
      exact (cmp_psi_prime (cmp_prime_of_lt_sq (by omega) h2 hmin)).symm
    have hfe : p + 1 + n = p + (n + 1) := by omega
    by_cases h3 : p ∣ m
    · simp only [h1, h2, h3, ite_true, ite_false]
      have hm0 : 0 < m := by omega
      -- `p` is prime
      have hpp : p.Prime := by
        have hmf := Nat.minFac_prime (by omega : p ≠ 1)
        have hle := hmin _ hmf (dvd_trans (Nat.minFac_dvd p) h3)
        have hle2 := Nat.minFac_le (by omega : 0 < p)
        have heq : p.minFac = p := by omega
        rw [heq] at hmf
        exact hmf
      obtain ⟨hspec1, hspec2⟩ := stripPow_spec (fuel := m) (by omega : 1 < p) hm0 le_rfl
      rcases hs : stripPow p m m with ⟨k, r⟩
      rw [hs] at hspec1 hspec2
      simp only at hspec1 hspec2 ⊢
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk
          rw [pow_zero, one_mul] at hspec1
          rw [← hspec1] at hspec2
          exact absurd h3 hspec2
        · exact hk
      have hr0 : 0 < r := by
        rcases Nat.eq_zero_or_pos r with hr | hr
        · subst hr; omega
        · exact hr
      have hrm : r ≤ m := by
        conv_rhs => rw [hspec1]
        exact Nat.le_mul_of_pos_left r (Nat.pow_pos (by omega))
      have hcop : Nat.Coprime (p ^ k) r :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hspec2)
      have hih : psiAux n (p + 1) r = psi r := by
        apply ih (by omega)
        · rw [hfe]; omega
        · intro q hq hqr
          have hqm : q ∣ m := by
            rw [hspec1]; exact Dvd.dvd.mul_left hqr _
          have hpq := hmin q hq hqm
          have hne : q ≠ p := by
            rintro rfl; exact hspec2 hqr
          omega
      rw [hih]
      conv_rhs => rw [hspec1, psi_mul_internal hcop]
      congr 1
      by_cases h2k : p ^ k = 2
      · simp only [h2k, ite_true]
        exact psi_two.symm
      · simp only [h2k, ite_false]
        rw [psi_prime_pow_internal hpp hk h2k, Nat.totient_prime_pow hpp hk]
    · simp only [h1, h2, h3, ite_false]
      apply ih (by omega)
      · rw [hfe]; exact hfuel
      · intro q hq hqm
        have hpq := hmin q hq hqm
        have hne : q ≠ p := by
          rintro rfl; exact h3 hqm
        omega

theorem psiC_eq_psi (m : ℕ) : psiC m = psi m := by
  unfold psiC
  apply psiAux_eq le_rfl
  · nlinarith
  · intro q hq _
    exact hq.two_le

end Crystallographic
