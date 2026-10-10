module

public import Crystallographic.Defs

/-!
# The arithmetic of `ψ`

Values, additivity on coprime factors, the comparison with `φ`, parity, the divisor-sum form, the
bound `m ≤ 2^(ψ m + 1)`, and the covering inequality `ψ m ≤ ∑_{d ∈ S} φ d` (for `0 ∉ S`) used by
necessity.
-/

@[expose] public section

namespace Crystallographic

/-- The `p`-term of `ψ m`. -/
def psi_term (m p : ℕ) : ℕ :=
  if p ^ m.factorization p = 2 then 0 else Nat.totient (p ^ m.factorization p)

theorem psi_eq_sum_term (m : ℕ) : psi m = ∑ p ∈ m.primeFactors, psi_term m p := rfl

theorem psi_factorization_pos {m p : ℕ} (hp : p ∈ m.primeFactors) : 0 < m.factorization p :=
  Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization]))

theorem psi_zero : psi 0 = 0 := by simp [psi]

theorem psi_one : psi 1 = 0 := by simp [psi]

theorem psi_two : psi 2 = 0 := by
  rw [psi, Nat.prime_two.primeFactors, Finset.sum_singleton, Nat.prime_two.factorization_self]
  norm_num

theorem psi_prime_pow_internal {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (h2 : p ^ k ≠ 2) :
    psi (p ^ k) = Nat.totient (p ^ k) := by
  rw [psi, Nat.primeFactors_prime_pow hk.ne' hp, Finset.sum_singleton,
    hp.factorization_pow, Finsupp.single_eq_same]
  simp [h2]

theorem psi_term_mul_left {a b p : ℕ} (hab : Nat.Coprime a b) (hp : p ∈ a.primeFactors) :
    psi_term (a * b) p = psi_term a p := by
  have hb : b.factorization p = 0 := by
    apply Finsupp.notMem_support_iff.mp
    rw [Nat.support_factorization]
    exact Finset.disjoint_left.mp hab.disjoint_primeFactors hp
  simp only [psi_term, Nat.factorization_mul_apply_of_coprime hab, hb, add_zero]

theorem psi_mul_internal {a b : ℕ} (hab : Nat.Coprime a b) : psi (a * b) = psi a + psi b := by
  rw [psi_eq_sum_term, hab.primeFactors_mul, Finset.sum_union hab.disjoint_primeFactors,
    psi_eq_sum_term a, psi_eq_sum_term b]
  congr 1
  · exact Finset.sum_congr rfl fun p hp => psi_term_mul_left hab hp
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [mul_comm]
    exact psi_term_mul_left hab.symm hp

theorem psi_eq_zero_iff_internal (m : ℕ) : psi m = 0 ↔ m ≤ 2 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · omega
    have h2 : ∀ p ∈ m.primeFactors, p = 2 ∧ p ^ m.factorization p = 2 := by
      intro p hp
      have ht := (Finset.sum_eq_zero_iff.mp h) p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hk := psi_factorization_pos hp
      have hq : p ^ m.factorization p = 2 := by
        by_contra hne
        simp only [hne, ↓reduceIte, Nat.totient_eq_zero] at ht
        exact absurd ht (pow_ne_zero _ hpr.ne_zero)
      refine ⟨?_, hq⟩
      have hd : p ∣ 2 := hq ▸ dvd_pow_self p hk.ne'
      exact (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp hd
    have hprod := Nat.prod_primeFactors_pow_factorization hm.ne'
    rw [Finset.prod_congr rfl (fun p hp => (h2 p hp).2), Finset.prod_const] at hprod
    have hsub : m.primeFactors ⊆ {2} := fun p hp => Finset.mem_singleton.mpr (h2 p hp).1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    rw [hprod]
    calc 2 ^ m.primeFactors.card ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hcard
      _ = 2 := by norm_num
  · intro h
    interval_cases m
    · exact psi_zero
    · exact psi_one
    · exact psi_two

/-- The sum-versus-product inequality, with the side condition carried through the induction. -/
theorem psi_sum_le_prod_aux {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℕ)
    (h1 : ∀ i ∈ s, 1 ≤ a i) (hle : ∀ i ∈ s, b i ≤ a i) (h0 : ∀ i ∈ s, a i = 1 → b i = 0) :
    ∑ i ∈ s, b i ≤ ∏ i ∈ s, a i ∧ (∏ i ∈ s, a i = 1 → ∑ i ∈ s, b i = 0) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hle i (Finset.mem_insert_of_mem hi))
      (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have hA := h1 j (Finset.mem_insert_self j s)
    have hB := hle j (Finset.mem_insert_self j s)
    have hB0 := h0 j (Finset.mem_insert_self j s)
    have hP : 1 ≤ ∏ i ∈ s, a i :=
      Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i hi =>
        Nat.one_le_iff_ne_zero.mp (h1 i (Finset.mem_insert_of_mem hi)))
    set A := a j
    set B := b j
    set P := ∏ i ∈ s, a i
    set S := ∑ i ∈ s, b i
    rcases Nat.lt_or_ge A 2 with hA2 | hA2
    · have hA1 : A = 1 := by omega
      have := hB0 hA1
      rw [hA1, this, one_mul, zero_add]
      exact ⟨ih1, ih2⟩
    rcases Nat.lt_or_ge P 2 with hP2 | hP2
    · have hP1 : P = 1 := by omega
      have := ih2 hP1
      rw [hP1, this, mul_one, add_zero]
      exact ⟨hB, fun h => by omega⟩
    refine ⟨?_, fun h => ?_⟩
    · nlinarith
    · nlinarith

theorem psi_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℕ)
    (h1 : ∀ i ∈ s, 1 ≤ a i) (hle : ∀ i ∈ s, b i ≤ a i) (h0 : ∀ i ∈ s, a i = 1 → b i = 0) :
    ∑ i ∈ s, b i ≤ ∏ i ∈ s, a i :=
  (psi_sum_le_prod_aux s a b h1 hle h0).1

theorem psi_totient_eq_prod {m : ℕ} (hm : m ≠ 0) :
    Nat.totient m = ∏ p ∈ m.primeFactors, Nat.totient (p ^ m.factorization p) := by
  rw [Nat.totient_eq_prod_factorization hm, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.totient_prime_pow (Nat.prime_of_mem_primeFactors hp) (psi_factorization_pos hp)]

theorem psi_le_totient_internal (m : ℕ) : psi m ≤ Nat.totient m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [psi_zero]
  rw [psi_eq_sum_term, psi_totient_eq_prod hm]
  apply psi_sum_le_prod
  · intro p hp
    exact Nat.totient_pos.mpr (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
  · intro p hp
    unfold psi_term
    split_ifs <;> simp
  · intro p hp h1
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hk := psi_factorization_pos hp
    rcases Nat.totient_eq_one_iff.mp h1 with h | h
    · exact absurd h (Nat.one_lt_pow hk.ne' hpr.one_lt).ne'
    · simp [psi_term, h]

theorem even_psi_internal (m : ℕ) : Even (psi m) := by
  rw [psi_eq_sum_term]
  refine Finset.even_sum _ fun p hp => ?_
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hk := psi_factorization_pos hp
  unfold psi_term
  split_ifs with h
  · exact ⟨0, rfl⟩
  · apply Nat.totient_even
    have := Nat.one_lt_pow hk.ne' hpr.one_lt
    omega

theorem psi_prime_pow_le_two_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    p ^ k ≤ 2 ^ Nat.totient (p ^ k) := by
  rw [Nat.totient_prime_pow hp hk]
  have h2 := hp.two_le
  have hp1 : p ≤ 2 ^ (p - 1) := by
    have := (p - 1).lt_two_pow_self
    omega
  have hk1 : k ≤ p ^ (k - 1) := by
    have := (k - 1).lt_two_pow_self
    have : 2 ^ (k - 1) ≤ p ^ (k - 1) := Nat.pow_le_pow_left h2 _
    omega
  calc p ^ k ≤ (2 ^ (p - 1)) ^ k := Nat.pow_le_pow_left hp1 _
    _ = 2 ^ ((p - 1) * k) := by rw [← pow_mul]
    _ ≤ 2 ^ (p ^ (k - 1) * (p - 1)) := by
      apply Nat.pow_le_pow_right (by norm_num)
      rw [mul_comm]
      exact Nat.mul_le_mul_right _ hk1

theorem le_two_pow_psi_internal {m : ℕ} (hm : 0 < m) : m ≤ 2 ^ (psi m + 1) := by
  have hprod := Nat.prod_primeFactors_pow_factorization hm.ne'
  have hterm : ∀ p ∈ m.primeFactors, Nat.totient (p ^ m.factorization p) =
      psi_term m p + (if p = 2 ∧ p ^ m.factorization p = 2 then 1 else 0) := by
    intro p hp
    unfold psi_term
    by_cases h : p ^ m.factorization p = 2
    · have hpr := Nat.prime_of_mem_primeFactors hp
      have hk := psi_factorization_pos hp
      have hp2 : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp (h ▸ dvd_pow_self p hk.ne')
      subst hp2
      simp [h]
    · simp [h]
  have hsum : ∑ p ∈ m.primeFactors, Nat.totient (p ^ m.factorization p) ≤ psi m + 1 := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← psi_eq_sum_term]
    have : ∑ p ∈ m.primeFactors, (if p = 2 ∧ p ^ m.factorization p = 2 then 1 else 0) ≤
        ∑ p ∈ m.primeFactors, (if p = 2 then 1 else 0) := by
      refine Finset.sum_le_sum fun p _ => ?_
      by_cases h : p = 2
      · simp only [h, true_and, ↓reduceIte]
        split_ifs <;> norm_num
      · simp [h]
    rw [Finset.sum_ite_eq'] at this
    split_ifs at this <;> omega
  calc m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := hprod
    _ ≤ ∏ p ∈ m.primeFactors, 2 ^ Nat.totient (p ^ m.factorization p) :=
      Finset.prod_le_prod fun p hp =>
        psi_prime_pow_le_two_pow (Nat.prime_of_mem_primeFactors hp) (psi_factorization_pos hp)
    _ = 2 ^ ∑ p ∈ m.primeFactors, Nat.totient (p ^ m.factorization p) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ 2 ^ (psi m + 1) := Nat.pow_le_pow_right (by norm_num) hsum

theorem psi_eq_sum_divisors_internal (m : ℕ) :
    psi m = ∑ d ∈ m.divisors,
      if IsPrimePow d ∧ Nat.Coprime d (m / d) ∧ d ≠ 2 then Nat.totient d else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [psi_zero]
  set g : ℕ → ℕ := fun d =>
    if IsPrimePow d ∧ Nat.Coprime d (m / d) ∧ d ≠ 2 then Nat.totient d else 0 with hg
  have hinj : Set.InjOn (fun p => p ^ m.factorization p) (m.primeFactors : Set ℕ) := by
    intro p hp p' hp' h
    have hp1 := Nat.prime_of_mem_primeFactors hp
    have hp1' := Nat.prime_of_mem_primeFactors hp'
    have h' := congrArg Nat.primeFactors h
    simp only at h'
    rw [Nat.primeFactors_prime_pow (psi_factorization_pos hp).ne' hp1,
      Nat.primeFactors_prime_pow (psi_factorization_pos hp').ne' hp1'] at h'
    exact Finset.singleton_injective h'
  have hsub : m.primeFactors.image (fun p => p ^ m.factorization p) ⊆ m.divisors := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨Nat.ordProj_dvd m p, hm⟩
  have hz : ∀ d ∈ m.divisors,
      d ∉ m.primeFactors.image (fun p => p ^ m.factorization p) → g d = 0 := by
    intro d hd hnot
    simp only [hg]
    split_ifs with h
    · exfalso
      obtain ⟨hpp, hcop, -⟩ := h
      obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
      have hdm : p ^ j ∣ m := Nat.dvd_of_mem_divisors hd
      apply hnot
      refine Finset.mem_image.mpr ⟨p, Nat.mem_primeFactors.mpr
        ⟨hp, dvd_trans (dvd_pow_self p hj.ne') hdm, hm⟩, ?_⟩
      have hcp : Nat.Coprime p (m / p ^ j) :=
        Nat.Coprime.coprime_dvd_left (dvd_pow_self p hj.ne') hcop
      have h0 : (m / p ^ j).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcp)
      have hmul : m = p ^ j * (m / p ^ j) := (Nat.mul_div_cancel' hdm).symm
      have hj' : m.factorization p = j := by
        rw [hmul, Nat.factorization_mul_apply_of_coprime hcop, hp.factorization_pow,
          Finsupp.single_eq_same, h0, add_zero]
      simp only [hj']
    · rfl
  rw [← Finset.sum_subset hsub hz, Finset.sum_image hinj, psi_eq_sum_term]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hk := psi_factorization_pos hp
  have hpp : IsPrimePow (p ^ m.factorization p) :=
    (isPrimePow_nat_iff _).mpr ⟨p, _, hpr, hk, rfl⟩
  have hcop : Nat.Coprime (p ^ m.factorization p) (m / p ^ m.factorization p) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hpr hm)
  simp only [hg, psi_term]
  by_cases h : p ^ m.factorization p = 2
  · simp only [h, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
  · have hy : IsPrimePow (p ^ m.factorization p) ∧
        Nat.Coprime (p ^ m.factorization p) (m / p ^ m.factorization p) ∧
        p ^ m.factorization p ≠ 2 := ⟨hpp, hcop, h⟩
    simp only [h, ↓reduceIte]
    exact (ite_eq_left_iff.mpr fun hn => absurd hy hn).symm

theorem psi_term_mono {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hab : a ≤ b) :
    (if p ^ a = 2 then 0 else Nat.totient (p ^ a)) ≤
      (if p ^ b = 2 then 0 else Nat.totient (p ^ b)) := by
  by_cases h1 : p ^ a = 2
  · simp [h1]
  have h2 : p ^ b ≠ 2 := by
    intro h2
    have hdvd : p ^ a ∣ 2 := h2 ▸ Nat.pow_dvd_pow p hab
    have := Nat.le_of_dvd (by norm_num) hdvd
    have := Nat.one_lt_pow ha.ne' hp.one_lt
    omega
  simp only [h1, h2, ↓reduceIte]
  exact Nat.le_of_dvd (Nat.totient_pos.mpr (pow_pos hp.pos _))
    (Nat.totient_dvd_of_dvd (Nat.pow_dvd_pow p hab))

/-- The covering inequality; the members of `S` must be nonzero (for `S = {0}` and `m = 3` the cover
holds, since `3 ∣ 0`, but `ψ 3 = 2 > φ 0 = 0`). -/
theorem psi_le_sum_totient_of_zero_notMem {m : ℕ} {S : Finset ℕ} (hS : 0 ∉ S)
    (hcover : ∀ p ∈ m.primeFactors, ∃ d ∈ S, p ^ m.factorization p ∣ d) :
    psi m ≤ ∑ d ∈ S, Nat.totient d := by
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
    _ ≤ Nat.totient d := psi_le_totient_internal d

end Crystallographic
