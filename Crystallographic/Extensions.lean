module

public import Crystallographic.Main
public import Crystallographic.Extra

/-!
# Every even minimum dimension occurs

The image of `psi` is exactly the even natural numbers.  In fact, every such value is
attained at an odd squarefree positive integer.  The proof uses Bertrand's postulate:
for a target `2 * n > 0`, select an odd prime `p` with `n + 1 < p ≤ 2 * n + 1`
and recurse on `2 * n - (p - 1)`.  This remainder is smaller than `p - 1`, so `p`
cannot divide the previously constructed integer; multiplication by `p` preserves
squarefreeness and adds exactly `p - 1` to `psi`.

Consequently, for positive dimensions `N` and `M`, `finiteOrders N ⊆ finiteOrders M` iff
`N / 2 ≤ M / 2`, and equality iff `N / 2 = M / 2`; every positive even dimension adds an odd
squarefree order.

The witnesses are those of the proof of Proposition 3(2) of Bamberg–Cairns–Kilminster (2003),
p. 207; the half-dimension statements follow from it with the restriction and the parity of `ψ`.
-/

@[expose] public section

namespace Crystallographic

/-- An odd prime divisor of a positive integer contributes at least `p - 1` to `psi`. -/
theorem prime_sub_one_le_psi_internal {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpm : p ∣ m) : p - 1 ≤ psi m := by
  have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.ne'⟩
  have hterm : p - 1 ≤ psi_term m p := by
    have h := psi_term_mono hp (a := 1) (by norm_num) (psi_factorization_pos hmem)
    simpa [psi_term, hp2, Nat.totient_prime hp] using h
  exact hterm.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)

/-- Every even natural number is `psi m` for a positive odd squarefree integer `m`. -/
theorem exists_odd_squarefree_psi_eq_internal (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ Squarefree m ∧ psi m = 2 * n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, Nat.one_pos, odd_one, squarefree_one, by simp [psi_one]⟩
    obtain ⟨p, hp, hpl, hpu⟩ :=
      Nat.exists_prime_lt_and_le_two_mul (n + 1) (by omega)
    have hp2 : p ≠ 2 := by omega
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    obtain ⟨j, hj⟩ := hpodd
    have hjn : j ≤ n := by omega
    have hr : n - j < n := by omega
    obtain ⟨m, hm, hmodd, hmsq, hpsi⟩ := ih (n - j) hr
    have hnot : ¬ p ∣ m := by
      intro hpm
      have hbound := prime_sub_one_le_psi_internal hm hp hp2 hpm
      omega
    have hcop : Nat.Coprime p m := (hp.coprime_iff_not_dvd).mpr hnot
    have hpsip : psi p = p - 1 := by
      have h := psi_prime_pow_internal hp (k := 1) (by norm_num) (by simpa using hp2)
      simpa [Nat.totient_prime hp] using h
    refine ⟨p * m, Nat.mul_pos hp.pos hm, (hp.odd_of_ne_two hp2).mul hmodd,
      (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hmsq⟩, ?_⟩
    rw [psi_mul_internal hcop, hpsip, hpsi]
    omega

/-- The image of `psi` is exactly the even natural numbers. -/
theorem range_psi_internal : Set.range psi = {n : ℕ | Even n} := by
  ext n
  constructor
  · rintro ⟨m, rfl⟩
    exact even_psi_internal m
  · rintro ⟨k, hk⟩
    obtain ⟨m, _, _, _, hpsi⟩ := exists_odd_squarefree_psi_eq_internal k
    exact ⟨m, by omega⟩

/-- For positive dimensions, the finite orders of GL(N, Z) are among those of GL(M, Z) iff N / 2 <= M / 2. -/
theorem finiteOrders_subset_iff_internal {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    finiteOrders N ⊆ finiteOrders M ↔ N / 2 ≤ M / 2 := by
  rw [finiteOrders_eq_internal hN, finiteOrders_eq_internal hM]
  constructor
  · intro h
    obtain ⟨m, hm, _, _, hpsi⟩ := exists_odd_squarefree_psi_eq_internal (N / 2)
    have hmem : m ∈ {m : ℕ | 0 < m ∧ psi m ≤ N} := ⟨hm, by omega⟩
    have hbound := (h hmem).2
    omega
  · intro h m hm
    obtain ⟨k, hk⟩ := even_psi_internal m
    exact ⟨hm.1, by have := hm.2; omega⟩

/-- Two positive dimensions have the same finite orders iff their integer halves agree. -/
theorem finiteOrders_eq_iff_internal {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    finiteOrders N = finiteOrders M ↔ N / 2 = M / 2 := by
  constructor
  · intro h
    apply Nat.le_antisymm
    · exact (finiteOrders_subset_iff_internal hN hM).mp (by rw [h])
    · exact (finiteOrders_subset_iff_internal hM hN).mp (by rw [h])
  · intro h
    apply Set.Subset.antisymm
    · exact (finiteOrders_subset_iff_internal hN hM).mpr (by omega)
    · exact (finiteOrders_subset_iff_internal hM hN).mpr (by omega)

/-- An odd squarefree order appears for the first time at each positive even dimension. -/
theorem exists_new_odd_squarefree_order_internal (n : ℕ) :
    ∃ m : ℕ, Odd m ∧ Squarefree m ∧
      m ∈ finiteOrders (2 * n + 2) ∧ m ∉ finiteOrders (2 * n + 1) := by
  obtain ⟨m, hm, hmodd, hmsq, hpsi⟩ := exists_odd_squarefree_psi_eq_internal (n + 1)
  refine ⟨m, hmodd, hmsq, ?_, ?_⟩
  · rw [finiteOrders_eq_internal (by omega)]
    exact ⟨hm, by omega⟩
  · rw [finiteOrders_eq_internal (by omega)]
    rintro ⟨_, hbound⟩
    omega

end Crystallographic
