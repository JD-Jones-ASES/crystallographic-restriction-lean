module

public import Crystallographic

/-!
# Solution

Each statement of `Challenge.lean`, restated verbatim and closed by the internal theorem of the same
name with the suffix `_internal` (the modules of `Crystallographic/`; VERIFICATION.md names the module of
each theorem). This module does not import `Challenge.lean`; the definitions come from
`Crystallographic/Defs.lean`, which restates those of the Challenge character for character.
-/

@[expose] public section

namespace Crystallographic

theorem psi_eq_zero_iff (m : ℕ) : psi m = 0 ↔ m ≤ 2 :=
  psi_eq_zero_iff_internal m

theorem psi_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (h2 : p ^ k ≠ 2) :
    psi (p ^ k) = Nat.totient (p ^ k) :=
  psi_prime_pow_internal hp hk h2

theorem psi_mul {a b : ℕ} (hab : Nat.Coprime a b) : psi (a * b) = psi a + psi b :=
  psi_mul_internal hab

theorem psi_le_totient (m : ℕ) : psi m ≤ Nat.totient m :=
  psi_le_totient_internal m

theorem even_psi (m : ℕ) : Even (psi m) :=
  even_psi_internal m

theorem psi_eq_sum_divisors (m : ℕ) :
    psi m = ∑ d ∈ m.divisors,
      if IsPrimePow d ∧ Nat.Coprime d (m / d) ∧ d ≠ 2 then Nat.totient d else 0 :=
  psi_eq_sum_divisors_internal m

theorem le_two_pow_psi {m : ℕ} (hm : 0 < m) : m ≤ 2 ^ (psi m + 1) :=
  le_two_pow_psi_internal hm

theorem psi_orderOf_le {N : ℕ} (A : Matrix.GeneralLinearGroup (Fin N) ℤ) :
    psi (orderOf A) ≤ N :=
  psi_orderOf_le_internal A

theorem exists_orderOf_eq {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (h : psi m ≤ N) :
    ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m :=
  exists_orderOf_eq_internal hN hm h

theorem exists_orderOf_eq_iff {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m) ↔ psi m ≤ N :=
  exists_orderOf_eq_iff_internal hN hm

theorem finiteOrders_eq {N : ℕ} (hN : 0 < N) : finiteOrders N = {m | 0 < m ∧ psi m ≤ N} :=
  finiteOrders_eq_internal hN

theorem isLeast_dimension {m : ℕ} (hm : 0 < m) :
    IsLeast {N | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m}
      (if m = 2 then 1 else psi m) :=
  isLeast_dimension_internal hm

theorem exists_orderOf_eq_totient {n : ℕ} (hn : 0 < n) :
    ∃ A : Matrix.GeneralLinearGroup (Fin (Nat.totient n)) ℤ, orderOf A = n :=
  exists_orderOf_eq_totient_internal hn

theorem exists_orderOf_eq_iff_rat {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℚ, orderOf A = m) ↔ psi m ≤ N :=
  exists_orderOf_eq_iff_rat_internal hN hm

theorem finiteOrders_zero : finiteOrders 0 = {1} :=
  finiteOrders_zero_internal

theorem finiteOrders_mono {N N' : ℕ} (h : N ≤ N') : finiteOrders N ⊆ finiteOrders N' :=
  finiteOrders_mono_internal h

theorem finiteOrders_succ_of_even {N : ℕ} (hN : 0 < N) (hN2 : Even N) :
    finiteOrders (N + 1) = finiteOrders N :=
  finiteOrders_succ_of_even_internal hN hN2

theorem le_two_pow_of_mem_finiteOrders {N m : ℕ} (h : m ∈ finiteOrders N) :
    m ≤ 2 ^ (N + 1) :=
  le_two_pow_of_mem_finiteOrders_internal h

theorem finiteOrders_finite (N : ℕ) : (finiteOrders N).Finite :=
  finiteOrders_finite_internal N

theorem exists_orderOf_eq_iff_sl {N m : ℕ} (hN : 2 ≤ N) (hm : 0 < m) :
    (∃ A : Matrix.SpecialLinearGroup (Fin N) ℤ, orderOf A = m) ↔ psi m ≤ N :=
  exists_orderOf_eq_iff_sl_internal hN hm

theorem orderOf_sl_one (A : Matrix.SpecialLinearGroup (Fin 1) ℤ) : orderOf A = 1 :=
  orderOf_sl_one_internal A

theorem finiteOrders_one : finiteOrders 1 = {1, 2} :=
  finiteOrders_one_internal

theorem finiteOrders_two : finiteOrders 2 = {1, 2, 3, 4, 6} :=
  finiteOrders_two_internal

theorem finiteOrders_three : finiteOrders 3 = {1, 2, 3, 4, 6} :=
  finiteOrders_three_internal

theorem finiteOrders_four : finiteOrders 4 = {1, 2, 3, 4, 5, 6, 8, 10, 12} :=
  finiteOrders_four_internal

theorem finiteOrders_five : finiteOrders 5 = {1, 2, 3, 4, 5, 6, 8, 10, 12} :=
  finiteOrders_five_internal

theorem finiteOrders_six :
    finiteOrders 6 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} :=
  finiteOrders_six_internal

theorem finiteOrders_seven :
    finiteOrders 7 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} :=
  finiteOrders_seven_internal

theorem finiteOrders_eight :
    finiteOrders 8 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40,
      42, 60} :=
  finiteOrders_eight_internal

theorem finiteOrders_nine :
    finiteOrders 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40,
      42, 60} :=
  finiteOrders_nine_internal

theorem finiteOrders_ten :
    finiteOrders 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 28, 30,
      35, 36, 40, 42, 45, 48, 56, 60, 70, 72, 84, 90, 120} :=
  finiteOrders_ten_internal

theorem finiteOrders_eleven :
    finiteOrders 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 28, 30,
      35, 36, 40, 42, 45, 48, 56, 60, 70, 72, 84, 90, 120} :=
  finiteOrders_eleven_internal

theorem finiteOrders_twelve :
    finiteOrders 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 26,
      28, 30, 33, 35, 36, 40, 42, 44, 45, 48, 56, 60, 63, 66, 70, 72, 80, 84, 90, 105, 120, 126, 140,
      168, 180, 210} :=
  finiteOrders_twelve_internal

theorem psi_2520 : psi 2520 = 20 :=
  psi_2520_internal

theorem psi_2310 : psi 2310 = 22 :=
  psi_2310_internal

theorem psi_eq_twentyfour :
    ∀ m ∈ ({2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620, 5040} : Finset ℕ), psi m = 24 :=
  psi_eq_twentyfour_internal

theorem isLeast_dimension_2520 :
    IsLeast {N | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = 2520} 20 :=
  isLeast_dimension_2520_internal

theorem isLeast_dimension_2310 :
    IsLeast {N | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = 2310} 22 :=
  isLeast_dimension_2310_internal

theorem isLeast_dimension_twentyfour :
    ∀ m ∈ ({2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620, 5040} : Finset ℕ),
      IsLeast {N | ∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ, orderOf A = m} 24 :=
  isLeast_dimension_twentyfour_internal

theorem isGreatest_finiteOrders_one : IsGreatest (finiteOrders 1) 2 :=
  isGreatest_finiteOrders_one_internal

theorem isGreatest_finiteOrders_two : IsGreatest (finiteOrders 2) 6 :=
  isGreatest_finiteOrders_two_internal

theorem isGreatest_finiteOrders_four : IsGreatest (finiteOrders 4) 12 :=
  isGreatest_finiteOrders_four_internal

theorem isGreatest_finiteOrders_six : IsGreatest (finiteOrders 6) 30 :=
  isGreatest_finiteOrders_six_internal

theorem isGreatest_finiteOrders_eight : IsGreatest (finiteOrders 8) 60 :=
  isGreatest_finiteOrders_eight_internal

theorem isGreatest_finiteOrders_ten : IsGreatest (finiteOrders 10) 120 :=
  isGreatest_finiteOrders_ten_internal

theorem isGreatest_finiteOrders_twelve : IsGreatest (finiteOrders 12) 210 :=
  isGreatest_finiteOrders_twelve_internal

theorem exists_odd_squarefree_psi_eq (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ Squarefree m ∧ psi m = 2 * n :=
  exists_odd_squarefree_psi_eq_internal n

theorem range_psi : Set.range psi = {n : ℕ | Even n} :=
  range_psi_internal

theorem finiteOrders_subset_iff {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    finiteOrders N ⊆ finiteOrders M ↔ N / 2 ≤ M / 2 :=
  finiteOrders_subset_iff_internal hN hM

theorem finiteOrders_eq_iff {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    finiteOrders N = finiteOrders M ↔ N / 2 = M / 2 :=
  finiteOrders_eq_iff_internal hN hM

theorem exists_new_odd_squarefree_order (n : ℕ) :
    ∃ m : ℕ, Odd m ∧ Squarefree m ∧
      m ∈ finiteOrders (2 * n + 2) ∧ m ∉ finiteOrders (2 * n + 1) :=
  exists_new_odd_squarefree_order_internal n

theorem exists_integral_invariant_posDef {N m : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin N) ℤ) (hm : 0 < m) (hA : orderOf A = m) :
    ∃ Q : Matrix (Fin N) (Fin N) ℤ,
      Q.IsSymm ∧ Q.PosDef ∧ ((Int.castRingHom ℝ).mapMatrix Q).PosDef ∧
        Matrix.transpose (A : Matrix (Fin N) (Fin N) ℤ) * Q *
          (A : Matrix (Fin N) (Fin N) ℤ) = Q :=
  exists_integral_invariant_posDef_internal A hm hA

theorem exists_integral_posDef_isometry_iff {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∃ A : Matrix.GeneralLinearGroup (Fin N) ℤ,
      ∃ Q : Matrix (Fin N) (Fin N) ℤ,
        orderOf A = m ∧ Q.IsSymm ∧ Q.PosDef ∧
          ((Int.castRingHom ℝ).mapMatrix Q).PosDef ∧
          Matrix.transpose (A : Matrix (Fin N) (Fin N) ℤ) * Q *
            (A : Matrix (Fin N) (Fin N) ℤ) = Q) ↔ psi m ≤ N :=
  exists_integral_posDef_isometry_iff_internal hN hm

end Crystallographic
