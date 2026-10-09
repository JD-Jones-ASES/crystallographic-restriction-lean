module

public import Crystallographic.Main
public import Crystallographic.Compute

/-!
# The tables

`finiteOrders N = {m | 0 < m ∧ psi m ≤ N}` (`finiteOrders_eq_internal`), `m ≤ 2 ^ (N + 1)` for
`psi m ≤ N` (`le_two_pow_psi_internal`), and `psi = psiC` (`psiC_eq_psi`); so each table is a
`decide +kernel` over `m < 2 ^ (N + 1)` of `psiC m ≤ N ↔ m ∈ table`, and each maximum reads off
its table. Lane: **tables**.
-/

@[expose] public section

namespace Crystallographic

theorem finiteOrders_one_internal : finiteOrders 1 = {1, 2} := sorry

theorem finiteOrders_two_internal : finiteOrders 2 = {1, 2, 3, 4, 6} := sorry

theorem finiteOrders_three_internal : finiteOrders 3 = {1, 2, 3, 4, 6} := sorry

theorem finiteOrders_four_internal : finiteOrders 4 = {1, 2, 3, 4, 5, 6, 8, 10, 12} := sorry

theorem finiteOrders_five_internal : finiteOrders 5 = {1, 2, 3, 4, 5, 6, 8, 10, 12} := sorry

theorem finiteOrders_six_internal :
    finiteOrders 6 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} := sorry

theorem finiteOrders_seven_internal :
    finiteOrders 7 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} := sorry

theorem finiteOrders_eight_internal :
    finiteOrders 8 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40,
      42, 60} := sorry

theorem finiteOrders_nine_internal :
    finiteOrders 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40,
      42, 60} := sorry

theorem finiteOrders_ten_internal :
    finiteOrders 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 28, 30,
      35, 36, 40, 42, 45, 48, 56, 60, 70, 72, 84, 90, 120} := sorry

theorem finiteOrders_eleven_internal :
    finiteOrders 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 28, 30,
      35, 36, 40, 42, 45, 48, 56, 60, 70, 72, 84, 90, 120} := sorry

theorem finiteOrders_twelve_internal :
    finiteOrders 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 26,
      28, 30, 33, 35, 36, 40, 42, 44, 45, 48, 56, 60, 63, 66, 70, 72, 80, 84, 90, 105, 120, 126, 140,
      168, 180, 210} := sorry

theorem isGreatest_finiteOrders_one_internal : IsGreatest (finiteOrders 1) 2 := sorry

theorem isGreatest_finiteOrders_two_internal : IsGreatest (finiteOrders 2) 6 := sorry

theorem isGreatest_finiteOrders_four_internal : IsGreatest (finiteOrders 4) 12 := sorry

theorem isGreatest_finiteOrders_six_internal : IsGreatest (finiteOrders 6) 30 := sorry

theorem isGreatest_finiteOrders_eight_internal : IsGreatest (finiteOrders 8) 60 := sorry

theorem isGreatest_finiteOrders_ten_internal : IsGreatest (finiteOrders 10) 120 := sorry

theorem isGreatest_finiteOrders_twelve_internal : IsGreatest (finiteOrders 12) 210 := sorry

end Crystallographic
