module

public import Crystallographic.Main
public import Crystallographic.Compute

/-!
# The tables

`finiteOrders N = {m | 0 < m ∧ psi m ≤ N}` (`finiteOrders_eq_internal`), `m ≤ 2 ^ (N + 1)` for
`psi m ≤ N` (`le_two_pow_psi_internal`), and `psi = psiC` (`psiC_eq_psi`). One kernel check
(`tbl_chunks12`, chunked to bound the kernel's recursion depth) shows that below `8193` the orders
with `psiC m ≤ 12` are exactly the `48` members of `tbl_L12`; every table `N ≤ 12` is then cut out
of that list by a `decide +kernel` over its `48` members (`tbl_table`), and each maximum reads off
its list.
-/

@[expose] public section

namespace Crystallographic

/-- The `48` orders `m` with `ψ(m) ≤ 12`. -/
def tbl_L12 : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 26, 28, 30, 33,
   35, 36, 40, 42, 44, 45, 48, 56, 60, 63, 66, 70, 72, 80, 84, 90, 105, 120, 126, 140, 168, 180,
   210]

/-- The kernel check, chunked (`512 * i + k`, `i < 17`, `k < 512`) to keep the kernel's recursion
depth bounded: below `8704`, `0 < m ∧ psiC m ≤ 12` holds exactly on `tbl_L12`. -/
theorem tbl_chunks12 : ∀ i, i < 17 → ∀ k, k < 512 →
    (0 < 512 * i + k ∧ psiC (512 * i + k) ≤ 12 ↔ 512 * i + k ∈ tbl_L12) := by
  decide +kernel

theorem tbl_key12 : ∀ m, m < 8193 → (0 < m ∧ psiC m ≤ 12 ↔ m ∈ tbl_L12) := by
  intro m hm
  have h := tbl_chunks12 (m / 512) (by omega) (m % 512) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

/-- Every table `N ≤ 12` is cut out of `tbl_L12`: if `psiC m ≤ N` holds on `tbl_L12` exactly for
the members of `L`, and `L ⊆ tbl_L12`, then `finiteOrders N` is the set of members of `L`. -/
theorem tbl_table {N : ℕ} (hN : 0 < N) (hN12 : N ≤ 12) (L : List ℕ)
    (hcut : ∀ m ∈ tbl_L12, (psiC m ≤ N ↔ m ∈ L)) (hsub : ∀ m ∈ L, m ∈ tbl_L12) :
    finiteOrders N = {m | m ∈ L} := by
  have hbig : ∀ m ∈ tbl_L12, m < 8193 := by decide +kernel
  rw [finiteOrders_eq_internal hN]
  ext m
  show (0 < m ∧ psi m ≤ N) ↔ m ∈ L
  constructor
  · rintro ⟨hm, h⟩
    have hb := le_two_pow_psi_internal hm
    have hp : 2 ^ (psi m + 1) ≤ 2 ^ 13 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h13 : (2 : ℕ) ^ 13 = 8192 := by norm_num
    have hmem : m ∈ tbl_L12 :=
      (tbl_key12 m (by omega)).1 ⟨hm, by rw [psiC_eq_psi]; omega⟩
    exact (hcut m hmem).1 (by rw [psiC_eq_psi]; exact h)
  · intro h
    have hmem := hsub m h
    have h' := (tbl_key12 m (hbig m hmem)).2 hmem
    exact ⟨h'.1, by rw [← psiC_eq_psi]; exact (hcut m hmem).2 h⟩

theorem tbl_isGreatest {N M : ℕ} {L : List ℕ} (h : finiteOrders N = {m | m ∈ L}) (hM : M ∈ L)
    (hle : ∀ m ∈ L, m ≤ M) : IsGreatest (finiteOrders N) M := by
  rw [h]
  exact ⟨hM, fun m hm => hle m hm⟩

theorem tbl_list_one : finiteOrders 1 = {m | m ∈ [1, 2]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_two : finiteOrders 2 = {m | m ∈ [1, 2, 3, 4, 6]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_three : finiteOrders 3 = {m | m ∈ [1, 2, 3, 4, 6]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_four : finiteOrders 4 = {m | m ∈ [1, 2, 3, 4, 5, 6, 8, 10, 12]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_five : finiteOrders 5 = {m | m ∈ [1, 2, 3, 4, 5, 6, 8, 10, 12]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_six : finiteOrders 6 = {m | m ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_seven : finiteOrders 7 = {m | m ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_eight : finiteOrders 8 = {m | m ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40, 42, 60]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_nine : finiteOrders 9 = {m | m ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40, 42, 60]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_ten : finiteOrders 10 = {m | m ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 28, 30, 35, 36, 40,
    42, 45, 48, 56, 60, 70, 72, 84, 90, 120]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_eleven : finiteOrders 11 = {m | m ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 28, 30, 35, 36, 40,
    42, 45, 48, 56, 60, 70, 72, 84, 90, 120]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem tbl_list_twelve : finiteOrders 12 = {m | m ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 26, 28, 30, 33,
    35, 36, 40, 42, 44, 45, 48, 56, 60, 63, 66, 70, 72, 80, 84, 90, 105, 120, 126, 140, 168,
    180, 210]} :=
  tbl_table (by norm_num) (by norm_num) _ (by decide +kernel) (by decide +kernel)

theorem finiteOrders_one_internal : finiteOrders 1 = {1, 2} := by
  rw [tbl_list_one]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_two_internal : finiteOrders 2 = {1, 2, 3, 4, 6} := by
  rw [tbl_list_two]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_three_internal : finiteOrders 3 = {1, 2, 3, 4, 6} := by
  rw [tbl_list_three]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_four_internal : finiteOrders 4 = {1, 2, 3, 4, 5, 6, 8, 10, 12} := by
  rw [tbl_list_four]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_five_internal : finiteOrders 5 = {1, 2, 3, 4, 5, 6, 8, 10, 12} := by
  rw [tbl_list_five]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_six_internal :
    finiteOrders 6 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} := by
  rw [tbl_list_six]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_seven_internal :
    finiteOrders 7 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} := by
  rw [tbl_list_seven]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_eight_internal :
    finiteOrders 8 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40,
      42, 60} := by
  rw [tbl_list_eight]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_nine_internal :
    finiteOrders 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40,
      42, 60} := by
  rw [tbl_list_nine]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_ten_internal :
    finiteOrders 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 28, 30,
      35, 36, 40, 42, 45, 48, 56, 60, 70, 72, 84, 90, 120} := by
  rw [tbl_list_ten]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_eleven_internal :
    finiteOrders 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 28, 30,
      35, 36, 40, 42, 45, 48, 56, 60, 70, 72, 84, 90, 120} := by
  rw [tbl_list_eleven]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem finiteOrders_twelve_internal :
    finiteOrders 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 26,
      28, 30, 33, 35, 36, 40, 42, 44, 45, 48, 56, 60, 63, 66, 70, 72, 80, 84, 90, 105, 120, 126, 140,
      168, 180, 210} := by
  rw [tbl_list_twelve]
  ext m
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem isGreatest_finiteOrders_one_internal : IsGreatest (finiteOrders 1) 2 :=
  tbl_isGreatest tbl_list_one (by decide) (by decide)

theorem isGreatest_finiteOrders_two_internal : IsGreatest (finiteOrders 2) 6 :=
  tbl_isGreatest tbl_list_two (by decide) (by decide)

theorem isGreatest_finiteOrders_four_internal : IsGreatest (finiteOrders 4) 12 :=
  tbl_isGreatest tbl_list_four (by decide) (by decide)

theorem isGreatest_finiteOrders_six_internal : IsGreatest (finiteOrders 6) 30 :=
  tbl_isGreatest tbl_list_six (by decide) (by decide)

theorem isGreatest_finiteOrders_eight_internal : IsGreatest (finiteOrders 8) 60 :=
  tbl_isGreatest tbl_list_eight (by decide) (by decide)

theorem isGreatest_finiteOrders_ten_internal : IsGreatest (finiteOrders 10) 120 :=
  tbl_isGreatest tbl_list_ten (by decide) (by decide)

theorem isGreatest_finiteOrders_twelve_internal : IsGreatest (finiteOrders 12) 210 :=
  tbl_isGreatest tbl_list_twelve (by decide) (by decide)

end Crystallographic
