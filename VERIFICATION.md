# Verification

All fifty-three statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard, the
definition and statement checks, the standard-library replay of the tables, the metadata check, the module-resolution
check, the elaboration check and Palomar's core-notation audit of the statements pass; `python scripts/verify.py` runs
them all and ends with `VERIFY: PASS`. The expanded pre-submission tree was replayed under the pinned toolchain on 2026-10-10 UTC
(243 project constants audited; 55 declarations, the 53 theorems and the 2 definitions, printed by
the core-notation audit). A build log is evidence for its exact source tree only. Theorems are numbered
as in `comparator.json`, which is also their order in Challenge.lean. `comparator.json` lists no `definition_names`: a
name there is a definition hole whose value the Solution supplies; the two definitions here (`psi`, `finiteOrders`) are
fully specified in the Challenge, so the comparator checks the Solution's values against them.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `psi_eq_zero_iff` — ψ(m) = 0 iff m ≤ 2 | Crystallographic/Psi.lean |
| 2 | `psi_prime_pow` — ψ(pᵏ) = φ(pᵏ) for a prime power pᵏ ≠ 2 | Crystallographic/Psi.lean |
| 3 | `psi_mul` — ψ(ab) = ψ(a) + ψ(b) for coprime a, b | Crystallographic/Psi.lean |
| 4 | `psi_le_totient` — ψ(m) ≤ φ(m) | Crystallographic/Psi.lean |
| 5 | `even_psi` — ψ(m) is even | Crystallographic/Psi.lean |
| 6 | `psi_eq_sum_divisors` — ψ(m) as the sum of φ(d) over the exact prime-power divisors d ≠ 2 of m | Crystallographic/Psi.lean |
| 7 | `le_two_pow_psi` — m ≤ 2^(ψ(m) + 1) for m ≥ 1 | Crystallographic/Psi.lean |
| 8 | `psi_orderOf_le` — ψ(orderOf A) ≤ N for every A ∈ GL(N, ℤ) (necessity) | Crystallographic/Necessity.lean |
| 9 | `exists_orderOf_eq` — for N ≥ 1, m ≥ 1, ψ(m) ≤ N there is A ∈ GL(N, ℤ) of order m (sufficiency) | Crystallographic/Sufficiency.lean |
| 10 | `exists_orderOf_eq_iff` — the crystallographic restriction: for N ≥ 1, m ≥ 1, GL(N, ℤ) has an element of order m iff ψ(m) ≤ N | Crystallographic/Main.lean |
| 11 | `finiteOrders_eq` — the finite orders of GL(N, ℤ), N ≥ 1, are {m ≥ 1 : ψ(m) ≤ N} | Crystallographic/Main.lean |
| 12 | `isLeast_dimension` — the least N carrying an element of order m ≥ 1 is ψ(m), or 1 for m = 2 | Crystallographic/Main.lean |
| 13 | `exists_orderOf_eq_totient` — GL(φ(n), ℤ) has an element of order n, for every n ≥ 1 | Crystallographic/Block.lean |
| 14 | `exists_orderOf_eq_iff_rat` — the same restriction for GL(N, ℚ) | Crystallographic/Main.lean |
| 15 | `finiteOrders_zero` — GL(0, ℤ) has only the order 1 | Crystallographic/Extra.lean |
| 16 | `finiteOrders_mono` — the finite orders grow with the dimension | Crystallographic/Extra.lean |
| 17 | `finiteOrders_succ_of_even` — GL(N + 1, ℤ) has the same finite orders as GL(N, ℤ) for even N ≥ 2 | Crystallographic/Main.lean |
| 18 | `le_two_pow_of_mem_finiteOrders` — every finite order of GL(N, ℤ) is at most 2^(N + 1) | Crystallographic/Main.lean |
| 19 | `finiteOrders_finite` — the set of finite orders of GL(N, ℤ) is finite | Crystallographic/Main.lean |
| 20 | `exists_orderOf_eq_iff_sl` — the same restriction for SL(N, ℤ), N ≥ 2 | Crystallographic/SL.lean |
| 21 | `orderOf_sl_one` — SL(1, ℤ) is trivial: every element has order 1 | Crystallographic/SL.lean |
| 22 | `finiteOrders_one` — Ord₁ = {1, 2} | Crystallographic/Tables.lean |
| 23 | `finiteOrders_two` — Ord₂ = {1, 2, 3, 4, 6} | Crystallographic/Tables.lean |
| 24 | `finiteOrders_three` — Ord₃ = {1, 2, 3, 4, 6} | Crystallographic/Tables.lean |
| 25 | `finiteOrders_four` — Ord₄ = {1, 2, 3, 4, 5, 6, 8, 10, 12} | Crystallographic/Tables.lean |
| 26 | `finiteOrders_five` — Ord₅ = Ord₄ | Crystallographic/Tables.lean |
| 27 | `finiteOrders_six` — Ord₆, seventeen orders, largest 30 | Crystallographic/Tables.lean |
| 28 | `finiteOrders_seven` — Ord₇ = Ord₆ | Crystallographic/Tables.lean |
| 29 | `finiteOrders_eight` — Ord₈, twenty-four orders, largest 60 | Crystallographic/Tables.lean |
| 30 | `finiteOrders_nine` — Ord₉ = Ord₈ | Crystallographic/Tables.lean |
| 31 | `finiteOrders_ten` — Ord₁₀, thirty-five orders, largest 120 | Crystallographic/Tables.lean |
| 32 | `finiteOrders_eleven` — Ord₁₁ = Ord₁₀ | Crystallographic/Tables.lean |
| 33 | `finiteOrders_twelve` — Ord₁₂, forty-eight orders, largest 210 | Crystallographic/Tables.lean |
| 34 | `psi_2520` — ψ(2520) = 20 | Crystallographic/Erratum.lean |
| 35 | `psi_2310` — ψ(2310) = 22 | Crystallographic/Erratum.lean |
| 36 | `psi_eq_twentyfour` — ψ = 24 at 2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620, 5040 | Crystallographic/Erratum.lean |
| 37 | `isLeast_dimension_2520` — the least dimension with an element of order 2520 is 20 | Crystallographic/Erratum.lean |
| 38 | `isLeast_dimension_2310` — the least dimension with an element of order 2310 is 22 | Crystallographic/Erratum.lean |
| 39 | `isLeast_dimension_twentyfour` — the least dimension with an element of order 2184, …, 5040 is 24 | Crystallographic/Erratum.lean |
| 40 | `isGreatest_finiteOrders_one` — the largest finite order in GL(1, ℤ) is 2 | Crystallographic/Tables.lean |
| 41 | `isGreatest_finiteOrders_two` — 6 in GL(2, ℤ) | Crystallographic/Tables.lean |
| 42 | `isGreatest_finiteOrders_four` — 12 in GL(4, ℤ) | Crystallographic/Tables.lean |
| 43 | `isGreatest_finiteOrders_six` — 30 in GL(6, ℤ) | Crystallographic/Tables.lean |
| 44 | `isGreatest_finiteOrders_eight` — 60 in GL(8, ℤ) | Crystallographic/Tables.lean |
| 45 | `isGreatest_finiteOrders_ten` — 120 in GL(10, ℤ) | Crystallographic/Tables.lean |
| 46 | `isGreatest_finiteOrders_twelve` — 210 in GL(12, ℤ) | Crystallographic/Tables.lean |
| 47 | `exists_odd_squarefree_psi_eq` — every even value of ψ has a positive odd squarefree witness | Crystallographic/Extensions.lean |
| 48 | `range_psi` — the image of ψ is exactly the even naturals | Crystallographic/Extensions.lean |
| 49 | `finiteOrders_subset_iff` — positive-dimensional spectra are included exactly when the integer half-dimensions are ordered | Crystallographic/Extensions.lean |
| 50 | `finiteOrders_eq_iff` — positive-dimensional spectra agree exactly when their integer half-dimensions agree | Crystallographic/Extensions.lean |
| 51 | `exists_new_odd_squarefree_order` — an odd squarefree order first appears at each positive even dimension | Crystallographic/Extensions.lean |
| 52 | `exists_integral_invariant_posDef` — every finite-order integral matrix preserves an integral symmetric positive definite form, positive definite also over ℝ | Crystallographic/InvariantForm.lean |
| 53 | `exists_integral_posDef_isometry_iff` — ψ(m) ≤ N is realized by an isometry of a suitable integral positive definite form | Crystallographic/InvariantForm.lean |

## The checks and their limits

- **Pins.** `lean-toolchain` and the Mathlib revision of `lake-manifest.json` are the committed ones.
- **Build.** `lake build` of the four targets `Crystallographic`, `Challenge`, `Solution`, `Test` under the pinned
  toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (`065356127b1dc0016f66b7283ce0ce2c4055aa55`).
  Every proof is checked by Lean's kernel; the tables use `decide +kernel` on a structurally recursive `psiC` proved
  equal to `psi`. No `native_decide`.
- **Axiom audit** (`Test/Axioms.lean`): every constant of the development depends on no axiom beyond `propext`,
  `Classical.choice`, `Quot.sound`; it fails on fewer than 200 constants or a missing compared theorem.
- **Source guard** (`scripts/check-source.py`): no `sorry`, `axiom`, `native_decide`, `unsafe`, `partial`, `mutual`,
  `opaque`, `implemented_by`, `extern`, kernel-bypass options, in the development, the Solution and the Test.
- **Definitions and statements** (`scripts/check_definitions.py`, `scripts/check_statements.py`): the two definitions of
  Challenge.lean appear character for character in `Crystallographic/Defs.lean` under the same import; every theorem
  header of Challenge.lean appears verbatim in Solution.lean, which does not import the Challenge.
- **Elaboration check**: `psi` and `finiteOrders` printed with `pp.all` from `Challenge` and from
  `Crystallographic.Defs` are identical (the registry's comparator judges the elaborated constants).
- **Palomar's core-notation audit** (`scripts/core_notation_audit.lean`, unmodified apart from a three-line provenance
  comment): every compared declaration renders with Mathlib's constants as opaque axioms.
- **Metadata** (`scripts/verify.py`): formalization.yaml parses; the title is at most 300 characters; `main_results` and
  `alignment.statements` match comparator.json in exact order (the consult tightened the latter check); no definition holes; no original-proof source.
- **Standard-library replay** (`scripts/check_tables.py`): ψ from the factorization against the divisor-sum form to
  3000; the zero set, parity, `ψ ≤ φ` and `m ≤ 2^(ψ(m) + 1)` to 10⁵; additivity for coprime `a, b < 2000` with
  `ab ≤ 10⁵`; the twelve order sets by the bound and by brute force to 10⁵ against the literals of Challenge.lean; the
  maxima; every row of Table 1 of Bamberg–Cairns–Kilminster re-derived by the structural enumeration (checked against
  brute force for `n ≤ 14`) and compared with the printed row, with exactly the eleven omissions the theorems state.
- **Module resolution** (`scripts/check_module_resolution.py`, under `lake env`): `Challenge` and `Solution` resolve to
  this repository's files first in `LEAN_SRC_PATH`.
- **Not checked here**: literature status or priority (the registry certifies statement matching and kernel replay
  only); the statements of the sources beyond the pages cited in formalization.yaml; that the eleven values are the only
  omissions from Table 1 is a computation outside Lean, not a theorem.

## Consult replay and additional mathematical notes

The full local entry point `python scripts/verify.py` passed after the seven compared theorems were
integrated, including the build of all four targets, the axiom audit, definition elaboration and
core-notation audit. The original mathematical results were retained. The isolated intentional
placeholders in `Challenge.lean` are excluded from proof counts and from `Solution.lean`'s proof
dependency graph; `Solution.lean` never imports it.

This hosted runner virtualizes process IDs while exposing the standard `/proc/self/exe` alias.
The unchanged Linux Lean executable initially failed when its runtime queried `/proc/<getpid()>/exe`.
The consult used a small libc `readlink` adapter mapping only that own-process executable-path
query to `/proc/self/exe`. It did not intercept Lean functions or proof operations, and no compiler,
kernel, Mathlib source, or proof-checking option was changed. Its source and the replay log are
included in the consult package for reproducibility; ordinary local Lean installations do not need
this runner-specific adapter.

`MATHEMATICAL-EXTENSIONS.md` is explicitly outside the compared Lean scope. Its standard-library
verifier `python scripts/check_minimal_classes.py` and its `python -O` replay both pass for orders
1 through 500: 869 minimum-dimensional rational conjugacy classes in total, with every proposed
class construction and determinant-minus-one minimum dimension agreeing with exhaustive cyclotomic
multiset enumeration. This finite check does not certify the statements for all orders; the
all-orders evidence supplied there is the written mathematical proof.

[SOURCES.md](SOURCES.md) gives the direct source-reading audit. Reading the recovered originals
changes the bibliographic evidence, rather than the Lean verification gate. The Palomar submission
service's own comparator and independent checker remain part of the registry's submission process;
the local script does not claim to have run that hosted process.
