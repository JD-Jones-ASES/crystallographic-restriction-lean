# Verification

All thirty-six statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard, the
definition and statement checks, the standard-library replay of the tables, the metadata check, the module-resolution
check, the elaboration check and Palomar's core-notation audit of the statements pass; `python scripts/verify.py` runs
them all and ends with `VERIFY: PASS`. The checks below were last run on the tree of the final commit (CONSTANTS_PLACEHOLDER
project constants audited, 38 declarations printed); a build log is evidence for that tree only. Theorems are numbered
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
| 12 | `isLeast_dimension` — the least N carrying an element of order m is ψ(m), or 1 for m = 2 | Crystallographic/Main.lean |
| 13 | `exists_orderOf_eq_totient` — GL(φ(n), ℤ) has an element of order n, for every n ≥ 1 | Crystallographic/Block.lean |
| 14 | `exists_orderOf_eq_iff_rat` — the same restriction for GL(N, ℚ) | Crystallographic/Main.lean |
| 15 | `finiteOrders_succ_of_even` — GL(N + 1, ℤ) has the finite orders of GL(N, ℤ) for even N ≥ 2 | Crystallographic/Main.lean |
| 16 | `le_two_pow_of_mem_finiteOrders` — every finite order of GL(N, ℤ) is at most 2^(N + 1) | Crystallographic/Main.lean |
| 17 | `finiteOrders_finite` — the set of finite orders of GL(N, ℤ) is finite | Crystallographic/Main.lean |
| 18 | `finiteOrders_one` — Ord₁ = {1, 2} | Crystallographic/Tables.lean |
| 19 | `finiteOrders_two` — Ord₂ = {1, 2, 3, 4, 6} | Crystallographic/Tables.lean |
| 20 | `finiteOrders_three` — Ord₃ = {1, 2, 3, 4, 6} | Crystallographic/Tables.lean |
| 21 | `finiteOrders_four` — Ord₄ = {1, 2, 3, 4, 5, 6, 8, 10, 12} | Crystallographic/Tables.lean |
| 22 | `finiteOrders_five` — Ord₅ = Ord₄ | Crystallographic/Tables.lean |
| 23 | `finiteOrders_six` — Ord₆, seventeen orders, largest 30 | Crystallographic/Tables.lean |
| 24 | `finiteOrders_seven` — Ord₇ = Ord₆ | Crystallographic/Tables.lean |
| 25 | `finiteOrders_eight` — Ord₈, twenty-four orders, largest 60 | Crystallographic/Tables.lean |
| 26 | `finiteOrders_nine` — Ord₉ = Ord₈ | Crystallographic/Tables.lean |
| 27 | `finiteOrders_ten` — Ord₁₀, thirty-five orders, largest 120 | Crystallographic/Tables.lean |
| 28 | `finiteOrders_eleven` — Ord₁₁ = Ord₁₀ | Crystallographic/Tables.lean |
| 29 | `finiteOrders_twelve` — Ord₁₂, forty-eight orders, largest 210 | Crystallographic/Tables.lean |
| 30 | `isGreatest_finiteOrders_one` — the largest finite order in GL(1, ℤ) is 2 | Crystallographic/Tables.lean |
| 31 | `isGreatest_finiteOrders_two` — 6 in GL(2, ℤ) | Crystallographic/Tables.lean |
| 32 | `isGreatest_finiteOrders_four` — 12 in GL(4, ℤ) | Crystallographic/Tables.lean |
| 33 | `isGreatest_finiteOrders_six` — 30 in GL(6, ℤ) | Crystallographic/Tables.lean |
| 34 | `isGreatest_finiteOrders_eight` — 60 in GL(8, ℤ) | Crystallographic/Tables.lean |
| 35 | `isGreatest_finiteOrders_ten` — 120 in GL(10, ℤ) | Crystallographic/Tables.lean |
| 36 | `isGreatest_finiteOrders_twelve` — 210 in GL(12, ℤ) | Crystallographic/Tables.lean |

## The checks and their limits

- **Build.** `lake build` of the four targets `Crystallographic`, `Challenge`, `Solution`, `Test` under the pinned
  toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (`065356127b1dc0016f66b7283ce0ce2c4055aa55`).
  Every proof is checked by Lean's kernel; the tables use `decide +kernel` on a structurally recursive `psiC` proved
  equal to `psi`. No `native_decide`.
- **Axiom audit** (`Test/Axioms.lean`): every constant of the development depends on no axiom beyond `propext`,
  `Classical.choice`, `Quot.sound`; it fails on fewer than 40 constants or a missing compared theorem.
- **Source guard** (`scripts/check-source.py`): no `sorry`, `axiom`, `native_decide`, `unsafe`, `partial`, `mutual`,
  `opaque`, `implemented_by`, `extern`, kernel-bypass options, in the development, the Solution and the Test.
- **Definitions and statements** (`scripts/check_definitions.py`, `scripts/check_statements.py`): the two definitions of
  Challenge.lean appear character for character in `Crystallographic/Defs.lean` under the same import; every theorem
  header of Challenge.lean appears verbatim in Solution.lean, which does not import the Challenge.
- **Elaboration check**: `psi` and `finiteOrders` printed with `pp.all` from `Challenge` and from
  `Crystallographic.Defs` are identical (the registry's comparator judges the elaborated constants).
- **Palomar's core-notation audit** (`scripts/core_notation_audit.lean`, an unmodified copy): every compared
  declaration renders with Mathlib's constants as opaque axioms.
- **Standard-library replay** (`scripts/check_tables.py`): ψ by two routes to 3000; the arithmetic statements to 10⁵;
  the twelve order sets by the bound and by brute force to 10⁵ against the literals of Challenge.lean; the maxima.
- **Module resolution** (`scripts/check_module_resolution.py`, under `lake env`): `Challenge` and `Solution` resolve to
  this repository's files first in `LEAN_SRC_PATH`.
- **Not checked here**: literature status or priority (the registry certifies statement matching and kernel replay
  only); the statements of the sources beyond what is quoted in PROOF.md.
