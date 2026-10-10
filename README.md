# The crystallographic restriction in every dimension: for N, m ≥ 1, GL(N, ℤ) has an element of order m if and only if ψ(m) ≤ N

For a positive integer `m` let `ψ(m)` be the sum of `φ(pᵏ)` over the prime powers `pᵏ` exactly dividing `m`, except that
the prime power `2` contributes `0` (`φ` is Euler's totient; `ψ(1) = ψ(2) = 0`, `ψ(3) = ψ(4) = ψ(6) = 2`,
`ψ(5) = ψ(8) = ψ(10) = ψ(12) = 4`, `ψ(ab) = ψ(a) + ψ(b)` for coprime `a, b`; OEIS A080737). The crystallographic
restriction in every dimension states that for `N ≥ 1` the group `GL(N, ℤ)` of invertible integer `N × N` matrices has an
element of order `m ≥ 1` if and only if `ψ(m) ≤ N` (Vaidyanathaswamy, J. London Math. Soc. 3 (1928) 121–124 and
268–272, Theorem I on p. 268; Hiller, Acta Cryst. A41 (1985) 541–544; a proof in Kuzmanovich–Pavlichenkov, Amer. Math.
Monthly 109 (2002) 173–186; Theorem 1 of Bamberg–Cairns–Kilminster, Amer. Math. Monthly 110 (2003) 202–209). In
dimensions two and three this is the classical restriction: the finite orders are `1, 2, 3, 4, 6`.

[Challenge.lean](Challenge.lean) defines `ψ` (`psi`) and the set `finiteOrders N` of finite orders of elements of
`GL(N, ℤ)` and states fifty-six theorems; [Solution.lean](Solution.lean) proves them, kernel-only; the table in
[VERIFICATION.md](VERIFICATION.md) names each:

- the arithmetic of `ψ`: `ψ(m) = 0` iff `m ≤ 2`; `ψ(pᵏ) = φ(pᵏ)` for a prime power `pᵏ ≠ 2`; additivity on coprime
  factors; `ψ ≤ φ`; `ψ` even; `ψ` as a sum over the exact prime-power divisors; `m ≤ 2^(ψ(m) + 1)`;
- necessity: `ψ(orderOf A) ≤ N` for every `A ∈ GL(N, ℤ)`, through the minimal polynomial over `ℚ`, a product of distinct
  cyclotomic polynomials whose indices have least common multiple `orderOf A`;
- sufficiency: for `N ≥ 1`, `m ≥ 1`, `ψ(m) ≤ N`, an element of order `m` — one block of size `φ(pᵏ)` per prime power
  `pᵏ ≠ 2` of `m` (multiplication by the root on `ℤ[X]/(Φ_{pᵏ})`), the sign when `m ≡ 2 (mod 4)`, an identity block;
- the equivalence; `finiteOrders N = {m | 0 < m ∧ ψ(m) ≤ N}`; the least dimension carrying an element of order `m`
  (`ψ(m)`, or `1` for `m = 2`); an element of `GL(φ(n), ℤ)` of order `n` for every `n ≥ 1`; the same equivalence over `ℚ`;
  `GL(0, ℤ)` has only the order `1`, and the finite orders grow with the dimension; `GL(N + 1, ℤ)` has the same finite
  orders as `GL(N, ℤ)` for even `N ≥ 2`; the set of finite orders is finite, bounded by `2^(N + 1)`;
- the same equivalence in `SL(N, ℤ)` for `N ≥ 2` (an element of odd order has determinant `1`; the block for `2ᵏ`,
  `k ≥ 2`, has even size and determinant `1`; `−A` keeps the determinant in even dimension), and `SL(1, ℤ)` is trivial;
- the tables of finite orders for `N = 1, …, 12` (OEIS A080738) and the largest finite order `2, 6, 12, 30, 60, 120, 210`
  in dimensions `1, 2, 4, 6, 8, 10, 12`, by the bound and a kernel computation of `ψ`; beyond dimension 12, the eleven
  orders with `ψ = 20, 22, 24` missing from Table 1 of Bamberg–Cairns–Kilminster, with their least dimensions;
- every even number is `ψ(m)` for an odd squarefree `m ≥ 1` (Proposition 3(2) of Bamberg–Cairns–Kilminster and its
  proof), so the values of `ψ` are the even numbers; for `N, M ≥ 1`, `finiteOrders N ⊆ finiteOrders M` iff
  `N / 2 ≤ M / 2`, and `finiteOrders N = finiteOrders M` iff `N / 2 = M / 2`; `GL(2n + 2, ℤ)` has an odd squarefree
  finite order that `GL(2n + 1, ℤ)` lacks;
- every `A ∈ GL(N, ℤ)` of finite order `m` preserves a symmetric integral form (`∑_{k<m} (Aᵏ)ᵀAᵏ`), positive definite on
  integer and on real vectors; so, for `N, m ≥ 1`, some element of order `m` of `GL(N, ℤ)` preserves a positive definite
  integral form iff `ψ(m) ≤ N`;
- determinant `−1`: for `m ≥ 1`, `GL(N, ℤ)` has an element of order `m` and determinant `−1` iff `m` is even and
  `N ≥ ψ(m) + 1`, so the least such dimension is `ψ(m) + 1` for even `m`; the same in `GL(N, ℚ)`. Necessity goes
  through the invariant form: `AᵀQA = Q` gives `det(A + 1) = −det(A + 1)`, so `−1` is an eigenvalue and `Φ₂` divides
  the minimal polynomial; sufficiency is `diag(−1, B)` with `B ∈ SL(ψ(m), ℤ)` of order `m`.

The hypotheses `N ≥ 1` and `m ≥ 1` are necessary and made explicit: `GL(0, ℤ)` is trivial while `ψ(2) = 0`, and Mathlib's
`orderOf` is `0` at infinite order.

On paper, not in Lean ([PROOF.md](PROOF.md) §12): for `m > 2`, the elements of order `m` of `GL(ψ(m), ℤ)` fall into
`1`, `2^r − 1`, `2^r` or `3·2^(r−1)` classes under conjugacy in `GL(ψ(m), ℚ)`, `r` being the number of odd primes
dividing `m` (for `m` odd; `m ≡ 2 (mod 4)`; `4 ∣ m` otherwise; `4 ∥ m` and `3 ∥ m`). `scripts/check_minimal_classes.py`
checks this, and the determinant `−1` threshold, by exhaustive enumeration for every `m ≤ 500`.

Not claimed: priority for the two- and three-dimensional cases (public Lean proofs of the case `N = 2` exist:
acprk/symmetry-graded-lean, akiselev/ferris-howard); the wallpaper or space groups; the isometry group of a given lattice
or form; integral conjugacy; the classes of PROOF.md §12 as Lean theorems.

The theorem is the standard description of the finite orders of integer matrices, used in the crystallography of
higher-dimensional lattices and quasicrystals and in integral representation theory; Mathlib's `docs/1000.yaml`
(Q3527223) and mathlib4 issue #6091 (item 60) list it unformalized.

> As of 2026-10-09 (UTC), no formalization of the crystallographic restriction in every dimension, in either direction,
> was located in the Palomar registry, Mathlib (whose `docs/1000.yaml` entry Q3527223 lists the theorem with no
> declaration, and whose issue #6091 item 60 lists the necessity direction as a target), TauCeti, ATLAS, lean-eval,
> LeanPool, formal-conjectures, openai/math, Hexagon, the Isabelle AFP, GitHub's Lean, Isabelle and Rocq code, or arXiv.
> The case `N = 2` is formalized in acprk/symmetry-graded-lean and in akiselev/ferris-howard (both unregistered), and a
> trace form for rotations of `ℚ³` in the Rocq development Horsocrates/theory-of-systems-coq. Submissions under review at
> Palomar are not visible in its data API.

The tables for `N ≤ 12` agree with rows `n ≤ 12` of Table 1 of Bamberg–Cairns–Kilminster, with OEIS A080738 (the rows
`ψ⁻¹{2k}`), A080740 (the number of finite orders) and A005417 (the largest finite order); the least dimension is OEIS
A152455 and `ψ` is A080737. Rows `n = 20, 22, 24` of that Table 1 omit every value above `2000` (`2520`; `2310`;
`2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620, 5040`; the largest entry printed in the table is `1980`); the six
statements `psi_2520` … `isLeast_dimension_twentyfour` of the section "Beyond dimension 12" of Challenge.lean check
these values of `ψ`, and the least dimensions they give, in the kernel; `scripts/check_tables.py` re-derives every row
of the table and lists the omissions.

Lean `v4.35.0-rc2` (lean-toolchain) and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`, the
committed manifest) are pinned; there are no GitHub Actions workflows. `python scripts/verify.py --fetch-cache` runs every
check (pins, source guard, definition and statement comparisons, the standard-library replays of the tables and of the
enumeration for PROOF.md §12, the metadata check, the build with the axiom audit, module resolution, the elaboration check
of the two definitions, Palomar's core-notation audit);
[VERIFICATION.md](VERIFICATION.md) lists them and their limits, [PROOF.md](PROOF.md) gives the mathematics with the Lean
name of every step, and [DISCLOSURE.md](DISCLOSURE.md) the assistance statement.

License: [MIT](LICENSE) for the Lean files and scripts; `scripts/core_notation_audit.lean` is Palomar's, under its MIT
licence ([LICENSES/PalomarSubmission-MIT.txt](LICENSES/PalomarSubmission-MIT.txt)).
