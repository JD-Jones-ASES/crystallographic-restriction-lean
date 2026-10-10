# The crystallographic restriction in every dimension: GL(N, ℤ) has an element of order m if and only if ψ(m) ≤ N

For a positive integer `m` let `ψ(m)` be the sum of `φ(pᵏ)` over the prime powers `pᵏ` exactly dividing `m`, except that
the prime power `2` contributes `0` (`φ` is Euler's totient; `ψ(1) = ψ(2) = 0`, `ψ(3) = ψ(4) = ψ(6) = 2`,
`ψ(5) = ψ(8) = ψ(10) = ψ(12) = 4`, `ψ(ab) = ψ(a) + ψ(b)` for coprime `a, b`; OEIS A080737). The crystallographic
restriction in every dimension states that for `N ≥ 1` the group `GL(N, ℤ)` of invertible integer `N × N` matrices has an
element of order `m ≥ 1` if and only if `ψ(m) ≤ N` (Vaidyanathaswamy, J. London Math. Soc. 3 (1928) 121–124; Hiller,
Acta Cryst. A41 (1985) 541–544; a proof in Kuzmanovich–Pavlichenkov, Amer. Math. Monthly 109 (2002) 173–186; Theorem 1 of
Bamberg–Cairns–Kilminster, Amer. Math. Monthly 110 (2003) 202–209). In dimensions two and three this is the classical
restriction: the finite orders are `1, 2, 3, 4, 6`.

[Challenge.lean](Challenge.lean) defines `ψ` (`psi`) and the set `finiteOrders N` of finite orders of elements of
`GL(N, ℤ)` and states forty-six theorems; [Solution.lean](Solution.lean) proves them, kernel-only; the table in
[VERIFICATION.md](VERIFICATION.md) names each:

- the arithmetic of `ψ`: `ψ(m) = 0` iff `m ≤ 2`; `ψ(pᵏ) = φ(pᵏ)` for a prime power `pᵏ ≠ 2`; additivity on coprime
  factors; `ψ ≤ φ`; `ψ` even; `ψ` as a sum over the exact prime-power divisors; `m ≤ 2^(ψ(m) + 1)`;
- necessity: `ψ(orderOf A) ≤ N` for every `A ∈ GL(N, ℤ)`, through the minimal polynomial over `ℚ`, a product of distinct
  cyclotomic polynomials whose indices have least common multiple `orderOf A`;
- sufficiency: for `N ≥ 1`, `m ≥ 1`, `ψ(m) ≤ N`, an element of order `m` — one block of size `φ(pᵏ)` per prime power
  `pᵏ ≠ 2` of `m` (multiplication by the root on `ℤ[X]/(Φ_{pᵏ})`), the sign when `m ≡ 2 (mod 4)`, an identity block;
- the equivalence; `finiteOrders N = {m | 0 < m ∧ ψ(m) ≤ N}`; the least dimension carrying an element of order `m`
  (`ψ(m)`, or `1` for `m = 2`); an element of `GL(φ(n), ℤ)` of order `n` for every `n ≥ 1`; the same equivalence over `ℚ`;
  `GL(0, ℤ)` has only the order `1`, and the finite orders grow with the dimension; `GL(N + 1, ℤ)` has the finite orders
  of `GL(N, ℤ)` for even `N ≥ 2`; the set of finite orders is finite, bounded by `2^(N + 1)`;
- the same equivalence in `SL(N, ℤ)` for `N ≥ 2` (an element of odd order has determinant `1`; the block for `2ᵏ`,
  `k ≥ 2`, has even size and determinant `1`; `−A` keeps the determinant in even dimension), and `SL(1, ℤ)` is trivial;
- the tables of finite orders for `N = 1, …, 12` (OEIS A080738) and the largest finite order `2, 6, 12, 30, 60, 120, 210`
  in dimensions `1, 2, 4, 6, 8, 10, 12`, by the bound and a kernel computation of `ψ`; beyond dimension 12, the eleven
  orders with `ψ = 20, 22, 24` missing from Table 1 of Bamberg–Cairns–Kilminster, with their least dimensions.

The hypotheses `N ≥ 1` and `m ≥ 1` are necessary and made explicit: `GL(0, ℤ)` is trivial while `ψ(2) = 0`, and Mathlib's
`orderOf` is `0` at infinite order.

Not claimed: the two-dimensional case as a first (it is in public Lean, acprk/symmetry-graded-lean and
akiselev/ferris-howard); the wallpaper or space groups; isometry groups.

> As of 2026-10-09 (UTC), no formalization of the crystallographic restriction in every dimension, in either direction,
> was located in the Palomar registry, Mathlib (whose `docs/1000.yaml` entry Q3527223 lists the theorem with no
> declaration, and whose issue #6091 item 60 lists the necessity direction as a target), TauCeti, ATLAS, lean-eval,
> LeanPool, formal-conjectures, openai/math, Hexagon, the Isabelle AFP, GitHub's Lean, Isabelle and Rocq code, or arXiv.
> The case `N = 2` is formalized in acprk/symmetry-graded-lean and in akiselev/ferris-howard (both unregistered), and a
> trace form for rotations of `ℚ³` in the Rocq development Horsocrates/theory-of-systems-coq. Submissions under review at
> Palomar are not visible in its data API.

The tables for `N ≤ 12` agree with rows `n ≤ 12` of Table 1 of Bamberg–Cairns–Kilminster, with OEIS A080738 (the rows
`ψ⁻¹{2k}`), A080740 (the number of finite orders) and A005417 (the largest finite order); the least dimension is OEIS
A152455 and `ψ` is A080737. Rows `n = 20, 22, 24` of that Table 1 omit their values above `2000` (`2520`; `2310`;
`2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620, 5040`); the six statements of the last section of Challenge.lean
check these values of `ψ` and the least dimensions they give in the kernel.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are pinned by the
committed manifest; there are no GitHub Actions workflows. `python scripts/verify.py --fetch-cache` runs every check
(pins, source guard, definition and statement comparisons, the standard-library replay of the tables, the build with the
axiom audit, module resolution, the elaboration check of the two definitions, Palomar's core-notation audit);
[VERIFICATION.md](VERIFICATION.md) lists them and their limits, [PROOF.md](PROOF.md) gives the mathematics with the Lean
name of every step, and [DISCLOSURE.md](DISCLOSURE.md) the assistance statement.

License: [MIT](LICENSE) for the Lean files and scripts; `scripts/core_notation_audit.lean` is Palomar's, under its MIT
licence ([LICENSES/PalomarSubmission-MIT.txt](LICENSES/PalomarSubmission-MIT.txt)).
