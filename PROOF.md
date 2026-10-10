# The proofs, with the Lean names

The definitions are in `Crystallographic/Defs.lean`, identical to those of `Challenge.lean`. Each Challenge theorem is
the `_internal` theorem of the same name in the module named in VERIFICATION.md, restated in `Solution.lean`. `φ` is
`Nat.totient`; `m.factorization p` is the exponent of the prime `p` in `m`; `GL(N, ℤ)` is
`Matrix.GeneralLinearGroup (Fin N) ℤ`, the units of the matrix ring; `orderOf` is Mathlib's, `0` at infinite order.

## 1. The function ψ (`Crystallographic/Psi.lean`)

`psi m = ∑ p ∈ m.primeFactors, if p ^ m.factorization p = 2 then 0 else φ (p ^ m.factorization p)`: Hiller's
additive totient, the sum of `φ(pᵏ)` over the prime powers `pᵏ` exactly dividing `m`, the term for `pᵏ = 2` being `0`
(OEIS A080737; `ψ(0) = ψ(1) = ψ(2) = 0`).

- `psi_prime_pow`: for a prime power `pᵏ ≠ 2` (`k ≥ 1`) the sum has the single term `φ(pᵏ)`
  (`Nat.primeFactors_prime_pow`, `Nat.Prime.factorization_pow`).
- `psi_mul`: for coprime `a`, `b` the prime factors of `ab` are the disjoint union of those of `a` and `b`, and the
  exponent of each prime in `ab` is its exponent in the factor that contains it (`Nat.primeFactors_mul`,
  `Nat.Coprime.disjoint_primeFactors`, `Nat.factorization_mul`); the degenerate cases `a = 0` or `b = 0` force the other
  factor to be `1`.
- `psi_eq_zero_iff`: for `m ≥ 3` either `4 ∣ m`, and the `2`-term is `φ(2ᵏ) ≥ 2`, or an odd prime `p` divides `m`, and its
  term is `φ(pᵏ) ≥ p − 1 ≥ 2`; for `m ≤ 2` every term vanishes.
- `psi_le_totient`: `φ(m) = ∏ φ(pᵏ)` over the same prime powers (`Nat.totient_eq_prod_factorization`); a sum of naturals
  each `≥ 2` is at most their product, and the omitted term `φ(2) = 1` is a neutral factor.
- `even_psi`: `φ(pᵏ)` is even for `pᵏ > 2` (`Nat.totient_even`), and a sum of even numbers is even.
- `psi_eq_sum_divisors`: the exact prime-power divisors `d ≠ 2` of `m` (`IsPrimePow d`, `Nat.Coprime d (m / d)`) are
  `p ^ m.factorization p` for `p ∈ m.primeFactors`, a bijection under which the two sums agree term by term.
- `le_two_pow_psi`: every prime power `q ≠ 2` satisfies `q ≤ 2^φ(q)` (`3 ≤ 4`; for `q ≥ 4`, `φ(q) ≥ q/2` and
  `2^(q/2) ≥ q`), and `2 ≤ 2¹`; multiplying over the prime powers of `m`, with the exponent `ψ(m) + [2 ∥ m]` additive on
  coprime factors, gives `m ≤ 2^(ψ(m) + 1)` for `m ≥ 1`.
- `psi_le_sum_totient` (the covering inequality, used by necessity): if every prime power `pᵏ ∥ m` divides some
  `d ∈ S`, then `ψ(m) ≤ ∑_{d ∈ S} φ(d)`. Choose such a `d_p` for each prime `p` of `m`; the `p`-term of `ψ(m)` is at most
  the `p`-term of `ψ(d_p)` (the exponent of `p` in `d_p` is at least that in `m`, `φ(p^·)` is monotone, and the
  `2`-exception only lowers the left side); grouping the primes by their `d`, the terms assigned to one `d` are
  distinct terms of `ψ(d)`, and `ψ(d) ≤ φ(d)`.

## 2. Necessity (`Crystallographic/Necessity.lean`): `psi_orderOf_le`

Over `ℚ` (`psi_orderOf_le_rat`): let `A ∈ GL(N, ℚ)`, `M` its matrix. If `orderOf A = 0`, `ψ(0) = 0`. Otherwise
`m := orderOf A ≥ 1`, `M^m = 1`, so the minimal polynomial `f := minpoly ℚ M` divides `X^m − 1` (`minpoly.dvd`), and
`f ∣ charpoly M` (`Matrix.minpoly_dvd_charpoly`) gives `natDegree f ≤ N` (`Matrix.charpoly_natDegree_eq_dim`).
Let `S := {d ∣ m : Φ_d ∣ f}` with `Φ_d = cyclotomic d ℚ`. The `Φ_d` are pairwise coprime irreducibles
(`Polynomial.cyclotomic.isCoprime_rat`, `Polynomial.cyclotomic.irreducible_rat`), so `∏_{d ∈ S} Φ_d ∣ f`
(`Finset.prod_dvd_of_coprime`) and `∑_{d ∈ S} φ(d) ≤ natDegree f ≤ N` (`Polynomial.natDegree_cyclotomic`). The cover:
for a prime power `q = pᵏ ∥ m`, if no `d ∈ S` were divisible by `q`, then `f` would be coprime to every `Φ_d` with
`d ∣ m`, `q ∣ d` (`Irreducible.coprime_iff_not_dvd`), hence — splitting `X^m − 1 = ∏_{d ∣ m} Φ_d`
(`Polynomial.prod_cyclotomic_eq_X_pow_sub_one`) — would divide `∏_{d ∣ m/p} Φ_d = X^{m/p} − 1`
(`IsCoprime.dvd_of_dvd_mul_left`), so `M^{m/p} = 1` (`Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero`, `minpoly.aeval`)
and `m ∣ m/p` (`orderOf_dvd_iff_pow_eq_one`), impossible. Then `psi_le_sum_totient` with this `S` gives `ψ(m) ≤ N`.
Over `ℤ` (`psi_orderOf_le`): the hom `Units.map (RingHom.mapMatrix (Int.castRingHom ℚ))` from `GL(N, ℤ)` to `GL(N, ℚ)`
is injective, so it preserves `orderOf` (`orderOf_injective`).

## 3. The blocks (`Crystallographic/Block.lean`)

- `exists_orderOf_eq_totient`: for `n ≥ 1`, `g := cyclotomic n ℤ` is monic of degree `φ(n)`; on `R := AdjoinRoot g`
  the power basis `AdjoinRoot.powerBasis'` has `φ(n)` elements, and multiplication by `root g` (`Algebra.lmul`), written
  in that basis (`LinearMap.toMatrixAlgEquiv`), is an injective ring hom `R → Matrix (Fin φ(n)) (Fin φ(n)) ℤ`. The root is
  a unit of order `n`: `root^n = 1` because `Φ_n ∣ X^n − 1` (`AdjoinRoot.mk_eq_zero`,
  `Polynomial.cyclotomic.dvd_X_pow_sub_one`), and `root^d ≠ 1` for `0 < d < n` because `Φ_n ∤ X^d − 1`: over `ℚ`
  (`Polynomial.map_dvd_map`, `Polynomial.map_cyclotomic_int`) `Φ_n` is prime and would divide some `Φ_e` with `e ∣ d`,
  `e < n`, contradicting coprimality. `Units.map` carries the unit to `GL(φ(n), ℤ)` with the same order.
- `exists_orderOf_eq_mul`: block sums `fromBlocks A 0 0 B`, reindexed along `finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)`,
  form an injective hom from `GL(a, ℤ) × GL(b, ℤ)`; `(A, 1)` and `(1, B)` commute, so for coprime orders the product has
  order `uv` (`Commute.orderOf_mul_eq_mul_orderOf_of_coprime`).
- `exists_orderOf_eq_of_le`: the block sum with an identity block.
- `orderOf_neg_one_gl`, `exists_orderOf_eq_two_mul`: `−1` has order `2` in `GL(N, ℤ)` for `N ≥ 1`; it commutes with `A`,
  so `−A = (−1)·A` has order `2u` when `A` has odd order `u`.

## 4. Sufficiency (`Crystallographic/Sufficiency.lean`): `exists_orderOf_eq`

`exists_orderOf_eq_psi`: for `m ≥ 1`, `m ≠ 2`, an element of order `m` in `GL(ψ(m), ℤ)`. By
`Nat.recOnPosPrimePosCoprime`, for `m` odd or divisible by `4`: `m = 1` is the empty matrix; a prime power `pᵏ ≠ 2` is
the cyclotomic block, of size `φ(pᵏ) = ψ(pᵏ)` (`psi_prime_pow`); coprime factors `a`, `b` (both odd, or `4` dividing one
and the other odd) are block-summed into dimension `ψ(a) + ψ(b) = ψ(ab)` (`psi_mul`). For `m ≡ 2 (mod 4)`, `m ≠ 2`:
`m = 2m'` with `m'` odd, `m' ≥ 3`, `ψ(m) = ψ(m') ≥ 2`, and `−A` for the element `A` of order `m'`
(`exists_orderOf_eq_two_mul`). Then `exists_orderOf_eq`: `m = 2` is `−1` in `GL(N, ℤ)`, `N ≥ 1`; otherwise pad
`GL(ψ(m), ℤ) → GL(N, ℤ)` (`exists_orderOf_eq_of_le`).

## 5. The restriction and its corollaries (`Crystallographic/Main.lean`)

`exists_orderOf_eq_iff` combines §2 and §4; `finiteOrders_eq` restates it as a set. `isLeast_dimension`: `GL(ψ(m), ℤ)`
has an element of order `m` for `m ≠ 2` (`GL(0, ℤ)` has `1` for `m = 1`), `GL(1, ℤ)` has `−1` for `m = 2`, and any
`N` with an element of order `m` has `ψ(m) ≤ N` (`psi_orderOf_le`), with `N ≠ 0` when `m = 2` since `GL(0, ℤ)` is trivial.
`exists_orderOf_eq_iff_rat`: necessity is §2 over `ℚ`; the integer witness, mapped along the injective hom of §2, is
the rational one. `finiteOrders_succ_of_even`: `ψ(m) ≤ N + 1` with `ψ(m)` and `N` even gives `ψ(m) ≤ N` (`even_psi`).
`le_two_pow_of_mem_finiteOrders`: `m ≤ 2^(ψ(m) + 1) ≤ 2^(N + 1)` (`le_two_pow_psi`, `psi_orderOf_le`);
`finiteOrders_finite` follows. `finiteOrders_zero` (`Crystallographic/Extra.lean`): every element of `GL(0, ℤ)` is `1`, of order `1`.
`finiteOrders_mono`: an identity block pads an element of `GL(N, ℤ)` to `GL(N', ℤ)` (`exists_orderOf_eq_of_le`).

## 6. The tables (`Crystallographic/Compute.lean`, `Crystallographic/Tables.lean`)

`psi` is defined through `Nat.factorization`, which the kernel does not evaluate, so `Compute.lean` defines `psiC` by
trial division with a fuel argument (`stripPow`, `psiAux`, structural recursion) and proves `psiC_eq_psi`
(`psiAux_eq`: induction on the fuel under the invariant that `m` has no prime factor below the trial divisor `p` and
`m < (p + fuel)²`; a number `1 < m < p²` with no prime factor below `p` is prime; a trial divisor `p ∣ m` with no
smaller prime factor of `m` is prime; `stripPow_spec` removes it exactly). Each table `finiteOrders_N` then reads:
`finiteOrders N = {m | 0 < m ∧ ψ(m) ≤ N}` (`finiteOrders_eq`), `ψ(m) ≤ N` forces `m ≤ 2^(N + 1)` (`le_two_pow_psi`), and
`decide +kernel` checks `psiC m ≤ N ↔ m ∈ table` for every `m < 2^(N + 1)`. The maxima `isGreatest_finiteOrders_N` read
off the tables.

**Beyond dimension 12** (`Crystallographic/Erratum.lean`). `psi_2520 : ψ(2520) = 20`, `psi_2310 : ψ(2310) = 22` and
`psi_eq_twentyfour` (ψ = 24 at 2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620, 5040) are kernel computations of `psiC`;
`isLeast_dimension_2520`, `isLeast_dimension_2310`, `isLeast_dimension_twentyfour` combine them with `isLeast_dimension`.
Table 1 of Bamberg–Cairns–Kilminster prints `ψ⁻¹{n}` for even `n ≤ 24`; its rows `n ≤ 18` agree with `ψ`, while rows 20, 22
and 24 omit exactly these eleven values, all above 2000 (the largest printed entry is 1980). The omission was found while
checking the table against `ψ` and confirmed by two independent enumerations outside Lean (a sieve with the bound
`m ≤ 2^(n + 1)`, and the structural enumeration of products of prime powers `q ≤ 2n`).

## 7. Relation to the sources

The theorem is Vaidyanathaswamy's (1928), on the orders of integer matrices; Hiller (1985) rediscovered it in the
language of the crystallographic restriction, introduced the additive totient `ψ` and tabulated the orders to dimension
23; Kuzmanovich and Pavlichenkov (2002) give a proof; Bamberg, Cairns and Kilminster (2003) state it as their Theorem 1
with Table 1 of the sets `Ord_n`. The proofs here are the standard ones through minimal and cyclotomic polynomials and
companion blocks, written for Mathlib. The hypotheses `N ≥ 1` and `m ≥ 1` are made explicit: `GL(0, ℤ)` is trivial while
`ψ(2) = 0`, and Lean's `orderOf` is `0` at infinite order. The text read is the authors' PDF of Bamberg–Cairns–Kilminster
(pp. 202–209, with the Monthly's pagination); Hiller and Kuzmanovich–Pavlichenkov were read in abstract only, and
Vaidyanathaswamy's two 1928 notes not at all. In the OEIS, `ψ` is A080737, the least dimension A152455, the rows
`ψ⁻¹{2k}` A080738, the number of finite orders A080740 and the largest finite order A005417. The two-dimensional case is
already in public Lean (acprk/symmetry-graded-lean and akiselev/ferris-howard, 2026-08 and 2026-09, both unregistered);
nothing here claims a first formalization of the classical restriction.
