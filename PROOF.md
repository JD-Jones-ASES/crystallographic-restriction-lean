# The proofs, with the Lean names

The definitions are in `Crystallographic/Defs.lean`, identical to those of `Challenge.lean`. Each Challenge theorem is
the `_internal` theorem of the same name in the module named in VERIFICATION.md, restated in `Solution.lean`. `φ` is
`Nat.totient`; `m.factorization p` is the exponent of the prime `p` in `m`; `GL(N, ℤ)` is
`Matrix.GeneralLinearGroup (Fin N) ℤ`, the units of the matrix ring; `orderOf` is Mathlib's, `0` at infinite order.

## 1. The function ψ (`Crystallographic/Psi.lean`)

`psi m = ∑ p ∈ m.primeFactors, if p ^ m.factorization p = 2 then 0 else φ (p ^ m.factorization p)`: the additive
totient defined on p. 202 of Bamberg–Cairns–Kilminster, the sum of `φ(pᵏ)` over the prime powers `pᵏ` exactly dividing `m`, the term for `pᵏ = 2` being
`0` (OEIS A080737; `ψ(0) = ψ(1) = ψ(2) = 0`).

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
- `psi_le_sum_totient_of_zero_notMem` (the covering inequality, used by necessity): if `0 ∉ S` and every prime
  power `pᵏ ∥ m` divides some `d ∈ S`, then `ψ(m) ≤ ∑_{d ∈ S} φ(d)`. Choose such a `d_p` for each prime `p` of `m`; the `p`-term of `ψ(m)` is at most
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
and `m ∣ m/p` (`orderOf_dvd_iff_pow_eq_one`), impossible. Then `psi_le_sum_totient_of_zero_notMem` with this `S` (no divisor is `0`) gives `ψ(m) ≤ N`.
Over `ℤ` (`psi_orderOf_le`): the hom `Units.map (RingHom.mapMatrix (Int.castRingHom ℚ))` from `GL(N, ℤ)` to `GL(N, ℚ)`
is injective, so it preserves `orderOf` (`orderOf_injective`).

## 3. The blocks (`Crystallographic/Block.lean`)

- `exists_orderOf_eq_totient`: for `n ≥ 1`, `g := cyclotomic n ℤ` is monic of degree `φ(n)`; on `R := AdjoinRoot g`
  the power basis `pb := AdjoinRoot.powerBasis'` has `φ(n)` elements, and `Φ := Algebra.leftMulMatrix pb.basis`, the
  matrix of multiplication in that basis, is an injective algebra hom `R → Matrix (Fin φ(n)) (Fin φ(n)) ℤ`
  (`Algebra.leftMulMatrix_injective`). The root has order `n`: `root^n = 1` because `Φ_n ∣ X^n − 1`
  (`AdjoinRoot.mk_eq_zero`, `Polynomial.cyclotomic.dvd_X_pow_sub_one`); and `n ∣ orderOf root` because
  `AdjoinRoot.lift (Int.castRingHom ℂ) ζ` sends the root to `ζ = exp(2πi/n)`, a primitive `n`-th root of unity
  (`Complex.isPrimitiveRoot_exp`, `Polynomial.map_cyclotomic_int`, `IsPrimitiveRoot.isRoot_cyclotomic`), so
  `n = orderOf ζ ∣ orderOf root` (`orderOf_map_dvd`, `IsPrimitiveRoot.eq_orderOf`). `Φ root` is a unit
  (`IsUnit.of_pow_eq_one`) of the same order (`orderOf_injective`, `orderOf_units`), and `blk_cast` moves it to
  `GL(φ(n), ℤ)`.
- `exists_orderOf_eq_mul`: the injective monoid homs `P ↦ fromBlocks P 0 0 1` and `Q ↦ fromBlocks 1 0 0 Q` (`blk_inl`,
  `blk_inr`) have commuting images (`blk_commute`), so for coprime orders their product has order `uv`
  (`Commute.orderOf_mul_eq_mul_orderOf_of_coprime`, `blk_transfer`); `blk_reindex` moves it along
  `finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)`.
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

`psi` is defined through `Nat.factorization`, which the kernel evaluates only impractically slowly at the table sizes,
so `Compute.lean` defines `psiC` by
trial division with a fuel argument (`stripPow`, `psiAux`, structural recursion) and proves `psiC_eq_psi`
(`psiAux_eq`: induction on the fuel under the invariant that `m` has no prime factor below the trial divisor `p` and
`m < (p + fuel)²`; a number `1 < m < p²` with no prime factor below `p` is prime; a trial divisor `p ∣ m` with no
smaller prime factor of `m` is prime; `stripPow_spec` removes it exactly). Each table `finiteOrders_N` then reads:
`finiteOrders N = {m | 0 < m ∧ ψ(m) ≤ N}` (`finiteOrders_eq`), and `ψ(m) ≤ N ≤ 12` forces `m ≤ 2^(N + 1) ≤ 8192`
(`le_two_pow_psi`). Seventeen kernel checks (`tbl_chunk12_0`, …, `tbl_chunk12_16`, one declaration per block of `512`
values so the kernel's caches are released between them; assembled by `tbl_chunks12` and `tbl_key12`) show that below
`8193` the `m ≥ 1` with `psiC m ≤ 12` are exactly the 48 members of the list `tbl_L12`;
each table `N ≤ 12` is then cut out of that list by a `decide +kernel` over its 48 members (`tbl_table`). The maxima
`isGreatest_finiteOrders_N` read off the tables.

**Beyond dimension 12** (`Crystallographic/Erratum.lean`). `psi_2520 : ψ(2520) = 20`, `psi_2310 : ψ(2310) = 22` and
`psi_eq_twentyfour` (ψ = 24 at 2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620, 5040) are kernel computations of `psiC`;
`isLeast_dimension_2520`, `isLeast_dimension_2310`, `isLeast_dimension_twentyfour` combine them with `isLeast_dimension`.
Table 1 of Bamberg–Cairns–Kilminster prints `ψ⁻¹{n}` for even `n ≤ 24`; its rows `n ≤ 18` agree with `ψ`, while rows 20, 22
and 24 omit exactly these eleven values, all above 2000 (the largest printed entry is 1980). The Lean statements prove the
eleven values and their least dimensions; that nothing else is missing is checked outside Lean by `scripts/check_tables.py`,
which re-derives every row by the structural enumeration of the products of prime powers `q ≤ 2n` (every `q ≠ 2` with
`φ(q) ≤ n` has `q ≤ 2n`), checks the enumeration against brute force for `n ≤ 14`, and compares each row with the printed one.

## 7. The special linear group (`Crystallographic/SL.lean`)

`orderOf_sl_one`: a `1 × 1` matrix of determinant `1` is `1`. `exists_orderOf_eq_iff_sl` (`N ≥ 2`): necessity through the
injective inclusion `Matrix.SpecialLinearGroup.toGL` and `psi_orderOf_le`. Sufficiency tracks the determinant through the
construction of §4 (`sl_good n m`: an integer matrix of determinant `1` and order `m` in dimension `n`): write
`m = 2ᵏ u` with `u` odd. An element of `GL(ψ(u), ℤ)` of odd order `u` has determinant `1` (`sl_good_of_gl_odd`: the
determinant is `±1` and its `u`-th power is `1`). For `k = 1`, `u = 1`: `−1` in dimension `2`; for `k = 1`, `u ≥ 3`: `−A`
in the even dimension `ψ(u) = ψ(m)` (`sl_good_two_mul`, `Matrix.det_neg`). For `k ≥ 2`: multiplication by the root on
`ℤ[X]/(X^(2^(k−1)) + 1)` in its power basis (`sl_two_pow_block`) has order `2ᵏ` (its `2^(k−1)`-th power is `−1`) and
determinant `1` — the characteristic polynomial of the left-multiplication matrix is the minimal polynomial
(`charpoly_leftMulMatrix`), which is `X^(2^(k−1)) + 1` (`minpoly.unique'`), so `det = (−1)^(2^(k−1)) · 1`
(`Matrix.det_eq_sign_charpoly_coeff`); block sums multiply determinants (`sl_good_mul`, `Matrix.det_fromBlocks_zero₂₁`)
and identity padding keeps them (`sl_good_of_le`).

## 8. Relation to the sources

The direct original statement of the additive-totient criterion is **Theorem I, p. 268**, of
Vaidyanathaswamy's *On the Possible Periods of Integer-Matrices*, J. London Math. Soc. 3 (1928),
268–272, proved on pp. 269–271. His earlier *Integer-Roots of the Unit Matrix*, pp. 121–124 of the
same volume, supplies the cyclotomic characteristic-polynomial/LCM criterion and companion-block
construction on pp. 122–123. Both notes were read in full during the pre-submission consult from
the [original volume in the Central University Library, Iași](https://dspace.bcu-iasi.ro/handle/123456789/43233).
The later paper's p. 272 footnote corrects the earlier paper's omission of order 6 in dimension 2.
Its Theorem II (minimum totient sum for a fixed LCM) needs order 2 handled separately if stated
literally for every positive order; the repository already does this in `isLeast_dimension`.

Bamberg–Cairns–Kilminster (2003), Theorem 1 on p. 202, is the directly read modern source for the
precise `psi` convention and the main statement. Their published author PDF, pp. 202–209, was read
in full. Proposition 3(2) and its proof on p. 207 are the source for the odd squarefree witnesses
in §9. The invariant integral Gram form in §10 is the standard finite-group averaging construction,
written without division.

Hiller (1985) and Kuzmanovich–Pavlichenkov (2002) **remain unread in full** in this consult. Hiller's
abstract and the references in Bamberg–Cairns–Kilminster establish the related higher-dimensional
lattice result; the latter paper cites Kuzmanovich–Pavlichenkov for a proof. An indexed public
scan of Hiller was located but could not be retrieved. No full-text reading or unchecked small-argument
convention for Hiller's `Phi` is claimed. [SOURCES.md](SOURCES.md) records exact access status,
page references, and the original papers' boundary conventions.

The hypotheses `N ≥ 1` and `m ≥ 1` remain explicit: `GL(0, ℤ)` is trivial while `psi(2) = 0`, and
Mathlib's `orderOf` is `0` at infinite order. In the OEIS, `psi` is A080737, the least dimension
A152455 (including its value 0 at order 1), the rows `psi⁻¹{2k}` A080738, the number of finite orders
A080740 and the largest finite order A005417. The two-dimensional case is already in public Lean
(acprk/symmetry-graded-lean and akiselev/ferris-howard, both unregistered at the original review);
nothing here claims a first formalization of the classical two-dimensional restriction.

## 9. Every even minimum dimension occurs (`Crystallographic/Extensions.lean`)

`exists_odd_squarefree_psi_eq`: for every `n`, some positive odd squarefree `m` has `psi(m) = 2n`.
This formalizes the witness constructed in the proof of BCK Proposition 3(2), p. 207. The proof
uses strong induction on `n`. The base case is `m = 1`. For `n > 0`, Bertrand's postulate supplies
an odd prime `p` with `n + 1 < p < 2(n + 1)`, hence `p ≤ 2n + 1`. Write `p = 2j + 1` and apply
the induction hypothesis at `n - j`. An odd prime divisor `p` of an integer `m' > 0` would force
`p - 1 ≤ psi(m')` (`prime_sub_one_le_psi_internal`), but here
`psi(m') = 2(n - j) < p - 1`. Thus `p` and `m'` are coprime, their product is odd and squarefree,
and additivity gives `psi(p * m') = (p - 1) + 2(n - j) = 2n`.

`range_psi` combines this with `even_psi`. For positive `N, M`,
`finiteOrders_subset_iff` proves that inclusion of the two finite-order sets is equivalent to
`N / 2 ≤ M / 2`. The forward implication applies the inclusion to a witness with
`psi(m) = 2 * (N / 2)`; the reverse implication uses parity of `psi`. Antisymmetry gives
`finiteOrders_eq_iff`. Finally, `exists_new_odd_squarefree_order` puts a witness of value
`2n + 2` in dimension `2n + 2` and excludes it from dimension `2n + 1`.

## 10. Integral invariant forms (`Crystallographic/InvariantForm.lean`)

For a matrix `A` over a commutative ring, define

```text
invariantGram A m = sum_{0 <= k < m} (A^k)^T * A^k.
```

`invariantGram_isSymm` proves symmetry. If `A^m = I`, multiplying on the left by `A^T` and on
the right by `A` shifts the sum to the powers `1, ..., m`; the two endpoint terms are both the
identity. This is `invariantGram_invariant`. `invariantGram_map` proves compatibility with
every coefficient-ring homomorphism.

For `m > 0`, the first summand is the identity, and the remaining Gram matrices are positive
semidefinite. `invariantGram_posDef` proves positive definiteness in Mathlib's ordered-star-ring
setting; `invariantGram_posDef_real` additionally proves that an integer Gram sum remains
positive definite after casting to the reals. In conventional notation, for a nonzero real vector,

```text
x^T Q x = sum_{k < m} ||A^k x||^2 >= ||x||^2 > 0.
```

`exists_integral_invariant_posDef` specializes the construction to any integer matrix of positive
finite order. There is no division, so every entry of `Q` is an integer. Combining this with the
existing existence criterion gives `exists_integral_posDef_isometry_iff`: for `N, m > 0`, an
integer matrix of order `m` preserving a suitable positive definite integral form exists exactly
when `psi(m) ≤ N`. The form is existentially chosen along with the matrix; unimodularity of the
form, the automorphism group of a fixed lattice, and classification of whole isometry groups are
not conclusions of these statements.

## 11. Further handwritten results

`MATHEMATICAL-EXTENSIONS.md` proves the determinant-minus-one minimum dimension and the exact
classification/count of rational conjugacy classes at minimum dimension. It analyzes equality in
the additive-totient inequalities, including the cost-free exponent-one factor 2 and the exceptional
combination of prime powers 3 and 4. These arguments are not Lean theorems in this submission.
The independent finite enumerator `scripts/check_minimal_classes.py` checks them through order
500; finite enumeration is evidence for the argument, not a proof for all orders.
