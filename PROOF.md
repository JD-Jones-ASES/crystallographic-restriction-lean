# The proofs, with the Lean names

The definitions are in `Crystallographic/Defs.lean`, identical to those of `Challenge.lean`. Each Challenge theorem is
the `_internal` theorem of the same name in the module named in VERIFICATION.md, restated in `Solution.lean`. `φ` is
`Nat.totient`; `m.factorization p` is the exponent of the prime `p` in `m`; `GL(N, ℤ)` is
`Matrix.GeneralLinearGroup (Fin N) ℤ`, the units of the matrix ring; `orderOf` is Mathlib's, `0` at infinite order.

## 1. The function ψ (`Crystallographic/Psi.lean`)

`psi m = ∑ p ∈ m.primeFactors, if p ^ m.factorization p = 2 then 0 else φ (p ^ m.factorization p)`: the additive
totient `ψ` as defined by Bamberg–Cairns–Kilminster (p. 202), the sum of `φ(pᵏ)` over the prime powers `pᵏ` exactly dividing `m`, the
term for `pᵏ = 2` being `0` (OEIS A080737; `ψ(0) = ψ(1) = ψ(2) = 0`).

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

In the 1928 vocabulary the "order" of a matrix is its dimension and its "period" its order. Vaidyanathaswamy's
*Integer-roots of the unit matrix* (J. London Math. Soc. 3 (1928) 121–124) shows (pp. 122–123) that an integer matrix
with `Ωʳ = 1` has characteristic polynomial `∏ Φ_{dᵢ}^{xᵢ}` with `dᵢ ∣ r`, of period exactly `r` iff `lcm dᵢ = r`, in
dimension `∑ xᵢ φ(dᵢ)`, and realizes every solution by a block sum of companion matrices (the matrices up to integral
conjugacy are left open, p. 122); p. 123 deduces finitely many periods in each dimension. *On the possible periods of
integer-matrices* (ibid. 268–272) states the criterion as Theorem I (p. 268): period `r` occurs in dimension `n` iff
`ψ(r) ≤ n` (`exists_orderOf_eq_iff`). Its proof (pp. 269–271) exhibits solutions and bounds `∑ φ(dᵢ)` below over
distinct `dᵢ ≠ 1` with `lcm r` (Theorem II, p. 270, which read literally fails at `r = 2`, where the minimum is
`φ(2) = 1`; `isLeast_dimension` treats `m = 2` apart). Page 271 has the one equality case `φ(3)φ(4) = φ(3) + φ(4)` and
the period `2r` from an odd period `r` in the same dimension (`exists_orderOf_eq_two_mul`); p. 272 the growth with `n`
(`finiteOrders_mono`), no new period in an odd dimension (Theorem III, stated for every odd `n`; dimension 1 has the
period 2 that dimension 0 lacks, so `n ≥ 3` here; `finiteOrders_succ_of_even`), the least
dimension `ψ(r)` for `r > 2` (`isLeast_dimension`), and a footnote correcting p. 123 (dimension 2 has the periods 2, 3,
4 and 6). Bamberg–Cairns–Kilminster state the theorem without proof (Theorem 1, p. 202), with the parity of `ψ`
(p. 203), Table 1 (p. 204) and Proposition 3(2) with its proof (p. 207; §9). Hiller (1985) and Kuzmanovich–Pavlichenkov
(2002) were read in abstract only. The proofs here take the cyclotomic route of the 1928 notes, with necessity through
the minimal polynomial and the factor `2` supplied by `−A` (§4). In the OEIS, `ψ` is A080737, the least dimension
A152455, the rows `ψ⁻¹{2k}` A080738, the number of finite orders A080740 and the largest finite order A005417. The
two-dimensional case is already in public Lean (acprk/symmetry-graded-lean and akiselev/ferris-howard, both
unregistered as of 2026-10-09); nothing here claims a first formalization of the classical restriction.

## 9. The values of ψ, and the finite orders by half-dimension (`Crystallographic/Extensions.lean`)

`exists_odd_squarefree_psi_eq`: every `2n` is `ψ(m)` for an odd squarefree `m ≥ 1` (Bamberg–Cairns–Kilminster,
Proposition 3(2) and its proof, p. 207). Strong induction on `n`, with `m = 1` at `n = 0`. For `n > 0`, Bertrand's
postulate (`Nat.exists_prime_lt_and_le_two_mul` at `n + 1`) gives a prime `p = 2j + 1` with `n + 1 < p ≤ 2n + 2`, so
`1 ≤ j ≤ n`; the hypothesis at `n − j` gives `m'` with `ψ(m') = 2(n − j) < p − 1`. An odd prime dividing `m' ≥ 1`
contributes at least `p − 1` to `ψ(m')` (`prime_sub_one_le_psi`), so `p ∤ m'`, `pm'` is odd and squarefree,
and `ψ(pm') = (p − 1) + 2(n − j) = 2n` (`psi_mul`). `range_psi` adds `even_psi`. `finiteOrders_subset_iff` (`N, M ≥ 1`,
through `finiteOrders_eq`): a witness with `ψ(m) = 2(N / 2) ≤ N` gives `N / 2 ≤ M / 2`; conversely `ψ(m) ≤ N` and `ψ(m)`
even give `ψ(m) ≤ 2(N / 2) ≤ M`. `finiteOrders_eq_iff` follows by antisymmetry. `exists_new_odd_squarefree_order`: the
witness for `2n + 2` lies in `finiteOrders (2n + 2)` and not in `finiteOrders (2n + 1)`.

## 10. An invariant integral form (`Crystallographic/InvariantForm.lean`)

`invariantGram A m = ∑_{k < m} (Aᵏ)ᵀ Aᵏ` over a commutative ring is symmetric (`invariantGram_isSymm`); if `Aᵐ = 1`,
`Aᵀ (invariantGram A m) A` is the same sum over `k = 1, …, m`, whose term `k = m` is the term `k = 0`
(`invariantGram_invariant`); it commutes with ring homomorphisms (`invariantGram_map`). For `m > 0` it is positive
definite, its term `k = 0` being `1` and the others positive semidefinite (`invariantGram_posDef`, over an ordered ring
with trivial star such as `ℤ`, `ℚ` or `ℝ`; `invariantGram_posDef_real` after the cast to `ℝ`: `xᵀQx = ∑ |Aᵏx|² ≥ |x|²`;
for a symmetric integer matrix, positivity on integer vectors and on real vectors are equivalent, and `Q.IsSymm` is part
of `Q.PosDef`, so the statements carry redundant conjuncts). `exists_integral_invariant_posDef` applies it to
`A ∈ GL(N, ℤ)` of order `m ≥ 1`; there is no division, so the form is integral. This is the sum of the transforms of the
identity form over the group generated by `A`, Serre's construction for finite subgroups of `GL(n, ℚ)` (*Bounds for
the orders of the finite subgroups of G(k)*, §1.3.2), where an integer then clears the denominators; over `ℤ` none arise. `exists_integral_posDef_isometry_iff` (`N, m ≥ 1`) adds
`exists_orderOf_eq` and `psi_orderOf_le`: for integral forms, Bamberg–Cairns–Kilminster's remark (p. 202) that `Ord_n` is
the set of orders of the symmetries of lattices in dimension `n`. The form is chosen with the matrix; its unimodularity
(false in general: `Q = 4·I₂` for the rotation of order 4 of `ℤ²`) and the isometry group of a given form are not addressed.

## 11. Determinant `−1` (`Crystallographic/DetNegOne.lean`)

`exists_orderOf_eq_det_neg_one_iff` (`m ≥ 1`): `GL(N, ℤ)` has an element of order `m` and determinant `−1` iff `m` is
even and `ψ(m) + 1 ≤ N`; `isLeast_dimension_det_neg_one` reads off the least dimension `ψ(m) + 1` for even `m`, and
`exists_orderOf_eq_det_neg_one_iff_rat` is the same over `ℚ`. Sufficiency (`dn_good`, as `sl_good` in §7): `[−1]` for
`m = 2`; for even `m > 2`, `ψ(m) ≥ 2` (`psi_eq_zero_iff`, `even_psi`), `B ∈ SL(ψ(m), ℤ)` of order `m` from §7
(`sl_suff`), and the block sum of `[−1]` and `B` (`dn_block`: determinants multiply, `Matrix.det_fromBlocks_zero₂₁`; the
order is the lcm, `Prod.orderOf` along `sl_blockHom`) has determinant `−1` and order `lcm(2, m) = m`; an identity block
pads (`dn_good_of_le`). Necessity, over `ℚ` (`dn_nec_rat`): `(det M)ᵐ = 1` and `det M = −1` make `m` even. The Gram sum
`Q = invariantGram M m` (§10) is positive definite, so `det Q ≠ 0`, and `MᵀQM = Q` gives `MᵀQ(M + 1) = (M + 1)ᵀQ`,
whence `det M · det(M + 1) = det(M + 1)` and `det(M + 1) = 0` (`dn_det_add_one_eq_zero`). If `Φ₂ = X + 1` did not divide
the minimal polynomial `f`, a Bézout identity `aΦ₂ + bf = 1` evaluated at `M` would invert `M + 1`
(`dn_cyclotomic_two_dvd`); so `2 ∈ S`, the set of §2 (`aux_nec_S` repeats its construction: `∑_{d ∈ S} φ(d) ≤ N` and
the cover). The cover gives `ψ(m) ≤ ∑_{d ∈ S} ψ(d)` (`dn_psi_le_sum_psi`, the proof of
`psi_le_sum_totient_of_zero_notMem` without its last step), and `ψ(2) = 0 < 1 = φ(2)` with `ψ ≤ φ` elsewhere gives
`∑_{d ∈ S} ψ(d) + 1 ≤ ∑_{d ∈ S} φ(d) ≤ N`.

## 12. On paper, not in Lean: the classes at the least dimension

Over `ℚ` an element of `GL(N, ℤ)` of finite order `m` is conjugate to a block sum of companion matrices of some
`Φ_{d_j}`, `d_j ∣ m`, with `lcm d_j = m` and `N = ∑ φ(d_j)` (the 1928 framework, §8), and its class under `GL(N, ℚ)`
is determined by the multiset of the `d_j` (the minimal polynomial is squarefree, so the module is semisimple). Since
`ψ(m) ≤ ∑ ψ(d_j) ≤ ∑ φ(d_j)` (§1, §11), `N = ψ(m)` forces equality throughout: each `d_j` has `ψ(d_j) = φ(d_j)`, which
holds exactly for `pᵉ`, `2pᵉ` (`p` odd, `e ≥ 1`), `2ᵏ` (`k ≥ 2`) and `12` (Lemmas I–II and p. 271 of the second 1928
note), and each odd prime power `qᵢ ∥ m`, and `2ᵃ` if `a ≥ 2`, divides exactly one `d_j`; no `d_j` is `1` or `2` and
none repeats. So for `m = 2ᵃ q₁ ⋯ q_r > 2` (`qᵢ` the odd prime powers of `m`) the classes are: `Φ_{q₁} ⋯ Φ_{q_r}` for
`a = 0`; for `a = 1`, `Φ_{qᵢ}` or `Φ_{2qᵢ}` chosen independently for each `i` with at least one `Φ_{2qᵢ}`; for `a ≥ 2`,
`Φ_{2ᵃ}` times those independent choices, and also, when `a = 2` and `3 ∥ m`, `Φ₁₂` in place of the factors for `4` and
`3` with the other choices free. Their number is `1`, `2^r − 1`, `2^r`, or `3·2^(r−1)` in the case `4 ∥ m`, `3 ∥ m`
(for `m = 12`: `Φ₃Φ₄`, `Φ₆Φ₄`, `Φ₁₂`; for `m = 30`: `Φ₃Φ₁₀`, `Φ₆Φ₅`, `Φ₆Φ₁₀`). Integral conjugacy is not addressed
(open already on p. 122 of the first note). `scripts/check_minimal_classes.py` enumerates, for every `m ≤ 500`, the multisets of cyclotomic
indices with lcm `m` and dimension at most `ψ(m) + 1`, and finds exactly these classes at the least dimension (867 for `3 ≤ m ≤ 500`, 869 with
the single classes of `m = 1` and `m = 2`), and the least dimension `ψ(m) + 1` with determinant `−1` for even `m` and none for odd `m` (§11); it is a finite
check, not a proof.
