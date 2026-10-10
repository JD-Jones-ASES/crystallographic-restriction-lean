# Primary-source audit

Pre-submission consult, 2026-10-10 UTC. Original repository inspected at
`3b1c237f18122450e1ede1e9f11ea099dd7f28ba`.

## What was actually read

| Source | Reading status | Role |
| --- | --- | --- |
| Vaidyanathaswamy, *Integer-Roots of the Unit Matrix* (1928), pp. 121–124 | Full original journal pages read, with visual inspection | Cyclotomic characteristic polynomials, the dimension/LCM criterion, companion-block realization |
| Vaidyanathaswamy, *On the Possible Periods of Integer-Matrices* (1928), pp. 268–272 | Full original journal pages read, with visual inspection | The explicit additive-totient threshold and its proof |
| Bamberg–Cairns–Kilminster (2003), pp. 202–209 | Full published author PDF read; tables visually inspected | The modern `psi` convention, Theorem 1, Table 1, and Proposition 3(2) |
| Hiller (1985), pp. 541–544 | Abstract and bibliographic information; full text not retrieved | Historical/background reference, with details attributed through BCK where indicated |
| Kuzmanovich–Pavlichenkov (2002), pp. 173–186 | Abstract and bibliographic information; full text not retrieved | The proof reference recommended by BCK; no claim of direct reading |

An indexed public scan of Hiller was found, but ordinary attempts to retrieve it returned timeouts
or HTTP 502. An indexed excerpt is not a full-text reading. Publisher/JSTOR, author-page and
institutional-repository searches did not recover an accessible full copy of Kuzmanovich–Pavlichenkov.
No access control was bypassed and no source author was contacted.

## The recovered original volume

The Biblioteca Centrală Universitară “Mihai Eminescu” Iași provides a public scan of the original
1928 *Journal of the London Mathematical Society*, volume 3:

- [Volume record](https://dspace.bcu-iasi.ro/handle/123456789/43233)
- [Complete volume PDF](https://dspace.bcu-iasi.ro/bitstream/123456789/43233/2/The%20Journal%20of%20the%20London%20Mathematical%20Society%2c%201928%2c%20Vol.3.pdf)

The downloaded volume has 334 PDF pages. The first note occupies PDF pages 131–134 (printed
pp. 121–124); the second occupies PDF pages 278–282 (printed pp. 268–272). The first and last
pages of the earlier note also contain portions of adjacent articles. Page numbers in the
following table always mean the original printed page numbers.

## Exact correspondence with the originals

In the 1928 terminology, the *order* of a matrix means its dimension, and its *period* means what
this repository calls its group-theoretic order.

| Source and location | Content and correspondence |
| --- | --- |
| 1928a, p. 122, §1 | Companion matrix of a monic integer polynomial. The text explicitly distinguishes the allowable polynomial data from the harder classification up to integral conjugacy. |
| 1928a, pp. 122–123, §2, equations (2)–(3) | Cyclotomic factors with indices `d_i` and multiplicities `x_i` give dimension `sum x_i phi(d_i)` and exact period `lcm d_i`; block-diagonal companion matrices realize the data. |
| 1928a, p. 123, §3 | Finitely many possible periods in a fixed dimension; prime and prime-power divisibility bounds. |
| 1928b, p. 268, Theorem I | The exact prime-power additive-totient criterion, with the isolated factor 2 omitted. This is the direct original citation for `exists_orderOf_eq_iff`. |
| 1928b, p. 269, §2 | Sufficiency: prime-power blocks, absorption of a single factor 2 into an odd block index, and padding. |
| 1928b, pp. 270–271, Theorem II | The minimum of a sum of cyclotomic degrees with prescribed LCM, through the sum-versus-product totient inequality. The isolated period 2 requires a separate boundary case. |
| 1928b, p. 271 | The only equality when merging distinct prime-power blocks different from 2 is the pair 3 and 4. This observation is already in the source and is used in the separate mathematical extension note. |
| 1928b, p. 271, final unnumbered statement | An odd period can be doubled without increasing the dimension. |
| 1928b, p. 272, Theorem III | No first appearance in an odd dimension, in the modern scope at least 3. |
| 1928b, p. 272, Theorems IV–V | Additivity of the prime-power totient cost for coprime periods; prime-power decomposition. Actual minimum dimensions require the isolated-order-2 exception described below. |
| BCK, p. 202, Theorem 1 | The directly read modern definition `psi(1) = psi(2) = 0` and exact finite-order criterion. |
| BCK, p. 207, Proposition 3(2) and proof | Every even nonnegative integer is a value of `psi`, with an odd squarefree witness constructed using Bertrand's postulate. Formalized in `Crystallographic/Extensions.lean`. |

### A historical correction that direct reading reveals

The earlier note's p. 123 example omits period 6 in dimension 2. The later note explicitly corrects
this in its p. 272 footnote: period 6 already occurs in dimension 2, and dimension 3 adds no new
period. The repository's tables were already correct. The README now cites the later note,
Theorem I, for the explicit threshold, while retaining the earlier note for the cyclotomic framework.

### Small arguments and dimension conventions

The isolated order 2 must remain separate in any minimum-dimension assertion: `psi(2) = 0`, but
the least matrix dimension realizing order 2 is 1. Theorem II in the later note is therefore not
copied literally with an unrestricted order parameter. Likewise, “no new orders in odd dimension”
is applied from dimension 2 to 3 and thereafter; dimension 1 provides order 2 over dimension 0.

The repository allows dimension 0, where only order 1 exists. Thus its least dimension at order
1 is 0. The first two entries of [OEIS A152455](https://oeis.org/A152455/b152455.txt) are indeed
`a(1) = 0` and `a(2) = 1`; no convention correction is needed there.

The definitions are explicitly attributed to BCK's `psi` convention. Hiller's precise conventions
at arguments 1 and 2 are not independently certified by this source audit.

## Bibliographic references

1. R. Vaidyanathaswamy, “Integer-Roots of the Unit Matrix,” *Journal of the London Mathematical
   Society* s1-3 (1928), no. 2, 121–124.
   [DOI](https://doi.org/10.1112/jlms/s1-3.2.121).
2. R. Vaidyanathaswamy, “On the Possible Periods of Integer-Matrices,” *Journal of the London
   Mathematical Society* s1-3 (1928), no. 4, 268–272.
   [DOI](https://doi.org/10.1112/jlms/s1-3.4.268).
3. H. Hiller, “The Crystallographic Restriction in Higher Dimensions,” *Acta Crystallographica*
   A41 (1985), 541–544. [DOI](https://doi.org/10.1107/S0108767385001180).
4. J. Kuzmanovich and A. Pavlichenkov, “Finite Groups of Matrices Whose Entries Are Integers,”
   *The American Mathematical Monthly* 109 (2002), no. 2, 173–186.
   [DOI](https://doi.org/10.1080/00029890.2002.11919850);
   [JSTOR DOI](https://doi.org/10.2307/2695329).
5. J. Bamberg, G. Cairns and D. Kilminster, “The Crystallographic Restriction, Permutations, and
   Goldbach's Conjecture,” *The American Mathematical Monthly* 110 (2003), no. 3, 202–209.
   [DOI](https://doi.org/10.1080/00029890.2003.11919956);
   [published author PDF](https://cage.ugent.be/~bamberg/Research_files/The%20crystallographic%20restriction,%20permutations%20and%20Goldbach%27s%20conjecture.pdf).

## Replacement for the earlier caveat

The published BCK 2003 author PDF and both of Vaidyanathaswamy's 1928 notes were read in full.
The latter were recovered from the original 1928 JLMS volume in the public digital collection
of the Central University Library in Iași. The explicit additive-totient criterion appears as
Theorem I on p. 268 of the later note, with proof on pp. 269–271; the companion-block construction
and cyclotomic LCM criterion are in the earlier note, pp. 122–123. Hiller 1985 and
Kuzmanovich–Pavlichenkov 2002 remained unavailable in full text during this audit, so article-specific
claims about them remain attributed through accessible metadata or BCK.
