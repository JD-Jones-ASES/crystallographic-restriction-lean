# Additional mathematical consequences

These are complete mathematical arguments developed during the consult. They are **not Lean-verified**. No claim of literature novelty is made. The new Lean module `Crystallographic/Extensions.lean` instead formalizes BCK Proposition 3(2), including the odd squarefree witness already constructed in its proof, and exact spectrum consequences.

## 1. A useful arithmetic inequality, including equality conditions

For a prime `p`, define

\[
g_p(e)=\begin{cases}
0,&e=0,\\
0,&p=2\text{ and }e=1,\\
p^{e-1}(p-1),&\text{otherwise}.
\end{cases}
\]

For positive integers `d_1,...,d_s`, with `m=lcm(d_1,...,d_s)` (empty lcm 1 and empty maximum 0),

\[
\psi(m)=\sum_p\max_j g_p(v_p(d_j))
\le \sum_j\psi(d_j)\le\sum_j\varphi(d_j).
\tag{1}
\]

The first identity holds because each `g_p` is nondecreasing. Equality in the first inequality holds exactly when, for each odd prime `p`, at most one `d_j` is divisible by `p`, and at most one `d_j` is divisible by 4. Factors 2 of exponent exactly 1 have zero cost and can recur without affecting equality.

For a positive integer `d`, equality `psi(d)=phi(d)` holds exactly for

\[
d=p^e\quad(p\text{ odd},e\ge1),\qquad
d=2p^e\quad(p\text{ odd},e\ge1),\qquad
d=2^a\quad(a\ge2),\qquad d=12.
\tag{2}
\]

Proof: `d=1,2` has `psi=0<phi=1`. Otherwise let `w_1,...,w_t` be the totients of the exact prime-power divisors other than a possible factor 2 of exponent 1. Each `w_i>=2`, `psi(d)=sum w_i`, and `phi(d)=product w_i`. For one term equality is automatic. For two terms, `a+b=ab` iff `(a-1)(b-1)=1`, hence both terms are 2. The only prime powers of totient 2 are 3 and 4, giving `d=12`. For at least three terms, the sum is strictly below the product: for two terms the product is at least the sum and at least 4, and multiplying by a further term `c>=2` strictly exceeds adding it, since `(P-1)(c-1)>1`. Induction gives strict inequality for all larger lists.

## 2. Exact classification with determinant minus one

**Theorem.** For positive `m` and any nonnegative `N`, there exists `A in GL(N,Z)` with `order(A)=m` and `det A=-1` if and only if

\[
m\text{ is even}\quad\text{and}\quad N\ge\psi(m)+1.
\]

Therefore every positive even order has least orientation-reversing integral dimension exactly `psi(m)+1`.

**Necessity.** A finite-order rational matrix has squarefree minimal polynomial dividing `X^m-1`, because characteristic zero makes `X^m-1` squarefree. Its rational representation is therefore a direct sum, with multiplicities, of simple cyclotomic modules `Q[X]/(Phi_d)`, where `d|m`. Let their indices, including repetitions, be `d_1,...,d_s`. Then

\[
m=\operatorname{lcm}(d_1,\ldots,d_s),\qquad
N=\sum_j\varphi(d_j).
\]

A cyclotomic block has determinant +1 except for `Phi_2=X+1`, whose determinant is -1. (For `d>2`, `phi(d)` is even and the constant term is 1; `Phi_1=X-1` gives determinant +1.) Thus determinant -1 forces an odd, positive number of `d_j=2`, and also forces `m` even. Each occurrence of `d_j=2` contributes 1 to `sum phi` and 0 to `sum psi`. Inequality (1) consequently gives

\[
N=\sum_j\varphi(d_j)\ge 1+\sum_j\psi(d_j)\ge1+\psi(m).
\]

**Sufficiency.** For `m=2`, the matrix `[-1]` has the required dimension `psi(2)+1=1`. For even `m>2`, the existing repository proves `psi(m)>=2` and constructs `B in SL(psi(m),Z)` with order `m`. The block matrix `diag(-1,B)` has determinant -1, dimension `psi(m)+1`, and order `lcm(2,m)=m`. Identity blocks pad either construction to any larger dimension.

Examples of least dimensions: order 2 -> 1; orders 4 and 6 -> 3; orders 8, 10, 12 -> 5; order 30 -> 7. The determinant -1 order spectra consequently grow at odd dimensions and are unchanged on moving from an odd dimension to the next even dimension.

## 3. Rational conjugacy classes at the minimum dimension

Write

\[
m=2^a\prod_{i=1}^{r}p_i^{e_i},
\]

where the `p_i` are the distinct odd prime divisors of `m` and `q_i=p_i^{e_i}`.

**Theorem.** For `m>2`, all rational conjugacy classes of order `m` in dimension `psi(m)` have exactly the following characteristic polynomials.

1. If `a=0`, the single polynomial `product_i Phi_(q_i)`.
2. If `a=1`, choose independently `Phi_(q_i)` or `Phi_(2q_i)` for each `i`, with at least one even choice. Multiply the selected factors.
3. If `a>=2`, choose independently `Phi_(q_i)` or `Phi_(2q_i)` for each `i` and include the factor `Phi_(2^a)`.
4. Additionally, if `a=2` and `v_3(m)=1`, replace the contributions for the exact prime powers 4 and 3 by the single factor `Phi_12`. Each of the remaining odd prime-power factors still has its independent odd/even choice.

Every listed polynomial has an integral companion-block representative, and there are no others.

**Proof.** The cyclotomic-module decomposition above gives `N=sum phi(d_j)` and `m=lcm d_j`. Setting `N=psi(m)` forces equality in both inequalities in (1). Hence each `d_j` must be in list (2). Equality at each odd prime forces that prime to occur in exactly one block, necessarily with its full exponent `e_i`. Equality at 2 forces the full `2^a` for `a>=2` into exactly one block; all other blocks may contain 2 at exponent 1. Thus every odd prime-power contribution has the choices `Phi_(q_i)` and `Phi_(2q_i)`. If `a=0`, only the first choice is compatible with the required order. If `a=1`, at least one second choice is necessary to supply a factor 2 to the lcm. If `a>=2`, the full 2-power is carried by its own block except for the only permissible combined block, `Phi_12`, which is available precisely when `a=2` and `v_3(m)=1`.

These conditions also show there are no repetitions of factors or `Phi_1` or `Phi_2` factors at minimum dimension. Conversely, direct inspection shows every listed characteristic polynomial has degree `psi(m)` and lcm of indices `m`. Integer cyclotomic companion blocks realize it.

Finally, finite-order rational representations are semisimple; a direct sum of the simple modules `Q[X]/(Phi_d)` is determined up to isomorphism by their multiplicities. Therefore its characteristic polynomial determines rational conjugacy, and distinct listed polynomials give distinct rational conjugacy classes. This argument makes **no assertion about integral conjugacy**.

The exact number of rational conjugacy classes is consequently

\[
c(m)=\begin{cases}
1,&a=0,\\
2^r-1,&a=1,\\
3\cdot2^{r-1},&a=2\text{ and }v_3(m)=1,\\
2^r,&a\ge2\text{ otherwise}.
\end{cases}
\]

The exceptional orders 1 and 2 also have one class each, in dimensions 0 and 1 respectively.

Examples:

| Order | Minimum dimension | Rational classes |
|---:|---:|---:|
| 6 | 2 | 1 |
| 12 | 4 | 3 |
| 24 | 6 | 2 |
| 30 | 6 | 3 |
| 36 | 8 | 2 |
| 60 | 8 | 6 |
| 120 | 10 | 4 |
| 210 | 12 | 7 |
| 420 | 14 | 12 |

For example, order 12 in minimum dimension 4 has characteristic polynomials `Phi_3 Phi_4`, `Phi_6 Phi_4`, and `Phi_12`; order 30 in dimension 6 has `Phi_3 Phi_10`, `Phi_6 Phi_5`, and `Phi_6 Phi_10`.

**Independent finite check.** The standalone verifier `scripts/check_minimal_classes.py` uses standard-library Python to enumerate all cyclotomic multisets with `sum phi(d_j)=psi(m)` and `lcm(d_j)=m`, including repetitions and indices 1 and 2, for every `1<=m<=500` by default (using the correct minimum dimension 1 at `m=2`). It also checks the least dimension at which a determinant -1 class occurs, within the proved bound `psi(m)+1`, and verifies the listed characteristic-polynomial constructions. Run `python scripts/check_minimal_classes.py`; this computation is a sanity check, not the proof or a Lean certificate.

## 4. Bibliographic boundary

Vaidyanathaswamy, *On the Possible Periods of Integer-Matrices*, Journal of the London
Mathematical Society 3 (1928), pp. 268–272, already identifies the exceptional equality
pair of prime powers 3 and 4 on p. 271. That source observation is used in (2) and
explains the `Phi_12` option in the minimum-dimension classification above. The preceding
note, *Integer-Roots of the Unit Matrix*, pp. 121–124, gives the cyclotomic degree/LCM
framework on pp. 122–123 and explicitly distinguishes it from integral conjugacy.
Both notes were recovered from the [original 1928 volume](https://dspace.bcu-iasi.ro/handle/123456789/43233);
see [SOURCES.md](SOURCES.md) for the scan and precise page correspondence.

Bamberg, Cairns and Kilminster, *The Crystallographic Restriction, Permutations, and Goldbach's Conjecture*, American Mathematical Monthly 110 (2003), pp. 202–209, Proposition 3(2) and its proof on p. 207 explicitly prove the odd-squarefree surjectivity formalized in `Extensions.lean`. Author-hosted primary text:

https://cage.ugent.be/~bamberg/Research_files/The%20crystallographic%20restriction,%20permutations%20and%20Goldbach%27s%20conjecture.pdf

The paper notes that `psi` is onto the nonnegative even integers and proves this by the same Bertrand induction. The determinant and minimum-conjugacy derivations above should be described as additional consequences established in the consult. Their appearance here is not evidence of mathematical novelty, and they must not be listed as kernel-verified claims without a Lean formalization.
