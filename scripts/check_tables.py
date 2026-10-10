#!/usr/bin/env python3
"""Standard-library replay of the tables in Challenge.lean.

Two independent computations of the additive totient psi (Bamberg-Cairns-Kilminster 2003, p. 202) (through the prime factorization, and
through the exact prime-power divisors), the sets {m >= 1 : psi(m) <= N} for N = 1..12 computed with the
bound m <= 2^(N+1) and again by brute force to 10^5, the largest element of each, and the comparison
against the set literals of the theorems finiteOrders_<N> and the values of isGreatest_finiteOrders_<N> in
Challenge.lean. Also checks, to 10^5, the arithmetic the Challenge states: psi(m) = 0 iff m <= 2, psi is
even, psi <= phi, m <= 2^(psi m + 1), and additivity on coprime pairs a, b < 2000 with ab <= 100000. Finally it re-derives the
rows psi^{-1}{n} of Table 1 of Bamberg-Cairns-Kilminster (2003) for even n <= 24 by the structural
enumeration (products of prime powers q <= 2n with distinct primes, since phi(q) <= n forces q <= 2n), checks
the enumeration against brute force for n <= 14, compares each row with the printed one (transcribed below from
p. 204 of the authors' PDF) and requires exactly the omissions the theorems psi_2520, psi_2310 and
psi_eq_twentyfour state, with nothing wrong in the printed rows. Exact integers only; no dependencies beyond
the standard library. Last line: VERDICT: PASS or VERDICT: FAIL; exit status 0 on PASS.
"""

from math import gcd
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
WORDS = ["one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve"]
BOUND = 100_000


def factorization(m):
    out = {}
    p = 2
    while p * p <= m:
        while m % p == 0:
            out[p] = out.get(p, 0) + 1
            m //= p
        p += 1
    if m > 1:
        out[m] = out.get(m, 0) + 1
    return out


def totient(n):
    result = n
    for p in factorization(n):
        result = result // p * (p - 1)
    return result if n > 0 else 0


def psi_factorization(m):
    return sum(0 if p ** k == 2 else p ** (k - 1) * (p - 1) for p, k in factorization(m).items())


def psi_divisors(m):
    """The sum of phi(d) over the divisors d != 2 of m that are prime powers coprime to m / d."""
    total = 0
    for d in range(2, m + 1):
        if m % d == 0 and gcd(d, m // d) == 1 and d != 2 and len(factorization(d)) == 1:
            total += sum(1 for a in range(1, d + 1) if gcd(a, d) == 1)
    return total


# Table 1 of Bamberg-Cairns-Kilminster, Amer. Math. Monthly 110 (2003) 202-209, p. 204: the rows psi^{-1}{n}
# (the orders of GL(n, Z) that are not orders of GL(n - 1, Z)) for even n <= 24, as printed.
BCK_TABLE_1 = {
    2: [3, 4, 6], 4: [5, 8, 10, 12], 6: [7, 9, 14, 15, 18, 20, 24, 30], 8: [16, 21, 28, 36, 40, 42, 60],
    10: [11, 22, 35, 45, 48, 56, 70, 72, 84, 90, 120],
    12: [13, 26, 33, 44, 63, 66, 80, 105, 126, 140, 168, 180, 210],
    14: [39, 52, 55, 78, 88, 110, 112, 132, 144, 240, 252, 280, 360, 420],
    16: [17, 32, 34, 65, 77, 99, 104, 130, 154, 156, 165, 198, 220, 264, 315, 330, 336, 504, 630, 840],
    18: [19, 27, 38, 51, 54, 68, 91, 96, 102, 117, 176, 182, 195, 231, 234, 260, 308, 312, 390, 396, 440, 462,
         560, 660, 720, 1260],
    20: [25, 50, 57, 76, 85, 108, 114, 136, 160, 170, 204, 208, 273, 364, 385, 468, 495, 520, 528, 546, 616,
         770, 780, 792, 924, 990, 1008, 1320, 1680],
    22: [23, 46, 75, 95, 100, 119, 135, 143, 150, 152, 153, 190, 216, 224, 228, 238, 255, 270, 286, 288, 306,
         340, 408, 455, 480, 510, 585, 624, 693, 728, 880, 910, 936, 1092, 1155, 1170, 1386, 1540, 1560, 1848,
         1980],
    24: [69, 92, 133, 138, 171, 189, 200, 266, 272, 285, 300, 342, 357, 378, 380, 429, 456, 476, 540, 570, 572,
         612, 672, 680, 714, 819, 858, 1020, 1040, 1232, 1365, 1584, 1638, 1820],
}
EXPECTED_OMISSIONS = {20: [2520], 22: [2310],
                      24: [2184, 2340, 2640, 2730, 2772, 3080, 3960, 4620, 5040]}


def prime_powers_upto(bound):
    out = []
    for p in range(2, bound + 1):
        if all(p % d for d in range(2, int(p ** 0.5) + 1)):
            q = p
            while q <= bound:
                out.append((p, q))
                q *= p
    return out


def psi_preimage(n):
    """The m with psi(m) = n, by the structural enumeration: m is a product of prime powers q with distinct
    primes, and every q != 2 has phi(q) <= n, hence q <= 2n."""
    pps = prime_powers_upto(2 * n)
    primes = sorted({p for p, _ in pps})
    found = set()

    def rec(i, m, s):
        if s == n:
            found.add(m)
        if i == len(primes) or s > n:
            return
        rec(i + 1, m, s)
        p = primes[i]
        for pp, q in pps:
            if pp == p:
                t = 0 if q == 2 else q // p * (p - 1)
                if s + t <= n:
                    rec(i + 1, m * q, s + t)
    rec(0, 1, 0)
    return sorted(found)


def table_literals(text):
    tables = {}
    for word in WORDS:
        m = re.search(r"theorem finiteOrders_" + word + r"\s*:\s*finiteOrders (\d+) = \{([^}]*)\}", text, re.S)
        if not m:
            raise SystemExit(f"finiteOrders_{word} not found in Challenge.lean")
        tables[int(m.group(1))] = sorted(int(x) for x in m.group(2).replace("\n", " ").split(","))
    maxima = {}
    for m in re.finditer(r"theorem isGreatest_finiteOrders_(\w+)\s*:\s*IsGreatest \(finiteOrders (\d+)\) (\d+)", text):
        maxima[int(m.group(2))] = int(m.group(3))
    return tables, maxima


def main():
    ok = True

    def check(name, good, detail=""):
        nonlocal ok
        ok &= bool(good)
        print(f"[{'ok' if good else 'FAIL'}] {name}" + (f": {detail}" if detail else ""))

    psi = [0] * (BOUND + 1)
    for m in range(BOUND + 1):
        psi[m] = psi_factorization(m)
    check("psi by two routes agrees to 3000", all(psi[m] == psi_divisors(m) for m in range(3001)))
    check("psi(m) = 0 iff m <= 2", all((psi[m] == 0) == (m <= 2) for m in range(BOUND + 1)))
    check("psi is even", all(psi[m] % 2 == 0 for m in range(BOUND + 1)))
    check("psi <= phi", all(psi[m] <= totient(m) for m in range(1, BOUND + 1)))
    check("m <= 2^(psi m + 1)", all(m <= 2 ** (psi[m] + 1) for m in range(1, BOUND + 1)))
    check("psi(ab) = psi(a) + psi(b) for coprime a, b < 2000 with ab <= 100000",
          all(psi[a * b] == psi[a] + psi[b] for a in range(1, 2000) for b in range(1, 2000)
              if gcd(a, b) == 1 and a * b <= BOUND))

    text = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    tables, maxima = table_literals(text)
    for N in range(1, 13):
        bounded = [m for m in range(1, 2 ** (N + 1) + 1) if psi[m] <= N]
        brute = [m for m in range(1, BOUND + 1) if psi[m] <= N]
        check(f"Ord_{N} with the bound equals the brute force", bounded == brute, f"{len(brute)} orders")
        check(f"finiteOrders_{WORDS[N - 1]} literal", tables[N] == brute,
              f"max {max(brute)}" if tables[N] == brute else f"literal {tables[N]} vs {brute}")
        if N in maxima:
            check(f"isGreatest_finiteOrders_{WORDS[N - 1]} value", maxima[N] == max(brute), str(maxima[N]))
    check("maxima stated for N = 1, 2, 4, 6, 8, 10, 12", sorted(maxima) == [1, 2, 4, 6, 8, 10, 12])

    for n, printed in BCK_TABLE_1.items():
        true_row = psi_preimage(n)
        check(f"psi^-1({n}): every enumerated value has psi = {n}", all(psi_factorization(m) == n for m in true_row))
        if n <= 14:
            check(f"psi^-1({n}): the enumeration equals the brute force to 2^(n+1)",
                  true_row == [m for m in range(1, 2 ** (n + 1) + 1) if psi_factorization(m) == n])
        wrong = sorted(set(printed) - set(true_row))
        omitted = sorted(set(true_row) - set(printed))
        check(f"BCK Table 1 row {n}: no wrong entry", not wrong, str(wrong) if wrong else "")
        check(f"BCK Table 1 row {n}: omissions {EXPECTED_OMISSIONS.get(n, [])}",
              omitted == EXPECTED_OMISSIONS.get(n, []), str(omitted))

    print("VERDICT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
