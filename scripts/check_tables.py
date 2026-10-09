#!/usr/bin/env python3
"""Standard-library replay of the tables in Challenge.lean.

Two independent computations of Hiller's additive totient psi (through the prime factorization, and
through the exact prime-power divisors), the sets {m >= 1 : psi(m) <= N} for N = 1..12 computed with the
bound m <= 2^(N+1) and again by brute force to 10^5, the largest element of each, and the comparison
against the set literals of the theorems finiteOrders_<N> and the values of isGreatest_finiteOrders_<N> in
Challenge.lean. Also checks, to 10^5, the arithmetic the Challenge states: psi(m) = 0 iff m <= 2, psi is
even, psi <= phi, m <= 2^(psi m + 1), additivity on coprime pairs below 2000. Exact integers only; no
dependencies beyond the standard library. Last line: VERDICT: PASS or VERDICT: FAIL; exit status 0 on PASS.
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
    check("psi(ab) = psi(a) + psi(b) for coprime a, b < 2000",
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

    print("VERDICT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
