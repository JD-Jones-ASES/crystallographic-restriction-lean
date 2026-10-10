#!/usr/bin/env python3
"""Exhaustively check the handwritten minimum-dimension consequences.

Enumerate all characteristic polynomials of finite-order rational matrices with
order m and dimension at most psi(m)+1. A polynomial is encoded by the multiset
of its cyclotomic indices. Dynamic programming counts every multiplicity choice,
including Phi_1 and Phi_2, with dimension, lcm of indices, and determinant sign
as the state. This enumeration does not assume the classification being checked.

The checks cover m=1,...,500 by default, using only Python's standard library.
They provide finite sanity checks for MATHEMATICAL-EXTENSIONS.md; they are not
Lean proofs and do not establish the all-orders assertions by computation.
"""

import argparse
from math import gcd


def require(condition, message):
    """Remain effective when run with python -O."""
    if not condition:
        raise RuntimeError(message)


def lcm(a, b):
    return a // gcd(a, b) * b


def factorization(m):
    require(m > 0, "factorization is used only on positive integers")
    result = {}
    p = 2
    while p * p <= m:
        while m % p == 0:
            result[p] = result.get(p, 0) + 1
            m //= p
        p += 1
    if m > 1:
        result[m] = 1
    return result


def totient(m):
    result = m
    for p in factorization(m):
        result = result // p * (p - 1)
    return result


def psi(m):
    return sum(
        p ** (e - 1) * (p - 1)
        for p, e in factorization(m).items()
        if (p, e) != (2, 1)
    )


def all_characteristic_polynomial_counts(m, max_dimension):
    """Count all multisets of cyclotomic indices within the dimension budget.

    Keys are (dimension, lcm_of_indices, minus_one_multiplicity_mod_two).
    The last coordinate records determinant -1 precisely when it equals 1.
    """
    states = {(0, 1, 0): 1}
    for d in range(1, m + 1):
        if m % d:
            continue
        cost = totient(d)
        if cost > max_dimension:
            continue
        following = {}
        for (dimension, order, sign), count in states.items():
            for multiplicity in range((max_dimension - dimension) // cost + 1):
                key = (
                    dimension + multiplicity * cost,
                    lcm(order, d) if multiplicity else order,
                    sign ^ (multiplicity % 2 if d == 2 else 0),
                )
                following[key] = following.get(key, 0) + count
        states = following
    return states


def predicted_minimal_types(m):
    """The explicitly classified polynomials; each tuple lists its indices."""
    if m == 1:
        return {()}
    if m == 2:
        return {(2,)}
    fac = factorization(m)
    a = fac.get(2, 0)
    odd_powers = [p ** e for p, e in fac.items() if p != 2]
    if a == 0:
        return {tuple(sorted(odd_powers))}
    types = set()
    for choices in range(1 << len(odd_powers)):
        if a == 1 and choices == 0:
            continue
        indices = [
            q * (2 if choices & (1 << i) else 1)
            for i, q in enumerate(odd_powers)
        ]
        if a >= 2:
            indices.append(2 ** a)
        types.add(tuple(sorted(indices)))
    if a == 2 and fac.get(3, 0) == 1:
        remaining = [q for q in odd_powers if q != 3]
        for choices in range(1 << len(remaining)):
            indices = [12] + [
                q * (2 if choices & (1 << i) else 1)
                for i, q in enumerate(remaining)
            ]
            types.add(tuple(sorted(indices)))
    return types


def predicted_class_count(m):
    if m <= 2:
        return 1
    fac = factorization(m)
    a = fac.get(2, 0)
    r = len(fac) - int(2 in fac)
    if a == 0:
        return 1
    if a == 1:
        return 2 ** r - 1
    if a == 2 and fac.get(3, 0) == 1:
        return 3 * 2 ** (r - 1)
    return 2 ** r


def check_order(m):
    cost = psi(m)
    minimal_dimension = 1 if m == 2 else cost
    states = all_characteristic_polynomial_counts(m, cost + 1)
    observed_count = sum(
        states.get((minimal_dimension, m, sign), 0) for sign in (0, 1)
    )
    expected_count = predicted_class_count(m)
    require(
        observed_count == expected_count,
        "order {}: enumerated {} classes, predicted {}".format(
            m, observed_count, expected_count
        ),
    )

    types = predicted_minimal_types(m)
    require(len(types) == expected_count, "duplicate or missing constructed class")
    for indices in types:
        dimension = sum(totient(d) for d in indices)
        order = 1
        for d in indices:
            order = lcm(order, d)
        require(
            dimension == minimal_dimension and order == m,
            "order {}: invalid constructed polynomial {}".format(m, indices),
        )

    negative_dimensions = [
        n for n in range(cost + 2) if states.get((n, m, 1), 0)
    ]
    actual_negative_minimum = min(negative_dimensions) if negative_dimensions else None
    expected_negative_minimum = cost + 1 if m % 2 == 0 else None
    require(
        actual_negative_minimum == expected_negative_minimum,
        "order {}: determinant -1 minimum {}, expected {}".format(
            m, actual_negative_minimum, expected_negative_minimum
        ),
    )
    return observed_count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-order", type=int, default=500)
    args = parser.parse_args()
    if args.max_order < 1:
        parser.error("--max-order must be positive")
    total_classes = sum(check_order(m) for m in range(1, args.max_order + 1))
    print(
        "PASS: orders 1..{}; {} minimum-dimension rational classes; "
        "all determinant -1 minimum dimensions and constructions agree.".format(
            args.max_order, total_classes
        )
    )
    print("Finite external sanity check only; the all-orders arguments are handwritten.")


if __name__ == "__main__":
    main()
