module

public import Crystallographic.Psi

/-!
# A kernel-computable `ψ`

`psi` is defined through `Nat.factorization`, which the kernel cannot evaluate. `psiC` computes the
same function by trial division with a fuel argument (structural recursion, so `decide +kernel`
reduces it): `psiAux fuel p m` sums the `ψ`-terms of the prime powers of `m` whose primes are
`≥ p`, under the invariant that `m` has no prime factor below `p` and `m < (p + fuel)²`. If `m ≤ 1`
the sum is `0`; if `1 < m < p²` then `m` is prime and contributes `m − 1` (or `0` when `m = 2`);
otherwise, when `p ∣ m`, `p` is prime, `stripPow` removes it (`m = p ^ k * m'`, `p ∤ m'`), the term
is `φ (p ^ k)` (or `0` when `p ^ k = 2`) and the loop continues at `p + 1` on `m'`; when `p ∤ m`
the loop continues at `p + 1` on `m`. Lane: **compute** (proves `psiC_eq_psi`; the definitions are
the desk's and are shared with the **tables** lane, so change them only by agreement).
-/

@[expose] public section

namespace Crystallographic

/-- `stripPow p fuel m = (k, m')` with `m = p ^ k * m'` and `p ∤ m'`, for `1 < p`, `0 < m ≤ fuel`. -/
def stripPow (p : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, m => (0, m)
  | fuel + 1, m =>
    if 1 < p ∧ 0 < m ∧ p ∣ m then
      match stripPow p fuel (m / p) with
      | (k, r) => (k + 1, r)
    else (0, m)

/-- The trial-division loop; see the module docstring. -/
def psiAux : ℕ → ℕ → ℕ → ℕ
  | fuel, p, m =>
    if m ≤ 1 then 0
    else if m < p * p then (if m = 2 then 0 else m - 1)
    else
      match fuel with
      | 0 => 0
      | fuel + 1 =>
        if p ∣ m then
          match stripPow p m m with
          | (k, r) => (if p ^ k = 2 then 0 else p ^ (k - 1) * (p - 1)) + psiAux fuel (p + 1) r
        else psiAux fuel (p + 1) m

/-- The kernel-computable `ψ`. -/
def psiC (m : ℕ) : ℕ := psiAux m 2 m

theorem stripPow_spec {p fuel m : ℕ} (hp : 1 < p) (hm : 0 < m) (hfuel : m ≤ fuel) :
    m = p ^ (stripPow p fuel m).1 * (stripPow p fuel m).2 ∧ ¬ p ∣ (stripPow p fuel m).2 := sorry

theorem psiAux_eq {fuel p m : ℕ} (hp : 2 ≤ p) (hfuel : m < (p + fuel) * (p + fuel))
    (hmin : ∀ q, q.Prime → q ∣ m → p ≤ q) : psiAux fuel p m = psi m := sorry

theorem psiC_eq_psi (m : ℕ) : psiC m = psi m := sorry

end Crystallographic
