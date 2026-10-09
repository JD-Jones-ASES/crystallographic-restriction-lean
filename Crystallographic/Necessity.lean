module

public import Crystallographic.Psi

/-!
# Necessity: `ψ (orderOf A) ≤ N`

Over `ℚ`: for `A : GL (Fin N) ℚ` of finite order `m`, the minimal polynomial `f` of the matrix
divides `X ^ m − 1 = ∏_{d ∣ m} Φ_d`. Let `S = {d ∣ m : Φ_d ∣ f}`. The `Φ_d` are pairwise coprime
irreducibles over `ℚ`, so `∏_{d ∈ S} Φ_d ∣ f`, whence `∑_{d ∈ S} φ d ≤ natDegree f ≤ N`
(`Matrix.minpoly_dvd_charpoly`, `Matrix.charpoly_natDegree_eq_dim`). If some prime power `p ^ k`
exactly dividing `m` divided no `d ∈ S`, then `f` would be coprime to every `Φ_d` with `d ∣ m`,
`p ^ k ∣ d`, hence would divide `∏_{d ∣ m / p} Φ_d = X ^ (m / p) − 1`, so `A ^ (m / p) = 1`,
contradicting `orderOf A = m`. Then `psi_le_sum_totient` gives `ψ m ≤ ∑_{d ∈ S} φ d ≤ N`.
For infinite order `orderOf A = 0` and `ψ 0 = 0`. Over `ℤ`: map to `ℚ` by the injective
hom `Units.map (RingHom.mapMatrix (Int.castRingHom ℚ))`, which preserves `orderOf`.
Lane: **necessity**.
-/

@[expose] public section

namespace Crystallographic

/-- Necessity over `ℚ`. -/
theorem psi_orderOf_le_rat {N : ℕ} (A : Matrix.GeneralLinearGroup (Fin N) ℚ) :
    psi (orderOf A) ≤ N := sorry

theorem psi_orderOf_le_internal {N : ℕ} (A : Matrix.GeneralLinearGroup (Fin N) ℤ) :
    psi (orderOf A) ≤ N := sorry

end Crystallographic
