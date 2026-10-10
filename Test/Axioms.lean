module

import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

A module file importing `Solution` (not `Challenge.lean`). Walks every constant of the environment
whose name begins with `Crystallographic.`, `_private.Crystallographic.` or `_private.Solution.` (the public declarations of
this development; the private auxiliaries that Lean generates are not enumerated under the module
system, but `collectAxioms` reaches every private constant a public proof refers to, including a
private `axiom`), and collects the axioms each depends on. Anything outside `propext`,
`Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`. The audit
also fails if it matched fewer constants than the floor below (so a renamed namespace cannot make it
pass vacuously) or if any of the compared theorems is missing from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "Crystallographic." || label.startsWith "_private.Crystallographic." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 200 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 200"
  for n in [`Crystallographic.psi_eq_zero_iff, `Crystallographic.psi_prime_pow,
      `Crystallographic.psi_mul, `Crystallographic.psi_le_totient, `Crystallographic.even_psi,
      `Crystallographic.psi_eq_sum_divisors, `Crystallographic.le_two_pow_psi,
      `Crystallographic.psi_orderOf_le, `Crystallographic.exists_orderOf_eq,
      `Crystallographic.exists_orderOf_eq_iff, `Crystallographic.finiteOrders_eq,
      `Crystallographic.isLeast_dimension, `Crystallographic.exists_orderOf_eq_totient,
      `Crystallographic.exists_orderOf_eq_iff_rat, `Crystallographic.finiteOrders_zero,
      `Crystallographic.finiteOrders_mono, `Crystallographic.finiteOrders_succ_of_even,
      `Crystallographic.le_two_pow_of_mem_finiteOrders, `Crystallographic.finiteOrders_finite,
      `Crystallographic.exists_orderOf_eq_iff_sl, `Crystallographic.orderOf_sl_one,
      `Crystallographic.finiteOrders_one, `Crystallographic.finiteOrders_two,
      `Crystallographic.finiteOrders_three, `Crystallographic.finiteOrders_four,
      `Crystallographic.finiteOrders_five, `Crystallographic.finiteOrders_six,
      `Crystallographic.finiteOrders_seven, `Crystallographic.finiteOrders_eight,
      `Crystallographic.finiteOrders_nine, `Crystallographic.finiteOrders_ten,
      `Crystallographic.finiteOrders_eleven, `Crystallographic.finiteOrders_twelve,
      `Crystallographic.psi_2520, `Crystallographic.psi_2310,
      `Crystallographic.psi_eq_twentyfour, `Crystallographic.isLeast_dimension_2520,
      `Crystallographic.isLeast_dimension_2310, `Crystallographic.isLeast_dimension_twentyfour,
      `Crystallographic.isGreatest_finiteOrders_one,
      `Crystallographic.isGreatest_finiteOrders_two,
      `Crystallographic.isGreatest_finiteOrders_four,
      `Crystallographic.isGreatest_finiteOrders_six,
      `Crystallographic.isGreatest_finiteOrders_eight,
      `Crystallographic.isGreatest_finiteOrders_ten,
      `Crystallographic.isGreatest_finiteOrders_twelve,
      `Crystallographic.exists_odd_squarefree_psi_eq, `Crystallographic.range_psi,
      `Crystallographic.finiteOrders_subset_iff, `Crystallographic.finiteOrders_eq_iff,
      `Crystallographic.exists_new_odd_squarefree_order,
      `Crystallographic.exists_integral_invariant_posDef,
      `Crystallographic.exists_integral_posDef_isometry_iff] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
