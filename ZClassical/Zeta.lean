import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Bernoulli
-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-02.
/-!
# ZClassical.Zeta — the CLASSICAL register: the analytic continuation's value at −1 is −1/12

Separate from ZTL's `ZZeta.lean` (zero axioms, Lean core, in the ZTL repository): this file rests on Mathlib's complex analysis and so on its
classical axioms (`#print axioms` below). It ties the finite operation of ZZeta (−B₂/2) to the function ζ.
-/

namespace ZClassical

theorem riemannZeta_neg_one : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  simp only [Nat.cast_one, pow_one] at h
  rw [h]
  norm_num

/-- ζ(0) = −1/2: the ζ-regularized value of 1 + 1 + 1 + …, so the ζ method cannot read S and 0 + S as one value
(ZZetaBridge.not_stable_of_ones); 0 + 1 + 2 + … gets ζ(−1) − ζ(0) = 5/12 -/
theorem riemannZeta_zero_val : riemannZeta 0 = -1 / 2 := riemannZeta_zero

theorem shifted_value : riemannZeta (-1) - riemannZeta 0 = 5 / 12 := by
  rw [riemannZeta_neg_one, riemannZeta_zero]; norm_num

end ZClassical

#print axioms ZClassical.riemannZeta_neg_one
#print axioms ZClassical.riemannZeta_zero_val
#print axioms ZClassical.shifted_value
