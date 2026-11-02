-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-03.
import ZClassical.Bridge
import ZClassical.Zeta
/-!
# ZClassical.ZetaReading — the bridge on one case: "S = S" for S = 1 + 2 + 3 + …

Atom 0 is p = "the value of S read here is −1/12", dirty: the reading method's answer depends on how S is presented.
The formula `xnor p p` ("p iff p") is the step every manipulation of S takes for granted: two occurrences of S carry one
value. Under the bridge (`ZClassical.Bridge.dispositions`):

* every UNIFORM reading makes it true (p ↔ p), so it is EARNED IF STABLE;
* one OCCURRENCE reading makes it false, and ζ supplies it: read S itself as ζ(−1) (= −1/12, true) and the occurrence
  presented as 0 + S as ζ(−1) − ζ(0) (= 5/12, so "= −1/12" is false). So it is NOT EARNED.

The reading of the two presentations through ζ is a model of the occurrences, not a theorem about them; the numbers in
it are Mathlib's theorems (`ZClassical.Zeta`).
-/
namespace ZClassical.ZetaReading
open V V.Speak ZClassical.Bridge Classical

/-- the method is not fixed: atom 0 is dirty -/
def v : Nat → V := fun _ => .Z

/-- p ↔ p, for p = "the value of S read here is −1/12" -/
def selfEq : Fm := .xnor (.atom 0) (.atom 0)

/-- ζ's reading of the two occurrences: the left one is S, the right one is S presented as 0 + S -/
def zetaJ : List Bool → Prop
  | false :: _ => riemannZeta (-1) = -1 / 12
  | _          => riemannZeta (-1) - riemannZeta 0 = -1 / 12

theorem zeta_reading_breaks : ¬ semO v zetaJ selfEq := by
  have hl : riemannZeta (-1) = -1 / 12 := riemannZeta_neg_one
  have hr : ¬ (riemannZeta (-1) - riemannZeta 0 = -1 / 12) := by
    rw [shifted_value]; norm_num
  show ¬ bin (fun a b => a == b) (riemannZeta (-1) = -1 / 12) (riemannZeta (-1) - riemannZeta 0 = -1 / 12)
  unfold bin
  rw [decide_eq_true hl, decide_eq_false hr]
  decide

theorem uniform_holds (I : Nat → Prop) : semU v I selfEq := by
  show bin (fun a b => a == b) (I 0) (I 0)
  unfold bin
  cases decide (I 0) <;> rfl

/-- **"S = S" for 1 + 2 + 3 + …: EARNED IF STABLE, not EARNED** — and the reading that blocks EARNED is ζ's own. -/
theorem selfEq_disposition : EarnedIfStable v selfEq ∧ ¬ StrictEarned v selfEq := by
  have d := dispositions v selfEq
  have notAll : ¬ ∀ J, semO v J selfEq := fun h => zeta_reading_breaks (h zetaJ)
  exact ⟨d.2.2.1.mpr ⟨notAll, uniform_holds⟩, fun h => notAll (d.1.mp h)⟩

end ZClassical.ZetaReading

#print axioms ZClassical.ZetaReading.zeta_reading_breaks
#print axioms ZClassical.ZetaReading.selfEq_disposition
