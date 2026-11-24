import Mathlib

/-!
# Gap — the Lean twin of ZTL's strict bound (`zgap.py`, 2026-11-24)

ZTL's numeric floor marks an interval end as EXCLUDED (`Gap`): `x=(0,inf]` reads x > 0, a witnessed gap from 0
(VR's `rlt`). The Python floor keeps the mark through `+`, `-`, a reciprocal and the comparisons; everywhere else the
mark is dropped, which reads the end as closed (wider, sound). This module proves, over any linear ordered field, the
rules the Python floor applies:

* `add_lo` / `add_hi`: an end of a sum is excluded iff an end that makes it is (for independent readings: a
  reading of the sum reaches the end only when both summands reach theirs);
* `sub_lo`: the same for a difference;
* `inv_pos_lo`: the reciprocal of a divisor in `(0, h]` lies in `[1/h, ∞)` — no reading is 0;
* the comparison rules: a top end 0 that is excluded gives `d < 0` (`lt_of_top_excl`), a bottom end 0 that is
  excluded gives `0 < d` (`pos_of_bot_excl`), and an excluded 0 at either end gives `d ≠ 0` (`ne_of_excl`).

The product's rule (an extreme excluded iff every corner reaching it uses an excluded end, a closed 0 factor
attaining 0) is NOT proved here. It is measured in ZTL `test_znum_gap.py` and `test_intwords.py` by exhaustive
grids.

An end is a value plus a flag: `excl = true` means the value itself is not a reading.
-/

namespace ZGap

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `x` is above a lower end `(a, excl)`: strictly when the end is excluded. -/
def AboveLo (a : K) (excl : Bool) (x : K) : Prop := if excl then a < x else a ≤ x
/-- `x` is below an upper end `(b, excl)`. -/
def BelowHi (b : K) (excl : Bool) (x : K) : Prop := if excl then x < b else x ≤ b

theorem add_lo {a c x y : K} {ea ec : Bool} (hx : AboveLo a ea x) (hy : AboveLo c ec y) :
    AboveLo (a + c) (ea || ec) (x + y) := by
  unfold AboveLo at *
  cases ea <;> cases ec <;> simp at hx hy ⊢ <;> linarith

theorem add_hi {b d x y : K} {eb ed : Bool} (hx : BelowHi b eb x) (hy : BelowHi d ed y) :
    BelowHi (b + d) (eb || ed) (x + y) := by
  unfold BelowHi at *
  cases eb <;> cases ed <;> simp at hx hy ⊢ <;> linarith

/-- `x − y`'s lower end is `a − d` (x's bottom minus y's top), excluded iff either is. -/
theorem sub_lo {a d x y : K} {ea ed : Bool} (hx : AboveLo a ea x) (hy : BelowHi d ed y) :
    AboveLo (a - d) (ea || ed) (x - y) := by
  unfold AboveLo BelowHi at *
  cases ea <;> cases ed <;> simp at hx hy ⊢ <;> linarith

/-- A divisor in `(0, h]` has a reciprocal `≥ 1/h`; no reading of it is 0. -/
theorem inv_pos_lo {h y : K} (hy0 : 0 < y) (hyh : y ≤ h) : 1 / h ≤ 1 / y ∧ y ≠ 0 :=
  ⟨one_div_le_one_div_of_le hy0 hyh, ne_of_gt hy0⟩

/-- The comparison rule `d < 0` from a top end 0 that is EXCLUDED (closed, it gives only `d ≤ 0`). -/
theorem lt_of_top_excl {d : K} (h : BelowHi 0 true d) : d < 0 := by
  simpa [BelowHi] using h

theorem pos_of_bot_excl {d : K} (h : AboveLo 0 true d) : 0 < d := by
  simpa [AboveLo] using h

/-- Apartness (VR's `rapart`): an excluded 0 at either end and `d ≠ 0`. -/
theorem ne_of_excl {d : K} (h : AboveLo 0 true d ∨ BelowHi 0 true d) : d ≠ 0 := by
  rcases h with h | h
  · exact ne_of_gt (pos_of_bot_excl h)
  · exact ne_of_lt (lt_of_top_excl h)

/-- The other side: a CLOSED end decides nothing strict — 0 itself is a reading of `[0, 1]`. -/
theorem closed_end_reaches : ∃ d : K, AboveLo 0 false d ∧ ¬ (0 < d) :=
  ⟨0, by simp [AboveLo], lt_irrefl 0⟩

end ZGap

#print axioms ZGap.add_lo
#print axioms ZGap.add_hi
#print axioms ZGap.sub_lo
#print axioms ZGap.inv_pos_lo
#print axioms ZGap.lt_of_top_excl
#print axioms ZGap.pos_of_bot_excl
#print axioms ZGap.ne_of_excl
#print axioms ZGap.closed_end_reaches
