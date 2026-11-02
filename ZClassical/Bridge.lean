-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-03.
import ZSpeaks
import ClassicalAgreement
/-!
# ZClassical.Bridge — ZTL's six dispositions as statements of classical mathematics

ZTL's judge (ZTL, `lean/ZSpeaks.lean`) gives a formula φ over atoms, under a valuation v that marks each atom true (T),
false (F) or dirty (Z), one of six dispositions. This file translates each of them into a statement about
CLASSICAL PROPOSITIONS: a dirty atom may stand for any proposition at all, a clean atom for a proved (T) or refuted (F)
one. Two ways to let a dirty atom stand for propositions:

* **uniformly** — one proposition `I n` for atom n at every occurrence (`semU v I φ`): a completion of the atom;
* **occurrence by occurrence** — each occurrence its own proposition (`semO v J φ`, where `J` is read along the
  occurrence's position in the formula): ZTL's dirty reading, each occurrence read on its own.

**The bridge (`dispositions`).**
* EARNED            ⇔ φ holds under EVERY occurrence-by-occurrence reading;
* REFUTED           ⇔ φ fails under every occurrence-by-occurrence reading;
* EARNED IF STABLE  ⇔ φ holds under every uniform reading, but not under every occurrence-by-occurrence one;
* REFUTED IF STABLE ⇔ φ fails under every uniform reading, but not under every occurrence-by-occurrence one;
* ON CREDIT         ⇔ some uniform reading makes φ true and some makes it false, and ZTL's greedy register says T;
* OPEN              ⇔ the same disagreement, and the greedy register does not say T.
The first four are statements of classical mathematics outright. ON CREDIT and OPEN agree on the classical side —
the propositions consistent with the data DISAGREE about φ — and part only by ZTL's own greedy register (`evalF`), which
classical logic does not have: that is where classical mathematics is silent and ZTL still speaks.

Classical: the step from a proposition to its truth value uses excluded middle (`Classical.propDecidable`), so the
theorems here rest on `propext`, `Classical.choice`, `Quot.sound` — printed below. ZTL itself stays on the empty axiom
list; this is its classical register.
-/
namespace ZClassical.Bridge
open V V.Speak Classical

/-! ## Readings by propositions -/

/-- a binary connective over propositions, through its truth table `g` (excluded middle) -/
noncomputable def bin (g : Bool → Bool → Bool) (A B : Prop) : Prop :=
  g (decide A) (decide B) = true

/-- an atom's proposition: a clean atom is proved (T) or refuted (F); a dirty one is the proposition `P` given -/
def atomP (v : Nat → V) (P : Prop) (n : Nat) : Prop :=
  match v n with
  | .T => True
  | .F => False
  | .Z => P

/-- the UNIFORM reading: dirty atom n is the proposition `I n` at every occurrence (a completion) -/
noncomputable def semU (v : Nat → V) (I : Nat → Prop) : Fm → Prop
  | .atom n   => atomP v (I n) n
  | .top      => True
  | .bot      => False
  | .neg φ    => ¬ semU v I φ
  | .conj φ ψ => bin (fun a b => a && b) (semU v I φ) (semU v I ψ)
  | .disj φ ψ => bin (fun a b => a || b) (semU v I φ) (semU v I ψ)
  | .imp φ ψ  => bin (fun a b => !a || b) (semU v I φ) (semU v I ψ)
  | .xor φ ψ  => bin (fun a b => a != b) (semU v I φ) (semU v I ψ)
  | .xnor φ ψ => bin (fun a b => a == b) (semU v I φ) (semU v I ψ)

/-- the OCCURRENCE reading: `J` is read along the position — the left operand of a binary connective gets
`J (false :: _)`, the right one `J (true :: _)`; a dirty atom's occurrence is the proposition `J []` there -/
noncomputable def semO (v : Nat → V) : (List Bool → Prop) → Fm → Prop
  | J, .atom n   => atomP v (J []) n
  | _, .top      => True
  | _, .bot      => False
  | J, .neg φ    => ¬ semO v J φ
  | J, .conj φ ψ => bin (fun a b => a && b) (semO v (fun q => J (false :: q)) φ) (semO v (fun q => J (true :: q)) ψ)
  | J, .disj φ ψ => bin (fun a b => a || b) (semO v (fun q => J (false :: q)) φ) (semO v (fun q => J (true :: q)) ψ)
  | J, .imp φ ψ  => bin (fun a b => !a || b) (semO v (fun q => J (false :: q)) φ) (semO v (fun q => J (true :: q)) ψ)
  | J, .xor φ ψ  => bin (fun a b => a != b) (semO v (fun q => J (false :: q)) φ) (semO v (fun q => J (true :: q)) ψ)
  | J, .xnor φ ψ => bin (fun a b => a == b) (semO v (fun q => J (false :: q)) φ) (semO v (fun q => J (true :: q)) ψ)

/-- two readings side by side: the left operand's and the right operand's -/
def split (J1 J2 : List Bool → Prop) : List Bool → Prop
  | false :: q => J1 q
  | true :: q  => J2 q
  | []         => True

/-! ## The uniform reading is ZTL's completion -/

theorem dec_eq_of_iff {A : Prop} {x : Bool} (h : A ↔ x = true) :
    decide A = x := by
  cases x
  · exact decide_eq_false (fun a => absurd (h.mp a) (by decide))
  · exact decide_eq_true (h.mpr rfl)

theorem semU_cval (v : Nat → V) (I : Nat → Prop) (b : Nat → Bool)
    (hb : ∀ n, atomP v (I n) n ↔ b n = true) : ∀ φ : Fm, semU v I φ ↔ cval b φ = true := by
  intro φ
  induction φ with
  | atom n => exact hb n
  | top => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | bot => exact ⟨fun h => h.elim, fun h => nomatch h⟩
  | neg φ ih =>
      show ¬ semU v I φ ↔ (!cval b φ) = true
      cases hc : cval b φ <;> simp_all
  | conj φ ψ ihφ ihψ =>
      show bin _ _ _ ↔ _; unfold bin; rw [dec_eq_of_iff ihφ, dec_eq_of_iff ihψ]; rfl
  | disj φ ψ ihφ ihψ =>
      show bin _ _ _ ↔ _; unfold bin; rw [dec_eq_of_iff ihφ, dec_eq_of_iff ihψ]; rfl
  | imp φ ψ ihφ ihψ =>
      show bin _ _ _ ↔ _; unfold bin; rw [dec_eq_of_iff ihφ, dec_eq_of_iff ihψ]; rfl
  | xor φ ψ ihφ ihψ =>
      show bin _ _ _ ↔ _; unfold bin; rw [dec_eq_of_iff ihφ, dec_eq_of_iff ihψ]; rfl
  | xnor φ ψ ihφ ihψ =>
      show bin _ _ _ ↔ _; unfold bin; rw [dec_eq_of_iff ihφ, dec_eq_of_iff ihψ]; rfl

/-- the classical bits of a uniform reading -/
noncomputable def bitsOf (v : Nat → V) (I : Nat → Prop) (n : Nat) : Bool :=
  match v n with
  | .T => true
  | .F => false
  | .Z => decide (I n)

theorem bitsOf_spec (v : Nat → V) (I : Nat → Prop) (n : Nat) : atomP v (I n) n ↔ bitsOf v I n = true := by
  unfold atomP bitsOf
  cases v n
  · exact ⟨fun _ => rfl, fun _ => trivial⟩
  · exact ⟨fun h => h.elim, fun h => nomatch h⟩
  · exact (decide_eq_true_iff).symm

/-- from a uniform reading, a total refinement of v (a completion) on which ZTL computes the reading's truth -/
theorem completion_of_reading (v : Nat → V) (I : Nat → Prop) :
    V.refines v (fun n => emb (bitsOf v I n)) ∧ total (fun n => emb (bitsOf v I n)) ∧
    ∀ φ, evalF (fun n => emb (bitsOf v I n)) φ = emb (cval (bitsOf v I) φ) := by
  refine ⟨fun n hz => ?_, fun n => ?_, fun φ => evalF_agrees _ φ⟩
  · show emb (bitsOf v I n) = v n
    unfold bitsOf
    cases h : v n
    · rfl
    · rfl
    · exact absurd h hz
  · show emb (bitsOf v I n) ≠ Z
    cases bitsOf v I n <;> intro e <;> exact nomatch e

/-- from a completion, the uniform reading it is -/
theorem reading_of_completion (v w : Nat → V) (hr : V.refines v w) (ht : total w) :
    ∀ φ, evalF w φ = emb (cval (fun n => decide (w n = T)) φ) ∧
      (∀ n, atomP v (w n = T) n ↔ decide (w n = T) = true) := by
  have hw : w = fun n => emb (decide (w n = T)) := by
    funext n
    have := ht n
    cases h : w n
    · rfl
    · rfl
    · exact absurd h this
  intro φ
  refine ⟨?_, fun n => ?_⟩
  · conv => lhs; rw [hw]
    exact evalF_agrees _ φ
  · unfold atomP
    cases hv : v n
    · have : w n = T := by rw [hr n (by rw [hv]; intro e; exact nomatch e), hv]
      simp [this]
    · have : w n = F := by rw [hr n (by rw [hv]; intro e; exact nomatch e), hv]
      simp [this]
    · exact (decide_eq_true_iff).symm

/-- **IF STABLE side.** ZTL's `Enum` (true in every completion: the judge's grant) is "true under every uniform
reading by propositions"; `StableF` is "false under every uniform reading". -/
theorem enum_iff (v : Nat → V) (φ : Fm) : Enum v φ ↔ ∀ I : Nat → Prop, semU v I φ := by
  constructor
  · intro h I
    obtain ⟨hr, ht, he⟩ := completion_of_reading v I
    have hT := h _ hr ht
    rw [he φ] at hT
    have hc : cval (bitsOf v I) φ = true := by
      cases hc : cval (bitsOf v I) φ
      · rw [hc] at hT; exact nomatch hT
      · rfl
    exact (semU_cval v I _ (bitsOf_spec v I) φ).mpr hc
  · intro h w hr ht
    obtain ⟨he, hb⟩ := reading_of_completion v w hr ht φ
    have := (semU_cval v (fun n => w n = T) _ hb φ).mp (h _)
    rw [he, this]; rfl

theorem stableF_iff (v : Nat → V) (φ : Fm) : StableF v φ ↔ ∀ I : Nat → Prop, ¬ semU v I φ := by
  constructor
  · intro h I hs
    obtain ⟨hr, ht, he⟩ := completion_of_reading v I
    have hF := h _ hr ht
    rw [he φ, (semU_cval v I _ (bitsOf_spec v I) φ).mp hs] at hF
    exact nomatch hF
  · intro h w hr ht
    obtain ⟨he, hb⟩ := reading_of_completion v w hr ht φ
    have hn : ¬ cval (fun n => decide (w n = T)) φ = true := fun hc =>
      h _ ((semU_cval v (fun n => w n = T) _ hb φ).mpr hc)
    rw [he]
    cases hc : cval (fun n => decide (w n = T)) φ
    · rfl
    · exact absurd hc hn

/-! ## The occurrence reading is ZTL's dirty reading -/

theorem any2 (f : Bool → Bool) : [true, false].any f = true ↔ ∃ a, f a = true := by
  constructor
  · intro h
    cases h1 : f true
    · cases h2 : f false
      · simp [List.any, h1, h2] at h
      · exact ⟨false, h2⟩
    · exact ⟨true, h1⟩
  · rintro ⟨a, ha⟩
    cases a <;> simp [List.any, ha]

theorem ok_iff (P : Bool × Bool) (S : (List Bool → Prop) → Prop)
    (h1 : P.1 = true ↔ ∃ J : List Bool → Prop, S J) (h2 : P.2 = true ↔ ∃ J : List Bool → Prop, ¬ S J) (a : Bool) :
    ok a P = true ↔ ∃ J : List Bool → Prop, decide (S J) = a := by
  cases a
  · show P.2 = true ↔ _
    rw [h2]
    exact ⟨fun ⟨J, hJ⟩ => ⟨J, decide_eq_false hJ⟩, fun ⟨J, hJ⟩ => ⟨J, of_decide_eq_false hJ⟩⟩
  · show P.1 = true ↔ _
    rw [h1]
    exact ⟨fun ⟨J, hJ⟩ => ⟨J, decide_eq_true hJ⟩, fun ⟨J, hJ⟩ => ⟨J, of_decide_eq_true hJ⟩⟩

/-- one binary connective: the dirty reading's two flags are "some occurrence reading makes it true / false" -/
theorem bin_case (g : Bool → Bool → Bool) (P Q : Bool × Bool) (SP SQ : (List Bool → Prop) → Prop)
    (hP1 : P.1 = true ↔ ∃ J : List Bool → Prop, SP J) (hP2 : P.2 = true ↔ ∃ J : List Bool → Prop, ¬ SP J)
    (hQ1 : Q.1 = true ↔ ∃ J : List Bool → Prop, SQ J) (hQ2 : Q.2 = true ↔ ∃ J : List Bool → Prop, ¬ SQ J) :
    ((comb g P Q).1 = true ↔ ∃ J : List Bool → Prop, bin g (SP (fun q => J (false :: q))) (SQ (fun q => J (true :: q)))) ∧
    ((comb g P Q).2 = true ↔ ∃ J : List Bool → Prop, ¬ bin g (SP (fun q => J (false :: q))) (SQ (fun q => J (true :: q)))) := by
  have oP := ok_iff P SP hP1 hP2
  have oQ := ok_iff Q SQ hQ1 hQ2
  constructor
  · show [true, false].any (fun a => [true, false].any (fun c => ok a P && ok c Q && g a c)) = true ↔ _
    rw [any2]
    constructor
    · rintro ⟨a, ha⟩
      rw [any2] at ha
      obtain ⟨c, hc⟩ := ha
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨ha, hc'⟩, hg⟩ := hc
      obtain ⟨J1, e1⟩ := (oP a).mp ha
      obtain ⟨J2, e2⟩ := (oQ c).mp hc'
      exact ⟨split J1 J2, by unfold bin; show g _ _ = true; rw [show (fun q => split J1 J2 (false :: q)) = J1 from rfl,
        show (fun q => split J1 J2 (true :: q)) = J2 from rfl, e1, e2]; exact hg⟩
    · rintro ⟨J, hJ⟩
      refine ⟨decide (SP (fun q => J (false :: q))), (any2 _).mpr
        ⟨decide (SQ (fun q => J (true :: q))), ?_⟩⟩
      simp only [Bool.and_eq_true]
      exact ⟨⟨(oP _).mpr ⟨_, rfl⟩, (oQ _).mpr ⟨_, rfl⟩⟩, hJ⟩
  · show [true, false].any (fun a => [true, false].any (fun c => ok a P && ok c Q && !(g a c))) = true ↔ _
    rw [any2]
    constructor
    · rintro ⟨a, ha⟩
      rw [any2] at ha
      obtain ⟨c, hc⟩ := ha
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨⟨ha, hc'⟩, hg⟩ := hc
      obtain ⟨J1, e1⟩ := (oP a).mp ha
      obtain ⟨J2, e2⟩ := (oQ c).mp hc'
      refine ⟨split J1 J2, fun hb => ?_⟩
      unfold bin at hb
      rw [show (fun q => split J1 J2 (false :: q)) = J1 from rfl,
        show (fun q => split J1 J2 (true :: q)) = J2 from rfl, e1, e2, hg] at hb
      exact nomatch hb
    · rintro ⟨J, hJ⟩
      refine ⟨decide (SP (fun q => J (false :: q))), (any2 _).mpr
        ⟨decide (SQ (fun q => J (true :: q))), ?_⟩⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨⟨(oP _).mpr ⟨_, rfl⟩, (oQ _).mpr ⟨_, rfl⟩⟩, ?_⟩
      unfold bin at hJ
      cases hgv : g (decide (SP (fun q => J (false :: q))))
          (decide (SQ (fun q => J (true :: q))))
      · rfl
      · exact absurd hgv hJ

/-- **ZTL's dirty reading, by propositions.** `rd v φ` — "some reading of the occurrences makes φ true / false" — is
exactly "some occurrence-by-occurrence choice of propositions makes φ true / false". -/
theorem rd_iff (v : Nat → V) : ∀ φ : Fm,
    ((rd v φ).1 = true ↔ ∃ J : List Bool → Prop, semO v J φ) ∧ ((rd v φ).2 = true ↔ ∃ J : List Bool → Prop, ¬ semO v J φ) := by
  intro φ
  induction φ with
  | atom n =>
      show ((subs (v n)).contains true = true ↔ ∃ J : List Bool → Prop, atomP v (J []) n) ∧
        ((subs (v n)).contains false = true ↔ ∃ J : List Bool → Prop, ¬ atomP v (J []) n)
      unfold atomP
      cases v n
      · exact ⟨⟨fun _ => ⟨fun _ => True, trivial⟩, fun _ => rfl⟩, ⟨(fun h => nomatch h), fun h => h.elim fun _ h => absurd trivial h⟩⟩
      · exact ⟨⟨(fun h => nomatch h), fun h => h.elim fun _ h => h.elim⟩, ⟨fun _ => ⟨fun _ => True, id⟩, fun _ => rfl⟩⟩
      · exact ⟨⟨fun _ => ⟨fun _ => True, trivial⟩, fun _ => rfl⟩, ⟨fun _ => ⟨fun _ => False, id⟩, fun _ => rfl⟩⟩
  | top => exact ⟨⟨fun _ => ⟨fun _ => True, trivial⟩, fun _ => rfl⟩, ⟨(fun h => nomatch h), fun h => h.elim fun _ h => absurd trivial h⟩⟩
  | bot => exact ⟨⟨(fun h => nomatch h), fun h => h.elim fun _ h => h.elim⟩, ⟨fun _ => ⟨fun _ => True, id⟩, fun _ => rfl⟩⟩
  | neg φ ih =>
      show ((rd v φ).2 = true ↔ ∃ J : List Bool → Prop, ¬ semO v J φ) ∧ ((rd v φ).1 = true ↔ ∃ J : List Bool → Prop, ¬ ¬ semO v J φ)
      refine ⟨ih.2, ?_⟩
      rw [ih.1]
      exact ⟨fun ⟨J, h⟩ => ⟨J, fun n => n h⟩, fun ⟨J, h⟩ => ⟨J, Classical.byContradiction h⟩⟩
  | conj φ ψ ihφ ihψ => exact bin_case _ _ _ (fun J => semO v J φ) (fun J => semO v J ψ) ihφ.1 ihφ.2 ihψ.1 ihψ.2
  | disj φ ψ ihφ ihψ => exact bin_case _ _ _ (fun J => semO v J φ) (fun J => semO v J ψ) ihφ.1 ihφ.2 ihψ.1 ihψ.2
  | imp φ ψ ihφ ihψ => exact bin_case _ _ _ (fun J => semO v J φ) (fun J => semO v J ψ) ihφ.1 ihφ.2 ihψ.1 ihψ.2
  | xor φ ψ ihφ ihψ => exact bin_case _ _ _ (fun J => semO v J φ) (fun J => semO v J ψ) ihφ.1 ihφ.2 ihψ.1 ihψ.2
  | xnor φ ψ ihφ ihψ => exact bin_case _ _ _ (fun J => semO v J φ) (fun J => semO v J ψ) ihφ.1 ihφ.2 ihψ.1 ihψ.2

/-- **EARNED side.** Strong Kleene T (the judge's EARNED) is "true under every occurrence reading"; strong Kleene F
(REFUTED) is "false under every occurrence reading". -/
theorem kev_T_iff (v : Nat → V) (φ : Fm) : kev v φ = T ↔ ∀ J, semO v J φ := by
  have h := rd_is_kleene v φ
  have r := (rd_iff v φ).2
  constructor
  · intro hk J
    rw [hk] at h
    exact Classical.byContradiction fun hn => by
      have := r.mpr ⟨J, hn⟩; rw [h] at this; exact nomatch this
  · intro hall
    have h2 : (rd v φ).2 = false := by
      cases hr : (rd v φ).2
      · rfl
      · obtain ⟨J, hJ⟩ := r.mp hr; exact absurd (hall J) hJ
    rw [h] at h2
    cases hk : kev v φ <;> rw [hk] at h2 <;> first | rfl | exact nomatch h2

theorem kev_F_iff (v : Nat → V) (φ : Fm) : kev v φ = F ↔ ∀ J, ¬ semO v J φ := by
  have h := rd_is_kleene v φ
  have r := (rd_iff v φ).1
  constructor
  · intro hk J hs
    rw [hk] at h
    have := r.mpr ⟨J, hs⟩; rw [h] at this; exact nomatch this
  · intro hall
    have h1 : (rd v φ).1 = false := by
      cases hr : (rd v φ).1
      · rfl
      · obtain ⟨J, hJ⟩ := r.mp hr; exact absurd hJ (hall J)
    rw [h] at h1
    cases hk : kev v φ <;> rw [hk] at h1 <;> first | rfl | exact nomatch h1

/-! ## The six dispositions, in classical terms -/

/-- **The bridge.** Each of the judge's six dispositions of φ under v, stated with classical propositions. -/
theorem dispositions (v : Nat → V) (φ : Fm) :
    (StrictEarned v φ ↔ ∀ J, semO v J φ) ∧
    (kev v φ = F ↔ ∀ J, ¬ semO v J φ) ∧
    (EarnedIfStable v φ ↔ ¬ (∀ J, semO v J φ) ∧ ∀ I, semU v I φ) ∧
    (RefutedIfStable v φ ↔ ¬ (∀ J, ¬ semO v J φ) ∧ ∀ I, ¬ semU v I φ) ∧
    (OnCredit v φ ↔ evalF v φ = T ∧ ¬ (∀ J, semO v J φ) ∧ (∃ I, ¬ semU v I φ) ∧ ∃ I, semU v I φ) ∧
    (Open v φ ↔ evalF v φ ≠ T ∧ ¬ (∀ J, ¬ semO v J φ) ∧ (∃ I, ¬ semU v I φ) ∧ ∃ I, semU v I φ) := by
  have hT := kev_T_iff v φ
  have hF := kev_F_iff v φ
  have hE := enum_iff v φ
  have hS := stableF_iff v φ
  have nE : ¬ Enum v φ ↔ ∃ I, ¬ semU v I φ := by
    rw [hE]; exact ⟨fun h => Classical.byContradiction fun hn => h fun I =>
      Classical.byContradiction fun hI => hn ⟨I, hI⟩, fun ⟨I, hI⟩ h => hI (h I)⟩
  have nS : ¬ StableF v φ ↔ ∃ I, semU v I φ := by
    rw [hS]; exact ⟨fun h => Classical.byContradiction fun hn => h fun I hI => hn ⟨I, hI⟩,
      fun ⟨I, hI⟩ h => h I hI⟩
  refine ⟨(strict_earned_iff_kleene v φ).trans hT, hF, ?_, ?_, ?_, ?_⟩
  · unfold EarnedIfStable; rw [ne_eq, hT, hE]
  · unfold RefutedIfStable; rw [ne_eq, hF, hS]
  · unfold OnCredit; rw [ne_eq, hT, nE, nS]
  · unfold Open; rw [ne_eq (kev v φ), hF, nE, nS]

/-! ## Where the bridge ends: ON CREDIT vs OPEN is not a property of the readings

ZTL's greedy register `evalF` is strong Kleene with the assertion ↑ (Z ↦ F) at EVERY connective (ZTL `*_is_up_kleene`):
an intermediate result not yet proved counts as false. That is a property of the formula's SHAPE, not of its classical
content. `credit_not_semantic`: p and ¬¬p, with p dirty, have the same truth under every uniform reading and under every
occurrence reading — classically one statement — yet ZTL calls p OPEN and ¬¬p ON CREDIT. So no translation through
readings can separate ON CREDIT from OPEN; the bridge stops there by a theorem, not by an omission. -/

theorem not_enum_atom : ¬ Enum (fun _ => Z) (.atom 0) := fun h => by
  have := h (fun _ => F) (fun _ hz => absurd rfl hz) (fun _ e => nomatch e)
  exact nomatch this

theorem not_stableF_atom : ¬ StableF (fun _ => Z) (.atom 0) := fun h => by
  have := h (fun _ => T) (fun _ hz => absurd rfl hz) (fun _ e => nomatch e)
  exact nomatch this

theorem credit_not_semantic :
    (∀ J, semO (fun _ => Z) J (.atom 0) ↔ semO (fun _ => Z) J (.neg (.neg (.atom 0)))) ∧
    (∀ I, semU (fun _ => Z) I (.atom 0) ↔ semU (fun _ => Z) I (.neg (.neg (.atom 0)))) ∧
    Open (fun _ => Z) (.atom 0) ∧ OnCredit (fun _ => Z) (.neg (.neg (.atom 0))) := by
  have nE2 : ¬ Enum (fun _ => Z) (.neg (.neg (.atom 0))) := fun h => by
    have := h (fun _ => F) (fun _ hz => absurd rfl hz) (fun _ e => nomatch e)
    exact nomatch this
  have nS2 : ¬ StableF (fun _ => Z) (.neg (.neg (.atom 0))) := fun h => by
    have := h (fun _ => T) (fun _ hz => absurd rfl hz) (fun _ e => nomatch e)
    exact nomatch this
  refine ⟨fun J => ⟨fun h n => n h, fun h => Classical.byContradiction h⟩,
    fun I => ⟨fun h n => n h, fun h => Classical.byContradiction h⟩,
    ⟨(fun e => nomatch e), (fun e => nomatch e), not_enum_atom, not_stableF_atom⟩,
    ⟨rfl, (fun e => nomatch e), nE2, nS2⟩⟩

end ZClassical.Bridge

#print axioms ZClassical.Bridge.enum_iff
#print axioms ZClassical.Bridge.stableF_iff
#print axioms ZClassical.Bridge.rd_iff
#print axioms ZClassical.Bridge.kev_T_iff
#print axioms ZClassical.Bridge.kev_F_iff
#print axioms ZClassical.Bridge.dispositions
#print axioms ZClassical.Bridge.credit_not_semantic
