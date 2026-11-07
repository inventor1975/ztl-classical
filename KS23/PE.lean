/-
  KS23.PE — polynomial expressions with integer coefficients in two variables, and a kernel-cheap
  identity test by Kronecker substitution: `e ≡ 0` is decided by ONE exact integer evaluation at
  `(B, B^K)`, with `B` above the coefficient mass and `K` above the degree in the first variable.
-/
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import KS23.Dy

namespace KS23
open MvPolynomial

inductive PE where
  | v0 | v1
  | hp (H : List (List Int)) (a b : PE)
  | add (a b : PE) | sub (a b : PE) | mul (a b : PE)

def hornZ (cs : List Int) (y : Int) : Int := cs.foldr (fun c acc => c + y * acc) 0
def horn2Z (H : List (List Int)) (x y : Int) : Int := H.foldr (fun row acc => hornZ row y + x * acc) 0

def PE.evalZ : PE → Int → Int → Int
  | .v0, x, _ => x
  | .v1, _, y => y
  | .hp H a b, x, y => horn2Z H (a.evalZ x y) (b.evalZ x y)
  | .add a b, x, y => a.evalZ x y + b.evalZ x y
  | .sub a b, x, y => a.evalZ x y - b.evalZ x y
  | .mul a b, x, y => a.evalZ x y * b.evalZ x y

noncomputable def PE.evalR : PE → ℝ → ℝ → ℝ
  | .v0, x, _ => x
  | .v1, _, y => y
  | .hp H a b, x, y => horn2R H (a.evalR x y) (b.evalR x y)
  | .add a b, x, y => a.evalR x y + b.evalR x y
  | .sub a b, x, y => a.evalR x y - b.evalR x y
  | .mul a b, x, y => a.evalR x y * b.evalR x y

def absRows (H : List (List Int)) : List (List Int) := H.map (fun row => row.map (fun c => (c.natAbs : Int)))

def PE.abs : PE → PE
  | .v0 => .v0
  | .v1 => .v1
  | .hp H a b => .hp (absRows H) a.abs b.abs
  | .add a b => .add a.abs b.abs
  | .sub a b => .add a.abs b.abs
  | .mul a b => .mul a.abs b.abs

def h2deg (H : List (List Int)) (dA dB : Nat) : Nat :=
  H.foldr (fun row acc => Nat.max (row.length * dB) (dA + acc)) 0

/-- an upper bound for the degree in the first variable -/
def PE.dR : PE → Nat
  | .v0 => 1
  | .v1 => 0
  | .hp H a b => h2deg H a.dR b.dR
  | .add a b => Nat.max a.dR b.dR
  | .sub a b => Nat.max a.dR b.dR
  | .mul a b => a.dR + b.dR

/-- the Kronecker identity test -/
def PE.check (e : PE) : Bool :=
  let B : Int := e.abs.evalZ 1 1 + 2
  e.evalZ B (B ^ (e.dR + 1)) == 0

/-! ## Semantics in `MvPolynomial (Fin 2) ℤ` -/

noncomputable def hornM (cs : List Int) (y : MvPolynomial (Fin 2) ℤ) : MvPolynomial (Fin 2) ℤ :=
  cs.foldr (fun c acc => C c + y * acc) 0
noncomputable def horn2M (H : List (List Int)) (x y : MvPolynomial (Fin 2) ℤ) : MvPolynomial (Fin 2) ℤ :=
  H.foldr (fun row acc => hornM row y + x * acc) 0

noncomputable def PE.toM : PE → MvPolynomial (Fin 2) ℤ
  | .v0 => X 0
  | .v1 => X 1
  | .hp H a b => horn2M H a.toM b.toM
  | .add a b => a.toM + b.toM
  | .sub a b => a.toM - b.toM
  | .mul a b => a.toM * b.toM

section hom
variable {S : Type*} [CommRing S]
def hornG (cs : List Int) (y : S) : S := cs.foldr (fun (c : Int) (acc : S) => (c : S) + y * acc) 0
def horn2G (H : List (List Int)) (x y : S) : S := H.foldr (fun (row : List Int) (acc : S) => hornG row y + x * acc) 0

theorem map_hornM (f : MvPolynomial (Fin 2) ℤ →+* S) (cs : List Int) (y) :
    f (hornM cs y) = hornG cs (f y) := by
  induction cs with
  | nil => simp [hornM, hornG]
  | cons c cs ih =>
    simp only [hornM, hornG, List.foldr_cons] at ih ⊢
    rw [map_add, map_mul, ih, eq_intCast C c, map_intCast]

theorem map_horn2M (f : MvPolynomial (Fin 2) ℤ →+* S) (H : List (List Int)) (x y) :
    f (horn2M H x y) = horn2G H (f x) (f y) := by
  induction H with
  | nil => simp [horn2M, horn2G]
  | cons row H ih =>
    simp only [horn2M, horn2G, List.foldr_cons] at ih ⊢
    rw [map_add, map_mul, ih, map_hornM]
end hom

theorem hornZ_eq (cs : List Int) (y : Int) : hornZ cs y = hornG cs y := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [hornZ, hornG, List.foldr_cons] at ih ⊢; rw [ih, Int.cast_id]
theorem horn2Z_eq (H : List (List Int)) (x y : Int) : horn2Z H x y = horn2G H x y := by
  induction H with
  | nil => rfl
  | cons row H ih => simp only [horn2Z, horn2G, List.foldr_cons] at ih ⊢; rw [ih, hornZ_eq]
theorem hornR_eq (cs : List Int) (y : ℝ) : hornR cs y = hornG cs y := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [hornR, hornG, List.foldr_cons] at ih ⊢
theorem horn2R_eq (H : List (List Int)) (x y : ℝ) : horn2R H x y = horn2G H x y := by
  induction H with
  | nil => rfl
  | cons row H ih => simp only [horn2R, horn2G, List.foldr_cons] at ih ⊢; rw [ih, hornR_eq]

theorem PE.evalZ_eq (e : PE) (x y : Int) : e.evalZ x y = eval ![x, y] e.toM := by
  induction e with
  | v0 => simp [PE.evalZ, PE.toM]
  | v1 => simp [PE.evalZ, PE.toM]
  | hp H a b iha ihb => simp only [PE.evalZ, PE.toM]; rw [horn2Z_eq, iha, ihb, ← map_horn2M (eval ![x, y])]
  | add a b iha ihb => simp [PE.evalZ, PE.toM, iha, ihb]
  | sub a b iha ihb => simp [PE.evalZ, PE.toM, iha, ihb]
  | mul a b iha ihb => simp [PE.evalZ, PE.toM, iha, ihb]

theorem PE.evalR_eq (e : PE) (x y : ℝ) : e.evalR x y = eval₂Hom (Int.castRingHom ℝ) ![x, y] e.toM := by
  induction e with
  | v0 => simp [PE.evalR, PE.toM]
  | v1 => simp [PE.evalR, PE.toM]
  | hp H a b iha ihb =>
    simp only [PE.evalR, PE.toM]; rw [horn2R_eq, iha, ihb, ← map_horn2M (eval₂Hom (Int.castRingHom ℝ) ![x, y])]
  | add a b iha ihb => simp [PE.evalR, PE.toM, iha, ihb]
  | sub a b iha ihb => simp [PE.evalR, PE.toM, iha, ihb]
  | mul a b iha ihb => simp [PE.evalR, PE.toM, iha, ihb]

/-! ## Coefficient domination -/

def Dom (p P : MvPolynomial (Fin 2) ℤ) : Prop := ∀ m, |coeff m p| ≤ coeff m P

theorem Dom.nonneg {p P : MvPolynomial (Fin 2) ℤ} (h : Dom p P) (m) : 0 ≤ coeff m P :=
  le_trans (abs_nonneg _) (h m)

theorem Dom.add {p P q Q : MvPolynomial (Fin 2) ℤ} (h1 : Dom p P) (h2 : Dom q Q) : Dom (p + q) (P + Q) := by
  intro m; rw [coeff_add, coeff_add]; exact le_trans (abs_add_le _ _) (add_le_add (h1 m) (h2 m))

theorem Dom.sub {p P q Q : MvPolynomial (Fin 2) ℤ} (h1 : Dom p P) (h2 : Dom q Q) : Dom (p - q) (P + Q) := by
  intro m; rw [coeff_sub, coeff_add]; exact le_trans (abs_sub _ _) (add_le_add (h1 m) (h2 m))

theorem Dom.mul {p P q Q : MvPolynomial (Fin 2) ℤ} (h1 : Dom p P) (h2 : Dom q Q) : Dom (p * q) (P * Q) := by
  intro m; classical
  rw [coeff_mul, coeff_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]; exact mul_le_mul (h1 _) (h2 _) (abs_nonneg _) (h1.nonneg _)

theorem Dom.C (c : Int) : Dom (C c) (C (c.natAbs : Int)) := by
  intro m; classical
  rw [coeff_C, coeff_C]; split <;> simp

theorem Dom.X (i : Fin 2) : Dom (X i) (X i) := by
  intro m; classical
  rw [coeff_X']; split <;> simp

theorem Dom.zero : Dom (0 : MvPolynomial (Fin 2) ℤ) 0 := by intro m; simp

theorem Dom.hornM {y Y : MvPolynomial (Fin 2) ℤ} (h : Dom y Y) (cs : List Int) :
    Dom (hornM cs y) (hornM (cs.map (fun c => (c.natAbs : Int))) Y) := by
  induction cs with
  | nil => simpa [hornM] using Dom.zero
  | cons c cs ih =>
    simp only [KS23.hornM, List.map_cons, List.foldr_cons] at ih ⊢
    exact (Dom.C c).add (h.mul ih)

theorem Dom.horn2M {x X' y Y : MvPolynomial (Fin 2) ℤ} (hx : Dom x X') (hy : Dom y Y) (H : List (List Int)) :
    Dom (horn2M H x y) (horn2M (absRows H) X' Y) := by
  induction H with
  | nil => simpa [horn2M, absRows] using Dom.zero
  | cons row H ih =>
    simp only [KS23.horn2M, absRows, List.map_cons, List.foldr_cons] at ih ⊢
    exact (hy.hornM row).add (hx.mul ih)

theorem PE.dom (e : PE) : Dom e.toM e.abs.toM := by
  induction e with
  | v0 => exact Dom.X 0
  | v1 => exact Dom.X 1
  | hp H a b iha ihb => exact Dom.horn2M iha ihb H
  | add a b iha ihb => exact iha.add ihb
  | sub a b iha ihb => exact iha.sub ihb
  | mul a b iha ihb => exact iha.mul ihb

/-! ## Degree bound -/

theorem deg_hornM (cs : List Int) (y : MvPolynomial (Fin 2) ℤ) (d : Nat) (hy : degreeOf 0 y ≤ d) :
    degreeOf 0 (hornM cs y) ≤ cs.length * d := by
  induction cs with
  | nil => simp [hornM, degreeOf_zero]
  | cons c cs ih =>
    simp only [KS23.hornM, List.foldr_cons, List.length_cons] at ih ⊢
    refine le_trans (degreeOf_add_le _ _ _) (max_le ?_ ?_)
    · rw [degreeOf_C]; exact Nat.zero_le _
    · exact le_trans (degreeOf_mul_le _ _ _) (by nlinarith)

theorem deg_horn2M (H : List (List Int)) (x y : MvPolynomial (Fin 2) ℤ) (dx dy : Nat)
    (hx : degreeOf 0 x ≤ dx) (hy : degreeOf 0 y ≤ dy) : degreeOf 0 (horn2M H x y) ≤ h2deg H dx dy := by
  induction H with
  | nil => simp [horn2M, degreeOf_zero]
  | cons row H ih =>
    simp only [KS23.horn2M, h2deg, List.foldr_cons] at ih ⊢
    refine le_trans (degreeOf_add_le _ _ _) (max_le_max (deg_hornM row y dy hy) ?_)
    exact le_trans (degreeOf_mul_le _ _ _) (by omega)

theorem PE.deg (e : PE) : degreeOf 0 e.toM ≤ e.dR := by
  induction e with
  | v0 => simp [PE.toM, PE.dR, degreeOf_X]
  | v1 => simp [PE.toM, PE.dR, degreeOf_X]
  | hp H a b iha ihb => exact deg_horn2M H _ _ _ _ iha ihb
  | add a b iha ihb => exact le_trans (degreeOf_add_le _ _ _) (max_le_max iha ihb)
  | sub a b iha ihb => exact le_trans (degreeOf_sub_le _ _ _) (max_le_max iha ihb)
  | mul a b iha ihb => exact le_trans (degreeOf_mul_le _ _ _) (Nat.add_le_add iha ihb)

/-! ## Kronecker -/

theorem eval_kron (p : MvPolynomial (Fin 2) ℤ) (B : ℤ) (K : ℕ) :
    eval ![B, B ^ K] p = ∑ d ∈ p.support, coeff d p * B ^ (d 0 + K * d 1) := by
  rw [eval_eq']; refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fin.prod_univ_two]; simp [pow_add, pow_mul]

theorem sum_abs_le_eval_one {p P : MvPolynomial (Fin 2) ℤ} (h : Dom p P) :
    ∑ d ∈ p.support, |coeff d p| ≤ eval (fun _ => 1) P := by
  rw [eval_eq']; simp only [one_pow, Finset.prod_const_one, mul_one]
  have hsub : p.support ⊆ P.support := by
    intro d hd; rw [mem_support_iff] at hd ⊢
    have := h d; have := abs_pos.2 hd; omega
  calc ∑ d ∈ p.support, |coeff d p| ≤ ∑ d ∈ p.support, coeff d P := Finset.sum_le_sum fun d _ => h d
    _ ≤ ∑ d ∈ P.support, coeff d P := Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => h.nonneg d

theorem kron_zero (p : MvPolynomial (Fin 2) ℤ) (B : ℤ) (K : ℕ) (hB : 2 ≤ B)
    (hdeg : ∀ m ∈ p.support, m 0 < K) (hL : ∑ d ∈ p.support, |coeff d p| < B)
    (h0 : eval ![B, B ^ K] p = 0) : p = 0 := by
  classical
  by_contra hp
  have hne : p.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; exact hp (support_eq_empty.1 h)
  set φ : (Fin 2 →₀ ℕ) → ℕ := fun d => d 0 + K * d 1
  obtain ⟨ms, hms, hmax⟩ := p.support.exists_max_image φ hne
  have hinj : ∀ d ∈ p.support, φ d = φ ms → d = ms := by
    intro d hd hφ
    have h1 := hdeg d hd; have h2 := hdeg ms hms
    have hK : 0 < K := by omega
    have e0 : d 0 = ms 0 := by
      have := congrArg (· % K) hφ; simp only [φ] at this
      rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
    have e1 : d 1 = ms 1 := by
      simp only [φ] at hφ; rw [e0] at hφ
      exact Nat.eq_of_mul_eq_mul_left hK (by omega)
    ext i; fin_cases i <;> simp [e0, e1]
  have hlt : ∀ d ∈ p.support.erase ms, φ d + 1 ≤ φ ms := by
    intro d hd
    have hd' := Finset.mem_of_mem_erase hd
    have := hmax d hd'
    rcases Nat.lt_or_ge (φ d) (φ ms) with h | h
    · omega
    · exact absurd (hinj d hd' (le_antisymm this h)) (Finset.ne_of_mem_erase hd)
  rw [eval_kron, ← Finset.add_sum_erase _ _ hms] at h0
  set cs := coeff ms p
  have hcs : cs ≠ 0 := mem_support_iff.1 hms
  have hB0 : (0:ℤ) < B := by omega
  have hP : (0:ℤ) < B ^ φ ms := pow_pos hB0 _
  have key : |cs * B ^ φ ms| = |∑ d ∈ p.support.erase ms, coeff d p * B ^ (d 0 + K * d 1)| := by
    rw [show cs * B ^ φ ms = - ∑ d ∈ p.support.erase ms, coeff d p * B ^ (d 0 + K * d 1) by simp only [φ, cs]; linarith, abs_neg]
  have hbound : B * |∑ d ∈ p.support.erase ms, coeff d p * B ^ (d 0 + K * d 1)| ≤
      (∑ d ∈ p.support, |coeff d p|) * B ^ φ ms := by
    calc B * |∑ d ∈ p.support.erase ms, coeff d p * B ^ (d 0 + K * d 1)|
        ≤ B * ∑ d ∈ p.support.erase ms, |coeff d p * B ^ (d 0 + K * d 1)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hB0.le
      _ = ∑ d ∈ p.support.erase ms, |coeff d p| * (B * B ^ (d 0 + K * d 1)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => ?_
          rw [abs_mul, abs_of_pos (pow_pos hB0 _)]; ring
      _ ≤ ∑ d ∈ p.support.erase ms, |coeff d p| * B ^ φ ms := by
          refine Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [← pow_succ']; exact pow_le_pow_right₀ (by omega) (hlt d hd)
      _ ≤ ∑ d ∈ p.support, |coeff d p| * B ^ φ ms :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset ms p.support)
            (fun d _ _ => mul_nonneg (abs_nonneg _) hP.le)
      _ = (∑ d ∈ p.support, |coeff d p|) * B ^ φ ms := by rw [Finset.sum_mul]
  have h1 : 1 ≤ |cs| := Int.one_le_abs hcs
  rw [← key, abs_mul, abs_of_pos hP] at hbound
  have e1 : B * B ^ φ ms ≤ B * (|cs| * B ^ φ ms) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hP.le h1) hB0.le
  have e2 : (∑ d ∈ p.support, |coeff d p|) * B ^ φ ms < B * B ^ φ ms := mul_lt_mul_of_pos_right hL hP
  linarith

theorem PE.check_sound (e : PE) (h : e.check = true) : ∀ x y : ℝ, e.evalR x y = 0 := by
  intro x y
  unfold PE.check at h
  simp only [beq_iff_eq] at h
  set B : Int := e.abs.evalZ 1 1 + 2
  have hL := sum_abs_le_eval_one e.dom
  have h11 : (![1, 1] : Fin 2 → ℤ) = fun _ => 1 := by funext i; fin_cases i <;> rfl
  have hev : e.abs.evalZ 1 1 = eval (fun _ => 1) e.abs.toM := by rw [PE.evalZ_eq, h11]
  have hz : e.toM = 0 := by
    apply kron_zero e.toM B (e.dR + 1)
    · have : 0 ≤ e.abs.evalZ 1 1 := by rw [hev]; exact le_trans (Finset.sum_nonneg fun d _ => abs_nonneg _) hL
      omega
    · intro m hm; have := monomial_le_degreeOf 0 hm; have := e.deg; omega
    · rw [← hev] at hL; omega
    · rw [← PE.evalZ_eq]; exact h
  rw [PE.evalR_eq, hz, map_zero]

end KS23
