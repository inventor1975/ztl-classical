/-
  KS23.QE — expressions with dyadic constants (`half`), reduced to integer expressions `PE` by clearing the
  powers of two: `(e.clr).1 = 2^(e.clr).2 · e` as functions, so `e ≡ 0` is decided by the Kronecker test on `clr`.
-/
import KS23.Chain

namespace KS23

inductive QE where
  | v0 | v1
  | c (z : Int)
  | half (a : QE)
  | hp (H : List (List Int)) (a b : QE)
  | add (a b : QE) | sub (a b : QE) | mul (a b : QE)

noncomputable def QE.evalR : QE → ℝ → ℝ → ℝ
  | .v0, x, _ => x
  | .v1, _, y => y
  | .c z, _, _ => z
  | .half a, x, y => a.evalR x y / 2
  | .hp H a b, x, y => horn2R H (a.evalR x y) (b.evalR x y)
  | .add a b, x, y => a.evalR x y + b.evalR x y
  | .sub a b, x, y => a.evalR x y - b.evalR x y
  | .mul a b, x, y => a.evalR x y * b.evalR x y

def QE.subst (e A B : QE) : QE :=
  match e with
  | .v0 => A
  | .v1 => B
  | .c z => .c z
  | .half a => .half (a.subst A B)
  | .hp H a b => .hp H (a.subst A B) (b.subst A B)
  | .add a b => .add (a.subst A B) (b.subst A B)
  | .sub a b => .sub (a.subst A B) (b.subst A B)
  | .mul a b => .mul (a.subst A B) (b.subst A B)

theorem QE.evalR_subst (A B e : QE) (r s : ℝ) : (e.subst A B).evalR r s = e.evalR (A.evalR r s) (B.evalR r s) := by
  induction e with
  | v0 => rfl
  | v1 => rfl
  | c z => rfl
  | half a ih => simp only [QE.subst, QE.evalR, ih]
  | hp H a b iha ihb => simp only [QE.subst, QE.evalR, iha, ihb]
  | add a b iha ihb => simp only [QE.subst, QE.evalR, iha, ihb]
  | sub a b iha ihb => simp only [QE.subst, QE.evalR, iha, ihb]
  | mul a b iha ihb => simp only [QE.subst, QE.evalR, iha, ihb]

/-! scaling a Horner row: `c_j ↦ c_j · 2^(k(d-j))` -/
def scaleRow : List Int → Nat → Nat → List Int
  | [], _, _ => []
  | c :: cs, k, d => (c * 2 ^ (k * d)) :: scaleRow cs k (d - 1)

theorem hornR_cons (c : Int) (cs : List Int) (y : ℝ) : hornR (c :: cs) y = c + y * hornR cs y := rfl
theorem horn2R_cons (row : List Int) (H : List (List Int)) (x y : ℝ) :
    horn2R (row :: H) x y = hornR row y + x * horn2R H x y := rfl

theorem hornR_scale (cs : List Int) (k d : Nat) (h : cs.length ≤ d + 1) (y : ℝ) :
    hornR (scaleRow cs k d) ((2:ℝ) ^ k * y) = (2:ℝ) ^ (k * d) * hornR cs y := by
  induction cs generalizing d with
  | nil => simp [scaleRow, hornR]
  | cons c cs ih =>
    simp only [scaleRow, hornR_cons]
    cases d with
    | zero =>
      have : cs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at h; omega)
      subst this; simp [scaleRow, hornR]
    | succ d =>
      rw [show d + 1 - 1 = d by omega, ih d (by simp only [List.length_cons] at h; omega)]
      push_cast; rw [show k * (d + 1) = k * d + k by ring, pow_add]; ring

def scale2 : List (List Int) → Nat → Nat → Nat → Nat → List (List Int)
  | [], _, _, _, _ => []
  | row :: H, ka, kb, dA, dB => ((scaleRow row kb dB).map (· * 2 ^ (ka * dA))) :: scale2 H ka kb (dA - 1) dB

theorem hornR_mulc (cs : List Int) (m : Int) (y : ℝ) : hornR (cs.map (· * m)) y = m * hornR cs y := by
  induction cs with
  | nil => simp [hornR]
  | cons c cs ih => simp only [hornR, List.map_cons, List.foldr_cons] at ih ⊢; rw [ih]; push_cast; ring

theorem horn2R_scale (H : List (List Int)) (ka kb dA dB : Nat) (hA : H.length ≤ dA + 1)
    (hB : ∀ row ∈ H, row.length ≤ dB + 1) (x y : ℝ) :
    horn2R (scale2 H ka kb dA dB) ((2:ℝ) ^ ka * x) ((2:ℝ) ^ kb * y) = (2:ℝ) ^ (ka * dA + kb * dB) * horn2R H x y := by
  induction H generalizing dA with
  | nil => simp [scale2, horn2R]
  | cons row H ih =>
    simp only [scale2, horn2R_cons]
    rw [hornR_mulc, hornR_scale row kb dB (hB row List.mem_cons_self) y]
    cases dA with
    | zero =>
      have : H = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hA; omega)
      subst this; simp [scale2, horn2R]
    | succ dA =>
      rw [show dA + 1 - 1 = dA by omega, ih dA (by simp only [List.length_cons] at hA; omega) (fun r hr => hB r (List.mem_cons_of_mem _ hr))]
      push_cast; rw [show ka * (dA + 1) = ka * dA + ka by ring, pow_add, pow_add, pow_add]; ring

def maxLen (H : List (List Int)) : Nat := H.foldr (fun row acc => Nat.max row.length acc) 0

theorem maxLen_ge (H : List (List Int)) : ∀ row ∈ H, row.length ≤ maxLen H := by
  induction H with
  | nil => intro r h; simp at h
  | cons r H ih =>
    intro row h; simp only [maxLen, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact le_trans (ih row h) (Nat.le_max_right _ _)

def pw (k : Nat) : PE := cE (2 ^ k)

/-- clear the powers of two -/
def QE.clr : QE → PE × Nat
  | .v0 => (.v0, 0)
  | .v1 => (.v1, 0)
  | .c z => (cE z, 0)
  | .half a => let p := a.clr; (p.1, p.2 + 1)
  | .hp H a b =>
    let p := a.clr; let q := b.clr
    let dA := H.length; let dB := maxLen H
    (.hp (scale2 H p.2 q.2 dA dB) p.1 q.1, p.2 * dA + q.2 * dB)
  | .add a b =>
    let p := a.clr; let q := b.clr; let h := max p.2 q.2
    (.add (.mul (pw (h - p.2)) p.1) (.mul (pw (h - q.2)) q.1), h)
  | .sub a b =>
    let p := a.clr; let q := b.clr; let h := max p.2 q.2
    (.sub (.mul (pw (h - p.2)) p.1) (.mul (pw (h - q.2)) q.1), h)
  | .mul a b => let p := a.clr; let q := b.clr; (.mul p.1 q.1, p.2 + q.2)

theorem evalR_pw (k : Nat) (r s : ℝ) : (pw k).evalR r s = (2:ℝ) ^ k := by
  unfold pw; rw [evalR_cE]; push_cast; rfl

theorem QE.clr_eval (e : QE) (r s : ℝ) : e.clr.1.evalR r s = (2:ℝ) ^ e.clr.2 * e.evalR r s := by
  induction e with
  | v0 => simp [QE.clr, PE.evalR, QE.evalR]
  | v1 => simp [QE.clr, PE.evalR, QE.evalR]
  | c z => simp [QE.clr, QE.evalR, evalR_cE]
  | half a ih => simp only [QE.clr, QE.evalR]; rw [ih, pow_succ]; field_simp
  | hp H a b iha ihb =>
    simp only [QE.clr, PE.evalR, QE.evalR]
    rw [iha, ihb]
    exact horn2R_scale H _ _ _ _ (by omega) (fun row h => by have := maxLen_ge H row h; omega) _ _ |>.trans (by ring)
  | add a b iha ihb =>
    simp only [QE.clr, PE.evalR, QE.evalR, evalR_pw]; rw [iha, ihb]
    have e1 : (2:ℝ) ^ (max a.clr.2 b.clr.2 - a.clr.2) * 2 ^ a.clr.2 = 2 ^ (max a.clr.2 b.clr.2) := by
      rw [← pow_add]; congr 1; have := Nat.le_max_left a.clr.2 b.clr.2; omega
    have e2 : (2:ℝ) ^ (max a.clr.2 b.clr.2 - b.clr.2) * 2 ^ b.clr.2 = 2 ^ (max a.clr.2 b.clr.2) := by
      rw [← pow_add]; congr 1; have := Nat.le_max_right a.clr.2 b.clr.2; omega
    rw [← mul_assoc, ← mul_assoc, e1, e2]; ring
  | sub a b iha ihb =>
    simp only [QE.clr, PE.evalR, QE.evalR, evalR_pw]; rw [iha, ihb]
    have e1 : (2:ℝ) ^ (max a.clr.2 b.clr.2 - a.clr.2) * 2 ^ a.clr.2 = 2 ^ (max a.clr.2 b.clr.2) := by
      rw [← pow_add]; congr 1; have := Nat.le_max_left a.clr.2 b.clr.2; omega
    have e2 : (2:ℝ) ^ (max a.clr.2 b.clr.2 - b.clr.2) * 2 ^ b.clr.2 = 2 ^ (max a.clr.2 b.clr.2) := by
      rw [← pow_add]; congr 1; have := Nat.le_max_right a.clr.2 b.clr.2; omega
    rw [← mul_assoc, ← mul_assoc, e1, e2]; ring
  | mul a b iha ihb => simp only [QE.clr, PE.evalR, QE.evalR]; rw [iha, ihb, pow_add]; ring

def QE.check (e : QE) : Bool := e.clr.1.check

theorem QE.check_sound (e : QE) (h : e.check = true) : ∀ x y : ℝ, e.evalR x y = 0 := by
  intro x y
  have h0 := PE.check_sound _ h x y
  rw [QE.clr_eval] at h0
  exact (mul_eq_zero.1 h0).resolve_left (by positivity)

/-- a dyadic constant m / 2^e -/
def halves : Nat → QE → QE
  | 0, a => a
  | k + 1, a => .half (halves k a)
def dyE (d : Dy) : QE := halves d.e (.c d.m)
theorem evalR_halves (k : Nat) (a : QE) (r s : ℝ) : (halves k a).evalR r s = a.evalR r s / 2 ^ k := by
  induction k with
  | zero => simp [halves]
  | succ k ih => simp only [halves, QE.evalR]; rw [ih, pow_succ]; field_simp
theorem evalR_dyE (d : Dy) (r s : ℝ) : (dyE d).evalR r s = d.val := by
  unfold dyE; rw [evalR_halves]; simp [QE.evalR, Dy.val]

end KS23
