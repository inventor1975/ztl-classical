/-
  KS23.Dy — exact dyadic numbers m / 2^e and outward-rounded intervals, computable in the kernel.
-/
import Mathlib.Tactic

namespace KS23

/-- `m / 2^e`. -/
structure Dy where
  m : Int
  e : Nat
deriving Repr, DecidableEq

namespace Dy
def ofInt (c : Int) : Dy := ⟨c, 0⟩
def neg (a : Dy) : Dy := ⟨-a.m, a.e⟩
def mul (a b : Dy) : Dy := ⟨a.m * b.m, a.e + b.e⟩
/-- exact sum, aligned to the larger exponent -/
def add (a b : Dy) : Dy :=
  if a.e ≤ b.e then ⟨a.m * 2 ^ (b.e - a.e) + b.m, b.e⟩ else ⟨a.m + b.m * 2 ^ (a.e - b.e), a.e⟩
/-- `a ≤ b` decided exactly -/
def le (a b : Dy) : Bool := a.m * 2 ^ b.e ≤ b.m * 2 ^ a.e
def min (a b : Dy) : Dy := if le a b then a else b
def max (a b : Dy) : Dy := if le a b then b else a
/-- the mantissa precision kept after rounding -/
def P : Nat := 62
/-- how many bits to drop -/
def drop (a : Dy) : Nat := Nat.min a.e (a.m.natAbs.log2 - P)
/-- round down (floor) -/
def rdn (a : Dy) : Dy := let k := drop a; ⟨a.m / (2 ^ k : Nat), a.e - k⟩
/-- round up (ceil) -/
def rup (a : Dy) : Dy := let k := drop a; ⟨-((-a.m) / (2 ^ k : Nat)), a.e - k⟩
def half (a : Dy) : Dy := ⟨a.m, a.e + 1⟩
end Dy

structure Iv where
  lo : Dy
  hi : Dy
deriving Repr, DecidableEq

namespace Iv
def const (c : Int) : Iv := ⟨Dy.ofInt c, Dy.ofInt c⟩
def add (a b : Iv) : Iv := ⟨Dy.rdn (Dy.add a.lo b.lo), Dy.rup (Dy.add a.hi b.hi)⟩
def sub (a b : Iv) : Iv := ⟨Dy.rdn (Dy.add a.lo b.hi.neg), Dy.rup (Dy.add a.hi b.lo.neg)⟩
def mul (a b : Iv) : Iv :=
  let p1 := Dy.mul a.lo b.lo; let p2 := Dy.mul a.lo b.hi
  let p3 := Dy.mul a.hi b.lo; let p4 := Dy.mul a.hi b.hi
  ⟨Dy.rdn (Dy.min (Dy.min p1 p2) (Dy.min p3 p4)), Dy.rup (Dy.max (Dy.max p1 p2) (Dy.max p3 p4))⟩
/-- certainly not containing 0 -/
def excl0 (a : Iv) : Bool := decide (0 < a.lo.m) || decide (a.hi.m < 0)
end Iv

/-- Horner rows: `[c0, c1, ...]` means `c0 + y*(c1 + y*(...))`. -/
def hornI (cs : List Int) (y : Iv) : Iv := cs.foldr (fun c acc => Iv.add (Iv.const c) (Iv.mul y acc)) (Iv.const 0)
/-- bivariate: rows indexed by the power of x -/
def horn2I (H : List (List Int)) (x y : Iv) : Iv := H.foldr (fun row acc => Iv.add (hornI row y) (Iv.mul x acc)) (Iv.const 0)

end KS23

/-! ## Soundness over ℝ -/
namespace KS23

noncomputable def Dy.val (a : Dy) : ℝ := (a.m : ℝ) / 2 ^ a.e

theorem two_pow_pos (e : Nat) : (0 : ℝ) < 2 ^ e := by positivity

theorem Dy.val_mul (a b : Dy) : (Dy.mul a b).val = a.val * b.val := by
  simp only [Dy.val, Dy.mul, pow_add]; push_cast; field_simp

theorem Dy.val_neg (a : Dy) : (Dy.neg a).val = - a.val := by
  simp only [Dy.val, Dy.neg]; push_cast; ring

theorem Dy.val_add (a b : Dy) : (Dy.add a b).val = a.val + b.val := by
  unfold Dy.add Dy.val
  split
  · next h =>
    have : (2:ℝ) ^ b.e = 2 ^ a.e * 2 ^ (b.e - a.e) := by rw [← pow_add]; congr 1; omega
    simp only []; push_cast; rw [this]; field_simp
  · next h =>
    have : (2:ℝ) ^ a.e = 2 ^ b.e * 2 ^ (a.e - b.e) := by rw [← pow_add]; congr 1; omega
    simp only []; push_cast; rw [this]; field_simp

theorem Dy.le_iff (a b : Dy) : Dy.le a b = true ↔ a.val ≤ b.val := by
  unfold Dy.le Dy.val
  rw [decide_eq_true_iff, div_le_div_iff₀ (two_pow_pos _) (two_pow_pos _)]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem Dy.val_min (a b : Dy) : (Dy.min a b).val = Min.min a.val b.val := by
  unfold Dy.min; split
  · next h => rw [min_eq_left ((Dy.le_iff a b).1 h)]
  · next h =>
    have : ¬ a.val ≤ b.val := fun h' => h ((Dy.le_iff a b).2 h')
    rw [min_eq_right (le_of_lt (not_le.1 this))]

theorem Dy.val_max (a b : Dy) : (Dy.max a b).val = Max.max a.val b.val := by
  unfold Dy.max; split
  · next h => rw [max_eq_right ((Dy.le_iff a b).1 h)]
  · next h =>
    have : ¬ a.val ≤ b.val := fun h' => h ((Dy.le_iff a b).2 h')
    rw [max_eq_left (le_of_lt (not_le.1 this))]

theorem Dy.drop_le (a : Dy) : Dy.drop a ≤ a.e := Nat.min_le_left _ _

/-- the core of rounding: `(m / 2^k) / 2^(e-k) ≤ m / 2^e` -/
theorem round_down_le (m : Int) (e k : Nat) (hk : k ≤ e) :
    ((m / ((2 ^ k : Nat) : Int) : Int) : ℝ) / 2 ^ (e - k) ≤ (m : ℝ) / 2 ^ e := by
  have hpos : (0 : Int) < ((2 ^ k : Nat) : Int) := by positivity
  have h1 : m / ((2 ^ k : Nat) : Int) * ((2 ^ k : Nat) : Int) ≤ m := Int.ediv_mul_le m (ne_of_gt hpos)
  have h2 : ((m / ((2 ^ k : Nat) : Int) : Int) : ℝ) * 2 ^ k ≤ (m : ℝ) := by exact_mod_cast h1
  have he : (2:ℝ) ^ e = 2 ^ (e - k) * 2 ^ k := by rw [← pow_add]; congr 1; omega
  rw [he, div_le_div_iff₀ (two_pow_pos _) (by positivity)]
  nlinarith [two_pow_pos (e - k)]

theorem Dy.rdn_le (a : Dy) : (Dy.rdn a).val ≤ a.val := by
  unfold Dy.rdn Dy.val; exact round_down_le a.m a.e _ (Dy.drop_le a)

theorem Dy.le_rup (a : Dy) : a.val ≤ (Dy.rup a).val := by
  unfold Dy.rup Dy.val
  have := round_down_le (-a.m) a.e (Dy.drop a) (Dy.drop_le a)
  push_cast at this ⊢
  rw [neg_div] at this ⊢
  linarith

/-! intervals -/
def Iv.mem (x : ℝ) (I : Iv) : Prop := I.lo.val ≤ x ∧ x ≤ I.hi.val

theorem Iv.mem_const (c : Int) : Iv.mem (c : ℝ) (Iv.const c) := by
  simp [Iv.mem, Iv.const, Dy.ofInt, Dy.val]

theorem Iv.mem_add {x y : ℝ} {I J : Iv} (hx : Iv.mem x I) (hy : Iv.mem y J) : Iv.mem (x + y) (Iv.add I J) := by
  unfold Iv.mem Iv.add at *
  refine ⟨le_trans (Dy.rdn_le _) ?_, le_trans ?_ (Dy.le_rup _)⟩ <;> rw [Dy.val_add] <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem Iv.mem_sub {x y : ℝ} {I J : Iv} (hx : Iv.mem x I) (hy : Iv.mem y J) : Iv.mem (x - y) (Iv.sub I J) := by
  unfold Iv.mem Iv.sub at *
  refine ⟨le_trans (Dy.rdn_le _) ?_, le_trans ?_ (Dy.le_rup _)⟩ <;> rw [Dy.val_add, Dy.val_neg] <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mul_ge_min {a b x y : ℝ} (hx : a ≤ x ∧ x ≤ b) : Min.min (a*y) (b*y) ≤ x*y := by
  rcases le_total 0 y with hy | hy
  · exact le_trans (min_le_left _ _) (by nlinarith)
  · exact le_trans (min_le_right _ _) (by nlinarith)

theorem mul_le_max {a b x y : ℝ} (hx : a ≤ x ∧ x ≤ b) : x*y ≤ Max.max (a*y) (b*y) := by
  rcases le_total 0 y with hy | hy
  · exact le_trans (by nlinarith) (le_max_right _ _)
  · exact le_trans (by nlinarith) (le_max_left _ _)

theorem Iv.mem_mul {x y : ℝ} {I J : Iv} (hx : Iv.mem x I) (hy : Iv.mem y J) : Iv.mem (x * y) (Iv.mul I J) := by
  unfold Iv.mem Iv.mul at *
  simp only []
  refine ⟨le_trans (Dy.rdn_le _) ?_, le_trans ?_ (Dy.le_rup _)⟩
  · rw [Dy.val_min, Dy.val_min, Dy.val_min, Dy.val_mul, Dy.val_mul, Dy.val_mul, Dy.val_mul]
    have h1 := mul_ge_min (y := y) hx
    have h2 : Min.min (I.lo.val*J.lo.val) (I.lo.val*J.hi.val) ≤ I.lo.val*y := by
      have := mul_ge_min (y := I.lo.val) hy; rw [mul_comm J.lo.val, mul_comm J.hi.val, mul_comm y] at this; exact this
    have h3 : Min.min (I.hi.val*J.lo.val) (I.hi.val*J.hi.val) ≤ I.hi.val*y := by
      have := mul_ge_min (y := I.hi.val) hy; rw [mul_comm J.lo.val, mul_comm J.hi.val, mul_comm y] at this; exact this
    rcases min_choice (I.lo.val*y) (I.hi.val*y) with h | h <;> rw [h] at h1
    · exact le_trans (min_le_left _ _) (le_trans h2 h1)
    · exact le_trans (min_le_right _ _) (le_trans h3 h1)
  · rw [Dy.val_max, Dy.val_max, Dy.val_max, Dy.val_mul, Dy.val_mul, Dy.val_mul, Dy.val_mul]
    have h1 := mul_le_max (y := y) hx
    have h2 : I.lo.val*y ≤ Max.max (I.lo.val*J.lo.val) (I.lo.val*J.hi.val) := by
      have := mul_le_max (y := I.lo.val) hy; rw [mul_comm J.lo.val, mul_comm J.hi.val, mul_comm y] at this; exact this
    have h3 : I.hi.val*y ≤ Max.max (I.hi.val*J.lo.val) (I.hi.val*J.hi.val) := by
      have := mul_le_max (y := I.hi.val) hy; rw [mul_comm J.lo.val, mul_comm J.hi.val, mul_comm y] at this; exact this
    rcases max_choice (I.lo.val*y) (I.hi.val*y) with h | h <;> rw [h] at h1
    · exact le_trans h1 (le_trans h2 (le_max_left _ _))
    · exact le_trans h1 (le_trans h3 (le_max_right _ _))

theorem Iv.excl0_ne {x : ℝ} {I : Iv} (h : Iv.excl0 I = true) (hx : Iv.mem x I) : x ≠ 0 := by
  unfold Iv.excl0 at h; unfold Iv.mem at hx
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · have h0 : (0:ℝ) < I.lo.m := by exact_mod_cast h
    have : 0 < I.lo.val := div_pos h0 (two_pow_pos _)
    intro hx0; rw [hx0] at hx; linarith [hx.1]
  · have h0 : (I.hi.m : ℝ) < 0 := by exact_mod_cast h
    have : I.hi.val < 0 := div_neg_of_neg_of_pos h0 (two_pow_pos _)
    intro hx0; rw [hx0] at hx; linarith [hx.2]

/-! Horner -/
noncomputable def hornR (cs : List Int) (y : ℝ) : ℝ := cs.foldr (fun (c : Int) (acc : ℝ) => (c : ℝ) + y * acc) 0
noncomputable def horn2R (H : List (List Int)) (x y : ℝ) : ℝ := H.foldr (fun (row : List Int) (acc : ℝ) => hornR row y + x * acc) 0

theorem mem_hornI (cs : List Int) {y : ℝ} {Y : Iv} (hy : Iv.mem y Y) : Iv.mem (hornR cs y) (hornI cs Y) := by
  induction cs with
  | nil => simpa [hornR, hornI] using Iv.mem_const 0
  | cons c cs ih =>
    simp only [hornR, hornI, List.foldr_cons] at ih ⊢
    exact Iv.mem_add (Iv.mem_const c) (Iv.mem_mul hy ih)

theorem mem_horn2I (H : List (List Int)) {x y : ℝ} {X Y : Iv} (hx : Iv.mem x X) (hy : Iv.mem y Y) :
    Iv.mem (horn2R H x y) (horn2I H X Y) := by
  induction H with
  | nil => simpa [horn2R, horn2I] using Iv.mem_const 0
  | cons row H ih =>
    simp only [horn2R, horn2I, List.foldr_cons] at ih ⊢
    exact Iv.mem_add (mem_hornI row hy) (Iv.mem_mul hx ih)

end KS23
