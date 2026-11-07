/-
  KS23.Geom — vectors in ℝ³, realizations of an orthogonality graph, and the pointwise geometry
  used by the chain: two perpendiculars, the plane parameter, and the orthonormal-frame WLOG.
-/
import Mathlib.Tactic

namespace KS23

@[ext] structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

def dot (u v : V3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z
def cross (u v : V3) : V3 := ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩
def smul (c : ℝ) (u : V3) : V3 := ⟨c * u.x, c * u.y, c * u.z⟩
def vadd (u v : V3) : V3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def V3.zero : V3 := ⟨0, 0, 0⟩

/-- Two vectors span the same ray (the kscert definition). -/
def SameRay (u v : V3) : Prop := ∃ c : ℝ, c ≠ 0 ∧ v = smul c u

/-- A real realization of the graph on vertices `1..n` with edge list `E`: nonzero vectors, orthogonal
    along every edge, pairwise distinct as rays (same shape as kscert's `Realization`). -/
structure Realization (n : Nat) (E : List (Nat × Nat)) where
  vec : Nat → V3
  nonzero : ∀ v, 1 ≤ v → v ≤ n → vec v ≠ V3.zero
  orth : ∀ e ∈ E, dot (vec e.1) (vec e.2) = 0
  distinct : ∀ v w, 1 ≤ v → v ≤ n → 1 ≤ w → w ≤ n → v ≠ w → ¬ SameRay (vec v) (vec w)

theorem dot_self_pos {u : V3} (h : u ≠ V3.zero) : 0 < dot u u := by
  unfold dot
  by_contra hc
  apply h; ext <;> simp [V3.zero] <;> nlinarith [sq_nonneg u.x, sq_nonneg u.y, sq_nonneg u.z]

theorem ne_zero_of_dot {u : V3} (h : dot u u ≠ 0) : u ≠ V3.zero := by
  intro hu; apply h; rw [hu]; simp [dot, V3.zero]

theorem dot_comm (u v : V3) : dot u v = dot v u := by unfold dot; ring
theorem dot_smul_left (c : ℝ) (u v : V3) : dot (smul c u) v = c * dot u v := by unfold dot smul; ring
theorem dot_smul_right (c : ℝ) (u v : V3) : dot u (smul c v) = c * dot u v := by unfold dot smul; ring
theorem cross_smul_left (c : ℝ) (u v : V3) : cross (smul c u) v = smul c (cross u v) := by
  ext <;> simp [cross, smul] <;> ring
theorem cross_smul_right (c : ℝ) (u v : V3) : cross u (smul c v) = smul c (cross u v) := by
  ext <;> simp [cross, smul] <;> ring
theorem smul_smul (a b : ℝ) (u : V3) : smul a (smul b u) = smul (a * b) u := by
  ext <;> simp [smul] <;> ring
theorem smul_one (u : V3) : smul 1 u = u := by ext <;> simp [smul]
theorem dot_cross_self_left (u v : V3) : dot (cross u v) u = 0 := by unfold dot cross; ring
theorem dot_cross_self_right (u v : V3) : dot (cross u v) v = 0 := by unfold dot cross; ring

/-- Lagrange: `|u × v|² = |u|²|v|² - (u·v)²`. -/
theorem lagrange (u v : V3) : dot (cross u v) (cross u v) = dot u u * dot v v - dot u v ^ 2 := by
  unfold dot cross; ring

theorem smul_ne_zero {c : ℝ} {u : V3} (hc : c ≠ 0) (hu : u ≠ V3.zero) : smul c u ≠ V3.zero := by
  intro h; apply hu
  have h1 := congrArg V3.x h; have h2 := congrArg V3.y h; have h3 := congrArg V3.z h
  simp [smul, V3.zero] at h1 h2 h3
  ext <;> simp [V3.zero] <;> tauto

/-- if `c × w = 0` and `c ≠ 0` then `w` is a multiple of `c` -/
theorem par_of_cross_zero {c w : V3} (hc : c ≠ V3.zero) (h : cross c w = V3.zero) :
    w = smul (dot c w / dot c c) c := by
  have hp := dot_self_pos hc
  have h1 := congrArg V3.x h; have h2 := congrArg V3.y h; have h3 := congrArg V3.z h
  simp only [cross, V3.zero] at h1 h2 h3
  have ex : w.x * dot c c = dot c w * c.x := by unfold dot; linear_combination c.z*h2 - c.y*h3
  have ey : w.y * dot c c = dot c w * c.y := by unfold dot; linear_combination -c.z*h1 + c.x*h3
  have ez : w.z * dot c c = dot c w * c.z := by unfold dot; linear_combination -c.x*h2 + c.y*h1
  ext <;> simp only [smul] <;> rw [div_mul_eq_mul_div, eq_div_iff hp.ne'] <;> assumption

/-- `u × v ≠ 0` for nonzero vectors on distinct rays -/
theorem cross_ne_zero {u v : V3} (hu : u ≠ V3.zero) (hv : v ≠ V3.zero) (h : ¬ SameRay u v) :
    cross u v ≠ V3.zero := by
  intro hc; apply h
  refine ⟨dot u v / dot u u, ?_, par_of_cross_zero hu hc⟩
  intro h0; rw [par_of_cross_zero hu hc, h0] at hv; apply hv; ext <;> simp [smul, V3.zero]

/-- orthogonal nonzero vectors have nonzero cross product -/
theorem cross_ne_zero_of_orth {u v : V3} (hu : u ≠ V3.zero) (hv : v ≠ V3.zero) (h : dot u v = 0) :
    cross u v ≠ V3.zero := by
  intro hc
  have := lagrange u v; rw [hc, h] at this
  have : dot V3.zero V3.zero = 0 := by simp [dot, V3.zero]
  nlinarith [dot_self_pos hu, dot_self_pos hv]

/-- a vector orthogonal to `a` and `b` is a multiple of `a × b` (when that is nonzero) -/
theorem perp_two {w a b : V3} (ha : dot w a = 0) (hb : dot w b = 0) (hc : cross a b ≠ V3.zero) :
    w = smul (dot (cross a b) w / dot (cross a b) (cross a b)) (cross a b) := by
  apply par_of_cross_zero hc
  have e1 : cross (cross a b) w = vadd (smul (dot a w) b) (smul (- dot b w) a) := by
    ext <;> simp [cross, vadd, smul, dot] <;> ring
  rw [e1, dot_comm a w, dot_comm b w, ha, hb]; ext <;> simp [vadd, smul, V3.zero]

/-- the x-step: if `P_a = λa x_a`, `P_b = λb x_b`, `x_v ⊥ x_a, x_b`, rays distinct, and
    `g * P_v = P_a × P_b`, then `P_v` is a nonzero multiple of `x_v`. -/
theorem xstep {xa xb xv Pa Pb Pv : V3} {la lb g : ℝ} (hla : la ≠ 0) (hlb : lb ≠ 0)
    (hPa : Pa = smul la xa) (hPb : Pb = smul lb xb)
    (hxa : xa ≠ V3.zero) (hxb : xb ≠ V3.zero) (hxv : xv ≠ V3.zero) (hab : ¬ SameRay xa xb)
    (hva : dot xv xa = 0) (hvb : dot xv xb = 0) (hid : smul g Pv = cross Pa Pb) :
    ∃ l : ℝ, l ≠ 0 ∧ Pv = smul l xv := by
  have hc := cross_ne_zero hxa hxb hab
  have hk := perp_two hva hvb hc
  set k := dot (cross xa xb) xv / dot (cross xa xb) (cross xa xb)
  have hk0 : k ≠ 0 := by intro h0; rw [hk, h0] at hxv; apply hxv; ext <;> simp [smul, V3.zero]
  have hcr : cross Pa Pb = smul (la * lb / k) xv := by
    rw [hPa, hPb, cross_smul_left, cross_smul_right, smul_smul]
    conv_rhs => rw [hk, smul_smul]
    congr 1; field_simp
  have hg : g ≠ 0 := by
    intro h0; rw [h0] at hid
    have : cross Pa Pb = V3.zero := by rw [← hid]; ext <;> simp [smul, V3.zero]
    rw [hcr] at this; exact smul_ne_zero (div_ne_zero (mul_ne_zero hla hlb) hk0) hxv this
  refine ⟨la * lb / k / g, div_ne_zero (div_ne_zero (mul_ne_zero hla hlb) hk0) hg, ?_⟩
  have : Pv = smul (1 / g) (smul g Pv) := by rw [smul_smul]; field_simp; rw [smul_one]
  rw [this, hid, hcr, smul_smul]; congr 1; field_simp

theorem dot_vadd_left (a b c : V3) : dot (vadd a b) c = dot a c + dot b c := by unfold dot vadd; ring

/-- decomposition in an orthogonal frame `w, p, q`: a vector `y ⊥ w` is `α p + β q`. -/
theorem in_plane {y w p q : V3} (hw : w ≠ V3.zero) (hp : p ≠ V3.zero) (hq : q ≠ V3.zero)
    (hwp : dot w p = 0) (hwq : dot w q = 0) (hpq : dot p q = 0) (hy : dot y w = 0) :
    y = vadd (smul (dot y p / dot p p) p) (smul (dot y q / dot q q) q) := by
  have pp := dot_self_pos hp; have qq := dot_self_pos hq
  set α := dot y p / dot p p with hα
  set β := dot y q / dot q q with hβ
  set z := vadd y (vadd (smul (-α) p) (smul (-β) q)) with hzdef
  have hqp : dot q p = 0 := by rw [dot_comm]; exact hpq
  have zp : dot z p = 0 := by
    rw [hzdef, dot_vadd_left, dot_vadd_left, dot_smul_left, dot_smul_left, hqp, hα]; field_simp; ring
  have zq : dot z q = 0 := by
    rw [hzdef, dot_vadd_left, dot_vadd_left, dot_smul_left, dot_smul_left, hpq, hβ]; field_simp; ring
  have zw : dot z w = 0 := by
    rw [hzdef, dot_vadd_left, dot_vadd_left, dot_smul_left, dot_smul_left, dot_comm p w, dot_comm q w,
      hwp, hwq, hy]; ring
  have hc := cross_ne_zero_of_orth hp hq hpq
  have hz := perp_two zp zq hc
  have hw' := perp_two hwp hwq hc
  set κ := dot (cross p q) z / dot (cross p q) (cross p q)
  set κ' := dot (cross p q) w / dot (cross p q) (cross p q)
  have hκ' : κ' ≠ 0 := by intro h0; rw [hw', h0] at hw; apply hw; ext <;> simp [smul, V3.zero]
  have hm : κ * κ' * dot (cross p q) (cross p q) = 0 := by
    have := zw; rw [hz, hw', dot_smul_left, dot_smul_right] at this; linarith
  have hκ : κ = 0 := by
    rcases mul_eq_zero.1 hm with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd h hκ'
    · exact absurd h (ne_of_gt (dot_self_pos hc))
  have hz0 : z = V3.zero := by rw [hz, hκ]; ext <;> simp [smul, V3.zero]
  have h1 := congrArg V3.x hz0; have h2 := congrArg V3.y hz0; have h3 := congrArg V3.z hz0
  simp only [hzdef, vadd, smul, V3.zero] at h1 h2 h3
  ext <;> simp only [vadd, smul] <;> linarith

/-- the plane parameter: every direction `(α, β) ≠ 0` is `μ (1 - t², 2t)` with `t ∈ [-1,1]`, `μ ≠ 0`. -/
theorem plane_param {α β : ℝ} (h : α ≠ 0 ∨ β ≠ 0) :
    ∃ t μ : ℝ, -1 ≤ t ∧ t ≤ 1 ∧ μ ≠ 0 ∧ 1 - t ^ 2 = μ * α ∧ 2 * t = μ * β := by
  have hpos : 0 < α ^ 2 + β ^ 2 := by
    rcases h with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg β]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg α]
  set ρ := Real.sqrt (α ^ 2 + β ^ 2)
  have hρ : 0 < ρ := Real.sqrt_pos.2 hpos
  have hρ2 : ρ ^ 2 = α ^ 2 + β ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  have hβρ : |β| ≤ ρ := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg α])
  have hαρ : |α| ≤ ρ := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg β])
  rcases le_total 0 α with ha | ha
  · have hd : 0 < α + ρ := by linarith
    refine ⟨β / (α + ρ), 2 / (α + ρ), ?_, ?_, by positivity, ?_, ?_⟩
    · rw [le_div_iff₀ hd]; linarith [neg_abs_le β]
    · rw [div_le_iff₀ hd]; linarith [le_abs_self β]
    · field_simp; nlinarith [hρ2]
    · field_simp
  · have hd : 0 < -α + ρ := by linarith [abs_of_nonpos ha]
    refine ⟨-β / (-α + ρ), -2 / (-α + ρ), ?_, ?_, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ hd]; linarith [le_abs_self β]
    · rw [div_le_iff₀ hd]; linarith [neg_abs_le β]
    · exact div_ne_zero (by norm_num) (ne_of_gt hd)
    · field_simp; nlinarith [hρ2]
    · field_simp

end KS23

namespace KS23

/-- the param step: with `pp ∥ Pw × Prr` and `qq ∥ Pw × pp` (both via nonzero factors), every vector
    `xv ⊥ xw` is a nonzero multiple of `(1-t²) pp + 2t qq` for some `t ∈ [-1,1]`. -/
theorem pstep {xw xr xv Pw Pr pp qq : V3} {lw lr gp gq : ℝ} (hlw : lw ≠ 0) (hlr : lr ≠ 0)
    (hPw : Pw = smul lw xw) (hPr : Pr = smul lr xr)
    (hxw : xw ≠ V3.zero) (hxr : xr ≠ V3.zero) (hxv : xv ≠ V3.zero) (hwr : ¬ SameRay xw xr)
    (hvw : dot xv xw = 0) (hid1 : smul gp pp = cross Pw Pr) (hid2 : smul gq qq = cross Pw pp) :
    ∃ t μ : ℝ, -1 ≤ t ∧ t ≤ 1 ∧ μ ≠ 0 ∧ vadd (smul (1 - t ^ 2) pp) (smul (2 * t) qq) = smul μ xv := by
  have hPw0 : Pw ≠ V3.zero := by rw [hPw]; exact smul_ne_zero hlw hxw
  have hcr : cross Pw Pr ≠ V3.zero := by
    rw [hPw, hPr, cross_smul_left, cross_smul_right]
    exact smul_ne_zero hlw (smul_ne_zero hlr (cross_ne_zero hxw hxr hwr))
  have hgp : gp ≠ 0 := by intro h0; apply hcr; rw [← hid1, h0]; ext <;> simp [smul, V3.zero]
  have hpp : pp = smul (1 / gp) (cross Pw Pr) := by rw [← hid1, smul_smul]; field_simp; rw [smul_one]
  have hpp0 : pp ≠ V3.zero := by rw [hpp]; exact smul_ne_zero (by simpa using hgp) hcr
  have hwp : dot Pw pp = 0 := by rw [hpp, dot_smul_right, dot_comm, dot_cross_self_left, mul_zero]
  have hcq : cross Pw pp ≠ V3.zero := cross_ne_zero_of_orth hPw0 hpp0 hwp
  have hgq : gq ≠ 0 := by intro h0; apply hcq; rw [← hid2, h0]; ext <;> simp [smul, V3.zero]
  have hqq : qq = smul (1 / gq) (cross Pw pp) := by rw [← hid2, smul_smul]; field_simp; rw [smul_one]
  have hqq0 : qq ≠ V3.zero := by rw [hqq]; exact smul_ne_zero (by simpa using hgq) hcq
  have hwq : dot Pw qq = 0 := by rw [hqq, dot_smul_right, dot_comm, dot_cross_self_left, mul_zero]
  have hpq : dot pp qq = 0 := by rw [hqq, dot_smul_right, dot_comm, dot_cross_self_right, mul_zero]
  have hvP : dot xv Pw = 0 := by rw [hPw, dot_smul_right, hvw, mul_zero]
  have hdec := in_plane hPw0 hpp0 hqq0 hwp hwq hpq hvP
  set α := dot xv pp / dot pp pp
  set β := dot xv qq / dot qq qq
  have hab : α ≠ 0 ∨ β ≠ 0 := by
    by_contra h; push_neg at h; apply hxv; rw [hdec, h.1, h.2]; ext <;> simp [vadd, smul, V3.zero]
  obtain ⟨t, μ, ht1, ht2, hμ, e1, e2⟩ := plane_param hab
  refine ⟨t, μ, ht1, ht2, hμ, ?_⟩
  have : xv = smul (1 / μ) (vadd (smul (μ * α) pp) (smul (μ * β) qq)) := by
    conv_lhs => rw [hdec]
    ext <;> simp only [vadd, smul] <;> field_simp
  rw [e1, e2, this, smul_smul, mul_one_div_cancel hμ, smul_one]

end KS23

namespace KS23

def eb : Nat → V3
  | 0 => ⟨1, 0, 0⟩
  | 1 => ⟨0, 1, 0⟩
  | _ => ⟨0, 0, 1⟩

section frame
variable {n0 n1 n2 : V3} (h00 : dot n0 n0 = 1) (h11 : dot n1 n1 = 1) (h22 : dot n2 n2 = 1)
  (h01 : dot n0 n1 = 0) (h02 : dot n0 n2 = 0) (h12 : dot n1 n2 = 0)
include h00 h11 h22 h01 h02 h12

theorem recon (y : V3) : y = vadd (smul (dot y n0) n0) (vadd (smul (dot y n1) n1) (smul (dot y n2) n2)) := by
  have nz : ∀ u : V3, dot u u = 1 → u ≠ V3.zero := fun u h => ne_zero_of_dot (by rw [h]; norm_num)
  set y' := vadd y (smul (- dot y n2) n2) with hy'
  have hy2 : dot y' n2 = 0 := by rw [hy', dot_vadd_left, dot_smul_left, h22]; ring
  have hy0 : dot y' n0 = dot y n0 := by rw [hy', dot_vadd_left, dot_smul_left, dot_comm n2 n0, h02]; ring
  have hy1 : dot y' n1 = dot y n1 := by rw [hy', dot_vadd_left, dot_smul_left, dot_comm n2 n1, h12]; ring
  have hd := in_plane (nz n2 h22) (nz n0 h00) (nz n1 h11) (by rw [dot_comm]; exact h02) (by rw [dot_comm]; exact h12) h01 hy2
  rw [hy0, hy1, h00, h11, div_one, div_one] at hd
  have c1 := congrArg V3.x hd; have c2 := congrArg V3.y hd; have c3 := congrArg V3.z hd
  simp only [hy', vadd, smul] at c1 c2 c3
  ext <;> simp only [vadd, smul] <;> linarith

def coord (n0 n1 n2 y : V3) : V3 := ⟨dot y n0, dot y n1, dot y n2⟩

theorem dot_coord (u v : V3) : dot (coord n0 n1 n2 u) (coord n0 n1 n2 v) = dot u v := by
  have hu := recon h00 h11 h22 h01 h02 h12 u
  conv_rhs => rw [hu]
  rw [dot_vadd_left, dot_vadd_left, dot_smul_left, dot_smul_left, dot_smul_left]
  simp only [coord, dot]; ring

theorem coord_zero {u : V3} (h : coord n0 n1 n2 u = V3.zero) : u = V3.zero := by
  have hu := recon h00 h11 h22 h01 h02 h12 u
  have a := congrArg V3.x h; have b := congrArg V3.y h; have c := congrArg V3.z h
  simp only [coord, V3.zero] at a b c
  rw [hu, a, b, c]; ext <;> simp [vadd, smul, V3.zero]

theorem coord_sameRay {u v : V3} (h : SameRay (coord n0 n1 n2 u) (coord n0 n1 n2 v)) : SameRay u v := by
  obtain ⟨c, hc, he⟩ := h
  refine ⟨c, hc, ?_⟩
  have a := congrArg V3.x he; have b := congrArg V3.y he; have d := congrArg V3.z he
  simp only [coord, smul] at a b d
  rw [recon h00 h11 h22 h01 h02 h12 v, a, b, d]
  conv_rhs => rw [recon h00 h11 h22 h01 h02 h12 u]
  ext <;> simp only [vadd, smul] <;> ring
end frame

theorem unit_of {u : V3} (hu : u ≠ V3.zero) :
    dot (smul (1 / Real.sqrt (dot u u)) u) (smul (1 / Real.sqrt (dot u u)) u) = 1 := by
  have hp := dot_self_pos hu
  rw [dot_smul_left, dot_smul_right, ← mul_assoc, div_mul_div_comm, one_mul, Real.mul_self_sqrt hp.le]
  field_simp

theorem isEdge_orth {n : Nat} {E : List (Nat × Nat)} (x : Realization n E) {a b : Nat}
    (h : (a, b) ∈ E ∨ (b, a) ∈ E) : dot (x.vec a) (x.vec b) = 0 := by
  rcases h with h | h
  · exact x.orth _ h
  · rw [dot_comm]; exact x.orth _ h

/-- WLOG: a realization can be rotated so that a triangle `b0 b1 b2` sits on the coordinate axes. -/
theorem wlog_frame {n : Nat} {E : List (Nat × Nat)} (x : Realization n E) (b : Nat → Nat)
    (hb : ∀ i, i < 3 → 1 ≤ b i ∧ b i ≤ n)
    (e01 : (b 0, b 1) ∈ E ∨ (b 1, b 0) ∈ E) (e02 : (b 0, b 2) ∈ E ∨ (b 2, b 0) ∈ E)
    (e12 : (b 1, b 2) ∈ E ∨ (b 2, b 1) ∈ E) :
    ∃ x' : Realization n E, ∀ i, i < 3 → ∃ μ : ℝ, μ ≠ 0 ∧ x'.vec (b i) = smul μ (eb i) := by
  have nz : ∀ i, i < 3 → x.vec (b i) ≠ V3.zero := fun i hi => x.nonzero _ (hb i hi).1 (hb i hi).2
  set N : Nat → V3 := fun i => smul (1 / Real.sqrt (dot (x.vec (b i)) (x.vec (b i)))) (x.vec (b i))
  have hN : ∀ i, i < 3 → dot (N i) (N i) = 1 := fun i hi => unit_of (nz i hi)
  have hO : ∀ i j, (b i, b j) ∈ E ∨ (b j, b i) ∈ E → dot (N i) (N j) = 0 := by
    intro i j h; simp only [N]; rw [dot_smul_left, dot_smul_right, isEdge_orth x h]; ring
  have h00 := hN 0 (by norm_num); have h11 := hN 1 (by norm_num); have h22 := hN 2 (by norm_num)
  have h01 := hO 0 1 e01; have h02 := hO 0 2 e02; have h12 := hO 1 2 e12
  refine ⟨{ vec := fun v => coord (N 0) (N 1) (N 2) (x.vec v),
            nonzero := fun v h1 h2 h => x.nonzero v h1 h2 (coord_zero h00 h11 h22 h01 h02 h12 h),
            orth := fun e he => by rw [dot_coord h00 h11 h22 h01 h02 h12]; exact x.orth e he,
            distinct := fun v w h1 h2 h3 h4 hvw h => x.distinct v w h1 h2 h3 h4 hvw
              (coord_sameRay h00 h11 h22 h01 h02 h12 h) }, ?_⟩
  intro i hi
  have hp : ∀ j, j < 3 → 0 < Real.sqrt (dot (x.vec (b j)) (x.vec (b j))) :=
    fun j hj => Real.sqrt_pos.2 (dot_self_pos (nz j hj))
  have self : ∀ j, j < 3 → dot (x.vec (b j)) (N j) = Real.sqrt (dot (x.vec (b j)) (x.vec (b j))) := by
    intro j hj; simp only [N]; rw [dot_smul_right]
    have h1 := Real.mul_self_sqrt (dot_self_pos (nz j hj)).le
    have h2 := hp j hj
    field_simp; linarith
  have cross0 : ∀ j k, (b j, b k) ∈ E ∨ (b k, b j) ∈ E → dot (x.vec (b j)) (N k) = 0 := by
    intro j k h; simp only [N]; rw [dot_smul_right, isEdge_orth x h, mul_zero]
  have sw : ∀ {j k}, (b j, b k) ∈ E ∨ (b k, b j) ∈ E → (b k, b j) ∈ E ∨ (b j, b k) ∈ E := fun h => h.symm
  interval_cases i
  · refine ⟨_, (hp 0 (by norm_num)).ne', ?_⟩
    simp only [coord]; rw [self 0 (by norm_num), cross0 0 1 e01, cross0 0 2 e02]; ext <;> simp [smul, eb]
  · refine ⟨_, (hp 1 (by norm_num)).ne', ?_⟩
    simp only [coord]; rw [self 1 (by norm_num), cross0 1 0 (sw e01), cross0 1 2 e12]; ext <;> simp [smul, eb]
  · refine ⟨_, (hp 2 (by norm_num)).ne', ?_⟩
    simp only [coord]; rw [self 2 (by norm_num), cross0 2 0 (sw e02), cross0 2 1 (sw e12)]; ext <;> simp [smul, eb]

end KS23
