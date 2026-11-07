/-
  KS23.Chain — the level-0 chain certificate: explicit polynomial vectors `P_v(r,s)` with identities
  checked by Kronecker substitution, and the theorem that any (axis-normalized) realization yields a
  parameter point `(r,s) ∈ [-1,1]²` at which every `P_v` is a nonzero multiple of the realization vector.
-/
import KS23.Geom
import KS23.PE

namespace KS23

abbrev HP := List (List Int)

structure PV where
  x : HP
  y : HP
  z : HP
deriving Inhabited

noncomputable def PV.ev (P : PV) (r s : ℝ) : V3 := ⟨horn2R P.x r s, horn2R P.y r s, horn2R P.z r s⟩

def hpE (H : HP) : PE := .hp H .v0 .v1
def cE (c : Int) : PE := .hp [[c]] .v0 .v1
def varE (k : Nat) : PE := if k = 0 then .v0 else .v1
def lk (T : List (Nat × PV)) (v : Nat) : PV := (T.lookup v).getD default

theorem evalR_hpE (H : HP) (r s : ℝ) : (hpE H).evalR r s = horn2R H r s := rfl
theorem evalR_cE (c : Int) (r s : ℝ) : (cE c).evalR r s = c := by
  simp [cE, PE.evalR, horn2R, hornR]
theorem evalR_varE (k : Nat) (r s : ℝ) : (varE k).evalR r s = if k = 0 then r else s := by
  unfold varE; split <;> rfl

/-- `g * Pv = Pa × Pb`, componentwise -/
def idCross (g : HP) (Pv Pa Pb : PV) : List PE :=
  [ .sub (.mul (hpE g) (hpE Pv.x)) (.sub (.mul (hpE Pa.y) (hpE Pb.z)) (.mul (hpE Pa.z) (hpE Pb.y))),
    .sub (.mul (hpE g) (hpE Pv.y)) (.sub (.mul (hpE Pa.z) (hpE Pb.x)) (.mul (hpE Pa.x) (hpE Pb.z))),
    .sub (.mul (hpE g) (hpE Pv.z)) (.sub (.mul (hpE Pa.x) (hpE Pb.y)) (.mul (hpE Pa.y) (hpE Pb.x))) ]

def parE (k : Nat) (g p q c : HP) : PE :=
  .sub (.mul (hpE g) (hpE c))
    (.add (.mul (.sub (cE 1) (.mul (varE k) (varE k))) (hpE p)) (.mul (.mul (cE 2) (varE k)) (hpE q)))
/-- `g * Pv = (1 - X²) pp + 2 X qq` -/
def idParam (k : Nat) (g : HP) (Pv pp qq : PV) : List PE :=
  [parE k g pp.x qq.x Pv.x, parE k g pp.y qq.y Pv.y, parE k g pp.z qq.z Pv.z]

def ebI (i c : Nat) : Int := if i = c then 1 else 0
def idBasis (Pv : PV) (i : Nat) : List PE :=
  [.sub (hpE Pv.x) (cE (ebI i 0)), .sub (hpE Pv.y) (cE (ebI i 1)), .sub (hpE Pv.z) (cE (ebI i 2))]

theorem allcheck {l : List PE} (h : l.all PE.check = true) : ∀ e ∈ l, ∀ r s, e.evalR r s = 0 :=
  fun e he => PE.check_sound e (List.all_eq_true.1 h e he)

theorem idCross_sound {g : HP} {Pv Pa Pb : PV} (h : (idCross g Pv Pa Pb).all PE.check = true) (r s : ℝ) :
    smul (horn2R g r s) (Pv.ev r s) = cross (Pa.ev r s) (Pb.ev r s) := by
  have H := allcheck h
  have h1 := H _ List.mem_cons_self r s; have h2 := H _ (List.mem_cons_of_mem _ List.mem_cons_self) r s; have h3 := H _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) r s
  simp only [PE.evalR, evalR_hpE] at h1 h2 h3
  ext <;> simp only [smul, cross, PV.ev] <;> linarith

theorem idParam_sound {k : Nat} {g : HP} {Pv pp qq : PV} (h : (idParam k g Pv pp qq).all PE.check = true) (r s : ℝ) :
    smul (horn2R g r s) (Pv.ev r s) =
      vadd (smul (1 - (if k = 0 then r else s) ^ 2) (pp.ev r s)) (smul (2 * (if k = 0 then r else s)) (qq.ev r s)) := by
  have H := allcheck h
  have h1 := H _ List.mem_cons_self r s; have h2 := H _ (List.mem_cons_of_mem _ List.mem_cons_self) r s; have h3 := H _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) r s
  simp only [parE, PE.evalR, evalR_hpE, evalR_cE, evalR_varE] at h1 h2 h3
  ext <;> simp only [smul, vadd, PV.ev] <;> push_cast at h1 h2 h3 ⊢ <;> nlinarith [h1, h2, h3]

theorem idBasis_sound {Pv : PV} {i : Nat} (hi : i < 3) (h : (idBasis Pv i).all PE.check = true) (r s : ℝ) :
    Pv.ev r s = eb i := by
  have H := allcheck h
  have h1 := H _ List.mem_cons_self r s; have h2 := H _ (List.mem_cons_of_mem _ List.mem_cons_self) r s; have h3 := H _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) r s
  simp only [PE.evalR, evalR_hpE, evalR_cE] at h1 h2 h3
  interval_cases i <;> ext <;> simp [PV.ev, eb, ebI] at h1 h2 h3 ⊢ <;> linarith

/-! independence of a variable -/
def indepK (k : Nat) (H : HP) : Bool := if k = 0 then decide (H.length ≤ 1) else H.all (fun row => decide (row.length ≤ 1))
def indepV (k : Nat) (P : PV) : Bool := indepK k P.x && indepK k P.y && indepK k P.z

theorem hornR_short {cs : List Int} (h : cs.length ≤ 1) (y y' : ℝ) : hornR cs y = hornR cs y' := by
  match cs, h with
  | [], _ => rfl
  | [c], _ => simp [hornR]

theorem indepK_sound {k : Nat} {H : HP} (h : indepK k H = true) (r s t : ℝ) :
    horn2R H r s = horn2R H (if k = 0 then t else r) (if k = 0 then s else t) := by
  unfold indepK at h
  split at h
  · next hk =>
    simp only [hk, if_true]
    match H, (decide_eq_true_iff.1 h) with
    | [], _ => rfl
    | [row], _ => simp [horn2R]
  · next hk =>
    simp only [hk, if_false]
    induction H with
    | nil => rfl
    | cons row H ih =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [horn2R, List.foldr_cons] at ih ⊢
      rw [hornR_short h.1 s t, ih h.2]

theorem indepV_sound {k : Nat} {P : PV} (h : indepV k P = true) (r s t : ℝ) :
    P.ev r s = P.ev (if k = 0 then t else r) (if k = 0 then s else t) := by
  simp only [indepV, Bool.and_eq_true] at h
  simp only [PV.ev]; rw [← indepK_sound h.1.1, ← indepK_sound h.1.2, ← indepK_sound h.2]

/-! the chain -/
inductive Step where
  | basis (v i : Nat)
  | cross (v a b : Nat) (g : HP)
  | param (v w rr k : Nat) (pp : PV) (gp : HP) (qq : PV) (gq : HP) (g : HP)

def Step.v : Step → Nat
  | .basis v _ => v
  | .cross v _ _ _ => v
  | .param v _ _ _ _ _ _ _ _ => v

structure L0 where
  n : Nat
  E : List (Nat × Nat)
  steps : List Step
  P : List (Nat × PV)

def isEdge (E : List (Nat × Nat)) (a b : Nat) : Bool := E.contains (a, b) || E.contains (b, a)
def inR (n v : Nat) : Bool := decide (1 ≤ v) && decide (v ≤ n)

theorem isEdge_sound {E : List (Nat × Nat)} {a b : Nat} (h : isEdge E a b = true) : (a, b) ∈ E ∨ (b, a) ∈ E := by
  unfold isEdge at h; simp only [Bool.or_eq_true, List.contains_iff_mem] at h; exact h
theorem inR_sound {n v : Nat} (h : inR n v = true) : 1 ≤ v ∧ v ≤ n := by
  unfold inR at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h

def stepOK (C : L0) (done : List Nat) : Step → Bool
  | .basis v i => inR C.n v && decide (i < 3) && (idBasis (lk C.P v) i).all PE.check
  | .cross v a b g => inR C.n v && inR C.n a && inR C.n b && (a != b) && done.contains a && done.contains b &&
      isEdge C.E v a && isEdge C.E v b && (idCross g (lk C.P v) (lk C.P a) (lk C.P b)).all PE.check
  | .param v w rr k pp gp qq gq g => inR C.n v && inR C.n w && inR C.n rr && (w != rr) && done.contains w &&
      done.contains rr && isEdge C.E v w && done.all (fun u => indepV k (lk C.P u)) && indepV k pp && indepV k qq &&
      indepK k gp && indepK k gq && (idCross gp pp (lk C.P w) (lk C.P rr)).all PE.check &&
      (idCross gq qq (lk C.P w) pp).all PE.check && (idParam k g (lk C.P v) pp qq).all PE.check

def chainOK (C : L0) : List Nat → List Step → Bool
  | _, [] => true
  | done, st :: rest => stepOK C done st && chainOK C (st.v :: done) rest

def Inv (C : L0) (x : Nat → V3) (r s : ℝ) (v : Nat) : Prop := ∃ l : ℝ, l ≠ 0 ∧ (lk C.P v).ev r s = smul l (x v)

theorem chain_sound (C : L0) (x : Realization C.n C.E)
    (hb : ∀ v i, i < 3 → Step.basis v i ∈ C.steps → ∃ μ : ℝ, μ ≠ 0 ∧ x.vec v = smul μ (eb i)) :
    ∀ (sts : List Step) (done : List Nat) (r s : ℝ), (∀ st ∈ sts, st ∈ C.steps) → chainOK C done sts = true →
      -1 ≤ r → r ≤ 1 → -1 ≤ s → s ≤ 1 → (∀ v ∈ done, Inv C x.vec r s v) →
      ∃ r' s' : ℝ, -1 ≤ r' ∧ r' ≤ 1 ∧ -1 ≤ s' ∧ s' ≤ 1 ∧ ∀ v ∈ sts.map Step.v ++ done, Inv C x.vec r' s' v := by
  intro sts
  induction sts with
  | nil => intro done r s _ _ h1 h2 h3 h4 hI; exact ⟨r, s, h1, h2, h3, h4, by simpa using hI⟩
  | cons st rest ih =>
    intro done r s hmem hok h1 h2 h3 h4 hI
    simp only [chainOK, Bool.and_eq_true] at hok
    obtain ⟨hst, hrest⟩ := hok
    have hmem' : ∀ st' ∈ rest, st' ∈ C.steps := fun st' h => hmem st' (List.mem_cons_of_mem _ h)
    have hin : st ∈ C.steps := hmem st (List.mem_cons_self)
    -- one step: produce a new point and invariants for st.v :: done
    have step : ∃ r' s' : ℝ, -1 ≤ r' ∧ r' ≤ 1 ∧ -1 ≤ s' ∧ s' ≤ 1 ∧ ∀ v ∈ st.v :: done, Inv C x.vec r' s' v := by
      cases st with
      | basis v i =>
        simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hst
        obtain ⟨⟨hv, hi⟩, hid⟩ := hst
        refine ⟨r, s, h1, h2, h3, h4, ?_⟩
        intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · obtain ⟨μ, hμ, hx⟩ := hb _ i hi hin
          refine ⟨1 / μ, by simpa using hμ, ?_⟩
          rw [idBasis_sound hi hid, hx, smul_smul]; field_simp; rw [smul_one]
        · exact hI u hu
      | cross v a b g =>
        simp only [stepOK, Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at hst
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨hv, ha⟩, hbb⟩, hab⟩, hda⟩, hdb⟩, hea⟩, heb⟩, hid⟩ := hst
        refine ⟨r, s, h1, h2, h3, h4, ?_⟩
        intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · obtain ⟨la, hla, hPa⟩ := hI a hda
          obtain ⟨lb, hlb, hPb⟩ := hI b hdb
          have va := inR_sound hv; have aa := inR_sound ha; have bb := inR_sound hbb
          exact xstep hla hlb hPa hPb (x.nonzero _ aa.1 aa.2) (x.nonzero _ bb.1 bb.2) (x.nonzero _ va.1 va.2)
            (x.distinct a b aa.1 aa.2 bb.1 bb.2 hab) (isEdge_orth x (isEdge_sound hea))
            (isEdge_orth x (isEdge_sound heb)) (idCross_sound hid r s)
        · exact hI u hu
      | param v w rr k pp gp qq gq g =>
        simp only [stepOK, Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at hst
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hw⟩, hrr⟩, hwr⟩, hdw⟩, hdr⟩, hevw⟩, hind⟩, hipp⟩, hiqq⟩, higp⟩, higq⟩, hid1⟩, hid2⟩, hid3⟩ := hst
        obtain ⟨lw, hlw, hPw⟩ := hI w hdw
        obtain ⟨lr, hlr, hPr⟩ := hI rr hdr
        have vv := inR_sound hv; have ww := inR_sound hw; have rv := inR_sound hrr
        have e1 := idCross_sound hid1 r s
        have e2 := idCross_sound hid2 r s
        obtain ⟨t, μ, ht1, ht2, hμ, hpar⟩ := pstep hlw hlr hPw hPr (x.nonzero _ ww.1 ww.2) (x.nonzero _ rv.1 rv.2)
          (x.nonzero _ vv.1 vv.2) (x.distinct w rr ww.1 ww.2 rv.1 rv.2 hwr) (isEdge_orth x (isEdge_sound hevw)) e1 e2
        set r' := if k = 0 then t else r
        set s' := if k = 0 then s else t
        have hr' : -1 ≤ r' ∧ r' ≤ 1 := by simp only [r']; split <;> constructor <;> linarith
        have hs' : -1 ≤ s' ∧ s' ≤ 1 := by simp only [s']; split <;> constructor <;> linarith
        refine ⟨r', s', hr'.1, hr'.2, hs'.1, hs'.2, ?_⟩
        intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · have e3 := idParam_sound hid3 r' s'
          have hX : (if k = 0 then r' else s') = t := by simp only [r', s']; split <;> rfl
          rw [hX, ← indepV_sound hipp r s t, ← indepV_sound hiqq r s t, hpar] at e3
          have hg : horn2R g r' s' ≠ 0 := by
            intro h0; rw [h0] at e3
            exact smul_ne_zero hμ (x.nonzero _ vv.1 vv.2) (by rw [← e3]; ext <;> simp [smul, V3.zero])
          refine ⟨μ / horn2R g r' s', div_ne_zero hμ hg, ?_⟩
          have : (lk C.P u).ev r' s' = smul (1 / horn2R g r' s') (smul (horn2R g r' s') ((lk C.P u).ev r' s')) := by
            rw [smul_smul]; field_simp; rw [smul_one]
          rw [this, e3, smul_smul]; congr 1; field_simp
        · obtain ⟨l, hl, hP⟩ := hI u hu
          refine ⟨l, hl, ?_⟩
          rw [← indepV_sound (List.all_eq_true.1 hind u hu) r s t]; exact hP
    obtain ⟨r', s', g1, g2, g3, g4, hI'⟩ := step
    obtain ⟨r'', s'', k1, k2, k3, k4, hfin⟩ := ih (st.v :: done) r' s' hmem' hrest g1 g2 g3 g4 hI'
    refine ⟨r'', s'', k1, k2, k3, k4, ?_⟩
    intro v hv
    apply hfin
    simp only [List.map_cons, List.mem_append, List.mem_cons] at hv ⊢
    tauto

end KS23
