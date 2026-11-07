/-
  KS23.Cert — charts (reparametrizations of the level-0 parameter square), interval evaluation of the
  vertex vectors on a box, the quadtree check, and the final non-realizability theorem.
-/
import KS23.QE

namespace KS23

structure IV3 where
  x : Iv
  y : Iv
  z : Iv

def IV3.mem (u : V3) (I : IV3) : Prop := Iv.mem u.x I.x ∧ Iv.mem u.y I.y ∧ Iv.mem u.z I.z
def icross (A B : IV3) : IV3 :=
  ⟨Iv.sub (Iv.mul A.y B.z) (Iv.mul A.z B.y), Iv.sub (Iv.mul A.z B.x) (Iv.mul A.x B.z),
   Iv.sub (Iv.mul A.x B.y) (Iv.mul A.y B.x)⟩
def idot (A B : IV3) : Iv := Iv.add (Iv.add (Iv.mul A.x B.x) (Iv.mul A.y B.y)) (Iv.mul A.z B.z)
def hornV (P : PV) (X Y : Iv) : IV3 := ⟨horn2I P.x X Y, horn2I P.y X Y, horn2I P.z X Y⟩

theorem mem_icross {u v : V3} {A B : IV3} (hu : IV3.mem u A) (hv : IV3.mem v B) : IV3.mem (cross u v) (icross A B) :=
  ⟨Iv.mem_sub (Iv.mem_mul hu.2.1 hv.2.2) (Iv.mem_mul hu.2.2 hv.2.1),
   Iv.mem_sub (Iv.mem_mul hu.2.2 hv.1) (Iv.mem_mul hu.1 hv.2.2),
   Iv.mem_sub (Iv.mem_mul hu.1 hv.2.1) (Iv.mem_mul hu.2.1 hv.1)⟩
theorem mem_idot {u v : V3} {A B : IV3} (hu : IV3.mem u A) (hv : IV3.mem v B) : Iv.mem (dot u v) (idot A B) :=
  Iv.mem_add (Iv.mem_add (Iv.mem_mul hu.1 hv.1) (Iv.mem_mul hu.2.1 hv.2.1)) (Iv.mem_mul hu.2.2 hv.2.2)
theorem mem_hornV (P : PV) {r s : ℝ} {X Y : Iv} (hr : Iv.mem r X) (hs : Iv.mem s Y) : IV3.mem (P.ev r s) (hornV P X Y) :=
  ⟨mem_horn2I _ hr hs, mem_horn2I _ hr hs, mem_horn2I _ hr hs⟩

/-! ## substitution in polynomial expressions -/
def PE.subst (e A B : PE) : PE :=
  match e with
  | .v0 => A
  | .v1 => B
  | .hp H a b => .hp H (a.subst A B) (b.subst A B)
  | .add a b => .add (a.subst A B) (b.subst A B)
  | .sub a b => .sub (a.subst A B) (b.subst A B)
  | .mul a b => .mul (a.subst A B) (b.subst A B)

theorem PE.evalR_subst (A B e : PE) (r s : ℝ) : (e.subst A B).evalR r s = e.evalR (A.evalR r s) (B.evalR r s) := by
  induction e with
  | v0 => rfl
  | v1 => rfl
  | hp H a b iha ihb => simp only [PE.subst, PE.evalR, iha, ihb]
  | add a b iha ihb => simp only [PE.subst, PE.evalR, iha, ihb]
  | sub a b iha ihb => simp only [PE.subst, PE.evalR, iha, ihb]
  | mul a b iha ihb => simp only [PE.subst, PE.evalR, iha, ihb]

/-! ## charts -/
inductive Tok where
  | split
  | leaf (e m : Nat)
  | opn (j : Nat)
  | ext (j : Nat)

def hpQ (H : HP) : QE := .hp H .v0 .v1
theorem evalR_hpQ (H : HP) (r s : ℝ) : (hpQ H).evalR r s = horn2R H r s := rfl

structure Chart where
  phi1 : QE
  phi2 : QE
  R : List (Nat × PV)
  f : List (Nat × (HP × Int))
  X0 : Iv
  Y0 : Iv
  masks : List (List Nat)
  toks : List Tok
  sq : List (Dy × Dy × Dy)

/-- `L · (P_v ∘ φ) = g_v * R_v`, componentwise (f = g / L) -/
def idChart (Ch : Chart) (P R : PV) (f : HP × Int) : List QE :=
  [ .sub (.mul (.c f.2) (.hp P.x Ch.phi1 Ch.phi2)) (.mul (hpQ f.1) (hpQ R.x)),
    .sub (.mul (.c f.2) (.hp P.y Ch.phi1 Ch.phi2)) (.mul (hpQ f.1) (hpQ R.y)),
    .sub (.mul (.c f.2) (.hp P.z Ch.phi1 Ch.phi2)) (.mul (hpQ f.1) (hpQ R.z)) ]

def chartIdsOK (C0 : L0) (Ch : Chart) : Bool :=
  Ch.R.all (fun p => let f := (Ch.f.lookup p.1).getD ([[1]], 1)
    (f.2 != 0) && (idChart Ch (lk C0.P p.1) p.2 f).all QE.check)

def tabStep (Ch : Chart) (mask : List Nat) (X Y : Iv) (tab : List (Nat × IV3)) : Step → List (Nat × IV3)
  | .cross v a b _ =>
    match (if mask.contains v then Ch.R.lookup v else none) with
    | some Rv => (v, hornV Rv X Y) :: tab
    | none =>
      match tab.lookup a, tab.lookup b with
      | some A, some B => (v, icross A B) :: tab
      | _, _ => tab
  | st =>
    match Ch.R.lookup st.v with
    | some Rv => (st.v, hornV Rv X Y) :: tab
    | none => tab

def evalTab (C0 : L0) (Ch : Chart) (mask : List Nat) (X Y : Iv) : List (Nat × IV3) :=
  C0.steps.foldl (tabStep Ch mask X Y) []

def leafOK (C0 : L0) (Ch : Chart) (X Y : Iv) (e m : Nat) : Bool :=
  match C0.E[e]?, Ch.masks[m]? with
  | some (a, b), some mask =>
    let tab := evalTab C0 Ch mask X Y
    match tab.lookup a, tab.lookup b with
    | some A, some B => Iv.excl0 (idot A B)
    | _, _ => false
  | _, _ => false

def inSq (q : Dy × Dy × Dy) (X Y : Iv) : Bool :=
  Dy.le (Dy.add q.1 q.2.2.neg) X.lo && Dy.le X.hi (Dy.add q.1 q.2.2) &&
  Dy.le (Dy.add q.2.1 q.2.2.neg) Y.lo && Dy.le Y.hi (Dy.add q.2.1 q.2.2)

def midD (a b : Dy) : Dy := Dy.half (Dy.add a b)

def treeChk (C0 : L0) (Ch : Chart) (ex : List (Iv × Iv × List Tok)) : Nat → Iv → Iv → List Tok → Option (List Tok)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | fuel + 1, X, Y, t :: rest =>
    match t with
    | .leaf e m => if leafOK C0 Ch X Y e m then some rest else none
    | .opn j =>
      match Ch.sq[j]? with
      | some q => if inSq q X Y then some rest else none
      | none => none
    | .ext j =>
      match ex[j]? with
      | some p => if decide (p.1 = X ∧ p.2.1 = Y) then some rest else none
      | none => none
    | .split =>
      let mx := midD X.lo X.hi
      let my := midD Y.lo Y.hi
      match treeChk C0 Ch ex fuel ⟨X.lo, mx⟩ ⟨Y.lo, my⟩ rest with
      | none => none
      | some r1 =>
        match treeChk C0 Ch ex fuel ⟨mx, X.hi⟩ ⟨Y.lo, my⟩ r1 with
        | none => none
        | some r2 =>
          match treeChk C0 Ch ex fuel ⟨X.lo, mx⟩ ⟨my, Y.hi⟩ r2 with
          | none => none
          | some r3 => treeChk C0 Ch ex fuel ⟨mx, X.hi⟩ ⟨my, Y.hi⟩ r3

def chartX (a b : Dy) : QE × QE := (.add (dyE a) .v0, .add (dyE b) (.mul .v0 .v1))
def chartY (a b : Dy) : QE × QE := (.add (dyE a) (.mul .v0 .v1), .add (dyE b) .v0)

/-- the child chart covers `[-ρ,ρ] × [-1,1]` and its map is the parent map composed with `ψ` -/
def kidOK (Ch K : Chart) (ψ : QE × QE) (ρ : Dy) : Bool :=
  (QE.sub K.phi1 (Ch.phi1.subst ψ.1 ψ.2)).check && (QE.sub K.phi2 (Ch.phi2.subst ψ.1 ψ.2)).check &&
  Dy.le K.X0.lo ρ.neg && Dy.le ρ K.X0.hi && Dy.le K.Y0.lo (Dy.ofInt (-1)) && Dy.le (Dy.ofInt 1) K.Y0.hi

def kidsOK (Ch : Chart) : List (Dy × Dy × Dy) → List (Chart × Chart) → Bool
  | [], [] => true
  | q :: qs, k :: ks => kidOK Ch k.1 (chartX q.1 q.2.1) q.2.2 && kidOK Ch k.2 (chartY q.1 q.2.1) q.2.2 && kidsOK Ch qs ks
  | _, _ => false

def chartChk (C0 : L0) (Ch : Chart) (ex : List (Iv × Iv × List Tok)) (kids : List (Chart × Chart)) : Bool :=
  chartIdsOK C0 Ch && (treeChk C0 Ch ex 64 Ch.X0 Ch.Y0 Ch.toks).isSome && kidsOK Ch Ch.sq kids

/-- a chart is OK if no realization's level-0 parameters are the image of a point of its box -/
def ChartOK (C0 : L0) (Ch : Chart) : Prop :=
  ∀ (x : Realization C0.n C0.E) (r s : ℝ), Iv.mem r Ch.X0 → Iv.mem s Ch.Y0 →
    (∀ v ∈ C0.steps.map Step.v, Inv C0 x.vec (Ch.phi1.evalR r s) (Ch.phi2.evalR r s) v) → False

/-! ## soundness -/

theorem chainOK_cross {C : L0} : ∀ (sts : List Step) (done : List Nat), chainOK C done sts = true →
    ∀ v a b g, Step.cross v a b g ∈ sts →
      inR C.n v = true ∧ inR C.n a = true ∧ inR C.n b = true ∧ a ≠ b ∧ isEdge C.E v a = true ∧ isEdge C.E v b = true := by
  intro sts
  induction sts with
  | nil => intro _ _ v a b g h; simp at h
  | cons st rest ih =>
    intro done h v a b g hm
    simp only [chainOK, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hm with rfl | hm
    · simp only [stepOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, ha⟩, hb⟩, hab⟩, _⟩, _⟩, hea⟩, heb⟩, _⟩, _⟩ := h
      exact ⟨hv, ha, hb, hab, hea, heb⟩
    · exact ih _ h.2 v a b g hm

theorem mem_of_lookup {α : Type} : ∀ {l : List (Nat × α)} {a : Nat} {b : α}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, c) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · next he => simp only [Option.some.injEq] at h; subst h; rw [beq_iff_eq] at he; subst he; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem lookup_cons {α : Type} (k v : Nat) (A : α) (l : List (Nat × α)) :
    ((k, A) :: l).lookup v = if v = k then some A else l.lookup v := by
  simp only [List.lookup]; split <;> simp_all

theorem chainOK_inR {C : L0} : ∀ (sts : List Step) (done : List Nat), chainOK C done sts = true →
    ∀ st ∈ sts, inR C.n st.v = true := by
  intro sts
  induction sts with
  | nil => intro _ _ st h; simp at h
  | cons st rest ih =>
    intro done h st' hm
    simp only [chainOK, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hm with rfl | hm
    · have h1 := h.1
      cases st' with
      | basis v i => simp only [stepOK, Bool.and_eq_true] at h1; exact h1.1.1
      | cross v a b g => simp only [stepOK, Bool.and_eq_true] at h1; exact h1.1.1.1.1.1.1.1.1
      | param v w rr k pp gp qq gq g => simp only [stepOK, Bool.and_eq_true] at h1; exact h1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
    · exact ih _ h.2 st' hm

def TabOK (x : Nat → V3) (tab : List (Nat × IV3)) : Prop :=
  ∀ v A, tab.lookup v = some A → ∃ k : ℝ, k ≠ 0 ∧ IV3.mem (smul k (x v)) A

/-- every entry of the interval table encloses a nonzero multiple of the realization vector -/
theorem evalTab_sound (C0 : L0) (hL : chainOK C0 [] C0.steps = true) (Ch : Chart) (hids : chartIdsOK C0 Ch = true)
    (x : Realization C0.n C0.E) (mask : List Nat) (X Y : Iv) (r s : ℝ) (hr : Iv.mem r X) (hs : Iv.mem s Y)
    (hI : ∀ v ∈ C0.steps.map Step.v, Inv C0 x.vec (Ch.phi1.evalR r s) (Ch.phi2.evalR r s) v) :
    TabOK x.vec (evalTab C0 Ch mask X Y) := by
  have hrng : ∀ v ∈ C0.steps.map Step.v, x.vec v ≠ V3.zero := by
    intro v hv
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hv
    have := inR_sound (chainOK_inR _ _ hL st hst)
    exact x.nonzero _ this.1 this.2
  have hexp : ∀ v Rv, v ∈ C0.steps.map Step.v → Ch.R.lookup v = some Rv →
      ∃ k : ℝ, k ≠ 0 ∧ IV3.mem (smul k (x.vec v)) (hornV Rv X Y) := by
    intro v Rv hv hR
    have hc := List.all_eq_true.1 hids _ (mem_of_lookup hR)
    set f := (Ch.f.lookup v).getD ([[1]], 1)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨hL, hc⟩ := hc
    have H := fun e he => QE.check_sound e (List.all_eq_true.1 hc e he)
    have h1 := H _ List.mem_cons_self r s
    have h2 := H _ (List.mem_cons_of_mem _ List.mem_cons_self) r s
    have h3 := H _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) r s
    simp only [QE.evalR, evalR_hpQ] at h1 h2 h3
    obtain ⟨l, hl, hP⟩ := hI v hv
    have hLr : (f.2 : ℝ) ≠ 0 := by exact_mod_cast hL
    have hPe : smul (horn2R f.1 r s) (Rv.ev r s) = smul (f.2 * l) (x.vec v) := by
      rw [← smul_smul, ← hP]; ext <;> simp only [PV.ev, smul] <;> linarith
    have hf : horn2R f.1 r s ≠ 0 := by
      intro h0; rw [h0] at hPe
      exact smul_ne_zero (mul_ne_zero hLr hl) (hrng v hv) (by rw [← hPe]; ext <;> simp [smul, V3.zero])
    refine ⟨f.2 * l / horn2R f.1 r s, div_ne_zero (mul_ne_zero hLr hl) hf, ?_⟩
    have : smul (f.2 * l / horn2R f.1 r s) (x.vec v) = Rv.ev r s := by
      have e : Rv.ev r s = smul (1 / horn2R f.1 r s) (smul (horn2R f.1 r s) (Rv.ev r s)) := by
        rw [smul_smul]; field_simp; rw [smul_one]
      rw [e, hPe, smul_smul]; congr 1; field_simp
    rw [this]; exact mem_hornV Rv hr hs
  -- fold induction
  have key : ∀ (sts : List Step) (tab : List (Nat × IV3)), (∀ st ∈ sts, st ∈ C0.steps) → TabOK x.vec tab →
      TabOK x.vec (sts.foldl (tabStep Ch mask X Y) tab) := by
    intro sts
    induction sts with
    | nil => intro tab _ h; exact h
    | cons st rest ih =>
      intro tab hsub htab
      simp only [List.foldl_cons]
      apply ih _ (fun st' h => hsub st' (List.mem_cons_of_mem _ h))
      have hst : st ∈ C0.steps := hsub st List.mem_cons_self
      have hstv : st.v ∈ C0.steps.map Step.v := List.mem_map_of_mem hst
      -- adding an explicit entry
      have addE : ∀ v Rv, v ∈ C0.steps.map Step.v → Ch.R.lookup v = some Rv →
          TabOK x.vec ((v, hornV Rv X Y) :: tab) := by
        intro v Rv hv hR u A hu
        rw [lookup_cons] at hu
        split at hu
        · next he => subst he; simp only [Option.some.injEq] at hu; subst hu; exact hexp u Rv hv hR
        · exact htab u A hu
      cases st with
      | cross v a b g =>
        obtain ⟨hv, ha, hb, hab, hea, heb⟩ := chainOK_cross _ _ hL v a b g hst
        simp only [tabStep]
        split
        · next Rv hR =>
          split at hR
          · exact addE v Rv hstv hR
          · simp at hR
        · split
          · next A B hA hB =>
            intro u U hu
            rw [lookup_cons] at hu
            split at hu
            · next he =>
              subst he; simp only [Option.some.injEq] at hu; subst hu
              obtain ⟨ka, hka, hmA⟩ := htab a A hA
              obtain ⟨kb, hkb, hmB⟩ := htab b B hB
              have va := inR_sound hv; have aa := inR_sound ha; have bb := inR_sound hb
              have hxa := x.nonzero _ aa.1 aa.2; have hxb := x.nonzero _ bb.1 bb.2; have hxv := x.nonzero _ va.1 va.2
              have hc := cross_ne_zero hxa hxb (x.distinct a b aa.1 aa.2 bb.1 bb.2 hab)
              have hk := perp_two (isEdge_orth x (isEdge_sound hea)) (isEdge_orth x (isEdge_sound heb)) hc
              set κ := dot (cross (x.vec a) (x.vec b)) (x.vec u) / dot (cross (x.vec a) (x.vec b)) (cross (x.vec a) (x.vec b))
              have hκ : κ ≠ 0 := by intro h0; rw [hk, h0] at hxv; apply hxv; ext <;> simp [smul, V3.zero]
              refine ⟨ka * kb / κ, div_ne_zero (mul_ne_zero hka hkb) hκ, ?_⟩
              have : smul (ka * kb / κ) (x.vec u) = cross (smul ka (x.vec a)) (smul kb (x.vec b)) := by
                rw [cross_smul_left, cross_smul_right, smul_smul]
                conv_lhs => rw [hk, smul_smul]
                congr 1; field_simp
              rw [this]; exact mem_icross hmA hmB
            · exact htab u U hu
          · exact htab
      | basis v i =>
        simp only [tabStep]
        split
        · next Rv hR => exact addE _ Rv hstv hR
        · exact htab
      | param v w rr k pp gp qq gq g =>
        simp only [tabStep]
        split
        · next Rv hR => exact addE _ Rv hstv hR
        · exact htab
  exact key C0.steps [] (fun _ h => h) (by intro v A h; simp [List.lookup] at h)

theorem leaf_sound (C0 : L0) (hL : chainOK C0 [] C0.steps = true) (Ch : Chart) (hids : chartIdsOK C0 Ch = true)
    (x : Realization C0.n C0.E) (X Y : Iv) (e m : Nat) (h : leafOK C0 Ch X Y e m = true)
    (r s : ℝ) (hr : Iv.mem r X) (hs : Iv.mem s Y)
    (hI : ∀ v ∈ C0.steps.map Step.v, Inv C0 x.vec (Ch.phi1.evalR r s) (Ch.phi2.evalR r s) v) : False := by
  unfold leafOK at h
  split at h
  · next a b mask hE hm =>
    simp only at h
    split at h
    · next A B hA hB =>
      have T := evalTab_sound C0 hL Ch hids x mask X Y r s hr hs hI
      obtain ⟨ka, hka, hmA⟩ := T a A hA
      obtain ⟨kb, hkb, hmB⟩ := T b B hB
      have hd := mem_idot hmA hmB
      have hedge : (a, b) ∈ C0.E := List.mem_of_getElem? hE
      have h0 : dot (smul ka (x.vec a)) (smul kb (x.vec b)) = 0 := by
        rw [dot_smul_left, dot_smul_right, x.orth _ hedge]; ring
      exact Iv.excl0_ne h hd h0
    · simp at h
  · simp at h

theorem Dy.val_ofInt (c : Int) : (Dy.ofInt c).val = c := by simp [Dy.ofInt, Dy.val]
theorem Dy.val_half (a : Dy) : (Dy.half a).val = a.val / 2 := by
  simp only [Dy.half, Dy.val, pow_succ]; field_simp

def InSqR (q : Dy × Dy × Dy) (r s : ℝ) : Prop :=
  q.1.val - q.2.2.val ≤ r ∧ r ≤ q.1.val + q.2.2.val ∧ q.2.1.val - q.2.2.val ≤ s ∧ s ≤ q.2.1.val + q.2.2.val

theorem inSq_sound {q : Dy × Dy × Dy} {X Y : Iv} (h : inSq q X Y = true) {r s : ℝ} (hr : Iv.mem r X)
    (hs : Iv.mem s Y) : InSqR q r s := by
  unfold inSq at h; simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [Dy.le_iff, Dy.val_add, Dy.val_neg] at h1 h3
  rw [Dy.le_iff, Dy.val_add] at h2 h4
  unfold Iv.mem at hr hs
  exact ⟨by linarith [hr.1], by linarith [hr.2], by linarith [hs.1], by linarith [hs.2]⟩

theorem treeChk_sound (C0 : L0) (hL : chainOK C0 [] C0.steps = true) (Ch : Chart) (hids : chartIdsOK C0 Ch = true)
    (x : Realization C0.n C0.E) (ex : List (Iv × Iv × List Tok))
    (hex : ∀ p ∈ ex, ∀ r s, Iv.mem r p.1 → Iv.mem s p.2.1 →
      (∀ v ∈ C0.steps.map Step.v, Inv C0 x.vec (Ch.phi1.evalR r s) (Ch.phi2.evalR r s) v) → ∃ q ∈ Ch.sq, InSqR q r s) :
    ∀ (fuel : Nat) (X Y : Iv) (toks rest : List Tok), treeChk C0 Ch ex fuel X Y toks = some rest →
    ∀ r s, Iv.mem r X → Iv.mem s Y →
      (∀ v ∈ C0.steps.map Step.v, Inv C0 x.vec (Ch.phi1.evalR r s) (Ch.phi2.evalR r s) v) → ∃ q ∈ Ch.sq, InSqR q r s := by
  intro fuel
  induction fuel with
  | zero => intro X Y toks rest h; simp [treeChk] at h
  | succ fuel ih =>
    intro X Y toks rest h r s hr hs hI
    match toks, h with
    | [], h => simp [treeChk] at h
    | t :: rest', h =>
      cases t with
      | leaf e m =>
        simp only [treeChk] at h
        split at h
        · next hl => exact (leaf_sound C0 hL Ch hids x X Y e m hl r s hr hs hI).elim
        · simp at h
      | opn j =>
        simp only [treeChk] at h
        split at h
        · next q hq =>
          split at h
          · next hin => exact ⟨q, List.mem_of_getElem? hq, inSq_sound hin hr hs⟩
          · simp at h
        · simp at h
      | ext j =>
        simp only [treeChk] at h
        split at h
        · next p hp =>
          split at h
          · next heq =>
            obtain ⟨e1, e2⟩ := of_decide_eq_true heq
            exact hex p (List.mem_of_getElem? hp) r s (e1 ▸ hr) (e2 ▸ hs) hI
          · simp at h
        · simp at h
      | split =>
        simp only [treeChk] at h
        set mx := midD X.lo X.hi
        set my := midD Y.lo Y.hi
        have hmx : mx.val = (X.lo.val + X.hi.val) / 2 := by simp only [mx, midD, Dy.val_half, Dy.val_add]
        have hmy : my.val = (Y.lo.val + Y.hi.val) / 2 := by simp only [my, midD, Dy.val_half, Dy.val_add]
        have sx : Iv.mem r ⟨X.lo, mx⟩ ∨ Iv.mem r ⟨mx, X.hi⟩ := by
          unfold Iv.mem at hr ⊢; rcases le_total r mx.val with h' | h'
          · exact Or.inl ⟨hr.1, h'⟩
          · exact Or.inr ⟨h', hr.2⟩
        have sy : Iv.mem s ⟨Y.lo, my⟩ ∨ Iv.mem s ⟨my, Y.hi⟩ := by
          unfold Iv.mem at hs ⊢; rcases le_total s my.val with h' | h'
          · exact Or.inl ⟨hs.1, h'⟩
          · exact Or.inr ⟨h', hs.2⟩
        split at h
        · simp at h
        · next r1 h1 =>
          split at h
          · simp at h
          · next r2 h2 =>
            split at h
            · simp at h
            · next r3 h3 =>
              rcases sx with ax | ax <;> rcases sy with ay | ay
              · exact ih _ _ _ _ h1 r s ax ay hI
              · exact ih _ _ _ _ h3 r s ax ay hI
              · exact ih _ _ _ _ h2 r s ax ay hI
              · exact ih _ _ _ _ h r s ax ay hI

theorem kidOK_sound {Ch K : Chart} {ψ : QE × QE} {ρ : Dy} (h : kidOK Ch K ψ ρ = true) :
    (∀ r s, K.phi1.evalR r s = Ch.phi1.evalR (ψ.1.evalR r s) (ψ.2.evalR r s)) ∧
    (∀ r s, K.phi2.evalR r s = Ch.phi2.evalR (ψ.1.evalR r s) (ψ.2.evalR r s)) ∧
    (∀ r s, -ρ.val ≤ r → r ≤ ρ.val → -1 ≤ s → s ≤ 1 → Iv.mem r K.X0 ∧ Iv.mem s K.Y0) := by
  unfold kidOK at h; simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun r s => ?_, fun r s => ?_, fun r s a1 a2 a3 a4 => ?_⟩
  · have := QE.check_sound _ h1 r s; simp only [QE.evalR, QE.evalR_subst] at this; linarith
  · have := QE.check_sound _ h2 r s; simp only [QE.evalR, QE.evalR_subst] at this; linarith
  · rw [Dy.le_iff, Dy.val_neg] at h3; rw [Dy.le_iff] at h4
    rw [Dy.le_iff, Dy.val_ofInt] at h5; rw [Dy.le_iff, Dy.val_ofInt] at h6
    push_cast at h5 h6
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem kidsOK_mem {Ch : Chart} : ∀ (qs : List (Dy × Dy × Dy)) (ks : List (Chart × Chart)), kidsOK Ch qs ks = true →
    ∀ q ∈ qs, ∃ k ∈ ks, kidOK Ch k.1 (chartX q.1 q.2.1) q.2.2 = true ∧ kidOK Ch k.2 (chartY q.1 q.2.1) q.2.2 = true
  | [], _, _, q, hq => by simp at hq
  | q' :: qs, [], h, q, hq => by simp [kidsOK] at h
  | q' :: qs, k :: ks, h, q, hq => by
    simp only [kidsOK, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨k, List.mem_cons_self, h.1.1, h.1.2⟩
    · obtain ⟨k', hk', hh⟩ := kidsOK_mem qs ks h.2 q hq
      exact ⟨k', List.mem_cons_of_mem _ hk', hh⟩

theorem cover_square {a b r s ρ : ℝ} (h1 : a - ρ ≤ r) (h2 : r ≤ a + ρ) (h3 : b - ρ ≤ s) (h4 : s ≤ b + ρ) :
    (∃ r' s', -ρ ≤ r' ∧ r' ≤ ρ ∧ -1 ≤ s' ∧ s' ≤ 1 ∧ a + r' = r ∧ b + r' * s' = s) ∨
    (∃ r' s', -ρ ≤ r' ∧ r' ≤ ρ ∧ -1 ≤ s' ∧ s' ≤ 1 ∧ a + r' * s' = r ∧ b + r' = s) := by
  rcases le_total |s - b| |r - a| with h | h
  · left
    by_cases hz : r - a = 0
    · refine ⟨r - a, 0, by linarith, by linarith, by norm_num, by norm_num, by ring, ?_⟩
      rw [hz, abs_zero] at h; have : s - b = 0 := abs_nonpos_iff.1 h
      linarith
    · have hq : |(s - b) / (r - a)| ≤ 1 := by rw [abs_div]; exact (div_le_one (abs_pos.2 hz)).2 h
      refine ⟨r - a, (s - b) / (r - a), by linarith, by linarith, (abs_le.1 hq).1, (abs_le.1 hq).2, by ring, ?_⟩
      field_simp; ring
  · right
    by_cases hz : s - b = 0
    · refine ⟨0, 0, by linarith, by linarith, by norm_num, by norm_num, ?_, by linarith⟩
      rw [hz, abs_zero] at h; have : r - a = 0 := abs_nonpos_iff.1 h
      linarith
    · have hq : |(r - a) / (s - b)| ≤ 1 := by rw [abs_div]; exact (div_le_one (abs_pos.2 hz)).2 h
      refine ⟨s - b, (r - a) / (s - b), by linarith, by linarith, (abs_le.1 hq).1, (abs_le.1 hq).2, ?_, by ring⟩
      field_simp; ring

theorem chart_ok (C0 : L0) (hL : chainOK C0 [] C0.steps = true) (Ch : Chart) (ex : List (Iv × Iv × List Tok))
    (kids : List (Chart × Chart)) (hchk : chartChk C0 Ch ex kids = true)
    (hpc : ∀ p ∈ ex, (treeChk C0 Ch [] 64 p.1 p.2.1 p.2.2).isSome = true)
    (hk : ∀ p ∈ kids, ChartOK C0 p.1 ∧ ChartOK C0 p.2) : ChartOK C0 Ch := by
  intro x r s hr hs hI
  unfold chartChk at hchk; simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨hids, htree⟩, hkids⟩ := hchk
  obtain ⟨rest, hrest⟩ := Option.isSome_iff_exists.1 htree
  have hex : ∀ p ∈ ex, ∀ r s, Iv.mem r p.1 → Iv.mem s p.2.1 →
      (∀ v ∈ C0.steps.map Step.v, Inv C0 x.vec (Ch.phi1.evalR r s) (Ch.phi2.evalR r s) v) → ∃ q ∈ Ch.sq, InSqR q r s := by
    intro p hp r s hr hs hI
    obtain ⟨rest', hrest'⟩ := Option.isSome_iff_exists.1 (hpc p hp)
    exact treeChk_sound C0 hL Ch hids x [] (by intro p hp; simp at hp) 64 _ _ _ rest' hrest' r s hr hs hI
  obtain ⟨q, hq, hin⟩ := treeChk_sound C0 hL Ch hids x ex hex 64 _ _ _ rest hrest r s hr hs hI
  obtain ⟨k, hkm, hkx, hky⟩ := kidsOK_mem _ _ hkids q hq
  obtain ⟨hX1, hX2, hXb⟩ := kidOK_sound hkx
  obtain ⟨hY1, hY2, hYb⟩ := kidOK_sound hky
  obtain ⟨hin1, hin2, hin3, hin4⟩ := hin
  rcases cover_square hin1 hin2 hin3 hin4 with ⟨r', s', a1, a2, a3, a4, e1, e2⟩ | ⟨r', s', a1, a2, a3, a4, e1, e2⟩
  · obtain ⟨m1, m2⟩ := hXb r' s' a1 a2 a3 a4
    apply (hk k hkm).1 x r' s' m1 m2
    have p1 : k.1.phi1.evalR r' s' = Ch.phi1.evalR r s := by
      rw [hX1]; simp only [chartX, QE.evalR, evalR_dyE]; rw [e1, e2]
    have p2 : k.1.phi2.evalR r' s' = Ch.phi2.evalR r s := by
      rw [hX2]; simp only [chartX, QE.evalR, evalR_dyE]; rw [e1, e2]
    rw [p1, p2]; exact hI
  · obtain ⟨m1, m2⟩ := hYb r' s' a1 a2 a3 a4
    apply (hk k hkm).2 x r' s' m1 m2
    have p1 : k.2.phi1.evalR r' s' = Ch.phi1.evalR r s := by
      rw [hY1]; simp only [chartY, QE.evalR, evalR_dyE]; rw [e1, e2]
    have p2 : k.2.phi2.evalR r' s' = Ch.phi2.evalR r s := by
      rw [hY2]; simp only [chartY, QE.evalR, evalR_dyE]; rw [e1, e2]
    rw [p1, p2]; exact hI

/-! ## the final statement -/
def basisOK (b0 b1 b2 : Nat) : Step → Bool
  | .basis v i => (v == b0 && i == 0) || (v == b1 && i == 1) || (v == b2 && i == 2)
  | _ => true

def L0check (C0 : L0) (b0 b1 b2 : Nat) : Bool :=
  chainOK C0 [] C0.steps && inR C0.n b0 && inR C0.n b1 && inR C0.n b2 &&
  isEdge C0.E b0 b1 && isEdge C0.E b0 b2 && isEdge C0.E b1 b2 && C0.steps.all (basisOK b0 b1 b2)

def rootOK (Ch : Chart) : Bool :=
  match Ch.phi1, Ch.phi2 with
  | .v0, .v1 => Dy.le Ch.X0.lo (Dy.ofInt (-1)) && Dy.le (Dy.ofInt 1) Ch.X0.hi &&
                Dy.le Ch.Y0.lo (Dy.ofInt (-1)) && Dy.le (Dy.ofInt 1) Ch.Y0.hi
  | _, _ => false

theorem no_realization (C0 : L0) (b0 b1 b2 : Nat) (h : L0check C0 b0 b1 b2 = true) (root : Chart)
    (hroot : rootOK root = true) (hok : ChartOK C0 root) : Realization C0.n C0.E → False := by
  intro x
  unfold L0check at h; simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hL, i0⟩, i1⟩, i2⟩, e01⟩, e02⟩, e12⟩, hbs⟩ := h
  set b : Nat → Nat := fun i => if i = 0 then b0 else if i = 1 then b1 else b2
  have hb : ∀ i, i < 3 → 1 ≤ b i ∧ b i ≤ C0.n := by
    intro i hi; interval_cases i
    · exact inR_sound i0
    · exact inR_sound i1
    · exact inR_sound i2
  obtain ⟨x', hx'⟩ := wlog_frame x b hb (isEdge_sound e01) (isEdge_sound e02) (isEdge_sound e12)
  have hbasis : ∀ v i, i < 3 → Step.basis v i ∈ C0.steps → ∃ μ : ℝ, μ ≠ 0 ∧ x'.vec v = smul μ (eb i) := by
    intro v i hi hm
    have := List.all_eq_true.1 hbs _ hm
    simp only [basisOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
    rcases this with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
    · exact hx' 0 (by norm_num)
    · exact hx' 1 (by norm_num)
    · exact hx' 2 (by norm_num)
  obtain ⟨r, s, h1, h2, h3, h4, hI⟩ := chain_sound C0 x' hbasis C0.steps [] 0 0 (fun _ h => h) hL
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp)
  unfold rootOK at hroot
  split at hroot
  · next hp1 hp2 =>
    simp only [Bool.and_eq_true] at hroot
    obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hroot
    rw [Dy.le_iff, Dy.val_ofInt] at k1 k2 k3 k4
    push_cast at k1 k2 k3 k4
    apply hok x' r s ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    rw [hp1, hp2]; simp only [QE.evalR]; simpa using hI
  · simp at hroot

end KS23

namespace KS23
theorem chainOK_of_L0check {C0 : L0} {b0 b1 b2 : Nat} (h : L0check C0 b0 b1 b2 = true) :
    chainOK C0 [] C0.steps = true := by
  unfold L0check at h; simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1
end KS23
