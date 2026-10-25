module

public import SquaresInCircles.Eight.Owners.Exceptional.ContactSupport
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTCurvature

/-!
# Eight squares: the positive-T stress at an EH0 contact

The T primary stays fixed while the G/E split varies, and its force is bounded on the same
containing circle as G (`T_work_le`). The varying EH multiplier cancels against the EH contact,
signed angle included; the point and frame of H do not move. The weak owners make the stress
nonpositive (`necessary`), and it is concave in the split (`concave`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTStress
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open PositiveAngularEnvelope ExceptionalContactStress

def btOwner (td : Bool) : Fin 4 := if td then 2 else 3
def tdOwner (td : Bool) : Fin 4 := if td then 2 else 0
def primary (C : SignedCycle) (td : Bool) : ℝ :=
  if td then delta C.theta T else delta C.theta B
def bWeight (td : Bool) (c eta z : ℝ) : ℝ := if td then c*tilt eta z else c
def tWeight (td : Bool) (c eta z : ℝ) : ℝ := if td then c else c*tilt eta z

theorem bt_cases (td : Bool) : btOwner td=2 ∨ btOwner td=3 := by
  cases td <;> simp [btOwner]
theorem td_cases (td : Bool) : tdOwner td=0 ∨ tdOwner td=2 := by
  cases td <;> simp [tdOwner]

def forces (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta z x e : ℝ) : Vertex → Point :=
  SoleEStress.forces C ab (btOwner td) (tdOwner td) 3 0
    (k*tilt eta x) k l (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e)

def variableDemand (C : SignedCycle) (td : Bool) (k l c eta z x e : ℝ) : ℝ :=
  k*tilt eta x*edgeWidth (delta C.theta H)+k*edgeWidth x+
    l*edgeWidth (delta C.theta A)+bWeight td c eta z*edgeWidth (delta C.theta B)+
    tWeight td c eta z*edgeWidth (delta C.theta T)+edgeWidth e+
    tilt eta e*edgeWidth (delta C.theta E)

def anchorWork (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta z x e : ℝ) : ℝ :=
  work (forces C ab td k l c eta z x e H) (C.point H)+
    work (forces C ab td k l c eta z x e A) (C.point A)+
    work (forces C ab td k l c eta z x e B) (C.point B)+
    work (forces C ab td k l c eta z x e D) (C.point D)

def tWork (C : SignedCycle) (td : Bool) (c eta z : ℝ) : ℝ :=
  c*Real.sin z*((C.point T).a+(if td then -eta else eta)*(C.point T).y)

def adjustment (C : SignedCycle) (td : Bool) (R c eta z : ℝ) : ℝ :=
  bWeight td c eta z*(edgeWidth (delta C.theta B)-C.edge B (btOwner td))+
    tWeight td c eta z*(edgeWidth (delta C.theta T)-C.edge T (tdOwner td))-
    c*(edgeWidth (delta C.theta B)-C.edge B 2)-
    c*(edgeWidth (delta C.theta T)-C.edge T 0)+tWork C td c eta z-
    c*sigma R eta*Real.sin z

def value (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta t z x : ℝ) : ℝ :=
  ExceptionalContactStress.value C ab R k l c eta (t-z) x+adjustment C td R c eta z

def stress (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta z x e : ℝ) : ℝ :=
  variableDemand C td k l c eta z x e-anchorWork C ab td k l c eta z x e-
    k*sigma R eta*Real.sin x-c*sigma R eta*Real.sin z-eWork C eta e

def anchorSupport (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta z x e : ℝ) : ℝ :=
  R*SoleEStress.anchorNorms C ab (btOwner td) (tdOwner td) 3 0
    (k*tilt eta x) k l (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e)-
    SoleEStress.halfShift C ab (btOwner td) (tdOwner td) 3 0
      (k*tilt eta x) k l (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e)

def increment (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta z x e : ℝ) : ℝ :=
  SoleEStress.increment C ab (btOwner td) (tdOwner td) 3 0
    (k*tilt eta x) k l (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e) R

def baseline (td : Bool) (R k l c eta z x e : ℝ) : ℝ :=
  k*ExceptionalContactSupport.contactScalar R eta x+
    c*ExceptionalContactSupport.contactScalar R eta z+2*l+
    ExceptionalContactSupport.contactScalar R eta e-
    R*SoleEStress.zeroNorms (k*tilt eta x) k l
      (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e)

theorem value_eq_stress {C : SignedCycle} {ab : Fin 4} (td : Bool) (R k l c eta : ℝ)
    {t z x : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈Icc 0 frameCap)
    (hz : z∈Icc 0 t) (hx : x∈Icc 0 (t-z))
    (hsource : primary C td=z) (hn : C.NormalAnchors) (hcontact : Contact C) :
    value C ab td R k l c eta t z x=stress C ab td R k l c eta z x (t-z-x) := by
  have hw : t-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hz.1,ht.2]⟩
  rw [value,ExceptionalContactStress.value_eq_stress R k l c eta hab hw hx hn hcontact]
  rcases hab with rfl | rfl <;> cases td <;>
    simp only [primary, Bool.false_eq_true, ↓reduceIte] at hsource <;> subst hsource <;>
    simp [stress,variableDemand,anchorWork,ExceptionalPositiveTStress.forces,adjustment,tWork,
      ExceptionalContactStress.stress,ExceptionalContactStress.variableDemand,
      ExceptionalContactStress.anchorWork,ExceptionalContactStress.forces,
      SoleEStress.forces,SoleEStress.weights,CoreEStress.owners,force,previous,source,
      target,word,add,scale,work,SignedCycle.edge,zeroProjection,quarterProjection,
      H,A,B,T,D,E,next,btOwner,tdOwner,bWeight,tWeight,ExceptionalContactStress.tilt] <;> ring

theorem concave {C : SignedCycle} (ab : Fin 4) (td : Bool) {R k l c eta t z : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap) (hk : k∈Icc (431/500:ℝ) (521/500))
    (heta : eta∈Icc (1/4:ℝ) (327/1000)) (ht : t∈Icc 0 frameCap)
    (hz : z∈Icc 0 t) (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained qCap)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hEy : 0≤(C.point E).y) :
    ConcaveOn ℝ (Icc 0 (t-z)) (value C ab td R k l c eta t z) := by
  have hw : t-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hz.1,ht.2]⟩
  have hh := ExceptionalPositiveTCurvature.concave
    (K:=ExceptionalContactStress.constant C ab k l c+(C.point E).y)
    (transverse_residual (hs H) (hc H) (ha H)).le hk
    ⟨by linarith [heta.1],heta.2⟩
    (tilt_reserve hR hQU ⟨heta.1,by linarith [heta.2]⟩).le
    (contained_bounds (hs E) (hc E)).1.le hEy hw
  exact hh.add_const (adjustment C td R c eta z)

theorem G_work_le {C : SignedCycle} (ab : Fin 4) (td : Bool) {R k eta : ℝ}
    (l c z e : ℝ) (hR : 0≤R) (hk : 0≤k) (heta : 0≤eta)
    (hx : delta C.theta G∈Icc 0 frameCap)
    (hs : (C.point G).Sorted) (hc : (C.point G).Contained (R^2)) :
    work (forces C ab td k l c eta z (delta C.theta G) e G) (C.point G)≤
      k*sigma R eta*Real.sin (delta C.theta G) := by
  have hh := work_le_circleSupport hR hs hc
    (ExceptionalPositiveTStress.forces C ab td k l c eta z (delta C.theta G) e G)
  have hf : ExceptionalPositiveTStress.forces C ab td k l c eta z (delta C.theta G) e G=
      SecondaryEStress.forces C ab (btOwner td) (tdOwner td) (tiltedWeight k eta (delta C.theta G)) k l
        (bWeight td c eta z) (tWeight td c eta z) G := by
    rw [ExceptionalPositiveTStress.forces,SoleEStress.force_G]; rfl
  have hsup := positive_G_support (R:=R) (ab:=ab) (bt:=btOwner td) (td:=tdOwner td)
    (l:=l) (b:=bWeight td c eta z) (t:=tWeight td c eta z) hk heta hx
  rw [hf] at hh ⊢
  rw [hsup] at hh
  refine hh.trans (le_of_eq ?_)
  unfold primarySupport sigma
  ring

theorem T_work_le {C : SignedCycle} (ab : Fin 4) (td : Bool) {R c eta z : ℝ}
    (k l x e : ℝ) (hR : 0≤R) (hc0 : 0≤c) (heta : 0≤eta)
    (hz : z∈Icc 0 frameCap) (hsource : primary C td=z)
    (hs : (C.point T).Sorted) (hc : (C.point T).Contained (R^2)) :
    work (forces C ab td k l c eta z x e T) (C.point T)≤
      c*sigma R eta*Real.sin z := by
  have hh := work_le_circleSupport hR hs hc
    (ExceptionalPositiveTStress.forces C ab td k l c eta z x e T)
  have hsin := mul_nonneg hc0 (transport_trig hz).2.2.1
  have hvec : ExceptionalPositiveTStress.forces C ab td k l c eta z x e T=
      (c*Real.sin z,(if td then -(c*Real.sin z) else c*Real.sin z)*eta) := by
    rw [ExceptionalPositiveTStress.forces,SoleEStress.force_T]
    cases td
    · rw [show btOwner false=3 from rfl,show tdOwner false=0 from rfl,force_T_bt_primary]
      simp only [primary,Bool.false_eq_true,↓reduceIte] at hsource
      subst hsource
      simp only [bWeight,tWeight,ExceptionalContactStress.tilt,Bool.false_eq_true,↓reduceIte]
      exact Prod.ext (by dsimp only) (by dsimp only; ring)
    · rw [show btOwner true=2 from rfl,show tdOwner true=2 from rfl,force_T_td_primary]
      simp only [primary,↓reduceIte] at hsource
      subst hsource
      simp only [bWeight,tWeight,ExceptionalContactStress.tilt,↓reduceIte]
      exact Prod.ext (by dsimp only) (by dsimp only; ring)
  rw [hvec] at hh ⊢
  cases td
  · simp only [Bool.false_eq_true,↓reduceIte] at hh ⊢
    rw [(scaled_primary_support (R:=R) hsin heta).2] at hh
    refine hh.trans (le_of_eq ?_)
    unfold sigma; ring
  · simp only [↓reduceIte] at hh ⊢
    rw [(scaled_primary_support (R:=R) hsin heta).1] at hh
    refine hh.trans (le_of_eq ?_)
    unfold sigma; ring

theorem E_work (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta z x : ℝ) :
    work (forces C ab td k l c eta z x (delta C.theta D) E) (C.point E)=
      eWork C eta (delta C.theta D) := by
  rw [ExceptionalPositiveTStress.forces,SoleEStress.force_E (Or.inr rfl) (Or.inl rfl)]
  simp [primaryDE,primaryEH,ExceptionalContactStress.tilt,work,eWork]
  ring

theorem necessary {C : SignedCycle} {ab : Fin 4} (td : Bool) {R k l c eta t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hk : 0≤k) (hl : 0≤l) (hc0 : 0≤c)
    (heta : 0≤eta) (ht : t∈Icc 0 frameCap) (hz : z∈Icc 0 t)
    (hsource : primary C td=z) (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D+z=t)
    (hpoints : ∀ i,(C.point i).Sorted) (hcircle : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td) 3 0 i)) :
    value C ab td R k l c eta t z (delta C.theta G)≤0 := by
  let x := delta C.theta G
  let e := delta C.theta D
  have hx : x∈Icc 0 (t-z) := ⟨hG,by dsimp [x,e] at *; linarith⟩
  have he : e∈Icc 0 (t-z) := ⟨hD,by dsimp [x,e] at *; linarith⟩
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by linarith [hx.2,hz.1,ht.2]⟩
  have he' : e∈Icc 0 frameCap := ⟨he.1,by linarith [he.2,hz.1,ht.2]⟩
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans ht.2⟩
  have hxe : t-z-x=e := by dsimp [x,e]; linarith
  have hn0 := mul_nonneg hk (tilt_nonneg heta hx')
  have hp0 := tilt_nonneg heta he'
  have hm0 := mul_nonneg hc0 (tilt_nonneg heta hz')
  have hb0 : 0≤bWeight td c eta z := by cases td <;> simp_all [bWeight]
  have ht0 : 0≤tWeight td c eta z := by cases td <;> simp_all [tWeight]
  have hw : ∀ i,0≤SoleEStress.weights (k*tilt eta x) k l
      (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e) i := by
    intro i
    fin_cases i <;> simp [SoleEStress.weights,hn0,hk,hl,hb0,ht0,hp0]
  let Bnd : Vertex → ℝ := ![
    work (forces C ab td k l c eta z x e H) (C.point H),k*sigma R eta*Real.sin x,
    work (forces C ab td k l c eta z x e A) (C.point A),
    work (forces C ab td k l c eta z x e B) (C.point B),c*sigma R eta*Real.sin z,
    work (forces C ab td k l c eta z x e D) (C.point D),eWork C eta e]
  have hb : ∀ i,work (forces C ab td k l c eta z x e i) (C.point i)≤Bnd i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact G_work_le ab td l c z e hR hk heta hx' (hpoints G) (hcircle G)
    · exact le_rfl
    · exact le_rfl
    · exact T_work_le ab td k l x e hR hc0 heta hz' hsource (hpoints T) (hcircle T)
    · exact le_rfl
    · exact (E_work C ab td k l c eta z x).le
  have hsep := weighted_separation_le hw hf hb
  have hd : variableDemand C td k l c eta z x e=
      demand C (SoleEStress.weights (k*tilt eta x) k l
        (bWeight td c eta z) (tWeight td c eta z) 1 (tilt eta e)) := by
    rw [SoleEStress.demand_eq]
    simp [variableDemand,x,e]
  rw [value_eq_stress td R k l c eta hab ht hz hx hsource hn hcontact,hxe]
  dsimp only [stress]
  rw [hd]
  simp only [Bnd,Fin.sum_univ_seven,Matrix.cons_val] at hsep
  dsimp only [anchorWork]
  linarith

end SquaresInCircles.Eight.ExceptionalPositiveTStress
