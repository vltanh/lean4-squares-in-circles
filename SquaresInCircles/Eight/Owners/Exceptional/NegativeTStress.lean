module

public import SquaresInCircles.Eight.Owners.Critical.NegativeTOrdinaryData

/-!
# Eight squares: original exceptional-contact stress with a negative T primary

The selected BT/TD owners and their secant weights
are changed in the literal original seven-edge stress. Their residual
adjustment is constant during the G/E split. The varying EH multiplier
still multiplies the original exact EH0 contact, including its signed
error. T's work is evaluated at its actual flat-core coordinate.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalNegativeTStress
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open PositiveAngularEnvelope ExceptionalContactStress
open CriticalNegativeTOrdinaryData (bWeight tWeight)

def btOwner (td : Bool) : Fin 4 := if td then 2 else 3
def tdOwner (td : Bool) : Fin 4 := if td then 2 else 0
def primary (C : SignedCycle) (td : Bool) : ℝ := if td then delta C.theta T else delta C.theta B

theorem bt_cases (td : Bool) : btOwner td=2 ∨ btOwner td=3 := by cases td <;> simp [btOwner]
theorem td_cases (td : Bool) : tdOwner td=0 ∨ tdOwner td=2 := by cases td <;> simp [tdOwner]

def adjustment (C : SignedCycle) (td : Bool) (c s : ℝ) : ℝ :=
  bWeight td c s*(edgeWidth (delta C.theta B)-C.edge B (btOwner td))+
    tWeight td c s*(edgeWidth (delta C.theta T)-C.edge T (tdOwner td))-
    c*(edgeWidth (delta C.theta B)-C.edge B 2)-
    c*(edgeWidth (delta C.theta T)-C.edge T 0)

def value (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta t s x : ℝ) : ℝ :=
  ExceptionalContactStress.value C ab R k l c eta t x+adjustment C td c s

def forces (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ) : Vertex → Point :=
  SoleEStress.forces C ab (btOwner td) (tdOwner td) 3 0
    (k*tilt eta x) k l (bWeight td c s) (tWeight td c s) 1 (tilt eta e)

def variableDemand (C : SignedCycle) (td : Bool) (k l c eta s x e : ℝ) : ℝ :=
  k*tilt eta x*edgeWidth (delta C.theta H)+k*edgeWidth x+
    l*edgeWidth (delta C.theta A)+bWeight td c s*edgeWidth (delta C.theta B)+
    tWeight td c s*edgeWidth (delta C.theta T)+edgeWidth e+
    tilt eta e*edgeWidth (delta C.theta E)

def anchorWork (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ) : ℝ :=
  work (forces C ab td k l c eta s x e H) (C.point H)+
    work (forces C ab td k l c eta s x e A) (C.point A)+
    work (forces C ab td k l c eta s x e B) (C.point B)+
    work (forces C ab td k l c eta s x e D) (C.point D)

def stress (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta s x e : ℝ) : ℝ :=
  variableDemand C td k l c eta s x e-anchorWork C ab td k l c eta s x e-
    work (forces C ab td k l c eta s x e T) (C.point T)-
    k*sigma R eta*Real.sin x-eWork C eta e

def anchorSupport (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta s x e : ℝ) : ℝ :=
  R*SoleEStress.anchorNorms C ab (btOwner td) (tdOwner td) 3 0
    (k*tilt eta x) k l (bWeight td c s) (tWeight td c s) 1 (tilt eta e)-
    SoleEStress.halfShift C ab (btOwner td) (tdOwner td) 3 0
      (k*tilt eta x) k l (bWeight td c s) (tWeight td c s) 1 (tilt eta e)

def increment (C : SignedCycle) (ab : Fin 4) (td : Bool) (R k l c eta s x e : ℝ) : ℝ :=
  SoleEStress.increment C ab (btOwner td) (tdOwner td) 3 0
    (k*tilt eta x) k l (bWeight td c s) (tWeight td c s) 1 (tilt eta e) R

def gain (td : Bool) (R l c s : ℝ) : ℝ :=
  FlatTStress.secantCharge R c (if td then 1 else l) s

theorem value_eq_stress {C : SignedCycle} {ab : Fin 4} (td : Bool) (R k l c eta s : ℝ)
    {t x : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t)
    (hn : C.NormalAnchors) (hcontact : Contact C) :
    value C ab td R k l c eta t s x=stress C ab td R k l c eta s x (t-x) := by
  rw [value,ExceptionalContactStress.value_eq_stress R k l c eta hab ht hx hn hcontact]
  rcases hab with rfl | rfl <;> cases td <;>
    simp [stress,variableDemand,anchorWork,forces,adjustment,
      ExceptionalContactStress.stress,ExceptionalContactStress.variableDemand,
      ExceptionalContactStress.anchorWork,ExceptionalContactStress.forces,
      SoleEStress.forces,SoleEStress.weights,CoreEStress.owners,force,previous,source,
      target,word,add,scale,work,SignedCycle.edge,zeroProjection,quarterProjection,
      H,A,B,T,D,E,next,btOwner,tdOwner] <;> ring

theorem concave {C : SignedCycle} (ab : Fin 4) (td : Bool) {R k l c eta t s : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap) (hk : k∈Icc (431/500:ℝ) 1)
    (heta : eta∈Icc (1/4:ℝ) (327/1000)) (ht : t∈Icc 0 frameCap)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained qCap)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hEy : 0≤(C.point E).y) :
    ConcaveOn ℝ (Icc 0 t) (value C ab td R k l c eta t s) := by
  exact (ExceptionalContactStress.concave ab hR hQU hk heta ht hs hc ha hEy).add_const _

theorem G_work_le {C : SignedCycle} (ab : Fin 4) (td : Bool) {R k eta : ℝ} (l c s e : ℝ)
    (hR : 0≤R) (hk : 0≤k) (heta : 0≤eta) (hx : delta C.theta G∈Icc 0 frameCap)
    (hs : (C.point G).Sorted) (hc : (C.point G).Contained (R^2)) :
    work (forces C ab td k l c eta s (delta C.theta G) e G) (C.point G)≤
      k*sigma R eta*Real.sin (delta C.theta G) := by
  have hh := work_le_circleSupport hR hs hc (forces C ab td k l c eta s (delta C.theta G) e G)
  have hf : forces C ab td k l c eta s (delta C.theta G) e G =
      SecondaryEStress.forces C ab (btOwner td) (tdOwner td)
        (tiltedWeight k eta (delta C.theta G)) k l (bWeight td c s) (tWeight td c s) G := by
    rw [forces,SoleEStress.force_G]; rfl
  have hsup := positive_G_support (C := C) (R := R) (ab := ab) (bt := btOwner td)
    (td := tdOwner td) (l := l) (b := bWeight td c s) (t := tWeight td c s) hk heta hx
  rw [hf,hsup] at hh
  rw [hf]
  refine hh.trans (le_of_eq ?_)
  simp only [primarySupport,sigma]
  ring

theorem E_work (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x : ℝ) :
    work (forces C ab td k l c eta s x (delta C.theta D) E) (C.point E)=
      eWork C eta (delta C.theta D) := by
  rw [forces,SoleEStress.force_E (Or.inr rfl) (Or.inl rfl)]
  simp [primaryDE,primaryEH,ExceptionalContactStress.tilt,work,eWork]
  ring

theorem necessary {C : SignedCycle} {ab : Fin 4} (td : Bool) {R k l c eta t s : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hk : 0≤k) (hl : 0≤l) (hc0 : 0≤c)
    (heta : 0≤eta) (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t)
    (hpoints : ∀ i,(C.point i).Sorted) (hcircle : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td) 3 0 i)) :
    value C ab td R k l c eta t s (delta C.theta G)≤0 := by
  let x := delta C.theta G
  let e := delta C.theta D
  have hx : x∈Icc 0 t := ⟨hG,by dsimp [x,e] at *; linarith⟩
  have he : e∈Icc 0 t := ⟨hD,by dsimp [x,e] at *; linarith⟩
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  have he' : e∈Icc 0 frameCap := ⟨he.1,he.2.trans ht.2⟩
  have hxe : t-x=e := by dsimp [x,e]; linarith
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have hb0 : 0≤bWeight td c s := by cases td <;> simp [bWeight] <;> positivity
  have ht0 : 0≤tWeight td c s := by cases td <;> simp [tWeight] <;> positivity
  have hn0 := mul_nonneg hk (tilt_nonneg heta hx')
  have hp0 := tilt_nonneg heta he'
  have hw : ∀ i,0≤SoleEStress.weights (k*tilt eta x) k l
      (bWeight td c s) (tWeight td c s) 1 (tilt eta e) i := by
    intro i
    fin_cases i <;> simp [SoleEStress.weights,hn0,hk,hl,hb0,ht0,hp0]
  let Bnd : Vertex → ℝ := ![
    work (forces C ab td k l c eta s x e H) (C.point H),k*sigma R eta*Real.sin x,
    work (forces C ab td k l c eta s x e A) (C.point A),
    work (forces C ab td k l c eta s x e B) (C.point B),
    work (forces C ab td k l c eta s x e T) (C.point T),
    work (forces C ab td k l c eta s x e D) (C.point D),eWork C eta e]
  have hb : ∀ i,work (forces C ab td k l c eta s x e i) (C.point i)≤Bnd i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact G_work_le ab td l c s e hR hk heta hx' (hpoints G) (hcircle G)
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact (E_work C ab td k l c eta s x).le
  have hsep := weighted_separation_le hw hf hb
  have hd : variableDemand C td k l c eta s x e=
      demand C (SoleEStress.weights (k*tilt eta x) k l (bWeight td c s) (tWeight td c s) 1 (tilt eta e)) := by
    rw [SoleEStress.demand_eq]
    simp [variableDemand,x,e]
  rw [value_eq_stress td R k l c eta s hab ht hx hn hcontact,hxe]
  change stress C ab td R k l c eta s x e≤0
  dsimp [stress]
  rw [hd]
  simp only [Bnd,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero] at hsep
  dsimp [anchorWork]
  linarith

theorem anchorWork_le {C : SignedCycle} {ab : Fin 4} (td : Bool) (R k l c eta s x e : ℝ)
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) :
    anchorWork C ab td k l c eta s x e≤anchorSupport C ab td R k l c eta s x e := by
  have hH := work_le_signed_support hR (hc H) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.H_nonneg]) (forces C ab td k l c eta s x e H)
  have hA := work_le_signed_support hR (hc A) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.A_nonneg]) (forces C ab td k l c eta s x e A)
  have hB := work_le_signed_support hR (hc B) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.B_nonpos]) (forces C ab td k l c eta s x e B)
  have hD := work_le_signed_support hR (hc D) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.D_nonpos]) (forces C ab td k l c eta s x e D)
  have hsum := SoleEStress.sum_bounds C hab (bt_cases td) (td_cases td)
    (Or.inr rfl) (Or.inl rfl) (k*tilt eta x) k l (bWeight td c s) (tWeight td c s) 1 (tilt eta e) R
  simp only [SoleEStress.bound,Fin.sum_univ_succ] at hsum
  dsimp [anchorWork,anchorSupport,forces] at *
  dsimp [signedSupport] at hsum
  linarith

theorem T_work {C : SignedCycle} (ab : Fin 4) (td : Bool) (k l c eta x e : ℝ) {s : ℝ}
    (hs : s∈Icc 0 frameCap) (hsource : primary C td= -s) (hflat : (C.point T).a=7/12) :
    work (forces C ab td k l c eta s x e T) (C.point T)= -(7/12)*c*Real.tan s := by
  have hcos := (transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)).ne'
  rw [forces,SoleEStress.force_T]
  cases td
  · exact negative_BT_work hcos (by simpa [primary] using hsource) hflat
  · exact negative_TD_work hcos (by simpa [primary] using hsource) hflat

theorem decomposition {C : SignedCycle} {ab : Fin 4} (td : Bool) (R k l c eta x e : ℝ) {s : ℝ}
    (hab : ab=0 ∨ ab=2) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hs : s∈Icc 0 frameCap) (hsource : primary C td= -s)
    (halign : td=false → delta C.theta T=0) :
    variableDemand C td k l c eta s x e-anchorSupport C ab td R k l c eta s x e+
      (7/12)*c*Real.tan s-k*sigma R eta*Real.sin x-sigma R eta*Real.sin e=
      ExceptionalContactSupport.baseline R k l c eta x e+gain td R l c s+
        increment C ab td R k l c eta s x e := by
  have hcos := (transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)).ne'
  rcases hab with rfl | rfl <;> cases td <;>
    simp [primary] at hsource <;>
    simp [variableDemand,anchorSupport,increment,ExceptionalContactSupport.baseline,
      gain,FlatTStress.secantCharge,SoleEStress.increment,SoleEStress.anchorNorms,
      SoleEStress.halfShift,SoleEStress.zeroNorms,btOwner,tdOwner,bWeight,tWeight,
      ordinaryDE,ordinaryEH,hsource,halign,width_eq (ha H),width_eq (ha A),
      width_eq (ha B),width_eq (ha E),edgeWidth_negative_formula hs,
      Real.tan_eq_sin_div_cos,PositiveAngularEnvelope.phi,psi,pairNorm_symm k l] <;>
    field_simp [hcos] <;> ring

theorem value_lower {C : SignedCycle} {ab : Fin 4} (td : Bool) {R k l c eta t s x : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (heta : 0≤eta)
    (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t) (hs : s∈Icc 0 frameCap)
    (hpoints : ∀ i,(C.point i).Sorted) (hcircle : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap) (hcontact : Contact C)
    (hsource : primary C td= -s) (hflat : (C.point T).a=7/12)
    (halign : td=false → delta C.theta T=0) :
    ExceptionalContactSupport.baseline R k l c eta x (t-x)+gain td R l c s+
      increment C ab td R k l c eta s x (t-x)≤value C ab td R k l c eta t s x := by
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  have hw := anchorWork_le td R k l c eta s x (t-x) hab hR hcircle hn
  have hT := T_work ab td k l c eta x (t-x) hs hsource hflat
  have hE := ExceptionalContactSupport.eWork_le hR heta he (hpoints E) (hcircle E)
  have hid := decomposition td R k l c eta x (t-x) hab ha hs hsource halign
  rw [value_eq_stress td R k l c eta s hab ht hx hn hcontact]
  dsimp [stress]
  linarith

end SquaresInCircles.Eight.ExceptionalNegativeTStress
