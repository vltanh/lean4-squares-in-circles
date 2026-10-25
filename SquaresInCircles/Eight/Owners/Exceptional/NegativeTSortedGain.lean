module

public import SquaresInCircles.Eight.Owners.Critical.NegativeTOrdinaryData
public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTScalarModel
public import SquaresInCircles.Eight.Owners.Sole.NegativeTDSupport

/-!
# Eight squares: the sorted-D secant gain outside the critical strip

D is bounded by its sorted support at the same `q`, which gives the gain `c J(s)` with
`J s = (13/12) tan s - (2/5)(sec s - 1)` (`sorted_gain_lower`). The quadratic lower slope `s g(s)`
comes from an identity of Taylor polynomials (`J_quadratic`); its decreasing slope is used only up
to the cap, and beyond it the derivative of `J` gives the growth `83/100` (`late_growth`). The
corrected gain then bounds the gain of the stress (`corrected_gain`).
-/

section
/-!
## Original exceptional-contact stress with a negative T primary

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
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ExceptionalNegativeTSortedGain
open GlobalGA ActualSortedSupport ExceptionalECoefficients
open ExceptionalNegativeTScalarModel (g)

def J (s : ℝ) : ℝ := (13/12)*Real.tan s-(2/5)*(1/Real.cos s-1)
def Jd (s : ℝ) : ℝ := (13/12-(2/5)*Real.sin s)/(Real.cos s)^2
def sortedGain (q c s : ℝ) : ℝ :=
  c*((13/12)*Real.tan s+(1/Real.cos s-1)/2)-ActualSortedSupport.support q 1 (c/Real.cos s)+ActualSortedSupport.support q 1 c
def correction (b : Band) (td : Bool) (t : ℝ) : ℝ :=
  if td && decide (b≠.low) then (8/25)*(c b t-1)^2 else 0
def lowerGain (b : Band) (td : Bool) (t s : ℝ) : ℝ :=
  if td then c b t*J s else (21/20)*c b t*s

@[simp] theorem J_zero : J 0=0 := by norm_num [J]
@[simp] theorem sortedGain_zero (q c : ℝ) : sortedGain q c 0=0 := by simp [sortedGain]

theorem g_decreasing {s a : ℝ} (hs : s∈Icc 0 a) (ha : a≤3/10) : g a≤g s := by
  have hp := mul_nonneg (sub_nonneg.mpr hs.2)
    (show 0≤(1/5:ℝ)-(8/25)*(a+s) by linarith [hs.1,hs.2])
  dsimp [g]
  nlinarith

theorem g_lower {a : ℝ} (ha : a∈Icc 0 (3/10:ℝ)) : 10521/10000<g a := by
  have hh := g_decreasing ha (by norm_num : (3/10:ℝ)≤3/10)
  norm_num [g] at hh ⊢
  linarith

theorem J_quadratic {s : ℝ} (hs : s∈Ioc 0 (3/10:ℝ)) : s*g s<J s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by norm_num [frameCap]; linarith [hs.2]⟩
  have hc : 0<Real.cos s := transport_cos_pos (by rw [abs_of_nonneg hs.1.le]; exact hs'.2)
  have hsin := mul_le_mul_of_nonneg_left (sin_lower_seven hs.1.le) (by norm_num : (0:ℝ)≤13/12)
  have hcosL := mul_le_mul_of_nonneg_left (cos_lower_six hs.1.le) (by norm_num : (0:ℝ)≤2/5)
  have hgpos : 0 ≤ s*g s := mul_nonneg hs.1.le (by linarith [g_lower (Ioc_subset_Icc_self hs)])
  have hcosU := mul_le_mul_of_nonneg_left (cos_upper_four hs.1.le) hgpos
  let reserve : ℝ := 37/900-s/12+(223/1800)*s^2+(7/900)*s^3-(4097/302400)*s^4
  have hs4 := pow_le_pow_left₀ hs.1.le hs.2 4
  have hreserve : (2/125:ℝ)<reserve := by
    dsimp [reserve]
    norm_num at hs4
    nlinarith [sq_nonneg s,pow_nonneg hs.1.le 3]
  have hnum : s^3*reserve≤
      (13/12)*Real.sin s-(2/5)*(1-Real.cos s)-s*g s*Real.cos s := by
    dsimp [g,reserve] at *
    nlinarith
  have hnum0 : 0<(13/12)*Real.sin s-(2/5)*(1-Real.cos s)-s*g s*Real.cos s := by
    have hp := mul_pos (pow_pos hs.1 3) (show 0<reserve by linarith)
    linarith
  have hid : (J s-s*g s)*Real.cos s=
      (13/12)*Real.sin s-(2/5)*(1-Real.cos s)-s*g s*Real.cos s := by
    dsimp [J]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
  rw [← hid] at hnum0
  have hh := (mul_pos_iff_of_pos_right hc).1 hnum0
  linarith

theorem J_linear {s a : ℝ} (ha : a∈Icc 0 (3/10:ℝ)) (hs : s∈Icc 0 a) :
    g a*s≤J s := by
  by_cases hz : s=0
  · simp [hz]
  · have hs0 : 0<s := lt_of_le_of_ne hs.1 (Ne.symm hz)
    have hh := J_quadratic ⟨hs0,hs.2.trans ha.2⟩
    have hm := mul_le_mul_of_nonneg_right (g_decreasing hs ha.2) hs.1
    nlinarith

theorem J_hasDerivAt {s : ℝ} (hc : Real.cos s≠0) : HasDerivAt J (Jd s) s := by
  have ht := (Real.hasDerivAt_tan hc).const_mul (13/12:ℝ)
  have hs := ((Real.hasDerivAt_cos s).inv hc).sub_const 1
  convert ht.sub (hs.const_mul (2/5:ℝ)) using 1
  · funext y
    simp only [J,Pi.sub_apply,Pi.inv_apply,one_div]
  · dsimp [Jd]
    field_simp [hc]

theorem derivative_lower {b : Band} {t s : ℝ} (ht : t∈domain b)
    (hs : s∈Icc 0 (3/10:ℝ)) : (83/100:ℝ)<c b t*Jd s := by
  have hc0 : 17253/20000≤c b t := by
    by_cases hb : b=.low
    · subst b
      exact (low_bounds ht).1.trans (low_bounds ht).2.2.1
    · linarith [(balanced_bounds hb ht).2.2.2.1]
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs'.2)
  have hsin := (Real.sin_le hs.1).trans hs.2
  have hcos2 : (Real.cos s)^2≤1 := by nlinarith [(transport_trig hs').1,Real.cos_le_one s]
  have hnum : (83/100:ℝ)<c b t*(13/12-(2/5)*Real.sin s) := by
    have hm := mul_le_mul hc0 (show (289/300:ℝ)≤13/12-(2/5)*Real.sin s by linarith)
      (by norm_num) (by linarith)
    nlinarith
  dsimp [Jd]
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ (pow_pos hcos 2)).2
  nlinarith

theorem late_growth {b : Band} {t a s : ℝ} (ht : t∈domain b)
    (ha : a∈Icc 0 (3/10:ℝ)) (hs : s∈Icc a (3/10:ℝ)) :
    (83/100)*(s-a)≤c b t*(J s-J a) := by
  let f : ℝ → ℝ := fun x => c b t*J x-(83/100)*x
  have hd (x : ℝ) (hx : x∈Icc 0 (3/10:ℝ)) :
      HasDerivAt f (c b t*Jd x-83/100) x := by
    have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; norm_num [frameCap]; linarith [hx.2])
    have h1 : HasDerivAt (fun y => c b t*J y) (c b t*Jd x) x :=
      (J_hasDerivAt hc.ne').const_mul _
    have h2 : HasDerivAt (fun y : ℝ => (83/100:ℝ)*y) (83/100) x := by
      simpa using (hasDerivAt_id x).const_mul (83/100:ℝ)
    exact h1.sub h2
  have hm : MonotoneOn f (Icc 0 (3/10:ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => hd x (Ioo_subset_Icc_self hx)
    · intro x hx
      linarith [derivative_lower ht (Ioo_subset_Icc_self hx)]
  have hh := hm ha ⟨ha.1.trans hs.1,hs.2⟩ hs.1
  dsimp [f] at hh
  linarith

theorem sorted_gain_lower {q c s : ℝ} (hL : qLow≤q) (hQ : q≤qCap)
    (hc : 0<c) (hs : s∈Icc 0 (3/10:ℝ)) : c*J s≤ sortedGain q c s := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; norm_num [frameCap]; linarith [hs.2])
  have hsec : c≤c/Real.cos s := (le_div_iff₀ hcos).2 (by nlinarith [Real.cos_le_one s])
  have hlip := second_lipschitz_nine_tenths hL hQ
    (show 0≤1+c by positivity) (show 0≤1+c/Real.cos s by positivity)
    (div_pos hc hcos) hsec
  have hid : c/Real.cos s-c=c*(1/Real.cos s-1) := by ring
  rw [hid] at hlip
  dsimp [J,sortedGain]
  nlinarith

theorem correction_lower {q t : ℝ} {b : Band} (hL : qLow≤q) (hQ : q≤qCap)
    (ht : t∈domain b) :
    correction b true t≤full q 1 (c b t)-ActualSortedSupport.support q 1 (c b t) := by
  have hc := (ranges ht).2.2.2.1
  by_cases hb : b=.low
  · subst b
    have hh := support_le_full (show 0≤q by norm_num [qLow] at hL; linarith)
      (show 0≤1+c .low t by positivity)
    simp only [correction,Bool.true_and,ne_eq,not_true_eq_false,decide_false,
      Bool.false_eq_true,↓reduceIte]
    linarith
  · have hbnd := balanced_bounds hb ht
    have hN : Real.sqrt (1+(c b t)^2)≤307/200 := by
      have hroot := Real.sq_sqrt (show 0≤1+(c b t)^2 by positivity)
      have h0 := Real.sqrt_nonneg (1+(c b t)^2)
      nlinarith [hbnd.2.2.2.1,hbnd.2.2.2.2.1]
    have hh := SoleNegativeTDSupport.sorted_correction hL hQ
      (by norm_num : (0:ℝ)≤1) hc.le hbnd.2.2.2.1.le (by simpa using hN)
    simpa [correction,hb] using hh

theorem corrected_gain {q t s : ℝ} {b : Band}
    (hL : qLow≤q) (hQ : q≤qCap) (ht : t∈domain b)
    (hs : s∈Icc 0 (3/10:ℝ)) :
    correction b true t+c b t*J s≤
      ExceptionalNegativeTStress.gain true (Real.sqrt q) (ell b t) (c b t) s+
        full q 1 (c b t/Real.cos s)-ActualSortedSupport.support q 1 (c b t/Real.cos s) := by
  have hb := correction_lower hL hQ ht
  have hg := sorted_gain_lower hL hQ (ranges ht).2.2.2.1 hs
  have hid : full q 1 (c b t)-ActualSortedSupport.support q 1 (c b t)+sortedGain q (c b t) s=
      ExceptionalNegativeTStress.gain true (Real.sqrt q) (ell b t) (c b t) s+
        full q 1 (c b t/Real.cos s)-ActualSortedSupport.support q 1 (c b t/Real.cos s) := by
    simp only [full,sortedGain,ExceptionalNegativeTStress.gain,FlatTStress.secantCharge,
      PositiveAngularEnvelope.pairNorm_zero,↓reduceIte,one_pow]
    ring
  rw [← hid]
  linarith

end SquaresInCircles.Eight.ExceptionalNegativeTSortedGain
end
end
end
