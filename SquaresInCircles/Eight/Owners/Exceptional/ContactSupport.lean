module

public import SquaresInCircles.Eight.Owners.Sole.FixedSplit
public import SquaresInCircles.Eight.Owners.Sole.EndpointSupport

/-!
# Eight squares: endpoint supports of the exceptional contact stress

The norm supports enter after the concave expression at fixed points: the stress is at least the
baseline plus the ordinary increment (`value_lower`), where the increment keeps the signed angles,
the EH0 angle included, and E is bounded on the same radius as the other points. The baselines at
the endpoints E and G (`baseline_at_E`, `baseline_at_G`) share one ordinary four-block problem, and
the E endpoint is the smaller one (`E_le_G`, `E_lt_G`).
-/

section
/-!
## Uniform fixed-coordinate concavity at a positive E contact

The exact contact removes the varying EH multiplier.
The same harmonic therefore covers the outside-strip rational families
and the sharp supporting dual. Its curvature reserve holds throughout
the complete split interval, with E's actual nonnegative tangent kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ExceptionalContactCurvature
open SoleFixedSplit

theorem comparison_harmonic {k t x : ℝ} (hk : k∈Icc (431/500:ℝ) 1)
    (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t) :
    SoleFixedSplit.harmonic (-(87/200)*k) ((957/1000)*k) (-(1/2)) (183/200) t x≤-4/25 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ht
  have hkc := mul_le_mul_of_nonneg_right hk.1 (show 0≤Real.cos t by linarith)
  have hks := mul_le_mul_of_nonneg_right hk.2 hs0
  have hcl := mul_lt_mul_of_pos_left hc (by norm_num : (0:ℝ)<431/500)
  rw [show (-4/25:ℝ) = -(4/25) by norm_num]
  apply harmonic_endpoint_upper ht hx (by norm_num)
  · simp only [SoleFixedSplit.harmonic,Real.cos_zero,Real.sin_zero,sub_zero,mul_one,mul_zero,
      add_zero]
    nlinarith [hk.1]
  · simp only [SoleFixedSplit.harmonic,sub_self,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,
      add_zero]
    nlinarith

theorem curvature {MH k eta sigma a b t x : ℝ}
    (hMH : -(13/200:ℝ)≤MH) (hk : k∈Icc (431/500:ℝ) 1)
    (heta : eta∈Icc 0 (327/1000:ℝ)) (hsigma : sigma-1/2≤187/200)
    (ha : a≤283/200) (hb : 0≤b) (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t) :
    -SoleFixedSplit.harmonic (k*MH+k/2) (k*eta*MH+k/2-k*sigma)
      (1/2+b) (1/2-a) t x≤-4/25 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx'
  obtain ⟨hce,hce1,hse0,hse,hsce⟩ := transport_trig he
  have hk0 : 0≤k := by linarith [hk.1]
  have hn : 0≤k*(Real.cos x+eta*Real.sin x) :=
    mul_nonneg hk0 (by nlinarith [mul_nonneg heta.1 hs0])
  have hmH := mul_le_mul_of_nonneg_right hMH hn
  have hcoef : sigma-1/2+(13/200)*eta≤957/1000 := by linarith [heta.2]
  have hcoefG := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hk0 hs0)
  have hcoefE := mul_le_mul_of_nonneg_right ha hse0
  have hminor := mul_nonneg hb (show 0≤Real.cos (t-x) by linarith)
  have hmajor : -SoleFixedSplit.harmonic (k*MH+k/2) (k*eta*MH+k/2-k*sigma)
      (1/2+b) (1/2-a) t x≤
      SoleFixedSplit.harmonic (-(87/200)*k) ((957/1000)*k) (-(1/2)) (183/200) t x := by
    dsimp [SoleFixedSplit.harmonic]
    nlinarith
  exact hmajor.trans (comparison_harmonic hk ht hx)

theorem concave {K MH k eta sigma a b t : ℝ}
    (hMH : -(13/200:ℝ)≤MH) (hk : k∈Icc (431/500:ℝ) 1)
    (heta : eta∈Icc 0 (327/1000:ℝ)) (hsigma : sigma-1/2≤187/200)
    (ha : a≤283/200) (hb : 0≤b) (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 t) (high K MH k eta sigma a b t) := by
  apply concave_of_deriv2
    (f' := harmonicDeriv (k*MH+k/2) (k*eta*MH+k/2-k*sigma) (1/2+b) (1/2-a) t)
    (f'' := fun x => -SoleFixedSplit.harmonic (k*MH+k/2) (k*eta*MH+k/2-k*sigma) (1/2+b) (1/2-a) t x)
  · intro x hx
    exact (SoleFixedSplit.harmonic_hasDerivAt _ _ _ _ _ _).const_add _
  · intro x hx
    exact harmonicDeriv_hasDerivAt _ _ _ _ _ _
  · intro x hx
    exact (curvature hMH hk heta hsigma ha hb ht hx).trans (by norm_num)

/-- A nonnegative sharp endpoint and a strictly positive G endpoint
exclude every split with an actual positive G error, including x=t. -/
theorem positive_of_positive_right {f : ℝ → ℝ} {t x : ℝ}
    (hf : ConcaveOn ℝ (Icc 0 t) f) (hx : x∈Ioc 0 t)
    (h0 : 0≤f 0) (ht : 0<f t) : 0<f x := by
  have ht0 : 0<t := hx.1.trans_le hx.2
  have ha : 0≤(t-x)/t := div_nonneg (sub_nonneg.mpr hx.2) ht0.le
  have hb : 0<x/t := div_pos hx.1 ht0
  have hab : (t-x)/t+x/t=1 := by field_simp; ring
  have hpoint : ((t-x)/t) • (0:ℝ)+(x/t) • t=x := by
    simp only [smul_eq_mul,mul_zero,zero_add]
    exact div_mul_cancel₀ x ht0.ne'
  have hh := hf.2 (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht0.le⟩)
    (show t∈Icc 0 t from ⟨ht0.le,le_rfl⟩) ha hb.le hab
  rw [hpoint] at hh
  have hl := mul_nonneg ha h0
  have hr := mul_pos hb ht
  simp only [smul_eq_mul] at hh
  linarith

end SquaresInCircles.Eight.ExceptionalContactCurvature
end
end
end

section
/-!
## The stress at the exceptional positive E contact

The stress `value` is taken at fixed coordinates: the ordinary angles and the four anchor points
are those of the cycle. The EH0 contact (`Contact`) may have a nonzero signed error; its equality
cancels the varying EH multiplier exactly, with no alignment of the anchor points. The weak owners
and the contact make the stress nonpositive (`necessary`), and it is concave in the G/E split
(`concave`). The same expression serves the rational weights outside the critical strip and the
supporting weights of the sharp family.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalContactStress
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks

def tilt (eta x : ℝ) : ℝ := Real.cos x+eta*Real.sin x

def Contact (C : SignedCycle) : Prop :=
  edgeWidth (delta C.theta E)=(C.point H).a*Real.cos (delta C.theta E)+
    (C.point H).y*Real.sin (delta C.theta E)+(C.point E).y

def constant (C : SignedCycle) (ab : Fin 4) (k l c : ℝ) : ℝ :=
  l*(edgeWidth (delta C.theta A)-C.edge A ab)+
    c*(edgeWidth (delta C.theta B)-C.edge B 2)+
    c*(edgeWidth (delta C.theta T)-C.edge T 0)-k*(C.point A).a-(C.point D).a

def forces (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ) : Vertex → Point :=
  SoleEStress.forces C ab 2 0 3 0 (k*tilt eta x) k l c c 1 (tilt eta e)

def variableDemand (C : SignedCycle) (k l c eta x e : ℝ) : ℝ :=
  k*tilt eta x*edgeWidth (delta C.theta H)+k*edgeWidth x+
    l*edgeWidth (delta C.theta A)+c*edgeWidth (delta C.theta B)+
    c*edgeWidth (delta C.theta T)+edgeWidth e+tilt eta e*edgeWidth (delta C.theta E)

def anchorWork (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ) : ℝ :=
  work (forces C ab k l c eta x e H) (C.point H)+
    work (forces C ab k l c eta x e A) (C.point A)+
    work (forces C ab k l c eta x e B) (C.point B)+
    work (forces C ab k l c eta x e D) (C.point D)

def eWork (C : SignedCycle) (eta e : ℝ) : ℝ :=
  Real.sin e*((C.point E).a+eta*(C.point E).y)

def stress (C : SignedCycle) (ab : Fin 4) (R k l c eta x e : ℝ) : ℝ :=
  variableDemand C k l c eta x e-anchorWork C ab k l c eta x e-
    k*sigma R eta*Real.sin x-eWork C eta e

def value (C : SignedCycle) (ab : Fin 4) (R k l c eta t x : ℝ) : ℝ :=
  SoleFixedSplit.high (constant C ab k l c+(C.point E).y) (SoleSplitModel.transverse C)
    k eta (sigma R eta) (C.point E).a (C.point E).y t x

theorem tilt_nonneg {eta x : ℝ} (heta : 0≤eta) (hx : x∈Icc 0 frameCap) :
    0≤tilt eta x := by
  obtain ⟨hc,_,hs,_,_⟩ := transport_trig hx
  dsimp [tilt]
  nlinarith [mul_nonneg heta hs]

theorem value_eq_stress {C : SignedCycle} {ab : Fin 4} (R k l c eta : ℝ) {t x : ℝ}
    (hab : ab=0 ∨ ab=2) (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t)
    (hn : C.NormalAnchors) (hcontact : Contact C) :
    value C ab R k l c eta t x=stress C ab R k l c eta x (t-x) := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  have hH := hn.H_nonneg
  dsimp [Contact] at hcontact
  rw [value,SoleFixedSplit.high_formula]
  rcases hab with rfl | rfl <;>
    simp [stress,variableDemand,anchorWork,eWork,constant,SoleSplitModel.transverse,
      forces,SoleEStress.forces,SoleEStress.weights,CoreEStress.owners,force,previous,
      source,target,word,add,scale,work,SignedCycle.edge,zeroProjection,quarterProjection,
      H,A,B,T,D,E,next,tilt,edgeWidth_positive_formula hx',
      edgeWidth_positive_formula he] at hcontact hH ⊢ <;>
    rw [abs_of_nonneg hH] <;>
    linear_combination (-(Real.cos (t-x)+eta*Real.sin (t-x)))*hcontact

theorem original_demand (C : SignedCycle) (k l c eta : ℝ) :
    variableDemand C k l c eta (delta C.theta G) (delta C.theta D)=
      demand C (SoleEStress.weights (k*tilt eta (delta C.theta G)) k l c c 1
        (tilt eta (delta C.theta D))) := by
  rw [SoleEStress.demand_eq]
  simp [variableDemand]

theorem E_work (C : SignedCycle) (ab : Fin 4) (k l c eta x : ℝ) :
    work (forces C ab k l c eta x (delta C.theta D) E) (C.point E)=
      eWork C eta (delta C.theta D) := by
  unfold forces
  rw [SoleEStress.force_E (Or.inr rfl) (Or.inl rfl)]
  simp [primaryDE,primaryEH,tilt,work,eWork]
  ring

theorem T_force (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ) :
    forces C ab k l c eta x e T=(0,0) := by
  unfold forces
  rw [SoleEStress.force_T,force_T_secondary]
  simp

theorem G_work_le {C : SignedCycle} (ab : Fin 4) {R k eta : ℝ} (l c e : ℝ)
    (hR : 0≤R) (hk : 0≤k) (heta : 0≤eta)
    (hx : delta C.theta G∈Icc 0 frameCap)
    (hs : (C.point G).Sorted) (hc : (C.point G).Contained (R^2)) :
    work (forces C ab k l c eta (delta C.theta G) e G) (C.point G)≤
      k*sigma R eta*Real.sin (delta C.theta G) := by
  have hh := work_le_circleSupport hR hs hc (forces C ab k l c eta (delta C.theta G) e G)
  have hf : forces C ab k l c eta (delta C.theta G) e G=
      SecondaryEStress.forces C ab 2 0 (tiltedWeight k eta (delta C.theta G)) k l c c G := by
    unfold forces; rw [SoleEStress.force_G]; rfl
  have hsup := positive_G_support (R := R) (ab := ab) (bt := 2) (td := 0)
    (l := l) (b := c) (t := c) hk heta hx
  rw [hf] at hh ⊢
  rw [hsup] at hh
  refine hh.trans (le_of_eq ?_)
  unfold primarySupport sigma
  ring

/-- The seven weak owners and the EH contact make the stress nonpositive; no separate support of E
is used and no point moves. -/
theorem necessary {C : SignedCycle} {ab : Fin 4} {R k l c eta t : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hk : 0≤k) (hl : 0≤l) (hc0 : 0≤c)
    (heta : 0≤eta) (ht : t∈Icc 0 frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) :
    value C ab R k l c eta t (delta C.theta G)≤0 := by
  let x := delta C.theta G
  let e := delta C.theta D
  have hx : x∈Icc 0 t := ⟨hG,by dsimp [x,e] at *; linarith⟩
  have he : e∈Icc 0 t := ⟨hD,by dsimp [x,e] at *; linarith⟩
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  have he' : e∈Icc 0 frameCap := ⟨he.1,he.2.trans ht.2⟩
  have hxe : t-x=e := by dsimp [x,e]; linarith
  have hn0 := mul_nonneg hk (tilt_nonneg heta hx')
  have hp0 := tilt_nonneg heta he'
  have hw : ∀ i,0≤SoleEStress.weights (k*tilt eta x) k l c c 1 (tilt eta e) i := by
    intro i
    fin_cases i <;> simp [SoleEStress.weights,hn0,hk,hl,hc0,hp0]
  let Bnd : Vertex → ℝ := ![
    work (forces C ab k l c eta x e H) (C.point H),k*sigma R eta*Real.sin x,
    work (forces C ab k l c eta x e A) (C.point A),
    work (forces C ab k l c eta x e B) (C.point B),0,
    work (forces C ab k l c eta x e D) (C.point D),eWork C eta e]
  have hb : ∀ i,work (forces C ab k l c eta x e i) (C.point i)≤Bnd i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact G_work_le ab l c e hR hk heta hx' (hs G) (hc G)
    · exact le_rfl
    · exact le_rfl
    · show work (forces C ab k l c eta x e T) (C.point T)≤Bnd T
      rw [T_force]; simp [work,Bnd,T]
    · exact le_rfl
    · exact (E_work C ab k l c eta x).le
  have hsep := weighted_separation_le hw hf hb
  rw [value_eq_stress R k l c eta hab ht hx hn hcontact,hxe]
  change stress C ab R k l c eta x e≤0
  have hd : variableDemand C k l c eta x e=
      demand C (SoleEStress.weights (k*tilt eta x) k l c c 1 (tilt eta e)) :=
    original_demand C k l c eta
  dsimp only [stress]
  rw [hd]
  simp only [Bnd,Fin.sum_univ_seven,Matrix.cons_val] at hsep
  dsimp only [anchorWork]
  linarith

theorem concave {C : SignedCycle} (ab : Fin 4) {R k l c eta t : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap) (hk : k∈Icc (431/500:ℝ) 1)
    (heta : eta∈Icc (1/4:ℝ) (327/1000)) (ht : t∈Icc 0 frameCap)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained qCap)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hEy : 0≤(C.point E).y) :
    ConcaveOn ℝ (Icc 0 t) (value C ab R k l c eta t) := by
  apply ExceptionalContactCurvature.concave
    (transverse_residual (hs H) (hc H) (ha H)).le hk
    ⟨by linarith [heta.1],heta.2⟩
    (tilt_reserve hR hQU ⟨heta.1,by linarith [heta.2]⟩).le
    (contained_bounds (hs E) (hc E)).1.le hEy ht

end SquaresInCircles.Eight.ExceptionalContactStress
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalContactSupport
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open PositiveAngularEnvelope ExceptionalContactStress

def anchorSupport (C : SignedCycle) (ab : Fin 4) (R k l c eta x e : ℝ) : ℝ :=
  R*SoleEStress.anchorNorms C ab 2 0 3 0 (k*tilt eta x) k l c c 1 (tilt eta e)-
    SoleEStress.halfShift C ab 2 0 3 0 (k*tilt eta x) k l c c 1 (tilt eta e)

def increment (C : SignedCycle) (ab : Fin 4) (R k l c eta x e : ℝ) : ℝ :=
  SoleEStress.increment C ab 2 0 3 0 (k*tilt eta x) k l c c 1 (tilt eta e) R

def baseline (R k l c eta x e : ℝ) : ℝ :=
  (3/2)*(k*tilt eta x)+2*l+3*c+(1+tilt eta e)/2+k*(edgeWidth x+1/2)+
    edgeWidth e+tilt eta e-
    R*SoleEStress.zeroNorms (k*tilt eta x) k l c c 1 (tilt eta e)-
    k*sigma R eta*Real.sin x-sigma R eta*Real.sin e

theorem anchorWork_le {C : SignedCycle} {ab : Fin 4} (R k l c eta x e : ℝ)
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) :
    anchorWork C ab k l c eta x e≤anchorSupport C ab R k l c eta x e := by
  have hH := work_le_signed_support hR (hc H) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.H_nonneg]) (ExceptionalContactStress.forces C ab k l c eta x e H)
  have hA := work_le_signed_support hR (hc A) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.A_nonneg]) (ExceptionalContactStress.forces C ab k l c eta x e A)
  have hB := work_le_signed_support hR (hc B) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.B_nonpos]) (ExceptionalContactStress.forces C ab k l c eta x e B)
  have hD := work_le_signed_support hR (hc D) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.D_nonpos]) (ExceptionalContactStress.forces C ab k l c eta x e D)
  have hsum := SoleEStress.sum_bounds C hab (Or.inl rfl) (Or.inl rfl)
    (Or.inr rfl) (Or.inl rfl) (k*tilt eta x) k l c c 1 (tilt eta e) R
  simp only [SoleEStress.bound,Fin.sum_univ_seven,Matrix.cons_val] at hsum
  unfold anchorWork anchorSupport
  unfold ExceptionalContactStress.forces at hH hA hB hD ⊢
  unfold signedSupport at hsum
  linarith

theorem eWork_le {C : SignedCycle} {R eta e : ℝ}
    (hR : 0≤R) (heta : 0≤eta) (he : e∈Icc 0 frameCap)
    (hs : (C.point E).Sorted) (hc : (C.point E).Contained (R^2)) :
    eWork C eta e≤ sigma R eta*Real.sin e := by
  have hsin := (transport_trig he).2.2.1
  have hh := work_le_circleSupport hR hs hc (Real.sin e,Real.sin e*eta)
  rw [(scaled_primary_support (R := R) hsin heta).2] at hh
  dsimp [work,eWork,sigma] at *
  nlinarith

theorem variable_decomposition {C : SignedCycle} {ab : Fin 4} (R k l c eta x e : ℝ)
    (hab : ab=0 ∨ ab=2) (ha : ∀ i,|delta C.theta i|≤frameCap) :
    variableDemand C k l c eta x e-anchorSupport C ab R k l c eta x e-
      k*sigma R eta*Real.sin x-sigma R eta*Real.sin e=
        baseline R k l c eta x e+increment C ab R k l c eta x e := by
  rcases hab with rfl | rfl <;>
    simp only [variableDemand,anchorSupport,baseline,increment,SoleEStress.increment,
      SoleEStress.anchorNorms,SoleEStress.halfShift,SoleEStress.zeroNorms,
      ordinaryDE,ordinaryEH,ite_true,ite_false,show (3:Fin 4)≠2 by decide,
      show (2:Fin 4)≠0 by decide,width_eq (ha H),width_eq (ha A),width_eq (ha B),
      width_eq (ha T),width_eq (ha E),phi_zero,psi_zero,zero_add,add_zero,mul_zero,mul_one] <;> ring

theorem value_lower {C : SignedCycle} {ab : Fin 4} {R k l c eta t x : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (heta : 0≤eta)
    (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hcontact : Contact C) :
    baseline R k l c eta x (t-x)+increment C ab R k l c eta x (t-x)≤
      value C ab R k l c eta t x := by
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  have hanchor := anchorWork_le R k l c eta x (t-x) hab hR hc hn
  have hework := eWork_le hR heta he (hs E) (hc E)
  have hid := variable_decomposition R k l c eta x (t-x) hab ha
  rw [value_eq_stress R k l c eta hab ht hx hn hcontact]
  dsimp [stress]
  linarith

def contactScalar (R eta t : ℝ) : ℝ :=
  1+2*Real.cos t+(1+2*eta-R*Real.sqrt (1+eta^2))*Real.sin t

def atE (R k l c eta t : ℝ) : ℝ :=
  3*k+2*l+3*c+contactScalar R eta t-
    R*(pairNorm (tilt eta t) k 0+pairNorm k l 0+pairNorm l c 0+pairNorm 1 c 0)

def atG (R k l c eta t : ℝ) : ℝ :=
  3+2*l+3*c+k*contactScalar R eta t-
    R*(pairNorm 1 (k*tilt eta t) 0+pairNorm k l 0+pairNorm l c 0+pairNorm 1 c 0)

theorem baseline_at_E {R k l c eta t : ℝ} (ht : t∈Icc 0 frameCap) :
    baseline R k l c eta 0 t=atE R k l c eta t := by
  have hw0 : edgeWidth (0:ℝ)=1 := by simp [edgeWidth,pairWidth]
  simp [baseline,atE,contactScalar,ExceptionalContactStress.tilt,SoleEStress.zeroNorms,sigma,hw0,
    edgeWidth_positive_formula ht]
  ring

theorem baseline_at_G {R k l c eta t : ℝ} (ht : t∈Icc 0 frameCap) :
    baseline R k l c eta t 0=atG R k l c eta t := by
  have hw0 : edgeWidth (0:ℝ)=1 := by simp [edgeWidth,pairWidth]
  simp [baseline,atG,contactScalar,ExceptionalContactStress.tilt,SoleEStress.zeroNorms,sigma,hw0,
    edgeWidth_positive_formula ht]
  ring

theorem endpoint_difference (R k l c eta t : ℝ) :
    atG R k l c eta t-atE R k l c eta t=
      (1-k)*(3-contactScalar R eta t)+
        R*(pairNorm (tilt eta t) k 0-pairNorm 1 (k*tilt eta t) 0) := by
  dsimp [atG,atE]
  ring

theorem endpoint_norm_order {k p : ℝ} (hk : k∈Icc 0 1) (hp : 1≤p) :
    pairNorm 1 (k*p) 0≤pairNorm p k 0 := by
  have hk2 : 0≤1-k^2 := by nlinarith [hk.1,hk.2]
  have hp2 : 0≤p^2-1 := by nlinarith
  have hh := mul_nonneg hk2 hp2
  simp only [pairNorm,Real.sin_zero,mul_zero,add_zero]
  apply Real.sqrt_le_sqrt
  nlinarith

theorem E_le_G {R k l c eta t : ℝ} (hR : 0≤R) (hk : k∈Icc 0 1)
    (hp : 1≤tilt eta t) (hC : contactScalar R eta t≤3) :
    atE R k l c eta t≤atG R k l c eta t := by
  have hnorm := endpoint_norm_order hk hp
  have hfirst := mul_nonneg (sub_nonneg.mpr hk.2) (sub_nonneg.mpr hC)
  have hsecond := mul_nonneg hR (sub_nonneg.mpr hnorm)
  have hd := endpoint_difference R k l c eta t
  linarith

/-- For `k < 1` and contact scalar below `3`, the G endpoint strictly exceeds the E endpoint. The
sharp critical family can have a zero E endpoint, and its G endpoint is still strict. -/
theorem E_lt_G {R k l c eta t : ℝ} (hR : 0≤R) (hk : k∈Ico 0 1)
    (hp : 1≤tilt eta t) (hC : contactScalar R eta t<3) :
    atE R k l c eta t<atG R k l c eta t := by
  have hnorm := endpoint_norm_order ⟨hk.1,hk.2.le⟩ hp
  have hfirst := mul_pos (sub_pos.mpr hk.2) (sub_pos.mpr hC)
  have hsecond := mul_nonneg hR (sub_nonneg.mpr hnorm)
  have hd := endpoint_difference R k l c eta t
  linarith

end SquaresInCircles.Eight.ExceptionalContactSupport
end
end
end
