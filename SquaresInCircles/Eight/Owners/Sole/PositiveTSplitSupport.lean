module

public import SquaresInCircles.Eight.Owners.Sole.EndpointSupport
public import SquaresInCircles.Eight.Owners.Sole.TScalarModel

/-!
# Eight squares: the original weak witnesses imply the positive-T split inequality

G and E are bounded in their original signed
coordinates. H/A/B/D/T retain their actual work. In particular the
concave split is necessary before independent anchor supports are used.
The two physical T rows and the two weak AB owners stay explicit.
-/

section
/-!
## Splitting G and E at fixed coordinates with the T primary

The error of T and every signed ordinary angle stay fixed; only the two nonnegative primary
parameters of G and E vary. The work of T stays in the constant term (`constant`, `formula`), so
the concavity of the split (`high_concave`, `concave`) concerns the cycle itself, not a moved
configuration, and positivity at both endpoints gives positivity on the split
(`positive_of_endpoints`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SolePositiveTSplitModel
open Candidate SignedStress SoleResiduals SoleTScalarModel

def btOwner (td : Bool) : Fin 4 := if td then 2 else 3
def tdOwner (td : Bool) : Fin 4 := if td then 2 else 0
def deOwner (f : Family) : Fin 4 := if isDE f then 3 else 2
def ehOwner (f : Family) : Fin 4 := if isDE f then 0 else 1
def ePrimary (C : SignedCycle) (f : Family) : ℝ :=
  if isDE f then delta C.theta D else delta C.theta E
def tPrimary (C : SignedCycle) (td : Bool) : ℝ :=
  if td then delta C.theta T else delta C.theta B

def nWeight (f : Family) (t z x : ℝ) : ℝ :=
  k f t z*(Real.cos x+g f t*Real.sin x)
def mWeight (f : Family) (t z : ℝ) : ℝ :=
  c f t z*(Real.cos z+eta t*Real.sin z)
def btWeight (f : Family) (td : Bool) (t z : ℝ) : ℝ := if td then mWeight f t z else c f t z
def tdWeight (f : Family) (td : Bool) (t z : ℝ) : ℝ := if td then c f t z else mWeight f t z
def deWeight (f : Family) (t e : ℝ) : ℝ :=
  if tiltedE f then Real.cos e+epsilon f t*Real.sin e else 1
def ehWeight (f : Family) : ℝ := lambda f

def transverse (C : SignedCycle) : ℝ := SoleSplitModel.transverse C
def radialD (C : SignedCycle) : ℝ :=
  edgeWidth (delta C.theta D)-(C.point D).a*Real.cos (delta C.theta D)-
    |(C.point D).y| *Real.sin (delta C.theta D)
def radialH (C : SignedCycle) : ℝ :=
  edgeWidth (delta C.theta E)-(C.point H).a*Real.cos (delta C.theta E)-
    |(C.point H).y| *Real.sin (delta C.theta E)

def constant (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (t z : ℝ) : ℝ :=
  ell f t z*(edgeWidth (delta C.theta A)-C.edge A ab)+
    btWeight f td t z*(edgeWidth (delta C.theta B)-C.edge B (btOwner td))+
    tdWeight f td t z*(edgeWidth (delta C.theta T)-C.edge T (tdOwner td))-
    k f t z*(C.point A).a+
    if isDE f then lambda f*radialH C-(C.point D).a else -(C.point H).a

def eBound (C : SignedCycle) (f : Family) (R M t e : ℝ) : ℝ :=
  if tiltedE f then sigma R (epsilon f t)*Real.sin e
  else if isDE f then M*Real.sin e
  else (C.point E).a*Real.sin e+|(C.point E).y| *(1-Real.cos e)

def value (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (R M t z x : ℝ) : ℝ :=
  if tiltedE f then
    SoleFixedSplit.tilted (constant C ab f td t z) (transverse C) (radialD C)
      (k f t z) (g f t) (epsilon f t) (sigma R (g f t)) (sigma R (epsilon f t)) (t-z) x
  else if isDE f then
    SoleFixedSplit.high (constant C ab f td t z) (transverse C)
      (k f t z) (g f t) (sigma R (g f t)) M 0 (t-z) x
  else
    SoleFixedSplit.high (constant C ab f td t z+radialD C) (transverse C)
      (k f t z) (g f t) (sigma R (g f t)) (C.point E).a |(C.point E).y| (t-z) x

structure Bounds (f : Family) (t z : ℝ) : Prop where
  k_mem : k f t z∈Icc (431/500) (53/50)
  g_mem : g f t∈Icc (1/4) (7/20)
  tilted_epsilon : tiltedE f=true → epsilon f t∈Icc (1/4) (7/20)
  tilted_g : tiltedE f=true → g f t≤8/25
  tilted_length : tiltedE f=true → t-z≤7/20
  high_k : tiltedE f=false → 49/50≤k f t z
  high_g : tiltedE f=false → g f t≤67/200

theorem bounds {f : Family} {t z : ℝ} (ht : t∈domain f) (hz : z∈Icc 0 t) :
    Bounds f t z := by
  have hangle := angle ht
  have ht0 : 0≤t := hangle.1
  have ht7 : t≤7/10 := hangle.2
  have hsq : t^2≤(7/10)*t := by
    have hp := mul_nonneg ht0 (sub_nonneg.mpr ht7)
    nlinarith
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · cases f <;> norm_num [domain,left,right] at ht <;>
      dsimp [k,K] <;> constructor <;>
      linarith only [hz.1,hz.2,sq_nonneg t,sq_nonneg (t-1/5),hsq,ht.1,ht.2]
  · cases f <;> norm_num [domain,left,right] at ht <;>
      dsimp [g] <;> constructor <;> linarith only [ht.1,ht.2]
  · intro he
    cases f <;> norm_num [tiltedE] at he <;>
      norm_num [domain,left,right] at ht <;> dsimp [epsilon] <;>
      constructor <;> linarith only [sq_nonneg t,ht.1,ht.2,hsq]
  · intro he
    cases f <;> simp [tiltedE] at he <;> norm_num [g]
  · intro he
    cases f <;> norm_num [tiltedE] at he <;>
      norm_num [domain,left,right] at ht <;> linarith only [ht.2,hz.1]
  · intro he
    cases f <;> norm_num [tiltedE] at he <;>
      norm_num [domain,left,right] at ht <;> dsimp [k,K] <;>
      linarith only [ht.1,ht.2,hz.1]
  · intro he
    cases f <;> norm_num [tiltedE] at he <;>
      norm_num [domain,left,right] at ht <;> dsimp [g] <;>
      linarith only [ht.1,ht.2]

theorem high_harmonic {k w x : ℝ} (hk : k∈Icc (49/50:ℝ) (53/50))
    (hw : w∈Icc 0 frameCap) (hx : x∈Icc 0 w) :
    SoleFixedSplit.harmonic (-(87/200)*k) ((957/1000)*k)
      (-(1/2)) (183/200) w x≤-19/100 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hw
  suffices hh : SoleFixedSplit.harmonic (-(87/200)*k) ((957/1000)*k)
      (-(1/2)) (183/200) w x≤-(19/100) by linarith
  apply SoleFixedSplit.harmonic_endpoint_upper hw hx (by norm_num)
  · simp only [SoleFixedSplit.harmonic,Real.cos_zero,Real.sin_zero,
      sub_zero,mul_one,mul_zero,add_zero]
    linarith [hk.1]
  · have hcoef : -(87/200)*Real.cos w+(957/1000)*Real.sin w≤29/100 := by linarith
    have hm := mul_le_mul_of_nonneg_left hcoef (by linarith [hk.1] : 0≤k)
    simp only [SoleFixedSplit.harmonic,sub_self,Real.cos_zero,Real.sin_zero,
      mul_one,mul_zero,add_zero]
    nlinarith [hk.2]

theorem high_curvature {MH k g σG a b w x : ℝ}
    (hMH : -(13/200:ℝ)≤MH) (hk : k∈Icc (49/50:ℝ) (53/50))
    (hg : g∈Icc 0 (67/200:ℝ)) (hG : σG-1/2≤187/200)
    (ha : a≤283/200) (hb : 0≤b) (hw : w∈Icc 0 frameCap) (hx : x∈Icc 0 w) :
    -SoleFixedSplit.harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG)
      (1/2+b) (1/2-a) w x≤-19/100 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hw.2⟩
  have he : w-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hw.2,hx.1]⟩
  obtain ⟨hcx,hcx1,hsx,hsx1,hscx⟩ := transport_trig hx'
  obtain ⟨hce,hce1,hse,hse1,hsce⟩ := transport_trig he
  have hk0 : 0≤k := by linarith [hk.1]
  have hn : 0≤k*(Real.cos x+g*Real.sin x) :=
    mul_nonneg hk0 (by nlinarith [mul_nonneg hg.1 hsx])
  have hmH := mul_le_mul_of_nonneg_right hMH hn
  have hcoef : σG-1/2+(13/200)*g≤957/1000 := by linarith [hg.2]
  have hcoefG := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hk0 hsx)
  have hcoefE := mul_le_mul_of_nonneg_right ha hse
  have hminor := mul_nonneg hb (by linarith : 0≤Real.cos (w-x))
  have hmajor : -SoleFixedSplit.harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG)
      (1/2+b) (1/2-a) w x≤
      SoleFixedSplit.harmonic (-(87/200)*k) ((957/1000)*k) (-(1/2)) (183/200) w x := by
    dsimp [SoleFixedSplit.harmonic]
    nlinarith
  exact hmajor.trans (high_harmonic hk hw hx)

theorem high_concave {K MH k g σG a b w : ℝ}
    (hMH : -(13/200:ℝ)≤MH) (hk : k∈Icc (49/50:ℝ) (53/50))
    (hg : g∈Icc 0 (67/200:ℝ)) (hG : σG-1/2≤187/200)
    (ha : a≤283/200) (hb : 0≤b) (hw : w∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 w) (SoleFixedSplit.high K MH k g σG a b w) := by
  apply concave_of_deriv2
    (f' := SoleFixedSplit.harmonicDeriv (k*MH+k/2) (k*g*MH+k/2-k*σG)
      (1/2+b) (1/2-a) w)
    (f'' := fun x => -SoleFixedSplit.harmonic (k*MH+k/2) (k*g*MH+k/2-k*σG)
      (1/2+b) (1/2-a) w x)
  · intro x hx
    exact (SoleFixedSplit.harmonic_hasDerivAt _ _ _ _ _ _).const_add _
  · intro x hx
    exact SoleFixedSplit.harmonicDeriv_hasDerivAt _ _ _ _ _ _
  · intro x hx
    exact (high_curvature hMH hk hg hG ha hb hw hx).trans (by norm_num)

theorem concave {C : SignedCycle} (ab : Fin 4) {f : Family} (td : Bool) {R M t z : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap) (hM : M≤283/200)
    (ht : t∈domain f) (hz : z∈Icc 0 t)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained qCap)
    (ha : ∀ i,|delta C.theta i|≤frameCap) :
    ConcaveOn ℝ (Icc 0 (t-z)) (value C ab f td R M t z) := by
  have hb := bounds ht hz
  have hMH : -(13/200:ℝ)≤transverse C :=
    (transverse_residual (hs H) (hc H) (ha H)).le
  have hMD : -(83/200:ℝ)≤radialD C :=
    (radial_residual (hs D) (hc D) (ha D)).le
  have hG := (tilt_reserve hR hQU hb.g_mem).le
  have hw : t-z∈Icc 0 frameCap :=
    ⟨by linarith [hz.2],by linarith [hz.1,(angle ht).2]⟩
  by_cases he : tiltedE f=true
  · have hε := hb.tilted_epsilon he
    have hE := (tilt_reserve hR hQU hε).le
    unfold value
    simp only [he,ite_true]
    apply SoleFixedSplit.tilted_concave hMH hMD hb.k_mem.1
      ⟨by linarith [hb.g_mem.1],hb.tilted_g he⟩ (by linarith [hε.1]) hG
    · linarith [hε.2]
    · exact ⟨hw.1,hb.tilted_length he⟩
  · have he' : tiltedE f=false := Bool.eq_false_of_not_eq_true he
    have hk : k f t z∈Icc (49/50:ℝ) (53/50) := ⟨hb.high_k he',hb.k_mem.2⟩
    have hg : g f t∈Icc 0 (67/200:ℝ) := ⟨by linarith [hb.g_mem.1],hb.high_g he'⟩
    unfold value
    simp only [he',Bool.false_eq_true,ite_false]
    split_ifs
    · exact high_concave hMH hk hg hG hM (by norm_num) hw
    · exact high_concave hMH hk hg hG (contained_bounds (hs E) (hc E)).1.le
        (abs_nonneg _) hw

theorem formula {C : SignedCycle} (ab : Fin 4) {f : Family} (td : Bool) (R M : ℝ)
    {t z x : ℝ} (ht : t∈domain f) (hz : z∈Icc 0 t) (hx : x∈Icc 0 (t-z)) :
    value C ab f td R M t z x=
      constant C ab f td t z+nWeight f t z x*transverse C+
      k f t z*edgeWidth x-k f t z*sigma R (g f t)*Real.sin x+
      (if isDE f then 0 else deWeight f t (t-z-x)*radialD C)+
      edgeWidth (t-z-x)-eBound C f R M t (t-z-x) := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by linarith [hx.2,hz.1,(angle ht).2]⟩
  have he : t-z-x∈Icc 0 frameCap :=
    ⟨by linarith [hx.2],by linarith [hx.1,hz.1,(angle ht).2]⟩
  cases f <;>
    simp [value,eBound,deWeight,tiltedE,isDE,nWeight,
      SoleFixedSplit.tilted_formula,SoleFixedSplit.high_formula,
      edgeWidth_positive_formula hx',edgeWidth_positive_formula he] <;> ring

theorem positive_of_endpoints {C : SignedCycle} {ab : Fin 4} {f : Family} {td : Bool}
    {R M t z x : ℝ}
    (hconc : ConcaveOn ℝ (Icc 0 (t-z)) (value C ab f td R M t z))
    (hx : x∈Icc 0 (t-z))
    (h0 : 0<value C ab f td R M t z 0)
    (h1 : 0<value C ab f td R M t z (t-z)) : 0<value C ab f td R M t z x := by
  exact (lt_min h0 h1).trans_le (hconc.min_le_of_mem_Icc
    (left_mem_Icc.mpr (hx.1.trans hx.2)) (right_mem_Icc.mpr (hx.1.trans hx.2)) hx)

end SquaresInCircles.Eight.SolePositiveTSplitModel
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTSplitSupport
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks
open SoleTScalarModel SolePositiveTSplitModel

def forceData (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (t z x e : ℝ) :
    Vertex → Point :=
  SoleEStress.forces C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
    (nWeight f t z x) (k f t z) (ell f t z) (btWeight f td t z) (tdWeight f td t z)
    (deWeight f t e) (ehWeight f)

def variableDemand (C : SignedCycle) (f : Family) (td : Bool) (t z x e : ℝ) : ℝ :=
  nWeight f t z x*edgeWidth (delta C.theta H)+k f t z*edgeWidth x+
    ell f t z*edgeWidth (delta C.theta A)+btWeight f td t z*edgeWidth (delta C.theta B)+
    tdWeight f td t z*edgeWidth (delta C.theta T)+
    deWeight f t e*edgeWidth (if isDE f then e else delta C.theta D)+
    ehWeight f*edgeWidth (if isDE f then delta C.theta E else e)

def fixedWork (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (t z x e : ℝ) : ℝ :=
  work (forceData C ab f td t z x e H) (C.point H)+
    work (forceData C ab f td t z x e A) (C.point A)+
    work (forceData C ab f td t z x e B) (C.point B)+
    work (forceData C ab f td t z x e T) (C.point T)+
    work (forceData C ab f td t z x e D) (C.point D)

def stress (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool)
    (R M t z x e : ℝ) : ℝ :=
  variableDemand C f td t z x e-fixedWork C ab f td t z x e-
    k f t z*sigma R (g f t)*Real.sin x-eBound C f R M t e

theorem deOwner_cases (f : Family) : deOwner f=2 ∨ deOwner f=3 := by
  cases f <;> simp [deOwner,isDE]
theorem ehOwner_cases (f : Family) : ehOwner f=0 ∨ ehOwner f=1 := by
  cases f <;> simp [ehOwner,isDE]

theorem value_eq_stress {C : SignedCycle} {ab : Fin 4} {f : Family} (td : Bool)
    (R M : ℝ) {t z x : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈domain f)
    (hz : z∈Icc 0 t) (hx : x∈Icc 0 (t-z)) (hn : C.NormalAnchors) :
    SolePositiveTSplitModel.value C ab f td R M t z x=
      stress C ab f td R M t z x (t-z-x) := by
  have hH : |(C.point H).y|=(C.point H).y := abs_of_nonneg hn.H_nonneg
  have hD : |(C.point D).y|=-(C.point D).y := abs_of_nonpos hn.D_nonpos
  rw [SolePositiveTSplitModel.formula ab td R M ht hz hx]
  simp only [stress,variableDemand,fixedWork,constant,transverse,SoleSplitModel.transverse,
    radialD,radialH,hH,hD,forceData,SoleEStress.forces,force,work]
  rcases hab with rfl | rfl <;> cases f <;> cases td <;>
    simp [SoleEStress.weights,CoreEStress.owners,previous,source,target,word,add,scale,
      SignedCycle.edge,zeroProjection,quarterProjection,H,A,B,T,D,E,next,btOwner,tdOwner,
      deOwner,ehOwner,deWeight,ehWeight,lambda,tiltedE,isDE] <;> ring

theorem original_demand (C : SignedCycle) (f : Family) (td : Bool) (t z : ℝ) :
    variableDemand C f td t z (delta C.theta G) (ePrimary C f)=
      demand C (SoleEStress.weights (nWeight f t z (delta C.theta G)) (k f t z)
        (ell f t z) (btWeight f td t z) (tdWeight f td t z)
        (deWeight f t (ePrimary C f)) (ehWeight f)) := by
  rw [SoleEStress.demand_eq]
  cases f <;> simp [variableDemand,ePrimary,isDE]

theorem E_force (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (t z x : ℝ) :
    forceData C ab f td t z x (ePrimary C f) E=
      if isDE f then (Real.sin (ePrimary C f),lambda f-Real.cos (ePrimary C f))
      else (Real.sin (ePrimary C f),Real.cos (ePrimary C f)-deWeight f t (ePrimary C f)) := by
  unfold forceData
  rw [SoleEStress.force_E (deOwner_cases f) (ehOwner_cases f)]
  cases f <;> simp [deOwner,ehOwner,primaryDE,primaryEH,ePrimary,
    deWeight,ehWeight,lambda,isDE,tiltedE]

theorem E_work_le {C : SignedCycle} (ab : Fin 4) {f : Family} (td : Bool) {R M t z x : ℝ}
    (hR : 0≤R) (ht : t∈domain f) (hz : z∈Icc 0 t)
    (he : ePrimary C f∈Icc 0 (t-z))
    (hs : (C.point E).Sorted) (hc : (C.point E).Contained (R^2))
    (ha : (C.point E).a≤M) (hsign : isDE f=true → (C.point E).y≤0) :
    work (forceData C ab f td t z x (ePrimary C f) E) (C.point E)≤
      eBound C f R M t (ePrimary C f) := by
  have he' : ePrimary C f∈Icc 0 frameCap :=
    ⟨he.1,by linarith [he.2,hz.1,(angle ht).2]⟩
  have hsin := (transport_trig he').2.2.1
  have hcos := Real.cos_le_one (ePrimary C f)
  rw [E_force]
  by_cases hd : isDE f=true
  · have hy := hsign hd
    have htilt : tiltedE f=false := by cases f <;> simp_all [isDE,tiltedE]
    have hlam : lambda f=5/4 := by simp [lambda,hd]
    have hv : 0≤lambda f-Real.cos (ePrimary C f) := by rw [hlam]; linarith
    have hm := mul_nonpos_of_nonneg_of_nonpos hv hy
    have ha' := mul_le_mul_of_nonneg_right ha hsin
    simp [eBound,hd,htilt,work]
    nlinarith
  · have hd' : isDE f=false := Bool.eq_false_of_not_eq_true hd
    simp only [hd',Bool.false_eq_true,↓reduceIte]
    by_cases htilt : tiltedE f=true
    · have hε := (coefficient_positive ht hz).2.2.2.2.1
      have hw := work_le_circleSupport hR hs hc
        (Real.sin (ePrimary C f),-Real.sin (ePrimary C f)*epsilon f t)
      have hsupp := (scaled_primary_support (R := R) hsin hε).1
      rw [hsupp] at hw
      simp only [eBound,deWeight,htilt,↓reduceIte,work,sigma] at *
      linarith
    · have htilt' : tiltedE f=false := Bool.eq_false_of_not_eq_true htilt
      have hy := mul_le_mul_of_nonpos_left (neg_abs_le (C.point E).y)
        (show Real.cos (ePrimary C f)-1≤0 by linarith)
      simp only [eBound,deWeight,htilt',hd',Bool.false_eq_true,↓reduceIte,work]
      linarith

theorem G_work_le {C : SignedCycle} (ab : Fin 4) {f : Family} (td : Bool) {R t z e : ℝ}
    (hR : 0≤R) (ht : t∈domain f) (hz : z∈Icc 0 t)
    (hx : delta C.theta G∈Icc 0 (t-z))
    (hs : (C.point G).Sorted) (hc : (C.point G).Contained (R^2)) :
    work (forceData C ab f td t z (delta C.theta G) e G) (C.point G)≤
      k f t z*sigma R (g f t)*Real.sin (delta C.theta G) := by
  obtain ⟨hk,hl,hc0,hg,hε,hη⟩ := coefficient_positive ht hz
  have hx' : delta C.theta G∈Icc 0 frameCap :=
    ⟨hx.1,by linarith [hx.2,hz.1,(angle ht).2]⟩
  have hw := work_le_circleSupport hR hs hc (forceData C ab f td t z (delta C.theta G) e G)
  have hfd : forceData C ab f td t z (delta C.theta G) e G=
      SecondaryEStress.forces C ab (btOwner td) (tdOwner td)
        (tiltedWeight (k f t z) (g f t) (delta C.theta G)) (k f t z) (ell f t z)
        (btWeight f td t z) (tdWeight f td t z) G := by
    unfold forceData
    rw [SoleEStress.force_G]
    rfl
  have hsupp := positive_G_support (R := R) (ab := ab) (bt := btOwner td) (td := tdOwner td)
    (l := ell f t z) (b := btWeight f td t z) (t := tdWeight f td t z) hk.le hg hx'
  rw [hfd,hsupp] at hw
  rw [hfd]
  have hp : primarySupport R (k f t z) (g f t) (delta C.theta G)=
      k f t z*sigma R (g f t)*Real.sin (delta C.theta G) := by
    simp only [primarySupport,sigma]
    ring
  linarith

theorem positive_weights {f : Family} (td : Bool) {t z x e : ℝ}
    (ht : t∈domain f) (hz : z∈Icc 0 t) (hx : x∈Icc 0 (t-z)) (he : e∈Icc 0 (t-z)) :
    0<nWeight f t z x ∧ 0<k f t z ∧ 0<ell f t z ∧
      0<btWeight f td t z ∧ 0<tdWeight f td t z ∧ 0<deWeight f t e ∧ 0<ehWeight f := by
  obtain ⟨hk,hl,hc,hg,hε,hη⟩ := coefficient_positive ht hz
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by linarith [hx.2,hz.1,(angle ht).2]⟩
  have he' : e∈Icc 0 frameCap := ⟨he.1,by linarith [he.2,hz.1,(angle ht).2]⟩
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans (angle ht).2⟩
  have hn : 0<nWeight f t z x := by
    dsimp [nWeight]
    exact mul_pos hk (add_pos_of_pos_of_nonneg
      (by linarith [(transport_trig hx').1]) (mul_nonneg hg (transport_trig hx').2.2.1))
  have hm : 0< mWeight f t z := by
    dsimp [mWeight]
    exact mul_pos hc (add_pos_of_pos_of_nonneg
      (by linarith [(transport_trig hz').1]) (mul_nonneg hη (transport_trig hz').2.2.1))
  have hd : 0<deWeight f t e := by
    dsimp [deWeight]
    split_ifs
    · exact add_pos_of_pos_of_nonneg (by linarith [(transport_trig he').1])
        (mul_nonneg hε (transport_trig he').2.2.1)
    · norm_num
  refine ⟨hn,hk,hl,?_,?_,hd,?_⟩
  · dsimp [btWeight]; split_ifs <;> assumption
  · dsimp [tdWeight]; split_ifs <;> assumption
  · dsimp [ehWeight,lambda]; split_ifs <;> norm_num

/-- Necessity has no lower-radius assumption. The original seven weak
contacts and original signed points are the complete geometric input. -/
theorem necessary {C : SignedCycle} {ab : Fin 4} {f : Family} (td : Bool) {R M t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (ht : t∈domain f) (hz : z∈Icc 0 t)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C f)
    (htotal : delta C.theta G+ePrimary C f+z=t)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : (C.point E).a≤M)
    (hsign : isDE f=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i
      (CoreEStress.owners ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f) i)) :
    SolePositiveTSplitModel.value C ab f td R M t z (delta C.theta G)≤0 := by
  have hx : delta C.theta G∈Icc 0 (t-z) := ⟨hG,by linarith⟩
  have he : ePrimary C f∈Icc 0 (t-z) := ⟨hE,by linarith⟩
  have hxe : t-z-delta C.theta G=ePrimary C f := by linarith
  obtain ⟨hn0,hk,hl,hbt,htd,hde,heh⟩ := positive_weights td ht hz hx he
  have hw : ∀ i,0≤SoleEStress.weights (nWeight f t z (delta C.theta G)) (k f t z) (ell f t z)
      (btWeight f td t z) (tdWeight f td t z) (deWeight f t (ePrimary C f)) (ehWeight f) i := by
    intro i
    fin_cases i <;> simp [SoleEStress.weights,hn0.le,hk.le,hl.le,hbt.le,htd.le,hde.le,heh.le]
  have hbound : ∀ i,work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) i) (C.point i)≤
      (![work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) H) (C.point H),
        k f t z*sigma R (g f t)*Real.sin (delta C.theta G),
        work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) A) (C.point A),
        work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) B) (C.point B),
        work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) T) (C.point T),
        work (forceData C ab f td t z (delta C.theta G) (ePrimary C f) D) (C.point D),
        eBound C f R M t (ePrimary C f)] : Vertex → ℝ) i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact G_work_le ab td hR ht hz hx (hs G) (hc G)
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact E_work_le ab td hR ht hz he (hs E) (hc E) ha hsign
  have hsep := weighted_separation_le hw hf hbound
  rw [value_eq_stress td R M hab ht hz hx hn,hxe]
  have hd := original_demand C f td t z
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    add_zero] at hsep
  simp only [stress,fixedWork,hd]
  linarith

end SquaresInCircles.Eight.SolePositiveTSplitSupport
end
end
end
