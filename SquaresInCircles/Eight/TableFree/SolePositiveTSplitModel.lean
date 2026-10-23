module

public import SquaresInCircles.Eight.TableFree.SoleTScalarModel
public import SquaresInCircles.Eight.TableFree.SoleSplitModel

/-!
# Fixed-coordinate G/E splitting with the T primary retained

Uncompiled source. The actual T error and all ordinary signed angles
stay fixed. Only the two nonnegative G/E primary parameters vary. The
original T work is kept in the constant term, so no claim about a moved
endpoint configuration is involved in this concavity argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SolePositiveTSplitModel
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
    |(C.point D).y|*Real.sin (delta C.theta D)
def radialH (C : SignedCycle) : ℝ :=
  edgeWidth (delta C.theta E)-(C.point H).a*Real.cos (delta C.theta E)-
    |(C.point H).y|*Real.sin (delta C.theta E)

def constant (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (t z : ℝ) : ℝ :=
  ell f t z*(edgeWidth (delta C.theta A)-C.edge A ab)+
    btWeight f td t z*(edgeWidth (delta C.theta B)-C.edge B (btOwner td))+
    tdWeight f td t z*(edgeWidth (delta C.theta T)-C.edge T (tdOwner td))-
    k f t z*(C.point A).a+
    if isDE f then lambda f*radialH C-(C.point D).a else -(C.point H).a

def eBound (C : SignedCycle) (f : Family) (R M t e : ℝ) : ℝ :=
  if tiltedE f then sigma R (epsilon f t)*Real.sin e
  else if isDE f then M*Real.sin e
  else (C.point E).a*Real.sin e+|(C.point E).y|*(1-Real.cos e)

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
      nlinarith [hz.1,hz.2,sq_nonneg t,sq_nonneg (t-1/5)]
  · cases f <;> norm_num [domain,left,right] at ht <;>
      dsimp [g] <;> constructor <;> linarith [ht.1,ht.2]
  · intro he
    cases f <;> norm_num [tiltedE] at he <;>
      norm_num [domain,left,right] at ht <;> dsimp [epsilon] <;>
      constructor <;> nlinarith [sq_nonneg t,ht.1,ht.2]
  · intro he
    cases f <;> norm_num [tiltedE,g] at he ⊢
  · intro he
    cases f <;> norm_num [tiltedE] at he <;>
      norm_num [domain,left,right] at ht <;> linarith [ht.2,hz.1]
  · intro he
    cases f <;> norm_num [tiltedE] at he <;>
      norm_num [domain,left,right] at ht <;> dsimp [k,K] <;>
      linarith [ht.1,ht.2,hz.1]
  · intro he
    cases f <;> norm_num [tiltedE] at he <;>
      norm_num [domain,left,right] at ht <;> dsimp [g] <;>
      linarith [ht.1,ht.2]

theorem high_harmonic {k w x : ℝ} (hk : k∈Icc (49/50:ℝ) (53/50))
    (hw : w∈Icc 0 frameCap) (hx : x∈Icc 0 w) :
    SoleFixedSplit.harmonic (-(87/200)*k) ((957/1000)*k)
      (-(1/2)) (183/200) w x≤-19/100 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hw
  apply SoleFixedSplit.harmonic_endpoint_upper hw hx (by norm_num)
  · simp only [SoleFixedSplit.harmonic,Real.cos_zero,Real.sin_zero,
      sub_zero,mul_one,mul_zero,add_zero,zero_add]
    nlinarith [hk.1]
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
    simp only [value,he,if_true]
    apply SoleFixedSplit.tilted_concave hMH hMD hb.k_mem.1
      ⟨by linarith [hb.g_mem.1],hb.tilted_g he⟩ (by linarith [hε.1]) hG
    · linarith [hε.2]
    · exact ⟨hw.1,hb.tilted_length he⟩
  · have he' : tiltedE f=false := Bool.eq_false_of_not_eq_true he
    have hk : k f t z∈Icc (49/50:ℝ) (53/50) := ⟨hb.high_k he',hb.k_mem.2⟩
    have hg : g f t∈Icc 0 (67/200:ℝ) := ⟨by linarith [hb.g_mem.1],hb.high_g he'⟩
    simp only [value,he',if_false]
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

end SquaresInCircles.Eight.TableFree.SolePositiveTSplitModel
