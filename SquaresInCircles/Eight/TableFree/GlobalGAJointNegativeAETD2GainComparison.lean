module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2Stress
public import SquaresInCircles.Eight.TableFree.PositiveSecantGain

/-!
# Both original primary gains dominate the same secant gain

Uncompiled transcription of Section 2 of the joint-negative exclusion.
The DE3 comparison follows the sorted support through its intrinsic
diagonal/full-circle transition. Both branch derivatives are controlled
on the whole secant interval before they are joined.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.SecantCoordinate

def sortedNorm (c w : ℝ) : ℝ :=
  if w≤c then (w+c)/Real.sqrt 2 else Real.sqrt (w^2+c^2)
def sortedGain (c x : ℝ) : ℝ :=
  SecantNormCurvature.secant x-1+(13/12)*Real.tan x-
    R*(sortedNorm c (SecantNormCurvature.secant x)-sortedNorm c 1)

theorem diagonal_radius : GlobalGA.Secondary.diagonal+1/2=R/Real.sqrt 2 := by
  simp only [GlobalGA.Secondary.diagonal,diagonalCoordinate,sub_add_cancel]
  rw [Real.sqrt_div' qCap (by norm_num : (0:ℝ)≤2)]

theorem clipped_norm (c w : ℝ) :
    clippedSupport w c=R*sortedNorm c w-(w+c)/2 := by
  by_cases hw : w≤c
  · simp only [clippedSupport,sortedNorm,if_pos hw,diagonalSupport]
    have hd := diagonal_radius
    rw [eq_sub_of_add_eq hd]
    ring
  · simp [clippedSupport,sortedNorm,hw,fullSupport]

theorem sortedNorm_one (c : ℝ) : sortedNorm c 1=dNorm c := by
  simp [sortedNorm,dNorm]

theorem fullGain_monotone {k m x : ℝ} (hk : 0≤k) (hkm : k≤ m)
    (hx : x∈Icc 0 frameCap) : F k x≤F m x := by
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  have hh := PositiveSecantGain.norm_increment_antitone hk hkm
    (SecantNormCurvature.secant_ge_one hc)
  have hR := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg qCap)
  dsimp [F,SecantNormCurvature.normalized,SecantNormCurvature.supportNorm]
  have hkm2 : k^2+(SecantNormCurvature.secant x)^2=
      (SecantNormCurvature.secant x)^2+k^2 := by ring
  have hmm2 : m^2+(SecantNormCurvature.secant x)^2=
      (SecantNormCurvature.secant x)^2+m^2 := by ring
  rw [hkm2,hmm2,add_comm (k^2) 1,add_comm (m^2) 1]
  linarith

theorem sorted_increment {k c w : ℝ}
    (hk : 0<k) (hk1 : k≤1) (hkc : k≤c) (hw : 1≤w) :
    sortedNorm c w-sortedNorm c 1≤
      Real.sqrt (w^2+k^2)-Real.sqrt (1+k^2) := by
  have hc : 0<c := hk.trans_le hkc
  have h2 : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h22 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have rootD (a x : ℝ) (ha : 0<a) :
      HasDerivAt (fun x => Real.sqrt (x^2+a^2)) (x/Real.sqrt (x^2+a^2)) x := by
    have hn : x^2+a^2≠0 := by positivity
    refine (((hasDerivAt_id' x).fun_pow 2).add_const (a^2)).sqrt hn |>.congr_deriv ?_
    simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    field_simp
  have rootP (a x : ℝ) (ha : 0<a) : 0<Real.sqrt (x^2+a^2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hf : MonotoneOn (fun x => Real.sqrt (x^2+k^2)-(x+c)/Real.sqrt 2) (Icc 1 w) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact ((rootD k x hk).sub (((hasDerivAt_id x).add_const c).div_const _)).continuousAt.continuousWithinAt
    · intro x hx
      exact (rootD k x hk).sub (((hasDerivAt_id x).add_const c).div_const _)
    · intro x hx
      have hx0 : 0<x := by linarith [hx.1]
      have hN := rootP k x hk
      have hN2 := Real.sq_sqrt (show 0≤x^2+k^2 by positivity)
      have hupper : Real.sqrt (x^2+k^2)≤Real.sqrt 2*x := by
        have hxk : k≤x := hk1.trans hx.1.le
        have hk2 := pow_le_pow_left₀ hk.le hxk 2
        have hh := Real.sqrt_le_sqrt (show x^2+k^2≤2*x^2 by linarith)
        rwa [Real.sqrt_mul (by norm_num),Real.sqrt_sq hx0.le] at hh
      apply sub_nonneg.mpr
      exact (div_le_div_iff₀ h2 hN).2 (by simpa [mul_comm] using hupper)
  have hg : MonotoneOn (fun x => Real.sqrt (x^2+k^2)-Real.sqrt (x^2+c^2)) (Icc 1 w) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact ((rootD k x hk).sub (rootD c x hc)).continuousAt.continuousWithinAt
    · intro x hx
      exact (rootD k x hk).sub (rootD c x hc)
    · intro x hx
      apply sub_nonneg.mpr
      apply div_le_div_of_nonneg_left (by linarith [hx.1]) (rootP k x hk)
      apply Real.sqrt_le_sqrt
      linarith [pow_le_pow_left₀ hk.le hkc 2]
  have hmatch (x : ℝ) (hx : x∈Icc 1 w) (he : x-c=0) :
      Real.sqrt (x^2+k^2)-(x+c)/Real.sqrt 2=
        Real.sqrt (x^2+k^2)-Real.sqrt (x^2+c^2) := by
    have hxc : x=c := by linarith
    rw [hxc]
    have hN2 := Real.sq_sqrt (show 0≤c^2+c^2 by positivity)
    have heq : Real.sqrt (c^2+c^2)=(c+c)/Real.sqrt 2 := by
      apply (eq_div_iff h2.ne').2
      rw [show c^2+c^2=2*c^2 by ring,Real.sqrt_mul (by norm_num),Real.sqrt_sq hc.le,mul_comm,
        ← mul_assoc,← sq,h22]
      ring
    rw [heq]
  have hmono := monotone_continuous_switch (e:=fun x => x-c)
    (by fun_prop) hf hg hmatch
  have hh := hmono ⟨le_rfl,hw⟩ ⟨hw,le_rfl⟩ hw
  beta_reduce at hh
  have hid (x : ℝ) :
      (if x-c≤0 then Real.sqrt (x^2+k^2)-(x+c)/Real.sqrt 2
        else Real.sqrt (x^2+k^2)-Real.sqrt (x^2+c^2))=
          Real.sqrt (x^2+k^2)-sortedNorm c x := by
    simp only [sortedNorm,sub_nonpos]
    split_ifs <;> rfl
  rw [hid,hid] at hh
  norm_num only [one_pow] at hh
  linarith

theorem sortedGain_lower {k c x : ℝ} (hk : 0<k) (hk1 : k≤1) (hkc : k≤c)
    (hx : x∈Icc 0 frameCap) : F k x≤ sortedGain c x := by
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  have hh := sorted_increment hk hk1 hkc (SecantNormCurvature.secant_ge_one hc)
  have hR := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg qCap)
  dsimp [F,sortedGain,SecantNormCurvature.normalized,SecantNormCurvature.supportNorm]
  have hid : k^2+(SecantNormCurvature.secant x)^2=
      (SecantNormCurvature.secant x)^2+k^2 := by ring
  rw [hid,add_comm (k^2) 1]
  linarith

namespace Source

def aGain (atG : Bool) (k c r z : ℝ) : ℝ := F (if atG then k else tilted c z) r
def eGain (atH : Bool) (k c s : ℝ) : ℝ := if atH then F k s else sortedGain c s

theorem baseline_identity (atG atH : Bool) (k c z : ℝ) {r s : ℝ}
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hz : z∈Icc 0 frameCap) :
    exactBaseline atG atH k c r s z=baseline k c z+aGain atG k c r z+eGain atH k c s := by
  have hrw := NegativeAPositiveTD.secant_width_identity (l:=1) hr
  have hsw := NegativeAPositiveTD.secant_width_identity (l:=1) hs
  dsimp [NegativeAPositiveTD.secant] at hrw hsw
  have hw := edgeWidth_positive_formula hz
  have swap (u v : ℝ) : Real.sqrt (u^2+v^2)=Real.sqrt (v^2+u^2) := by congr 1; ring
  cases atG <;> cases atH <;>
    simp only [exactBaseline,baseline,aGain,eGain,lambdaG,lambdaB,lambdaH,lambdaD,
      Bool.false_eq_true,↓reduceIte,clipped_norm,sortedNorm_one,fullSupport,
      F,sortedGain,SecantNormCurvature.normalized,SecantNormCurvature.supportNorm,
      one_pow,hw]
  all_goals
    simp only [add_comm (k^2) ((sec r)^2),add_comm (k^2) ((sec s)^2),
      add_comm (k^2) 1,add_comm ((tilted c z)^2) 1]
    dsimp [sec,SecantNormCurvature.secant,tilted]
    nlinarith only [hrw,hsw]

theorem common_baseline_lower {k c r s z : ℝ} (atG atH : Bool)
    (hk : 0<k) (hk1 : k≤1) (hkc : k≤c) (hkm : k≤tilted c z)
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) :
    baseline k c z+F k r+F k s≤exactBaseline atG atH k c r s z := by
  have ha : F k r≤aGain atG k c r z := by
    cases atG
    · exact fullGain_monotone hk.le hkm hr
    · exact le_rfl
  have he : F k s≤eGain atH k c s := by
    cases atH
    · exact sortedGain_lower hk hk1 hkc hs
    · exact le_rfl
  rw [baseline_identity atG atH k c z hr hs hz]
  linarith

end Source
end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2
