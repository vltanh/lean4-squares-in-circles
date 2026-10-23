module

public import SquaresInCircles.Eight.TableFree.SmallHardEnvelope
public import SquaresInCircles.Eight.TableFree.HardOuterGeometry

/-!
# The positive small-side transverse-zero endpoint is impossible

Uncompiled source draft.  The candidate G endpoint may have an enlarged
frame compared with the source G.  Only its own GA angle is bounded.
The endpoint budget and TD charge use the unchanged source H/D/E/T
points and frames, so no unproved spread for the candidate G is needed.
The new A point may be on its actual q-circle; its original tangent is
retained and the source B point is used without change.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate EndpointRotationPenalty EndpointBudgetScalars

namespace SmallPositiveZeroEndpoint

/-- The Taylor minorant is above .007 on one complete interval.  Its
chord remainder factors into the two endpoint distances times a positive
cubic, giving the reserve without a numerical or interval oracle. -/
theorem trigonometric_reserve {h : ℝ} (hh : h∈Icc (1/10 : ℝ) (2/5)) :
    7/1000<charge*h-(183/200)*Real.sin h-(1-Real.cos h)/2 := by
  have hh0 : 0≤h := by linarith [hh.1]
  have hs := sin_upper_five hh0
  have hc := Real.one_sub_sq_div_two_le_cos h
  have hcoef : 0≤279037/1600000-(120719/800000)*h+
      (61/16000)*h^2+(61/8000)*h^3 := by
    nlinarith [hh.2,pow_nonneg hh0 3,sq_nonneg h]
  have hprod : 0≤(h-1/10)*(2/5-h)*
      (279037/1600000-(120719/800000)*h+(61/16000)*h^2+(61/8000)*h^3) :=
    mul_nonneg (mul_nonneg (by linarith [hh.1]) (by linarith [hh.2])) hcoef
  have hid : charge*h-(183/200)*(h-h^3/6+h^5/120)-h^2/4=
      279037/40000000+(47718751/3920000000)*h+
        (h-1/10)*(2/5-h)*
          (279037/1600000-(120719/800000)*h+(61/16000)*h^2+(61/8000)*h^3) := by
    dsimp [charge]
    ring
  have hlower : 7/1000<charge*h-(183/200)*(h-h^3/6+h^5/120)-h^2/4 := by
    rw [hid]
    linarith [hh.1]
  linarith

/-- A contained zero-tangent G spends more than .007 beyond the affine
outer charge on H.  Sorting at H excludes the entire interval h≤.1. -/
theorem zero_outer_strict_charge {q h : ℝ} {H G : SignedPoint}
    (hq : q≤qCap) (hGc : G.Contained q) (hGy : G.y=0)
    (hHy : H.y<9/10) (hh : h∈Ioc 0 (2/5 : ℝ))
    (hHG : zeroFeasible H G h 0) :
    1+7/1000<H.y+charge*h := by
  have hi : h∈Icc 0 frameCap := by
    dsimp [frameCap]
    exact ⟨hh.1.le,by linarith [hh.2]⟩
  have htr := transport_trig hi
  have hGa : G.a<283/200 := by
    have hc := hGc.trans hq
    rw [SignedPoint.Contained,SignedPoint.circle,hGy] at hc
    norm_num at hc
    dsimp [qCap] at hc
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hGa.le htr.2.2.1
  have hHlower : 1/2+Real.cos h/2-(183/200)*Real.sin h≤H.y := by
    have hf := hHG
    rw [zeroFeasible,edgeWidth_positive_formula hi] at hf
    simp only [zeroProjection,Matrix.cons_val_zero,hGy,zero_mul,sub_zero] at hf
    nlinarith
  have hh10 : 1/10<h := by
    by_contra! hsmall
    have hs := Real.sin_le hh.1.le
    have hc := Real.one_sub_sq_div_two_le_cos h
    have hsq := pow_le_pow_left₀ hh.1.le hsmall 2
    nlinarith
  have hr := trigonometric_reserve ⟨hh10.le,hh.2⟩
  linarith

theorem endpoint_constant_lower : 415/1000<S0 := by
  have hr := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
  have hs := Real.sqrt_nonneg (qCap-1)
  dsimp [S0,qCap] at *
  nlinarith

end SmallPositiveZeroEndpoint

namespace SignedCycle

/-- The transverse-zero alternative in the positive HG0 small-side
boundary construction is excluded using the unchanged source cycle.
P and Q are its actual candidate A/G points, and theta is its candidate
G frame.  Neither a source-radius lift nor total spread for Q is hidden
in the statement. -/
theorem HardOuterGeometry.small_positive_G_zero_impossible {q θ : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hTy : 0≤(I.cycle.point T).y)
    (P Q : SignedPoint) (hPs : P.Sorted) (hPc : P.AvoidsCore)
    (hPq : P.Contained q) (hPy : P.y=(I.cycle.point A).y)
    (hQq : Q.Contained q) (hQy : Q.y=0)
    (hHθ : I.cycle.theta H<θ) (hθA : θ-I.cycle.theta A≤frameCap)
    (hHG : zeroFeasible (I.cycle.point H) Q (θ-I.cycle.theta H) 0)
    (hGA : quarterFeasible Q P (I.cycle.theta A-θ) 0) : False := by
  let z := θ-I.cycle.theta A
  let v := I.cycle.theta A-I.cycle.theta T
  let h := θ-I.cycle.theta H
  have hz : z∈Icc 0 frameCap := by
    dsimp [z]
    exact ⟨by linarith,hθA⟩
  have hv : v∈Icc 0 frameCap := by
    refine ⟨sub_nonneg.mpr hTA,?_⟩
    exact (le_abs_self v).trans (I.necessary.spread A T)
  have hPa : 1/2<P.a := SignedPoint.primary_gt_half hPs hPc
  have hPy0 : 0≤P.y := by rw [hPy]; linarith [hsmall.1]
  have hAc : (P.a+1/2)^2+((I.cycle.point A).y+1/2)^2≤qCap := by
    have hh := hPq.trans hq
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hPy0,hPy] using hh
  have hBc : ((I.cycle.point B).a+1/2)^2+(3/2-(I.cycle.point A).y)^2≤qCap := by
    have hh := (I.necessary.contained B).trans hq
    have hy : -(I.cycle.point B).y+1/2=3/2-(I.cycle.point A).y := by linarith
    simpa [SignedPoint.Contained,SignedPoint.circle,
      abs_of_nonpos I.anchors_normal.B_nonpos,hy] using hh
  have hGA' : 1/2≤(P.a-1/2)*Real.cos z-
      ((I.cycle.point A).y+1/2)*Real.sin z := by
    have hf : quarterFeasible Q P (-z) 0 := by
      simpa [z,neg_sub] using hGA
    rw [quarterFeasible,edgeWidth_negative_formula hz] at hf
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hQy,hPy] at hf
    nlinarith
  have hBT' : (I.cycle.point T).y+1/2≤
      ((I.cycle.point B).a-1/2)*Real.cos v-
        (3/2-(I.cycle.point A).y)*Real.sin v := by
    have hf : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
      have hδ : I.cycle.theta T-I.cycle.theta B= -v := by dsimp [v]; rw [←hAB]; ring
      simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,hδ]
        using I.BT_hard
    rw [quarterFeasible,edgeWidth_negative_formula hv] at hf
    simp only [quarterProjection,Matrix.cons_val_two,Real.cos_neg,Real.sin_neg] at hf
    have hBy : (I.cycle.point B).y=(I.cycle.point A).y-1 := by linarith
    rw [hBy] at hf
    nlinarith
  have hzmax := SmallHardEnvelope.hard_angle_upper hsmall hPa hAc hz hGA'
  have hd : (I.cycle.point A).y-67/200∈Icc 0 (33/200 : ℝ) := by
    constructor <;> linarith [hsmall.1,hsmall.2]
  have hhi : h∈Ioc 0 (2/5 : ℝ) := by
    have hzbound := (SmallHardEnvelope.majorant_bounds hd).1.2
    dsimp [h,z] at *
    constructor <;> linarith
  have hHy : (I.cycle.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hHcharge := SmallPositiveZeroEndpoint.zero_outer_strict_charge
    hq hQq hQy hHy hhi hHG
  have hmiddle := SmallHardEnvelope.actual_middle_bound hsmall hPa hAc hBc
    hz hv hTy hGA' hBT'
  have hTDcharge := (signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs).2
  have hbudget := I.endpoint_bound hq
  have hS := SmallPositiveZeroEndpoint.endpoint_constant_lower
  dsimp [h,z,v,charge,epsilon] at *
  linarith

/-- The source-facing statement obtains its strict budget from the
unchanged original H/D/E witnesses. -/
theorem HardInput.small_positive_G_zero_impossible {q θ : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hTy : 0≤(I.cycle.point T).y)
    (P Q : SignedPoint) (hPs : P.Sorted) (hPc : P.AvoidsCore)
    (hPq : P.Contained q) (hPy : P.y=(I.cycle.point A).y)
    (hQq : Q.Contained q) (hQy : Q.y=0)
    (hHθ : I.cycle.theta H<θ) (hθA : θ-I.cycle.theta A≤frameCap)
    (hHG : zeroFeasible (I.cycle.point H) Q (θ-I.cycle.theta H) 0)
    (hGA : quarterFeasible Q P (I.cycle.theta A-θ) 0) : False :=
  I.outerGeometry.small_positive_G_zero_impossible hq hAB hnorm hsmall
    hTA hAH hTy P Q hPs hPc hPq hPy hQq hQy hHθ hθA hHG hGA

end SignedCycle
end SquaresInCircles.Eight.TableFree
