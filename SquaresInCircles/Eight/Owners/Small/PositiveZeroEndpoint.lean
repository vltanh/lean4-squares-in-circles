module

public import SquaresInCircles.Eight.Owners.Hard.OuterGeometry
public import SquaresInCircles.Eight.Owners.Small.HardEnvelope
public import SquaresInCircles.Eight.Words.Zero.SignedCharge

/-!
# Eight squares: no transverse-zero endpoint on the positive small side

The candidate endpoint G may have a larger frame than the original G; only its own GA angle is
bounded. The endpoint budget and the TD charge use the points and frames of H, D, E, T of the
cycle, so no spread bound for the candidate G is needed. The new point A may lie on the circle of
`q` and keeps the tangent of the original A, and B is used unchanged. A contained G with zero
tangent spends more than `7/1000` beyond the affine outer charge on H
(`zero_outer_strict_charge`), which excludes the endpoint
(`HardOuterGeometry.small_positive_G_zero_impossible`,
`HardInput.small_positive_G_zero_impossible`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate EndpointRotationPenalty EndpointBudgetScalars

namespace SmallPositiveZeroEndpoint

/-- On `[1/10, 2/5]` the Taylor minorant exceeds `7/1000`: its chord remainder factors into the two
endpoint distances times a positive cubic. -/
theorem trigonometric_reserve {h : ℝ} (hh : h∈Icc (1/10 : ℝ) (2/5)) :
    7/1000<EndpointRotationPenalty.charge*h-(183/200)*Real.sin h-(1-Real.cos h)/2 := by
  have hh0 : 0≤h := by linarith [hh.1]
  have hs := sin_upper_five hh0
  have hc := Real.one_sub_sq_div_two_le_cos (x := h)
  have hcoef : 0≤279037/1600000-(120719/800000)*h+
      (61/16000)*h^2+(61/8000)*h^3 := by
    have h2 := mul_le_mul_of_nonneg_left hh.2 hh0
    linarith [hh.2,pow_nonneg hh0 3,sq_nonneg h]
  have hprod : 0≤(h-1/10)*(2/5-h)*
      (279037/1600000-(120719/800000)*h+(61/16000)*h^2+(61/8000)*h^3) :=
    mul_nonneg (mul_nonneg (by linarith [hh.1]) (by linarith [hh.2])) hcoef
  have hid : EndpointRotationPenalty.charge*h-(183/200)*(h-h^3/6+h^5/120)-h^2/4=
      279037/40000000+(47718751/3920000000)*h+
        (h-1/10)*(2/5-h)*
          (279037/1600000-(120719/800000)*h+(61/16000)*h^2+(61/8000)*h^3) := by
    simp only [EndpointRotationPenalty.charge]
    ring
  have hlower : 7/1000<EndpointRotationPenalty.charge*h-(183/200)*(h-h^3/6+h^5/120)-h^2/4 := by
    rw [hid]
    linarith [hh.1]
  linarith

/-- A contained G with zero tangent spends more than `7/1000` beyond the affine outer charge on H;
sorting at H excludes the whole interval `h ≤ 1/10`. -/
theorem zero_outer_strict_charge {q h : ℝ} {H G : SignedPoint}
    (hq : q≤qCap) (hGc : G.Contained q) (hGy : G.y=0)
    (hHy : H.y<9/10) (hh : h∈Ioc 0 (2/5 : ℝ))
    (hHG : zeroFeasible H G h 0) :
    1+7/1000<H.y+EndpointRotationPenalty.charge*h := by
  have hi : h∈Icc 0 frameCap := by
    dsimp [frameCap]
    exact ⟨hh.1.le,by linarith [hh.2]⟩
  have htr := transport_trig hi
  have hGa : G.a<283/200 := by
    have hc : G.circle≤qCap := hGc.trans hq
    simp only [SignedPoint.circle,hGy,abs_zero] at hc
    dsimp [qCap] at hc
    by_contra! hle
    have h2 := pow_le_pow_left₀ (by norm_num) (show (283/200:ℝ)+1/2≤G.a+1/2 by linarith) 2
    linarith
  have hmul := mul_le_mul_of_nonneg_right hGa.le htr.2.2.1
  have hHlower : 1/2+Real.cos h/2-(183/200)*Real.sin h≤H.y := by
    have hf := hHG
    rw [zeroFeasible,edgeWidth_positive_formula hi] at hf
    simp only [zeroProjection,Matrix.cons_val_zero,hGy,zero_mul,sub_zero] at hf
    linarith
  have hh10 : 1/10<h := by
    by_contra! hsmall
    have hs := Real.sin_le hh.1.le
    have hc := Real.one_sub_sq_div_two_le_cos (x := h)
    have hsq := pow_le_pow_left₀ hh.1.le hsmall 2
    linarith
  have hr := trigonometric_reserve ⟨hh10.le,hh.2⟩
  linarith

theorem endpoint_constant_lower : 415/1000<S0 := by
  have hr := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
  have hs := Real.sqrt_nonneg (qCap-1)
  dsimp [S0,qCap] at *
  nlinarith

end SmallPositiveZeroEndpoint

namespace SignedCycle

/-- The transverse-zero alternative of the small-side construction of a positive HG0 is
impossible, by the cycle itself: `P` and `Q` are the candidate points of A and G, and `θ` the
candidate frame of G. The statement assumes no lift to the radius of the cycle and no spread bound
for `Q`. -/
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
  obtain ⟨z,hz_def⟩ : ∃ z, z=θ-I.cycle.theta A := ⟨_,rfl⟩
  obtain ⟨v,hv_def⟩ : ∃ v, v=I.cycle.theta A-I.cycle.theta T := ⟨_,rfl⟩
  obtain ⟨h,hh_def⟩ : ∃ h, h=θ-I.cycle.theta H := ⟨_,rfl⟩
  have hz : z∈Icc 0 frameCap := by
    rw [hz_def]
    exact ⟨by linarith,hθA⟩
  have hv : v∈Icc 0 frameCap := by
    rw [hv_def]
    refine ⟨sub_nonneg.mpr hTA,?_⟩
    exact (le_abs_self _).trans (I.necessary.spread A T)
  have hPa : 1/2<P.a := SignedPoint.primary_gt_half hPs hPc
  have hAy0 : 0≤(I.cycle.point A).y := by linarith [hsmall.1]
  have hAc : (P.a+1/2)^2+((I.cycle.point A).y+1/2)^2≤qCap := by
    have hh : P.circle≤qCap := hPq.trans hq
    simp only [SignedPoint.circle,hPy,abs_of_nonneg hAy0] at hh
    exact hh
  have hBc : ((I.cycle.point B).a+1/2)^2+(3/2-(I.cycle.point A).y)^2≤qCap := by
    have hh : (I.cycle.point B).circle≤qCap := (I.necessary.contained B).trans hq
    have hy : -(I.cycle.point B).y+1/2=3/2-(I.cycle.point A).y := by linarith
    simp only [SignedPoint.circle,abs_of_nonpos I.anchors_normal.B_nonpos,hy] at hh
    exact hh
  have hGA' : 1/2≤(P.a-1/2)*Real.cos z-
      ((I.cycle.point A).y+1/2)*Real.sin z := by
    have hf := hGA
    rw [quarterFeasible,show I.cycle.theta A-θ=-z by rw [hz_def]; ring,
      edgeWidth_negative_formula hz] at hf
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hQy,hPy] at hf
    linarith
  have hBT' : (I.cycle.point T).y+1/2≤
      ((I.cycle.point B).a-1/2)*Real.cos v-
        (3/2-(I.cycle.point A).y)*Real.sin v := by
    have hf : edgeWidth (I.cycle.theta T-I.cycle.theta B)≤
        quarterProjection (I.cycle.point B) (I.cycle.point T)
          (I.cycle.theta T-I.cycle.theta B) 2 := by
      simpa [Feasible,slack,edge,word,delta,next,B,T,sub_nonneg] using I.BT_hard
    have hδ : I.cycle.theta T-I.cycle.theta B= -v := by rw [hv_def,←hAB]; ring
    rw [hδ,edgeWidth_negative_formula hv] at hf
    simp only [quarterProjection,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,
      Real.cos_neg,Real.sin_neg] at hf
    have hBy : (I.cycle.point B).y=(I.cycle.point A).y-1 := by linarith
    rw [hBy] at hf
    linarith
  have hzmax := SmallHardEnvelope.hard_angle_upper hsmall hPa hAc hz hGA'
  have hd : (I.cycle.point A).y-67/200∈Icc 0 (33/200 : ℝ) := by
    constructor <;> linarith [hsmall.1,hsmall.2]
  have hhi : h∈Ioc 0 (2/5 : ℝ) := by
    have hzbound := (SmallHardEnvelope.majorant_bounds hd).1.2
    rw [hh_def]
    rw [hz_def] at hzmax
    constructor <;> linarith
  have hHy : (I.cycle.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hHcharge := SmallPositiveZeroEndpoint.zero_outer_strict_charge
    hq hQq hQy hHy hhi (by rw [hh_def]; exact hHG)
  have hmiddle := SmallHardEnvelope.actual_middle_bound hsmall hPa hAc hBc
    hz hv hTy hGA' hBT'
  have hTDcharge := (signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs).2
  have hbudget := I.endpoint_bound hq
  have hS := SmallPositiveZeroEndpoint.endpoint_constant_lower
  subst hz_def hv_def hh_def
  simp only [EndpointRotationPenalty.charge,epsilon] at hHcharge hmiddle hTDcharge hbudget
  linarith

/-- The same for a hard input, whose strict budget comes from the witnesses of H, D, E. -/
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
end SquaresInCircles.Eight
