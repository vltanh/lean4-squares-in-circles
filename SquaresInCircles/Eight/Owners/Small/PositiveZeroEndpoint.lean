module

public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein
public import SquaresInCircles.Eight.Owners.Endpoint.RotationPenalty
public import SquaresInCircles.Eight.Owners.Hard.OuterOrder
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

section
/-!
## A continuous small-middle hard envelope without inverse-angle branches

Three explicit quadratic majorants bound the
left hard angle and the two circle radii on the entire tangent interval
[.335,.5].  Their square and Taylor reserves are exact polynomial
identities.  The opposite hard contact contributes at most 1/2401 beyond
its zero-angle value.  The resulting bound is strictly below .419.

These are bounds on actual circle and contact inequalities.  No intrinsic
root, numerical maximizer, angular mesh or endpoint hypothesis is an input.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SmallHardEnvelope
open EndpointRotationPenalty

def angleUpper (d : ℝ) : ℝ := 39/125-(18/25)*d+d^2/5
def leftRadiusUpper (d : ℝ) : ℝ := 897/500-(93/200)*d-(67/200)*d^2
def rightRadiusUpper (d : ℝ) : ℝ := 8/5+(729/1000)*d-(39/100)*d^2

theorem majorant_bounds {d : ℝ} (hd : d∈Icc 0 (33/200 : ℝ)) :
    angleUpper d∈Icc (19/100 : ℝ) (39/125) ∧
      1<leftRadiusUpper d ∧ 0<rightRadiusUpper d := by
  have hd2 : d^2≤(33/200 : ℝ)^2 := pow_le_pow_left₀ hd.1 hd.2 2
  have hd2' : d^2≤(33/200 : ℝ)*d := by
    nlinarith [mul_nonneg hd.1 (show 0≤33/200-d by linarith [hd.2])]
  dsimp [angleUpper,leftRadiusUpper,rightRadiusUpper]
  exact ⟨⟨by nlinarith [sq_nonneg d],by nlinarith⟩,
    by nlinarith,by nlinarith⟩

theorem left_square_reserve {d : ℝ} (hd : 0≤d) :
    qCap<(leftRadiusUpper d)^2+(167/200+d)^2 := by
  have hid : (leftRadiusUpper d)^2+(167/200+d)^2-qCap=
      61/1000000+(79/50000)*d+(2849/200000)*d^2+
        (6231/20000)*d^3+(4489/40000)*d^4 := by
    dsimp [leftRadiusUpper,qCap]
    ring
  have hp : 0<61/1000000+(79/50000)*d+(2849/200000)*d^2+
      (6231/20000)*d^3+(4489/40000)*d^4 := by positivity
  linarith

theorem right_square_reserve {d : ℝ} (hd : d∈Icc 0 (33/200 : ℝ)) :
    qCap<(rightRadiusUpper d)^2+(233/200-d)^2 := by
  have hcoef : 0≤283441/1000000-(28431/50000)*d := by linarith [hd.2]
  have hid : (rightRadiusUpper d)^2+(233/200-d)^2-qCap=
      13/8000+(7/2500)*d+
        (283441/1000000-(28431/50000)*d)*d^2+(1521/10000)*d^4 := by
    dsimp [rightRadiusUpper,qCap]
    ring
  have hp : 0<13/8000+(7/2500)*d+
      (283441/1000000-(28431/50000)*d)*d^2+(1521/10000)*d^4 := by
    linarith [mul_nonneg hcoef (sq_nonneg d),hd.1,pow_nonneg hd.1 4]
  generalize qCap=Q at hid ⊢
  linarith

/-- One positive polynomial on the whole tangent interval bounds the
hard-angle expression at its explicit quadratic upper comparison. -/
theorem angle_taylor_reserve {d : ℝ} (hd : d∈Icc 0 (33/200 : ℝ)) :
    (leftRadiusUpper d-1)*
        (1-(angleUpper d)^2/2+(angleUpper d)^4/24)-
      (167/200+d)*(angleUpper d-(angleUpper d)^3/6)<1/2 := by
  have h6 : 0≤3526249/937500000-(341261/93750000)*d := by linarith [hd.2]
  have h8 : 0≤413/300000-(1453/5000000)*d := by linarith [hd.2]
  have hid : 1/2-((leftRadiusUpper d-1)*
        (1-(angleUpper d)^2/2+(angleUpper d)^4/24)-
      (167/200+d)*(angleUpper d-(angleUpper d)^3/6))=
      610740891/976562500000+(162535407/78125000000)*d+
        (28323632809/390625000000)*d^2+(709374067/19531250000)*d^3+
        (549769/156250000)*d^4+(16656879/1562500000)*d^5+
        (3526249/937500000-(341261/93750000)*d)*d^6+
        (413/300000-(1453/5000000)*d)*d^8+(67/3000000)*d^10 := by
    dsimp [leftRadiusUpper,angleUpper]
    ring
  have hp : 0<610740891/976562500000+(162535407/78125000000)*d+
        (28323632809/390625000000)*d^2+(709374067/19531250000)*d^3+
        (549769/156250000)*d^4+(16656879/1562500000)*d^5+
        (3526249/937500000-(341261/93750000)*d)*d^6+
        (413/300000-(1453/5000000)*d)*d^8+(67/3000000)*d^10 := by
    linarith [mul_nonneg h6 (pow_nonneg hd.1 6),mul_nonneg h8 (pow_nonneg hd.1 8),hd.1,
      pow_nonneg hd.1 2,pow_nonneg hd.1 3,pow_nonneg hd.1 4,pow_nonneg hd.1 5,pow_nonneg hd.1 10]
  linarith

theorem hard_angle_upper {a b z : ℝ}
    (hb : b∈Icc (67/200 : ℝ) (1/2)) (ha : 1/2<a)
    (hc : (a+1/2)^2+(b+1/2)^2≤qCap)
    (hz : z∈Icc 0 frameCap)
    (hf : 1/2≤(a-1/2)*Real.cos z-(b+1/2)*Real.sin z) :
    z<angleUpper (b-67/200) := by
  let d := b-67/200
  have hd : d∈Icc 0 (33/200 : ℝ) := by dsimp [d]; constructor <;> linarith [hb.1,hb.2]
  have hy : b+1/2=167/200+d := by dsimp [d]; ring
  have hmajor := majorant_bounds hd
  have hz' : angleUpper d∈Icc 0 frameCap := by
    dsimp [frameCap]
    exact ⟨by linarith [hmajor.1.1],by linarith [hmajor.1.2]⟩
  have har : a+1/2<leftRadiusUpper d := by
    have hs := left_square_reserve hd.1
    rw [←hy] at hs
    nlinarith [hmajor.2.1]
  by_contra! hbad
  have hcos := CorrelatedSameBlock.cos_anti hz' hz hbad
  have hsin := CorrelatedSameBlock.sin_mono hz' hz hbad
  have hpc := mul_le_mul_of_nonneg_left hcos (by linarith : 0≤a-1/2)
  have hys := mul_le_mul_of_nonneg_left hsin (by linarith [hb.1] : 0≤b+1/2)
  have hcap := mul_le_mul_of_nonneg_right
    (show a-1/2≤leftRadiusUpper d-1 by linarith)
    (show 0≤Real.cos (angleUpper d) by linarith [(transport_trig hz').1])
  have hct := mul_le_mul_of_nonneg_left (cos_upper_four hz'.1)
    (show 0≤leftRadiusUpper d-1 by linarith [hmajor.2.1])
  have hst := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hz'.1)
    (show 0≤167/200+d by linarith [hd.1])
  have hpoly := angle_taylor_reserve hd
  rw [hy] at hf hys
  linarith

/-- The opposite hard angle is below .21.  On that interval its Taylor
upper quadratic has curvature at most -1/2.  Completing its single square
costs at most 1/2401, including the weak zero-angle case. -/
theorem opposite_cap {P Y v : ℝ}
    (hP : P∈Icc (599/1000 : ℝ) (177/250))
    (hY : Y∈Icc (1 : ℝ) (233/200))
    (hv : v∈Icc 0 frameCap)
    (hf : 1/2≤P*Real.cos v-Y*Real.sin v) :
    P*Real.cos v-Y*Real.sin v+charge*v≤P+1/2401 := by
  have htr := transport_trig hv
  have hpc1 := mul_le_mul_of_nonneg_left (Real.cos_le_one v)
    (show 0≤P by linarith [hP.1])
  have hys1 := mul_le_mul_of_nonneg_right hY.1 htr.2.2.1
  have hsv : Real.sin v≤26/125 := by nlinarith [hP.2]
  have hv21 : v<21/100 := by
    by_contra! hvlong
    have hsm := CorrelatedSameBlock.sin_mono
      (show (21/100 : ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hv hvlong
    have hsl := Real.sin_ge_sub_cube (show (0:ℝ)≤21/100 by norm_num)
    norm_num at hsl
    linarith
  have hv3 : v^3≤(21/100 : ℝ)*v^2 := by
    have hh := mul_le_mul_of_nonneg_right hv21.le (sq_nonneg v)
    nlinarith
  have hv4 : v^4≤(21/100 : ℝ)^2*v^2 := by
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv.1 hv21.le 2) (sq_nonneg v)
    nlinarith
  have hct := mul_le_mul_of_nonneg_left (cos_upper_four hv.1)
    (show 0≤P by linarith [hP.1])
  have hst := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hv.1)
    (show 0≤Y by linarith [hY.1])
  have hp2 := mul_le_mul_of_nonneg_right hP.1 (sq_nonneg v)
  have hp4 := mul_le_mul_of_nonneg_right hP.2 (pow_nonneg hv.1 4)
  have hy3 := mul_le_mul_of_nonneg_right hY.2 (pow_nonneg hv.1 3)
  have hquad : P*Real.cos v-Y*Real.sin v≤P-Y*v-v^2/4 := by
    nlinarith
  have hyv := mul_le_mul_of_nonneg_right hY.1 hv.1
  dsimp [charge]
  nlinarith [sq_nonneg (v/2-1/49)]

/-- Only the actual middle circles and two hard contacts enter this
bound.  The other intermediate has its normal weak sign, encoded by t≥0.
The new left frame needs only its own angle bound, not a total spread
with the fixed opposite side. -/
theorem actual_middle_bound {aA aB b t z v : ℝ}
    (hb : b∈Icc (67/200 : ℝ) (1/2)) (haA : 1/2<aA)
    (hA : (aA+1/2)^2+(b+1/2)^2≤qCap)
    (hB : (aB+1/2)^2+(3/2-b)^2≤qCap)
    (hz : z∈Icc 0 frameCap) (hv : v∈Icc 0 frameCap) (ht : 0≤t)
    (hGA : 1/2≤(aA-1/2)*Real.cos z-(b+1/2)*Real.sin z)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(3/2-b)*Real.sin v) :
    t+charge*(z+v)<419/1000 := by
  let d := b-67/200
  let Y := 3/2-b
  let R := Real.sqrt (qCap-Y^2)
  have hd : d∈Icc 0 (33/200 : ℝ) := by dsimp [d]; constructor <;> linarith [hb.1,hb.2]
  have hY : Y∈Icc (1 : ℝ) (233/200) := by dsimp [Y]; constructor <;> linarith [hb.1,hb.2]
  have hY2 := pow_le_pow_left₀ (show 0≤Y by linarith [hY.1]) hY.2 2
  have hrad : 0≤qCap-Y^2 := by dsimp [qCap]; nlinarith
  have hR0 : 0≤R := Real.sqrt_nonneg _
  have hR2 : R^2=qCap-Y^2 := Real.sq_sqrt hrad
  have hR : R∈Icc (1599/1000 : ℝ) (427/250) := by
    have hYsq : (1:ℝ)≤Y^2 := by nlinarith [hY.1]
    constructor
    · exact (Real.le_sqrt (by norm_num) hrad).2 (by dsimp [qCap]; linarith)
    · exact (Real.sqrt_le_left (by norm_num)).2 (by dsimp [qCap]; linarith)
  have hBcap : aB-1/2≤R-1 := by
    change (aB+1/2)^2+Y^2≤qCap at hB
    have hle : aB+1/2≤R := Real.le_sqrt_of_sq_le (by linarith)
    linarith
  have hvc : 0≤Real.cos v := by linarith [(transport_trig hv).1]
  have hmul := mul_le_mul_of_nonneg_right hBcap hvc
  have hBT' : t+1/2≤(R-1)*Real.cos v-Y*Real.sin v := by
    dsimp [Y]
    linarith
  have henv := opposite_cap
    (show R-1∈Icc (599/1000 : ℝ) (177/250) by constructor <;> linarith [hR.1,hR.2])
    hY hv (by linarith)
  have hzmax := hard_angle_upper hb haA hA hz hGA
  have hRmax : R<rightRadiusUpper d := by
    have hs := right_square_reserve hd
    have hy : Y=233/200-d := by dsimp [Y,d]; ring
    rw [←hy] at hs
    exact (Real.sqrt_lt' (majorant_bounds hd).2.2).2 (by linarith)
  have hcombined : charge*angleUpper d+rightRadiusUpper d-3/2+1/2401<419/1000 := by
    have hid : charge*angleUpper d+rightRadiusUpper d-3/2+1/2401=
        2011/4802-(279/49000)*d-(911/4900)*d^2 := by
      dsimp [charge,angleUpper,rightRadiusUpper]
      ring
    rw [hid]
    linarith [hd.1,sq_nonneg d]
  have hcharge : 0<charge := by norm_num [charge]
  have hzcharge := mul_lt_mul_of_pos_left hzmax hcharge
  change charge*z<charge*angleUpper d at hzcharge
  linarith

end SquaresInCircles.Eight.SmallHardEnvelope
end
end
end

section
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
end
end
end
