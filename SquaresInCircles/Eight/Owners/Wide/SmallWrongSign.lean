module

public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein
public import SquaresInCircles.Eight.Owners.Endpoint.RotationPenalty
public import SquaresInCircles.Eight.Owners.Small.PositiveZeroEndpoint
public import SquaresInCircles.Eight.Words.Crossed.SmallWrongScalar

/-!
# Eight squares: the ordered wrong-sign exclusion on the full small interval

The middle primary is lifted only to its
actual q-circle, keeping its original tangent.  The wrong intermediate
is optimized on that same circle.  Its intrinsic cap either already
allows tangent zero or reaches zero by the proved monotone demand.
The unchanged source H/D/E/T budget excludes that concrete endpoint.
No conclusion about equality of lifted and original points is used.
-/

section
/-!
## A sharper continuous hard envelope down to the .28 tangent threshold

Three rational quadratic majorants give a
single polynomial comparison on the complete tangent interval [.28,.5].
The opposite contact has no angular excess when its transverse corner
exceeds the charge; the remaining intrinsic branch has a uniform
completed-square excess.  The resulting actual middle budget is below
.4175, without implicit optimizers or a numerical acceptance premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.WideSmallHardEnvelope
open EndpointRotationPenalty

def angleUpper (d : ℝ) : ℝ := 3893/12500-(18/25)*d+d^2/5
def leftRadiusUpper (d : ℝ) : ℝ := 89701/50000-(93/200)*d-(67/200)*d^2
def rightRadiusUpper (d : ℝ) : ℝ := 3199/2000+(729/1000)*d-(39/100)*d^2

theorem majorant_bounds {d : ℝ} (hd : d∈Icc (-(11/200 : ℝ)) (33/200)) :
    angleUpper d∈Icc (19/100 : ℝ) (353/1000) ∧
      1<leftRadiusUpper d ∧ 0<rightRadiusUpper d := by
  have habs : |d|≤33/200 := abs_le.mpr ⟨by linarith [hd.1],hd.2⟩
  have hd2 : d^2≤(33/200 : ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) habs 2
  have hchord : d^2≤(11/100)*d+363/40000 := by
    nlinarith [mul_nonneg (show 0≤d+11/200 by linarith [hd.1])
      (show 0≤33/200-d by linarith [hd.2])]
  dsimp [angleUpper,leftRadiusUpper,rightRadiusUpper]
  exact ⟨⟨by nlinarith [hd.2,sq_nonneg d],by nlinarith [hd.1]⟩,
    by nlinarith [hd.2],by nlinarith [hd.1]⟩

theorem left_square_reserve {d : ℝ} (hd : -(11/200 : ℝ)≤d) :
    qCap<(leftRadiusUpper d)^2+(167/200+d)^2 := by
  let x := d+11/200
  have hx : 0≤x := by dsimp [x]; linarith
  have hcoef : 0<219884361/80000000000-(28109813/800000000)*x+
      (573721/2000000)*x^2 := by
    nlinarith [sq_nonneg (x-9/140),sq_nonneg x]
  have hid : (leftRadiusUpper d)^2+(167/200+d)^2-qCap=
      2504114409/64000000000000+x*
        (219884361/80000000000-(28109813/800000000)*x+
          (573721/2000000)*x^2)+(4489/40000)*x^4 := by
    dsimp [leftRadiusUpper,qCap,x]
    ring
  have hp : 0<2504114409/64000000000000+x*
      (219884361/80000000000-(28109813/800000000)*x+
        (573721/2000000)*x^2)+(4489/40000)*x^4 := by positivity
  linarith

theorem right_square_reserve {d : ℝ} (hd : d≤33/200) :
    qCap<(rightRadiusUpper d)^2+(233/200-d)^2 := by
  have hcoef : 19/100≤283831/1000000-(28431/50000)*d+(1521/10000)*d^2 := by
    nlinarith [sq_nonneg d]
  have hprod := mul_le_mul_of_nonneg_right hcoef (sq_nonneg d)
  have hid : (rightRadiusUpper d)^2+(233/200-d)^2-qCap=
      101/4000000+(2071/1000000)*d+
        (283831/1000000-(28431/50000)*d+(1521/10000)*d^2)*d^2 := by
    dsimp [rightRadiusUpper,qCap]
    ring
  rw [←sub_pos]
  rw [hid]
  nlinarith [sq_nonneg (d+2071/380000)]

theorem angle_taylor_reserve {d : ℝ} (hd : d∈Icc (-(11/200 : ℝ)) (33/200)) :
    (leftRadiusUpper d-1)*
        (1-(angleUpper d)^2/2+(angleUpper d)^4/24)-
      (167/200+d)*(angleUpper d-(angleUpper d)^3/6)<1/2 := by
  obtain ⟨c,hcdef⟩ : ∃ c : ℝ,c=213602950719462301/117187500000000000000 := ⟨_,rfl⟩
  obtain ⟨K,hKdef⟩ : ∃ K : ℝ,K=2826945227271970329/39062500000000000000+
      (708646698993441/19531250000000000)*d+
      (10316357513921/2929687500000000)*d^2+
      (166726669477/15625000000000)*d^3+
      (35200013789/9375000000000)*d^4-
      (34103849/9375000000)*d^5+(1720519/1250000000)*d^6-
      (1453/5000000)*d^7+(67/3000000)*d^8 := ⟨_,rfl⟩
  have habs : |d|≤33/200 := abs_le.mpr ⟨by linarith only [hd.1],hd.2⟩
  have hp (n : ℕ) : |d^n|≤(33/200 : ℝ)^n := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg d) habs n
  have h3 := (abs_le.mp (hp 3)).1
  have h5 := (abs_le.mp (hp 5)).2
  have h7 := (abs_le.mp (hp 7)).2
  have hK : 3/50≤K := by
    rw [hKdef]
    linarith only [hd.1,sq_nonneg d,sq_nonneg (d^2),sq_nonneg (d^3),sq_nonneg (d^4),h3,h5,h7]
  have hlinear : -(1/500)*|d|≤c*d := by
    have hm := mul_le_mul_of_nonneg_left (neg_abs_le d) (show 0≤c by rw [hcdef]; norm_num)
    have hc := mul_le_mul_of_nonneg_right (show c≤1/500 by rw [hcdef]; norm_num) (abs_nonneg d)
    linarith only [hm,hc]
  have hquad := mul_le_mul_of_nonneg_right hK (sq_nonneg d)
  have hid : 1/2-((leftRadiusUpper d-1)*
        (1-(angleUpper d)^2/2+(angleUpper d)^4/24)-
      (167/200+d)*(angleUpper d-(angleUpper d)^3/6))=
      735951208656548699/29296875000000000000000+c*d+K*d^2 := by
    rw [hcdef,hKdef]
    dsimp [leftRadiusUpper,angleUpper]
    ring
  have hsquare : |d|^2=d^2 := sq_abs d
  have hpositive : 0<735951208656548699/29296875000000000000000+c*d+K*d^2 := by
    linarith only [sq_nonneg (|d|-1/60),hlinear,hquad,hsquare]
  linarith only [hid,hpositive]

theorem hard_angle_upper {a b z : ℝ}
    (hb : b∈Icc (7/25 : ℝ) (1/2)) (ha : 1/2<a)
    (hc : (a+1/2)^2+(b+1/2)^2≤qCap)
    (hz : z∈Icc 0 frameCap)
    (hf : 1/2≤(a-1/2)*Real.cos z-(b+1/2)*Real.sin z) :
    z<angleUpper (b-67/200) := by
  let d := b-67/200
  have hd : d∈Icc (-(11/200 : ℝ)) (33/200) := by
    dsimp [d]; constructor <;> linarith [hb.1,hb.2]
  have hy : b+1/2=167/200+d := by dsimp [d]; ring
  have hm := majorant_bounds hd
  have hz' : angleUpper d∈Icc 0 frameCap := by
    dsimp [frameCap]
    exact ⟨by linarith [hm.1.1],by linarith [hm.1.2]⟩
  have har : a+1/2<leftRadiusUpper d := by
    have hs := left_square_reserve hd.1
    rw [←hy] at hs
    nlinarith [hm.2.1]
  by_contra! hbad
  have hcos := CorrelatedSameBlock.cos_anti hz' hz hbad
  have hsin := CorrelatedSameBlock.sin_mono hz' hz hbad
  have hpc := mul_le_mul_of_nonneg_left hcos (by linarith : 0≤a-1/2)
  have hys := mul_le_mul_of_nonneg_left hsin (by linarith [hb.1] : 0≤b+1/2)
  have hcap := mul_le_mul_of_nonneg_right (show a-1/2≤leftRadiusUpper d-1 by linarith)
    (show 0≤Real.cos (angleUpper d) by linarith [(transport_trig hz').1])
  have hct := mul_le_mul_of_nonneg_left (cos_upper_four hz'.1)
    (show 0≤leftRadiusUpper d-1 by linarith [hm.2.1])
  have hst := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hz'.1)
    (show 0≤167/200+d by linarith [hd.1])
  have hpoly := angle_taylor_reserve hd
  rw [hy] at hf hys
  linarith

theorem opposite_quadratic {P Y v : ℝ}
    (hP : P∈Icc (557/1000 : ℝ) (177/250))
    (hY : Y∈Icc (1 : ℝ) (61/50))
    (hv : v∈Icc 0 frameCap)
    (hf : 1/2≤P*Real.cos v-Y*Real.sin v) :
    P*Real.cos v-Y*Real.sin v≤P-Y*v-v^2/5 := by
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
    nlinarith [mul_le_mul_of_nonneg_right hv21.le (sq_nonneg v)]
  have hv4 : v^4≤(21/100 : ℝ)^2*v^2 := by
    nlinarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv.1 hv21.le 2) (sq_nonneg v)]
  have hct := mul_le_mul_of_nonneg_left (cos_upper_four hv.1)
    (show 0≤P by linarith [hP.1])
  have hst := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hv.1)
    (show 0≤Y by linarith [hY.1])
  have hp2 := mul_le_mul_of_nonneg_right hP.1 (sq_nonneg v)
  have hp4 := mul_le_mul_of_nonneg_right hP.2 (pow_nonneg hv.1 4)
  have hy3 := mul_le_mul_of_nonneg_right hY.2 (pow_nonneg hv.1 3)
  nlinarith

/-- The sharper complete interval bound used by both crossed small
normal and wrong-sign endpoint comparisons. -/
theorem actual_middle_bound {aA aB b t z v : ℝ}
    (hb : b∈Icc (7/25 : ℝ) (1/2)) (haA : 1/2<aA)
    (hA : (aA+1/2)^2+(b+1/2)^2≤qCap)
    (hB : (aB+1/2)^2+(3/2-b)^2≤qCap)
    (hz : z∈Icc 0 frameCap) (hv : v∈Icc 0 frameCap) (ht : 0≤t)
    (hGA : 1/2≤(aA-1/2)*Real.cos z-(b+1/2)*Real.sin z)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(3/2-b)*Real.sin v) :
    t+charge*(z+v)<167/400 := by
  obtain ⟨d,hd_def⟩ : ∃ d : ℝ,d=b-67/200 := ⟨_,rfl⟩
  obtain ⟨Y,hY_def⟩ : ∃ Y : ℝ,Y=3/2-b := ⟨_,rfl⟩
  obtain ⟨R,hR_def⟩ : ∃ R : ℝ,R=Real.sqrt (qCap-Y^2) := ⟨_,rfl⟩
  have hd : d∈Icc (-(11/200 : ℝ)) (33/200) := by
    rw [hd_def]; constructor <;> linarith only [hb.1,hb.2]
  have hY : Y∈Icc (1 : ℝ) (61/50) := by
    rw [hY_def]; constructor <;> linarith only [hb.1,hb.2]
  have hY2 := pow_le_pow_left₀ (show 0≤Y by linarith only [hY.1]) hY.2 2
  have hYsq : (1:ℝ)≤Y^2 := one_le_pow₀ hY.1
  have hrad : 0≤qCap-Y^2 := by
    simp only [qCap]
    linarith only [hY2]
  have hR0 : 0≤R := by rw [hR_def]; exact Real.sqrt_nonneg _
  have hR2 : R^2=qCap-Y^2 := by rw [hR_def]; exact Real.sq_sqrt hrad
  have hR : R∈Icc (1557/1000 : ℝ) (427/250) := by
    rw [hR_def]
    constructor
    · rw [Real.le_sqrt (by norm_num) hrad]
      simp only [qCap]
      linarith only [hY2]
    · rw [Real.sqrt_le_left (by norm_num)]
      simp only [qCap]
      linarith only [hYsq]
  have hBcap : aB-1/2≤R-1 := by
    rw [← hY_def] at hB
    have h1 : |aB+1/2|≤R := by
      rw [hR_def]
      exact Real.abs_le_sqrt (by linarith only [hB])
    linarith only [le_abs_self (aB+1/2),h1]
  have hmul := mul_le_mul_of_nonneg_right hBcap
    (show 0≤Real.cos v by linarith only [(transport_trig hv).1])
  have hBT' : t+1/2≤(R-1)*Real.cos v-Y*Real.sin v := by
    rw [← hY_def] at hBT
    linarith only [hBT,hmul]
  have hquad := opposite_quadratic
    (show R-1∈Icc (557/1000 : ℝ) (177/250) by constructor <;> linarith only [hR.1,hR.2])
    hY hv (by linarith only [hBT',ht])
  have hzmax := hard_angle_upper hb haA hA hz hGA
  rw [← hd_def] at hzmax
  have hRmax : R<rightRadiusUpper d := by
    have hs := right_square_reserve hd.2
    have hy : Y=233/200-d := by rw [hY_def,hd_def]; ring
    rw [←hy] at hs
    have hpos := (majorant_bounds hd).2.2
    apply lt_of_pow_lt_pow_left₀ 2 hpos.le
    linarith only [hs,hR2]
  have hid : charge*angleUpper d+rightRadiusUpper d-3/2=
      40895/98000-(279/49000)*d-(911/4900)*d^2 := by
    dsimp [charge,angleUpper,rightRadiusUpper]
    ring
  have hzcharge := mul_lt_mul_of_pos_left hzmax (by norm_num [charge] : 0<charge)
  by_cases hYp : charge≤Y
  · have hpv := mul_le_mul_of_nonneg_right hYp hv.1
    have hcombined : charge*angleUpper d+rightRadiusUpper d-3/2<167/400 := by
      rw [hid]
      linarith only [sq_nonneg (d+279/18220)]
    linarith only [sq_nonneg v,hpv,hBT',hquad,hRmax,hcombined,hzcharge]
  · have hexcess : (R-1)*Real.cos v-Y*Real.sin v+charge*v≤R-1+5/9604 := by
      have hyv := mul_le_mul_of_nonneg_right hY.1 hv.1
      simp only [charge]
      linarith only [sq_nonneg (v-5/98),hquad,hyv]
    have hdlarge : 7/50≤d := by
      have h := lt_of_not_ge hYp
      simp only [charge] at h
      rw [hd_def]
      linarith only [h,hY_def]
    have hcombined : charge*angleUpper d+rightRadiusUpper d-3/2+5/9604<167/400 := by
      rw [hid]
      linarith only [sq_nonneg d,hdlarge]
    linarith only [hBT',hexcess,hRmax,hcombined,hzcharge]

end SquaresInCircles.Eight.WideSmallHardEnvelope
end
end
end

section
/-!
## Positive zero endpoints down to the tangent `0.28`

The H/D/E budget of the cycle and the opposite hard contact exclude the endpoint with G at zero
tangent on the whole small-tangent interval `[0.28, 0.5]`
(`HardOuterGeometry.wide_small_positive_G_zero_impossible`). Only the GA angle of the candidate is
bounded; the moved cycle needs no larger spread bound.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate EndpointRotationPenalty EndpointBudgetScalars

namespace SignedCycle

/-- The transverse-zero alternative of the small-side construction of a positive HG0 is impossible
for middle tangents in `[7/25, 1/2]`, by the cycle itself: `P` and `Q` are the candidate points of
A and G, and `θ` the candidate frame of G. The statement assumes no lift to the radius of the cycle
and no spread bound for `Q`. -/
theorem HardOuterGeometry.wide_small_positive_G_zero_impossible {q θ : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hTy : 0≤(I.cycle.point T).y)
    (P Q : SignedPoint) (hPs : P.Sorted) (hPc : P.AvoidsCore)
    (hPq : P.Contained q) (hPy : P.y=(I.cycle.point A).y)
    (hQq : Q.Contained q) (hQy : Q.y=0)
    (hHθ : I.cycle.theta H<θ) (hθA : θ-I.cycle.theta A≤frameCap)
    (hHG : zeroFeasible (I.cycle.point H) Q (θ-I.cycle.theta H) 0)
    (hGA : quarterFeasible Q P (I.cycle.theta A-θ) 0) : False := by
  obtain ⟨z,hzdef⟩ : ∃ z,z=θ-I.cycle.theta A := ⟨_,rfl⟩
  obtain ⟨v,hvdef⟩ : ∃ v,v=I.cycle.theta A-I.cycle.theta T := ⟨_,rfl⟩
  obtain ⟨h,hhdef⟩ : ∃ h,h=θ-I.cycle.theta H := ⟨_,rfl⟩
  have hz : z∈Icc 0 frameCap := ⟨by rw [hzdef]; linarith,by rw [hzdef]; exact hθA⟩
  have hv : v∈Icc 0 frameCap := by
    refine ⟨by rw [hvdef]; exact sub_nonneg.mpr hTA,?_⟩
    rw [hvdef]
    exact (le_abs_self _).trans (I.necessary.spread A T)
  have hPa : 1/2<P.a := SignedPoint.primary_gt_half hPs hPc
  have hPy0 : 0≤P.y := by rw [hPy]; linarith [hsmall.1]
  have hAc : (P.a+1/2)^2+((I.cycle.point A).y+1/2)^2≤qCap := by
    have hh := hPq.trans hq
    change (P.a+1/2)^2+(|P.y|+1/2)^2≤qCap at hh
    rw [abs_of_nonneg hPy0,hPy] at hh
    exact hh
  have hBc : ((I.cycle.point B).a+1/2)^2+(3/2-(I.cycle.point A).y)^2≤qCap := by
    have hc := (I.necessary.contained B).trans hq
    have hy : -(I.cycle.point B).y+1/2=3/2-(I.cycle.point A).y := by linarith
    change ((I.cycle.point B).a+1/2)^2+(|(I.cycle.point B).y|+1/2)^2≤qCap at hc
    rw [abs_of_nonpos I.anchors_normal.B_nonpos,hy] at hc
    exact hc
  have hGA' : 1/2≤(P.a-1/2)*Real.cos z-
      ((I.cycle.point A).y+1/2)*Real.sin z := by
    have hf : quarterFeasible Q P (-z) 0 := by
      have hd : I.cycle.theta A-θ= -z := by rw [hzdef]; ring
      rw [hd] at hGA
      exact hGA
    rw [quarterFeasible,edgeWidth_negative_formula hz] at hf
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hQy,hPy] at hf
    linarith
  have hBT' : (I.cycle.point T).y+1/2≤
      ((I.cycle.point B).a-1/2)*Real.cos v-
        (3/2-(I.cycle.point A).y)*Real.sin v := by
    have hf : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
      have hd : I.cycle.theta 4-I.cycle.theta 3= -v := by
        change I.cycle.theta T-I.cycle.theta B= -v; rw [hvdef,←hAB]; ring
      simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,hd]
        using I.BT_hard
    rw [quarterFeasible,edgeWidth_negative_formula hv] at hf
    simp [quarterProjection,Real.cos_neg,Real.sin_neg] at hf
    have hBy : (I.cycle.point B).y=(I.cycle.point A).y-1 := by linarith
    rw [hBy] at hf
    linarith
  have hzmax := WideSmallHardEnvelope.hard_angle_upper hsmall hPa hAc hz hGA'
  have hd : (I.cycle.point A).y-67/200∈Icc (-(11/200) : ℝ) (33/200) := by
    constructor <;> linarith [hsmall.1,hsmall.2]
  have hhi : h∈Ioc 0 (2/5 : ℝ) := by
    have hzbound := (WideSmallHardEnvelope.majorant_bounds hd).1.2
    rw [hhdef]
    rw [hzdef] at hzmax
    constructor <;> linarith
  have hHy : (I.cycle.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hHcharge := SmallPositiveZeroEndpoint.zero_outer_strict_charge
    hq hQq hQy hHy hhi (by rw [hhdef]; exact hHG)
  have hmiddle := WideSmallHardEnvelope.actual_middle_bound hsmall hPa hAc hBc
    hz hv hTy hGA' hBT'
  have hTDcharge := (signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs).2
  have hbudget := I.endpoint_bound hq
  have hS := SmallPositiveZeroEndpoint.endpoint_constant_lower
  rw [hhdef] at hHcharge
  rw [hzdef,hvdef] at hmiddle
  simp only [EndpointRotationPenalty.charge,epsilon] at hHcharge hmiddle hTDcharge hbudget
  linarith

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

theorem HardOuterGeometry.wide_small_wrong_G_impossible {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hTy : 0≤(I.cycle.point T).y)
    (hGy : 0≤(I.cycle.point G).y) (hGsmall : (I.cycle.point G).y<1/10) : False := by
  have hHupper : (I.cycle.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hcharge := (signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs).1
  have hHGorder : I.cycle.theta H<I.cycle.theta G := by
    simp only [EndpointRotationPenalty.charge] at hcharge
    linarith
  have hHG : I.cycle.Feasible H 0 := by
    have ho : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
      simpa [normalOwners,H] using I.witnesses.allowed H
    rcases ho with ho | ho
    · simpa [ho] using I.witnesses.feasible H
    · exact False.elim (not_lt_of_ge hGy (I.zero_signs.HG_canceling ho))
  obtain ⟨Θ,hΘdef⟩ : ∃ Θ,Θ=I.cycle.theta H-I.cycle.theta A := ⟨_,rfl⟩
  obtain ⟨e,hedef⟩ : ∃ e,e=I.cycle.theta G-I.cycle.theta H := ⟨_,rfl⟩
  have hΘ : 0≤Θ := by rw [hΘdef]; exact sub_nonneg.mpr hAH
  have he : 0<e := by rw [hedef]; exact sub_pos.mpr hHGorder
  have hz : Θ+e∈Icc 0 frameCap := by
    refine ⟨by linarith,?_⟩
    have hspread := (le_abs_self _).trans (I.necessary.spread G A)
    rw [hΘdef,hedef]
    linarith
  have hei : e∈Icc 0 frameCap := ⟨he.le,by linarith [hz.2]⟩
  let P := SignedPoint.outerAt q (I.cycle.point A).y
  obtain ⟨hPs,hPo,hPc⟩ := SignedPoint.outerAt_spec hqL
    (SignedPoint.contained_minor_le_diagonal (I.necessary.sorted A) (I.necessary.contained A))
  have hPy : P.y=(I.cycle.point A).y := rfl
  have hPa : (I.cycle.point A).a≤P.a := by
    have hsource := I.necessary.contained A
    have htarget := hPo
    change ((I.cycle.point A).a+1/2)^2+(|(I.cycle.point A).y|+1/2)^2≤q at hsource
    change (P.a+1/2)^2+(|P.y|+1/2)^2=q at htarget
    rw [hPy] at htarget
    have h2 : ((I.cycle.point A).a+1/2)^2≤(P.a+1/2)^2 := by linarith
    have h3 := le_of_pow_le_pow_left₀ two_ne_zero (by linarith [hPs.1]) h2
    linarith
  obtain ⟨p,hpdef⟩ : ∃ p,p=P.a-1/2 := ⟨_,rfl⟩
  obtain ⟨Y,hYdef⟩ : ∃ Y,Y=(I.cycle.point A).y+1/2 := ⟨_,rfl⟩
  have hY : Y∈Icc (39/50 : ℝ) 1 := by
    rw [hYdef]
    constructor <;> linarith [hsmall.1,hsmall.2]
  have hcircle : (p+1)^2+Y^2=q := by
    have hc := hPo
    change (P.a+1/2)^2+(|P.y|+1/2)^2=q at hc
    rw [hPy,abs_of_nonneg I.anchors_normal.A_nonneg] at hc
    rw [hpdef,hYdef]
    linarith
  have hp : p∈Icc (1/2 : ℝ) (819/1000) := by
    have hqL' := hqL
    have hq' := hq
    dsimp [qLow,qCap] at hqL' hq'
    have hPpos : 0<p := by
      have hh := SignedPoint.primary_gt_half hPs hPc
      rw [hpdef]
      linarith
    constructor
    · have hy2 := pow_le_pow_left₀ (show 0≤Y by linarith [hY.1]) hY.2 2
      by_contra! hlt
      have h3 := pow_lt_pow_left₀ (show p+1<3/2 by linarith) (by linarith) two_ne_zero
      linarith
    · have hy2 := pow_le_pow_left₀ (show (0:ℝ)≤39/50 by norm_num) hY.1 2
      by_contra! hlt
      have h3 := pow_lt_pow_left₀ (show (1819/1000:ℝ)<p+1 by linarith) (by norm_num) two_ne_zero
      linarith
  have S : CrossedSmallWrongScalar.CapData q p Y := {
    P_mem := hp
    Y_mem := hY
    circle := hcircle
    floor := hqL
    ceiling := hq }
  have hGA : -(I.cycle.point G).y+1/2≤PositiveSmallScalar.V p Y (Θ+e) := by
    have hf : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-(Θ+e)) 0 := by
      have hd : I.cycle.theta 2-I.cycle.theta 1= -(Θ+e) := by
        change I.cycle.theta A-I.cycle.theta G= -(Θ+e)
        rw [hΘdef,hedef]; ring
      simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,hd]
        using I.GA_hard
    rw [quarterFeasible,edgeWidth_negative_formula hz] at hf
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg] at hf
    have hmul := mul_le_mul_of_nonneg_right hPa (show 0≤Real.cos (Θ+e) by
      linarith [(transport_trig hz).1])
    simp only [PositiveSmallScalar.V]
    rw [hpdef,hYdef]
    linarith
  have hVlower : 2/5<PositiveSmallScalar.V p Y (Θ+e) := by linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) e 0 := by
    have hd : I.cycle.theta 1-I.cycle.theta 0=e := by
      change I.cycle.theta G-I.cycle.theta H=e
      rw [hedef]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,hd] using hHG
  let Q := SignedPoint.outerAt q 0
  have hQbound : |(0:ℝ)|≤diagonalCoordinate q := by
    have hh := (uniform_circle_reserves hqL hq).1
    rw [abs_zero]
    linarith
  obtain ⟨hQs,hQo,hQc⟩ := SignedPoint.outerAt_spec hqL hQbound
  have hQy : Q.y=0 := rfl
  have hGAzero {s : ℝ} (hs : s∈Ioc 0 e)
      (hV : 1/2≤PositiveSmallScalar.V p Y (Θ+s)) :
      quarterFeasible Q P (-(Θ+s)) 0 := by
    have hi : Θ+s∈Icc 0 frameCap :=
      ⟨by linarith [hs.1],by linarith [hs.2,hz.2]⟩
    rw [quarterFeasible,edgeWidth_negative_formula hi]
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hQy,hPy]
    simp only [PositiveSmallScalar.V] at hV
    rw [hpdef,hYdef] at hV
    linarith
  have hcandidate : ∃s,s∈Ioc 0 e ∧
      zeroFeasible (I.cycle.point H) Q s 0 ∧ quarterFeasible Q P (-(Θ+s)) 0 := by
    by_cases hcap : 1/2≤PositiveSmallScalar.V p Y (Θ+e)
    · have hQa : (I.cycle.point G).a≤Q.a := by
        have hGc := I.necessary.contained G
        have hQcircle := hQo
        change ((I.cycle.point G).a+1/2)^2+(|(I.cycle.point G).y|+1/2)^2≤q at hGc
        change (Q.a+1/2)^2+(|Q.y|+1/2)^2=q at hQcircle
        rw [abs_of_nonneg hGy] at hGc
        rw [hQy,abs_zero] at hQcircle
        have hy2 := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num)
          (show (1/2:ℝ)≤(I.cycle.point G).y+1/2 by linarith) 2
        have h2 : ((I.cycle.point G).a+1/2)^2≤(Q.a+1/2)^2 := by linarith
        have h3 := le_of_pow_le_pow_left₀ two_ne_zero (by linarith [hQs.1]) h2
        linarith
      have hg : zeroFeasible (I.cycle.point H) Q e 0 := by
        have hh := hHG'
        unfold zeroFeasible at hh ⊢
        simp only [zeroProjection,Matrix.cons_val_zero,hQy] at hh ⊢
        have ha := mul_le_mul_of_nonneg_right hQa (transport_trig hei).2.2.1
        have hy := mul_nonneg hGy (show 0≤Real.cos e by linarith [(transport_trig hei).1])
        linarith
      exact ⟨e,⟨he,le_rfl⟩,hg,hGAzero ⟨he,le_rfl⟩ hcap⟩
    · have hv : PositiveSmallScalar.V p Y (Θ+e)∈Ioo (2/5 : ℝ) (1/2) :=
        ⟨hVlower,lt_of_not_ge hcap⟩
      have hb := CrossedSmallWrongScalar.root_bounds S hz
        ⟨hv.1.le,hv.2.le⟩
      have hW2 : (SmallWrongScalar.W q p Y (Θ+e))^2=
          q-(1-PositiveSmallScalar.V p Y (Θ+e))^2 := Real.sq_sqrt hb.1.le
      have hGa : (I.cycle.point G).a≤SmallWrongScalar.W q p Y (Θ+e)-1/2 := by
        have hGc := I.necessary.contained G
        change ((I.cycle.point G).a+1/2)^2+(|(I.cycle.point G).y|+1/2)^2≤q at hGc
        rw [abs_of_nonneg hGy] at hGc
        have hy2 := pow_le_pow_left₀
          (show 0≤1-PositiveSmallScalar.V p Y (Θ+e) by linarith [hv.2])
          (show 1-PositiveSmallScalar.V p Y (Θ+e)≤(I.cycle.point G).y+1/2 by linarith) 2
        have h2 : ((I.cycle.point G).a+1/2)^2≤(SmallWrongScalar.W q p Y (Θ+e))^2 := by
          rw [hW2]; linarith
        have h3 := le_of_pow_le_pow_left₀ two_ne_zero
          (show 0≤SmallWrongScalar.W q p Y (Θ+e) from Real.sqrt_nonneg _) h2
        linarith
      have hsource : SmallWrongScalar.demand q p Y Θ e≤(I.cycle.point H).y := by
        have hh := hHG'
        rw [zeroFeasible,edgeWidth_positive_formula hei] at hh
        simp only [zeroProjection,Matrix.cons_val_zero] at hh
        have ha := mul_le_mul_of_nonneg_right hGa (transport_trig hei).2.2.1
        have hy := mul_le_mul_of_nonneg_right
          (show 1/2-PositiveSmallScalar.V p Y (Θ+e)≤(I.cycle.point G).y by linarith)
          (show 0≤Real.cos e by linarith [(transport_trig hei).1])
        simp only [SmallWrongScalar.demand]
        linarith
      obtain ⟨s,hs,hzero,hdemand⟩ := CrossedSmallWrongScalar.zero_contact S
        hΘ he hz hv hHupper hsource
      have hi : s∈Icc 0 frameCap := ⟨hs.1.le,hs.2.trans hei.2⟩
      have hW : SmallWrongScalar.W q p Y (Θ+s)=Real.sqrt (q-1/4) := by
        simp only [SmallWrongScalar.W,hzero]
        norm_num
      have hQa : Q.a=Real.sqrt (q-1/4)-1/2 := by
        simp only [Q,SignedPoint.outerAt,abs_zero]
        norm_num
      have hg : zeroFeasible (I.cycle.point H) Q s 0 := by
        simp only [SmallWrongScalar.demand] at hdemand
        rw [hzero,hW] at hdemand
        rw [zeroFeasible,edgeWidth_positive_formula hi]
        simp only [zeroProjection,Matrix.cons_val_zero,hQy,hQa]
        linarith
      exact ⟨s,hs,hg,hGAzero hs hzero.ge⟩
  obtain ⟨s,hs,hHGQ,hGAQ⟩ := hcandidate
  apply I.wide_small_positive_G_zero_impossible (θ := I.cycle.theta H+s)
    hq hAB hnorm hsmall hTA hAH hTy P Q hPs hPc hPo.le hPy hQo.le hQy
    (by linarith [hs.1])
    (by rw [hΘdef] at hz; linarith [hs.2,hz.2])
  · have hd : I.cycle.theta H+s-I.cycle.theta H=s := by ring
    rw [hd]
    exact hHGQ
  · have hd : I.cycle.theta A-(I.cycle.theta H+s)= -(Θ+s) := by rw [hΘdef]; ring
    rw [hd]
    exact hGAQ

end SignedCycle
end SquaresInCircles.Eight
end
end
end
