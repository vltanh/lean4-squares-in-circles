module

public import SquaresInCircles.Eight.Owners.Negative.CaptureEndpoint
public import SquaresInCircles.Eight.Owners.Negative.CaptureSimplex
public import SquaresInCircles.Eight.Owners.Nonpositive.ChainBounds

/-!
# Eight squares: the canonical negative hard error is less than `3/200`

The five-anchor weak system determines the continuous stress weights: one weight family, chosen
from the total sine, makes the defect positive on every split with total error at least `3/200`
(`exists_positive_defect`), while the five weak contacts make it nonpositive. So the error of a
five-anchor system is below `3/200` (`five_anchor_small_error`), and on the canonical negative
branch of a hard input the B–D error is below `3/200`
(`HardInput.nonpositive_canonical_small_error`); the argument uses the circles of the five
anchors.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace NegativeCapture
open NegativeCaptureData NegativeLargeDECalculus

theorem lambda_bounds {b : Band} {α : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ)) (hs : Real.sin α∈domain b) :
    (93/100:ℝ)<NegativeCaptureStress.lambda (NegativeCaptureData.f b (Real.sin α)) α ∧
      NegativeCaptureStress.lambda (NegativeCaptureData.f b (Real.sin α)) α<117/100 := by
  obtain ⟨ha0,ha1,hf0,hf1⟩ := actual_weight_bounds hs
  obtain ⟨hc,hc1,hs0,hs1⟩ := short_trig hα
  have hf : 0≤NegativeCaptureData.f b (Real.sin α) := by linarith
  have hfc := mul_le_mul_of_nonneg_left hc1 hf
  have hu := shifted_weight_upper hs
  have hupper : NegativeCaptureStress.lambda (NegativeCaptureData.f b (Real.sin α)) α<117/100 := by
    dsimp [NegativeCaptureStress.lambda,NegativeCaptureStress.k,NegativeLargeDEStress.k]
    linarith
  have hfs := mul_le_mul hf1.le hs1 hs0 (by norm_num : (0:ℝ)≤117/100)
  have hcoef : 0≤(307/1000)*(1+Real.cos α)-NegativeCaptureData.f b (Real.sin α)*Real.sin α := by
    nlinarith
  have hprod := mul_nonneg hs0 hcoef
  have hid :
      (NegativeCaptureStress.lambda (NegativeCaptureData.f b (Real.sin α)) α-
        NegativeCaptureData.f b (Real.sin α))*(1+Real.cos α)=
      Real.sin α*((307/1000)*(1+Real.cos α)-
        NegativeCaptureData.f b (Real.sin α)*Real.sin α) := by
    dsimp [NegativeCaptureStress.lambda,NegativeCaptureStress.k,NegativeLargeDEStress.k]
    nlinarith [congrArg (fun x : ℝ => NegativeCaptureData.f b (Real.sin α)*x)
      (Real.sin_sq_add_cos_sq α)]
  have hlower : NegativeCaptureData.f b (Real.sin α)≤
      NegativeCaptureStress.lambda (NegativeCaptureData.f b (Real.sin α)) α := by
    by_contra! hbad
    have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr hbad)
      (show 0<1+Real.cos α by linarith)
    rw [hid] at hneg
    linarith
  exact ⟨hf0.trans_le hlower,hupper⟩

/-- One weight family, chosen from the total sine, makes the defect positive on every split with
`3/200 ≤ t + e`. -/
theorem exists_positive_defect {α t u e : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ))
    (ht : 0≤t) (hu : 0≤u) (he : 0≤e) (hsum : t+u+e=α)
    (hcut : 3/200≤t+e) :
    ∃a f : ℝ, 0≤a ∧ 0≤f ∧ 0<NegativeCaptureStress.defect a f α t u e := by
  have hrα : NegativeCaptureShortAngle.r≤α := by
    dsimp [NegativeCaptureShortAngle.r]
    linarith
  have hsinmono : Real.sin NegativeCaptureShortAngle.r≤Real.sin α :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by dsimp [NegativeCaptureShortAngle.r]; linarith [Real.pi_pos])
      (by linarith [hα.2,Real.pi_gt_three]) hrα
  have hs : Real.sin α∈Icc (1499/100000:ℝ) (27/100) :=
    ⟨(NegativeCaptureShortAngle.sine_lower.trans_le hsinmono).le,
      (Real.sin_le hα.1).trans hα.2⟩
  obtain ⟨b,hdom⟩ := domain_covers hs
  obtain ⟨ha0,ha1,hf0,hf1⟩ := actual_weight_bounds hdom
  obtain ⟨hl0,hl1⟩ := lambda_bounds hα hdom
  have hp : a b (Real.sin α)+NegativeCaptureStress.η∈Ioo (0:ℝ) (18/25) := by
    dsimp [NegativeCaptureStress.η]
    constructor <;> linarith
  have ha : a b (Real.sin α)∈Ioo (0:ℝ) (18/25) := by constructor <;> linarith
  have hl : |NegativeCaptureStress.lambda (NegativeCaptureData.f b (Real.sin α)) α|≤117/100 := by
    rw [abs_of_nonneg (by linarith : 0≤
      NegativeCaptureStress.lambda (NegativeCaptureData.f b (Real.sin α)) α)]
    exact hl1.le
  have hpositive := NegativeCaptureStress.positive_on_truncated_simplex hp ha hl hα
    (show (0:ℝ)≤3/200 by norm_num) ht hu he hsum hcut
    (by simpa [NegativeCaptureModel.tVertex,NegativeCaptureModel.uVertex,
      NegativeCaptureModel.eVertex,NegativeCaptureShortAngle.r] using
        NegativeCaptureEndpoint.vertex_positive hα hdom 0)
    (by simpa [NegativeCaptureModel.tVertex,NegativeCaptureModel.uVertex,
      NegativeCaptureModel.eVertex,NegativeCaptureShortAngle.r] using
        NegativeCaptureEndpoint.vertex_positive hα hdom 1)
    (by simpa [NegativeCaptureModel.tVertex,NegativeCaptureModel.uVertex,
      NegativeCaptureModel.eVertex,NegativeCaptureShortAngle.r] using
        NegativeCaptureEndpoint.vertex_positive hα hdom 2)
    (by simpa [NegativeCaptureModel.tVertex,NegativeCaptureModel.uVertex,
      NegativeCaptureModel.eVertex,NegativeCaptureShortAngle.r] using
        NegativeCaptureEndpoint.vertex_positive hα hdom 3)
  exact ⟨a b (Real.sin α),NegativeCaptureData.f b (Real.sin α),
    by linarith,by linarith,hpositive⟩

/-- The five weak contacts, with the five anchors in the circle of `q`, force `t + e < 3/200`. -/
theorem five_anchor_small_error {H A B D E : SignedPoint} {q α t u e : ℝ}
    (hq : q≤qTrial) (ht : 0≤t) (hu : 0≤u) (he : 0≤e)
    (hsum : t+u+e=α) (hα : α≤27/100)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hcH : H.Contained q) (hcA : A.Contained q) (hcB : B.Contained q)
    (hcD : D.Contained q) (hcE : E.Contained q)
    (hHA : NegativeCaptureStress.W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      H.y/Real.cos e+A.a*Real.cos t-A.y*Real.sin t)
    (hAB : 1≤A.y+B.y) (hlarge : 1/2≤A.y)
    (hBD : 1+NegativeCaptureStress.W u≤B.a*Real.cos u-B.y*Real.sin u+D.y)
    (hDE : NegativeCaptureStress.W α≤D.a+E.a*Real.sin α-E.y*Real.cos α)
    (hEH : 1≤H.a+E.y) : t+e<3/200 := by
  by_contra! hbad
  obtain ⟨a,f,ha,hf,hpositive⟩ :=
    exists_positive_defect ⟨by linarith,hα⟩ ht hu he hsum hbad
  have hnonpositive := NegativeCaptureStress.five_anchor_defect ha hf ht hu he hsum hα
    hyH hyA hyB hyD hyE (hcH.trans hq) (hcA.trans hq) (hcB.trans hq)
    (hcD.trans hq) (hcE.trans hq) hHA hAB hlarge hBD hDE hEH
  linarith

end NegativeCapture

namespace SignedCycle
open Candidate PositiveCancelingOuter

/-- On the large-B canonical branch of a hard input the B–D frame error is below `3/200`. The
relabeling is scalar only: the five circle hypotheses and both witnesses at E stay attached to
the points of the cycle. -/
theorem HardInput.nonpositive_canonical_small_error {q : ℝ}
    (I : HardInput q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hGHframe : I.cycle.theta G=I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hTD : I.cycle.Feasible T 2) (hBy : 1/2≤ -(I.cycle.point B).y)
    (hDEframe : I.cycle.theta E=I.cycle.theta D)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    I.cycle.theta B-I.cycle.theta D<3/200 := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hHG := I.aligned_HG_zero hGHframe
  have hAG : I.cycle.theta A≤I.cycle.theta G := by rw [hGHframe]; exact hAH
  have hGH : I.cycle.theta G≤I.cycle.theta H := by rw [hGHframe]
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  let t := I.cycle.theta B-I.cycle.theta T
  let u := I.cycle.theta H-I.cycle.theta A
  let e := I.cycle.theta T-I.cycle.theta D
  let α := I.cycle.theta H-I.cycle.theta D
  have ht : 0≤t := sub_nonneg.mpr hTB
  have hu : 0≤u := sub_nonneg.mpr hAH
  have he : 0≤e := sub_nonneg.mpr hDT
  have hsum : t+u+e=α := by dsimp [t,u,e,α]; rw [hAB]; ring
  have hα : α≤27/100 := hb.span_lt.le
  have hDF := I.negative_TD2_composite hcap hDT hTB hTD
  have hHA0 : NegativeOuterEZero.demand (1-V (I.cycle.point B).reflect t) e≤
      (I.cycle.point D).reflect.y := by
    dsimp [NegativeNoncancelingBarrier.F] at hDF
    rw [show (I.cycle.theta B-I.cycle.theta D)-
      (I.cycle.theta B-I.cycle.theta T)=e by dsimp [e]; ring] at hDF
    change 0≤(I.cycle.point D).reflect.y-1/2+
      (V (I.cycle.point B).reflect t-1)*Real.cos e-(13/12)*Real.sin e at hDF
    dsimp [NegativeOuterEZero.demand]
    linarith
  have hHA := NegativeLargeDEStress.composite_secant
    (show t∈Icc 0 (27/100:ℝ) from ⟨ht,by linarith⟩)
    (show e∈Icc 0 (27/100:ℝ) from ⟨he,by linarith⟩) hHA0
  have hHF := I.negative_HG0_composite hcap hAG hGH hHG
  rw [hGHframe] at hHF
  have hBD : 1+NegativeCaptureStress.W u≤
      (I.cycle.point A).a*Real.cos u-(I.cycle.point A).y*Real.sin u+
        (I.cycle.point H).y := by
    change 0≤NegativeNoncancelingBarrier.F (I.cycle.point H) (I.cycle.point A) u u at hHF
    simp only [NegativeNoncancelingBarrier.F,sub_self,Real.cos_zero,Real.sin_zero,
      mul_one,mul_zero,sub_zero] at hHF
    dsimp [V,NegativeCaptureStress.W,NegativeLargeDEStress.W] at *
    linarith
  have hABsum : 1≤(I.cycle.point B).reflect.y+(I.cycle.point A).y := by
    have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
      simpa [normalOwners,A] using I.witnesses.allowed A
    have hfeas : 0≤zeroProjection (I.cycle.point A) (I.cycle.point B) (delta I.cycle.theta A)
        (I.witnesses.owner A)-edgeWidth (delta I.cycle.theta A) := I.witnesses.feasible A
    have hδ : delta I.cycle.theta A=0 := by
      have hn : next A=B := rfl
      simp only [delta,hn,hAB,sub_self]
    rw [hδ,edgeWidth_zero] at hfeas
    simp only [SignedPoint.reflect]
    rcases hj with hj | hj <;> rw [hj] at hfeas <;>
      simp [zeroProjection] at hfeas <;> linarith
  have hDEcontact : NegativeCaptureStress.W α≤
      (I.cycle.point H).a+(I.cycle.point E).reflect.a*Real.sin α-
        (I.cycle.point E).reflect.y*Real.cos α := by
    have hαdom : α∈Icc 0 (7/10:ℝ) := ⟨hb.span_nonneg,by linarith⟩
    have hh : edgeWidth α≤(I.cycle.point H).a+
        (I.cycle.point E).a*Real.sin α+(I.cycle.point E).y*Real.cos α := by
      have hEH' : 0≤quarterProjection (I.cycle.point E) (I.cycle.point H)
          (delta I.cycle.theta E) 1-edgeWidth (delta I.cycle.theta E) := hEH
      have hδE : delta I.cycle.theta E=α := by
        have hn : next E=H := rfl
        simp only [delta,hn,hDEframe]
        rfl
      rw [hδE] at hEH'
      simp only [quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero] at hEH'
      linarith
    rw [edgeWidth_positive_formula hαdom] at hh
    simpa [NegativeCaptureStress.W,NegativeLargeDEStress.W,SignedPoint.reflect] using hh
  have hEHcontact : 1≤(I.cycle.point D).reflect.a+(I.cycle.point E).reflect.y := by
    have hDE' : 0≤quarterProjection (I.cycle.point Candidate.D) (I.cycle.point E)
        (delta I.cycle.theta Candidate.D) 3-edgeWidth (delta I.cycle.theta Candidate.D) := hDE
    have hδD : delta I.cycle.theta Candidate.D=0 := by
      have hn : next Candidate.D=E := rfl
      simp only [delta,hn,hDEframe,sub_self]
    rw [hδD,edgeWidth_zero] at hDE'
    simp [quarterProjection] at hDE'
    simp only [SignedPoint.reflect]
    linarith
  have hresult := NegativeCapture.five_anchor_small_error
    (H := (I.cycle.point D).reflect) (A := (I.cycle.point B).reflect)
    (B := I.cycle.point A) (D := I.cycle.point H) (E := (I.cycle.point E).reflect)
    hq ht hu he hsum hα
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.D_nonpos)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos)
    I.anchors_normal.A_nonneg I.anchors_normal.H_nonneg
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.E_nonpos)
    (by simpa using I.necessary.contained D) (by simpa using I.necessary.contained B)
    (I.necessary.contained A) (I.necessary.contained H)
    (by simpa using I.necessary.contained E)
    hHA hABsum (by simpa [SignedPoint.reflect] using hBy) hBD hDEcontact hEHcontact
  dsimp [t,e] at hresult
  linarith

end SignedCycle
end SquaresInCircles.Eight
