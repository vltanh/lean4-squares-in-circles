module

public import SquaresInCircles.Eight.TableFree.GeometricExistenceStress
public import SquaresInCircles.Eight.GeometricModel.FiveCornerNominalTrial

/-!
# The actual radicals as a five-circle model and stationary datum

Uncompiled reconstruction.  This is the exact adapter from the fixed
compact position window to the original circle stress and to the broad
algebraic stationary predicate.  All four circle equations are derived
from the positive square roots.  No fitted or previously selected
stationary point enters the construction.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GeometricExistence
open ExactFamily ExactFamily.FiveCornerGeometry GeometricModel.FiveCorner

def data (q u t : ℝ) : Coordinates where
  q := q
  y := -u
  z := Real.tan (t/2)
  x₁ := lowerRight q u
  x₂ := topRight q u
  y₃ := topHeight q u
  x₄ := -lowerLeft q u

theorem data_angle {q u t : ℝ} (ht : t∈closedTilts) : coordinateAngle (data q u t)=t := by
  have hpi := Real.arctan_lt_pi_div_two (1/5:ℝ)
  have hl : -(Real.pi/2)<t/2 := by linarith [ht.1,Real.pi_pos]
  have hu : t/2<Real.pi/2 := by linarith [ht.2,Real.pi_pos]
  dsimp [coordinateAngle,data]
  rw [Real.arctan_tan hl hu]
  ring

theorem data_frame {q u t : ℝ} (ht : t∈closedTilts) :
    (data q u t).c=Real.cos t ∧ (data q u t).s=Real.sin t := by
  have hf := coordinateAngle_frame (data q u t)
  rw [data_angle ht] at hf
  exact ⟨hf.1.symm,hf.2.symm⟩

theorem data_x₃ (q u t : ℝ) : (data q u t).x₃= -topLeft q u := by
  dsimp [Coordinates.x₃,data,topLeft]
  ring

theorem data_y₄ (q u t : ℝ) : (data q u t).y₄= -lowerHeight q u := by
  dsimp [Coordinates.y₄,data,lowerHeight]
  ring

theorem data_components {q u t : ℝ} (ht : t∈closedTilts) :
    (data q u t).h₁= -firstComponent q (Real.cos t) (Real.sin t) u ∧
      (data q u t).h₂= -secondComponent q (Real.cos t) (Real.sin t) u := by
  obtain ⟨hc,hs⟩ := data_frame (q:=q) (u:=u) ht
  constructor
  · rw [Coordinates.h₁,hc,hs]
    dsimp [data,firstComponent]
    ring
  · rw [Coordinates.h₂,hc,hs,data_y₄]
    dsimp [data,secondComponent]
    ring

theorem data_defect {q u t : ℝ} (ht : t∈closedTilts) :
    (data q u t).defect=defect q (Real.cos t) (Real.sin t) u := by
  rw [Coordinates.defect,(data_components ht).1,(data_components ht).2]
  dsimp [data,defect]
  ring

theorem data_chain {q u t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (hu : u∈positionWindow) :
    (data q u t).IsChain := by
  have hb := window_bounds hql hqu hu
  have hA : lowerRight q u^2+u^2=q := upper_circle hb.domain.first_radicand
  have hB : topRight q u^2+(2-u)^2=q := upper_circle hb.domain.second_radicand
  have hD : topHeight q u^2+topLeft q u^2=q := upper_circle hb.domain.third_radicand
  have hE : lowerLeft q u^2+lowerHeight q u^2=q := upper_circle hb.domain.fourth_radicand
  refine ⟨by dsimp [data]; linarith [hb.r_lower],
    by dsimp [data]; linarith [hb.U_lower],
    by dsimp [data]; linarith [hb.Y_lower],
    by dsimp [data]; linarith [hb.w_lower],?_,?_,?_,?_⟩
  · dsimp [data]
    nlinarith
  · dsimp [data]
    nlinarith
  · rw [data_x₃]
    dsimp [data]
    nlinarith
  · rw [data_y₄]
    dsimp [data]
    nlinarith

def circleModel (q u t : ℝ) : GeometricModel.FiveCorner := ofCoordinates (data q u t)

theorem circleModel_angle {q u t : ℝ} (ht : t∈closedTilts) :
    (circleModel q u t).angle=t := data_angle ht

theorem circleModel_spans {q u t : ℝ} (ht : t∈closedTilts) :
    (circleModel q u t).spans := by
  apply ofCoordinates_spans
  rw [data_angle ht]
  exact tilt_quarter ht

theorem circleModel_fits {q u t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500)
    (hu : u∈positionWindow) (ht : t∈closedTilts)
    (hF : defect q (Real.cos t) (Real.sin t) u≤0) :
    (circleModel q u t).fits (Real.sqrt q) := by
  have hc := data_chain (t:=t) hql hqu hu
  have hqp : 0≤q := by nlinarith
  have hlast : (data q u t).defect≤0 := by rw [data_defect ht]; exact hF
  refine ⟨Real.sqrt_nonneg _,fun i => ?_⟩
  rw [Real.sq_sqrt hqp]
  change normSq ((data q u t).anchorPoints i)≤q
  fin_cases i
  · simpa [Coordinates.anchorPoints,normSq,data] using hc.first_circle.le
  · simpa [Coordinates.anchorPoints,normSq,data] using hc.second_circle.le
  · simpa [Coordinates.anchorPoints,normSq,data] using hc.third_circle.le
  · simpa [Coordinates.anchorPoints,normSq,data] using hc.fourth_circle.le
  · simp only [Coordinates.anchorPoints,Matrix.cons_val_zero,Matrix.cons_val_succ]
    rw [Coordinates.normSq_inFrame]
    dsimp [Coordinates.defect,data] at hlast
    linarith

/-- Nonpositive actual circle defect implies the original five-point
stress inequality, including the zero-tilt degenerate E mass. -/
theorem actual_gap_nonpos {q u t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500)
    (hu : u∈positionWindow) (ht : t∈closedTilts)
    (hF : defect q (Real.cos t) (Real.sin t) u≤0) : Nominal.gap q t≤0 := by
  have hs : Real.sin (circleModel q u t).angle≤3/10 := by
    rw [circleModel_angle ht]
    linarith [(tilt_trig ht).2.2]
  have hg := Nominal.gap_nonpos_of_spans (circleModel_spans ht)
    (circleModel_fits hql hqu hu ht hF) hs
  rw [circleModel_angle ht,Real.sq_sqrt (by nlinarith : 0≤q)] at hg
  exact hg

/-- Every interior simultaneous critical zero in the fixed geometric
window satisfies all original stationary branch conditions. -/
theorem data_stationary {q u t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500)
    (hu : u∈positionWindow) (ht : t∈tiltInterval)
    (hF : defect q (Real.cos t) (Real.sin t) u=0)
    (hP : positionHalf q (Real.cos t) (Real.sin t) u=0)
    (hT : tiltFirst q (Real.cos t) (Real.sin t) u=0) :
    (data q u t).IsStationary := by
  have htclosed : t∈closedTilts := ⟨ht.1.le,ht.2.le⟩
  obtain ⟨hc,hs,hratio⟩ := tiltInterval_bounds ht
  have hunit := trig_unit t
  have hupper := window_critical_below_one hql hqu hc hs.le hunit hratio.le hu hP hT
  have hstrip : CriticalStrip q u := ⟨hql,hqu,hu.1,hupper.le⟩
  have hb := hstrip.bounds
  have hchain := data_chain (t:=t) hql hqu hu
  have hhalf : t/2∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    have ha := Real.arctan_lt_pi_div_two (1/5:ℝ)
    constructor <;> linarith [ht.1,ht.2,Real.pi_pos]
  have hzpos : 0<(data q u t).z := by
    change 0<Real.tan (t/2)
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
      (by linarith [hhalf.2,Real.pi_pos])) (Real.cos_pos_of_mem_Ioo hhalf)
  have hzlt : (data q u t).z<1 := by
    apply Real.arctan_strictMono.lt_iff_lt.mp
    rw [Real.arctan_one]
    change Real.arctan (Real.tan (t/2))<Real.pi/4
    rw [Real.arctan_tan hhalf.1 hhalf.2]
    have ha := Real.arctan_lt_pi_div_two (1/5:ℝ)
    linarith [ht.2]
  have hzrange : 2*(data q u t).z/(1-(data q u t).z^2)<1/5 := by
    have hang : 2*Real.arctan (data q u t).z<Real.arctan (1/5) := by
      change coordinateAngle (data q u t)<Real.arctan (1/5)
      rw [data_angle htclosed]
      exact ht.2
    rw [Real.two_mul_arctan (by linarith : -1<(data q u t).z) hzlt] at hang
    exact Real.arctan_strictMono.lt_iff_lt.mp hang
  have hposzero : (data q u t).positionDerivative=0 := by
    have hcoord := coordinate_positionHalf hchain
    rw [(data_frame htclosed).1,(data_frame htclosed).2] at hcoord
    change 2*positionHalf q (Real.cos t) (Real.sin t) (-(-u))=
      -(data q u t).positionDerivative at hcoord
    rw [neg_neg,hP] at hcoord
    linarith
  have htiltzero : (data q u t).tiltDerivative=0 := by
    have hcoord := coordinate_tiltFirst hchain
    rw [(data_frame htclosed).1,(data_frame htclosed).2] at hcoord
    change tiltFirst q (Real.cos t) (Real.sin t) (-(-u))=
      (data q u t).tiltDerivative at hcoord
    rw [neg_neg,hT] at hcoord
    exact hcoord.symm
  refine ⟨hchain,hql,hqu,?_,?_,?_,?_,?_,hzpos,hzrange,hzlt,?_,hposzero,htiltzero⟩
  · change -1< -u
    linarith
  · change -u< -(1/2:ℝ)
    linarith [hu.1]
  · rw [data_y₄]
    linarith [hb.v_upper]
  · rw [data_y₄]
    linarith [hb.v_lower]
  · rw [data_y₄]
    change -u< -lowerHeight q u
    linarith [hu.1,hb.v_upper]
  · rw [data_defect htclosed]
    exact hF

end SquaresInCircles.Eight.TableFree.GeometricExistence
