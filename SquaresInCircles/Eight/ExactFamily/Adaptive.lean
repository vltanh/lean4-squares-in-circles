module

public import SquaresInCircles.Eight.ExactFamily.Stationary
public import SquaresInCircles.Eight.ExactFamily.Generated.AdaptiveBounds

/-!
# Adaptive comparison for every terminal tilt

Uncompiled draft.  The position coordinate is an actual zero supplied by the
intermediate value theorem.  A complete fixed rational cover certifies the
endpoint signs and the nine owner reserves on its stationary graph.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.ExactFamily
open Arithmetic Generated

def tiltBox : Set ℝ := Icc (1/20) (81/1000)

theorem uniform_grid_cover (n : ℕ) (hn : 0<n) {l w x : ℝ}
    (hw : 0 ≤ w) (hx : l ≤ x ∧ x ≤ l+(n:ℝ)*w) :
    ∃ i : Fin n, l+(i.val:ℝ)*w ≤ x ∧ x ≤ l+(i.val+1:ℝ)*w := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => exact ⟨0,by simpa using hx⟩
    | succ m =>
      by_cases h : x ≤ l+((m+1:ℕ):ℝ)*w
      · obtain ⟨i,hi⟩ := ih (by omega) ⟨hx.1,h⟩
        exact ⟨i.castSucc,by simpa using hi⟩
      · refine ⟨Fin.last (m+1),?_,?_⟩
        · simpa using (le_of_not_ge h)
        · simpa [Nat.cast_add,Nat.cast_one] using hx.2

theorem adaptive_grid_cover {z : ℝ} (hz : z ∈ tiltBox) :
    ∃ i : Fin 256, AdaptiveGenerated.zLo i ≤ z ∧ z ≤ AdaptiveGenerated.zHi i := by
  obtain ⟨i,hi⟩ := uniform_grid_cover 256 (by omega) (l:=1/20)
    (w:=31/256000) (x:=z) (by norm_num) (by simpa [tiltBox] using hz)
  exact ⟨i,by simpa [AdaptiveGenerated.zLo,AdaptiveGenerated.zHi,mul_comm] using hi⟩

theorem familyYY_derivative {q y z : ℝ} (hq : q ∈ radiusBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200))) (hz : z ∈ tiltBox) :
    HasDerivAt (fun r => familyY q (r,z)) (familyYY q (y,z)) y := by
  have hr := (family_regular hq ⟨hy,hz⟩).2.1
  have hd := Formula.hasDerivAt_partial FyFormula 1 ![q,y,z] hr
  rw [Fyy_diff] at hd
  convert hd using 1
  · funext r
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  · rfl

theorem familyY_continuous_y {q z : ℝ} (hq : q ∈ radiusBox) (hz : z ∈ tiltBox) :
    ContinuousOn (fun y => familyY q (y,z)) (Icc (-(937/1000)) (-(179/200))) := by
  intro y hy
  exact (familyYY_derivative hq hy hz).continuousAt.continuousWithinAt

theorem familyY_slope {q z a b : ℝ} (hq : q ∈ radiusBox) (hz : z ∈ tiltBox)
    (ha : a ∈ Icc (-(937/1000)) (-(179/200)))
    (hb : b ∈ Icc (-(937/1000)) (-(179/200))) (hab : a ≤ b) :
    6*(b-a) ≤ familyY q (b,z)-familyY q (a,z) := by
  have hm := monoOn_of_hasDeriv_nonneg (l:=-(937/1000)) (u:=-(179/200))
    (f:=fun y => familyY q (y,z)-6*y) (d:=fun y => familyYY q (y,z)-6)
    ((familyY_continuous_y hq hz).sub (continuous_const.mul continuous_id).continuousOn)
    (fun y hy => by
      convert (familyYY_derivative hq ⟨hy.1.le,hy.2.le⟩ hz).sub
        ((hasDerivAt_id y).const_mul 6) using 1 <;> ring)
    (fun y hy => by
      have hh := (hessian_data hq ⟨⟨hy.1.le,hy.2.le⟩,hz⟩).1
      linarith)
  have hh := hm ha hb hab
  linarith

theorem graph_endpoint_mem (i : Fin 256) {q z : ℝ}
    (hq : sharpLower ≤ q ∧ q ≤ sharpUpper)
    (hz : AdaptiveGenerated.zLo i ≤ z ∧ z ≤ AdaptiveGenerated.zHi i) :
    (AdaptiveGenerated.lowerBoxes i).Mem ![q,AdaptiveGenerated.yLo i,z] ∧
    (AdaptiveGenerated.upperBoxes i).Mem ![q,AdaptiveGenerated.yHi i,z] := by
  fin_cases i <;>
    simp [AdaptiveGenerated.lowerBoxes,AdaptiveGenerated.upperBoxes,
      AdaptiveGenerated.yLo,AdaptiveGenerated.yHi,AdaptiveGenerated.graphBoxes,
      AdaptiveGenerated.zLo,AdaptiveGenerated.zHi,QBox.Mem,QInterval.Mem,
      sharpLower,sharpUpper] at * <;>
    constructor <;> intro j <;> fin_cases j <;> norm_num at * <;> omega

theorem adaptive_position_exists {z : ℝ} (hz : z ∈ tiltBox) :
    ∃ y ∈ Icc (-(937/1000)) (-(179/200)), familyY qStar (y,z)=0 := by
  obtain ⟨i,hi⟩ := adaptive_grid_cover hz
  have hends := graph_endpoint_mem i ⟨qStar_bracket.1.le,qStar_bracket.2.le⟩ hi
  have hlo := AdaptiveGenerated.lower_sign i _ hends.1
  have hhi := AdaptiveGenerated.upper_sign i _ hends.2
  have hy := AdaptiveGenerated.graph_local i
  have hc := (familyY_continuous_y qStar_mem hz).mono
    (show Icc (AdaptiveGenerated.yLo i) (AdaptiveGenerated.yHi i) ⊆
      Icc (-(937/1000:ℝ)) (-(179/200)) from fun y h => ⟨hy.1.trans h.1,h.2.trans hy.2.2⟩)
  obtain ⟨y,hym,hy0⟩ := intermediate_value_Icc hy.2.1.le hc
    (show (0:ℝ) ∈ Icc (familyY qStar (AdaptiveGenerated.yLo i,z))
      (familyY qStar (AdaptiveGenerated.yHi i,z)) from ⟨hlo.le,hhi.le⟩)
  exact ⟨y,⟨hy.1.trans hym.1,hym.2.trans hy.2.2⟩,hy0⟩

def adaptiveY (z : ℝ) (hz : z ∈ tiltBox) : ℝ := Classical.choose (adaptive_position_exists hz)
def adaptiveData (z : ℝ) (hz : z ∈ tiltBox) : Coordinates :=
  radicalCoordinates qStar (adaptiveY z hz) z

theorem adaptiveY_mem {z : ℝ} (hz : z ∈ tiltBox) :
    adaptiveY z hz ∈ Icc (-(937/1000)) (-(179/200)) :=
  (Classical.choose_spec (adaptive_position_exists hz)).1

theorem adaptiveY_zero {z : ℝ} (hz : z ∈ tiltBox) :
    familyY qStar (adaptiveY z hz,z)=0 :=
  (Classical.choose_spec (adaptive_position_exists hz)).2

theorem adaptiveY_unique {z y : ℝ} (hz : z ∈ tiltBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200))) (hzero : familyY qStar (y,z)=0) :
    y=adaptiveY z hz := by
  have hm := adaptiveY_mem hz
  have hzero' := adaptiveY_zero hz
  rcases le_total y (adaptiveY z hz) with h | h
  · have hh := familyY_slope qStar_mem hz hy hm h
    linarith
  · have hh := familyY_slope qStar_mem hz hm hy h
    linarith

theorem adaptive_graph_mem {z : ℝ} (hz : z ∈ tiltBox) :
    ∃ i : Fin 256, (AdaptiveGenerated.graphBoxes i).Mem ![qStar,adaptiveY z hz,z] := by
  obtain ⟨i,hi⟩ := adaptive_grid_cover hz
  have he := graph_endpoint_mem i ⟨qStar_bracket.1.le,qStar_bracket.2.le⟩ hi
  have hlo := AdaptiveGenerated.lower_sign i _ he.1
  have hhi := AdaptiveGenerated.upper_sign i _ he.2
  have hyl := AdaptiveGenerated.graph_local i
  have hlo' : AdaptiveGenerated.yLo i < adaptiveY z hz := by
    by_contra! h
    have hm := familyY_slope qStar_mem hz (adaptiveY_mem hz)
      ⟨hyl.1,hyl.2.1.le.trans hyl.2.2⟩ h
    change familyY qStar (AdaptiveGenerated.yLo i,z)<0 at hlo
    linarith [adaptiveY_zero hz]
  have hhi' : adaptiveY z hz < AdaptiveGenerated.yHi i := by
    by_contra! h
    have hm := familyY_slope qStar_mem hz ⟨hyl.1.trans hyl.2.1.le,hyl.2.2⟩
      (adaptiveY_mem hz) h
    change 0<familyY qStar (AdaptiveGenerated.yHi i,z) at hhi
    linarith [adaptiveY_zero hz]
  refine ⟨i,?_⟩
  intro j; fin_cases j
  · exact (AdaptiveGenerated.graph_shape i).2 ⟨qStar_bracket.1.le,qStar_bracket.2.le⟩
  · exact ⟨hlo'.le,hhi'.le⟩
  · exact (AdaptiveGenerated.graph_z i z).2 hi

theorem adaptive_local_mem {z : ℝ} (hz : z ∈ tiltBox) :
    localBox.Mem ![qStar,adaptiveY z hz,z] := local_mem qStar_mem ⟨adaptiveY_mem hz,hz⟩

theorem adaptive_chain {z : ℝ} (hz : z ∈ tiltBox) : (adaptiveData z hz).IsChain :=
  radical_isChain (adaptive_local_mem hz)

theorem adaptive_weightDomain {z : ℝ} (hz : z ∈ tiltBox) :
    (adaptiveData z hz).WeightDomain := radical_weightDomain (adaptive_local_mem hz)

theorem adaptive_position_stationary {z : ℝ} (hz : z ∈ tiltBox) :
    (adaptiveData z hz).positionDerivative=0 := by
  rw [← familyY_radical (adaptive_chain hz)]
  exact adaptiveY_zero hz

theorem adaptive_curvature {z : ℝ} (hz : z ∈ tiltBox) :
    (z-sharpData.z)^2/8 ≤ (adaptiveData z hz).defect := by
  have h := family_strong_convex qStar_mem (minimizingPose_mem qStar)
    ⟨adaptiveY_mem hz,hz⟩
  rw [sharpPose_value,sharpPose_stationary.1,sharpPose_stationary.2] at h
  rw [familyValue_radical] at h
  dsimp [adaptiveData,sharpData,radicalCoordinates] at *
  nlinarith [sq_nonneg (adaptiveY z hz-sharpPose.1)]

theorem adaptive_sharp : adaptiveData sharpData.z
    (by exact (minimizingPose_mem qStar).2) = sharpData := by
  have hy := adaptiveY_unique (z:=sharpData.z) (y:=sharpData.y)
    (by exact (minimizingPose_mem qStar).2) (minimizingPose_mem qStar).1
    sharpPose_stationary.1
  simp [adaptiveData,sharpData,hy]

namespace Coordinates

def edgeAlpha (d : Coordinates) : ℝ := d.lam 0
def edgeBeta (d : Coordinates) : ℝ := d.lam 1
def edgeDelta (d : Coordinates) : ℝ := d.lam 3
def edgeOmega (d : Coordinates) : ℝ := d.lam 4
def edgeEpsilon (d : Coordinates) : ℝ := d.lam 6
def cutY (d : Coordinates) : ℝ := d.x₁-d.x₂
def cutJ (d : Coordinates) : ℝ := d.edgeEpsilon*d.c/d.edgeBeta-d.y₃*d.x₄/d.x₃
def cutX (d : Coordinates) : ℝ := d.edgeBeta*(d.y+2+d.cutJ)
def cutK (d : Coordinates) : ℝ := d.edgeBeta*(d.y₃+d.cutJ)
def cutL (d : Coordinates) : ℝ := d.edgeEpsilon*d.s*d.y₄/d.x₄
def h₂tilt (d : Coordinates) : ℝ := -d.c*(d.x₄+1)-d.s*d.y₄
def cutN (d : Coordinates) : ℝ := -d.edgeEpsilon*(d.h₁+d.h₂tilt)
def ownerReserve (d : Coordinates) : Fin 9 → ℝ :=
  ![d.cutX,d.edgeAlpha*(1-d.cutY)-d.cutX,d.cutK,d.edgeBeta-d.cutK,
    d.edgeBeta*(-917/1000-d.cutJ),d.edgeBeta*(1057/1000+d.cutJ),
    d.cutL,d.cutN-(392/1000)*d.edgeOmega,(485/1000)*d.edgeOmega-d.cutN]

theorem cut_identities {d : Coordinates} (hw : d.WeightDomain)
    (hy : d.positionDerivative=0) :
    d.cutK=d.edgeEpsilon*d.c+d.edgeDelta*(d.x₄-d.x₃) ∧
      d.cutL=d.edgeDelta-d.edgeEpsilon*d.c ∧
      d.edgeDelta*d.x₃= -d.edgeBeta*d.y₃ := by
  have hlast := d.last_force_residual hw
  rw [hy,zero_div] at hlast
  have hx₃ := ne_of_lt hw.x₃_neg
  have hx₄ := ne_of_lt hw.x₄_neg
  have hm := ne_of_gt hw.weightMass_pos
  have hbeta := ne_of_gt (hw.lam_pos 1)
  constructor
  · dsimp [cutK,cutJ,edgeBeta,edgeDelta,edgeEpsilon,lam,rawLambda,
      rawDelta,rawMuD] at *
    field_simp [hx₃,hx₄,hm,hbeta]
    ring
  constructor
  · dsimp [cutL,edgeDelta,edgeEpsilon,lam,rawLambda]
    dsimp [rawMuE] at hlast
    field_simp [hx₄] at hlast
    field_simp [hm,hx₄]
    nlinarith [hlast]
  · dsimp [edgeDelta,edgeBeta,lam,rawLambda,rawDelta,rawMuD]
    field_simp [hm,hx₃]
    ring

end Coordinates

end SquaresInCircles.Eight.ExactFamily
