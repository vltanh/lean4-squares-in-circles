module

public import SquaresInCircles.Eight.ExactFamily.Stationary
public import SquaresInCircles.Eight.ExactFamily.Generated.AdaptiveBounds

/-!
# Eight squares: the adaptive chain at every tilt

For each half-angle tangent `z` of the tilt in `tiltBox = [1/20, 81/1000]`, the adaptive chain
`adaptiveData z` is the chain at the squared radius `qStar` with the tilt `z` and the position
`adaptiveY z` at which the derivative of the defect in the position vanishes. That position is a
zero given by the intermediate value theorem: the fixed cover of 256 graph boxes of
`Generated/AdaptiveFormula.lean` covers the stationary graph, and `Generated/AdaptiveBounds.lean`
gives the derivative opposite signs at the two ends of the position interval of each box
(`adaptive_position_exists`). As
the derivative increases in the position with slope at least `6` (`familyY_slope`), the chosen
zero lies in the graph box of its tilt (`adaptive_graph_mem`). The defect of the adaptive chain
is at least `(z - z*)²/8` (`adaptive_curvature`). The file ends with the contact weights of the
edges and the nine owner reserves (`ownerReserve`), which the same cover bounds below.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.ExactFamily
open Arithmetic Generated

def tiltBox : Set ℝ := Icc (1/20) (81/1000)

theorem uniform_grid_cover (n : ℕ) (hn : 0<n) {l w x : ℝ} (hx : l ≤ x ∧ x ≤ l+(n:ℝ)*w) :
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
    (w:=31/256000) (x:=z) (by
      have hz' : (1/20:ℝ) ≤ z ∧ z ≤ 81/1000 := hz
      norm_num
      exact hz')
  exact ⟨i,by simpa [AdaptiveGenerated.zLo,AdaptiveGenerated.zHi,mul_comm] using hi⟩

theorem familyYY_derivative {q y z : ℝ} (hq : q ∈ radiusBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200))) (hz : z ∈ tiltBox) :
    HasDerivAt (fun r => familyY q (r,z)) (familyYY q (y,z)) y := by
  have hr := (family_regular hq (⟨hy,hz⟩ : (y,z) ∈ poseBox)).2.1
  have hd := Formula.hasDerivAt_partial FyFormula 1 ![q,y,z] hr
  rw [Fyy_diff] at hd
  have hfun : (fun t => FyFormula.eval (Function.update ![q,y,z] 1 t)) =
      (fun r => familyY q (r,z)) := by
    funext r
    simp only [familyY]
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  rw [hfun] at hd
  exact hd

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
      convert (familyYY_derivative hq ⟨hy.1.le,hy.2.le⟩ hz).fun_sub
        ((hasDerivAt_id' y).const_mul 6) using 1; ring)
    (fun y hy => by
      have hh := (hessian_data hq (⟨⟨hy.1.le,hy.2.le⟩,hz⟩ : (y,z) ∈ poseBox)).1
      linarith only [hh])
  have hh := hm ha hb hab
  dsimp only at hh
  linarith only [hh]

set_option maxRecDepth 4000 in
/-- The two endpoint boxes of every graph box: the radius and tilt intervals
of the graph box, and the lower or upper end of its position interval.  The
quantifier is unrolled over the 256 boxes and the numerals are compared. -/
private theorem Adaptive.endpoint_box_data : ∀ i : Fin 256,
    AdaptiveGenerated.lowerBoxes i 0 = ⟨97888353437936878163/25000000000000000000,
      97888353437936885663/25000000000000000000⟩ ∧
    AdaptiveGenerated.lowerBoxes i 1 = ⟨(AdaptiveGenerated.graphBoxes i 1).lo,
      (AdaptiveGenerated.graphBoxes i 1).lo⟩ ∧
    AdaptiveGenerated.lowerBoxes i 2 = ⟨1/20+31/256000*i.val, 1/20+31/256000*(i.val+1)⟩ ∧
    AdaptiveGenerated.upperBoxes i 0 = ⟨97888353437936878163/25000000000000000000,
      97888353437936885663/25000000000000000000⟩ ∧
    AdaptiveGenerated.upperBoxes i 1 = ⟨(AdaptiveGenerated.graphBoxes i 1).hi,
      (AdaptiveGenerated.graphBoxes i 1).hi⟩ ∧
    AdaptiveGenerated.upperBoxes i 2 = ⟨1/20+31/256000*i.val, 1/20+31/256000*(i.val+1)⟩ := by
  simp (config := {maxSteps := 1000000}) only [Fin.forall_fin_succ, AdaptiveGenerated.lowerBoxes,
    AdaptiveGenerated.upperBoxes, AdaptiveGenerated.graphBoxes, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, IsEmpty.forall_iff, and_true, true_and, Fin.val_zero, Fin.val_succ,
    QInterval.mk.injEq, Nat.reduceAdd, Nat.cast_ofNat]
  norm_num1
  simp only [and_self]

theorem graph_endpoint_mem (i : Fin 256) {q z : ℝ}
    (hq : sharpLower ≤ q ∧ q ≤ sharpUpper)
    (hz : AdaptiveGenerated.zLo i ≤ z ∧ z ≤ AdaptiveGenerated.zHi i) :
    (AdaptiveGenerated.lowerBoxes i).Mem ![q,AdaptiveGenerated.yLo i,z] ∧
    (AdaptiveGenerated.upperBoxes i).Mem ![q,AdaptiveGenerated.yHi i,z] := by
  obtain ⟨hl0,hl1,hl2,hu0,hu1,hu2⟩ := Adaptive.endpoint_box_data i
  have hq' := hq
  norm_num [sharpLower,sharpUpper] at hq'
  have hz' := hz
  simp only [AdaptiveGenerated.zLo,AdaptiveGenerated.zHi] at hz'
  constructor <;> intro j <;> fin_cases j <;>
    simp only [Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val,hl0,hl1,hl2,hu0,hu1,hu2,
      QInterval.Mem,AdaptiveGenerated.yLo,AdaptiveGenerated.yHi] <;>
    push_cast <;> first | exact hq' | exact hz' | exact ⟨le_rfl,le_rfl⟩

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
    linarith only [adaptiveY_zero hz, hz, h, hm, hlo]
  have hhi' : adaptiveY z hz < AdaptiveGenerated.yHi i := by
    by_contra! h
    have hm := familyY_slope qStar_mem hz ⟨hyl.1.trans hyl.2.1.le,hyl.2.2⟩
      (adaptiveY_mem hz) h
    change 0<familyY qStar (AdaptiveGenerated.yHi i,z) at hhi
    linarith only [adaptiveY_zero hz, hz, h, hm, hhi]
  refine ⟨i,?_⟩
  intro j; fin_cases j
  · exact (AdaptiveGenerated.graph_shape i).2 ⟨qStar_bracket.1.le,qStar_bracket.2.le⟩
  · exact ⟨hlo'.le,hhi'.le⟩
  · exact (AdaptiveGenerated.graph_z i z).2 hi

theorem adaptive_local_mem {z : ℝ} (hz : z ∈ tiltBox) :
    localBox.Mem ![qStar,adaptiveY z hz,z] :=
  local_mem qStar_mem (⟨adaptiveY_mem hz,hz⟩ : (adaptiveY z hz,z) ∈ poseBox)

theorem adaptive_chain {z : ℝ} (hz : z ∈ tiltBox) : (adaptiveData z hz).IsChain :=
  radical_isChain (adaptive_local_mem hz)

theorem adaptive_weightDomain {z : ℝ} (hz : z ∈ tiltBox) :
    (adaptiveData z hz).WeightDomain := radical_weightDomain (adaptive_local_mem hz)

theorem adaptive_position_stationary {z : ℝ} (hz : z ∈ tiltBox) :
    (adaptiveData z hz).positionDerivative=0 :=
  (familyY_radical (adaptive_chain hz)).symm.trans (adaptiveY_zero hz)

theorem adaptive_curvature {z : ℝ} (hz : z ∈ tiltBox) :
    (z-sharpData.z)^2/8 ≤ (adaptiveData z hz).defect := by
  have h := family_strong_convex (a:=sharpPose) (b:=(adaptiveY z hz,z)) qStar_mem
    (minimizingPose_mem qStar) ⟨adaptiveY_mem hz,hz⟩
  rw [sharpPose_value,sharpPose_stationary.1,sharpPose_stationary.2] at h
  rw [familyValue_radical] at h
  dsimp [adaptiveData,sharpData,radicalCoordinates] at *
  linarith only [sq_nonneg (adaptiveY z hz-sharpPose.1), hz, h]

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
  rw [hy,neg_zero,zero_div] at hlast
  have hx₃ := ne_of_lt hw.x₃_neg
  have hx₄ := ne_of_lt hw.x₄_neg
  have hm := ne_of_gt hw.weightMass_pos
  have hbeta := ne_of_gt (hw.lam_pos 1)
  have hβ := ne_of_gt hw.rawBeta_pos
  constructor
  · dsimp [cutK,cutJ,edgeBeta,edgeDelta,edgeEpsilon,lam,rawLambda,
      rawDelta,rawMuD] at *
    field_simp [hx₃,hx₄,hm,hbeta,hβ]
    ring
  constructor
  · dsimp [cutL,edgeDelta,edgeEpsilon,lam,rawLambda]
    dsimp [rawMuE] at hlast
    field_simp [hx₄] at hlast
    field_simp [hm,hx₄]
    linarith only [hlast]
  · dsimp [edgeDelta,edgeBeta,lam,rawLambda,rawDelta,rawMuD]
    field_simp [hm,hx₃]

end Coordinates

end SquaresInCircles.Eight.ExactFamily
