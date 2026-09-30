import SquaresInCircles.Six.Stress.FixedReification

/-!
# Actual packing semantics of fixed classification stresses

The arithmetic stress uses only C,W,D,S, with the exact same directed axes as
the original square SAT. Both central signs and every pair half-width are
accounted for. No assumption that a numerical checker succeeded is exposed to
this interface.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress.FixedSpec
open Normalization Normalization.Certificates

lemma angularWidth_neg (t : ℝ) : angularWidth (-t)=angularWidth t := by
  simp [angularWidth,Real.cos_neg,Real.sin_neg,abs_neg]

lemma angularWidth_pi_add (t : ℝ) : angularWidth (Real.pi+t)=angularWidth t := by
  simp [angularWidth,Real.cos_pi_add,Real.sin_pi_add,abs_neg]

lemma angularWidth_half_pi_add (t : ℝ) : angularWidth (Real.pi/2+t)=angularWidth t := by
  simp [angularWidth,Real.cos_add,Real.sin_add,abs_neg,add_comm]

lemma angularWidth_three_half_pi_add (t : ℝ) :
    angularWidth (3*Real.pi/2+t)=angularWidth t := by
  rw [show 3*Real.pi/2+t=Real.pi+(Real.pi/2+t) by ring,
    angularWidth_pi_add,angularWidth_half_pi_add]

/-- Virtual frames used by the scalar evaluator have the actual square frames. -/
def actualSquares {R : ℝ} (P : NormalizedPacking R) : Fin 4 → UnitSquare :=
  ![axisSquare P.center,P.square 2,P.square 3,P.square 4]

lemma actualSquares_frame {R : ℝ} (P : NormalizedPacking R) (i : Fin 4) :
    (actualSquares P i).cosine=(frame (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle i).cosine ∧
    (actualSquares P i).sine=(frame (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle i).sine := by
  have hW : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hS : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hD : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [NormalizedPacking.diagonalAngle]; ring
  fin_cases i <;> simp [actualSquares,NormalizedPacking.square,NormalizedPacking.model,
    PinPacking.model,pinModel,frame,phase,axisSquare,orientedSquare,hW,hD,hS]

lemma actualSquares_support {R : ℝ} (P : NormalizedPacking R) (i : Fin 4) (g : Point) :
    exactSupport R0 (actualSquares P i) g=
      exactSupport R0 (frame (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle i) g := by
  have h := actualSquares_frame P i
  simp only [exactSupport,frameX,frameY,h.1,h.2]

lemma fixed_wd_normal {R : ℝ} (P : NormalizedPacking R) (s : FixedSpec) :
    s.normal (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle 3=
      Stress.pairNormal s.wdAxis (P.square 2) (P.square 3) := by
  have hW : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hD : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [NormalizedPacking.diagonalAngle]; ring
  fin_cases h : s.wdAxis <;>
    simp [normal,basis,sign,basisVector,wdBasis,axisSign,h,phase,
      primary,secondary,scale,Stress.pairNormal,normalX,normalY,
      P.square_def,hW,hD,orientedSquare]

lemma fixed_ds_normal {R : ℝ} (P : NormalizedPacking R) (s : FixedSpec) :
    s.normal (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle 4=
      Stress.pairNormal s.dsAxis (P.square 3) (P.square 4) := by
  have hS : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hD : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [NormalizedPacking.diagonalAngle]; ring
  fin_cases h : s.dsAxis <;>
    simp [normal,basis,sign,basisVector,dsBasis,axisSign,h,phase,
      primary,secondary,scale,Stress.pairNormal,normalX,normalY,
      P.square_def,hS,hD,orientedSquare]

lemma fixed_wd_threshold {R : ℝ} (P : NormalizedPacking R) :
    halfWidths (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle 3=
      Seven.SAT.threshold (P.square 2) (P.square 3) := by
  rw [P.square_def 2,P.square_def 3,oriented_pair_threshold]
  have he : P.phase 3-P.phase 2=P.diagonalAngle-P.helperAngle 2 := by
    dsimp [NormalizedPacking.diagonalAngle,NormalizedPacking.helperAngle,matchingCardinal,cardinalCenter]
    ring
  rw [he]
  rfl

lemma fixed_ds_threshold {R : ℝ} (P : NormalizedPacking R) :
    halfWidths (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle 4=
      Seven.SAT.threshold (P.square 3) (P.square 4) := by
  rw [P.square_def 3,P.square_def 4,oriented_pair_threshold]
  have he : P.phase 4-P.phase 3=Real.pi/2+(-(P.diagonalAngle-P.helperAngle 4)) := by
    dsimp [NormalizedPacking.diagonalAngle,NormalizedPacking.helperAngle,matchingCardinal,cardinalCenter]
    ring
  rw [he,angularWidth_half_pi_add,angularWidth_neg]
  rfl

lemma fixed_central_W (c : Point) (w a b : ℝ) (card : Bool) :
    dot (if card then (1,0) else scale (-1) (primary (Real.pi+w)))
      (sub c (orientedSquare (Real.pi+w) a b).center)-(1/2+angularWidth w)=
      centralMargin (if card then .west else .own) (Real.pi+w) a b c.1 c.2 := by
  cases card
  · have h := primary_difference (Real.pi+w) a b c.1 c.2
    dsimp [frameX,sub,orientedSquare,centralNormal] at h
    simp only [centralMargin,angularWidth_pi_add]
    dsimp [dot,scale,primary,sub,orientedSquare,centralNormal]
    nlinarith
  · simp only [centralMargin,angularWidth_pi_add]
    dsimp [dot,sub,orientedSquare,centerX]
    ring

lemma fixed_central_S (c : Point) (t a b : ℝ) (card : Bool) :
    dot (if card then (0,1) else scale (-1) (primary (3*Real.pi/2+t)))
      (sub c (orientedSquare (3*Real.pi/2+t) a b).center)-(1/2+angularWidth t)=
      centralMargin (if card then .south else .own) (3*Real.pi/2+t) a b c.1 c.2 := by
  cases card
  · have h := primary_difference (3*Real.pi/2+t) a b c.1 c.2
    dsimp [frameX,sub,orientedSquare,centralNormal] at h
    simp only [centralMargin,angularWidth_three_half_pi_add]
    dsimp [dot,scale,primary,sub,orientedSquare,centralNormal]
    nlinarith
  · simp only [centralMargin,angularWidth_three_half_pi_add]
    dsimp [dot,sub,orientedSquare,centerY]
    ring

lemma fixed_central_D (c : Point) (d a b : ℝ) :
    dot (scale (-1) (primary (Real.pi+d)))
      (sub c (orientedSquare (Real.pi+d) a b).center)-(1/2+angularWidth d)=
      centralMargin .own (Real.pi+d) a b c.1 c.2 :=
  fixed_central_W c d a b false

/-- Actual active-edge hypotheses of a fixed row. Central bits are required
only for edges carrying positive weight. -/
def Realized {R : ℝ} (s : FixedSpec) (P : NormalizedPacking R) : Prop :=
  (s.weight 0≠0 → P.ownBits 2=(!s.westCardinal)) ∧
  (s.weight 1≠0 → P.ownBits 4=(!s.southCardinal)) ∧
  (s.weight 3≠0 → Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    dot (Stress.pairNormal s.wdAxis (P.square 2) (P.square 3))
      (sub (P.square 3).center (P.square 2).center)) ∧
  (s.weight 4≠0 → Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    dot (Stress.pairNormal s.dsAxis (P.square 3) (P.square 4))
      (sub (P.square 4).center (P.square 3).center))

lemma realized_separators {R : ℝ} (s : FixedSpec) (P : NormalizedPacking R)
    (hs : s.Realized P) (e : Fin 5) (he : s.weight e≠0) :
    halfWidths (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle e ≤
      dot (s.normal (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle e)
        (sub (actualSquares P (target e)).center (actualSquares P (source e)).center) := by
  have hW : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hS : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hD : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [NormalizedPacking.diagonalAngle]; ring
  fin_cases e
  · have hb := hs.1 he
    have hm : 0≤centralMargin (if s.westCardinal then .west else .own)
        (P.phase 2) (P.radial 2) (P.transverse 2) P.center.1 P.center.2 := by
      cases h : s.westCardinal
      · exact P.own_separator 2 (by simpa [h] using hb)
      · exact P.cardinal_separator 2 (by simpa [h] using hb)
    rw [hW,← fixed_central_W] at hm
    cases h : s.westCardinal <;>
      simpa [normal,basis,sign,basisVector,phase,halfWidths,actualSquares,source,target,
        primary,secondary,scale,P.square_def,h,hW,sub_nonneg] using hm
  · have hb := hs.2.1 he
    have hm : 0≤centralMargin (if s.southCardinal then .south else .own)
        (P.phase 4) (P.radial 4) (P.transverse 4) P.center.1 P.center.2 := by
      cases h : s.southCardinal
      · exact P.own_separator 4 (by simpa [h] using hb)
      · exact P.cardinal_separator 4 (by simpa [h] using hb)
    rw [hS,← fixed_central_S] at hm
    cases h : s.southCardinal <;>
      simpa [normal,basis,sign,basisVector,phase,halfWidths,actualSquares,source,target,
        primary,secondary,scale,P.square_def,h,hS,sub_nonneg] using hm
  · have hm := P.own_separator 3 P.diagonal_own
    rw [hD,← fixed_central_D] at hm
    simpa [normal,basis,sign,basisVector,phase,halfWidths,actualSquares,source,target,
      primary,scale,P.square_def,hD,sub_nonneg] using hm
  · rw [fixed_wd_threshold,fixed_wd_normal]
    exact hs.2.2.1 he
  · rw [fixed_ds_threshold,fixed_ds_normal]
    exact hs.2.2.2 he

/-- Feasibility always makes the fixed-row reverse defect nonpositive. -/
theorem defect_nonpos_of_packing {R : ℝ} (s : FixedSpec) (hv : s.valid)
    (P : NormalizedPacking R) (hs : s.Realized P) :
    s.defect (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle ≤ 0 := by
  apply nonpos_of_realized s hv _ _ _ (actualSquares P) (s.realized_separators P hs)
  intro i
  fin_cases i
  · exact Stress.center_le_boxSupport P.box _
  · rw [support,← actualSquares_support P 1]
    exact center_le_exactSupport (by linarith [R0_gt_three_halves])
      (oriented_contained_of_chart (P.contained 2)) _
  · rw [support,← actualSquares_support P 2]
    exact center_le_exactSupport (by linarith [R0_gt_three_halves])
      (oriented_contained_of_chart (P.contained 3)) _
  · rw [support,← actualSquares_support P 3]
    exact center_le_exactSupport (by linarith [R0_gt_three_halves])
      (oriented_contained_of_chart (P.contained 4)) _

end SquaresInCircles.Six.Stress.FixedSpec
