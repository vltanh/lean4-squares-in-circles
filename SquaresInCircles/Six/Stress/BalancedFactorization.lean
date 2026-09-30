import SquaresInCircles.Six.Stress.BalancedProjections

/-!
# Exact factorization of the common reverse stress

The half-widths, including both constant diagonal halves, are counted exactly
once. The actual six-square defect is identified with two common pair values
and the exact diagonal contribution before any scalar lower bound is applied.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization Classification

@[simp] lemma balanced_width_neg (x : ℝ) : angularWidth (-x)=angularWidth x := by
  simp [angularWidth,Real.cos_neg,Real.sin_neg,abs_neg]

@[simp] lemma balanced_width_half_add (x : ℝ) : angularWidth (Real.pi/2+x)=angularWidth x := by
  simp [angularWidth,Real.cos_add,Real.sin_add,add_comm]

@[simp] lemma balanced_width_pi_add (x : ℝ) : angularWidth (Real.pi+x)=angularWidth x := by
  simp [angularWidth,Real.cos_pi_add,Real.sin_pi_add,abs_neg]

@[simp] lemma balanced_width_threehalf_add (x : ℝ) : angularWidth (3*Real.pi/2+x)=angularWidth x := by
  rw [show 3*Real.pi/2+x=Real.pi+(Real.pi/2+x) by ring,
    balanced_width_pi_add,balanced_width_half_add]

lemma balanced_width_sub_half (x : ℝ) : angularWidth (x-Real.pi/2)=angularWidth x := by
  have h := balanced_width_half_add (x-Real.pi/2)
  rw [show Real.pi/2+(x-Real.pi/2)=x by ring] at h
  exact h.symm

lemma balanced_width_sub_threehalf (x : ℝ) : angularWidth (x-3*Real.pi/2)=angularWidth x := by
  have h := balanced_width_threehalf_add (x-3*Real.pi/2)
  rw [show 3*Real.pi/2+(x-3*Real.pi/2)=x by ring] at h
  exact h.symm

lemma balanced_threshold_center {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) :
    Seven.SAT.threshold (P.model 0) (P.model i.succ)=1/2+angularWidth (P.helperAngle i) := by
  change Seven.SAT.threshold (axisSquare P.center)
    (orientedSquare (P.phase i) (P.radial i) (P.transverse i))=_
  rw [central_threshold,P.phase_from_deviation]
  fin_cases i <;> simp [matchingCardinal,cardinalCenter]

lemma balanced_threshold_NW {R : ℝ} (P : NormalizedPacking R) :
    Seven.SAT.threshold (P.model 3) (P.model 2)=
      1/2+angularWidth (P.helperAngle 1-P.helperAngle 2) := by
  change Seven.SAT.threshold (P.square 2) (P.square 1)=_
  rw [P.square_def 2,P.square_def 1,oriented_pair_threshold]
  have hn : P.phase 1=Real.pi/2+P.helperAngle 1 := P.phase_from_deviation 1
  have hw : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  rw [hn,hw,show (Real.pi/2+P.helperAngle 1)-(Real.pi+P.helperAngle 2)=
    (P.helperAngle 1-P.helperAngle 2)-Real.pi/2 by ring,balanced_width_sub_half]

lemma balanced_threshold_ES {R : ℝ} (P : NormalizedPacking R) :
    Seven.SAT.threshold (P.model 5) (P.model 1)=
      1/2+angularWidth ((-P.helperAngle 0)-(-P.helperAngle 4)) := by
  change Seven.SAT.threshold (P.square 4) (P.square 0)=_
  rw [P.square_def 4,P.square_def 0,oriented_pair_threshold]
  have he : P.phase 0=P.helperAngle 0 := by
    simpa [matchingCardinal,cardinalCenter] using P.phase_from_deviation 0
  have hs : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  rw [he,hs,show P.helperAngle 0-(3*Real.pi/2+P.helperAngle 4)=
    (P.helperAngle 0-P.helperAngle 4)-3*Real.pi/2 by ring,balanced_width_sub_threehalf]
  rw [show (-P.helperAngle 0)-(-P.helperAngle 4)= -(P.helperAngle 0-P.helperAngle 4) by ring,
    balanced_width_neg]

lemma balanced_threshold_WD {R : ℝ} (P : NormalizedPacking R) :
    Seven.SAT.threshold (P.model 3) (P.model 4)=
      1/2+angularWidth (P.diagonalAngle-P.helperAngle 2) := by
  change Seven.SAT.threshold (P.square 2) (P.square 3)=_
  rw [P.square_def 2,P.square_def 3,oriented_pair_threshold]
  have hw : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hd : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [NormalizedPacking.diagonalAngle]; ring
  rw [hw,hd,show (Real.pi+P.diagonalAngle)-(Real.pi+P.helperAngle 2)=
    P.diagonalAngle-P.helperAngle 2 by ring]

lemma balanced_threshold_DS {R : ℝ} (P : NormalizedPacking R) :
    Seven.SAT.threshold (P.model 4) (P.model 5)=
      1/2+angularWidth (P.diagonalAngle-P.helperAngle 4) := by
  change Seven.SAT.threshold (P.square 3) (P.square 4)=_
  rw [P.square_def 3,P.square_def 4,oriented_pair_threshold]
  have hs : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hd : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [NormalizedPacking.diagonalAngle]; ring
  rw [hs,hd,show (3*Real.pi/2+P.helperAngle 4)-(Real.pi+P.diagonalAngle)=
    Real.pi/2+(-(P.diagonalAngle-P.helperAngle 4)) by ring,
    balanced_width_half_add,balanced_width_neg]

lemma balanced_threshold_factorization {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    (balancedSystem P u v).thresholdSum=
      pairThreshold (P.ownBits 1) (P.ownBits 2) (P.helperAngle 1) (P.helperAngle 2)+
      pairThreshold (P.ownBits 0) (P.ownBits 4) (-P.helperAngle 0) (-P.helperAngle 4)+
      mStar*(angularWidth (P.diagonalAngle-P.helperAngle 2)+
        angularWidth (P.diagonalAngle-P.helperAngle 4)) := by
  have hN := balanced_threshold_center P 1
  have hE := balanced_threshold_center P 0
  have hW := balanced_threshold_center P 2
  have hS := balanced_threshold_center P 4
  have hNW := balanced_threshold_NW P
  have hES := balanced_threshold_ES P
  have hWD := balanced_threshold_WD P
  have hDS := balanced_threshold_DS P
  simp [System.thresholdSum,balancedSystem,Fin.sum_univ_succ,hN,hE,hW,hS,hNW,hES,hWD,hDS,
    pairThreshold,balancedAlpha,balancedBeta,balancedGamma,balancedDelta]
  ring

def balancedUpper {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) (i : Fin 6) : ℝ :=
  if i=0 then 0 else exactSupport Six.radius (P.model i) ((balancedSystem P u v).force i)

def balancedDefect {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) : ℝ :=
  (balancedSystem P u v).thresholdSum-∑ i,balancedUpper P u v i

@[simp] lemma balancedUpper_zero {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    balancedUpper P u v 0=0 := by simp [balancedUpper]

lemma balancedUpper_helper {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) (i : Fin 5) :
    balancedUpper P u v i.succ=
      scalarSupport Six.radius (projectAt (P.phase i) ((balancedSystem P u v).force i.succ)).1
        (projectAt (P.phase i) ((balancedSystem P u v).force i.succ)).2 := by
  have hi : i.succ≠0 := by intro h; have hv := congrArg Fin.val h; simp at hv
  rw [balancedUpper,if_neg hi]
  rfl

/-- Exact identity, before any inequality or preferred-source selection. -/
theorem balanced_defect_factorization {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    balancedDefect P u v=
      pairValue (P.ownBits 1) (P.ownBits 2) u (P.helperAngle 1) (P.helperAngle 2)+
      pairValue (P.ownBits 0) (P.ownBits 4) v (-P.helperAngle 0) (-P.helperAngle 4)+
      diagonalValue (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle := by
  have hE := balancedUpper_helper P u v 0
  have hN := balancedUpper_helper P u v 1
  have hW := balancedUpper_helper P u v 2
  have hD := balancedUpper_helper P u v 3
  have hS := balancedUpper_helper P u v 4
  rw [balanced_local_east,scalarSupport_reflectLocal] at hE
  rw [balanced_local_north] at hN
  rw [balanced_local_west] at hW
  rw [balanced_local_diagonal] at hD
  rw [balanced_local_south,scalarSupport_reflectLocal] at hS
  rw [balancedDefect,balanced_threshold_factorization]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,balancedUpper_zero,hE,hN,hW,hD,hS,
    pairValue,diagonalValue]
  ring

/-- The scalar supports in the factorization bound the centers of the actual
packing at the exact candidate radius. -/
lemma balanced_upper_bounds {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar)
    (u v : Fin 4) (i : Fin 6) :
    dot ((balancedSystem P u v).force i) (P.model i).center≤balancedUpper P u v i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [balanced_central_force_zero,balancedUpper_zero]
    norm_num [dot]
  · have hj : j.succ≠0 := by intro h; have hv := congrArg Fin.val h; simp at hv
    rw [balancedUpper,if_neg hj]
    exact center_le_exactSupport radius_gt_half
      (P.toPinPacking.contained_in_candidate_disk hR j) _

/-- The reverse inequality follows from the actual packing and selected axes. -/
theorem balanced_defect_nonpositive {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar)
    (u v : Fin 4) (hsel : BalancedSelected P u v) : balancedDefect P u v≤0 :=
  (balancedSystem P u v).defect_nonpos P.model (balancedUpper P u v)
    (balanced_weights_nonnegative P u v) (balanced_separates P u v hsel)
    (balanced_upper_bounds P hR u v)

end SquaresInCircles.Six.Stress
