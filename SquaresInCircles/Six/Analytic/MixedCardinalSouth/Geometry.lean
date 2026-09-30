module
public import SquaresInCircles.Six.Analytic.MixedCardinalSouth.Scalar
public import SquaresInCircles.Six.Analytic.SecondaryReduction
public import SquaresInCircles.Six.Stress.Reverse

@[expose] public section

/-!
# A cardinal W rules out the second mixed source below s=12/25

Only CW, WD and DS enter the stress. There is no cardinal-S hypothesis.
The conclusion therefore includes every cardinal/cardinal case and all
OWN-S cases below the stated bound. A remaining missing-south configuration
with cardinal W must be in the large positive OWN-S tail.

Every source inequality is taken from the actual MissingSouthWing predicate;
no support branch is assumed. The generic stress sum uses the universal vertex
supports and the scalar concavity theorem from Scalar.lean. Compilation remains
deferred; this does not assert completion of the remaining tail.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.MixedCardinalSouth
open Normalization

def forceW (w : ℝ) : Point := (-4-3*Real.sin w,3*Real.cos w)
def forceD (w d : ℝ) : Point := (3*Real.sin w-3*Real.sin d,-3*Real.cos w+3*Real.cos d)
def forceS (d : ℝ) : Point := (3*Real.sin d,-3*Real.cos d)

def upperW (w : ℝ) : ℝ := R0*Real.sqrt (25+24*Real.sin w)-
  (4*Real.cos w+4*Real.sin w+3)/2

def upperD (w d : ℝ) : ℝ := R0*Real.sqrt (18-18*Real.cos (d-w))-
  (3*Real.sin (d-w)+3-3*Real.cos (d-w))/2

def upperS (s d : ℝ) : ℝ := 3*R0-(3/2)*(Real.cos (d-s)+Real.sin (d-s))

def system (w s d : ℝ) : Stress.System 4 3 where
  source := ![0,1,2]
  target := ![1,2,3]
  normal := ![(-1,0),(Real.sin w,-Real.cos w),(Real.sin d,-Real.cos d)]
  weight := ![4,3,3]
  threshold := ![1/2+angularWidth w,1/2+angularWidth (d-w),
    1/2+angularWidth (Real.pi/2+s-d)]

def upperValues (w s d : ℝ) : Fin 4 → ℝ := ![4*c0,upperW w,upperD w d,upperS s d]

lemma system_nonnegative (w s d : ℝ) : (system w s d).Nonnegative := by
  intro i
  fin_cases i <;> norm_num [system]

lemma system_forces (w s d : ℝ) (i : Fin 4) :
    (system w s d).force i = ![(4,0),forceW w,forceD w d,forceS d] i := by
  fin_cases i <;> apply Prod.ext <;>
    simp [Stress.System.force,system,forceW,forceD,forceS,Fin.sum_univ_succ] <;> ring

private lemma forceW_norm (w : ℝ) : normSq (forceW w)=25+24*Real.sin w := by
  dsimp [normSq,forceW]
  linear_combination 9*(Real.sin_sq_add_cos_sq w)

private lemma forceD_norm (w d : ℝ) : normSq (forceD w d)=18-18*Real.cos (d-w) := by
  dsimp [normSq,forceD]
  rw [Real.cos_sub]
  linear_combination 9*(Real.sin_sq_add_cos_sq d)+9*(Real.sin_sq_add_cos_sq w)

private lemma forceS_norm (d : ℝ) : normSq (forceS d)=9 := by
  dsimp [normSq,forceS]
  linear_combination 9*(Real.sin_sq_add_cos_sq d)

private lemma width_minus (S : UnitSquare) (g : Point) :
    (frameX S g-frameY S g)/2 ≤ width S g := by
  dsimp [width]
  linarith [le_abs_self (frameX S g),neg_le_abs (frameY S g)]

private lemma width_plus (S : UnitSquare) (g : Point) :
    (frameX S g+frameY S g)/2 ≤ width S g := by
  dsimp [width]
  linarith [le_abs_self (frameX S g),le_abs_self (frameY S g)]

lemma west_support {w a b : ℝ} (hc : ContainedChart a |b|) :
    dot (forceW w) (orientedSquare (Real.pi+w) a b).center ≤ upperW w := by
  have h := Stress.center_le_vertexSupport R0_nonneg (oriented_contained_of_chart hc) (forceW w)
  have hw := width_minus (orientedSquare (Real.pi+w) a b) (forceW w)
  have hx : frameX (orientedSquare (Real.pi+w) a b) (forceW w)=4*Real.cos w := by
    simp only [frameX,orientedSquare,forceW,Real.cos_pi_add,Real.sin_pi_add]
    ring
  have hy : frameY (orientedSquare (Real.pi+w) a b) (forceW w)=-4*Real.sin w-3 := by
    simp only [frameY,orientedSquare,forceW,Real.cos_pi_add,Real.sin_pi_add]
    linear_combination -3*(Real.sin_sq_add_cos_sq w)
  rw [hx,hy] at hw
  dsimp [Stress.vertexSupport,Stress.vectorLength] at h
  rw [forceW_norm] at h
  dsimp [upperW]
  linarith

lemma diagonal_support {w d a b : ℝ} (hc : ContainedChart a |b|) :
    dot (forceD w d) (orientedSquare (Real.pi+d) a b).center ≤ upperD w d := by
  have h := Stress.center_le_vertexSupport R0_nonneg (oriented_contained_of_chart hc) (forceD w d)
  have hw := width_minus (orientedSquare (Real.pi+d) a b) (forceD w d)
  have hx : frameX (orientedSquare (Real.pi+d) a b) (forceD w d)=3*Real.sin (d-w) := by
    simp only [frameX,orientedSquare,forceD,Real.cos_pi_add,Real.sin_pi_add,Real.sin_sub]
    ring
  have hy : frameY (orientedSquare (Real.pi+d) a b) (forceD w d)=3*Real.cos (d-w)-3 := by
    simp only [frameY,orientedSquare,forceD,Real.cos_pi_add,Real.sin_pi_add,Real.cos_sub]
    linear_combination -3*(Real.sin_sq_add_cos_sq d)
  rw [hx,hy] at hw
  dsimp [Stress.vertexSupport,Stress.vectorLength] at h
  rw [forceD_norm] at h
  dsimp [upperD]
  linarith

lemma south_support {s d a b : ℝ} (hc : ContainedChart a |b|) :
    dot (forceS d) (orientedSquare (3*Real.pi/2+s) a b).center ≤ upperS s d := by
  have h := Stress.center_le_vertexSupport R0_nonneg (oriented_contained_of_chart hc) (forceS d)
  have hw := width_plus (orientedSquare (3*Real.pi/2+s) a b) (forceS d)
  have hx : frameX (orientedSquare (3*Real.pi/2+s) a b) (forceS d)=3*Real.cos (d-s) := by
    simp only [frameX,orientedSquare,forceS,Real.cos_add,Real.sin_add,south_cos,south_sin,
      Real.cos_sub]
    ring
  have hy : frameY (orientedSquare (3*Real.pi/2+s) a b) (forceS d)=3*Real.sin (d-s) := by
    simp only [frameY,orientedSquare,forceS,Real.cos_add,Real.sin_add,south_cos,south_sin,
      Real.sin_sub]
    ring
  rw [hx,hy] at hw
  dsimp [Stress.vertexSupport,Stress.vectorLength] at h
  rw [forceS_norm] at h
  norm_num at h
  dsimp [upperS]
  linarith

private lemma positive_part_identity (x : ℝ) : |x|+x=2*max x 0 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx,max_eq_left hx]
    ring
  · rw [abs_of_neg (lt_of_not_ge hx),max_eq_right (le_of_not_ge hx)]
    ring

lemma gap_le_defect {w s d : ℝ}
    (hw : -(2/5) ≤ w ∧ w ≤ 2/5) (hs : s ≤ 12/25)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (hsrc : Real.pi/4 ≤ Real.pi/2+s-d) :
    gap w d ≤ (system w s d).thresholdSum-(∑ i,upperValues w s d i) := by
  have hq : 0 ≤ d-w ∧ d-w ≤ 6/5 := by
    constructor <;> linarith [hw.1,hw.2,hd.1,hd.2,Real.pi_lt_d2]
  have hx : 0 ≤ d-s ∧ d-s ≤ Real.pi/4 := by
    constructor <;> linarith [hd.1,hs,hsrc]
  have hcw := Real.cos_nonneg_of_mem_Icc
    (show w ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hw.1,hw.2,Real.pi_gt_d2])
  have hcq := Real.cos_nonneg_of_mem_Icc
    (show d-w ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_gt_d2])
  have hsq := Real.sin_nonneg_of_nonneg_of_le_pi hq.1
    (by linarith [hq.2,Real.pi_gt_d2])
  have hcx := Real.cos_nonneg_of_mem_Icc
    (show d-s ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
  have hsx := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_pos])
  have hW : angularWidth w=(Real.cos w+|Real.sin w|)/2 := by
    simp [angularWidth,abs_of_nonneg hcw]
  have hQ : angularWidth (d-w)=(Real.cos (d-w)+Real.sin (d-w))/2 := by
    simp [angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq]
  have hX : angularWidth (Real.pi/2+s-d)=(Real.cos (d-s)+Real.sin (d-s))/2 := by
    rw [show Real.pi/2+s-d=Real.pi/2-(d-s) by ring]
    simp [angularWidth,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
      abs_of_nonneg hcx,abs_of_nonneg hsx,add_comm]
  have hnorm := chord_norm hq
  have hwidth := south_width_lower hd hs hsrc
  have hpos := positive_part_identity (Real.sin w)
  simp only [Stress.System.thresholdSum,system,upperValues,Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp only [hW,hQ,hX]
  dsimp [gap,westTerm,MixedCardinalWest.southTerm,chordTerm,widthTerm,upperW,upperD,upperS]
  rw [Real.cos_neg,Real.sin_neg,neg_neg,hnorm]
  nlinarith only [hwidth,hpos]

/-- No source-index or cardinal-S assumption is hidden in the result. -/
theorem not_missing_south {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.helperAngle 4 ≤ 12/25) : ¬ MissingSouthWing P := by
  intro hmissing
  let w := P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hw : -(2/5) ≤ w ∧ w ≤ 2/5 := by
    have h := abs_lt.mp (P.cardinal_angle 2 hW)
    exact ⟨h.1.le,h.2.le⟩
  have hd : 1/2 ≤ d ∧ d ≤ Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hWphase : P.phase 2=Real.pi+w := P.phase_from_deviation 2
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hDphase : P.phase 3=Real.pi+d := by dsimp [d,NormalizedPacking.diagonalAngle]; ring
  have hr : Real.pi/4 ≤ Real.pi/2+s-d := by
    have h := DS_Dsecondary_gap_gt_quarter P hmissing.from_diagonal
    rw [hSphase,hDphase] at h
    linarith
  let Sq : Fin 4 → UnitSquare := ![axisSquare P.center,P.square 2,P.square 3,P.square 4]
  have hsep : (system w s d).Separates Sq := by
    intro e
    fin_cases e
    · have h := P.cardinal_separator 2 hW
      rw [hWphase] at h
      simp only [centralMargin,centerX,angularWidth,Real.cos_pi_add,Real.sin_pi_add,abs_neg] at h
      dsimp [system,Sq,dot,sub]
      rw [P.square_def 2,hWphase]
      dsimp [orientedSquare,axisSquare,angularWidth]
      simp only [Real.cos_pi_add,Real.sin_pi_add]
      nlinarith
    · have h := hmissing.west_wing
      rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,
        show (Real.pi+d)-(Real.pi+w)=d-w by ring] at h
      simpa [system,Sq,P.square_def,hWphase,hDphase,normalY,orientedSquare,
        Real.cos_pi_add,Real.sin_pi_add] using h
    · have h := hmissing.from_diagonal
      rw [P.square_def 3,P.square_def 4,hDphase,hSphase,oriented_pair_threshold,
        show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2+s-d by ring] at h
      simpa [system,Sq,P.square_def,hSphase,hDphase,normalY,orientedSquare,
        Real.cos_pi_add,Real.sin_pi_add] using h
  have hu (i : Fin 4) : dot ((system w s d).force i) (Sq i).center ≤ upperValues w s d i := by
    rw [system_forces]
    fin_cases i
    · dsimp [Sq,upperValues,axisSquare,dot]
      linarith [P.box.1.2]
    · dsimp [Sq,upperValues]
      rw [P.square_def 2,hWphase]
      exact west_support (P.contained 2)
    · dsimp [Sq,upperValues]
      rw [P.square_def 3,hDphase]
      exact diagonal_support (P.contained 3)
    · dsimp [Sq,upperValues]
      rw [P.square_def 4,hSphase]
      exact south_support (P.contained 4)
  have hnonpos := (system w s d).defect_nonpos Sq (upperValues w s d)
    (system_nonnegative w s d) hsep hu
  have hlow := gap_le_defect hw hS hd hr
  linarith [positive hw hd]

theorem south_wing {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.helperAngle 4 ≤ 12/25) :
    Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center) := by
  by_contra h
  exact not_missing_south P hW hS (missing_south_of_failure P h)

/-- Both-cardinal sources are now excluded without the old fixed-row tables. -/
theorem not_missing_south_both_cardinal {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) : ¬ MissingSouthWing P := by
  apply not_missing_south P hW
  have h := (abs_lt.mp (P.cardinal_angle 4 hS)).2
  linarith

/-- The still-open cardinal-W case is confined to the large positive OWN-S tail. -/
theorem remaining_case_requires_south_tail {R : ℝ} {P : NormalizedPacking R}
    (h : MissingSouthWing P) (hW : P.ownBits 2=false) :
    P.ownBits 4=true ∧ 12/25 < P.helperAngle 4 := by
  have hs : 12/25 < P.helperAngle 4 := by
    by_contra! hs
    exact not_missing_south P hW hs h
  refine ⟨?_,hs⟩
  cases hbit : P.ownBits 4
  · have hsmall := (abs_lt.mp (P.cardinal_angle 4 hbit)).2
    linarith
  · rfl

end SquaresInCircles.Six.Analytic.MixedCardinalSouth
