import SquaresInCircles.Six.Analytic.MixedCardinalWest.Endpoints
import SquaresInCircles.Six.Analytic.SecondaryReduction
import SquaresInCircles.Six.Stress.Reverse

/-!
# Actual-packing exclusion of the cardinal/cardinal mixed west-wing case

One fixed stress has weights (2,4,3,3) on C--W,C--S,W--D,D--S. Its pair
normals are D-secondary and S-secondary. Every exterior support is the
universally valid far-vertex support, weakened only by an explicit signed
projection bound on the width. No cap condition is guessed.

The scalar minorant is positive by the preceding whole-domain concavity proof.
This closes the cardinal/cardinal subcase of MissingWestWing. It does not
assert the remaining OWN subcases or the other mixed-source exclusion.
Compilation and kernel acceptance remain deferred.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.MixedCardinalWest
open Normalization

def forceW (d : ℝ) : Point := (-2-3*Real.sin d,3*Real.cos d)
def forceD (s d : ℝ) : Point := (3*Real.sin d-3*Real.cos s,-3*Real.cos d-3*Real.sin s)
def forceS (s : ℝ) : Point := (3*Real.cos s,-4+3*Real.sin s)

def upperW (w d : ℝ) : ℝ := R0*Real.sqrt (13+12*Real.sin d)-
  (2*Real.cos w+2*Real.sin w+3*(Real.sin (d-w)+Real.cos (d-w)))/2

def upperD (s d : ℝ) : ℝ := R0*Real.sqrt (18-18*Real.sin (d-s))-
  (3*Real.cos (d-s)+3-3*Real.sin (d-s))/2

def upperS (s : ℝ) : ℝ := R0*Real.sqrt (25-24*Real.sin s)-
  (4*Real.cos s+3-4*Real.sin s)/2

def system (w s d : ℝ) : Stress.System 4 4 where
  source := ![0,0,1,2]
  target := ![1,3,2,3]
  normal := ![(-1,0),(0,-1),(Real.sin d,-Real.cos d),(Real.cos s,Real.sin s)]
  weight := ![2,4,3,3]
  threshold := ![1/2+angularWidth w,1/2+angularWidth s,
    1/2+angularWidth (d-w),1/2+angularWidth (Real.pi/2+s-d)]

def upperValues (w s d : ℝ) : Fin 4 → ℝ := ![6*c0,upperW w d,upperD s d,upperS s]

lemma system_nonnegative (w s d : ℝ) : (system w s d).Nonnegative := by
  intro i
  fin_cases i <;> norm_num [system]

lemma system_forces (w s d : ℝ) (i : Fin 4) :
    (system w s d).force i = ![(2,4),forceW d,forceD s d,forceS s] i := by
  fin_cases i <;> apply Prod.ext <;>
    simp [Stress.System.force,system,forceW,forceD,forceS,Fin.sum_univ_succ] <;> ring

private lemma forceW_norm (d : ℝ) : normSq (forceW d)=13+12*Real.sin d := by
  dsimp [normSq,forceW]
  linear_combination 9*(Real.sin_sq_add_cos_sq d)

private lemma forceD_norm (s d : ℝ) : normSq (forceD s d)=18-18*Real.sin (d-s) := by
  dsimp [normSq,forceD]
  rw [Real.sin_sub]
  linear_combination 9*(Real.sin_sq_add_cos_sq d)+9*(Real.sin_sq_add_cos_sq s)

private lemma forceS_norm (s : ℝ) : normSq (forceS s)=25-24*Real.sin s := by
  dsimp [normSq,forceS]
  linear_combination 9*(Real.sin_sq_add_cos_sq s)

private lemma width_from_minus (S : UnitSquare) (g : Point) :
    (frameX S g-frameY S g)/2 ≤ width S g := by
  dsimp [width]
  linarith [le_abs_self (frameX S g),neg_le_abs (frameY S g)]

private lemma width_from_plus (S : UnitSquare) (g : Point) :
    (frameX S g+frameY S g)/2 ≤ width S g := by
  dsimp [width]
  linarith [le_abs_self (frameX S g),le_abs_self (frameY S g)]

lemma west_support {w d a b : ℝ} (hc : ContainedChart a |b|) :
    dot (forceW d) (orientedSquare (Real.pi+w) a b).center ≤ upperW w d := by
  have h := Stress.center_le_vertexSupport R0_nonneg (oriented_contained_of_chart hc) (forceW d)
  have hw := width_from_minus (orientedSquare (Real.pi+w) a b) (forceW d)
  have hx : frameX (orientedSquare (Real.pi+w) a b) (forceW d)=
      2*Real.cos w+3*Real.sin (d-w) := by
    simp only [frameX,orientedSquare,forceW,Real.cos_pi_add,Real.sin_pi_add,Real.sin_sub]
    ring
  have hy : frameY (orientedSquare (Real.pi+w) a b) (forceW d)=
      -2*Real.sin w-3*Real.cos (d-w) := by
    simp only [frameY,orientedSquare,forceW,Real.cos_pi_add,Real.sin_pi_add,Real.cos_sub]
    ring
  rw [hx,hy] at hw
  dsimp [Stress.vertexSupport,Stress.vectorLength] at h
  rw [forceW_norm] at h
  dsimp [upperW]
  linarith

lemma diagonal_support {s d a b : ℝ} (hc : ContainedChart a |b|) :
    dot (forceD s d) (orientedSquare (Real.pi+d) a b).center ≤ upperD s d := by
  have h := Stress.center_le_vertexSupport R0_nonneg (oriented_contained_of_chart hc) (forceD s d)
  have hw := width_from_plus (orientedSquare (Real.pi+d) a b) (forceD s d)
  have hx : frameX (orientedSquare (Real.pi+d) a b) (forceD s d)=3*Real.cos (d-s) := by
    simp only [frameX,orientedSquare,forceD,Real.cos_pi_add,Real.sin_pi_add,Real.cos_sub]
    ring
  have hy : frameY (orientedSquare (Real.pi+d) a b) (forceD s d)=3-3*Real.sin (d-s) := by
    simp only [frameY,orientedSquare,forceD,Real.cos_pi_add,Real.sin_pi_add,Real.sin_sub]
    linear_combination 3*(Real.sin_sq_add_cos_sq d)
  rw [hx,hy] at hw
  dsimp [Stress.vertexSupport,Stress.vectorLength] at h
  rw [forceD_norm] at h
  dsimp [upperD]
  linarith

lemma south_support {s a b : ℝ} (hc : ContainedChart a |b|) :
    dot (forceS s) (orientedSquare (3*Real.pi/2+s) a b).center ≤ upperS s := by
  have h := Stress.center_le_vertexSupport R0_nonneg (oriented_contained_of_chart hc) (forceS s)
  have hw := width_from_plus (orientedSquare (3*Real.pi/2+s) a b) (forceS s)
  have hx : frameX (orientedSquare (3*Real.pi/2+s) a b) (forceS s)=4*Real.cos s := by
    simp only [frameX,orientedSquare,forceS,Real.cos_add,Real.sin_add,south_cos,south_sin]
    ring
  have hy : frameY (orientedSquare (3*Real.pi/2+s) a b) (forceS s)=3-4*Real.sin s := by
    simp only [frameY,orientedSquare,forceS,Real.cos_add,Real.sin_add,south_cos,south_sin]
    linear_combination 3*(Real.sin_sq_add_cos_sq s)
  rw [hx,hy] at hw
  dsimp [Stress.vertexSupport,Stress.vectorLength] at h
  rw [forceS_norm] at h
  dsimp [upperS]
  linarith

private lemma sin_abs_difference (x : ℝ) : |x|-x=2*max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx,max_eq_right (by linarith)]
    ring
  · rw [abs_of_neg (lt_of_not_ge hx),max_eq_left (by linarith)]
    ring

/-- The defect of the actual incidence system is exactly the proved scalar
minorant after its signed universal support bounds, not a new support branch. -/
lemma system_gap {w s d : ℝ}
    (hw : -(2/5) ≤ w ∧ w ≤ 0) (hs : -(2/5) ≤ s ∧ s ≤ 2/5)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    (system w s d).thresholdSum-(∑ i,upperValues w s d i)=gap w s d := by
  have hcw : 0 ≤ Real.cos w := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hw.1,Real.pi_gt_d2],by linarith [hw.2,Real.pi_pos]⟩).le
  have hsw : Real.sin w ≤ 0 := by
    have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := -w)
      (by linarith [hw.2]) (by linarith [hw.1,Real.pi_gt_d2])
    rw [Real.sin_neg] at h
    linarith
  have hcs : 0 ≤ Real.cos s := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hs.1,Real.pi_gt_d2],by linarith [hs.2,Real.pi_gt_d2]⟩).le
  have hq : 0 ≤ d-w ∧ d-w ≤ Real.pi/2 := by
    constructor <;> linarith [hw.1,hw.2,hd.1,hd.2,Real.pi_gt_d2]
  have hx : 0 ≤ d-s ∧ d-s ≤ Real.pi/2 := by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2,Real.pi_gt_d2]
  have hcq : 0 ≤ Real.cos (d-w) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hq.1,Real.pi_pos],hq.2⟩
  have hsq := Real.sin_nonneg_of_nonneg_of_le_pi hq.1 (by linarith [hq.2,Real.pi_pos])
  have hcx : 0 ≤ Real.cos (d-s) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
  have hsx := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])
  have hwidthW : angularWidth w=(Real.cos w-Real.sin w)/2 := by
    simp [angularWidth,abs_of_nonneg hcw,abs_of_nonpos hsw]
  have hwidthS : angularWidth s=(Real.cos s+|Real.sin s|)/2 := by
    simp [angularWidth,abs_of_nonneg hcs]
  have hwidthQ : angularWidth (d-w)=(Real.cos (d-w)+Real.sin (d-w))/2 := by
    simp [angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq]
  have hwidthX : angularWidth (Real.pi/2+s-d)=(Real.cos (d-s)+Real.sin (d-s))/2 := by
    rw [show Real.pi/2+s-d=Real.pi/2-(d-s) by ring]
    simp [angularWidth,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
      abs_of_nonneg hcx,abs_of_nonneg hsx,add_comm]
  have hpos := sin_abs_difference (Real.sin s)
  simp only [Stress.System.thresholdSum,system,upperValues,Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp only [hwidthW,hwidthS,hwidthQ,hwidthX]
  dsimp [gap,southTerm,diagonalTerm,westTerm,upperW,upperD,upperS]
  nlinarith only [hpos]

/-- The cardinal/cardinal part of the genuine MissingWestWing predicate is
impossible on the full normalized domain, including source ties. -/
theorem not_missing_west {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) : ¬ MissingWestWing P := by
  intro hmissing
  let w := P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hw : -(2/5) ≤ w ∧ w ≤ 0 := by
    have hb := abs_lt.mp (P.cardinal_angle 2 hW)
    have hwall := hmissing.phase_wall
    dsimp [w]
    constructor <;> linarith [hb.1,hwall,P.diagonal_angle_range.2]
  have hs : -(2/5) ≤ s ∧ s ≤ 2/5 := by
    have h := abs_lt.mp (P.cardinal_angle 4 hS)
    exact ⟨h.1.le,h.2.le⟩
  have hd : 1/2 ≤ d ∧ d ≤ Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hWphase : P.phase 2=Real.pi+w := P.phase_from_deviation 2
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hDphase : P.phase 3=Real.pi+d := by dsimp [d,NormalizedPacking.diagonalAngle]; ring
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
    · have h := P.cardinal_separator 4 hS
      rw [hSphase] at h
      simp only [centralMargin,centerY,angularWidth,Real.cos_add,Real.sin_add,south_cos,
        south_sin,zero_mul,neg_one_mul,add_zero,zero_add,abs_neg] at h
      dsimp [system,Sq,dot,sub]
      rw [P.square_def 4,hSphase]
      dsimp [orientedSquare,axisSquare,angularWidth]
      simp only [Real.cos_add,Real.sin_add,south_cos,south_sin]
      nlinarith
    · have h := hmissing.from_diagonal
      rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,
        show (Real.pi+d)-(Real.pi+w)=d-w by ring] at h
      simpa [system,Sq,P.square_def,hWphase,hDphase,normalY,orientedSquare,
        Real.cos_pi_add,Real.sin_pi_add] using h
    · have h := hmissing.south_wing
      rw [P.square_def 3,P.square_def 4,hDphase,hSphase,oriented_pair_threshold,
        show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2+s-d by ring] at h
      simpa [system,Sq,P.square_def,hSphase,hDphase,normalY,orientedSquare,
        Real.cos_add,Real.sin_add,south_cos,south_sin] using h
  have hu (i : Fin 4) : dot ((system w s d).force i) (Sq i).center ≤ upperValues w s d i := by
    rw [system_forces]
    fin_cases i
    · dsimp [Sq,upperValues,axisSquare,dot]
      linarith [P.box.1.2,P.box.2.2]
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
  rw [system_gap hw hs hd] at hnonpos
  linarith [positive hw hs hd]

/-- The candidate west wing is therefore forced when both central wing choices
are cardinal. The other central-bit combinations remain separate obligations. -/
theorem west_wing {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) :
    Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) := by
  by_contra h
  exact not_missing_west P hW hS (missing_west_of_failure P h)

end SquaresInCircles.Six.Analytic.MixedCardinalWest
