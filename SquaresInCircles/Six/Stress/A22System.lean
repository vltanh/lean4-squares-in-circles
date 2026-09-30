module
public import SquaresInCircles.Six.Classification.CandidateTails
public import SquaresInCircles.Six.Stress.CandidateStressConstants
public import SquaresInCircles.Six.Stress.StrictSupport
public import SquaresInCircles.Six.Analytic.ElementaryTrig

@[expose] public section

/-!
# The variable adjacent-pair stress for Patterns 12 and 13

This is the geometric half of (A22-factor). The selected N/W and S/E source
axes come from the interior pins, while the D edges are the candidate graph.
The angle-dependent central multipliers cancel the force on C exactly.

The numerator/denominator sign proofs now use the analytic shifted-sine
identity in Analytic.ElementaryTrig. No sign formula, root box, or finite
certificate is used here. The imported candidate-graph classification still
has computational dependencies; this change does not claim to remove those.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization Classification

lemma a22_w_sign {w : ℝ} (hw : -2/3≤w ∧ w≤5/8) :
    0<Real.cos w ∧ 0<Real.cos w+Real.sin w :=
  Analytic.west_stress_sign hw

lemma a22_e_sign {e : ℝ} (he : -5/12≤e ∧ e≤3/10) :
    0<Real.cos e ∧ 0<Real.cos e+Real.sin e :=
  Analytic.east_stress_sign he

def a22MuN (w : ℝ) : ℝ := (Real.cos w+Real.sin w)/Real.cos w
def a22MuW (w : ℝ) : ℝ := 1/Real.cos w

def a22MuE (own : Bool) (e : ℝ) : ℝ :=
  if own then 1/Real.cos e else 1

def a22MuS (own : Bool) (e : ℝ) : ℝ :=
  if own then (Real.cos e+Real.sin e)/Real.cos e else 1

def a22CE {R : ℝ} (P : NormalizedPacking R) : Point :=
  if P.ownBits 0 then normalX (P.square 0) else (1,0)

/-- Eight edges: C-N, C-E, C-W, C-S, W-N, S-E, W-D, D-S. -/
def a22System {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) : System 6 8 where
  source := ![0,0,0,0,3,5,3,4]
  target := ![2,1,3,5,2,1,4,5]
  normal := ![
    (0,1),
    a22CE P,
    normalX (P.square 2),
    (0,-1),
    preferredPairAxis NWsigns (P.square 2) (P.square 1) u,
    preferredPairAxis ESsigns (P.square 4) (P.square 0) v,
    normalY (P.square 2),
    normalY (P.square 4)]
  weight := ![
    a22MuN (P.helperAngle 2),
    a22MuE (P.ownBits 0) (P.helperAngle 0),
    a22MuW (P.helperAngle 2),
    a22MuS (P.ownBits 0) (P.helperAngle 0),
    rStar,rStar,mStar,mStar]
  threshold := fun k =>
    Seven.SAT.threshold (P.model (![0,0,0,0,3,5,3,4] k))
      (P.model (![2,1,3,5,2,1,4,5] k))

lemma a22_weights_nonnegative {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    (a22System P u v).Nonnegative := by
  have hw0 := P.helper_windows.2.2.1
  have he0 := P.helper_windows.1
  have hw := a22_w_sign ⟨hw0.1.le,hw0.2.le⟩
  have he := a22_e_sign ⟨he0.1.le,he0.2.le⟩
  intro k
  fin_cases k
  · exact (div_pos hw.2 hw.1).le
  · cases h : P.ownBits 0 <;>
      simp [a22System,a22MuE,h,he.1.le]
  · exact (div_pos (by norm_num) hw.1).le
  · cases h : P.ownBits 0 <;>
      simp [a22System,a22MuS,h,he.1.le,he.2.le]
  · exact rStar_pos.le
  · exact rStar_pos.le
  · exact mStar_pos.le
  · exact mStar_pos.le

private lemma model_zero {R : ℝ} (P : NormalizedPacking R) :
    P.model 0=axisSquare P.center := rfl

private lemma model_succ {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) :
    P.model i.succ=P.square i := rfl

lemma selected_CN {R : ℝ} (P : NormalizedPacking R) (hN : P.ownBits 1=false) :
    Seven.SAT.threshold (P.model 0) (P.model 2) ≤
      dot (0,1) (sub (P.model 2).center (P.model 0).center) := by
  have h := P.cardinal_separator 1 hN
  rw [model_zero,model_succ,central_threshold]
  rw [P.square_def 1]
  dsimp [centralMargin,centerY,dot,sub,axisSquare,orientedSquare] at h ⊢
  linarith

lemma selected_CE {R : ℝ} (P : NormalizedPacking R) :
    Seven.SAT.threshold (P.model 0) (P.model 1) ≤
      dot (a22CE P) (sub (P.model 1).center (P.model 0).center) := by
  cases hE : P.ownBits 0
  · have h := P.cardinal_separator 0 hE
    rw [model_zero,model_succ,central_threshold]
    rw [P.square_def 0]
    simp only [a22CE,hE,Bool.false_eq_true,if_false]
    dsimp [centralMargin,centerX,dot,sub,axisSquare,orientedSquare] at h ⊢
    linarith
  · have h := P.own_separator 0 hE
    rw [model_zero,model_succ,central_threshold]
    rw [P.square_def 0]
    simp only [a22CE,hE,if_true,normalX]
    rw [primary_difference]
    dsimp [centralMargin]
    linarith

lemma selected_CW_own {R : ℝ} (P : NormalizedPacking R) (hW : P.ownBits 2=true) :
    Seven.SAT.threshold (P.model 0) (P.model 3) ≤
      dot (normalX (P.square 2)) (sub (P.model 3).center (P.model 0).center) := by
  have h := P.own_separator 2 hW
  rw [model_zero,model_succ,central_threshold]
  rw [P.square_def 2]
  rw [primary_difference]
  dsimp [centralMargin]
  linarith

lemma selected_CS {R : ℝ} (P : NormalizedPacking R) (hS : P.ownBits 4=false) :
    Seven.SAT.threshold (P.model 0) (P.model 5) ≤
      dot (0,-1) (sub (P.model 5).center (P.model 0).center) := by
  have h := P.cardinal_separator 4 hS
  rw [model_zero,model_succ,central_threshold]
  rw [P.square_def 4]
  dsimp [centralMargin,centerY,dot,sub,axisSquare,orientedSquare] at h ⊢
  linarith

lemma selected_WD_candidate {R : ℝ} (P : NormalizedPacking R)
    (h : DWSelected P 2) :
    Seven.SAT.threshold (P.model 3) (P.model 4) ≤
      dot (normalY (P.square 2)) (sub (P.model 4).center (P.model 3).center) := by
  simpa only [model_succ,Stress.pairNormal] using h

lemma selected_DS_candidate {R : ℝ} (P : NormalizedPacking R)
    (h : DSSelected P 6) :
    Seven.SAT.threshold (P.model 4) (P.model 5) ≤
      dot (normalY (P.square 4)) (sub (P.model 5).center (P.model 4).center) := by
  simpa only [model_succ,Stress.pairNormal] using h

theorem a22_separates {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4)
    (hN : P.ownBits 1=false) (hW : P.ownBits 2=true) (hS : P.ownBits 4=false)
    (hu : Seven.SAT.threshold (P.square 2) (P.square 1) ≤
      dot (preferredPairAxis NWsigns (P.square 2) (P.square 1) u)
        (sub (P.square 1).center (P.square 2).center))
    (hv : Seven.SAT.threshold (P.square 4) (P.square 0) ≤
      dot (preferredPairAxis ESsigns (P.square 4) (P.square 0) v)
        (sub (P.square 0).center (P.square 4).center)) :
    (a22System P u v).Separates P.model := by
  have hg := candidate_diagonal_edges P
  intro k
  fin_cases k
  · simpa [a22System] using selected_CN P hN
  · simpa [a22System] using selected_CE P
  · simpa [a22System] using selected_CW_own P hW
  · simpa [a22System] using selected_CS P hS
  · simpa [a22System,model_succ] using hu
  · simpa [a22System,model_succ] using hv
  · simpa [a22System] using selected_WD_candidate P hg.1
  · simpa [a22System] using selected_DS_candidate P hg.2.1

lemma a22_central_force_zero {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    (a22System P u v).force 0=(0,0) := by
  have hw0 := P.helper_windows.2.2.1
  have he0 := P.helper_windows.1
  have hw := a22_w_sign ⟨hw0.1.le,hw0.2.le⟩
  have he := a22_e_sign ⟨he0.1.le,he0.2.le⟩
  have hW : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hE : P.phase 0=P.helperAngle 0 := by
    simpa only [matchingCardinal,cardinalCenter,zero_add] using P.phase_from_deviation 0
  apply Prod.ext <;>
    simp [System.force,a22System,a22CE,a22MuN,a22MuW,a22MuE,a22MuS,
      P.square_def,hW,hE,normalX,orientedSquare,Real.cos_pi_add,Real.sin_pi_add]
  all_goals
    split <;>
    field_simp [ne_of_gt hw.1,ne_of_gt he.1] <;>
    ring

def a22Upper {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) (i : Fin 6) : ℝ :=
  if i=0 then 0 else exactSupport Six.radius (P.model i) ((a22System P u v).force i)

def a22Defect {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) : ℝ :=
  (a22System P u v).thresholdSum-∑ i, a22Upper P u v i

theorem a22_defect_nonpos {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar)
    (u v : Fin 4)
    (hN : P.ownBits 1=false) (hW : P.ownBits 2=true) (hS : P.ownBits 4=false)
    (hu : Seven.SAT.threshold (P.square 2) (P.square 1) ≤
      dot (preferredPairAxis NWsigns (P.square 2) (P.square 1) u)
        (sub (P.square 1).center (P.square 2).center))
    (hv : Seven.SAT.threshold (P.square 4) (P.square 0) ≤
      dot (preferredPairAxis ESsigns (P.square 4) (P.square 0) v)
        (sub (P.square 0).center (P.square 4).center)) :
    a22Defect P u v≤0 := by
  apply (a22System P u v).defect_nonpos P.model (a22Upper P u v)
    (a22_weights_nonnegative P u v) (a22_separates P u v hN hW hS hu hv)
  intro i
  fin_cases i
  · simp [a22Upper,a22_central_force_zero,dot]
  · rw [a22Upper,if_neg (by decide)]
    apply center_le_exactSupport radius_gt_half
    simpa only [model_succ] using P.toPinPacking.contained_in_candidate_disk hR 0
  · rw [a22Upper,if_neg (by decide)]
    apply center_le_exactSupport radius_gt_half
    simpa only [model_succ] using P.toPinPacking.contained_in_candidate_disk hR 1
  · rw [a22Upper,if_neg (by decide)]
    apply center_le_exactSupport radius_gt_half
    simpa only [model_succ] using P.toPinPacking.contained_in_candidate_disk hR 2
  · rw [a22Upper,if_neg (by decide)]
    apply center_le_exactSupport radius_gt_half
    simpa only [model_succ] using P.toPinPacking.contained_in_candidate_disk hR 3
  · rw [a22Upper,if_neg (by decide)]
    apply center_le_exactSupport radius_gt_half
    simpa only [model_succ] using P.toPinPacking.contained_in_candidate_disk hR 4

end SquaresInCircles.Six.Stress
