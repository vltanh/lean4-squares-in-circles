module
public import SquaresInCircles.Six.Equality.SupportRigidity
public import SquaresInCircles.Six.Equality.Reflection

@[expose] public section

/-!
# Complete equality reconstruction

Active support equality fixes the five exterior centers. The two positive
central contact multipliers then fix the central center. The cardinal frames
and the diagonal frame are compared as actual open and closed square sets;
no equality of oriented-square records is assumed when their side frames
represent the same square.
-/

noncomputable section
namespace SquaresInCircles.Six.Equality
open Stress Normalization

lemma cos_five_pi_fourths : Real.cos (5*Real.pi/4)= -Six.hStar := by
  rw [show 5*Real.pi/4=Real.pi+Real.pi/4 by ring,Real.cos_pi_add]
  simp [Six.hStar,halfDiagonal]

lemma sin_five_pi_fourths : Real.sin (5*Real.pi/4)= -Six.hStar := by
  rw [show 5*Real.pi/4=Real.pi+Real.pi/4 by ring,Real.sin_pi_add]
  simp [Six.hStar,halfDiagonal]

lemma rhoStar_mul_hStar : rhoStar*Six.hStar=Six.dStar := by
  rw [rhoStar_eq_two_h_d]
  linear_combination (2*Six.dStar)*Six.hStar_sq

def exteriorCenters : Fin 5 → Point :=
  ![(Six.sStar+1,Six.sStar),(Six.sStar,Six.sStar+1),(Six.sStar-1,Six.tStar),
    (-Six.dStar,-Six.dStar),(Six.tStar,Six.sStar-1)]

lemma candidate_exterior_centers {R : ℝ} (P : NormalizedPacking R)
    (ha : CandidateAngles P) (hc : CandidateCenterCoordinates P) (i : Fin 5) :
    (P.square i).center=exteriorCenters i := by
  obtain ⟨he,hn,hw,hd,hs⟩ := candidate_phases P ha
  fin_cases i
  · rw [P.square_def,he,hc.east_radial,hc.east_transverse]
    apply Prod.ext <;> simp [orientedSquare,exteriorCenters] <;> ring
  · rw [P.square_def,hn,hc.north_radial,hc.north_transverse]
    apply Prod.ext <;> simp [orientedSquare,exteriorCenters] <;> ring
  · rw [P.square_def,hw,hc.west_radial,hc.west_transverse]
    apply Prod.ext <;> simp [orientedSquare,exteriorCenters] <;> ring
  · rw [P.square_def,hd,hc.diagonal_radial,hc.diagonal_transverse]
    apply Prod.ext <;> simp [orientedSquare,exteriorCenters,cos_five_pi_fourths,
      sin_five_pi_fourths,rhoStar_mul_hStar]
  · rw [P.square_def,hs,hc.south_radial,hc.south_transverse]
    apply Prod.ext <;> simp [orientedSquare,exteriorCenters,south_cos,south_sin] <;> ring

/-- The central center is fixed by the two tight positive CN/CE contacts. -/
lemma candidate_central_center {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar)
    (u v : Fin 4) (hsel : BalancedSelected P u v) (ha : CandidateAngles P)
    (hc : CandidateCenterCoordinates P) (hzero : balancedDefect P u v=0) :
    P.center=(Six.sStar,Six.sStar) := by
  have hCE := balanced_separator_tight P hR u v hsel hzero 1
  have hCN := balanced_separator_tight P hR u v hsel hzero 0
  have haxes := balanced_center_axes P
  have hEaxis : balancedCenterAxis P 0=(1,0) := by rw [haxes.1,ha.1]; simp
  have hNaxis : balancedCenterAxis P 1=(0,1) := by rw [haxes.2.1,ha.2.1]; simp
  have hEthreshold : Seven.SAT.threshold (P.model 0) (P.model 1)=1 := by
    rw [balanced_threshold_center P 0,ha.1]
    norm_num [angularWidth]
  have hNthreshold : Seven.SAT.threshold (P.model 0) (P.model 2)=1 := by
    rw [balanced_threshold_center P 1,ha.2.1]
    norm_num [angularWidth]
  change dot (balancedCenterAxis P 0) (sub (P.square 0).center P.center)=
    Seven.SAT.threshold (P.model 0) (P.model 1) at hCE
  change dot (balancedCenterAxis P 1) (sub (P.square 1).center P.center)=
    Seven.SAT.threshold (P.model 0) (P.model 2) at hCN
  rw [hEaxis,hEthreshold,candidate_exterior_centers P ha hc 0] at hCE
  rw [hNaxis,hNthreshold,candidate_exterior_centers P ha hc 1] at hCN
  dsimp [dot,sub,exteriorCenters] at hCE hCN
  apply Prod.ext <;> linarith

/-- Cardinal side frames define the same square as the axis-aligned frame. -/
lemma cardinal_frame_open (S : UnitSquare)
    (h : (S.cosine=1 ∧ S.sine=0) ∨ (S.cosine=0 ∧ S.sine=1) ∨
      (S.cosine= -1 ∧ S.sine=0) ∨ (S.cosine=0 ∧ S.sine= -1)) (p : Point) :
    openSquare S p ↔ openSquare (axisSquare S.center) p := by
  rcases h with ⟨hc,hs⟩ | ⟨hc,hs⟩ | ⟨hc,hs⟩ | ⟨hc,hs⟩
  all_goals simp [openSquare,localX,localY,axisSquare,hc,hs,abs_neg,and_comm]

lemma opposite_frame_open (S T : UnitSquare)
    (hc : S.center=T.center) (hcos : S.cosine= -T.cosine) (hsin : S.sine= -T.sine) (p : Point) :
    openSquare S p ↔ openSquare T p := by
  have hx : localX S p= -localX T p := by
    dsimp [localX]
    rw [hc,hcos,hsin]
    ring
  have hy : localY S p= -localY T p := by
    dsimp [localY]
    rw [hc,hcos,hsin]
    ring
  simp only [openSquare,hx,hy,abs_neg]

/-- Candidate order C,N,E,W,S,D versus normalized order C,E,N,W,D,S. -/
def candidateOrder : Equiv.Perm (Fin 6) where
  toFun := ![0,2,1,3,5,4]
  invFun := ![0,2,1,3,5,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

lemma candidate_model_open {R : ℝ} (P : NormalizedPacking R)
    (ha : CandidateAngles P) (hc : CandidateCenterCoordinates P)
    (hcenter : P.center=(Six.sStar,Six.sStar)) (i : Fin 6) (p : Point) :
    openSquare (P.model (candidateOrder i)) p ↔ openSquare (Six.model i) p := by
  obtain ⟨he,hn,hw,hd,hs⟩ := candidate_phases P ha
  fin_cases i
  · change openSquare (axisSquare P.center) p ↔ openSquare (axisSquare (Six.sStar,Six.sStar)) p
    rw [hcenter]
  · change openSquare (P.square 1) p ↔ openSquare (axisSquare (Six.sStar,Six.sStar+1)) p
    have hf : (P.square 1).cosine=0 ∧ (P.square 1).sine=1 := by
      rw [P.square_def,hn]
      simp [orientedSquare]
    have ho := cardinal_frame_open (P.square 1) (Or.inr (Or.inl hf)) p
    rw [candidate_exterior_centers P ha hc 1] at ho
    exact ho
  · change openSquare (P.square 0) p ↔ openSquare (axisSquare (Six.sStar+1,Six.sStar)) p
    have hf : (P.square 0).cosine=1 ∧ (P.square 0).sine=0 := by
      rw [P.square_def,he]
      simp [orientedSquare]
    have ho := cardinal_frame_open (P.square 0) (Or.inl hf) p
    rw [candidate_exterior_centers P ha hc 0] at ho
    exact ho
  · change openSquare (P.square 2) p ↔ openSquare (axisSquare (Six.sStar-1,Six.tStar)) p
    have hf : (P.square 2).cosine= -1 ∧ (P.square 2).sine=0 := by
      rw [P.square_def,hw]
      simp [orientedSquare]
    have ho := cardinal_frame_open (P.square 2) (Or.inr (Or.inr (Or.inl hf))) p
    rw [candidate_exterior_centers P ha hc 2] at ho
    exact ho
  · change openSquare (P.square 4) p ↔ openSquare (axisSquare (Six.tStar,Six.sStar-1)) p
    have hf : (P.square 4).cosine=0 ∧ (P.square 4).sine= -1 := by
      rw [P.square_def,hs]
      simp [orientedSquare,south_cos,south_sin]
    have ho := cardinal_frame_open (P.square 4) (Or.inr (Or.inr (Or.inr hf))) p
    rw [candidate_exterior_centers P ha hc 4] at ho
    exact ho
  · change openSquare (P.square 3) p ↔ openSquare diagonalSquare p
    apply opposite_frame_open (P.square 3) diagonalSquare
    · exact candidate_exterior_centers P ha hc 3
    · rw [P.square_def,hd]
      simp [orientedSquare,diagonalSquare,cos_five_pi_fourths]
    · rw [P.square_def,hd]
      simp [orientedSquare,diagonalSquare,sin_five_pi_fourths]

/-- Complete reconstruction in the normalized frame, with both open and closed
point sets in the unchanged Congruent predicate. -/
theorem normalized_congruent_candidate {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar) :
    Congruent P.model (0,0) Six.model := by
  obtain ⟨u,v,hsel,ha,hsrc,hzero,_⟩ := normalized_candidate_data P hR
  have hc := candidate_center_coordinates P hR u v hsel ha hsrc hzero
  have hcenter := candidate_central_center P hR u v hsel ha hc hzero
  have ho (i : Fin 6) (p : Point) :
      openSquare (P.model (candidateOrder i)) p ↔ openSquare (Six.model i) p :=
    candidate_model_open P ha hc hcenter i p
  exact congruent_of_origin_sets candidateOrder ho
    (fun i => same_open_same_closed _ _ (ho i))

end SquaresInCircles.Six.Equality
