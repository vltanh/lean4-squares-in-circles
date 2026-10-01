import SquaresInCircles.Six.Analytic.SelectedPairWork
import SquaresInCircles.Six.Equality.ContactCoordinates

/-!
# The eight contacts

Under `ReductionHypotheses`, a normalized packing in a disk of squared radius at
most `q*` has radius `√q*`, and its exterior squares have the phases of the
model. The separations of the stress are then the eight contact inequalities of
`ContactCoordinates`: C with E, N, W and S along the sides of C, N–W and E–S
along the axes selected for these pairs, which are now axes of the model, and
W–D and D–S along the secondary axes of W and S. With the containment of the
squares they fix the coordinates of all six squares.
-/

noncomputable section
namespace SquaresInCircles.Six.Equality.AnalyticContacts
open Stress Normalization Analytic Analytic.FixedPair

/-- The phases of the model: E, N, W and S along the four axes, D at `5π/4`. -/
structure Frame {R : ℝ} (P : NormalizedPacking R) : Prop where
  east : P.phase 0=0
  north : P.phase 1=Real.pi/2
  west : P.phase 2=Real.pi
  diagonal : P.phase 3=5*Real.pi/4
  south : P.phase 4=3*Real.pi/2

lemma frame_of_angles {R : ℝ} (P : NormalizedPacking R)
    (ha : P.helperAngle 0=0 ∧ P.helperAngle 1=0 ∧ P.helperAngle 2=0 ∧
      P.helperAngle 4=0 ∧ P.diagonalAngle=Real.pi/4) : Frame P := by
  obtain ⟨he,hn,hw,hs,hd⟩ := ha
  have hE := P.phase_from_deviation 0
  have hN := P.phase_from_deviation 1
  have hW := P.phase_from_deviation 2
  have hS := P.phase_from_deviation 4
  simp only [matchingCardinal,cardinalCenter,he,hn,hw,hs,add_zero] at hE hN hW hS
  have hD : P.phase 3=5*Real.pi/4 := by
    dsimp [NormalizedPacking.diagonalAngle] at hd
    linarith
  exact ⟨hE,hN,hW,hD,hS⟩

private lemma source_at_origin {u : Fin 4} (hu : u=0 ∨ u=3) :
    sourceAxis 0 0 u=(1,0) := by
  rcases hu with rfl | rfl <;>
    simp [sourceAxis,primary,secondary,scale]

private lemma cos_quarter : Real.cos (Real.pi/4)=Six.hStar := by simp [Six.hStar]
private lemma sin_quarter : Real.sin (Real.pi/4)=Six.hStar := by simp [Six.hStar]

/-- With the phases of the model, the selected separations are the eight contact
inequalities. -/
theorem contacts_of_selected {R : ℝ} (P : NormalizedPacking R)
    (hD : CandidateDSeparators P) (u v : Fin 4) (hsel : SelectedPairs P u v)
    (ha : P.helperAngle 0=0 ∧ P.helperAngle 1=0 ∧ P.helperAngle 2=0 ∧
      P.helperAngle 4=0 ∧ P.diagonalAngle=Real.pi/4)
    (hu : u=0 ∨ u=3) (hv : v=0 ∨ v=3) :
    ContactCoordinates.Contacts P.center P.radial P.transverse := by
  have hf := frame_of_angles P ha
  obtain ⟨he,hn,hw,hs,hd⟩ := ha
  have hNWaxis : preferredPairAxis NWsigns (P.square 2) (P.square 1) u=(1,0) := by
    rw [preferred_northwest_axis,hn,hw]
    exact source_at_origin hu
  have hESaxis : preferredPairAxis ESsigns (P.square 4) (P.square 0) v=(0,1) := by
    have hswap := preferred_eastsouth_swap P v
    rw [he,hs,neg_zero,source_at_origin hv] at hswap
    have h := congrArg Six.diagonalPoint hswap
    simpa [Six.diagonalPoint] using h.symm
  have hNW := hsel.1
  rw [hNWaxis,P.square_def 2,P.square_def 1,hf.west,hf.north,
    oriented_pair_threshold,show Real.pi/2-Real.pi= -(Real.pi/2) by ring] at hNW
  have hES := hsel.2
  rw [hESaxis,P.square_def 4,P.square_def 0,hf.south,hf.east,
    oriented_pair_threshold] at hES
  have hWD := hD.1
  change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    frameY (P.square 2) (sub (P.square 3).center (P.square 2).center) at hWD
  rw [P.square_def 2,P.square_def 3,hf.west,hf.diagonal,
    oriented_pair_threshold,pair_frameY_left,
    show 5*Real.pi/4-Real.pi=Real.pi/4 by ring] at hWD
  have hDS := hD.2
  change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at hDS
  rw [P.square_def 3,P.square_def 4,hf.diagonal,hf.south,
    oriented_pair_threshold,pair_frameY_right,
    show 3*Real.pi/2-5*Real.pi/4=Real.pi/4 by ring] at hDS
  have hEast : 1+P.center.1 ≤ P.radial 0 := by
    rcases P.two_choice 0 with h | h
    all_goals rw [hf.east] at h
    all_goals norm_num [matchingCardinal,centralMargin,centralNormal,centerX,angularWidth] at h
    all_goals linarith
  have hNorth : 1+P.center.2 ≤ P.radial 1 := by
    rcases P.two_choice 1 with h | h
    all_goals rw [hf.north] at h
    all_goals norm_num [matchingCardinal,centralMargin,centralNormal,centerY,angularWidth] at h
    all_goals linarith
  have hWest : 1 ≤ P.radial 2+P.center.1 := by
    rcases P.two_choice 2 with h | h
    all_goals rw [hf.west] at h
    all_goals norm_num [matchingCardinal,centralMargin,centralNormal,centerX,angularWidth] at h
    all_goals linarith
  have hSouth : 1 ≤ P.radial 4+P.center.2 := by
    rcases P.two_choice 4 with h | h
    all_goals rw [hf.south] at h
    all_goals norm_num [matchingCardinal,centralMargin,centralNormal,centerY,
      angularWidth,south_cos,south_sin] at h
    all_goals linarith
  refine ⟨hEast,hNorth,hWest,hSouth,?_,?_,?_,?_⟩
  · simp [angularWidth,dot,sub,orientedSquare] at hNW
    linarith
  · simp [angularWidth,dot,sub,orientedSquare,south_cos,south_sin] at hES
    linarith
  · rw [angularWidth,cos_quarter,sin_quarter,abs_of_pos Six.hStar_pos] at hWD
    nlinarith only [hWD]
  · rw [angularWidth,cos_quarter,sin_quarter,abs_of_pos Six.hStar_pos] at hDS
    nlinarith only [hDS]

/-- Under `ReductionHypotheses`, a normalized packing in a disk of squared
radius at most `q*` has the phases, the coordinates and the central square of
the model, and radius `√q*`. -/
theorem coordinates_of_reduction {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (h : ReductionHypotheses P) :
    Frame P ∧ ContactCoordinates.Coordinates P.radial P.transverse ∧
      P.center=(Six.sStar,Six.sStar) ∧ R=Six.radius := by
  obtain ⟨u,v,hsel,ha,hu,hv,_,hr⟩ := candidate_data_with_selection P hR h
  have hf := frame_of_angles P ha
  have hcontacts := contacts_of_selected P h.diagonal_edges u v hsel ha hu hv
  have hbox (i : Fin 5) :
      (|P.radial i|+1/2)^2+(|P.transverse i|+1/2)^2 ≤ Six.radius^2 := by
    have hc := (P.packing.phi_le i.succ).trans hR
    simpa only [pinModel_succ,orientedSquare_alpha,orientedSquare_beta,phi,Six.radius_sq] using hc
  have hc := ContactCoordinates.coordinates_of_contacts hcontacts hbox
  exact ⟨hf,hc,ContactCoordinates.center_of_contacts hcontacts hc,hr⟩

end SquaresInCircles.Six.Equality.AnalyticContacts
