module
public import SquaresInCircles.Six.Analytic.FixedPairCoordinates
public import SquaresInCircles.Six.Stress.CandidateRadius

@[expose] public section

/-!
# Fixed-pair work from actual packing inequalities

The three real separator inequalities and the candidate-radius support bounds
imply the pair upper bound. The transverse term is left explicit for the later
D-edge assembly. No candidate D-edge, tail, pair-envelope, or bit-dependent
Domain theorem is imported or assumed here.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

/-- The exact central-force correction makes this valid without individually
balancing the two central normals. -/
theorem pair_work_bound (no wo : Bool) (u : Fin 4)
    {n w an bn aw bw : ℝ} {c : Point}
    (hc : (0≤c.1 ∧ c.1≤cStar) ∧ (0≤c.2 ∧ c.2≤cStar))
    (hNbox : (|an|+1/2)^2+(|bn|+1/2)^2≤Six.radius^2)
    (hWbox : (|aw|+1/2)^2+(|bw|+1/2)^2≤Six.radius^2)
    (hN : 1/2+angularWidth n≤dot (northNormal no n)
      (sub (orientedSquare (Real.pi/2+n) an bn).center c))
    (hW : 1/2+angularWidth w≤dot (westNormal wo w)
      (sub (orientedSquare (Real.pi+w) aw bw).center c))
    (hNW : 1/2+angularWidth (n-w)≤dot (sourceAxis n w u)
      (sub (orientedSquare (Real.pi/2+n) an bn).center
        (orientedSquare (Real.pi+w) aw bw).center)) :
    value no wo u n w≤c.1-c.2+mStar*(bw+1/2) := by
  have hweighted := mul_le_mul_of_nonneg_left hNW rStar_pos.le
  have hsum := add_le_add (add_le_add hN hW) hweighted
  rw [edge_work_identity] at hsum
  have hNs := scalar_center_support
    (x := (northForce no u n w).1) (y := (northForce no u n w).2)
    radius_gt_half hNbox
  have hWs := scalar_center_support
    (x := (westForce wo u n w).1) (y := (westForce wo u n w).2)
    radius_gt_half hWbox
  have hC := central_excess_support hc no wo n w
  dsimp [dot] at hsum hC
  dsimp [value,threshold]
  linarith

lemma width_pi_add (t : ℝ) : angularWidth (Real.pi+t)=angularWidth t := by
  simp [angularWidth,Real.cos_pi_add,Real.sin_pi_add,abs_neg]

lemma width_half_pi_add (t : ℝ) : angularWidth (Real.pi/2+t)=angularWidth t := by
  simp [angularWidth,Real.cos_add,Real.sin_add,abs_neg,add_comm]

lemma width_sub_half_pi (t : ℝ) : angularWidth (t-Real.pi/2)=angularWidth t := by
  simp [angularWidth,Real.cos_sub,Real.sin_sub,abs_neg,add_comm]

lemma northwest_threshold (n w an bn aw bw : ℝ) :
    Seven.SAT.threshold (orientedSquare (Real.pi+w) aw bw)
      (orientedSquare (Real.pi/2+n) an bn)=1/2+angularWidth (n-w) := by
  rw [oriented_pair_threshold]
  have h : (Real.pi/2+n)-(Real.pi+w)=(n-w)-Real.pi/2 := by ring
  rw [h,width_sub_half_pi]

/-- The actual cardinal-preferred central normal. -/
def chosenCenterAxis {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) : Point :=
  if P.ownBits i then primary (P.phase i) else primary (cardinalCenter (matchingCardinal i))

lemma chosen_center_separates {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) :
    Seven.SAT.threshold (P.model 0) (P.model i.succ)≤
      dot (chosenCenterAxis P i) (sub (P.model i.succ).center (P.model 0).center) := by
  change Seven.SAT.threshold (axisSquare P.center) (P.square i)≤
    dot (chosenCenterAxis P i) (sub (P.square i).center P.center)
  rw [P.square_def,central_threshold]
  cases hbit : P.ownBits i
  · have hm := P.cardinal_separator i hbit
    fin_cases i
    all_goals simp only [chosenCenterAxis,hbit,Bool.false_eq_true,if_false,
      matchingCardinal,cardinalCenter,primary,Real.cos_zero,Real.sin_zero,
      Real.cos_pi,Real.sin_pi,Real.cos_pi_div_two,Real.sin_pi_div_two,south_cos,south_sin]
    all_goals dsimp [centralMargin,centerX,centerY,dot,sub,orientedSquare] at hm ⊢
    all_goals linarith
  · have hm := P.own_separator i hbit
    simp only [chosenCenterAxis,hbit,if_true]
    change 1/2+angularWidth (P.phase i)≤
      frameX (orientedSquare (P.phase i) (P.radial i) (P.transverse i))
        (sub (orientedSquare (P.phase i) (P.radial i) (P.transverse i)).center P.center)
    rw [primary_difference]
    dsimp [centralMargin] at hm
    linarith

lemma chosen_north_axis {R : ℝ} (P : NormalizedPacking R) :
    chosenCenterAxis P 1=northNormal (P.ownBits 1) (P.helperAngle 1) := by
  have hn : P.phase 1=Real.pi/2+P.helperAngle 1 := P.phase_from_deviation 1
  cases hb : P.ownBits 1 <;>
    simp [chosenCenterAxis,northNormal,hb,hn,matchingCardinal,cardinalCenter,
      primary,Real.cos_add,Real.sin_add]

lemma chosen_west_axis {R : ℝ} (P : NormalizedPacking R) :
    chosenCenterAxis P 2=westNormal (P.ownBits 2) (P.helperAngle 2) := by
  have hw : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  cases hb : P.ownBits 2 <;>
    simp [chosenCenterAxis,westNormal,hb,hw,matchingCardinal,cardinalCenter,
      primary,Real.cos_pi_add,Real.sin_pi_add]

lemma preferred_northwest_axis {R : ℝ} (P : NormalizedPacking R) (u : Fin 4) :
    preferredPairAxis NWsigns (P.square 2) (P.square 1) u=
      sourceAxis (P.helperAngle 1) (P.helperAngle 2) u := by
  have hn : P.phase 1=Real.pi/2+P.helperAngle 1 := P.phase_from_deviation 1
  have hw : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  fin_cases u <;> simp [preferredPairAxis,unsignedPairAxis,NWsigns,sourceAxis,
    P.square_def,hn,hw,normalX,normalY,orientedSquare,primary,secondary]

/-- The selected N/W source is a consequence of the packing's interior pins.
No restriction to equality-compatible sources is made. -/
theorem actual_northwest_pair {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2≤Six.qStar) : ∃ u : Fin 4,
      value (P.ownBits 1) (P.ownBits 2) u (P.helperAngle 1) (P.helperAngle 2)≤
        P.center.1-P.center.2+mStar*(P.transverse 2+1/2) := by
  obtain ⟨u,hsel⟩ := P.NW_source
  have hn : P.phase 1=Real.pi/2+P.helperAngle 1 := P.phase_from_deviation 1
  have hw : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hN := chosen_center_separates P 1
  have hW := chosen_center_separates P 2
  change Seven.SAT.threshold (axisSquare P.center) (P.square 1)≤_ at hN
  change Seven.SAT.threshold (axisSquare P.center) (P.square 2)≤_ at hW
  rw [P.square_def,central_threshold,chosen_north_axis,hn,width_half_pi_add] at hN
  rw [P.square_def,central_threshold,chosen_west_axis,hw,width_pi_add] at hW
  rw [preferred_northwest_axis,P.square_def 2,P.square_def 1,hw,hn,northwest_threshold] at hsel
  have hNbox := (P.packing.phi_le (1:Fin 5).succ).trans hR
  have hWbox := (P.packing.phi_le (2:Fin 5).succ).trans hR
  change phi (alpha (P.square 1) (0,0)) (beta (P.square 1) (0,0))≤Six.qStar at hNbox
  change phi (alpha (P.square 2) (0,0)) (beta (P.square 2) (0,0))≤Six.qStar at hWbox
  rw [P.square_def,orientedSquare_alpha,orientedSquare_beta] at hNbox hWbox
  have hc := P.toPinPacking.sharp_central_box hR
  refine ⟨u,pair_work_bound (P.ownBits 1) (P.ownBits 2) u hc ?_ ?_ hN hW hsel⟩
  · simpa only [Six.radius_sq,phi] using hNbox
  · simpa only [Six.radius_sq,phi] using hWbox

end SquaresInCircles.Six.Analytic.FixedPair
