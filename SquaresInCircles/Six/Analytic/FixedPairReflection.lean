module
public import SquaresInCircles.Six.Analytic.FixedPairPacking

@[expose] public section

/-!
# The E/S pair is the same local calculation

The swap below transforms vectors in the scalar work identity; it is not a
second global normalization of the packing. The actual E/S separator is
selected before the coordinate swap. In particular the recorded D half-window
and the orientation trace are unchanged.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

lemma swap_sub (p q : Point) :
    Six.diagonalPoint (sub p q)=sub (Six.diagonalPoint p) (Six.diagonalPoint q) := rfl

lemma swap_dot (p q : Point) :
    dot (Six.diagonalPoint p) (Six.diagonalPoint q)=dot p q := by
  dsimp [dot,Six.diagonalPoint]
  ring

lemma reflected_east_center (e a b : ℝ) :
    (orientedSquare (Real.pi/2-e) a (-b)).center=
      Six.diagonalPoint (orientedSquare e a b).center := by
  apply Prod.ext <;>
    simp [orientedSquare,Six.diagonalPoint,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub] <;> ring

lemma reflected_south_center (s a b : ℝ) :
    (orientedSquare (Real.pi-s) a (-b)).center=
      Six.diagonalPoint (orientedSquare (3*Real.pi/2+s) a b).center := by
  apply Prod.ext <;>
    simp [orientedSquare,Six.diagonalPoint,Real.cos_pi_sub,Real.sin_pi_sub,
      Real.cos_add,Real.sin_add,south_cos,south_sin] <;> ring

lemma width_neg (t : ℝ) : angularWidth (-t)=angularWidth t := by
  simp [angularWidth,Real.cos_neg,Real.sin_neg,abs_neg]

lemma width_three_half_pi_add (s : ℝ) : angularWidth (3*Real.pi/2+s)=angularWidth s := by
  have h : 3*Real.pi/2+s=Real.pi+(Real.pi/2+s) := by ring
  rw [h,width_pi_add,width_half_pi_add]

lemma eastsouth_threshold (e s ae be aS bS : ℝ) :
    Seven.SAT.threshold (orientedSquare (3*Real.pi/2+s) aS bS)
      (orientedSquare e ae be)=1/2+angularWidth ((-e)-(-s)) := by
  rw [oriented_pair_threshold]
  have h : e-(3*Real.pi/2+s)=(e-s)-3*Real.pi/2 := by ring
  rw [h]
  have hn : (-e)-(-s)=-(e-s) := by ring
  rw [hn,width_neg]
  simp [angularWidth,Real.cos_sub,Real.sin_sub,south_cos,south_sin,abs_neg,add_comm]

lemma chosen_east_swap {R : ℝ} (P : NormalizedPacking R) :
    northNormal (P.ownBits 0) (-P.helperAngle 0)=Six.diagonalPoint (chosenCenterAxis P 0) := by
  have he : P.phase 0=P.helperAngle 0 := by
    simpa [matchingCardinal,cardinalCenter] using P.phase_from_deviation 0
  cases hb : P.ownBits 0 <;>
    simp [northNormal,chosenCenterAxis,hb,he,matchingCardinal,cardinalCenter,
      primary,Six.diagonalPoint,Real.cos_neg,Real.sin_neg]

lemma chosen_south_swap {R : ℝ} (P : NormalizedPacking R) :
    westNormal (P.ownBits 4) (-P.helperAngle 4)=Six.diagonalPoint (chosenCenterAxis P 4) := by
  have hs : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  cases hb : P.ownBits 4 <;>
    simp [westNormal,chosenCenterAxis,hb,hs,matchingCardinal,cardinalCenter,
      primary,Six.diagonalPoint,Real.cos_neg,Real.sin_neg,Real.cos_add,Real.sin_add,
      south_cos,south_sin]

lemma preferred_eastsouth_swap {R : ℝ} (P : NormalizedPacking R) (v : Fin 4) :
    sourceAxis (-P.helperAngle 0) (-P.helperAngle 4) v=
      Six.diagonalPoint (preferredPairAxis ESsigns (P.square 4) (P.square 0) v) := by
  have he : P.phase 0=P.helperAngle 0 := by
    simpa [matchingCardinal,cardinalCenter] using P.phase_from_deviation 0
  have hs : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  fin_cases v <;> apply Prod.ext <;>
    simp [sourceAxis,preferredPairAxis,unsignedPairAxis,ESsigns,P.square_def,
      he,hs,normalX,normalY,primary,secondary,orientedSquare,scale,Six.diagonalPoint,
      Real.cos_add,Real.sin_add,Real.cos_neg,Real.sin_neg,south_cos,south_sin] <;> ring

/-- E/S with its genuine selected source, keeping the local transverse sign. -/
theorem actual_eastsouth_pair {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2≤Six.qStar) : ∃ v : Fin 4,
      value (P.ownBits 0) (P.ownBits 4) v (-P.helperAngle 0) (-P.helperAngle 4)≤
        P.center.2-P.center.1+mStar*(-P.transverse 4+1/2) := by
  obtain ⟨v,hsel⟩ := P.ES_source
  have he : P.phase 0=P.helperAngle 0 := by
    simpa [matchingCardinal,cardinalCenter] using P.phase_from_deviation 0
  have hs : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hE := chosen_center_separates P 0
  have hS := chosen_center_separates P 4
  change Seven.SAT.threshold (axisSquare P.center) (P.square 0)≤_ at hE
  change Seven.SAT.threshold (axisSquare P.center) (P.square 4)≤_ at hS
  rw [P.square_def,central_threshold,he] at hE
  rw [P.square_def,central_threshold,hs,width_three_half_pi_add] at hS
  rw [P.square_def 4,P.square_def 0,hs,he,eastsouth_threshold] at hsel
  have hEbox := (P.packing.phi_le (0:Fin 5).succ).trans hR
  have hSbox := (P.packing.phi_le (4:Fin 5).succ).trans hR
  change phi (alpha (P.square 0) (0,0)) (beta (P.square 0) (0,0))≤Six.qStar at hEbox
  change phi (alpha (P.square 4) (0,0)) (beta (P.square 4) (0,0))≤Six.qStar at hSbox
  rw [P.square_def,orientedSquare_alpha,orientedSquare_beta] at hEbox hSbox
  have hc := P.toPinPacking.sharp_central_box hR
  have hNE : (orientedSquare (Real.pi/2+(-P.helperAngle 0))
      (P.radial 0) (-P.transverse 0)).center=Six.diagonalPoint (P.square 0).center := by
    rw [P.square_def,he]
    simpa only [sub_eq_add_neg] using reflected_east_center (P.helperAngle 0) (P.radial 0) (P.transverse 0)
  have hWS : (orientedSquare (Real.pi+(-P.helperAngle 4))
      (P.radial 4) (-P.transverse 4)).center=Six.diagonalPoint (P.square 4).center := by
    rw [P.square_def,hs]
    simpa only [sub_eq_add_neg] using reflected_south_center (P.helperAngle 4) (P.radial 4) (P.transverse 4)
  refine ⟨v,pair_work_bound (P.ownBits 0) (P.ownBits 4) v
    (c := Six.diagonalPoint P.center) ⟨hc.2,hc.1⟩ ?_ ?_ ?_ ?_ ?_⟩
  · simpa only [Six.radius_sq,phi,abs_neg] using hEbox
  · simpa only [Six.radius_sq,phi,abs_neg] using hSbox
  · rw [width_neg,chosen_east_swap,hNE,← swap_sub,swap_dot]
    exact hE
  · rw [width_neg,chosen_south_swap,hWS,← swap_sub,swap_dot]
    exact hS
  · rw [preferred_eastsouth_swap,hNE,hWS,← swap_sub,swap_dot]
    exact hsel

/-- Central coordinate terms cancel between the two actual pairs. The residual
transverse work is precisely the quantity the two candidate D-edges control.
This theorem does not assert that those D-edges have already been proved. -/
theorem actual_pair_sum {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2≤Six.qStar) : ∃ u v : Fin 4,
      value (P.ownBits 1) (P.ownBits 2) u (P.helperAngle 1) (P.helperAngle 2)+
        value (P.ownBits 0) (P.ownBits 4) v (-P.helperAngle 0) (-P.helperAngle 4)≤
      mStar*(1+P.transverse 2-P.transverse 4) := by
  obtain ⟨u,hu⟩ := actual_northwest_pair P hR
  obtain ⟨v,hv⟩ := actual_eastsouth_pair P hR
  exact ⟨u,v,by linarith⟩

end SquaresInCircles.Six.Analytic.FixedPair
