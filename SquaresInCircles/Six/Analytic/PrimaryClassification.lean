import SquaresInCircles.Six.Analytic.CardinalInwardEndpoints
import SquaresInCircles.Six.Analytic.CardinalDestinationPrimary
import SquaresInCircles.Six.Analytic.OwnDestinationPrimary

/-!
# W and D are separated along a second axis

W and D are separated along one of the eight directed axes `±e₁`, `±e₂` of the
two squares, and only the axes `e₂` of W and of D are possible. The axes `e₁`
of W and `-e₁` of D are excluded by the radial coordinates, the axes `-e₂` by
the chord between the pins of W and D, and the axes `-e₁` of W and `e₁` of D
case by case. For W on the west side of C the axis `-e₁` of W is excluded here:
by a phase gap of at most `π/3` when the angle of W is nonnegative, and
otherwise by a stress with the centres frozen, using `a_W + c_x ≥ 1`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private lemma cardinal_inward_frozen_nonpositive {v d aw bw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/5) (hd : 0≤d ∧ d≤Real.pi/4)
    (haxial : 1≤aw+cx)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (scale (-1) (normalX (orientedSquare (Real.pi-v) aw bw)))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) :
    cardinalInwardFrozen v d aw ad bd cx cy≤0 := by
  have hcd : 0≤Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_pos]⟩
  have hsd := Real.sin_nonneg_of_nonneg_of_le_pi hd.1 (by linarith [hd.2,Real.pi_pos])
  have hcq : 0≤Real.cos (v+d) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,hd.1,Real.pi_pos],by linarith [hv.2,hd.2,Real.pi_gt_d2]⟩
  have hsq := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤v+d by linarith [hv.1,hd.1])
    (show v+d≤Real.pi by linarith [hv.2,hd.2,Real.pi_gt_d2])
  have hD : 1/2-ad+(1/2-cx)*Real.cos d+(1/2-cy)*Real.sin d≤0 := by
    have hcpi : Real.cos (Real.pi+d) = -Real.cos d := by rw [add_comm,Real.cos_add_pi]
    have hspi : Real.sin (Real.pi+d) = -Real.sin d := by rw [add_comm,Real.sin_add_pi]
    simp only [centralMargin,centralNormal,angularWidth,hcpi,hspi,
      abs_neg,abs_of_nonneg hcd,abs_of_nonneg hsd] at hCD
    nlinarith only [hCD]
  have hproj : dot (scale (-1) (normalX (orientedSquare (Real.pi-v) aw bw)))
      (sub (orientedSquare (Real.pi+d) ad bd).center
        (orientedSquare (Real.pi-v) aw bw).center)=
      -(ad*Real.cos (v+d)-bd*Real.sin (v+d)-aw) := by
    rw [dot_scale_neg]
    change -(frameX (orientedSquare (Real.pi-v) aw bw)
      (sub (orientedSquare (Real.pi+d) ad bd).center
        (orientedSquare (Real.pi-v) aw bw).center))=_
    rw [pair_frameX_left,show (Real.pi+d)-(Real.pi-v)=v+d by ring]
  rw [hproj,oriented_pair_threshold,show (Real.pi+d)-(Real.pi-v)=v+d by ring,
    angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq] at hWD
  have hE : 1/2-aw+(1/2+ad)*Real.cos (v+d)+(1/2-bd)*Real.sin (v+d)≤0 := by
    nlinarith only [hWD]
  dsimp [cardinalInwardFrozen,frozenTrig]
  nlinarith only [hD,hE,haxial]

/-- If W is separated from C along the west side of C, W and D are not separated
along `-e₁` of W. -/
theorem normalized_cardinalW_inward_primary_excluded {R : ℝ}
    (P : NormalizedPacking R) (hcard : P.ownBits 2=false) :
    ¬ Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (scale (-1) (normalX (P.square 2)))
        (sub (P.square 3).center (P.square 2).center) := by
  intro hsep
  have hwphase : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hdphase : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [NormalizedPacking.diagonalAngle]; ring
  by_cases hw : 0≤P.helperAngle 2
  · have hq : |P.phase 3-P.phase 2|≤Real.pi/3 := by
      rw [abs_of_nonneg (sub_nonneg.mpr P.primary_order.2.2.1.le),hwphase,hdphase]
      linarith [P.diagonal_angle_range.2,Real.pi_pos]
    exact not_le_of_gt (oriented_inward_primary_excluded (P.contained 2) (P.contained 3)
      (P.avoidsCore 3) hq) hsep
  · have hwbound := abs_lt.mp (P.cardinal_angle 2 hcard)
    have hv : 0≤-P.helperAngle 2 ∧ -P.helperAngle 2≤2/5 := by
      constructor <;> linarith [hwbound.1,hwbound.2]
    have hd := P.diagonal_angle_range
    have hpositive := cardinal_inward_frozen_positive hv ⟨hd.1.le,hd.2⟩
      (P.contained 2).a_le_rho0 (P.contained 3)
      ((P.contained 3).u_lt_half (P.avoidsCore 3)) P.box
    have hC := P.cardinal_separator 2 hcard
    have hmc : matchingCardinal 2 = CentralAxis.west := rfl
    have haxial := west_cardinal_radial_lower (P.contained 2).half_le
      ((P.contained 2).u_lt_half (P.avoidsCore 2)).le
      (by simpa only [hwphase,hmc] using hC)
    have hwphase' : P.phase 2=Real.pi-(-P.helperAngle 2) := by rw [hwphase]; ring
    have hnegative := cardinal_inward_frozen_nonpositive hv ⟨hd.1.le,hd.2⟩ haxial
      (by simpa only [hdphase] using P.own_separator 3 P.diagonal_own)
      (by simpa only [P.square_def,hwphase',hdphase] using hsep)
    linarith

/-- Every directed axis that separates W and D is `e₂` of W (`k = 2`) or `e₂` of D
(`k = 6`). -/
theorem DW_selected_secondary {R : ℝ} (P : NormalizedPacking R) (k : Fin 8)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (Stress.pairNormal k (P.square 2) (P.square 3))
        (sub (P.square 3).center (P.square 2).center)) : k=2 ∨ k=6 := by
  have hout := normalized_outward_axes_excluded P 2 3 k hsep
  have hp := selected_axis_points_to_pin _ _ (P.pin 2) (P.pin 3) k hsep
  have hneg3 : k≠3 := by
    intro he
    subst k
    change 0<dot (scale (-1) (normalY (P.square 2)))
      (sub (Certificates.fixedPin 3) (Certificates.fixedPin 2)) at hp
    rw [dot_scale_neg] at hp
    linarith [P.DW_chord_positive_secondary.1]
  have hneg7 : k≠7 := by
    intro he
    subst k
    change 0<dot (scale (-1) (normalY (P.square 3)))
      (sub (Certificates.fixedPin 3) (Certificates.fixedPin 2)) at hp
    rw [dot_scale_neg] at hp
    linarith [P.DW_chord_positive_secondary.2]
  fin_cases k
  · exact False.elim (hout.1 rfl)
  · cases hbit : P.ownBits 2
    · exact False.elim (normalized_cardinalW_inward_primary_excluded P hbit hsep)
    · exact False.elim (normalized_ownW_inward_primary_excluded P hbit hsep)
  · exact Or.inl rfl
  · exact False.elim (hneg3 rfl)
  · cases hbit : P.ownBits 2
    · exact False.elim (normalized_cardinalW_destination_primary_excluded P hbit hsep)
    · exact False.elim (normalized_ownW_destination_primary_excluded P hbit hsep)
  · exact False.elim (hout.2 rfl)
  · exact Or.inr rfl
  · exact False.elim (hneg7 rfl)

/-- W and D are separated along `e₂` of W or `e₂` of D. -/
theorem DW_secondary_exists {R : ℝ} (P : NormalizedPacking R) : ∃ k : Fin 8,
    Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (Stress.pairNormal k (P.square 2) (P.square 3))
        (sub (P.square 3).center (P.square 2).center) ∧ (k=2 ∨ k=6) := by
  obtain ⟨k,hk,_,_⟩ := P.DW_source
  exact ⟨k,hk,DW_selected_secondary P k hk⟩

end SquaresInCircles.Six.Analytic
