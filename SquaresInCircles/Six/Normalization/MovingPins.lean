import SquaresInCircles.Six.Normalization.CardinalGeometry

/-!
# N24: unconditional east and north moving pins

The east OWN case is Lemma G's real geometric certificate. The north case is
its symmetric local calculation; it does not re-normalize D or assume the
reflected packing keeps D's half-window. Cardinal cases use the already proved
cap piercing. The final theorem has no separator-choice hypothesis.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

lemma PinPacking.east_own_moving_pin {R : ℝ} (P : PinPacking R)
    (hown : 0 ≤ centralMargin .own (P.phase 0) (P.radial 0) (P.transverse 0)
      P.center.1 P.center.2) :
    openSquare (orientedSquare (P.phase 0) (P.radial 0) (P.transverse 0)) (1+P.center.1,0) := by
  have ht := P.window 0
  norm_num [windowLower,windowUpper,phaseCenter] at ht
  have hb := (P.contained 0).bounds (P.avoidsCore 0)
  exact own_moving_pin_from_margin ht (P.contained 0) hb.1 hb.2.2
    P.box.1.1 P.box.2.1 P.box.1.2 P.box.2.2 hown

lemma own_margin_diagonal (t a b cx cy : ℝ) :
    centralMargin .own (Real.pi/2-t) a (-b) cy cx = centralMargin .own t a b cx cy := by
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub]
  ring

lemma PinPacking.north_own_moving_pin {R : ℝ} (P : PinPacking R)
    (hown : 0 ≤ centralMargin .own (P.phase 1) (P.radial 1) (P.transverse 1)
      P.center.1 P.center.2) :
    openSquare (orientedSquare (P.phase 1) (P.radial 1) (P.transverse 1)) (0,1+P.center.2) := by
  have hm : 0 ≤ centralMargin .own (P.mirror.phase 0) (P.mirror.radial 0)
      (P.mirror.transverse 0) P.mirror.center.1 P.mirror.center.2 := by
    change 0 ≤ centralMargin .own (mirroredPhase 0 (P.phase (mirrorPin 0)))
      (P.radial (mirrorPin 0)) (-P.transverse (mirrorPin 0)) P.center.2 P.center.1
    simpa [mirroredPhase,mirrorPin,own_margin_diagonal] using hown
  have he := P.mirror.east_own_moving_pin hm
  have hpoint := (mirrored_oriented_open 0 (P.phase 1) (P.radial 1) (P.transverse 1)
    (1+P.center.2,0)).mp he
  simpa [Six.diagonalPoint] using hpoint

/-- N24 after the cardinal-preferred two-choice theorem, with both cases proved. -/
theorem PinPacking.moving_pins {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    openSquare (orientedSquare (P.phase 0) (P.radial 0) (P.transverse 0)) (1+P.center.1,0) ∧
      openSquare (orientedSquare (P.phase 1) (P.radial 1) (P.transverse 1)) (0,1+P.center.2) := by
  constructor
  · rcases P.two_choice hD 0 with hc | ho
    · simpa [matchingCardinal,cardinalPiercingPoint] using P.cardinal_piercing 0 hc
    · exact P.east_own_moving_pin ho
  · rcases P.two_choice hD 1 with hc | ho
    · simpa [matchingCardinal,cardinalPiercingPoint] using P.cardinal_piercing 1 hc
    · exact P.north_own_moving_pin ho

end SquaresInCircles.Six.Normalization
