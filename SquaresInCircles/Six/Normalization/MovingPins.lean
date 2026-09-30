module
public import SquaresInCircles.Six.Normalization.CardinalGeometry
public import SquaresInCircles.Six.Analytic.OwnMovingPin

@[expose] public section

/-!
# N24: east and north moving pins by analytic geometry

The east OWN case uses a single whole-interval polynomial contradiction in
Analytic.OwnMovingPin. North is the same local coordinate identity; it does not
construct P.mirror, invoke its certificate-derived fields, or re-normalize D.
Cardinal cases use analytic cap piercing. The construction of the broad windows
and strong central box remains a separate analytic-conversion obligation.
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
  have habs : |P.phase 0| ≤ 5/12 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  exact Analytic.own_moving_pin habs (P.contained 0)
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
  have ht := P.window 1
  norm_num [windowLower,windowUpper,phaseCenter] at ht
  have habs : |Real.pi/2-P.phase 1| ≤ 5/12 := by
    apply abs_le.mpr
    constructor <;> linarith [ht.1,ht.2]
  have hc : ContainedChart (P.radial 1) |-P.transverse 1| := by
    simpa only [abs_neg] using P.contained 1
  have ho : 0 ≤ centralMargin .own (Real.pi/2-P.phase 1) (P.radial 1) (-P.transverse 1)
      P.center.2 P.center.1 := by
    simpa only [own_margin_diagonal] using hown
  have hp := Analytic.own_moving_pin habs hc
    P.box.2.1 P.box.1.1 P.box.2.2 P.box.1.2 ho
  have hpoint := (oriented_diagonal_open (P.phase 1) (P.radial 1) (P.transverse 1)
    (1+P.center.2,0)).mp hp
  simpa only [Six.diagonalPoint] using hpoint

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
