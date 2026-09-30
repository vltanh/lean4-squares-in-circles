import SquaresInCircles.Six.Normalization.WestCardinalStress
import SquaresInCircles.Six.Normalization.MovingPins
import SquaresInCircles.Six.Normalization.NearestPoint

/-!
# The complete normalization source interface

Every input is an actual packing and the candidate-radius ceiling. Proposition
A is proved before pins and sectors. The only global diagonal reflection is
recorded explicitly. Appendix A is invoked only after the strong box, windows,
W/D order and one-helper theorem are available. No A2 conclusion occurs in
this dependency chain.

This is source completion of the normalization package, not a claim that the
unrestricted lower bound or uniqueness has already been formalized.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

/-- N27's west-cardinal exclusion with the full Appendix A interface. -/
theorem PinPacking.D_west_negative {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    centralMargin .west (P.phase 3) (P.radial 3) (P.transverse 3) P.center.1 P.center.2 < 0 := by
  by_contra! hwestD
  have hwestW : ¬ 0 ≤ centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2)
      P.center.1 P.center.2 := by
    intro h
    have hi := P.one_helper_per_side 2 3 rfl h hwestD
    norm_num at hi
  have hownW : 0 ≤ centralMargin .own (P.phase 2) (P.radial 2) (P.transverse 2)
      P.center.1 P.center.2 := by
    rcases P.two_choice hD 2 with h | h
    · exact False.elim (hwestW h)
    · exact h
  have hw := P.window 2
  norm_num [windowLower,windowUpper,phaseCenter] at hw
  have hu := P.matching_cardinal_angle 3 hwestD
  simp only [matchingCardinal,cardinalCenter] at hu
  have hub := abs_lt.mp hu
  have hord := P.west_before_diagonal hD
  have htEq : Real.pi+(P.phase 2-Real.pi)=P.phase 2 := by ring
  have huEq : Real.pi+(P.phase 3-Real.pi)=P.phase 3 := by ring
  apply WestCardinal.impossible (c := P.center)
    (t := P.phase 2-Real.pi) (u := P.phase 3-Real.pi)
    (a := P.radial 2) (b := P.transverse 2) (A := P.radial 3) (B := P.transverse 3)
    P.box (P.contained 2) (P.contained 3) hw.1.le hub.1.le hub.2.le (by linarith)
  · simpa only [htEq] using hownW
  · simpa only [huEq] using hwestD
  · simpa only [htEq,huEq] using P.exterior_disjoint 2 3 (by decide)

/-- D is canonically OWN; cardinal ties have genuinely been excluded. -/
theorem PinPacking.D_own {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    P.canonicalOwn 3 = true ∧
      0 ≤ centralMargin .own (P.phase 3) (P.radial 3) (P.transverse 3) P.center.1 P.center.2 := by
  have hneg := P.D_west_negative hD
  have hbit : P.canonicalOwn 3=true := by
    apply (P.canonicalOwn_eq_true 3).mpr
    exact hneg
  exact ⟨hbit,P.own_of_canonicalOwn hD 3 hbit⟩

/-- The pin-labelled packing with its one global D half-window choice. All
remaining normalization outputs are the proved lemmas on this structure. -/
structure NormalizedPacking (R : ℝ) extends PinPacking R where
  diagonal_half : phase 3 ≤ 5*Real.pi/4

namespace NormalizedPacking
variable {R : ℝ} (P : NormalizedPacking R)

def model : Fin 6 → UnitSquare := P.toPinPacking.model

def ownBits : Fin 5 → Bool := P.toPinPacking.canonicalOwn

def helperAngle (i : Fin 5) : ℝ := P.phase i-cardinalCenter (matchingCardinal i)

def diagonalAngle : ℝ := P.phase 3-Real.pi

def diagonalDeviation : ℝ := P.phase 3-5*Real.pi/4

lemma central_box : (0 ≤ P.center.1 ∧ P.center.1 ≤ c0) ∧
    (0 ≤ P.center.2 ∧ P.center.2 ≤ c0) := P.box

lemma coarse_box : 0 ≤ P.center.1 ∧ P.center.1 < 23/200 ∧
    0 ≤ P.center.2 ∧ P.center.2 < 23/200 :=
  ⟨P.box.1.1,P.box.1.2.trans_lt c0_lt_23_200,
    P.box.2.1,P.box.2.2.trans_lt c0_lt_23_200⟩

lemma chart_bounds (i : Fin 5) :
    aMin ≤ P.radial i ∧ P.radial i ≤ rho0 ∧ |P.transverse i| ≤ U0 ∧
      |P.transverse i| < 1/2 ∧
      (177/200 < P.radial i ∧ P.radial i < 223/200 ∧ |P.transverse i| < 117/250) :=
  P.toPinPacking.chart_bounds i

lemma pins (i : Fin 5) : openSquare (P.model i.succ) (fixedPin i) := P.pin i

lemma axial_label (i : Fin 5) : Seven.label (P.radial i) |P.transverse i|=5*|P.transverse i|/4 :=
  P.toPinPacking.affine_label i

lemma primary_order :
    P.phase 0 < P.phase 1 ∧ P.phase 1 < P.phase 2 ∧ P.phase 2 < P.phase 3 ∧
      P.phase 3 < P.phase 4 ∧ P.phase 4 < P.phase 0+2*Real.pi :=
  P.toPinPacking.cyclic_primary_order P.diagonal_half

lemma diagonal_angle_bounds : -2/5 < P.diagonalAngle ∧ P.diagonalAngle ≤ Real.pi/4 :=
  P.toPinPacking.diagonal_deviation P.diagonal_half

lemma two_choice (i : Fin 5) :
    0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2 ∨
    0 ≤ centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2 :=
  P.toPinPacking.two_choice P.diagonal_half i

lemma own_separator (i : Fin 5) (hi : P.ownBits i=true) :
    0 ≤ centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2 :=
  P.toPinPacking.own_of_canonicalOwn P.diagonal_half i hi

lemma cardinal_separator (i : Fin 5) (hi : P.ownBits i=false) :
    0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2 :=
  (P.toPinPacking.canonicalOwn_eq_false i).mp hi

lemma cardinal_angle (i : Fin 5) (hi : P.ownBits i=false) : |P.helperAngle i| < 2/5 :=
  P.toPinPacking.matching_cardinal_angle i (P.cardinal_separator i hi)

lemma one_helper_per_side (i j : Fin 5) (hside : matchingCardinal i=matchingCardinal j)
    (hi : P.ownBits i=false) (hj : P.ownBits j=false) : i=j :=
  P.toPinPacking.one_helper_per_side i j hside (P.cardinal_separator i hi) (P.cardinal_separator j hj)

lemma moving_pins : openSquare (P.model 1) (1+P.center.1,0) ∧
    openSquare (P.model 2) (0,1+P.center.2) :=
  P.toPinPacking.moving_pins P.diagonal_half

lemma east_west_budget (hE : P.ownBits 0=false) (hW : P.ownBits 2=false) :
    |P.helperAngle 0|+|P.helperAngle 2| < 4*c0 := by
  simpa only [helperAngle,matchingCardinal,cardinalCenter,sub_zero] using
    P.toPinPacking.east_west_budget (P.cardinal_separator 0 hE) (P.cardinal_separator 2 hW)

lemma north_south_budget (hN : P.ownBits 1=false) (hS : P.ownBits 4=false) :
    |P.helperAngle 1|+|P.helperAngle 4| < 4*c0 := by
  simpa only [helperAngle,matchingCardinal,cardinalCenter] using
    P.toPinPacking.north_south_budget (P.cardinal_separator 1 hN) (P.cardinal_separator 4 hS)

lemma diagonal_own : P.ownBits 3=true := (P.toPinPacking.D_own P.diagonal_half).1

lemma marker_separation (i j : Fin 5) (hij : i≠j) :
    Real.pi/3 < dist (P.toPinPacking.affineMarker i) (P.toPinPacking.affineMarker j) :=
  P.toPinPacking.marker_separation i j hij

end NormalizedPacking

/-- One theorem constructs the full normalization interface from the original
packing. Its returned orientation trace records the possible diagonal reflection. -/
theorem normalize_of_ceiling {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hQ : R^2 ≤ Q0) :
    ∃ P : NormalizedPacking R, CongruentOrDiagonal S o P.model := by
  obtain ⟨P,hP⟩ := pinPacking_of_ceiling hp hQ
  obtain ⟨Q,hD,hQ'⟩ := normalize_D_half P
  let N : NormalizedPacking R := ⟨Q,hD⟩
  refine ⟨N,?_⟩
  rcases hQ' with h | h
  · exact Or.inl (Six.congruent_trans hP h)
  · exact Or.inr (Six.congruent_trans hP h)

/-- The exact candidate bound is strictly inside the rational normalization ceiling. -/
theorem normalize_of_candidate {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hR : R^2 ≤ Six.qStar) :
    ∃ P : NormalizedPacking R, CongruentOrDiagonal S o P.model :=
  normalize_of_ceiling hp (hR.trans Six.qStar_lt_Q0.le)

end SquaresInCircles.Six.Normalization
