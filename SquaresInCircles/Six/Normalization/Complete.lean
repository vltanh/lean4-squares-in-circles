import SquaresInCircles.Six.Normalization.WestCardinalStress
import SquaresInCircles.Six.Normalization.CardinalGeometry
import SquaresInCircles.Six.Analytic.OwnMovingPin
import SquaresInCircles.Six.Normalization.ActualMarkers

/-!
# Normalized packings

A normalized packing is a pin packing in which the phase of D is at most
`5π/4`. Then D is separated from C along its own axis: if D were separated
along the west side of C, W could not be, so W would be separated along its
own axis, and `WestCardinal.impossible` excludes that pair. The accessors
read off the angles of the squares from their cardinal directions, their
separators from C, and the order of their phases. Every packing of six unit
squares in a disk of squared radius at most `Q0` is congruent to a normalized
packing or to its reflection in the diagonal.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

/-- With the phase of D at most `5π/4`, D is not separated from C along the west
side of C. -/
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
  have h3 : matchingCardinal 3 = .west := rfl
  rw [h3] at hu
  simp only [cardinalCenter] at hu
  have hub := abs_lt.mp hu
  have hord := P.west_before_diagonal hD
  have htEq : Real.pi+(P.phase 2-Real.pi)=P.phase 2 := by ring
  have huEq : Real.pi+(P.phase 3-Real.pi)=P.phase 3 := by ring
  apply WestCardinal.impossible (c := P.center)
    (t := P.phase 2-Real.pi) (u := P.phase 3-Real.pi)
    (a := P.radial 2) (b := P.transverse 2) (A := P.radial 3) (B := P.transverse 3)
    P.box (P.contained 2) (P.contained 3) (P.avoidsCore 2) (P.avoidsCore 3)
    (by linarith [hw.1]) (by linarith [hub.1]) (by linarith [hub.2]) (by linarith)
  · simpa only [htEq] using hownW
  · simpa only [huEq] using hwestD
  · simpa only [htEq,huEq] using P.exterior_disjoint 2 3 (by decide)

/-- With the phase of D at most `5π/4`, D is separated from C along its own
axis. -/
theorem PinPacking.D_own {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    P.canonicalOwn 3 = true ∧
      0 ≤ centralMargin .own (P.phase 3) (P.radial 3) (P.transverse 3) P.center.1 P.center.2 := by
  have hneg := P.D_west_negative hD
  have hbit : P.canonicalOwn 3=true := by
    apply (P.canonicalOwn_eq_true 3).mpr
    exact hneg
  exact ⟨hbit,P.own_of_canonicalOwn hD 3 hbit⟩

/-- A pin packing in which the phase of D is at most `5π/4`. -/
structure NormalizedPacking (R : ℝ) extends PinPacking R where
  diagonal_half : phase 3 ≤ 5*Real.pi/4

namespace NormalizedPacking
variable {R : ℝ} (P : NormalizedPacking R)

def model : Fin 6 → UnitSquare := P.toPinPacking.model

def ownBits : Fin 5 → Bool := P.toPinPacking.canonicalOwn

def helperAngle (i : Fin 5) : ℝ := P.phase i-cardinalCenter (matchingCardinal i)

def diagonalAngle : ℝ := P.phase 3-Real.pi

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

lemma diagonal_own : P.ownBits 3=true := (P.toPinPacking.D_own P.diagonal_half).1

end NormalizedPacking

/-- A packing in a disk of squared radius at most `Q0` is congruent to a
normalized packing or to its reflection in the diagonal. -/
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

/-- The same for a disk of squared radius at most `qStar`, which is below
`Q0`. -/
theorem normalize_of_candidate {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hR : R^2 ≤ Six.qStar) :
    ∃ P : NormalizedPacking R, CongruentOrDiagonal S o P.model :=
  normalize_of_ceiling hp (hR.trans Six.qStar_lt_Q0.le)

end SquaresInCircles.Six.Normalization
