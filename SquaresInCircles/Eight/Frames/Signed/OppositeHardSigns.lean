module

public import SquaresInCircles.Eight.Owners.Endpoint.RotationPenalty
public import SquaresInCircles.Eight.Owners.Hard.OuterOrder
public import SquaresInCircles.Eight.Owners.Negative.CoreEReduction
public import SquaresInCircles.Eight.Words.Zero.SignedCharge

/-!
# Eight squares: a large middle tangent gives G or T its normal sign

Let A and B have a common frame with `yA - yB = 1` and `θT ≤ θA ≤ θG`. If the tangent of A is at
least `1/2`, then `yG < 0` (`HardOuterGeometry.large_middle_G_negative`); if that of B is, then
`yT > 0` (`large_middle_T_positive`), and the same holds for hard inputs. The opposite envelope
of `SignedOppositeHardEnvelope`, with the charges of H–G and T–D and the endpoint budget of H, D
and E, which exceeds `83/200` (`budget_reserve`), excludes the other sign; the opposite point may
have either sign. The case of T is the reflection of that of G, applied to the outer geometry
only, whose endpoint budget the reflection keeps; the sign of E is not normalized again.
-/

section
/-!
## Actual core-E reduction with either original tangent sign

Reflection is used to invoke the local E construction,
then undone. The returned boundary cycle has the original common radius,
all six original non-E points, all five nonincident owners and errors,
and no larger positive or negative variation. The harmless common frame
offset from two reflections is not mistaken for a changed edge error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCoreEReduction
open Candidate ActualCoreEBlocks NegativeCoreE SignedCycle

theorem reflected_primary_DE (C : SignedCycle) {eh : Fin 4}
    (heh : eh=0 ∨ eh=1) :
    primaryDE C.reflected (reflectedOwner eh)=primaryEH C eh := by
  rcases heh with rfl | rfl <;>
    simp [primaryDE,primaryEH,reflectedOwner,reflected_delta,reflectedIndex,next,D,E]

theorem reflected_primary_EH (C : SignedCycle) {de : Fin 4}
    (hde : de=2 ∨ de=3) :
    primaryEH C.reflected (reflectedOwner de)=primaryDE C de := by
  rcases hde with rfl | rfl <;>
    simp [primaryDE,primaryEH,reflectedOwner,reflected_delta,reflectedIndex,next,D,E]

theorem boundary_primary_DE {q : ℝ} (I : BoundaryInput q) :
    primaryDE I.reflected.cycle (I.reflected.witnesses.owner D)=
      primaryEH I.cycle (I.witnesses.owner E) := by
  change primaryDE I.cycle.reflected (reflectedOwner (I.witnesses.owner E))=_
  apply reflected_primary_DE
  simpa [normalOwners,E] using I.witnesses.allowed E

theorem boundary_primary_EH {q : ℝ} (I : BoundaryInput q) :
    primaryEH I.reflected.cycle (I.reflected.witnesses.owner E)=
      primaryDE I.cycle (I.witnesses.owner D) := by
  change primaryEH I.cycle.reflected (reflectedOwner (I.witnesses.owner D))=_
  apply reflected_primary_EH
  simpa [normalOwners,D] using I.witnesses.allowed D

theorem boundary_total {q : ℝ} (I : BoundaryInput q) :
    eTotal I.reflected.cycle (I.reflected.witnesses.owner D) (I.reflected.witnesses.owner E)=
      eTotal I.cycle (I.witnesses.owner D) (I.witnesses.owner E) := by
  rw [eTotal,boundary_primary_DE,boundary_primary_EH,eTotal,add_comm]

structure Endpoint (q : ℝ) (I : BoundaryInput q) where
  boundary : BoundaryInput q
  core : (boundary.cycle.point E).Core
  unchanged_points : ∀ i,i≠E → boundary.cycle.point i=I.cycle.point i
  unchanged_errors : ∀ i,i≠D → i≠E → delta boundary.cycle.theta i=delta I.cycle.theta i
  unchanged_owners : ∀ i,i≠D → i≠E → boundary.witnesses.owner i=I.witnesses.owner i
  positive_nonincrease : positiveVariation boundary.cycle.theta≤positiveVariation I.cycle.theta
  negative_nonincrease : negativeVariation boundary.cycle.theta≤negativeVariation I.cycle.theta
  normal_form :
    0≤eTotal boundary.cycle (boundary.witnesses.owner D) (boundary.witnesses.owner E) ∨
    ((boundary.cycle.point E).a=7/12 ∧
      primaryDE boundary.cycle (boundary.witnesses.owner D)≤0 ∧
      primaryEH boundary.cycle (boundary.witnesses.owner E)≤0)

def Endpoint.ofNormalized {q : ℝ} {I : NormalizedBoundaryInput q}
    (hq : q≤qCap) (R : Reduction q I) : Endpoint q I.toBoundaryInput where
  boundary := (R.move.boundaryInput I hq).toBoundaryInput
  core := by
    simpa [CycleMove.boundaryInput,CycleMove.cycle,replacePoint] using R.move.core
  unchanged_points i hi := (R.move.unchanged i hi).1
  unchanged_errors := R.move.other_delta
  unchanged_owners := R.move.other_owner I.witnesses
  positive_nonincrease := R.move.positive_nonincrease
  negative_nonincrease := R.move.negative_nonincrease
  normal_form := by
    simpa [CycleMove.boundaryInput,CycleMove.witnesses,CycleMove.cycle,replacePoint,D,E]
      using R.normal_form

/-- Return from a reduction on the reflected triple. All nonincident
original data are recovered, even though absolute frames acquire an offset. -/
def Endpoint.returnFromReflection {q : ℝ} {I : BoundaryInput q}
    (R : Endpoint q I.reflected) : Endpoint q I where
  boundary := R.boundary.reflected
  core := by
    simpa [BoundaryInput.reflected,SignedCycle.reflected,reflectedIndex,E] using R.core
  unchanged_points i hi := by
    have hj : reflectedIndex i≠E := by
      revert hi; fin_cases i <;> decide
    change (R.boundary.cycle.point (reflectedIndex i)).reflect=I.cycle.point i
    rw [R.unchanged_points _ hj]
    change (I.cycle.point (reflectedIndex (reflectedIndex i))).reflect.reflect=I.cycle.point i
    simp
  unchanged_errors i hiD hiE := by
    have hjD : reflectedIndex (next i)≠D := by
      revert hiD hiE; fin_cases i <;> decide
    have hjE : reflectedIndex (next i)≠E := by
      revert hiD hiE; fin_cases i <;> decide
    change delta R.boundary.cycle.reflected.theta i=delta I.cycle.theta i
    rw [reflected_delta,R.unchanged_errors _ hjD hjE]
    change delta I.cycle.reflected.theta (reflectedIndex (next i))=delta I.cycle.theta i
    rw [reflected_delta,reflectedIndex_next,reflectedIndex_involutive]
  unchanged_owners i hiD hiE := by
    have hjD : reflectedIndex (next i)≠D := by
      revert hiD hiE; fin_cases i <;> decide
    have hjE : reflectedIndex (next i)≠E := by
      revert hiD hiE; fin_cases i <;> decide
    change reflectedOwner (R.boundary.witnesses.owner (reflectedIndex (next i)))=
      I.witnesses.owner i
    rw [R.unchanged_owners _ hjD hjE]
    change reflectedOwner (reflectedOwner
      (I.witnesses.owner (reflectedIndex (next (reflectedIndex (next i))))))=I.witnesses.owner i
    simp only [reflectedOwner_involutive,reflectedIndex_next,reflectedIndex_involutive]
  positive_nonincrease := by
    change positiveVariation R.boundary.cycle.reflected.theta≤positiveVariation I.cycle.theta
    rw [reflected_positiveVariation]
    simpa [BoundaryInput.reflected,reflected_positiveVariation] using R.positive_nonincrease
  negative_nonincrease := by
    change negativeVariation R.boundary.cycle.reflected.theta≤negativeVariation I.cycle.theta
    rw [reflected_negativeVariation]
    simpa [BoundaryInput.reflected,reflected_negativeVariation] using R.negative_nonincrease
  normal_form := by
    rcases R.normal_form with h | ⟨hflat,hDE,hEH⟩
    · left
      rw [boundary_total]
      exact h
    · right
      refine ⟨?_,?_,?_⟩
      · simpa [BoundaryInput.reflected,SignedCycle.reflected,reflectedIndex,E,SignedPoint.reflect]
          using hflat
      · rw [boundary_primary_DE]
        exact hEH
      · rw [boundary_primary_EH]
        exact hDE

/-- The only source premises are the actual boundary data, the original
core label, and the sign of the selected primary total. -/
theorem reduce_negative_total {q : ℝ} (I : BoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) (hc : (I.cycle.point E).Core)
    (hneg : eTotal I.cycle (I.witnesses.owner D) (I.witnesses.owner E)<0) :
    Nonempty (Endpoint q I) := by
  by_cases hy : (I.cycle.point E).y≤0
  · let J : NormalizedBoundaryInput q := { toBoundaryInput := I, E_nonpos := hy }
    obtain ⟨R⟩ := NegativeCoreE.reduce_negative_total J hqL hqU hc hneg
    exact ⟨Endpoint.ofNormalized hqU R⟩
  · have hy' : (I.reflected.cycle.point E).y≤0 := by
      change -(I.cycle.point E).y≤0
      linarith
    let J : NormalizedBoundaryInput q := { toBoundaryInput := I.reflected, E_nonpos := hy' }
    have hc' : (J.cycle.point E).Core := by
      simpa [J,BoundaryInput.reflected,SignedCycle.reflected,reflectedIndex,E] using hc
    have hneg' : eTotal J.cycle (J.witnesses.owner D) (J.witnesses.owner E)<0 := by
      change eTotal I.reflected.cycle
        (I.reflected.witnesses.owner D) (I.reflected.witnesses.owner E)<0
      rw [boundary_total]
      exact hneg
    obtain ⟨R⟩ := NegativeCoreE.reduce_negative_total J hqL hqU hc' hneg'
    exact ⟨(Endpoint.ofNormalized hqU R).returnFromReflection⟩

end SquaresInCircles.Eight.SignedCoreEReduction
end
end
end

section
/-!
## Circle and angle bounds for the opposite envelope

The middle tangent of the opposite envelope is split at the rational tangent
`pivot = 3953/5000`, just above the left contact at the angle zero, into a low range of length
`lowLength` and a high range of length `highLength` (`low_domain`, `high_domain`). On each range,
the radii and the angles of the left and the right circles are bounded by polynomials in the
distance `d` to the pivot, with a positive square reserve in the containment at the level `qCap`
(`left_bounds`, `left_square_reserve`, `left_angle_polynomial`, `left_angle_contact`,
`left_angle_transverse`, `high_left_square`, `right_bounds_low`, `right_bounds_high`,
`right_square_low`, `right_square_high`). Each comparison is one polynomial inequality on its
whole interval. The two circle inequalities are enlarged to `qCap` only to derive these upper
bounds; the points, frames and owners stay as they are.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedOppositeHardEnvelope
open EndpointRotationPenalty

def pivot : ℝ := 3953/5000
def lowLength : ℝ := 1453/5000
def highLength : ℝ := 547/5000
def leftRadius (d : ℝ) : ℝ := 3/2+(861/1000)*d-(503/1000)*d^2
def leftAngle (d : ℝ) : ℝ := (673/1000)*d
def rightRadius (x : ℝ) : ℝ := 9237/5000+(48/125)*x-(73/250)*x^2
def rightY (x : ℝ) : ℝ := 3547/5000-x
def referenceAngle (x : ℝ) : ℝ := 12/25+(31/20)*x
def lowTolerance (d : ℝ) : ℝ := 1/500+d/25
def highTolerance (d : ℝ) : ℝ := 1/500+d/10

theorem low_domain {b : ℝ} (hb : b∈Icc (1/2 : ℝ) pivot) :
    pivot-b∈Icc 0 lowLength := by
  dsimp [pivot,lowLength] at *
  constructor <;> linarith [hb.1,hb.2]

theorem high_domain {b : ℝ} (hb : b∈Icc pivot (9/10 : ℝ)) :
    b-pivot∈Icc 0 highLength := by
  dsimp [pivot,highLength] at *
  constructor <;> linarith [hb.1,hb.2]

theorem left_bounds {d : ℝ} (hd : d∈Icc 0 lowLength) :
    leftRadius d∈Icc (3/2 : ℝ) (9/5) ∧
      leftAngle d∈Icc 0 (1/5 : ℝ) ∧
      pivot+1/2-d∈Icc (1 : ℝ) (13/10) := by
  have hd2 := pow_le_pow_left₀ hd.1 hd.2 2
  have hlinear : 0≤861/1000-(503/1000)*d := by
    dsimp [lowLength] at hd
    linarith [hd.2]
  have hprod := mul_nonneg hd.1 hlinear
  dsimp [leftRadius,leftAngle,pivot,lowLength] at *
  refine ⟨⟨by nlinarith,by nlinarith [sq_nonneg d]⟩,
    ⟨by linarith [hd.1],by linarith [hd.2]⟩,?_⟩
  constructor <;> linarith [hd.1,hd.2]

/-- `leftRadius d` is a quadratic majorant of the left circle: the point at the abscissa
`leftRadius d` and the height `pivot + 1/2 - d` lies outside the disk of squared radius `qCap`. -/
theorem left_square_reserve {d : ℝ} (hd : d∈Icc 0 lowLength) :
    qCap<(leftRadius d)^2+(pivot+1/2-d)^2 := by
  have hcoef : 0≤232321/1000000-(433083/500000)*d+
      (253009/1000000)*d^2 := by
    have hs := sq_nonneg (d-lowLength)
    dsimp [lowLength] at hd hs
    nlinarith [hd.2]
  have hid : (leftRadius d)^2+(pivot+1/2-d)^2-qCap=
      1209/25000000+(9/5000)*d+
        d^2*(232321/1000000-(433083/500000)*d+
          (253009/1000000)*d^2) := by
    dsimp [leftRadius,pivot,qCap]
    ring
  have hpositive : 0<1209/25000000+(9/5000)*d+
      d^2*(232321/1000000-(433083/500000)*d+
        (253009/1000000)*d^2) := by
    linarith [mul_nonneg (sq_nonneg d) hcoef,hd.1]
  generalize qCap=Q at hid ⊢
  linarith

/-- One quadratic reserve bounds the left angle polynomial on the whole low range. -/
theorem left_angle_polynomial {d : ℝ} (hd : d∈Icc 0 lowLength) :
    (leftRadius d-1)*(1-(leftAngle d)^2/2+(leftAngle d)^4/24)-
      (pivot+1/2-d)*(leftAngle d-(leftAngle d)^3/6)≤1/2 := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h3 := mul_le_mul_of_nonneg_right hd.2 (sq_nonneg d)
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg d)
  have h5 := pow_nonneg hd.1 5
  have hquadratic :
      -37869/5000000+(227071/4000000)*d-(109/1000)*d^2≤0 := by
    nlinarith [sq_nonneg (d-5677/21800),sq_nonneg d,hd.1]
  have htail :
      -(1294188907233/10000000000000)*d^2+
        (3234333831041/48000000000000)*d^3+
        (58876522884767/8000000000000000)*d^4-
        (103187773557623/24000000000000000)*d^5≤
          -(109/1000)*d^2 := by
    dsimp [lowLength] at h3 h4
    nlinarith [sq_nonneg d]
  have hpoly :
      -37869/5000000+(227071/4000000)*d-
        (1294188907233/10000000000000)*d^2+
        (3234333831041/48000000000000)*d^3+
        (58876522884767/8000000000000000)*d^4-
        (103187773557623/24000000000000000)*d^5≤0 := by linarith
  have hm := mul_nonpos_of_nonneg_of_nonpos hd.1 hpoly
  have hid : (leftRadius d-1)*
      (1-(leftAngle d)^2/2+(leftAngle d)^4/24)-
      (pivot+1/2-d)*(leftAngle d-(leftAngle d)^3/6)-1/2=
      d*(-37869/5000000+(227071/4000000)*d-
        (1294188907233/10000000000000)*d^2+
        (3234333831041/48000000000000)*d^3+
        (58876522884767/8000000000000000)*d^4-
        (103187773557623/24000000000000000)*d^5) := by
    dsimp [leftRadius,leftAngle,pivot]
    ring
  linarith

theorem left_angle_contact {d : ℝ} (hd : d∈Icc 0 lowLength) :
    (leftRadius d-1)*Real.cos (leftAngle d)-
      (pivot+1/2-d)*Real.sin (leftAngle d)≤1/2 := by
  obtain ⟨hR,hz,hY⟩ := left_bounds hd
  have hc := mul_le_mul_of_nonneg_left (cos_upper_four hz.1)
    (show 0≤leftRadius d-1 by linarith [hR.1])
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hz.1)
    (show 0≤pivot+1/2-d by linarith [hY.1])
  linarith [left_angle_polynomial hd]

theorem left_angle_transverse {d : ℝ} (hd : d∈Icc 0 lowLength) :
    charge≤(leftRadius d-1)*Real.sin (leftAngle d)+
        (pivot+1/2-d)*Real.cos (leftAngle d) ∧
      (leftRadius d-1)*Real.sin (leftAngle d)+
        (pivot+1/2-d)*Real.cos (leftAngle d)≤3/2 := by
  obtain ⟨hR,hz,hY⟩ := left_bounds hd
  have hz' : leftAngle d∈Icc 0 frameCap :=
    ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have htr := transport_trig hz'
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hz2 hz.1
  have hsinLower : (149/150)*leftAngle d≤Real.sin (leftAngle d) := by
    nlinarith [Real.sin_ge_sub_cube hz.1]
  have hcosLower : 49/50≤Real.cos (leftAngle d) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := leftAngle d)]
  have hsL := mul_le_mul_of_nonneg_right
    (show (1/2 : ℝ)≤leftRadius d-1 by linarith [hR.1]) htr.2.2.1
  have hcL := mul_le_mul_of_nonneg_left hcosLower
    (show 0≤pivot+1/2-d by linarith [hY.1])
  have hsU := mul_le_mul
    (show leftRadius d-1≤4/5 by linarith [hR.2])
    (Real.sin_le hz.1) htr.2.2.1 (by norm_num : (0:ℝ)≤4/5)
  have hcU := mul_le_mul_of_nonneg_left (Real.cos_le_one (leftAngle d))
    (show 0≤pivot+1/2-d by linarith [hY.1])
  constructor
  · dsimp [leftAngle,pivot,charge,lowLength] at *
    nlinarith [hd.2]
  · linarith [hz.2,hY.2]

theorem high_left_square {d : ℝ} (hd : 0≤d) :
    qCap<(3/2-(43/50)*d)^2+(pivot+1/2+d)^2 := by
  have hid : (3/2-(43/50)*d)^2+(pivot+1/2+d)^2-qCap=
      1209/25000000+(3/2500)*d+(4349/2500)*d^2 := by
    dsimp [pivot,qCap]
    ring
  have hp : 0<1209/25000000+(3/2500)*d+(4349/2500)*d^2 := by positivity
  linarith

theorem right_bounds_low {d : ℝ} (hd : d∈Icc 0 lowLength) :
    rightRadius (-d)∈Icc (17/10 : ℝ) (19/10) ∧
      rightY (-d)∈Icc (7/10 : ℝ) 1 ∧
      referenceAngle (-d)∈Icc 0 (12/25 : ℝ) ∧
      lowTolerance d∈Icc 0 (1/50 : ℝ) := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  dsimp [rightRadius,rightY,referenceAngle,lowTolerance,lowLength] at *
  refine ⟨⟨by nlinarith [hd.1,hd.2],by nlinarith [sq_nonneg d,hd.1]⟩,
    ⟨by linarith [hd.1],by linarith [hd.2]⟩,
    ⟨by linarith [hd.2],by linarith [hd.1]⟩,
    ⟨by linarith [hd.1],by linarith [hd.2]⟩⟩

theorem right_bounds_high {d : ℝ} (hd : d∈Icc 0 highLength) :
    rightRadius d∈Icc (17/10 : ℝ) (19/10) ∧
      rightY d∈Icc (3/5 : ℝ) (71/100) ∧
      referenceAngle d∈Icc (12/25 : ℝ) (13/20) ∧
      highTolerance d∈Icc 0 (1/50 : ℝ) := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  dsimp [rightRadius,rightY,referenceAngle,highTolerance,highLength] at *
  refine ⟨⟨by nlinarith,by nlinarith [sq_nonneg d]⟩,
    ⟨by linarith [hd.2],by linarith [hd.1]⟩,
    ⟨by linarith [hd.1],by linarith [hd.2]⟩,
    ⟨by linarith [hd.1],by linarith [hd.2]⟩⟩

theorem right_square_low {d : ℝ} (hd : d∈Icc 0 lowLength) :
    qCap<(rightRadius (-d))^2+(rightY (-d))^2 := by
  have hbase : 0<6689/12500000-d/312500 := by
    dsimp [lowLength] at hd
    linarith [hd.2]
  have hid : (rightRadius (-d))^2+(rightY (-d))^2-qCap=
      6689/12500000-d/312500+(42859/625000)*d^2+
        (3504/15625)*d^3+(5329/62500)*d^4 := by
    dsimp [rightRadius,rightY,qCap]
    ring
  have hp : 0<6689/12500000-d/312500+(42859/625000)*d^2+
      (3504/15625)*d^3+(5329/62500)*d^4 := by
    linarith [sq_nonneg d,pow_nonneg hd.1 3,pow_nonneg hd.1 4]
  generalize qCap=Q at hid ⊢
  linarith

theorem right_square_high {d : ℝ} (hd : d∈Icc 0 highLength) :
    qCap<(rightRadius d)^2+(rightY d)^2 := by
  have hcoef : 0≤42859/625000-(3504/15625)*d := by
    dsimp [highLength] at hd
    linarith [hd.2]
  have hid : (rightRadius d)^2+(rightY d)^2-qCap=
      6689/12500000+d/312500+
        d^2*(42859/625000-(3504/15625)*d)+(5329/62500)*d^4 := by
    dsimp [rightRadius,rightY,qCap]
    ring
  have hp : 0<6689/12500000+d/312500+
      d^2*(42859/625000-(3504/15625)*d)+(5329/62500)*d^4 := by
    linarith [mul_nonneg (sq_nonneg d) hcoef,hd.1,pow_nonneg hd.1 4]
  generalize qCap=Q at hid ⊢
  linarith

end SquaresInCircles.Eight.SignedOppositeHardEnvelope
end
end
end

section
/-!
## Reserves of the opposite envelope on the tangent ranges

The comparison angle `referenceAngle` is affine in the middle tangent. The residual lies between
the Taylor polynomials `lowerU` and `upperU`, within the tolerances `lowTolerance` and
`highTolerance` of the charge, and the transverse residual is at least `lowerV`
(`low_U_lower`, `low_U_upper`, `low_V_lower`, `high_U_lower`, `high_U_upper`, `high_V_lower`); one
completed square then covers every opposite angle. The upper budget is below `83/200` on the
whole low and high ranges (`objectiveLow_lt`, `objectiveHigh_lt`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedOppositeHardEnvelope
open EndpointRotationPenalty

def lowerU (x : ℝ) : ℝ :=
  (rightRadius x-1)*(referenceAngle x-(referenceAngle x)^3/6)+
    rightY x*(1-(referenceAngle x)^2/2)

def upperU (x : ℝ) : ℝ :=
  (rightRadius x-1)*(referenceAngle x-(referenceAngle x)^3/6+
    (referenceAngle x)^5/120)+
    rightY x*(1-(referenceAngle x)^2/2+(referenceAngle x)^4/24)

def lowerV (x : ℝ) : ℝ :=
  (rightRadius x-1)*(1-(referenceAngle x)^2/2)-rightY x*referenceAngle x

def upperValue (x η : ℝ) : ℝ :=
  (rightRadius x-1)*(1-(referenceAngle x)^2/2+(referenceAngle x)^4/24)-
    rightY x*(referenceAngle x-(referenceAngle x)^3/6)+
    charge*referenceAngle x+4*η^2

def objectiveLow (d : ℝ) : ℝ :=
  charge*leftAngle d+upperValue (-d) (lowTolerance d)-1/2

def objectiveHigh (d : ℝ) : ℝ :=
  upperValue d (highTolerance d)-1/2-(43/50)*d

theorem low_U_lower {d : ℝ} (hd : d∈Icc 0 lowLength) :
    charge-lowTolerance d≤lowerU (-d) := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h3 := pow_le_pow_left₀ hd.1 hd.2 3
  have h4 := pow_le_pow_left₀ hd.1 hd.2 4
  have hcoef : 0≤7074577/62500000-(102461243/500000000)*d-
      (64127809/1200000000)*d^2-(87451/1250000)*d^3-
      (2174743/12000000)*d^4 := by
    dsimp [lowLength] at hd h2 h3 h4
    nlinarith [hd.2]
  have hid : lowerU (-d)-charge+lowTolerance d=
      1537681/3828125000+d*(7074577/62500000-
        (102461243/500000000)*d-(64127809/1200000000)*d^2-
        (87451/1250000)*d^3-(2174743/12000000)*d^4) := by
    dsimp [lowerU,rightRadius,rightY,referenceAngle,charge,lowTolerance]
    ring
  have hp : 0≤1537681/3828125000+d*(7074577/62500000-
      (102461243/500000000)*d-(64127809/1200000000)*d^2-
      (87451/1250000)*d^3-(2174743/12000000)*d^4) := by
    linarith [mul_nonneg hd.1 hcoef]
  linarith

theorem low_U_upper {d : ℝ} (hd : d∈Icc 0 lowLength) :
    upperU (-d)≤charge+lowTolerance d := by
  have h4 := pow_le_pow_left₀ hd.1 hd.2 4
  have hcoef : 0≤145861629877/750000000000-
      (2089928023/96000000000)*d^4 := by
    dsimp [lowLength] at h4
    nlinarith
  have hquad : 0≤22123053791/11962890625000-
      (2373256837/195312500000)*d+(180164586367/1562500000000)*d^2 := by
    nlinarith [sq_nonneg (d-13/220),sq_nonneg d,hd.1]
  have hid : charge+lowTolerance d-upperU (-d)=
      (22123053791/11962890625000-(2373256837/195312500000)*d+
        (180164586367/1562500000000)*d^2)+
      d^3*(145861629877/750000000000-(2089928023/96000000000)*d^4)+
      (188270083717/2400000000000)*d^4+
      (17508975057/640000000000)*d^5+(10158731/2000000000)*d^6 := by
    dsimp [upperU,rightRadius,rightY,referenceAngle,charge,lowTolerance]
    ring
  have hp : 0≤(22123053791/11962890625000-(2373256837/195312500000)*d+
      (180164586367/1562500000000)*d^2)+
      d^3*(145861629877/750000000000-(2089928023/96000000000)*d^4)+
      (188270083717/2400000000000)*d^4+
      (17508975057/640000000000)*d^5+(10158731/2000000000)*d^6 := by
    linarith [mul_nonneg (pow_nonneg hd.1 3) hcoef,pow_nonneg hd.1 4,pow_nonneg hd.1 5,
      pow_nonneg hd.1 6]
  linarith

theorem low_V_lower {d : ℝ} (hd : d∈Icc 0 lowLength) :
    2/5≤lowerV (-d) := by
  have hcoef : 0≤2275681/2500000-(239937/20000000)*d := by
    dsimp [lowLength] at hd
    linarith [hd.2]
  have hid : lowerV (-d)-2/5=28961/3125000+
      d*(2275681/2500000-(239937/20000000)*d)+
      (3813/15625)*d^3+(70153/200000)*d^4 := by
    dsimp [lowerV,rightRadius,rightY,referenceAngle]
    ring
  have hp : 0≤28961/3125000+d*(2275681/2500000-(239937/20000000)*d)+
      (3813/15625)*d^3+(70153/200000)*d^4 := by
    linarith [mul_nonneg hd.1 hcoef,pow_nonneg hd.1 3,pow_nonneg hd.1 4]
  linarith

theorem high_U_lower {d : ℝ} (hd : d∈Icc 0 highLength) :
    charge-highTolerance d≤lowerU d := by
  have h3 := pow_le_pow_left₀ hd.1 hd.2 3
  have hcoef : 0≤1675423/62500000-(102461243/500000000)*d-
      (87451/1250000)*d^3 := by
    dsimp [highLength] at hd h3
    nlinarith [hd.2]
  have hid : lowerU d-charge+highTolerance d=
      1537681/3828125000+d*(1675423/62500000-
        (102461243/500000000)*d-(87451/1250000)*d^3)+
      (64127809/1200000000)*d^3+(2174743/12000000)*d^5 := by
    dsimp [lowerU,rightRadius,rightY,referenceAngle,charge,highTolerance]
    ring
  have hp : 0≤1537681/3828125000+d*(1675423/62500000-
      (102461243/500000000)*d-(87451/1250000)*d^3)+
      (64127809/1200000000)*d^3+(2174743/12000000)*d^5 := by
    linarith [mul_nonneg hd.1 hcoef,pow_nonneg hd.1 3,pow_nonneg hd.1 5]
  linarith

theorem high_U_upper {d : ℝ} (hd : d∈Icc 0 highLength) :
    upperU d≤charge+highTolerance d := by
  have hcoef2 : 0≤180164586367/1562500000000-
      (145861629877/750000000000)*d := by
    dsimp [highLength] at hd
    linarith [hd.2]
  have hcoef4 : 0≤188270083717/2400000000000-
      (17508975057/640000000000)*d := by
    dsimp [highLength] at hd
    linarith [hd.2]
  have hid : charge+highTolerance d-upperU d=
      22123053791/11962890625000+(29717006837/195312500000)*d+
      d^2*(180164586367/1562500000000-(145861629877/750000000000)*d)+
      d^4*(188270083717/2400000000000-(17508975057/640000000000)*d)+
      (10158731/2000000000)*d^6+(2089928023/96000000000)*d^7 := by
    dsimp [upperU,rightRadius,rightY,referenceAngle,charge,highTolerance]
    ring
  have hp : 0≤22123053791/11962890625000+(29717006837/195312500000)*d+
      d^2*(180164586367/1562500000000-(145861629877/750000000000)*d)+
      d^4*(188270083717/2400000000000-(17508975057/640000000000)*d)+
      (10158731/2000000000)*d^6+(2089928023/96000000000)*d^7 := by
    linarith [mul_nonneg (pow_nonneg hd.1 2) hcoef2,mul_nonneg (pow_nonneg hd.1 4) hcoef4,
      hd.1,pow_nonneg hd.1 6,pow_nonneg hd.1 7]
  linarith

theorem high_V_lower {d : ℝ} (hd : d∈Icc 0 highLength) :
    3/10≤lowerV d := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h3 := pow_le_pow_left₀ hd.1 hd.2 3
  have hbase : 0≤341461/3125000-(2275681/2500000)*d-
      (239937/20000000)*d^2-(3813/15625)*d^3 := by
    dsimp [highLength] at hd h2 h3
    nlinarith [hd.2]
  have hid : lowerV d-3/10=
      341461/3125000-(2275681/2500000)*d-
        (239937/20000000)*d^2-(3813/15625)*d^3+(70153/200000)*d^4 := by
    dsimp [lowerV,rightRadius,rightY,referenceAngle]
    ring
  nlinarith [pow_nonneg hd.1 4]

/-- The budget on the low range is below `83/200`: once its positive tail is collected into one
coefficient, it decreases from its value at the left end. -/
theorem objectiveLow_lt {d : ℝ} (hd : d∈Icc 0 lowLength) :
    objectiveLow d<83/200 := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h3 := pow_le_pow_left₀ hd.1 hd.2 3
  have h4 := pow_nonneg hd.1 4
  have h5 := pow_nonneg hd.1 5
  have hcoef : -1795899747/15312500000+
      (4405933259/12500000000)*d+(2492993371/30000000000)*d^2+
      (253068779/32000000000)*d^3-(268119/50000000)*d^4-
      (67417033/960000000)*d^5≤0 := by
    dsimp [lowLength] at hd h2 h3
    nlinarith [hd.2]
  have hm := mul_nonpos_of_nonneg_of_nonpos hd.1 hcoef
  have hid : objectiveLow d=39623908607/95703125000+
      d*(-1795899747/15312500000+
        (4405933259/12500000000)*d+(2492993371/30000000000)*d^2+
        (253068779/32000000000)*d^3-(268119/50000000)*d^4-
        (67417033/960000000)*d^5) := by
    dsimp [objectiveLow,upperValue,leftAngle,rightRadius,rightY,
      referenceAngle,lowTolerance,charge]
    ring
  have hconstant : (39623908607/95703125000 : ℝ)<83/200 := by norm_num
  linarith

/-- The budget on the high range is below `83/200`, with the same pivot; the left circle enters
through its tangent-line upper bound. -/
theorem objectiveHigh_lt {d : ℝ} (hd : d∈Icc 0 highLength) :
    objectiveHigh d<83/200 := by
  have h3 := pow_le_pow_left₀ hd.1 hd.2 3
  have h4 := pow_le_pow_left₀ hd.1 hd.2 4
  have h2 := pow_nonneg hd.1 2
  have h5 := pow_nonneg hd.1 5
  have hcoef : -822925253/15312500000+
      (4825933259/12500000000)*d-(2492993371/30000000000)*d^2+
      (253068779/32000000000)*d^3+(268119/50000000)*d^4-
      (67417033/960000000)*d^5≤0 := by
    dsimp [highLength] at hd h3 h4
    nlinarith [hd.2]
  have hm := mul_nonpos_of_nonneg_of_nonpos hd.1 hcoef
  have hid : objectiveHigh d=39623908607/95703125000+
      d*(-822925253/15312500000+
        (4825933259/12500000000)*d-(2492993371/30000000000)*d^2+
        (253068779/32000000000)*d^3+(268119/50000000)*d^4-
        (67417033/960000000)*d^5) := by
    dsimp [objectiveHigh,upperValue,rightRadius,rightY,referenceAngle,highTolerance,charge]
    ring
  have hconstant : (39623908607/95703125000 : ℝ)<83/200 := by norm_num
  linarith

end SquaresInCircles.Eight.SignedOppositeHardEnvelope
end
end
end

section
/-!
## The complete free signed opposite-angle envelope

Rotating around an explicit affine comparison
angle leaves one residual completed square.  The bounds are uniform over
the entire opposite-angle interval, so the opposite tangent may have
either sign.  The larger middle tangent cannot support a wrong weak
intermediate sign once the original outer budget is imposed.

This file proves the local scalar inequality directly from the two
actual circle inequalities and the two actual hard contacts.  It uses
neither a chosen maximizer nor an assumed curvature or endpoint result.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedOppositeHardEnvelope
open EndpointRotationPenalty

def referenceU (x : ℝ) : ℝ :=
  (rightRadius x-1)*Real.sin (referenceAngle x)+rightY x*Real.cos (referenceAngle x)

def referenceV (x : ℝ) : ℝ :=
  (rightRadius x-1)*Real.cos (referenceAngle x)-rightY x*Real.sin (referenceAngle x)

def rightFunction (x v : ℝ) : ℝ :=
  (rightRadius x-1)*Real.cos v-rightY x*Real.sin v+charge*v

theorem rotation_identity (P Y u d : ℝ) :
    P*Real.cos (u+d)-Y*Real.sin (u+d)=
      (P*Real.cos u-Y*Real.sin u)*Real.cos d-
        (P*Real.sin u+Y*Real.cos u)*Real.sin d := by
  rw [Real.cos_add,Real.sin_add]
  ring

private theorem signed_cos_upper {d : ℝ} :
    Real.cos d≤1-d^2/2+d^4/24 := by
  by_cases hd : 0≤d
  · exact cos_upper_four hd
  · have hh := cos_upper_four (show 0≤-d by linarith)
    rw [Real.cos_neg] at hh
    nlinarith

/-- A full-interval rotation estimate.  On the large tangent range the
positive displacement is at most one quarter; negative displacements
already have the favorable sine sign. -/
theorem rotation_upper {U V d η : ℝ}
    (hU : U∈Icc 0 (11/10 : ℝ))
    (hV : (2/5 : ℝ)≤V ∨ ((3/10 : ℝ)≤V ∧ d≤1/4))
    (hd : d∈Icc (-frameCap) frameCap)
    (hη : |charge-U|≤η) :
    V*Real.cos d-U*Real.sin d+charge*d≤V+4*η^2 := by
  have hdabs : |d|≤frameCap := abs_le.mpr hd
  have h2 : d^2≤49/100 := by
    have hh := pow_le_pow_left₀ (abs_nonneg d) hdabs 2
    simp only [frameCap,sq_abs] at hh
    linarith
  have h4 : d^4≤(49/100 : ℝ)*d^2 := by
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg d)]
  have hcos := signed_cos_upper (d := d)
  have hcos0 : Real.cos d-1≤0 := sub_nonpos.mpr (Real.cos_le_one d)
  have hparabolic : V*Real.cos d-U*Real.sin d+charge*d≤
      V+(charge-U)*d-d^2/16 := by
    by_cases hd0 : 0≤d
    · have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hd0) hU.1
      have hU3 := mul_le_mul_of_nonneg_right hU.2 (pow_nonneg hd0 3)
      rcases hV with hV | ⟨hV,hdshort⟩
      · have hcV := mul_le_mul_of_nonpos_right hV hcos0
        have hc := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤2/5)
        have h3 : d^3≤(7/10 : ℝ)*d^2 := by
          have hh := mul_le_mul_of_nonneg_right hd.2 (sq_nonneg d)
          dsimp [frameCap] at hh
          nlinarith
        nlinarith [sq_nonneg d]
      · have hcV := mul_le_mul_of_nonpos_right hV hcos0
        have hc := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤3/10)
        have h3 : d^3≤(1/4 : ℝ)*d^2 := by
          nlinarith [mul_le_mul_of_nonneg_right hdshort (sq_nonneg d)]
        nlinarith [sq_nonneg d]
    · have hs0 : d≤Real.sin d := by
        have hh := Real.sin_le (show 0≤-d by linarith)
        rw [Real.sin_neg] at hh
        linarith
      have hs := mul_le_mul_of_nonneg_left hs0 hU.1
      have hV0 : (3/10 : ℝ)≤V := by
        rcases hV with h | h
        · linarith
        · exact h.1
      have hcV := mul_le_mul_of_nonpos_right hV0 hcos0
      have hc := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤3/10)
      nlinarith [sq_nonneg d]
  have hη2 : (charge-U)^2≤η^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (charge-U)) hη 2
  nlinarith [sq_nonneg (d/4-2*(charge-U))]

theorem reference_taylor {x η : ℝ}
    (hR : 1≤rightRadius x) (hY : 0≤rightY x) (hu : 0≤referenceAngle x) :
    lowerU x≤referenceU x ∧ referenceU x≤upperU x ∧
      lowerV x≤referenceV x ∧
      referenceV x+charge*referenceAngle x+4*η^2≤upperValue x η := by
  have hP : 0≤rightRadius x-1 := by linarith
  have hsL := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hu) hP
  have hcL := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (x := referenceAngle x)) hY
  have hsU := mul_le_mul_of_nonneg_left (sin_upper_five hu) hP
  have hcU := mul_le_mul_of_nonneg_left (cos_upper_four hu) hY
  have hvcL := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (x := referenceAngle x)) hP
  have hvsU := mul_le_mul_of_nonneg_left (Real.sin_le hu) hY
  have hvcU := mul_le_mul_of_nonneg_left (cos_upper_four hu) hP
  have hvsL := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hu) hY
  dsimp [lowerU,upperU,lowerV,referenceU,referenceV,upperValue]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem right_function_upper {x η v : ℝ}
    (hU : referenceU x∈Icc 0 (11/10 : ℝ))
    (hV : (2/5 : ℝ)≤referenceV x ∨
      ((3/10 : ℝ)≤referenceV x ∧ v-referenceAngle x≤1/4))
    (hd : v-referenceAngle x∈Icc (-frameCap) frameCap)
    (hη : |charge-referenceU x|≤η) :
    rightFunction x v≤referenceV x+charge*referenceAngle x+4*η^2 := by
  have hh := rotation_upper hU hV hd hη
  have hid := rotation_identity (rightRadius x-1) (rightY x)
    (referenceAngle x) (v-referenceAngle x)
  rw [show referenceAngle x+(v-referenceAngle x)=v by ring] at hid
  change (rightRadius x-1)*Real.cos v-rightY x*Real.sin v=
    referenceV x*Real.cos (v-referenceAngle x)-
      referenceU x*Real.sin (v-referenceAngle x) at hid
  dsimp [rightFunction]
  nlinarith

/-- The opposite tangent is unrestricted.  Every actual opposite angle
is paid by the same explicit comparison and residual square. -/
theorem opposite_low {d v : ℝ} (hd : d∈Icc 0 lowLength)
    (hv : v∈Icc 0 frameCap) :
    rightFunction (-d) v≤upperValue (-d) (lowTolerance d) := by
  obtain ⟨hR,hY,hu,hη⟩ := right_bounds_low hd
  obtain ⟨hL,hU,hV,hvalue⟩ := reference_taylor
    (η := lowTolerance d) (by linarith [hR.1]) (by linarith [hY.1]) hu.1
  have hres : |charge-referenceU (-d)|≤lowTolerance d := by
    rw [abs_le]
    constructor <;> linarith [low_U_lower hd,low_U_upper hd]
  have htransverse : referenceU (-d)∈Icc 0 (11/10 : ℝ) := by
    have hres' := abs_le.mp hres
    dsimp [charge] at hres'
    constructor <;> linarith [hres'.1,hres'.2,hη.2]
  have hlong : (2/5 : ℝ)≤referenceV (-d) := (low_V_lower hd).trans hV
  have hdisplacement : v-referenceAngle (-d)∈Icc (-frameCap) frameCap := by
    dsimp [frameCap] at *
    constructor <;> linarith [hv.1,hv.2,hu.1,hu.2]
  exact (right_function_upper htransverse (Or.inl hlong) hdisplacement hres).trans hvalue

theorem opposite_high {d v : ℝ} (hd : d∈Icc 0 highLength)
    (hv : v∈Icc 0 frameCap) :
    rightFunction d v≤upperValue d (highTolerance d) := by
  obtain ⟨hR,hY,hu,hη⟩ := right_bounds_high hd
  obtain ⟨hL,hU,hV,hvalue⟩ := reference_taylor
    (η := highTolerance d) (by linarith [hR.1]) (by linarith [hY.1])
    (by linarith [hu.1])
  have hres : |charge-referenceU d|≤highTolerance d := by
    rw [abs_le]
    constructor <;> linarith [high_U_lower hd,high_U_upper hd]
  have htransverse : referenceU d∈Icc 0 (11/10 : ℝ) := by
    have hres' := abs_le.mp hres
    dsimp [charge] at hres'
    constructor <;> linarith [hres'.1,hres'.2,hη.2]
  have hlong : (3/10 : ℝ)≤referenceV d := (high_V_lower hd).trans hV
  have hshort : v-referenceAngle d≤1/4 := by
    dsimp [frameCap] at hv
    linarith [hv.2,hu.1]
  have hdisplacement : v-referenceAngle d∈Icc (-frameCap) frameCap := by
    dsimp [frameCap] at *
    constructor <;> linarith [hv.1,hv.2,hu.1,hu.2]
  exact (right_function_upper htransverse (Or.inr ⟨hlong,hshort⟩)
    hdisplacement hres).trans hvalue

theorem clipped_tail {U d : ℝ} (hU : U∈Icc charge (3/2 : ℝ))
    (hd : d∈Icc 0 frameCap) :
    (1/2)*Real.cos d-U*Real.sin d+charge*d≤1/2 := by
  have hU0 : 0≤U := by dsimp [charge] at hU; linarith [hU.1]
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h3 := mul_le_mul_of_nonneg_right hd.2 (sq_nonneg d)
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg d)
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hd.1) hU0
  have hUsmall := mul_le_mul_of_nonneg_right hU.2 (pow_nonneg hd.1 3)
  have hUlarge := mul_le_mul_of_nonneg_right hU.1 hd.1
  have hc := cos_upper_four hd.1
  dsimp [frameCap] at h2 h3 h4
  nlinarith [sq_nonneg d]

/-- The clipped left contribution is bounded without defining its
inverse contact angle.  This includes both sides of that contact. -/
theorem left_clipped {a g d z : ℝ} (hd : d∈Icc 0 lowLength)
    (hA : (a+1/2)^2+(pivot+1/2-d)^2≤qCap)
    (hz : z∈Icc 0 frameCap) (hg : g≤0)
    (hGA : g+1/2≤(a-1/2)*Real.cos z-(pivot+1/2-d)*Real.sin z) :
    g+charge*z≤charge*leftAngle d := by
  have hp : 0<charge := by norm_num [charge]
  by_cases hzlow : z≤leftAngle d
  · nlinarith [mul_le_mul_of_nonneg_left hzlow hp.le]
  · obtain ⟨hR,hu,hY⟩ := left_bounds hd
    have har : a+1/2≤leftRadius d := by
      have hs := left_square_reserve hd
      nlinarith [hR.1]
    have hzcos : 0≤Real.cos z := by linarith [(transport_trig hz).1]
    have hcap := mul_le_mul_of_nonneg_right
      (show a-1/2≤leftRadius d-1 by linarith) hzcos
    have hδ : z-leftAngle d∈Icc 0 frameCap :=
      ⟨by linarith,by linarith [hz.2,hu.1]⟩
    have hδcos : 0≤Real.cos (z-leftAngle d) := by
      linarith [(transport_trig hδ).1]
    have hcontact := mul_le_mul_of_nonneg_right (left_angle_contact hd) hδcos
    have hU := left_angle_transverse hd
    have htail := clipped_tail hU hδ
    have hrot := rotation_identity (leftRadius d-1) (pivot+1/2-d)
      (leftAngle d) (z-leftAngle d)
    rw [show leftAngle d+(z-leftAngle d)=z by ring] at hrot
    nlinarith

theorem left_high {a g d z : ℝ} (hd : d∈Icc 0 highLength)
    (ha : 1/2<a) (hA : (a+1/2)^2+(pivot+1/2+d)^2≤qCap)
    (hz : z∈Icc 0 frameCap)
    (hGA : g+1/2≤(a-1/2)*Real.cos z-(pivot+1/2+d)*Real.sin z) :
    g+charge*z≤ -(43/50)*d := by
  have hR : 0<3/2-(43/50)*d := by
    dsimp [highLength] at hd
    linarith [hd.2]
  have haR : a+1/2≤3/2-(43/50)*d := by
    nlinarith [high_left_square hd.1]
  have hY : 0≤pivot+1/2+d := by dsimp [pivot]; linarith [hd.1]
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hz2 hz.1
  have hsin : (9/10)*z≤Real.sin z := by
    dsimp [frameCap] at hz3
    nlinarith [Real.sin_ge_sub_cube hz.1,hz.1]
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one z)
    (show 0≤a-1/2 by linarith)
  have hs := mul_le_mul_of_nonneg_left hsin hY
  have hcoefficient : charge≤(9/10)*(pivot+1/2+d) := by
    dsimp [charge,pivot]
    linarith [hd.1]
  have hm := mul_le_mul_of_nonneg_right hcoefficient hz.1
  nlinarith

/-- Complete local signed envelope at the larger middle tangent.
There is no sign premise on t and no envelope premise. -/
theorem actual_middle_wrong_bound {aA aB b g t z v : ℝ}
    (hb : b∈Icc (1/2 : ℝ) (9/10)) (haA : 1/2<aA)
    (hA : (aA+1/2)^2+(b+1/2)^2≤qCap)
    (hB : (aB+1/2)^2+(3/2-b)^2≤qCap)
    (hz : z∈Icc 0 frameCap) (hv : v∈Icc 0 frameCap) (hg : g≤0)
    (hGA : g+1/2≤(aA-1/2)*Real.cos z-(b+1/2)*Real.sin z)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(3/2-b)*Real.sin v) :
    g+t+charge*(z+v)<83/200 := by
  have hcos : 0≤Real.cos v := by linarith [(transport_trig hv).1]
  by_cases hbp : b≤pivot
  · let d := pivot-b
    have hd : d∈Icc 0 lowLength := low_domain ⟨hb.1,hbp⟩
    have hyA : b+1/2=pivot+1/2-d := by dsimp [d]; ring
    have hyB : 3/2-b=rightY (-d) := by dsimp [rightY,d,pivot]; ring
    have haB : aB+1/2≤rightRadius (-d) := by
      have hsq := right_square_low hd
      rw [←hyB] at hsq
      nlinarith [(right_bounds_low hd).1.1]
    have hc := mul_le_mul_of_nonneg_right
      (show aB-1/2≤rightRadius (-d)-1 by linarith) hcos
    have hleft := left_clipped hd (by simpa only [←hyA] using hA) hz hg
      (by simpa only [←hyA] using hGA)
    have hright := opposite_low hd hv
    have hpoly := objectiveLow_lt hd
    rw [hyB] at hBT
    dsimp [rightFunction] at hright
    dsimp [objectiveLow] at hpoly
    nlinarith
  · let d := b-pivot
    have hd : d∈Icc 0 highLength := high_domain ⟨by linarith,hb.2⟩
    have hyA : b+1/2=pivot+1/2+d := by dsimp [d]; ring
    have hyB : 3/2-b=rightY d := by dsimp [rightY,d,pivot]; ring
    have haB : aB+1/2≤rightRadius d := by
      have hsq := right_square_high hd
      rw [←hyB] at hsq
      nlinarith [(right_bounds_high hd).1.1]
    have hc := mul_le_mul_of_nonneg_right
      (show aB-1/2≤rightRadius d-1 by linarith) hcos
    have hleft := left_high hd haA (by simpa only [←hyA] using hA) hz
      (by simpa only [←hyA] using hGA)
    have hright := opposite_high hd hv
    have hpoly := objectiveHigh_lt hd
    rw [hyB] at hBT
    dsimp [rightFunction] at hright
    dsimp [objectiveHigh] at hpoly
    nlinarith

end SquaresInCircles.Eight.SignedOppositeHardEnvelope
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace SignedOppositeHardEnvelope
open EndpointRotationPenalty EndpointBudgetScalars

theorem budget_reserve : (83/200 : ℝ)<S0 := by
  have hs := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
  have hs0 := Real.sqrt_nonneg (qCap-1)
  dsimp [S0,qCap] at *
  nlinarith

theorem negative_hard_contact {G A : SignedPoint} {z : ℝ}
    (hz : z∈Icc 0 frameCap) (hGA : quarterFeasible G A (-z) 0) :
    -G.y+1/2≤(A.a-1/2)*Real.cos z-(A.y+1/2)*Real.sin z := by
  have hh := hGA
  rw [quarterFeasible,edgeWidth_negative_formula hz] at hh
  simp [quarterProjection,Real.cos_neg,Real.sin_neg] at hh
  linarith

end SignedOppositeHardEnvelope

namespace SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars SignedOppositeHardEnvelope

/-- With A and B on a common frame, `yA - yB = 1`, `θT ≤ θA ≤ θG` and `yA ≥ 1/2`, G has `yG < 0`;
the tangent of T, the signs of the two outer errors and the zero owners are unrestricted. -/
theorem HardOuterGeometry.large_middle_G_negative {q : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hlarge : 1/2≤(I.cycle.point A).y) :
    (I.cycle.point G).y<0 := by
  by_contra! hwrong
  let z := I.cycle.theta G-I.cycle.theta A
  let v := I.cycle.theta B-I.cycle.theta T
  have hz : z∈Icc 0 frameCap := by
    refine ⟨sub_nonneg.mpr hAG,?_⟩
    exact (le_abs_self z).trans (I.necessary.spread G A)
  have hv : v∈Icc 0 frameCap := by
    refine ⟨by dsimp [v]; linarith,?_⟩
    exact (le_abs_self v).trans (I.necessary.spread B T)
  have hyB : -(I.cycle.point B).y+1/2=3/2-(I.cycle.point A).y := by linarith
  have hA : ((I.cycle.point A).a+1/2)^2+((I.cycle.point A).y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,
      abs_of_nonneg I.anchors_normal.A_nonneg] using
        (I.necessary.contained A).trans hq
  have hB : ((I.cycle.point B).a+1/2)^2+(3/2-(I.cycle.point A).y)^2≤qCap := by
    have hh := (I.necessary.contained B).trans hq
    change ((I.cycle.point B).a+1/2)^2+(|(I.cycle.point B).y|+1/2)^2≤qCap at hh
    rw [abs_of_nonpos I.anchors_normal.B_nonpos,hyB] at hh
    exact hh
  have hb : (I.cycle.point A).y∈Icc (1/2 : ℝ) (9/10) := by
    have hh := SignedPoint.coordinate_bounds (I.necessary.sorted A) (I.necessary.core A)
      (I.necessary.contained A) hq
    exact ⟨hlarge,(le_abs_self _).trans hh.2.2.le⟩
  have haA := SignedPoint.primary_gt_half (I.necessary.sorted A) (I.necessary.core A)
  have hga : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,delta,next,word,G,A,quarterFeasible] using I.GA_hard
  have hbt : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
    simpa [v,Feasible,slack,edge,delta,next,word,B,T,quarterFeasible] using I.BT_hard
  have hgaBound := negative_hard_contact hz hga
  have hbtReflected : quarterFeasible (I.cycle.point T).reflect
      (I.cycle.point B).reflect (-v) 0 := by
    simpa [reflectedOwner] using
      (quarterFeasible_reflect (I.cycle.point B) (I.cycle.point T) (-v) 2).2 hbt
  have hbtBound := negative_hard_contact hv hbtReflected
  simp only [SignedPoint.reflect,neg_neg] at hbtBound
  rw [hyB] at hbtBound
  have hscalar := actual_middle_wrong_bound hb haA hA hB hz hv
    (show -(I.cycle.point G).y≤0 by linarith) hgaBound hbtBound
  obtain ⟨hHG,hTD⟩ := signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs
  have hendpoint := I.endpoint_bound hq
  have hreserve := budget_reserve
  dsimp [z,v,EndpointRotationPenalty.charge,epsilon] at hscalar hHG hTD hendpoint
  nlinarith

/-- The reflected statement: with `-yB ≥ 1/2`, T has `yT > 0`. The point E and the sign of G are
kept as they are. -/
theorem HardOuterGeometry.large_middle_T_positive {q : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hlarge : 1/2≤ -(I.cycle.point B).y) :
    0<(I.cycle.point T).y := by
  have hAB' : I.reflected.cycle.theta A=I.reflected.cycle.theta B := by
    change I.cycle.theta B-I.cycle.theta B=I.cycle.theta B-I.cycle.theta A
    linarith
  have hsum' : (I.reflected.cycle.point A).y-(I.reflected.cycle.point B).y=1 := by
    change -(I.cycle.point B).y-(-(I.cycle.point A).y)=1
    linarith
  have hTA' : I.reflected.cycle.theta T≤I.reflected.cycle.theta A := by
    change I.cycle.theta B-I.cycle.theta G≤I.cycle.theta B-I.cycle.theta B
    linarith
  have hAG' : I.reflected.cycle.theta A≤I.reflected.cycle.theta G := by
    change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta T
    linarith
  have hlarge' : 1/2≤(I.reflected.cycle.point A).y := hlarge
  have hh := I.reflected.large_middle_G_negative hq hAB' hsum' hTA' hAG' hlarge'
  change -(I.cycle.point T).y<0 at hh
  linarith

theorem HardInput.large_middle_G_negative {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hlarge : 1/2≤(I.cycle.point A).y) :
    (I.cycle.point G).y<0 :=
  I.outerGeometry.large_middle_G_negative hq hAB hsum hTA hAG hlarge

theorem HardInput.large_middle_T_positive {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hlarge : 1/2≤ -(I.cycle.point B).y) :
    0<(I.cycle.point T).y :=
  I.outerGeometry.large_middle_T_positive hq hAB hsum hTA hAG hlarge

end SignedCycle
end SquaresInCircles.Eight
end
end
end
