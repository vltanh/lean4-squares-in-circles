import SquaresInCircles.Six.Normalization.PinReflection
import SquaresInCircles.Six.Analytic.CardinalFrame

/-!
# Separation along a side of the central square

An exterior square separated from the central square along one of its sides
has its frame within `2/5` of the direction of that side
(`PinPacking.cardinal_angle`): turned to that direction, the square lies beyond
a line at distance at least `coreRadius` from the origin, and
`primary_cap_angle` bounds its angle. So D, in its half window, is not
separated along the south side, and every exterior square is separated along
its own axis or along the matching side: east for E, north for N, west for W
and D, south for S (`PinPacking.two_choice`). `canonicalOwn` records which,
counting a square separated along both as separated along the side.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

/-- The direction of a side of the central square. -/
def cardinalCenter : CentralAxis → ℝ
  | .east => 0
  | .north => Real.pi/2
  | .west => Real.pi
  | .south => 3*Real.pi/2
  | _ => 0

/-- The exterior squares in the six cases of `PinPacking.cardinal_angle`:
E, N, W, D, D, S. -/
def cardinalCasePin : Fin 6 → Fin 5 := ![0,1,2,3,3,4]
/-- The sides of the central square in those cases: east, north, west, west,
south, south. -/
def cardinalCaseAxis : Fin 6 → CentralAxis := ![.east,.north,.west,.west,.south,.south]

private def caseDepth (j : Fin 6) (cx cy : ℝ) : ℝ :=
  ![1/2+cx,1/2+cy,1/2-cx,1/2-cx,1/2-cy,1/2-cy] j

private lemma sine_south : Real.sin (3*Real.pi/2) = -1 := by
  rw [show 3*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.sin_add]
  simp

private lemma cosine_south : Real.cos (3*Real.pi/2) = 0 := by
  rw [show 3*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.cos_add]
  simp

/-- The margin along a side of the central square, in the frame turned to that
side. -/
private lemma case_margin_identity (j : Fin 6) (t a b cx cy : ℝ) :
    centralMargin (cardinalCaseAxis j) t a b cx cy =
      a*Real.cos (t-cardinalCenter (cardinalCaseAxis j))-
      b*Real.sin (t-cardinalCenter (cardinalCaseAxis j))-
      (|Real.cos (t-cardinalCenter (cardinalCaseAxis j))|+
        |Real.sin (t-cardinalCenter (cardinalCaseAxis j))|)/2-caseDepth j cx cy := by
  fin_cases j
  all_goals simp only [cardinalCaseAxis,cardinalCenter,centralMargin,centerX,centerY,
    angularWidth,caseDepth,Fin.reduceFinMk,Matrix.cons_val,Real.cos_sub,Real.sin_sub,
    Real.cos_pi,Real.sin_pi,Real.cos_pi_div_two,Real.sin_pi_div_two,
    sine_south,cosine_south,abs_neg,mul_zero,mul_one,mul_neg_one,
    zero_add,add_zero,sub_zero,zero_sub,neg_neg]
  all_goals ring

/-- A square separated from the central square along a side has its angle
within `2/5` of the direction of that side. -/
theorem PinPacking.cardinal_angle {R : ℝ} (P : PinPacking R) (j : Fin 6)
    (hk : 0 ≤ centralMargin (cardinalCaseAxis j)
      (P.phase (cardinalCasePin j)) (P.radial (cardinalCasePin j))
      (P.transverse (cardinalCasePin j)) P.center.1 P.center.2) :
    |P.phase (cardinalCasePin j)-cardinalCenter (cardinalCaseAxis j)| < 2/5 := by
  let i := cardinalCasePin j
  let t := P.phase i-cardinalCenter (cardinalCaseAxis j)
  let h := caseDepth j P.center.1 P.center.2
  have ha0 : 0 ≤ P.radial i := by linarith [(P.contained i).half_le]
  have ha : |P.radial i| ≤ rho0 := by
    simpa only [abs_of_nonneg ha0] using (P.contained i).a_le_rho0
  have hb : |P.transverse i| < 1/2 :=
    (P.contained i).u_lt_half (P.avoidsCore i)
  have hh : coreRadius ≤ h := by
    have hsum := c0_add_coreRadius
    dsimp [h]
    fin_cases j <;> dsimp [caseDepth] <;>
      linarith [P.box.1.1,P.box.1.2,P.box.2.1,P.box.2.2,c0_pos]
  have ht : |t| ≤ 3*Real.pi/4 := by
    have hw := P.window i
    dsimp [i,t] at *
    fin_cases j <;>
      norm_num [cardinalCasePin,cardinalCaseAxis,cardinalCenter,phaseCenter,
        windowLower,windowUpper] at hw ⊢
    all_goals apply abs_le.mpr
    all_goals constructor <;> linarith [hw.1,hw.2,Real.pi_gt_d2]
  have hbox : (|P.radial i|+1/2)^2+(|P.transverse i|+1/2)^2 ≤ Q0 := by
    simpa only [abs_of_nonneg ha0] using (P.contained i).containment
  have hcap : h+(|Real.cos t|+|Real.sin t|)/2 ≤
      P.radial i*Real.cos t-P.transverse i*Real.sin t := by
    rw [case_margin_identity] at hk
    change 0 ≤ P.radial i*Real.cos t-P.transverse i*Real.sin t-
      (|Real.cos t|+|Real.sin t|)/2-h at hk
    linarith
  exact Analytic.primary_cap_angle ha hb hh ht hbox hcap

/-- In its half window, D is not separated from the central square along the
south side. -/
theorem PinPacking.D_south_negative {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    centralMargin .south (P.phase 3) (P.radial 3) (P.transverse 3) P.center.1 P.center.2 < 0 := by
  by_contra! h
  have hh := P.cardinal_angle 4 h
  have hl := (abs_lt.mp hh).1
  norm_num [cardinalCasePin,cardinalCaseAxis,cardinalCenter] at hl
  linarith [Real.pi_gt_d2]

/-- The side of the central square matching each exterior square: east for E,
north for N, west for W and D, south for S. -/
def matchingCardinal : Fin 5 → CentralAxis := ![.east,.north,.west,.west,.south]

/-- Each exterior square is separated from the central square along the
matching side or along its own axis. -/
theorem PinPacking.two_choice {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) (i : Fin 5) :
    0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
        P.center.1 P.center.2 ∨
      0 ≤ centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2 := by
  obtain ⟨k,hk⟩ := P.separator i
  have ha := P.allowed_separator i k hk
  by_cases hc : k=matchingCardinal i
  · exact Or.inl (by simpa [hc] using hk)
  by_cases ho : k=.own
  · exact Or.inr (by simpa [ho] using hk)
  have hlast : i=3 ∧ k=.south := by
    fin_cases i <;> cases k <;> simp [matchingCardinal,allowed] at *
  rcases hlast with ⟨rfl,rfl⟩
  linarith [P.D_south_negative hD]

/-- Whether square `i` is not separated from the central square along the
matching side, so that it is separated along its own axis
(`PinPacking.own_of_canonicalOwn`). -/
def PinPacking.canonicalOwn {R : ℝ} (P : PinPacking R) (i : Fin 5) : Bool :=
  decide (centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
    P.center.1 P.center.2 < 0)

lemma PinPacking.canonicalOwn_eq_true {R : ℝ} (P : PinPacking R) (i : Fin 5) :
    P.canonicalOwn i = true ↔
      centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
        P.center.1 P.center.2 < 0 := by simp [PinPacking.canonicalOwn]

lemma PinPacking.canonicalOwn_eq_false {R : ℝ} (P : PinPacking R) (i : Fin 5) :
    P.canonicalOwn i = false ↔
      0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
        P.center.1 P.center.2 := by simp [PinPacking.canonicalOwn,not_lt]

lemma PinPacking.own_of_canonicalOwn {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) (i : Fin 5) (hi : P.canonicalOwn i = true) :
    0 ≤ centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2 := by
  have hh := (P.canonicalOwn_eq_true i).mp hi
  rcases P.two_choice hD i with h | h
  · linarith
  · exact h

end SquaresInCircles.Six.Normalization
