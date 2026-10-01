import SquaresInCircles.Six.Analytic.SouthOuterTail.Profile

/-!
# The south tail with W on the west side of C

When W is separated from C along the west side of C, the south tail profile is
positive on the whole box `x ∈ [0, 2/5]`, `s ∈ [11/25, 2/3]`, `d ∈ [1/2, 11/14]`,
for both ends of the range of the centre of C. By the reduction to the ends of
the intervals it is enough to check the eight corners. There `cos` and `sin`
are bounded by their Taylor polynomials, and the root term, which decreases in
its argument, by the polynomial majorant at a Taylor lower bound of the
argument; the resulting bounds at the corners are rational.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail

private def cardinalKind (negative : Bool) : Fin 3 := if negative then 2 else 1
private def xEnd (right : Bool) : ℝ := if right then 2/5 else 0
private def sEnd (right : Bool) : ℝ := if right then 2/3 else 11/25
private def dEnd (right : Bool) : ℝ := if right then 11/14 else 1/2
private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def sinLower (x : ℝ) : ℝ :=
  if 0 ≤ x then x-x^3/6+x^5/120-x^7/5040 else x-x^3/6+x^5/120
private def sinUpper (x : ℝ) : ℝ :=
  if 0 ≤ x then x-x^3/6+x^5/120 else x-x^3/6+x^5/120-x^7/5040
private def argumentLower (negative : Bool) (x : ℝ) : ℝ :=
  if negative then -sinUpper x else sinLower x

private lemma cos_lower (x : ℝ) : cosLower x ≤ Real.cos x := by
  by_cases hx : 0 ≤ x
  · exact Seven.cos_lower_six hx
  · have h := Seven.cos_lower_six (x := -x) (by linarith)
    have h2 : (-x)^2 = x^2 := by ring
    have h4 : (-x)^4 = x^4 := by ring
    have h6 : (-x)^6 = x^6 := by ring
    rw [h2,h4,h6,Real.cos_neg] at h
    simpa [cosLower] using h

private lemma sin_bracket (x : ℝ) :
    sinLower x ≤ Real.sin x ∧ Real.sin x ≤ sinUpper x := by
  by_cases hx : 0 ≤ x
  · simp only [sinLower,sinUpper,ite_eq_left hx]
    exact ⟨Seven.sin_lower_seven hx,Seven.sin_upper_five hx⟩
  · have hl := Seven.sin_lower_seven (x := -x) (by linarith)
    have hu := Seven.sin_upper_five (x := -x) (by linarith)
    simp only [Real.sin_neg] at hl hu
    simp only [sinLower,sinUpper,ite_eq_right hx]
    constructor <;> nlinarith only [hl,hu]

private lemma root_at_endpoint (negative right : Bool) :
    westRoot (cardinalKind negative) (xEnd right) ≤
      rootPolynomial (argumentLower negative (xEnd right)) := by
  have hx : 0 ≤ xEnd right ∧ xEnd right ≤ 2/5 := by
    cases right <;> norm_num [xEnd]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_d2])
  have hs1 := (Real.sin_le hx.1).trans hx.2
  have ht := sin_bracket (xEnd right)
  have hl : argumentLower negative (xEnd right) ∈ Set.Icc (-(2/5)) (2/5) := by
    cases negative <;> cases right <;>
      norm_num [argumentLower,xEnd,sinLower,sinUpper]
  have hr : side (cardinalKind negative)*Real.sin (xEnd right) ∈
      Set.Icc (-(2/5)) (2/5) := by
    cases negative <;> simp [cardinalKind,side] <;>
      constructor <;> linarith
  have horder : argumentLower negative (xEnd right) ≤
      side (cardinalKind negative)*Real.sin (xEnd right) := by
    cases negative <;> simp [argumentLower,cardinalKind,side] <;>
      linarith [ht.1,ht.2]
  have h := root_antitone hl hr horder
  cases negative <;> simpa [westRoot,cardinalKind] using h

private def polynomialLower (negative upper : Bool) (x s d : ℝ) : ℝ :=
  constantTerm (cardinalKind negative) upper+
    cosineCoefficient (cardinalKind negative) upper*cosLower x+
    sineCoefficient (cardinalKind negative)*sinLower x-
    CandidateWestTail.radiusBound*rootPolynomial (argumentLower negative x)+
    A*cosLower s+(1/2+face upper)*sinLower s+
    mu*(cosLower (d+side (cardinalKind negative)*x)+
      sinLower (d+side (cardinalKind negative)*x))+
    nu*cosLower (d-s)-kappa*sinUpper (side (cardinalKind negative)*x+s)

private lemma polynomial_le (negative upper right : Bool) (s d : ℝ) :
    polynomialLower negative upper (xEnd right) s d ≤
      profile (cardinalKind negative) upper (xEnd right) s d := by
  have hr := root_at_endpoint negative right
  have cx := cos_lower (xEnd right)
  have sx := (sin_bracket (xEnd right)).1
  have cs := cos_lower s
  have ss := (sin_bracket s).1
  have cq := cos_lower (d+side (cardinalKind negative)*xEnd right)
  have sq := (sin_bracket (d+side (cardinalKind negative)*xEnd right)).1
  have cr := cos_lower (d-s)
  have sz := (sin_bracket (side (cardinalKind negative)*xEnd right+s)).2
  cases negative <;> cases upper <;>
    simp [polynomialLower,profile,cardinalKind,cosineCoefficient,sineCoefficient,
      side,face,beta,mu,nu,A,kappa,CandidateWestTail.radiusBound] at * <;>
    nlinarith only [hr,cx,sx,cs,ss,cq,sq,cr,sz]

private lemma polynomial_positive (negative upper xb sb db : Bool) :
    0 < polynomialLower negative upper (xEnd xb) (sEnd sb) (dEnd db) := by
  cases negative <;> cases upper <;> cases xb <;> cases sb <;> cases db <;>
    norm_num [polynomialLower,cardinalKind,xEnd,sEnd,dEnd,constantTerm,
      cosineCoefficient,sineCoefficient,side,face,beta,mu,nu,A,B,kappa,
      CandidateWestTail.radiusBound,southRootUpper,argumentLower,
      rootPolynomial,rootOffset,rootBase,rootRate,cosLower,sinLower,sinUpper]

private lemma endpoint_positive (negative upper xb sb db : Bool) :
    0 < profile (cardinalKind negative) upper (xEnd xb) (sEnd sb) (dEnd db) :=
  (polynomial_positive negative upper xb sb db).trans_le
    (polynomial_le negative upper xb (sEnd sb) (dEnd db))

/-- With W on the west side of C, the south tail profile is positive on the
whole box. -/
theorem positive_cardinal (negative upper : Bool) {x s d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 2/5) (hs : 11/25 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 < profile (if negative then 2 else 1) upper x s d := by
  have hx' : 0 ≤ x ∧ x ≤ xMax (cardinalKind negative) := by
    cases negative <;> simpa [cardinalKind,xMax] using hx
  have hxe (xb : Bool) : 0 ≤ xEnd xb ∧ xEnd xb ≤ xMax (cardinalKind negative) := by
    cases negative <;> cases xb <;> norm_num [cardinalKind,xMax,xEnd]
  have hse (sb : Bool) : 11/25 ≤ sEnd sb ∧ sEnd sb ≤ 2/3 := by
    cases sb <;> norm_num [sEnd]
  have atSouth (xb sb : Bool) :
      0 < profile (cardinalKind negative) upper (xEnd xb) (sEnd sb) d := by
    exact extend_diagonal _ _ (hxe xb) (hse sb) hd
      (endpoint_positive negative upper xb sb false)
      (endpoint_positive negative upper xb sb true)
  have atWest (xb : Bool) :
      0 < profile (cardinalKind negative) upper (xEnd xb) s d := by
    exact extend_south _ _ (hxe xb) hs hd (atSouth xb false) (atSouth xb true)
  apply extend_west (cardinalKind negative) upper hx' hs hd
  · exact atWest false
  · cases negative <;> simpa [cardinalKind,xEnd,xMax] using atWest true

end SquaresInCircles.Six.Analytic.SouthOuterTail
