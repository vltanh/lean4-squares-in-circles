module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSamePositiveGeometry

/-!
# The complete positive halves of the three same-sign primary owners

Uncompiled transcription of Section 4 of
`HAND_SHORT_WORD_SAME_SIGN_PRIMARY_COMPLETE_WITHOUT_TABLES.md`.
The two cases are the signs of the actual initial angle derivative.
After an active contact reaches the source diagonal, its original
target slack decreases to contact or to the axial endpoint. The axial
continuation increases with slope one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Positive
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)

theorem active_lower (r : Row) {B x : ℝ} (hd : Domain B x) :
    (44901/50000:ℝ)<cost r B x := by
  have hdom : ∀y∈Icc 0 x,Domain B y := fun y hy => physical_before hd hy
  have ht := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (19/100:ℝ)) (fun y hy => cost_hasDerivAt r (hdom y hy))
    (fun y hy => first_hasDerivAt r (hdom y hy))
    (fun y hy => (curvature r (hdom y hy)).le)
    (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hd.2.1.1⟩)
    (show x∈Icc 0 x from ⟨hd.2.1.1,le_rfl⟩)
  rw [initial_cost,initial_first] at ht
  have hB := (active_ranges hd).1
  by_cases he : 0≤initialAngle r B
  · have hp := mul_nonneg he hd.2.1.1
    have hvalue := aligned_lower r hB
    nlinarith [sq_nonneg x]
  · have hnegative := lt_of_not_ge he
    have hsmall := initialAngle_negative_location r hB hnegative
    have hvalue := aligned_initial_lower r ⟨hB.1,hsmall.le⟩
    have hderiv := initialAngle_lower r hB
    have hprod := mul_nonneg (show 0≤initialAngle r B+1/50 by linarith)
      (show 0≤1/50-initialAngle r B by linarith)
    have hsquare := sq_nonneg ((19/100)*x+initialAngle r B)
    nlinarith

lemma physical_state_cost (r : Row) {a b A B : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) :
    source r a+target r B=p r*a-q r*b-P r*A+t r*B := by
  rw [source,target,(SameContact.actual_arc hs).2,(SameContact.actual_arc ht).1]
  ring

/-- The complete original weak primary inequality, on the whole positive
angle half. The final target motion includes both of its closed endpoints. -/
theorem original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x+B*Real.cos x) :
    (44901/50000:ℝ)<Real.pi/2+x+c r+p r*a-q r*b-P r*A+t r*B := by
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have ha : a∈Icc outerDiagonal outerAxial := ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have hd : outerDiagonal∈Icc outerDiagonal outerAxial := ⟨le_rfl,SameContact.diagonal_le_axial⟩
  have hzero : (0:ℝ)∈Icc 0 outerDiagonal := ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩
  have hcontact : contact B x≤a := by
    dsimp [contact]
    rw [(SameContact.actual_arc ht).1]
    linarith
  have hcost : Real.pi/2+x+c r+source r a+target r B=
      Real.pi/2+x+c r+p r*a-q r*b-P r*A+t r*B := by
    have hh := physical_state_cost r hs ht
    linarith
  rw [←hcost]
  by_cases hactive : outerDiagonal≤contact B x
  · have hdom : Domain B x := ⟨hB,hx,hactive⟩
    have hmono := source_monotone r (primary_mem hdom) ha hcontact
    have hh := active_lower r hdom
    dsimp [cost] at hh
    linarith
  · have hsource := source_monotone r hd ha ha.1
    by_cases haxial : outerDiagonal≤contact 0 x
    · have hc : Continuous (fun D : ℝ => -contact D x) := by dsimp [contact,arc]; fun_prop
      obtain ⟨D,hD,hDe⟩ := intermediate_value_Icc hB.1 hc.continuousOn
        (show -outerDiagonal∈Icc (-contact 0 x) (-contact B x) from
          ⟨by linarith,by linarith⟩)
      have he : contact D x=outerDiagonal := by linarith
      have hDouter : D∈Icc 0 outerDiagonal := ⟨hD.1,hD.2.trans hB.2⟩
      have htarget := target_monotone r hDouter hB hD.2
      have hh := active_lower r (show Domain D x from ⟨hDouter,hx,he.ge⟩)
      dsimp [cost] at hh
      rw [he] at hh
      linarith
    · obtain ⟨e,he,heq⟩ := exists_axial_event
      have heDom : e∈Icc 0 (7/10) := ⟨by linarith [he.1],by linarith [he.2]⟩
      have hex : e≤x := by
        by_contra! hbad
        have hh := axial_strictAnti hx heDom hbad
        rw [heq] at hh
        linarith
      have htarget := target_monotone r hzero hB hB.1
      have hh := active_lower r (show Domain 0 e from ⟨hzero,heDom,heq.ge⟩)
      dsimp [cost] at hh
      rw [heq] at hh
      linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Positive
