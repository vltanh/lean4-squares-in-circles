module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeSmallData

/-!
# Completion of both small-slope negative-core side families

Uncompiled transcription of equations (16)--(17). Before the intrinsic
event, the original source diagonal decreases to the target side join.
After it, the active contact descends directly to that join. The shared
endpoint theorem closes both alternatives, including weak contacts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.SmallSide
open CommonQuarter CorePairGeometry Arithmetic

theorem diagonalB_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt diagonalB ((c0-(outerDiagonal-1/2)*Real.sin x)/(Real.cos x)^2) x := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  have h := (((hasDerivAt_const x (outerDiagonal-1/2)).div (Real.hasDerivAt_cos x) hc).const_sub
    (1/2)).fun_add ((CorePrimaryNegative.tangent_hasDerivAt hx).const_mul c0)
  exact h.congr_deriv (by ring)
theorem diagonalCost_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (diagonalCost r) (diagonalFirst r x) x := by
  have h := (((((hasDerivAt_id' x).const_mul (direction false)).const_add (Real.pi/2)).add_const
    (ocC r)).add_const ((ocP r-ocQ r)*outerDiagonal)).fun_add
      ((diagonalB_hasDerivAt hx).const_mul (ocG r))
  exact h.congr_deriv (by simp only [diagonalFirst,direction,Bool.false_eq_true,↓reduceIte]; ring)

theorem diagonalFirst_negative (r : Row) (hr : Rows r) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) : diagonalFirst r x<0 := by
  have hx0 : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans (event_domain he).2⟩
  have ht := positive_trig hx0
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hs := sin_mono hx0 (event_domain he) hx.2
  rw [he.2] at hs
  have hsbound : Real.sin x≤37/100 := hs.trans eventSine_bounds.2.le
  have hs2 := pow_le_pow_left₀ ht.2.2.1 hsbound 2
  have hg := (coefficients r (rows_remaining r hr)).2.1
  have hgU := (coefficient_reserves r hr).2.1
  have hterm := mul_nonneg (mul_nonneg hg.le
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1])) ht.2.2.1
  have hid : diagonalFirst r x*(Real.cos x)^2=
      (Real.sin x)^2-ocG r*(outerDiagonal-1/2)*Real.sin x+ocG r*c0-1 := by
    dsimp [diagonalFirst]
    field_simp [hc.ne']
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hn : diagonalFirst r x*(Real.cos x)^2<0 := by
    dsimp [c0] at hid
    nlinarith
  by_contra h
  have hp := mul_nonneg (le_of_not_gt h) (sq_nonneg (Real.cos x))
  linarith
theorem diagonal_descent (r : Row) (hr : Rows r) {e : ℝ} (he : IsEvent e) :
    AntitoneOn (diagonalCost r) (Icc 0 e) := by
  have hsub : Icc 0 e⊆Icc 0 (7/10) := fun x hx => ⟨hx.1,hx.2.trans (event_domain he).2⟩
  exact antiOn_of_hasDeriv_nonpos
    (fun x hx => (diagonalCost_hasDerivAt r (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx => diagonalCost_hasDerivAt r (hsub (Ioo_subset_Icc_self hx)))
    (fun x hx => (diagonalFirst_negative r hr he (Ioo_subset_Icc_self hx)).le)

theorem join_cost (r : Row) (x : ℝ) :
    cost r x (1/2)=Endpoint.H r false (angle false x) := by
  dsimp [cost,Endpoint.H,Endpoint.height,Endpoint.AA,Endpoint.BB,Endpoint.bC]
  rw [angle_cos]
  dsimp [direction,height,c0]
  ring
theorem diagonal_event_cost (r : Row) {e : ℝ} (he : IsEvent e) :
    diagonalCost r e=Endpoint.H r false (angle false e) := by
  have hheight : height e (1/2)=outerDiagonal := by
    dsimp [height]
    nlinarith [event_identity he]
  rw [←join_cost,diagonalCost,cost,diagonal_at_event he,hheight,source_diagonal]

theorem diagonal_lower (r : Row) (hr : Rows r) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (89809/100000:ℝ)<diagonalCost r x := by
  have hm := diagonal_descent r hr he hx ⟨he.1.1,le_rfl⟩ hx.2
  have hjoin := Endpoint.lower r (rows_remaining r hr) false (event_early he)
  rw [←diagonal_event_cost r he] at hjoin
  linarith

theorem original_to_contact (r : Row) (hr : Rows r) {a b B x : ℝ}
    (hs : OuterState a b) (hh : SourceDomain (height x B))
    (hheight : height x B≤a) : cost r x B≤outerCoreCost r a b (7/12) B (angle false x) := by
  have hm := M_monotone r (rows_remaining r hr) hh (actual_source_domain hs) hheight
  have hsid := source_identity r hs
  rw [primary_cost r (rows_remaining r hr)]
  dsimp [cost]
  linarith
theorem contact_diagonal_cost (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    cost r x (diagonalB x)=diagonalCost r x := by
  rw [cost,diagonal_contact hx,source_diagonal]
  rfl

theorem original_before (r : Row) (hr : Rows r) {e a b B x : ℝ}
    (he : IsEvent e) (hs : OuterState a b) (hx : x∈Icc 0 e)
    (hm : sourcePrimary r a b (7/12) B (angle false x)) :
    (89809/100000:ℝ)<outerCoreCost r a b (7/12) B (angle false x) := by
  have hx0 : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans (event_domain he).2⟩
  have hheight := original_height r hr hx0 hm
  have hdiag := diagonal_lower r hr he hx
  have houter := outer_bounds hs
  by_cases hBD : B≤diagonalB x
  · have hheightlo : outerDiagonal≤height x B := by
      rw [←diagonal_contact hx0]
      exact height_antitone hx0 hBD
    have hh : SourceDomain (height x B) :=
      ⟨by linarith [hheightlo,outer_endpoint_bounds.2.2.1],hheight.trans houter.2.1⟩
    have hdescent := active_descent r hr hx0 hBD (by rw [diagonal_contact hx0]) hh.2
    rw [contact_diagonal_cost r hx0] at hdescent
    exact hdiag.trans_le (hdescent.trans (original_to_contact r hr hs hh hheight))
  · have hd : SourceDomain outerDiagonal :=
      ⟨by linarith [outer_endpoint_bounds.2.2.1],
        by linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]⟩
    have hM := M_monotone r (rows_remaining r hr) hd (actual_source_domain hs) houter.1
    rw [source_diagonal,source_identity r hs] at hM
    have hg := mul_le_mul_of_nonneg_left (le_of_not_ge hBD)
      (coefficients r (rows_remaining r hr)).2.1.le
    rw [primary_cost r (rows_remaining r hr)]
    dsimp [diagonalCost] at hdiag
    linarith

theorem original_after (r : Row) (hr : Rows r) {e a b B x : ℝ}
    (he : IsEvent e) (hs : OuterState a b) (hB : B≤1/2) (hx : x∈Icc e (7/10))
    (hm : sourcePrimary r a b (7/12) B (angle false x)) :
    (89809/100000:ℝ)<outerCoreCost r a b (7/12) B (angle false x) := by
  have hx0 : x∈Icc 0 (7/10) := ⟨(event_domain he).1.trans hx.1,hx.2⟩
  have hheight := original_height r hr hx0 hm
  have hjoin := join_after_event he hx
  have hfirst := hjoin.trans (height_antitone hx0 hB)
  have hh : SourceDomain (height x B) :=
    ⟨by linarith [hfirst,outer_endpoint_bounds.2.2.1],hheight.trans (outer_bounds hs).2.1⟩
  have hdescent := active_descent r hr hx0 hB hjoin hh.2
  have hφ : angle false x∈earlyAngles := by
    have hφe := event_early he
    constructor
    · dsimp [angle,direction,lowerAngle]
      linarith [hx.2]
    · dsimp [angle,direction] at *
      linarith [hφe.2,hx.1]
  have hbound := Endpoint.lower r (rows_remaining r hr) false hφ
  rw [←join_cost] at hbound
  exact hbound.trans_le (hdescent.trans (original_to_contact r hr hs hh hheight))

theorem original (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (hA : A=7/12) (hB : B∈Icc 0 (1/2)) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle false x) := by
  subst A
  obtain ⟨e,he⟩ := event_exists
  rcases le_total x e with hxe|hex
  · have hh := original_before r hr he hs ⟨hx.1,hxe⟩ hm
    linarith
  · have hh := original_after r hr he hs hB.2 ⟨hex,hx.2⟩ hm
    linarith

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.SmallSide
