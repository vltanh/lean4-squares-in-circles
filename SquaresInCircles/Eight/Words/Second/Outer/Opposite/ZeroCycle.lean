module

public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroLReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAsymmetric
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroNegativePJ
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPositiveSpeeds
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Wrong.ZeroOriginalOwners

/-!
# Eight squares: all original outer zero-quarter edges of the second wrong word

The symmetric edge-four argument (`symmetric_source`, `symmetric_target`) joins the two
asymmetric edges. The separate G1 zero-owner theorem keeps every original weak axis, including
ties. The same-sign and opposite-sign families then give one outer-zero statement for the cyclic
assembly (`actual`).
-/

section
/-!
## Both original asymmetric opposite zero edges

The original G1 owner theorem retains every
weak owner and reduces it to the appropriate secondary order.  Both
literal role labels, signs, and the original cycle telescope are
restored; reflected reversal covers the target-secondary order.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Asymmetric
open CommonQuarter Arithmetic QuarterWordGeometry

lemma literal_zero (a b A B x : ℝ) :
    SecondWord.cost 0 .outer .outer true false a b A B x=x+PLabel.eval a b+JLabel.eval A B := by
  norm_num [SecondWord.cost,label,wrongValue,WordProblems.secondCoefficients,
    WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,next,RoleLabel.eval,PLabel,JLabel]
  ring
lemma literal_one (a b A B x : ℝ) :
    SecondWord.cost 1 .outer .outer true false a b A B x=x+JLabel.eval a b+PLabel.eval A B := by
  norm_num [SecondWord.cost,label,wrongValue,WordProblems.secondCoefficients,
    WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,next,RoleLabel.eval,PLabel,JLabel]
  ring

theorem original_source {i : Vertex} (hi : i=0 ∨ i=1)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    threshold i<SecondWord.cost i .outer .outer true false a b A B x := by
  rw [threshold_value]
  rcases hi with rfl | rfl
  · rw [literal_zero]
    have hh := original false hs ht hx hm
    dsimp [F,G] at hh
    linarith
  · rw [literal_one]
    have hh := original true hs ht hx hm
    dsimp [F,G] at hh
    linarith

theorem original_target {i : Vertex} (hi : i=0 ∨ i=1)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 (-1) x) :
    threshold i<SecondWord.cost i .outer .outer true false a b A B x := by
  have hrev : 0≤Eight.forwardMargin 0 A B a b 1 (-1) x := by
    simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm
  have hir : reverseEdge i=0 ∨ reverseEdge i=1 := by
    rcases hi with rfl | rfl <;> norm_num [reverseEdge]
  have hh := original_source hir ht hs hx hrev
  have he := cost_reflection i .outer .outer true false a b A B x
  norm_num at he
  rw [he,threshold_value] at hh
  simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F₀ : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F₀.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : i=0 ∨ i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i≠positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F₀ hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hz : F₀.word hgap pi_lt_22_over_7 i=0 := by
    rw [hw]; rcases hi with rfl | rfl <;> norm_num [WordProblems.wrongWord]
  have hx : |phaseValue F₀ hgap i|≤7/10 := by simpa [phaseValue,hz] using (difference_small F₀ i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hm := original_margin C F₀ hgap i j howner
  have hh : threshold i<SecondWord.cost i .outer .outer
      (positiveOf C i) (positiveOf C (next i)) (C.a i) (C.b i)
      (C.a (next i)) (C.b (next i)) (phaseValue F₀ hgap i) := by
    rcases WrongZeroOriginalOwners.original C F₀ hgap i hz j howner with
      ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
    · have htargetneg : positiveOf C (next i)=false := by
        cases h : positiveOf C (next i) <;> simp_all
      rw [hpos,htargetneg]
      exact original_source hi hsource htarget hx (by simpa [hpos,htargetneg,WordProblems.sign] using hm)
    · have hsourcepos : positiveOf C i=true := by cases h : positiveOf C i <;> simp_all
      rw [hsourcepos,hneg]
      exact original_target hi hsource htarget hx (by simpa [hsourcepos,hneg,WordProblems.sign] using hm)
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual (C : BoundaryCycle Q0) (F₀ : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F₀.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : i=0 ∨ i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i≠positiveOf C (next i)) :
    threshold i<phaseValue F₀ hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F₀ hgap hw i hi hs ht hsg j (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.SecondWord.OppositeZero.Asymmetric
end
end
end

section
/-!
## Label shapes and the small-angle support in the symmetric zero edge

The whole-arc third derivative, its tangent at one half, the two
restricted chords, and the single support tangent are kept separate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratioD ratioDD)

open StationaryPrimitives (Interval)

private lemma r82_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r82_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r82_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl
private lemma r82_mp_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).hi = S.hi := by subst e; rfl

private lemma r82_rootAt_lo {b : ℝ} (hb : b∈Icc 0 (9/10)) : (Reference.rootAt b hb).lo =
    (OppositeThree.ReferenceAlgebra.rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2)
      (by linarith [hb.2]) (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).lo := by
  unfold Reference.rootAt
  rw [r82_mpr_lo, r82_mp_lo]
  all_goals simp [U,ShortOuterOne.SameContact.arc]
private lemma r82_rootAt_hi {b : ℝ} (hb : b∈Icc 0 (9/10)) : (Reference.rootAt b hb).hi =
    (OppositeThree.ReferenceAlgebra.rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2)
      (by linarith [hb.2]) (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).hi := by
  unfold Reference.rootAt
  rw [r82_mpr_hi, r82_mp_hi]
  all_goals simp [U,ShortOuterOne.SameContact.arc]

private lemma r82_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r82_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (OppositeThree.ReferenceAlgebra.coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r82_mpr_lo r82_coordinate_eq (congrArg _ r82_coordinate_eq) _
private lemma r82_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (OppositeThree.ReferenceAlgebra.coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r82_mpr_hi r82_coordinate_eq (congrArg _ r82_coordinate_eq) _

attribute [local simp ↓] r82_rootAt_lo r82_rootAt_hi r82_coordinate_lo r82_coordinate_hi

lemma half_references : (781/1250:ℝ)<LLabel.d1 (1/2) ∧
    -(311/10000:ℝ)<LLabel.d2 (1/2) ∧ LLabel.d2 (1/2)<0 := by
  have h1 := (Reference.firstAt LLabel (1/2) (by norm_num)).mem.1
  have h2 := (Reference.secondAt LLabel (1/2) (by norm_num)).mem
  have r1 : (781/1250:ℝ)<(Reference.firstAt LLabel (1/2) (by norm_num)).lo := by
    opposite_reference_arithmetic
  have r2 : -(311/10000:ℝ)<(Reference.secondAt LLabel (1/2) (by norm_num)).lo := by
    opposite_reference_arithmetic
  have r3 : (Reference.secondAt LLabel (1/2) (by norm_num)).hi<0 := by
    opposite_reference_arithmetic
  exact ⟨r1.trans_le h1,r2.trans_le h2.1,h2.2.trans_lt r3⟩

lemma third_strong {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (2:ℝ)<LLabel.d3 b := by
  have hu := U_positive (outer_domain hb)
  have hc := UW_circle (outer_domain hb)
  have hU : U b<2 := by
    norm_num [Q0] at hc
    nlinarith [sq_nonneg (W b)]
  have hU3 : (U b)^3<(2:ℝ)^3 := by gcongr
  have hD : (39/80:ℝ)<ratioD b := by
    change (39/80:ℝ)<Q0/(U b)^3
    apply (lt_div_iff₀ (pow_pos hu 3)).2
    norm_num [Q0] at hU3 ⊢
    linarith
  have hDD := ratioDD_positive hb
  have hp := mul_nonneg hb.1 hDD.le
  norm_num [RoleLabel.d3,LLabel]
  nlinarith

lemma first_strong_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (1249/2000:ℝ)<LLabel.d1 b := by
  have hh := curvature_tangent (f := LLabel.d1) (d := LLabel.d2)
    (dd := LLabel.d3) (κ := 2) hb L_half_mem
    (fun t ht => LLabel.d1_hasDerivAt (outer_domain ht))
    (fun t ht => LLabel.d2_hasDerivAt (outer_domain ht))
    (fun t ht => (third_strong ht).le)
  have hhalf := half_references
  have hsq : (LLabel.d2 (1/2))^2<(311/10000:ℝ)^2 := by
    nlinarith [hhalf.2.1,hhalf.2.2]
  nlinarith [sq_nonneg (b-1/2+LLabel.d2 (1/2)/2)]

lemma first_upper_between {l u b M : ℝ} (hl : l∈Icc 0 outerDiagonal)
    (hu : u∈Icc 0 outerDiagonal) (hb : b∈Icc l u)
    (hleft : LLabel.d1 l<M) (hright : LLabel.d1 u<M) : LLabel.d1 b<M := by
  have hdom {t : ℝ} (ht : t∈Icc l u) : t∈Icc 0 outerDiagonal :=
    ⟨hl.1.trans ht.1,ht.2.trans hu.2⟩
  have hc : ConcaveOn ℝ (Icc l u) (fun t => M-LLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (LLabel.d1_hasDerivAt (outer_domain (hdom ht))).const_sub M)
      (fun t ht => (LLabel.d2_hasDerivAt (outer_domain (hdom ht))).neg)
      (fun t ht => neg_nonpos.mpr (L_third_positive (hdom ht)).le)
  have hh := concave_gt_of_endpoints hc hb
    (sub_pos.mpr hleft) (sub_pos.mpr hright)
  linarith

lemma first_middle_upper {b : ℝ} (hb : b∈Icc (1/10:ℝ) (17/20)) :
    LLabel.d1 b<51/50 :=
  first_upper_between (Asymmetric.rational_outer_mem (by norm_num))
    (Asymmetric.rational_outer_mem (by norm_num)) hb L_tenth_first L_85_first

lemma first_inner_upper {b : ℝ} (hb : b∈Icc (1/5:ℝ) (19/25)) :
    LLabel.d1 b<17/20 :=
  first_upper_between (Asymmetric.rational_outer_mem (by norm_num))
    (Asymmetric.rational_outer_mem (by norm_num)) hb L_fifth_first L_76_first

lemma first_outside_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hout : b≤2/5 ∨ 3/5≤b) : (649/1000:ℝ)<LLabel.d1 b := by
  rcases hout with hlo | hhi
  · have hh := L_first_early_antitone
      ⟨hb.1,by linarith⟩ (by norm_num : (2/5:ℝ)∈Icc 0 (1/2)) hlo
    exact L_four_first.trans_le hh
  · have hh := L_first_late_monotone
      ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num :
        (3/5:ℝ)∈Icc 0 (899/1000))).2⟩ ⟨by linarith,hb.2⟩ hhi
    exact L_six_first.trans_le hh

lemma small_chord {B : ℝ} (hB : B∈Icc (0:ℝ) (3/20)) :
    LLabel.outer 0+charge*B≤LLabel.outer B := by
  let f : ℝ→ℝ := fun t => LLabel.outer t-LLabel.outer 0-charge*t
  have hdom {t : ℝ} (ht : t∈Icc (0:ℝ) (3/20)) : t∈Icc 0 outerDiagonal :=
    Asymmetric.rational_outer_mem ⟨ht.1,by linarith [ht.2]⟩
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (3/20)) f :=
    concave_of_deriv2
      (fun t ht => ((LLabel.outer_hasDerivAt (outer_domain (hdom ht))).sub_const
        (LLabel.outer 0)).sub (((hasDerivAt_id' t).const_mul charge).congr_deriv (mul_one _)))
      (fun t ht => (LLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub_const charge)
      (fun t ht => (L_second_early ⟨ht.1,by linarith [ht.2]⟩).le)
  have hh := hc.min_le_of_mem_Icc (by norm_num) (by norm_num) hB
  have hleft : f 0=0 := by simp [f]
  have hright : 0≤f (3/20) := by
    dsimp [f]
    linarith [L_small_chord_reference]
  rw [hleft,min_eq_left hright] at hh
  dsimp [f] at hh
  linarith

lemma support_early {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) :
    -(15957/100000:ℝ)<LLabel.outer b-charge*b := by
  have hdom {t : ℝ} (ht : t∈Icc (0:ℝ) (3/5)) : t∈Icc 0 outerDiagonal :=
    Asymmetric.rational_outer_mem ⟨ht.1,by linarith [ht.2]⟩
  have hh := MinimumCalculus.endpoint_minimum
    (f := fun t => LLabel.outer t-charge*t)
    (d := fun t => LLabel.d1 t-charge) (dd := LLabel.d2) (ddd := LLabel.d3) hb
    (fun t ht => (LLabel.outer_hasDerivAt (outer_domain (hdom ht))).sub
      (((hasDerivAt_id' t).const_mul charge).congr_deriv (mul_one _)))
    (fun t ht => (LLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub_const charge)
    (fun t ht => LLabel.d2_hasDerivAt (outer_domain (hdom ht)))
    (fun t ht => (L_third_positive (hdom ht)).le)
    (by dsimp [charge]; linarith [L_six_first_upper])
  have hzero : -(15957/100000:ℝ)<LLabel.outer 0-charge*0 := by
    norm_num [RoleLabel.outer,RoleLabel.eval,LLabel]
  exact (lt_min hzero support_references.1).trans_le hh

lemma support_late {b : ℝ} (hb : b∈Icc (3/5:ℝ) outerDiagonal) :
    -(15957/100000:ℝ)<LLabel.outer b-charge*b := by
  have hdom {t : ℝ} (ht : t∈Icc (3/5:ℝ) outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2⟩
  have hcurv {t : ℝ} (ht : t∈Icc (3/5:ℝ) outerDiagonal) :
      (1/2:ℝ)<LLabel.d2 t :=
    L_six_second.trans_le (L_second_monotone
      (Asymmetric.rational_outer_mem (by norm_num)) (hdom ht) ht.1)
  have hh := curvature_tangent (f := fun t => LLabel.outer t-charge*t)
    (d := fun t => LLabel.d1 t-charge) (dd := LLabel.d2) (κ := (1/2:ℝ)) hb
    (show (17/20:ℝ)∈Icc (3/5:ℝ) outerDiagonal from
      ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩)
    (fun t ht => (LLabel.outer_hasDerivAt (outer_domain (hdom ht))).sub
      (((hasDerivAt_id' t).const_mul charge).congr_deriv (mul_one _)))
    (fun t ht => (LLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub_const charge)
    (fun t ht => (hcurv ht).le)
  have hd := abs_lt.mp support_references.2.2
  have hsq : (LLabel.d1 (17/20)-charge)^2<(1/200:ℝ)^2 := by nlinarith
  nlinarith [support_references.2.1,
    sq_nonneg ((b-17/20)/2+(LLabel.d1 (17/20)-charge))]

lemma support_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    -(15957/100000:ℝ)<LLabel.outer b-charge*b := by
  by_cases he : b≤3/5
  · exact support_early ⟨hb.1,he⟩
  · exact support_late ⟨by linarith,hb.2⟩

end SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
end
end
end

section
/-!
## The symmetric outer zero edge at nonnegative angle

The three written monotonicity regimes reduce to the aligned contact
or to the small positive-angle rectangle. No additional case search
or angle discretization is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma small_rectangle {B x : ℝ} (hd : PlusDomain B x)
    (hB : B≤3/20) (hx : x≤1/4) :
    (903/1000:ℝ)<plusCost LLabel LLabel B x := by
  have tr := positive_trig hd.2.1
  have hA := (outer_bounds (ShortOuterOne.SameContact.arc_state hd.1)).2.1
  have hcoef : arc B-1/2≤(183/200:ℝ) := by
    linarith [outer_endpoint_bounds.2.1]
  have hAprod := mul_le_mul_of_nonneg_right hcoef tr.2.2.1
  have hsin := Real.sin_le hd.2.1.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hBprod := mul_nonneg hd.1.1 (sub_nonneg.mpr tr.2.1)
  have hquad := mul_nonneg hd.2.1.1 (sub_nonneg.mpr hx)
  have hdeficit : 1-B-plus B x≤(391/400)*x := by
    dsimp [plus]
    nlinarith
  have hangle : charge*(1-B-plus B x)≤x := by
    dsimp [charge]
    linarith
  have htarget := small_chord ⟨hd.1.1,hB⟩
  have hsource := support_lower hd.2.2
  have hzero : LLabel.outer 0=(793/20000:ℝ) := L_zero
  rw [hzero] at htarget
  dsimp [plusCost,charge] at *
  linarith

lemma positive_large_target {B x : ℝ} (hd : PlusDomain B x) (hB : 3/10≤B) :
    0<plusFirst LLabel B x := by
  have hv := PositivePJ.speed_bound hd.1 hd.2.1
    (Asymmetric.rational_outer_mem (by norm_num : (3/10:ℝ)∈Icc 0 (899/1000)))
    hB (by norm_num : (0:ℝ)<21/25) Reference.mass_references.2.2.2
  have hp := L_first_upper hd.2.2
  have hh := mul_lt_mul hp hv.le (positive_data hd.1 hd.2.1).1
    (by norm_num : (0:ℝ)≤147/125)
  dsimp [plusFirst]
  norm_num at hh
  linarith

lemma middle_source {B x : ℝ} (hd : PlusDomain B x) (hB : B∈Icc (3/20:ℝ) (3/10)) :
    plus B x∈Icc (1/10:ℝ) (17/20) := by
  have hthree : (3/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have ht := plus_target_antitone hd.2.1 hd.1 hthree hB.2
  have ha := plus_angle_antitone hthree hd.2.1 (by norm_num) hd.2.1.2
  have hz := plus_angle_antitone hd.1 (by norm_num) hd.2.1 hd.2.1.1
  have hp0 : plus B 0=1-B := by norm_num [plus]; ring
  have ht' : plus (3/10) x≤plus B x := ht
  exact ⟨by linarith [Reference.plus_references.2.2.2.1],by linarith [hB.1]⟩

lemma positive_middle_target {B x : ℝ} (hd : PlusDomain B x)
    (hB : B∈Icc (3/20:ℝ) (3/10)) : 0<plusFirst LLabel B x := by
  have hv := PositivePJ.speed_bound hd.1 hd.2.1
    (Asymmetric.rational_outer_mem (by norm_num : (3/20:ℝ)∈Icc 0 (899/1000)))
    hB.1 (by norm_num : (0:ℝ)<47/50) Reference.mass_references.2.2.1
  have hp := first_middle_upper (middle_source hd hB)
  have hh := mul_lt_mul hp hv.le (positive_data hd.1 hd.2.1).1
    (by norm_num : (0:ℝ)≤51/50)
  dsimp [plusFirst]
  norm_num at hh
  linarith

lemma small_late_source {B x : ℝ} (hB : B∈Icc (0:ℝ) (3/20))
    (hx : x∈Icc (1/4:ℝ) (7/10)) : plus B x∈Icc (1/5:ℝ) (19/25) := by
  have hBi : B∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem
    ⟨hB.1,by linarith [hB.2]⟩
  have hxi : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have hsmall : (3/20:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have ht := plus_target_antitone hxi hBi hsmall hB.2
  have ha := plus_angle_antitone hsmall hxi (by norm_num) hx.2
  have ht0 := plus_target_antitone hxi outer_zero_mem hBi hB.1
  have ha0 := plus_angle_antitone outer_zero_mem (by norm_num) hxi hx.1
  exact ⟨by linarith [Reference.plus_references.2.2.2.2.1],
    by linarith [Reference.plus_references.2.2.2.2.2]⟩

lemma positive_small_late {B x : ℝ} (hd : PlusDomain B x)
    (hB : B≤3/20) (hx : 1/4≤x) : 0<plusFirst LLabel B x := by
  have hp := first_inner_upper (small_late_source ⟨hd.1.1,hB⟩ ⟨hx,hd.2.1.2⟩)
  have hv := PositivePJ.speed_upper hd.1 hd.2.1
  have hh := mul_lt_mul hp hv.le (positive_data hd.1 hd.2.1).1
    (by norm_num : (0:ℝ)≤17/20)
  dsimp [plusFirst]
  norm_num at hh
  linarith

lemma positive_after_small {B x : ℝ} (hd : PlusDomain B x) (hB : 3/20≤B) :
    0<plusFirst LLabel B x := by
  by_cases hlarge : 3/10≤B
  · exact positive_large_target hd hlarge
  · exact positive_middle_target hd ⟨hB,le_of_not_ge hlarge⟩

lemma positive_aligned_reduction {B x : ℝ} (hd : PlusDomain B x) (hB : 3/20≤B) :
    (89777/100000:ℝ)<plusCost LLabel LLabel B x := by
  have hdom {t : ℝ} (ht : t∈Icc 0 x) : PlusDomain B t := by
    have hti : t∈Icc 0 (7/10) := ⟨ht.1,ht.2.trans hd.2.1.2⟩
    have hlo := plus_angle_antitone hd.1 hti hd.2.1 ht.2
    have hhi := plus_angle_antitone hd.1 (by norm_num) hti ht.1
    have hp0 : plus B 0=1-B := by norm_num [plus]; ring
    exact ⟨hd.1,hti,⟨hd.2.2.1.trans hlo,by
      linarith [hB,fine_outer_endpoint_bounds.2]⟩⟩
  have hm : MonotoneOn (plusCost LLabel LLabel B) (Icc 0 x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (plusCost_hasDerivAt LLabel LLabel (hdom ht)).continuousAt.continuousWithinAt)
      (fun t ht => plusCost_hasDerivAt LLabel LLabel (hdom (Ioo_subset_Icc_self ht)))
      (fun t ht => (positive_after_small (hdom (Ioo_subset_Icc_self ht)) hB).le)
  have hz := (hdom ⟨le_rfl,hd.2.1.1⟩).2.2
  have hh := hm ⟨le_rfl,hd.2.1.1⟩ ⟨hd.2.1.1,le_rfl⟩ hd.2.1.1
  have hp0 : plus B 0=1/2+(1/2-B) := by norm_num [plus]
  rw [hp0] at hz
  have hl := AlignedL.original hz hd.1 (by ring)
  simp only [plusCost,hp0] at hh
  simp only [plusCost]
  linarith

lemma positive_small_reduction {B x : ℝ} (hd : PlusDomain B x) (hB : B≤3/20) :
    (17953/20000:ℝ)<plusCost LLabel LLabel B x := by
  by_cases hearly : x≤1/4
  · linarith [small_rectangle hd hB hearly]
  · have hstart : (1/4:ℝ)≤x := le_of_not_ge hearly
    have hdom {t : ℝ} (ht : t∈Icc (1/4:ℝ) x) : PlusDomain B t := by
      have hb := small_late_source ⟨hd.1.1,hB⟩ ⟨ht.1,ht.2.trans hd.2.1.2⟩
      exact ⟨hd.1,⟨by linarith [ht.1],ht.2.trans hd.2.1.2⟩,
        ⟨by linarith [hb.1],by linarith [hb.2,fine_outer_endpoint_bounds.2]⟩⟩
    have hm : MonotoneOn (plusCost LLabel LLabel B) (Icc (1/4:ℝ) x) :=
      monoOn_of_hasDeriv_nonneg
        (fun t ht => (plusCost_hasDerivAt LLabel LLabel (hdom ht)).continuousAt.continuousWithinAt)
        (fun t ht => plusCost_hasDerivAt LLabel LLabel (hdom (Ioo_subset_Icc_self ht)))
        (fun t ht => (positive_small_late (hdom (Ioo_subset_Icc_self ht)) hB ht.1.le).le)
    have hh := hm ⟨le_rfl,hstart⟩ ⟨hstart,le_rfl⟩ hstart
    have hl := small_rectangle (hdom ⟨le_rfl,hstart⟩) hB (le_refl _)
    linarith

/-- The entire nonnegative-angle symmetric physical contact. -/
theorem plus_lower {B x : ℝ} (hd : PlusDomain B x) :
    (17953/20000:ℝ)<plusCost LLabel LLabel B x := by
  by_cases hB : 3/20≤B
  · linarith [positive_aligned_reduction hd hB]
  · exact positive_small_reduction hd (le_of_not_ge hB)

end SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
end
end
end

section
/-!
## Where the negative-angle symmetric cost can fail to increase

The exact circle speed `speedAt` is kept. A nonpositive angular derivative forces `B > .67`,
`b < .66`, and `b < .56` when `B ≤ .7` (`nonpositive_angular_location`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic

lemma product_gt_one {p v l q : ℝ} (hp : 0<p) (hv : 0<v)
    (hl : 0≤l) (hq : 0<q) (hpl : l<p) (hqv : q≤v^2)
    (hreserve : 1<l^2*q) : 1<p*v := by
  have hp2 : l^2<p^2 := by nlinarith
  have hmul := mul_lt_mul hp2 hqv hq (sq_nonneg p)
  have hprod := mul_pos hp hv
  nlinarith

lemma target_location {B x : ℝ} (hd : MinusDomain B x)
    (hfirst : minusFirst LLabel B x≤0) : (67/100:ℝ)<B := by
  have hv := (positive_data hd.1 hd.2.1).2.1
  have hp : 0<LLabel.d1 (minus B x) := by linarith [first_strong_lower hd.2.2]
  have hn := minus_norm hd.1 x
  have hz := minus_z_bound hd
  have hproduct : LLabel.d1 (minus B x)*minusSpeed B x≤1 := by
    dsimp [minusFirst] at hfirst
    linarith
  by_contra! hB
  by_cases hmiddle : minus B x∈Icc (2/5:ℝ) (3/5)
  · have hz2 : (minus B x-1/2)^2≤(1/100:ℝ) := by
      nlinarith [hmiddle.1,hmiddle.2]
    have hrad : Q0-67/50-1/100≤(minusSpeed B x)^2 := by nlinarith
    have hh := product_gt_one hp hv (by norm_num : (0:ℝ)≤1249/2000)
      (by norm_num [Q0] : 0<Q0-67/50-1/100) (first_strong_lower hd.2.2)
      hrad (by norm_num [Q0])
    linarith
  · have hout : minus B x≤2/5 ∨ 3/5≤ minus B x := by
      by_contra! h
      exact hmiddle ⟨h.1.le,h.2.le⟩
    have hlabel := first_outside_lower hd.2.2 hout
    have hz2 : (minus B x-1/2)^2<(4/25:ℝ) := by nlinarith [hz.1,hz.2]
    have hrad : Q0-67/50-4/25≤(minusSpeed B x)^2 := by nlinarith
    have hh := product_gt_one hp hv (by norm_num : (0:ℝ)≤649/1000)
      (by norm_num [Q0] : 0<Q0-67/50-4/25) hlabel hrad (by norm_num [Q0])
    linarith

def speedAt (B b : ℝ) : ℝ := Real.sqrt (Q0-2*B-(b-1/2)^2)
def workAt (B b : ℝ) : ℝ := LLabel.d1 b*speedAt B b
def workAtD (B b : ℝ) : ℝ :=
  (LLabel.d2 b*(speedAt B b)^2-LLabel.d1 b*(b-1/2))/speedAt B b

lemma speedAt_data {B b : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hb : b∈Icc (1/2:ℝ) outerDiagonal) :
    0<speedAt B b ∧ (speedAt B b)^2=Q0-2*B-(b-1/2)^2 ∧
      Q0-9/5-4/25<(speedAt B b)^2 := by
  have hz : (b-1/2)^2<(4/25:ℝ) := by
    nlinarith [hb.1,hb.2,outer_endpoint_bounds.2.2.2]
  have hr : Q0-9/5-4/25<Q0-2*B-(b-1/2)^2 := by
    linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hr0 : 0<Q0-2*B-(b-1/2)^2 := by
    have h0 : (0:ℝ)<Q0-9/5-4/25 := by norm_num [Q0]
    linarith
  exact ⟨Real.sqrt_pos.mpr hr0,Real.sq_sqrt hr0.le,by
    dsimp [speedAt]
    rw [Real.sq_sqrt hr0.le]
    exact hr⟩

lemma speedAt_hasDerivAt {B b : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hb : b∈Icc (1/2:ℝ) outerDiagonal) :
    HasDerivAt (speedAt B) (-(b-1/2)/speedAt B b) b := by
  have hs := speedAt_data hB hb
  have hr : Q0-2*B-(b-1/2)^2≠0 := by nlinarith [sq_pos_of_pos hs.1,hs.2.1]
  have hin : HasDerivAt (fun y : ℝ => Q0-2*B-(y-1/2)^2) (-(2*(b-1/2))) b := by
    convert (((hasDerivAt_id' b).sub_const (1/2)).fun_pow 2).const_sub (Q0-2*B) using 1
    norm_num
  have h := hin.sqrt hr
  change HasDerivAt (fun y : ℝ => Real.sqrt (Q0-2*B-(y-1/2)^2)) _ b
  convert h using 1
  have hsp : speedAt B b=Real.sqrt (Q0-2*B-(b-1/2)^2) := rfl
  rw [← hsp]
  field_simp [hs.1.ne']

lemma workAt_hasDerivAt {B b : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hb : b∈Icc (1/2:ℝ) outerDiagonal) : HasDerivAt (workAt B) (workAtD B b) b := by
  have hs := (speedAt_data hB hb).1
  have h := (LLabel.d1_hasDerivAt (outer_domain ⟨by linarith [hb.1],hb.2⟩)).mul
    (speedAt_hasDerivAt hB hb)
  change HasDerivAt (fun y => LLabel.d1 y*speedAt B y) _ b
  convert h using 1
  dsimp only [workAtD]
  field_simp [hs.ne']
  ring

lemma workAt_actual {B x : ℝ} (hd : MinusDomain B x) (hb : 1/2≤ minus B x) :
    workAt B (minus B x)=LLabel.d1 (minus B x)*minusSpeed B x := by
  have hs := speedAt_data hd.1 ⟨hb,hd.2.2.2⟩
  have hv := (positive_data hd.1 hd.2.1).2.1
  have hn := minus_norm hd.1 x
  have he : speedAt B (minus B x)=minusSpeed B x := by nlinarith [hs.1,hs.2.1]
  rw [workAt,he]

lemma workAt_monotone {B a k M : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (ha : a∈Icc (1/2:ℝ) outerDiagonal) (hcap : B≤M)
    (hk : 0<k) (hka : k≤LLabel.d2 a)
    (hreserve : 0<k*(Q0-2*M-4/25)-(147/125)*(2/5)) :
    MonotoneOn (workAt B) (Icc a outerDiagonal) := by
  have hdom {b : ℝ} (hb : b∈Icc a outerDiagonal) : b∈Icc (1/2:ℝ) outerDiagonal :=
    ⟨ha.1.trans hb.1,hb.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun b hb => (workAt_hasDerivAt hB (hdom hb)).continuousAt.continuousWithinAt)
    (fun b hb => workAt_hasDerivAt hB (hdom (Ioo_subset_Icc_self hb)))
  intro b hb
  have hbi : b∈Icc 0 outerDiagonal := ⟨by linarith [ha.1,hb.1],hb.2.le⟩
  have hs := speedAt_data hB (hdom (Ioo_subset_Icc_self hb))
  have hD := hka.trans (L_second_monotone ⟨by linarith [ha.1],ha.2⟩ hbi hb.1.le)
  have hz : b-1/2∈Icc (0:ℝ) (2/5) :=
    ⟨by linarith [ha.1,hb.1],by linarith [hb.2,outer_endpoint_bounds.2.2.2]⟩
  have hz2 : (b-1/2)^2≤(4/25:ℝ) := by nlinarith [hz.1,hz.2]
  have hrad : Q0-2*M-4/25≤(speedAt B b)^2 := by nlinarith [hs.2.1]
  have h1 := mul_le_mul_of_nonneg_right hD (sq_nonneg (speedAt B b))
  have h2 := mul_le_mul_of_nonneg_left hrad hk.le
  have h3 := mul_le_mul (L_first_upper hbi).le hz.2 hz.1
    (by norm_num : (0:ℝ)≤147/125)
  dsimp [workAtD]
  exact div_nonneg (by nlinarith) hs.1.le

lemma work_56 {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (hcap : B≤7/10) :
    1<workAt B (14/25) := by
  have ha : (14/25:ℝ)∈Icc (1/2:ℝ) outerDiagonal :=
    ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hs := speedAt_data hB ha
  have hr : Q0-7/5-(3/50)^2≤(speedAt B (14/25))^2 := by
    nlinarith [hs.2.1]
  exact product_gt_one (by linarith [L_56_first]) hs.1
    (by norm_num : (0:ℝ)≤15817/25000)
    (by norm_num [Q0] : 0<Q0-7/5-(3/50)^2) L_56_first hr (by norm_num [Q0])

lemma work_66 {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 1<workAt B (33/50) := by
  have ha : (33/50:ℝ)∈Icc (1/2:ℝ) outerDiagonal :=
    ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hs := speedAt_data hB ha
  have hr : Q0-9/5-(4/25)^2≤(speedAt B (33/50))^2 := by
    nlinarith [hs.2.1,hB.2,outer_endpoint_bounds.2.2.2]
  exact product_gt_one (by linarith [L_66_first]) hs.1
    (by norm_num : (0:ℝ)≤6933/10000)
    (by norm_num [Q0] : 0<Q0-9/5-(4/25)^2) L_66_first hr (by norm_num [Q0])

lemma source_below_56 {B x : ℝ} (hd : MinusDomain B x)
    (hfirst : minusFirst LLabel B x≤0) (hcap : B≤7/10) : minus B x<(14/25:ℝ) := by
  by_contra! hb
  have ha : (14/25:ℝ)∈Icc (1/2:ℝ) outerDiagonal :=
    ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hm := workAt_monotone hd.1 ha hcap (by norm_num : (0:ℝ)<29/100)
    L_56_second.le (by norm_num [Q0])
  have hh := hm ⟨le_rfl,ha.2⟩ ⟨hb,hd.2.2.2⟩ hb
  have hl := work_56 hd.1 hcap
  rw [workAt_actual hd (by linarith)] at hh
  dsimp [minusFirst] at hfirst
  linarith

lemma source_below_66 {B x : ℝ} (hd : MinusDomain B x)
    (hfirst : minusFirst LLabel B x≤0) : minus B x<(33/50:ℝ) := by
  by_contra! hb
  have ha : (33/50:ℝ)∈Icc (1/2:ℝ) outerDiagonal :=
    ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hm := workAt_monotone hd.1 ha
    (show B≤(9/10:ℝ) by linarith [hd.1.2,outer_endpoint_bounds.2.2.2])
    (by norm_num : (0:ℝ)<93/100) L_66_second.le (by norm_num [Q0])
  have hh := hm ⟨le_rfl,ha.2⟩ ⟨hb,hd.2.2.2⟩ hb
  have hl := work_66 hd.1
  rw [workAt_actual hd (by linarith)] at hh
  dsimp [minusFirst] at hfirst
  linarith

theorem nonpositive_angular_location {B x : ℝ} (hd : MinusDomain B x)
    (hfirst : minusFirst LLabel B x≤0) :
    (67/100:ℝ)<B ∧ minus B x<(33/50:ℝ) ∧
      (B≤7/10 → minus B x<(14/25:ℝ)) :=
  ⟨target_location hd hfirst,source_below_66 hd hfirst,source_below_56 hd hfirst⟩

end SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
end
end
end

section
/-!
## The second descent direction for a negative symmetric contact

The ratio K/v is the explicit function J(B,z). Its coordinate derivatives
and the single endpoint estimate (19) give the target descent direction.
The rational radical lower bounds below only verify those named endpoint
comparisons; they do not subdivide a state or angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def qB (B : ℝ) : ℝ := Q0-2*B
def inverseRoot (B z : ℝ) : ℝ := Real.sqrt (qB B-z^2)
def inverseSlope (B z : ℝ) : ℝ :=
  (Q0-B-1/2)/(U B*qB B)+z/(qB B*inverseRoot B z)
def inverseSlopeB (B z : ℝ) : ℝ :=
  (Q0-1)/(U B*(qB B)^2)+
    (Q0-B-1/2)*(B+1/2)/((U B)^3*qB B)+
      z*(2/((qB B)^2*inverseRoot B z)+1/(qB B*(inverseRoot B z)^3))

lemma inverse_data {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(2/5):ℝ) (2/5)) :
    0<U B ∧ 0<qB B ∧ 0< inverseRoot B z ∧
      (inverseRoot B z)^2=qB B-z^2 := by
  have hq : (5289/2500:ℝ)<qB B := by
    norm_num [qB,Q0]
    linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hz2 : z^2≤(4/25:ℝ) := by nlinarith [hz.1,hz.2]
  have hr : 0<qB B-z^2 := by linarith
  exact ⟨U_positive (outer_domain hB),by linarith,Real.sqrt_pos.mpr hr,
    Real.sq_sqrt hr.le⟩

lemma inverseRoot_z_hasDerivAt {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(2/5):ℝ) (2/5)) :
    HasDerivAt (inverseRoot B) (-z/inverseRoot B z) z := by
  have h := inverse_data hB hz
  have hn : qB B-z^2≠0 := by nlinarith [h.2.2.1,h.2.2.2]
  have hin : HasDerivAt (fun y : ℝ => qB B-y^2) (-(2*z)) z := by
    convert ((hasDerivAt_id' z).fun_pow 2).const_sub (qB B) using 1
    norm_num
  change HasDerivAt (fun y : ℝ => Real.sqrt (qB B-y^2)) _ z
  convert hin.sqrt hn using 1
  have hr : inverseRoot B z=Real.sqrt (qB B-z^2) := rfl
  rw [← hr]
  field_simp [h.2.2.1.ne']

lemma inverseRoot_B_hasDerivAt {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(2/5):ℝ) (2/5)) :
    HasDerivAt (fun t => inverseRoot t z) (-1/inverseRoot B z) B := by
  have h := inverse_data hB hz
  have hn : qB B-z^2≠0 := by nlinarith [h.2.2.1,h.2.2.2]
  have hin : HasDerivAt (fun t : ℝ => qB t-z^2) (-2) B :=
    ((((hasDerivAt_id' B).const_mul 2).const_sub Q0).sub_const (z^2)).congr_deriv (by ring)
  change HasDerivAt (fun t : ℝ => Real.sqrt (qB t-z^2)) _ B
  convert hin.sqrt hn using 1
  have hr : inverseRoot B z=Real.sqrt (qB B-z^2) := rfl
  rw [← hr]
  field_simp [h.2.2.1.ne']

lemma inverseSlope_z_hasDerivAt {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(2/5):ℝ) (2/5)) :
    HasDerivAt (inverseSlope B) (1/(inverseRoot B z)^3) z := by
  have h := inverse_data hB hz
  have hd := ((hasDerivAt_id z).div ((inverseRoot_z_hasDerivAt hB hz).const_mul (qB B))
    (mul_ne_zero h.2.1.ne' h.2.2.1.ne')).const_add ((Q0-B-1/2)/(U B*qB B))
  convert hd using 1
  · rfl
  · have hq : qB B=(inverseRoot B z)^2+z^2 := by linarith [h.2.2.2]
    simp only [id]
    rw [hq]
    have hr := h.2.2.1.ne'
    have hq0 : (inverseRoot B z)^2+z^2≠0 := by positivity
    field_simp
    ring

lemma inverseSlope_B_hasDerivAt {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(2/5):ℝ) (2/5)) :
    HasDerivAt (fun t => inverseSlope t z) (inverseSlopeB B z) B := by
  have h := inverse_data hB hz
  have hU := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const (1/2)
  have hq : HasDerivAt qB (-2) B :=
    (((hasDerivAt_id' B).const_mul 2).const_sub Q0).congr_deriv (by ring)
  have hn := ((hasDerivAt_id B).const_sub Q0).sub_const (1/2)
  have hfirst := hn.div (hU.mul hq) (mul_ne_zero h.1.ne' h.2.1.ne')
  have hsecond := (hasDerivAt_const B z).div
    (hq.mul (inverseRoot_B_hasDerivAt hB hz)) (mul_ne_zero h.2.1.ne' h.2.2.1.ne')
  convert hfirst.add hsecond using 1
  · rfl
  · have key : inverseSlopeB B z=
        (-1*((arc B+1/2)*qB B)-(Q0-B-1/2)*(-ratio B*qB B+(arc B+1/2)*(-2)))/
          ((arc B+1/2)*qB B)^2+
        (0*(qB B*inverseRoot B z)-z*(-2*inverseRoot B z+qB B*(-1/inverseRoot B z)))/
          (qB B*inverseRoot B z)^2 := by
      have hu : U B=arc B+1/2 := rfl
      have hr : ratio B=(B+1/2)/(arc B+1/2) := rfl
      have hQ : Q0=qB B+2*B := by simp only [qB]; ring
      have ha : arc B+1/2≠0 := hu ▸ h.1.ne'
      have hq0 := h.2.1.ne'
      have hr0 := h.2.2.1.ne'
      rw [inverseSlopeB,hu,hr,hQ]
      generalize arc B+1/2=a at *
      generalize qB B=q at *
      generalize inverseRoot B z=r at *
      field_simp [ha,hq0,hr0]
      ring
    rw [key]
    rfl

lemma inverseSlope_z_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (inverseSlope B) (Icc (-(2/5):ℝ) (2/5)) :=
  monoOn_of_hasDeriv_nonneg
    (fun z hz => (inverseSlope_z_hasDerivAt hB hz).continuousAt.continuousWithinAt)
    (fun z hz => inverseSlope_z_hasDerivAt hB (Ioo_subset_Icc_self hz))
    (fun z hz => by
      have := (inverse_data hB (Ioo_subset_Icc_self hz)).2.2.1
      positivity)

lemma inverseSlope_B_nonneg {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈Icc (0:ℝ) (2/5)) : 0≤ inverseSlopeB B z := by
  have h := inverse_data hB ⟨by linarith [hz.1],hz.2⟩
  have hn : 0<Q0-B-1/2 := by norm_num [Q0]; linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hQ : 0<Q0-1 := by norm_num [Q0]
  have hW : 0<B+1/2 := by linarith [hB.1]
  dsimp only [inverseSlopeB]
  have t1 : 0≤(Q0-1)/(U B*(qB B)^2) :=
    div_nonneg hQ.le (mul_pos h.1 (pow_pos h.2.1 2)).le
  have t2 : 0≤(Q0-B-1/2)*(B+1/2)/((U B)^3*qB B) :=
    div_nonneg (mul_pos hn hW).le (mul_pos (pow_pos h.1 3) h.2.1).le
  have t3 : 0≤z*(2/((qB B)^2*inverseRoot B z)+1/(qB B*(inverseRoot B z)^3)) :=
    mul_nonneg hz.1 (add_nonneg
      (div_nonneg (by norm_num) (mul_pos (pow_pos h.2.1 2) h.2.2.1).le)
      (div_nonneg (by norm_num) (mul_pos h.2.1 (pow_pos h.2.2.1 3)).le))
  linarith

lemma inverseSlope_B_monotone {z : ℝ} (hz : z∈Icc (0:ℝ) (2/5)) :
    MonotoneOn (fun B => inverseSlope B z) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (inverseSlope_B_hasDerivAt hB ⟨by linarith [hz.1],hz.2⟩).continuousAt.continuousWithinAt)
    (fun B hB => inverseSlope_B_hasDerivAt (Ioo_subset_Icc_self hB) ⟨by linarith [hz.1],hz.2⟩)
    (fun B hB => inverseSlope_B_nonneg (Ioo_subset_Icc_self hB) hz)

lemma inverseSlope_actual {B x : ℝ} (hd : MinusDomain B x) :
    minusK B x/minusSpeed B x=inverseSlope B (minus B x-1/2) := by
  have hz := minus_z_bound hd
  have h := inverse_data hd.1 ⟨hz.1.le,hz.2.le⟩
  have hv := (positive_data hd.1 hd.2.1).2.1
  have hc := UW_circle (outer_domain hd.1)
  have hn := minus_norm hd.1 x
  have he : inverseRoot B (minus B x-1/2)=minusSpeed B x := by
    dsimp [qB] at h
    nlinarith [h.2.2.1,h.2.2.2]
  have hq : qB B=(U B)^2+(B-1/2)^2 := by
    dsimp [qB]
    dsimp [W] at hc
    nlinarith
  have hnum : Q0-B-1/2=(U B)^2+(B-1/2)*(B+1/2) := by
    dsimp [W] at hc
    nlinarith
  have hq0 : (U B)^2+(B-1/2)^2≠0 := hq ▸ h.2.1.ne'
  have hu0 := h.1.ne'
  have hv0 := hv.ne'
  rw [inverseSlope,he,hq,hnum]
  simp only [minusK,minusSpeed,minus,ratio,U] at hq0 hu0 hv0 ⊢
  generalize arc B+1/2=a at *
  generalize Real.cos x=c at *
  generalize Real.sin x=s at *
  obtain ⟨v,hvdef⟩ : ∃ v,v=a*c+(B-1/2)*s := ⟨_,rfl⟩
  rw [← hvdef] at hv0 ⊢
  field_simp [hq0,hu0,hv0]
  rw [hvdef]
  ring

lemma seven_radical_lower : (1573/1000:ℝ)<U (7/10) := by
  have hB : (7/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hc := UW_circle (outer_domain hB)
  have hu := U_positive (outer_domain hB)
  norm_num [Q0,W] at hc
  nlinarith

lemma slope_seven_small : inverseSlope (7/10) (3/50)<(351/500:ℝ) := by
  have hB : (7/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have h := inverse_data hB (by norm_num : (3/50:ℝ)∈Icc (-(2/5)) (2/5))
  have hv : (198/125:ℝ)< inverseRoot (7/10) (3/50) := by
    have hs := h.2.2.2
    norm_num [qB,Q0] at hs
    nlinarith [h.2.2.1]
  have hn : 0≤Q0-(7/10:ℝ)-1/2 := by norm_num [Q0]
  have h1 : (Q0-7/10-1/2)/(U (7/10)*qB (7/10))≤
      (Q0-7/10-1/2)/((1573/1000)*qB (7/10)) := by
    apply div_le_div_of_nonneg_left hn (by norm_num [qB,Q0])
    exact mul_le_mul_of_nonneg_right seven_radical_lower.le h.2.1.le
  have h2 : (3/50)/(qB (7/10)*inverseRoot (7/10) (3/50))≤
      (3/50)/(qB (7/10)*(198/125)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num [qB,Q0])
    exact mul_le_mul_of_nonneg_left hv.le h.2.1.le
  dsimp [inverseSlope]
  norm_num [qB,Q0] at h1 h2 ⊢
  linarith

lemma slope_seven_large : inverseSlope (7/10) (4/25)<(727/1000:ℝ) := by
  have hB : (7/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have h := inverse_data hB (by norm_num : (4/25:ℝ)∈Icc (-(2/5)) (2/5))
  have hv : (1577/1000:ℝ)< inverseRoot (7/10) (4/25) := by
    have hs := h.2.2.2
    norm_num [qB,Q0] at hs
    nlinarith [h.2.2.1]
  have h1 : (Q0-7/10-1/2)/(U (7/10)*qB (7/10))≤
      (Q0-7/10-1/2)/((1573/1000)*qB (7/10)) := by
    apply div_le_div_of_nonneg_left (by norm_num [Q0]) (by norm_num [qB,Q0])
    exact mul_le_mul_of_nonneg_right seven_radical_lower.le h.2.1.le
  have h2 : (4/25)/(qB (7/10)*inverseRoot (7/10) (4/25))≤
      (4/25)/(qB (7/10)*(1577/1000)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num [qB,Q0])
    exact mul_le_mul_of_nonneg_left hv.le h.2.1.le
  dsimp [inverseSlope]
  norm_num [qB,Q0] at h1 h2 ⊢
  linarith

/-- The positive-term majorant in equation (19), on the entire final interval. -/
lemma inverseSlopeB_upper {B : ℝ} (hB : B∈Icc (7/10:ℝ) outerDiagonal) :
    inverseSlopeB B (4/25)<(6/5:ℝ) := by
  have hBi : B∈Icc 0 outerDiagonal := ⟨by linarith [hB.1],hB.2⟩
  have h := inverse_data hBi (by norm_num : (4/25:ℝ)∈Icc (-(2/5)) (2/5))
  have hq : (5289/2500:ℝ)≤qB B := by
    norm_num [qB,Q0]
    linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hU : (699/500:ℝ)≤U B := by
    have hc := UW_circle (outer_domain hBi)
    have hW : W B≤(7/5:ℝ) := by dsimp [W]; linarith [hB.2,outer_endpoint_bounds.2.2.2]
    have hW0 : 0≤W B := by dsimp [W]; linarith [hBi.1]
    have hs := pow_le_pow_left₀ hW0 hW 2
    norm_num [Q0] at hc
    nlinarith [h.1]
  have hv : (289/200:ℝ)≤ inverseRoot B (4/25) := by
    nlinarith [h.2.2.1,h.2.2.2]
  have hn0 : 0≤Q0-B-1/2 := by norm_num [Q0]; linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hn : Q0-B-1/2≤Q0-6/5 := by linarith [hB.1]
  have hW : B+1/2≤(7/5:ℝ) := by linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hW0 : 0≤B+1/2 := by linarith [hB.1]
  have hq2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5289/2500) hq 2
  have hU3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤699/500) hU 3
  have hv3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤289/200) hv 3
  have hden1 := mul_le_mul hU hq2 (by norm_num) h.1.le
  have hden2 := mul_le_mul hU3 hq (by norm_num) (pow_nonneg h.1.le 3)
  have hden3 := mul_le_mul hq2 hv (by norm_num) (sq_nonneg (qB B))
  have hden4 := mul_le_mul hq hv3 (by norm_num) h.2.1.le
  have hnum := mul_le_mul hn hW hW0 (by norm_num [Q0] : (0:ℝ)≤Q0-6/5)
  have h1 := div_le_div_of_nonneg_left
    (by norm_num [Q0] : (0:ℝ)≤Q0-1) (by norm_num : (0:ℝ)<(699/500)*(5289/2500)^2) hden1
  have h2a := div_le_div_of_nonneg_right hnum (mul_pos (pow_pos h.1 3) h.2.1).le
  have h2b := div_le_div_of_nonneg_left
    (by norm_num [Q0] : (0:ℝ)≤(Q0-6/5)*(7/5))
    (by norm_num : (0:ℝ)<(699/500)^3*(5289/2500)) hden2
  have h3 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤2)
    (by norm_num : (0:ℝ)<(5289/2500)^2*(289/200)) hden3
  have h4 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)<(5289/2500)*(289/200)^3) hden4
  have href : (Q0-1)/((699/500)*(5289/2500)^2)+
      (Q0-6/5)*(7/5)/((699/500)^3*(5289/2500))+
      (4/25)*(2/((5289/2500)^2*(289/200))+1/((5289/2500)*(289/200)^3))<(6/5:ℝ) := by
    norm_num [Q0]
  dsimp [inverseSlopeB]
  linarith

lemma slope_gap_late {B : ℝ} (hB : B∈Icc (7/10:ℝ) outerDiagonal) :
    inverseSlope B (4/25)<LLabel.d1 B := by
  let f : ℝ→ℝ := fun t => LLabel.d1 t-inverseSlope t (4/25)
  have hdom {t : ℝ} (ht : t∈Icc (7/10:ℝ) outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2⟩
  have hd (t : ℝ) (ht : t∈Icc (7/10:ℝ) outerDiagonal) :
      HasDerivAt f (LLabel.d2 t-inverseSlopeB t (4/25)) t :=
    (LLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub
      (inverseSlope_B_hasDerivAt (hdom ht) (by norm_num))
  have hm : MonotoneOn f (Icc (7/10:ℝ) outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hd t (Ioo_subset_Icc_self ht))
      (fun t ht => by
        have hcurv := L_seven_second.trans_le (L_second_monotone
          (Asymmetric.rational_outer_mem (by norm_num)) (hdom (Ioo_subset_Icc_self ht)) ht.1.le)
        linarith [inverseSlopeB_upper (Ioo_subset_Icc_self ht)])
  have hh := hm ⟨le_rfl,(Asymmetric.rational_outer_mem (by norm_num)).2⟩ hB hB.1
  dsimp [f] at hh
  linarith [L_seven_first,slope_seven_large]

lemma target_derivative_positive {B x : ℝ} (hd : MinusDomain B x)
    (hfirst : minusFirst LLabel B x≤0) : 0< minusTarget LLabel LLabel B x := by
  obtain ⟨hB,hsource,hsmall⟩ := nonpositive_angular_location hd hfirst
  have hz := minus_z_bound hd
  have hv := (positive_data hd.1 hd.2.1).2.1
  have hK := (positive_data hd.1 hd.2.1).2.2.2
  have hwork : LLabel.d1 (minus B x)*minusSpeed B x≤1 := by
    dsimp [minusFirst] at hfirst
    linarith
  have hD : LLabel.d1 (minus B x)≤1/minusSpeed B x :=
    (le_div_iff₀ hv).2 hwork
  have hpay := mul_le_mul_of_nonneg_right hD hK.le
  have hratio : inverseSlope B (minus B x-1/2)<LLabel.d1 B := by
    by_cases he : B≤7/10
    · have hsourceSmall := hsmall he
      have h1 := inverseSlope_z_monotone hd.1 ⟨hz.1.le,hz.2.le⟩
        (by norm_num : (3/50:ℝ)∈Icc (-(2/5)) (2/5)) (by linarith)
      have h2 := inverseSlope_B_monotone (by norm_num : (3/50:ℝ)∈Icc 0 (2/5))
        hd.1 (Asymmetric.rational_outer_mem (by norm_num)) he
      have h3 := L_first_late_monotone
        ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩
        ⟨by linarith,hd.1.2⟩ hB.le
      linarith [slope_seven_small,L_67_first]
    · have h1 := inverseSlope_z_monotone hd.1 ⟨hz.1.le,hz.2.le⟩
        (by norm_num : (4/25:ℝ)∈Icc (-(2/5)) (2/5)) (by linarith)
      exact h1.trans_lt (slope_gap_late ⟨by linarith,hd.1.2⟩)
  rw [← inverseSlope_actual hd] at hratio
  have he : 1/minusSpeed B x*minusK B x=minusK B x/minusSpeed B x := by ring
  dsimp only [minusTarget]
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
end
end
end

section
/-!
## Boundary completeness for the symmetric negative-angle contact

A compact minimum with positive angle has a nonpositive one-sided angular derivative. The
location lemmas then put its source strictly inside the physical arc, and the positive target
derivative gives a feasible left descent, also at the closed target diagonal. Thus every minimum
is aligned (`minimum_aligned`), which gives the lower bound `minus_lower`.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

/-- A differentiable minimum at the right end of a nondegenerate left interval
has nonpositive derivative. The proof uses a local linear minorant. -/
private lemma right_minimum_derivative {f d : ℝ→ℝ} {l x : ℝ}
    (hlx : l<x) (hc : ContinuousAt d x)
    (hd : ∀t∈Icc l x, HasDerivAt f (d t) t)
    (hmin : ∀t∈Icc l x, f x≤f t) : d x≤0 := by
  by_contra! hpos
  have hN : {t : ℝ | l<t ∧ d x/2<d t}∈𝓝 x := by
    filter_upwards [eventually_gt_nhds hlx,
      hc.tendsto.eventually (eventually_gt_nhds (half_lt_self hpos))] with t ht hu
    exact ⟨ht,hu⟩
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hN
  let y := x-ε/2
  have hyx : y<x := by dsimp [y]; linarith
  have hball {t : ℝ} (ht : t∈Icc y x) : t∈Metric.ball x ε := by
    change dist t x<ε
    rw [Real.dist_eq]
    apply abs_lt.mpr
    dsimp [y] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hy : l<y := (hsub (hball ⟨le_rfl,hyx.le⟩)).1
  have hdom {t : ℝ} (ht : t∈Icc y x) : t∈Icc l x :=
    ⟨hy.le.trans ht.1,ht.2⟩
  have hm : MonotoneOn (fun t => f t-(d x/2)*t) (Icc y x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => ((hd t (hdom ht)).sub
        ((hasDerivAt_id t).const_mul (d x/2))).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (hdom (Ioo_subset_Icc_self ht))).sub
        ((hasDerivAt_id t).const_mul (d x/2)))
      (fun t ht => by linarith [(hsub (hball (Ioo_subset_Icc_self ht))).2])
  have hh := hm ⟨le_rfl,hyx.le⟩ ⟨hyx.le,le_rfl⟩ hyx.le
  have hl := hmin y ⟨hy.le,hyx.le⟩
  nlinarith [mul_pos (half_pos hpos) (sub_pos.mpr hyx)]

lemma targetFirst_continuousAt {B x : ℝ} (hd : MinusDomain B x) :
    ContinuousAt (fun C => minusTarget LLabel LLabel C x) B := by
  have hsource := ((LLabel.d1_hasDerivAt (outer_domain hd.2.2)).comp B
    (minus_target_hasDerivAt hd.1 x)).continuousAt
  have htarget := (LLabel.d1_hasDerivAt (outer_domain hd.1)).continuousAt
  have hratio := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).continuousAt
  have hK : ContinuousAt (fun C => minusK C x) B :=
    continuousAt_const.add (hratio.mul continuousAt_const)
  exact htarget.sub (hsource.mul hK)

lemma minimum_aligned {B x : ℝ} (hd : MinusDomain B x)
    (hmin : ∀C y, MinusDomain C y → minusCost LLabel LLabel B x≤ minusCost LLabel LLabel C y) :
    x=0 := by
  by_contra hxne
  have hx : 0<x := lt_of_le_of_ne hd.2.1.1 (Ne.symm hxne)
  have hdx : minusFirst LLabel B x≤0 :=
    right_minimum_derivative hx (minusFirst_hasDerivAt LLabel hd).continuousAt
      (fun t ht => minusCost_hasDerivAt LLabel LLabel (NegativePJ.domain_before hd ht))
      (fun t ht => hmin B t (NegativePJ.domain_before hd ht))
  have hloc := nonpositive_angular_location hd hdx
  have hsource : minus B x∈Ioo 0 outerDiagonal :=
    ⟨by linarith [minus_aligned_le hd.1 hd.2.1,hd.1.2,outer_endpoint_bounds.2.2.2],
      by linarith [hloc.2.1,fine_outer_endpoint_bounds.2]⟩
  let O : Set ℝ := Ioi 0 ∩ (fun C => minus C x) ⁻¹' Ioo 0 outerDiagonal
  have hcont : Continuous (fun C => minus C x) := by dsimp [minus,arc]; fun_prop
  have hO : IsOpen O := isOpen_Ioi.inter (isOpen_Ioo.preimage hcont)
  have hmem : B∈O := ⟨show (0:ℝ)<B by linarith [hloc.1],hsource⟩
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO hmem
  have hdom {C : ℝ} (hC : C∈Icc (B-ε) B) : MinusDomain C x := by
    have hh := hsub (show C∈Icc (B-ε) (B+ε) from ⟨hC.1,by linarith [hC.2]⟩)
    exact ⟨⟨hh.1.le,hC.2.trans hd.1.2⟩,hd.2.1,Ioo_subset_Icc_self hh.2⟩
  have hBder : minusTarget LLabel LLabel B x≤0 :=
    right_minimum_derivative (f := fun C => minusCost LLabel LLabel C x)
      (d := fun C => minusTarget LLabel LLabel C x) (by linarith : B-ε<B)
      (targetFirst_continuousAt hd)
      (fun C hC => minusCost_target_hasDerivAt LLabel LLabel (hdom hC))
      (fun C hC => hmin C x (hdom hC))
  exact (not_lt_of_ge hBder) (target_derivative_positive hd hdx)

/-- The whole negative-angle symmetric physical contact, with both diagonals. -/
theorem minus_lower {B x : ℝ} (hd : MinusDomain B x) :
    (89777/100000:ℝ)< minusCost LLabel LLabel B x := by
  let guard : ℝ×ℝ→ℝ := fun p => outerDiagonal-minus p.1 p.2
  let cost : ℝ×ℝ→ℝ := fun p => minusCost LLabel LLabel p.1 p.2
  have hg : Continuous guard := by dsimp [guard,minus,arc]; fun_prop
  have hc : Continuous cost := by
    dsimp [cost,minusCost,RoleLabel.outer,RoleLabel.eval,minus,arc]
    fun_prop
  obtain ⟨p,hp,hbetter,hmin⟩ := contact_region_minimum hg hc
    (p₀ := (B,x)) ⟨hd.1,hd.2.1,sub_nonneg.mpr hd.2.2.2⟩
  have hpd : MinusDomain p.1 p.2 :=
    ⟨hp.1,hp.2.1,⟨by
      linarith [minus_aligned_le hp.1 hp.2.1,hp.1.2,outer_endpoint_bounds.2.2.2],
      sub_nonneg.mp hp.2.2⟩⟩
  have haligned : p.2=0 := minimum_aligned hpd (fun C y hCy =>
    hmin (C,y) hCy.1 hCy.2.1 (sub_nonneg.mpr hCy.2.2.2))
  have hsource := hpd.2.2
  rw [haligned] at hsource
  norm_num [minus] at hsource
  have hl := AlignedL.original hsource hpd.1 (by ring)
  have hcost : (89777/100000:ℝ)< minusCost LLabel LLabel p.1 p.2 := by
    simpa [minusCost,minus,haligned] using hl
  exact hcost.trans_le hbetter

end SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
end
end
end

section
/-!
## The original symmetric opposite-sign outer zero-quarter pair

The
unchanged original labels are restored after lowering to first contact.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma label_monotone : MonotoneOn LLabel.outer (Icc 0 outerDiagonal) := L_monotone

theorem original_positive {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (17953/20000:ℝ)<x+LLabel.eval a b+LLabel.eval A B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hm' : plus B x≤b := by
    have hw := signed_width (show |x|≤7/10 from abs_le.mpr ⟨by linarith [hx.1],hx.2⟩)
    rw [abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin] at hm
    rw [hw] at hm
    dsimp [plus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hcontact : ∃C, C∈Icc 0 B ∧ PlusDomain C x ∧ plus C x≤b := by
    by_cases hp : 0≤plus B x
    · exact ⟨B,⟨hB.1,le_rfl⟩,⟨hB,hx,⟨hp,hm'.trans hb.2⟩⟩,hm'⟩
    · have hzero : 0<plus 0 x := by
        have hh := SameZero.b_lower outer_zero_mem hx
        have heq : SameZero.b 0 x=plus 0 x := by simp only [SameZero.b,plus]; ring
        linarith
      have hc : Continuous (fun C => plus C x) := by dsimp [plus,arc]; fun_prop
      obtain ⟨C,hC,he⟩ := intermediate_value_Icc hB.1 hc.neg.continuousOn
        (show (0:ℝ)∈Icc (-plus 0 x) (-plus B x) by constructor <;> linarith)
      have he' : -plus C x=0 := he
      have hplus : plus C x=0 := by linarith
      refine ⟨C,hC,⟨⟨hC.1,hC.2.trans hB.2⟩,hx,?_⟩,?_⟩
      · rw [hplus]
        exact outer_zero_mem
      · rw [hplus]
        exact hb.1
  obtain ⟨C,hC,hd,hbC⟩ := hcontact
  have h1 := label_monotone hd.2.2 hb hbC
  have h2 := label_monotone hd.1 hB hC.2
  have hh := plus_lower hd
  rw [LLabel.outer_actual hs] at h1
  rw [LLabel.outer_actual ht] at h2
  dsimp [plusCost] at hh
  linarith

theorem original_negative {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) (-x)) :
    (17953/20000:ℝ)< -x+LLabel.eval a b+LLabel.eval A B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hm' : minus B x≤b := by
    have hw := signed_width (show |-x|≤7/10 by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2)
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin,Real.sin_neg,Real.cos_neg] at hm
    rw [hw] at hm
    dsimp [minus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hd : MinusDomain B x := ⟨hB,hx,⟨by
    linarith [minus_aligned_le hB hx,hB.2,outer_endpoint_bounds.2.2.2],hm'.trans hb.2⟩⟩
  have h1 := label_monotone hd.2.2 hb hm'
  rw [LLabel.outer_actual hs] at h1
  have hh := minus_lower hd
  dsimp [minusCost] at hh
  rw [LLabel.outer_actual ht] at hh
  linarith

theorem original {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (17953/20000:ℝ)<x+LLabel.eval a b+LLabel.eval A B := by
  rcases le_total 0 x with hpos | hneg
  · exact original_positive hs ht ⟨hpos,(abs_le.mp hx).2⟩ hm
  · have hxn : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    simpa only [neg_neg] using original_negative hs ht hxn (by simpa using hm)

end SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.OppositeZero
open CommonQuarter Arithmetic QuarterWordGeometry

lemma literal_four (a b A B x : ℝ) :
    SecondWord.cost 4 .outer .outer true false a b A B x=
      x+LLabel.eval a b+LLabel.eval A B := by
  norm_num [SecondWord.cost,label,wrongValue,WordProblems.secondCoefficients,
    WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
    next,RoleLabel.eval,LLabel]
  ring

theorem symmetric_source {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    threshold 4<SecondWord.cost 4 .outer .outer true false a b A B x := by
  rw [threshold_value,literal_four]
  exact Symmetric.original hs ht hx hm

theorem symmetric_target {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 (-1) x) :
    threshold 4<SecondWord.cost 4 .outer .outer true false a b A B x := by
  have hrev : 0≤Eight.forwardMargin 0 A B a b 1 (-1) x := by
    simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm
  have hh := Symmetric.original ht hs hx hrev
  rw [threshold_value,literal_four]
  linarith

theorem symmetric_actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (hs : C.kind 4=.outer) (ht : C.kind (next 4)=.outer)
    (hsg : positiveOf C 4≠positiveOf C (next 4)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square 4) (C.square (next 4))) :
    threshold 4<phaseValue F hgap 4+wrongMarker C .second 4-
      wrongMarker C .second (next 4) := by
  have hz : F.word hgap pi_lt_22_over_7 4=0 := by
    rw [hw]
    norm_num [WordProblems.wrongWord]
  have hx : |phaseValue F hgap 4|≤7/10 := by
    simpa [phaseValue,hz] using (difference_small F 4).le
  have hsource : OuterState (C.a 4) (C.b 4) := by
    simpa [State,hs] using actual_state C 4
  have htarget : OuterState (C.a (next 4)) (C.b (next 4)) := by
    simpa [State,ht] using actual_state C (next 4)
  have hm := original_margin C F hgap 4 j howner
  have hh : threshold 4<SecondWord.cost 4 .outer .outer
      (positiveOf C 4) (positiveOf C (next 4)) (C.a 4) (C.b 4)
      (C.a (next 4)) (C.b (next 4)) (phaseValue F hgap 4) := by
    rcases WrongZeroOriginalOwners.original C F hgap 4 hz j howner with
      ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
    · have htargetneg : positiveOf C (next 4)=false := by
        cases h : positiveOf C (next 4) <;> simp_all
      rw [hpos,htargetneg]
      exact symmetric_source hsource htarget hx
        (by simpa [hpos,htargetneg,WordProblems.sign] using hm)
    · have hsourcepos : positiveOf C 4=true := by
        cases h : positiveOf C 4 <;> simp_all
      rw [hsourcepos,hneg]
      exact symmetric_target hsource htarget hx
        (by simpa [hsourcepos,hneg,WordProblems.sign] using hm)
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i≠positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hword : WordProblems.wrongWord .second i=0 := by simpa [hw] using hi
  have hcases : i=0 ∨ i=1 ∨ i=4 := by
    revert hword
    fin_cases i <;> norm_num [WordProblems.wrongWord]
  rcases hcases with hzero | hone | hfour
  · exact Asymmetric.actual_owner C F hgap hw i (Or.inl hzero) hs ht hsg j howner
  · exact Asymmetric.actual_owner C F hgap hw i (Or.inr hone) hs ht hsg j howner
  · subst i
    exact symmetric_actual_owner C F hgap hw hs ht hsg j howner

end SquaresInCircles.Eight.SecondWord.OppositeZero

namespace SquaresInCircles.Eight.SecondWord.OuterZero
open CommonQuarter Arithmetic QuarterWordGeometry

/-- Every zero edge, either sign relation, and every originally feasible axis. -/
theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  by_cases hsign : positiveOf C i=positiveOf C (next i)
  · exact SameZero.actual_owner C F hgap hw i hi hs ht hsign j howner
  · exact OppositeZero.actual_owner C F hgap hw i hi hs ht hsign j howner

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F hgap hw i hi hs ht j (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.SecondWord.OuterZero
end
end
end
