module

public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Owners.SplitConcavityTools
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeNegative
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveSourceDiagonal
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveAxisSlopes
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameCap
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveStationary
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveZeroGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveZeroBoundary
public import SquaresInCircles.Eight.Words.Wrong.ZeroOriginalOwners

/-!
# Eight squares: all six original opposite-sign outer zero owners of the short word

The
negative and positive angle halves meet with their actual weak contact.
Reversal swaps the original states and their label coefficients exactly;
it never changes a role label on another edge of the physical cycle.
-/

section
/-!
## The complete positive target-zero boundary

The
three increasing rows, the two convex-first-derivative rows, and the
remaining monotone-first-derivative row cover the whole physical axis.
The initial endpoint is the same actual source-diagonal contact used
in the preceding boundary proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Axis
open CommonQuarter CorePairGeometry Arithmetic

lemma initial_value (r : Row) {e : ℝ} (he : Same.Event.IsEvent e) :
    (89809/100000:ℝ)<value r e := by
  have hsource : b e=outerDiagonal := by rw [same_source]; exact he.2
  have hl := SourceDiagonal.event_cost r he
  dsimp [value,plusCost]
  rw [show plus 0 e=outerDiagonal from hsource]
  simp only [source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
    ShortOuterOne.SameContact.arc_diagonal,ShortOuterOne.SameContact.arc_zero,
    mul_zero,add_zero,zero_mul,zero_add]
  linarith

lemma four_second_monotone {e : ℝ} (he : Same.Event.IsEvent e) :
    MonotoneOn (second 4) (Icc e (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hx => (second_hasDerivAt 4 (domain he hx)).continuousAt.continuousWithinAt)
    (fun _ hx => second_hasDerivAt 4 (domain he (Ioo_subset_Icc_self hx)))
    (fun _ hx => (nonnegative_primary_third 4 (Or.inr (Or.inr rfl))
      (domain he (Ioo_subset_Icc_self hx))).le)

lemma four_first_positive {e x : ℝ} (he : Same.Event.IsEvent e)
    (hx : x∈Icc e (7/10)) : 0<first 4 x := by
  have hecap : e≤(7/10:ℝ) := (Same.Event.angle_mem he).2
  have hsecond {y : ℝ} (hy : y∈Icc e (7/10)) : second 4 y<0 := by
    have hh := four_second_monotone he hy ⟨hecap,le_rfl⟩ hy.2
    linarith [References.four_final.1]
  have hm : AntitoneOn (first 4) (Icc e (7/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun y hy => (first_hasDerivAt 4 (domain he hy)).continuousAt.continuousWithinAt)
      (fun y hy => first_hasDerivAt 4 (domain he (Ioo_subset_Icc_self hy)))
      (fun y hy => (hsecond (Ioo_subset_Icc_self hy)).le)
  have hh := hm hx ⟨hecap,le_rfl⟩ hx.2
  linarith [References.four_final.2]

lemma convex_first (r : Row) (hr : r=1 ∨ r=2) {e : ℝ} (he : Same.Event.IsEvent e) :
    ConvexOn ℝ (Icc e (7/10)) (first r) := by
  have hr' : r=1 ∨ r=2 ∨ r=4 := by rcases hr with rfl | rfl <;> simp
  have hc : ConcaveOn ℝ (Icc e (7/10)) (fun x => -first r x) :=
    concave_of_deriv2
      (fun x hx => (first_hasDerivAt r (domain he hx)).neg)
      (fun x hx => (second_hasDerivAt r (domain he hx)).neg)
      (fun x hx => neg_nonpos.mpr (nonnegative_primary_third r hr' (domain he hx)).le)
  have h := hc.neg
  have hfun : (-fun x => -first r x)=first r := by
    funext x
    simp
  rwa [hfun] at h

lemma two_endpoint_rows (r : Row) (hr : r=1 ∨ r=2) {e x : ℝ}
    (he : Same.Event.IsEvent e) (hx : x∈Icc e (7/10)) :
    (89809/100000:ℝ)<value r x := by
  have hlast : first r (7/10)≤0 := by
    rcases hr with rfl | rfl <;> linarith [References.one_final.1,References.two_final.1]
  have hfinal : (89809/100000:ℝ)<value r (7/10) := by
    rcases hr with rfl | rfl <;> linarith [References.one_final.2,References.two_final.2]
  have hmin := SplitConcavityTools.minimum_of_convex_derivative
    (fun x hx => value_hasDerivAt r (domain he hx)) (convex_first r hr he) hlast hx
  exact (lt_min (initial_value r he) hfinal).trans_le hmin

/-- The physical target-zero boundary contains no remaining scalar premise. -/
theorem lower (r : Row) {x : ℝ} (hd : PlusDomain 0 x) :
    (89809/100000:ℝ)<value r x := by
  obtain ⟨e,he⟩ := Same.Event.exists_event
  have hx : x∈Icc e (7/10) := ⟨before_event he hd,hd.2.1.2⟩
  by_cases hconvex : r=1 ∨ r=2
  · exact two_endpoint_rows r hconvex he hx
  have hderiv : ∀y∈Icc e (7/10),0<first r y := by
    intro y hy
    by_cases hfour : r=4
    · subst r
      exact four_first_positive he hy
    · have hrows : r=0 ∨ r=3 ∨ r=5 := by fin_cases r <;> simp_all
      exact increasing_rows r hrows (domain he hy)
  have hm : MonotoneOn (value r) (Icc e (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => (value_hasDerivAt r (domain he hy)).continuousAt.continuousWithinAt)
      (fun y hy => value_hasDerivAt r (domain he (Ioo_subset_Icc_self hy)))
      (fun y hy => (hderiv y (Ioo_subset_Icc_self hy)).le)
  exact (initial_value r he).trans_le (hm ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1)

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Axis
end
end
end

section
/-!
## Every positive-angle opposite-sign short-word zero contact

Compactness is applied to the whole original contact region (`contact_lower`). Alignment, the
final angle and all four state boundaries have their own estimates (`aligned_lower`,
`minimum_lower`). The six row-specific interior exclusions keep the original source and target
coordinates (`interior_not_minimum`). An inactive zero source is reduced to its contact by
decreasing the target coordinate, using the strict monotonicity of the label (`original`).
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open SecondWord (outer_domain outer_zero_mem)

lemma interior_not_minimum (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hB : B∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 (7/10))
    (hb : plus B x∈Ioo 0 outerDiagonal)
    (hmin : ∀C y, PlusDomain C y → plusCost r B x≤plusCost r C y) : False := by
  let T : Set ℝ := Ioo 0 outerDiagonal ∩ (fun C => plus C x) ⁻¹' Ioo 0 outerDiagonal
  have hcT : Continuous (fun C => plus C x) := by dsimp [plus,SecondWord.OppositeZero.plus,arc]; fun_prop
  have hT : IsOpen T := isOpen_Ioo.inter (isOpen_Ioo.preimage hcT)
  have hBT : B∈T := ⟨hB,hb⟩
  have hdomT {C : ℝ} (hC : C∈T) : PlusDomain C x :=
    ⟨Ioo_subset_Icc_self hC.1,hd.2.1,Ioo_subset_Icc_self hC.2⟩
  have hlocalT : IsLocalMin (fun C => plusCost r C x) B := by
    filter_upwards [hT.mem_nhds hBT] with C hC
    exact hmin C x (hdomT hC)
  have htarget : plusTarget r B x=0 :=
    hlocalT.hasDerivAt_eq_zero (plusCost_target_hasDerivAt r hd)
  have htargetCurvature : 0≤plusTargetCurvature r B x :=
    ContactMinimumDerivatives.second_nonnegative (f := fun C => plusCost r C x)
      (d := fun C => plusTarget r C x) (dd := fun C => plusTargetCurvature r C x) hT hBT
      (fun C hC => hmin C x (hdomT hC))
      (fun C hC => plusCost_target_hasDerivAt r (hdomT hC))
      (fun C hC => plusTarget_hasDerivAt r (hdomT hC))
      (plusTargetCurvature_continuousAt r hd)
  by_cases hzero : r=0
  · subst r
    exact (not_lt_of_ge htargetCurvature) (row_zero_stationary_curvature hd htarget)
  by_cases htwo : r=2
  · subst r
    exact Norm.interior_not_minimum hd hB hx hb htarget hmin
  by_cases hshape : r=3 ∨ r=5
  · exact (not_lt_of_ge htargetCurvature) (Shape.stationary_curvature_negative r hshape hd htarget)
  have hpositive : r=1 ∨ r=4 := by fin_cases r <;> simp_all
  let O : Set ℝ := Ioo 0 (7/10) ∩ (plus B) ⁻¹' Ioo 0 outerDiagonal
  have hcO : Continuous (plus B) := by
    show Continuous fun y => SecondWord.OppositeZero.plus B y
    simp only [SecondWord.OppositeZero.plus]
    fun_prop
  have hO : IsOpen O := isOpen_Ioo.inter (isOpen_Ioo.preimage hcO)
  have hxO : x∈O := ⟨hx,hb⟩
  have hdomO {y : ℝ} (hy : y∈O) : PlusDomain B y :=
    ⟨hd.1,Ioo_subset_Icc_self hy.1,Ioo_subset_Icc_self hy.2⟩
  have hlocalO : IsLocalMin (plusCost r B) x := by
    filter_upwards [hO.mem_nhds hxO] with y hy
    exact hmin B y (hdomO hy)
  have hangle : plusAngle r B x=0 :=
    hlocalO.hasDerivAt_eq_zero (plusCost_angle_hasDerivAt r hd)
  have hangleCurvature : 0≤Stationary.angleSecond r B x :=
    ContactMinimumDerivatives.second_nonnegative (f := plusCost r B)
      (d := plusAngle r B) (dd := Stationary.angleSecond r B) hO hxO
      (fun y hy => hmin B y (hdomO hy))
      (fun y hy => plusCost_angle_hasDerivAt r (hdomO hy))
      (fun y hy => Stationary.plusAngle_hasDerivAt r (hdomO hy))
      (Stationary.angleSecond_continuousAt r hd)
  rcases Stationary.stationary_descent r hpositive hd hangle with hcurv | hdesc
  · exact (not_lt_of_ge hangleCurvature) hcurv
  · linarith

lemma aligned_lower (r : Row) {B : ℝ} (hd : PlusDomain B 0) :
    (89809/100000:ℝ)<plusCost r B 0 := by
  have he : SecondWord.OppositeZero.plus B 0=1-B := by
    simp only [SecondWord.OppositeZero.plus,Real.cos_zero,Real.sin_zero]
    ring
  have hh := aligned_original r hd.2.2 hd.1 (by rw [he]; ring)
  show _<plusCost r B 0
  rw [plusCost,zero_add]
  exact hh

lemma minimum_lower (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hmin : ∀C y, PlusDomain C y → plusCost r B x≤plusCost r C y) :
    (89809/100000:ℝ)<plusCost r B x := by
  by_cases hzero : x=0
  · subst x
    exact aligned_lower r hd
  by_cases hcap : x=7/10
  · subst x
    exact Cap.lower r hd
  by_cases haxis : B=0
  · subst B
    exact Axis.lower r hd
  by_cases hdiag : B=outerDiagonal
  · subst B
    exact target_diagonal_lower r hd
  by_cases hsourceZero : plus B x=0
  · exact Zero.original_lower r hd hsourceZero
  by_cases hsourceDiagonal : plus B x=outerDiagonal
  · exact SourceDiagonal.original_lower r hd hsourceDiagonal
  have hB : B∈Ioo 0 outerDiagonal :=
    ⟨lt_of_le_of_ne hd.1.1 (Ne.symm haxis),lt_of_le_of_ne hd.1.2 hdiag⟩
  have hx : x∈Ioo 0 (7/10) :=
    ⟨lt_of_le_of_ne hd.2.1.1 (Ne.symm hzero),lt_of_le_of_ne hd.2.1.2 hcap⟩
  have hb : plus B x∈Ioo 0 outerDiagonal :=
    ⟨lt_of_le_of_ne hd.2.2.1 (Ne.symm hsourceZero),lt_of_le_of_ne hd.2.2.2 hsourceDiagonal⟩
  exact (interior_not_minimum r hd hB hx hb hmin).elim

/-- Every positive contact, with no stationary or boundary premise. -/
theorem contact_lower (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    (89809/100000:ℝ)<plusCost r B x := by
  let guard : ℝ×ℝ→ℝ := fun p => min (plus p.1 p.2) (outerDiagonal-plus p.1 p.2)
  let objective : ℝ×ℝ→ℝ := fun p => plusCost r p.1 p.2
  have hg : Continuous guard := by dsimp [guard,plus,SecondWord.OppositeZero.plus,arc]; fun_prop
  have hf : Continuous objective := by
    dsimp [objective,plusCost,source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
      plus,SecondWord.OppositeZero.plus,arc]
    fun_prop
  obtain ⟨p,hp,hbetter,hmin⟩ := contact_region_minimum hg hf (p₀ := (B,x))
    ⟨hd.1,hd.2.1,le_min hd.2.2.1 (sub_nonneg.mpr hd.2.2.2)⟩
  have hpd : PlusDomain p.1 p.2 :=
    ⟨hp.1,hp.2.1,⟨hp.2.2.trans (min_le_left _ _),
      sub_nonneg.mp (hp.2.2.trans (min_le_right _ _))⟩⟩
  have hl := minimum_lower r hpd (fun C y hCy =>
    hmin (C,y) hCy.1 hCy.2.1 (le_min hCy.2.2.1 (sub_nonneg.mpr hCy.2.2.2)))
  exact hl.trans_le hbetter

lemma target_axis_source_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<plus 0 x := by
  have hh := SecondWord.SameZero.b_lower outer_zero_mem hx
  have he : plus 0 x=SecondWord.SameZero.b 0 x := Axis.same_source x
  rw [he]
  linarith

/-- The weak original owner also includes the inactive zero-source alternative. -/
theorem original (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (89809/100000:ℝ)<x+c r+p r*a+q r*b+v r*A+t r*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hcut : plus B x≤b := by
    have hw := signed_width (show |x|≤7/10 by rw [abs_of_nonneg hx.1]; exact hx.2)
    rw [abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin] at hm
    rw [hw] at hm
    dsimp [plus,SecondWord.OppositeZero.plus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  by_cases hactive : 0≤plus B x
  · have hd : PlusDomain B x := ⟨hB,hx,⟨hactive,hcut.trans hb.2⟩⟩
    have hsource := source_monotone r hd.2.2 hb hcut
    rw [(source r).outer_actual hs] at hsource
    have hl := contact_lower r hd
    dsimp [plusCost] at hl
    rw [(target r).outer_actual ht] at hl
    dsimp [source,target,SecondWord.RoleLabel.eval] at *
    linarith
  · have hc : Continuous (fun C => plus C x) := by
      dsimp [plus,SecondWord.OppositeZero.plus,arc]
      fun_prop
    obtain ⟨C,hC,he⟩ := intermediate_value_Icc hB.1 hc.neg.continuousOn
      (show (0:ℝ)∈Icc (-plus 0 x) (-plus B x) from
        ⟨by linarith [target_axis_source_positive hx],by linarith⟩)
    have heq : plus C x=0 := by simpa using he
    have hCi : C∈Icc 0 outerDiagonal := ⟨hC.1,hC.2.trans hB.2⟩
    have hd : PlusDomain C x := ⟨hCi,hx,by show plus C x∈_; rw [heq]; exact outer_zero_mem⟩
    have hl := contact_lower r hd
    rw [plusCost,heq] at hl
    have hsource := source_monotone r outer_zero_mem hb hb.1
    have htarget := target_monotone r hCi hB hC.2
    rw [(source r).outer_actual hs] at hsource
    rw [(target r).outer_actual ht] at htarget
    dsimp [source,target,SecondWord.RoleLabel.eval] at *
    linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem original (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (449/500:ℝ)<x+c r+p r*a+q r*b+v r*A+t r*B := by
  by_cases hpos : 0≤x
  · have hh := Positive.original r hs ht ⟨hpos,(abs_le.mp hx).2⟩ hm
    linarith
  · have hx' : -x∈Set.Icc 0 (7/10) :=
      ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have hh := Negative.original r hs ht hx' (by simpa only [neg_neg] using hm)
    simp only [neg_neg] at hh
    linarith

private lemma reverse_target {a b A B x : ℝ}
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 (-1) x) :
    0≤Eight.forwardMargin 0 A B a b 1 (-1) x := by
  simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm

macro "short_opposite_literal" : tactic => `(tactic|
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,next,c,p,q,v,t] at * <;> linarith)

lemma zero_role (i : Vertex) (hi : WordProblems.wrongWord .short i=0) :
    i=0 ∨ i=1 ∨ i=3 := by
  revert hi
  fin_cases i <;> norm_num [WordProblems.wrongWord]

/-- Both original secondary owners at each of the three literal zero roles. -/
theorem original_secondary (i : Vertex) (hi : WordProblems.wrongWord .short i=0)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) x) :
    (449/500:ℝ)<x+wrongValue .short i .outer true a b-
      wrongValue .short (next i) .outer false A B := by
  rcases zero_role i hi with rfl | rfl | rfl
  · rcases hj with rfl | rfl
    · have hh := original 0 hs ht hx hm
      short_opposite_literal
    · have hh := original 1 ht hs hx (reverse_target hm)
      short_opposite_literal
  · rcases hj with rfl | rfl
    · have hh := original 2 hs ht hx hm
      short_opposite_literal
    · have hh := original 3 ht hs hx (reverse_target hm)
      short_opposite_literal
  · rcases hj with rfl | rfl
    · have hh := original 4 hs ht hx hm
      short_opposite_literal
    · have hh := original 5 ht hs hx (reverse_target hm)
      short_opposite_literal

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=true) (hτ : positiveOf C (next i)=false) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hword : WordProblems.wrongWord .short i=0 := by simpa [hw] using hi
  have hx : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have haxis : j=0 ∨ j=2 := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hm := original_margin C F hgap i j howner
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hh := original_secondary i hword hsource htarget hx j haxis (by simpa [hσ,hτ,WordProblems.sign] using hm)
  simpa only [wrongMarker,hs,ht,hσ,hτ] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=true) (hτ : positiveOf C (next i)=false) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F hgap hw i hi hs ht hσ hτ j
    (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.ShortOuterZero.Opposite
end
end
end
