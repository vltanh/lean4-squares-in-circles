module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositePositiveAxisReferences
public import SquaresInCircles.Eight.TableFree.SplitConcavityTools

/-!
# The complete positive target-zero boundary

Uncompiled transcription of the fourth boundary in Section 3.2. The
three increasing rows, the two convex-first-derivative rows, and the
remaining monotone-first-derivative row cover the whole physical axis.
The initial endpoint is the same actual source-diagonal contact used
in the preceding boundary proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis
open CommonQuarter CorePairGeometry Arithmetic

lemma initial_value (r : Row) {e : ℝ} (he : Same.Event.IsEvent e) :
    (89809/100000:ℝ)<value r e := by
  have hsource : b e=outerDiagonal := by rw [same_source]; exact he.2
  have hl := SourceDiagonal.event_cost r he
  dsimp [value,plusCost]
  rw [hsource]
  simp only [source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
    ShortOuterOne.SameContact.arc_diagonal,ShortOuterOne.SameContact.arc_zero,
    mul_zero,add_zero,zero_mul,zero_add]
  linarith

lemma four_second_monotone {e : ℝ} (he : Same.Event.IsEvent e) :
    MonotoneOn (second 4) (Icc e (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x hx => (second_hasDerivAt 4 (domain he hx)).continuousAt.continuousWithinAt)
    (fun x hx => second_hasDerivAt 4 (domain he (Ioo_subset_Icc_self hx)))
    (fun x hx => (nonnegative_primary_third 4 (Or.inr (Or.inr rfl))
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
  simpa only [neg_neg] using hc.neg

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

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis
