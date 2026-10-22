module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSamePrimary

/-!
# Literal reflection and source slopes for the same-sign secondary owners

Uncompiled transcription of Section 1 of
`HAND_SHORT_WORD_SAME_SIGN_SECONDARY_COMPLETE_WITHOUT_TABLES.md`.
Reflection exchanges the two already defined role functions. This is
the literal adjacent-label identity; no sign of a selected vertex is
changed in the cycle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)
open SecondWord (U W)

def targetCost (r : Row) (B : ℝ) : ℝ := p r*arc B-q r*B
def slope (r : Row) (b : ℝ) : ℝ := t r+P r*ratio b
def targetSlope (r : Row) (B : ℝ) : ℝ := q r+p r*ratio B
def H (r : Row) (B : ℝ) : ℝ := q r*U B+p r*W B

lemma slope_eq (r : Row) (b : ℝ) : slope r b=targetD r b := by dsimp [slope,targetD]; ring
lemma slope_bounds (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<slope r b ∧ slope r b<(6/5:ℝ) := by
  have hpos := targetD_positive r hb
  have hr := SecondWord.outer_ratio_bounds hb
  rw [←slope_eq] at hpos
  refine ⟨hpos,?_⟩
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg
    (coefficient_bounds r).2.2.2.2.1 (by linarith [hr.1] : 0≤ratio b)
  dsimp [slope]
  fin_cases r <;> norm_num [t] <;> linarith

lemma targetSlope_positive (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    0<targetSlope r B := by
  have hp := mul_nonneg (coefficient_bounds r).1
    (SameContact.ratio_pos (SameContact.outer_domain hB)).le
  dsimp [targetSlope]
  have hq : 0<q r := by fin_cases r <;> norm_num [q]
  linarith

lemma targetCost_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (targetCost r) (-targetSlope r B) B := by
  convert ((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).const_mul (p r)).sub
    ((hasDerivAt_id B).const_mul (q r)) using 1 <;>
    dsimp [targetCost,targetSlope] <;> ring

lemma targetCost_antitone (r : Row) : AntitoneOn (targetCost r) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (targetCost_hasDerivAt r hB).continuousAt.continuousWithinAt)
    (fun B hB => targetCost_hasDerivAt r (Ioo_subset_Icc_self hB))
    (fun B hB => neg_nonpos.mpr (targetSlope_positive r (Ioo_subset_Icc_self hB)).le)

lemma source_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (target r) (slope r b) b := by
  rw [slope_eq]
  exact Same.target_hasDerivAt r hb

lemma slope_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (slope r) (P r*ratioD b) b := by
  convert ((SameContact.ratio_hasDerivAt (SameContact.outer_domain hb)).const_mul (P r)).
    const_add (t r) using 1 <;> dsimp [slope] <;> ring

lemma original_cost (r : Row) {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    target r b+targetCost r B= -P r*a+t r*b+p r*A-q r*B := by
  rw [target,targetCost,(SameContact.actual_arc hs).1,(SameContact.actual_arc ht).1]
  ring

lemma aligned_original (r : Row) {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hm : 1≤b+A) :
    (8981/10000:ℝ)<Real.pi/2+c r-P r*a+t r*b+p r*A-q r*B := by
  have hh := Same.aligned_original r ht hs (by linarith)
  linarith

lemma H_positive (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 0<H r B := by
  have hU := SecondWord.U_positive (SecondWord.outer_domain hB)
  have hmain := mul_pos (show 0<q r by fin_cases r <;> norm_num [q]) hU
  have hother := mul_nonneg (coefficient_bounds r).1 (show 0≤W B by dsimp [W]; linarith [hB.1])
  dsimp [H]
  linarith

lemma H_upper (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : H r B<(91/50:ℝ) := by
  have hc := SecondWord.UW_circle (SecondWord.outer_domain hB)
  have hnonneg := sq_nonneg (q r*W B-p r*U B)
  have hid : (H r B)^2+(q r*W B-p r*U B)^2=Q0*((q r)^2+(p r)^2) := by
    dsimp [H]
    linear_combination ((q r)^2+(p r)^2)*hc
  by_cases hlast : r=2
  · subst r
    have ha := (outer_bounds (SameContact.arc_state hB)).2.1
    have ha0 := ShortOuterZero.fine_axial_bounds.2
    norm_num [H,p,q,U]
    linarith
  · fin_cases r <;> norm_num [p,q,Q0] at hlast hid ⊢ <;>
    nlinarith

lemma independent_floor (r : Row) :
    (39747/50000:ℝ)<Real.pi/2+c r-P r*outerAxial+(p r-q r)*outerDiagonal := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hp := pi_hand_enclosure.1
  fin_cases r <;> norm_num [c,p,q,P] <;> linarith

lemma independent_lower (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    (39747/50000:ℝ)+x<Real.pi/2+x+c r-P r*a+t r*b+p r*A-q r*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hzero : (0:ℝ)∈Icc 0 outerDiagonal := ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal := ⟨hzero.2,le_rfl⟩
  have hsrc := target_monotone r hzero hb hb.1
  have htar := targetCost_antitone r hB hdiag hB.2
  rw [target,SameContact.arc_zero] at hsrc
  rw [targetCost,SameContact.arc_diagonal] at htar
  have hh := original_cost r hs ht
  have hf := independent_floor r
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary
