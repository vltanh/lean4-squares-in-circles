module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroNegativeScalars

/-!
# Four complete negative-core to negative-outer families

The original weak owner pays the negative source label. The resulting
outer functional increases from the actual zero-source contact in three
families; the fourth is concave and has only that contact and the
diagonal as possible minimizers. Both values have already been bounded
on their complete geometric interval. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero.NegativeContact

open CommonQuarter CorePairGeometry

def coeffX (r : Row) (x : ℝ) : ℝ := -p r-g r*Real.sin x
def coeffY (r : Row) (x : ℝ) : ℝ := q r-g r*Real.cos x
def base (r : Row) (x : ℝ) : ℝ := x+c r+g r*(1+Real.sin x+Real.cos x)/2

lemma contact_value (r : Row) (x : ℝ) :
    H r x=base r x+coeffX r x*(U x-1/2)+coeffY r x*(V x-1/2) := by
  have hh := congrArg (fun z : ℝ => g r*z) (contact_equation x)
  dsimp [H,base,coeffX,coeffY]
  nlinarith only [hh]

lemma diagonal_value (r : Row) (x : ℝ) :
    G r x=base r x+(coeffX r x+coeffY r x)*outerDiagonal := by
  dsimp [G,base,coeffX,coeffY,cut,m]
  ring

lemma original_support (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc start (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤-b+A*Real.sin x+B*Real.cos x) :
    min (H r x) (G r x)≤base r x+coeffX r x*A+coeffY r x*B := by
  obtain ⟨hc,hB⟩ := original_contact hs ht hx hm
  have tr := positive_trig (show x∈Icc 0 (7/10) from
    ⟨by linarith [hx.1,(show (0:ℝ)<start by norm_num [start])],hx.2⟩)
  have hHv := (min_le_left (H r x) (G r x)).trans_eq (contact_value r x)
  have hGv := (min_le_right (H r x) (G r x)).trans_eq (diagonal_value r x)
  by_cases h3 : r=3
  · subst r
    have hX : 0≤coeffX 3 x := by norm_num [coeffX,p,g]; linarith [tr.2.2.2.1]
    have hh := CoreContact.outer_subarc_lower hc ht hB hX
      (m := min (H 3 x) (G 3 x)-base 3 x) (Y := coeffY 3 x)
      (by linarith) (by linarith)
    linarith
  · have hX : coeffX r x≤0 := by
      fin_cases r <;> first
        | exact absurd rfl h3
        | (norm_num [coeffX,p,g]; nlinarith [tr.2.2.1])
    have hY : 0≤coeffY r x := by
      fin_cases r <;> first
        | exact absurd rfl h3
        | (norm_num [coeffY,q,g]; linarith [tr.2.1])
    have hA := CoreContact.outer_primary_order hc ht hB
    have hp := mul_le_mul_of_nonpos_left hA hX
    have hq := mul_le_mul_of_nonneg_left hB hY
    linarith

/-- All four original negative-core/negative-outer source-secondary
families, including the full corner, side and weak contact cases. -/
theorem original_cost (r : Row) {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) :
    (449/500:ℝ)<φ+c r-g r*b-p r*A+q r*B := by
  have hx : φ∈Icc start (7/10) :=
    ⟨(original_angle hs ht hφ hm).le,(abs_le.mp hφ).2⟩
  have tr := positive_trig (show φ∈Icc 0 (7/10) from
    ⟨by linarith [hx.1,(show (0:ℝ)<start by norm_num [start])],hx.2⟩)
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  have hm' : (1+Real.sin φ+Real.cos φ)/2≤-b+A*Real.sin φ+B*Real.cos φ := by
    norm_num [forwardMargin] at hm
    rw [hw] at hm
    linarith
  have hsupport := original_support r hs ht hx hm'
  have hmargin := mul_le_mul_of_nonneg_left hm' (coefficient_bounds r).1.le
  have hcost : min (H r φ) (G r φ)≤φ+c r-g r*b-p r*A+q r*B := by
    dsimp [base,coeffX,coeffY] at hsupport
    nlinarith only [hsupport,hmargin]
  exact (lt_min (H_lower r hx) (G_lower r hx)).trans_le hcost

end SquaresInCircles.Eight.TableFree.ShortMixedZero.NegativeContact
