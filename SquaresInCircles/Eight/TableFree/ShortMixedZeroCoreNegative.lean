module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroCoreScalars

/-!
# The original six core-source negative families

The original weak separating inequality places the actual outer target
after its exact contact. A linear functional on this subarc is bounded
by its contact and diagonal values. Positive primary coefficient uses
circle concavity; the two remaining signs use direct monotonicity and
the diagonal tangent. No replacement feasibility is assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero

namespace CoreContact

open CommonQuarter CorePairGeometry Arithmetic

def coeffX (r : Row) (x : ℝ) : ℝ := g r*Real.sin x-p r
def coeffY (r : Row) (x : ℝ) : ℝ := q r-g r*Real.cos x
def base (r : Row) (x : ℝ) : ℝ := -x+c r+g r*(1+Real.sin x+Real.cos x)/2

lemma contact_value (r : Row) (x : ℝ) :
    H r x=base r x+coeffX r x*(U x-1/2)+coeffY r x*(V x-1/2) := by
  have hh := congrArg (fun z : ℝ => g r*z) (contact_equation x)
  dsimp [H,base,coeffX,coeffY]
  nlinarith only [hh]

lemma diagonal_value (r : Row) (x : ℝ) :
    G r x=base r x+(coeffX r x+coeffY r x)*outerDiagonal := by
  dsimp [G,base,coeffX,coeffY]
  ring

lemma outer_subarc_lower {a b A B X Y m : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hb : b≤B)
    (hX : 0≤X) (hl : m≤X*a+Y*b) (hu : m≤(X+Y)*outerDiagonal) :
    m≤X*A+Y*B := by
  have hB := (outer_bounds ht).2.2.2.1
  have hh := Arithmetic.circle_endpoints_lower (v := -1/2) (ρ := CommonQuarter.radius)
    (X := X) (Y := Y) (l := b) (u := outerDiagonal) hX
    (fun z hz => outer_radicand_pos ⟨hs.1.trans hz.1,hz.2⟩) ⟨hb,hB⟩
    (by simpa [← outer_branch hs] using hl)
    (by rw [outer_branch_endpoints.2]; linarith)
  simpa [← outer_branch ht] using hh

lemma outer_primary_order {a b A B : ℝ} (hs : OuterState a b)
    (ht : OuterState A B) (hb : b≤B) : A≤a := by
  have hsq := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hs.1])
    (show b+1/2≤B+1/2 by linarith) 2
  by_contra! hbad
  have hp := mul_pos (show 0<(A+1/2)-(a+1/2) by linarith)
    (show 0<(A+1/2)+(a+1/2) by linarith [hs.1,hs.2.1,ht.1,ht.2.1])
  nlinarith [hs.2.2,ht.2.2]

lemma contact_or_diagonal (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 cap)
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    min (H r x) (G r x)≤base r x+coeffX r x*A+coeffY r x*B := by
  obtain ⟨hc,hB⟩ := original_contact hs ht hx hm
  have hHv := (min_le_left (H r x) (G r x)).trans_eq (contact_value r x)
  have hGv := (min_le_right (H r x) (G r x)).trans_eq (diagonal_value r x)
  by_cases hX : 0≤coeffX r x
  · have hh := outer_subarc_lower hc ht hB hX
      (m := min (H r x) (G r x)-base r x) (Y := coeffY r x)
      (by linarith) (by linarith)
    linarith
  · have hX' : coeffX r x≤0 := (lt_of_not_ge hX).le
    have htr := trig_bounds hx
    have hr : r=3 ∨ r=5 := by
      fin_cases r <;> norm_num [coeffX,p,g] at hX ⊢ <;> nlinarith [htr.1]
    rcases hr with rfl | rfl
    · have hA := outer_primary_order hc ht hB
      have hY : 0≤coeffY 3 x := by
        norm_num [coeffY,q,g]
        linarith [htr.2.2.2]
      have h₁ := mul_le_mul_of_nonpos_left hA hX'
      have h₂ := mul_le_mul_of_nonneg_left hB hY
      linarith
    · have hsum := (positive_trig
        (show x∈Icc 0 (7/10) from ⟨hx.1,hx.2.trans (by norm_num [cap])⟩)).2.2.2.2.2
      have hder : coeffY 5 x-coeffX 5 x≤0 := by
        norm_num [coeffX,coeffY,p,q,g]
        linarith
      have hh := WrongWordCircleSupport.outer_diagonal_lower ht hX' hder
      linarith

theorem original_cost_lower (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 cap)
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    min (H r x) (G r x)≤-x+c r+g r*b-p r*A+q r*B := by
  have hh := contact_or_diagonal r hs ht hx hm
  have hp := mul_le_mul_of_nonneg_left hm (coefficient_bounds r).1.le
  dsimp [base,coeffX,coeffY] at hh
  nlinarith only [hh,hp]

end CoreContact

open CommonQuarter CorePairGeometry

/-- All six complementary opposite-sign families over their complete
negative angle half, including the original weak contact endpoints. -/
theorem opposite_core_negative (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)< -x+c r+g r*b-p r*A+q r*B := by
  have hx' : x∈Icc 0 CoreContact.cap := ⟨hx.1,(CoreContact.original_angle_cut hs ht hx hm).le⟩
  exact (lt_min (CoreContact.H_lower r hx') (CoreContact.G_lower r hx')).trans_le
    (CoreContact.original_cost_lower r hs ht hx' hm)

end SquaresInCircles.Eight.TableFree.ShortMixedZero
