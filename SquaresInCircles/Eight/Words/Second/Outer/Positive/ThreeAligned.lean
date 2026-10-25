module

public import SquaresInCircles.Eight.Words.Second.Outer.ConcaveSlope
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeAlignedReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeFirstContact

/-!
# Eight squares: the full aligned positive edge-three minimum

Below target primary coordinate one, the first contact has a concave
first derivative which is positive at its zero-source endpoint.  Its
minimum is therefore one of the two actual physical endpoints.  Above
primary coordinate one, ordinary label monotonicity gives the zero
endpoint directly.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma quarter_lower : Lower (Real.pi/2) := by
  show lowerAngle≤Real.pi/2 ∧ Real.pi/2≤Real.pi/2
  exact ⟨by dsimp only [lowerAngle]; linarith,le_rfl⟩

lemma aligned_contact_domain {B : ℝ} (hB : B∈Icc zeroTarget outerDiagonal) :
    FirstContact.Domain B (Real.pi/2) := by
  have hBout : B∈Icc 0 outerDiagonal := ⟨zeroTarget_mem.1.trans hB.1,hB.2⟩
  have hu := ShortOuterOne.SameContact.arc_antitone (outer_domain zeroTarget_mem)
    (outer_domain hBout) hB.1
  rw [zeroTarget_arc] at hu
  have hl := (CommonQuarter.outer_bounds (ShortOuterOne.SameContact.arc_state hBout)).1
  refine ⟨hBout,?_,quarter_lower⟩
  rw [FirstContact.source_at_quarter]
  constructor <;> linarith [fine_outer_endpoint_bounds.2]

lemma aligned_contact_first : 0<FirstContact.first zeroTarget (Real.pi/2) := by
  have he : FirstContact.source zeroTarget (Real.pi/2)=0 := by
    rw [FirstContact.source_at_quarter,zeroTarget_arc]
    norm_num
  have hp := mul_lt_mul V_zero_first_lower zeroTarget_ratio.le
    (by norm_num : (0:ℝ)<43/50)
    (by linarith [V_zero_first_lower] : 0≤VLabel.d1 0)
  dsimp [FirstContact.first]
  rw [he]
  simp only [FirstContact.sourceFirst,Real.sin_pi_div_two,Real.cos_pi_div_two,
    mul_one,add_zero]
  norm_num at hp
  linarith [zeroTarget_labels.2.1]

theorem aligned_contact_lower {B : ℝ} (hB : B∈Icc zeroTarget outerDiagonal) :
    (44889/50000:ℝ)<FirstContact.cost B (Real.pi/2) := by
  have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos hB
    (fun t ht => FirstContact.cost_hasDerivAt (aligned_contact_domain ht))
    (fun t ht => FirstContact.first_hasDerivAt (aligned_contact_domain ht))
    (fun t ht => FirstContact.second_hasDerivAt (aligned_contact_domain ht))
    (fun t ht => (FirstContact.third_negative (aligned_contact_domain ht)).le)
    aligned_contact_first
  have hz : (44889/50000:ℝ)<FirstContact.cost zeroTarget (Real.pi/2) := by
    have he : FirstContact.source zeroTarget (Real.pi/2)=0 := by
      rw [FirstContact.source_at_quarter,zeroTarget_arc]
      norm_num
    dsimp [FirstContact.cost]
    rw [he]
    have hs := zero_aligned_value
    dsimp [value] at hs
    linarith
  have hd : (44889/50000:ℝ)<FirstContact.cost outerDiagonal (Real.pi/2) := by
    have he : FirstContact.source outerDiagonal (Real.pi/2)=alignedSource := by
      rw [FirstContact.source_at_quarter,ShortOuterOne.SameContact.arc_diagonal]
      rfl
    dsimp [FirstContact.cost]
    rw [he]
    exact diagonal_aligned_value
  exact (lt_min hz hd).trans_le hh

lemma aligned_inactive_target {A B : ℝ} (ht : OuterState A B) (hA : 1≤A) :
    B≤zeroTarget := by
  have hh := ShortOuterOne.SameContact.arc_antitone (primary_domain primary_one_mem)
    (primary_domain (NegativeTwo.primary_mem ht)) hA
  rw [(ShortOuterOne.SameContact.actual_arc ht).2] at hh
  exact hh

lemma aligned_active_target {A B : ℝ} (ht : OuterState A B) (hA : A≤1) :
    zeroTarget≤B := by
  have hh := ShortOuterOne.SameContact.arc_antitone
    (primary_domain (NegativeTwo.primary_mem ht)) (primary_domain primary_one_mem) hA
  rw [(ShortOuterOne.SameContact.actual_arc ht).2] at hh
  exact hh

theorem original_aligned {a b A B : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (halign : 1≤b+A) :
    (44889/50000:ℝ)<value b B (Real.pi/2) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  by_cases hA : 1≤A
  · have htarget := L_monotone hB zeroTarget_mem (aligned_inactive_target ht hA)
    have hsource := V_monotone outer_zero_mem hb hb.1
    have hbase := zero_aligned_value
    dsimp [value] at *
    linarith
  · have hinterval : B∈Icc zeroTarget outerDiagonal :=
      ⟨aligned_active_target ht (by linarith),hB.2⟩
    have hdom := aligned_contact_domain hinterval
    have he : FirstContact.source B (Real.pi/2)=1-A := by
      rw [FirstContact.source_at_quarter,(ShortOuterOne.SameContact.actual_arc ht).1]
    have hsource := V_monotone hdom.2.1 hb
      (show FirstContact.source B (Real.pi/2)≤b by rw [he]; linarith)
    have hbase := aligned_contact_lower hinterval
    dsimp [FirstContact.cost,value] at *
    linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree
