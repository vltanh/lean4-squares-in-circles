module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositePositiveTargetDiagonal
public import SquaresInCircles.Eight.TableFree.ShortMixedZeroNegativeContact

/-!
# The actual source-zero boundary of a positive outer contact

Uncompiled transcription of the second boundary in Section 3.2. The
already written mixed-zero circle formulas are reused as formulas for
the very same target point. The source coordinate is zero, not a moved
core square. The original circle and contact equations identify the
rotated coordinates uniquely, including the diagonal entry.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Zero
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)

abbrev start := ShortMixedZero.NegativeContact.start
abbrev horizontal := ShortMixedZero.NegativeContact.U
abbrev vertical := ShortMixedZero.NegativeContact.V
abbrev factor := ShortMixedZero.NegativeContact.speed
abbrev factorD := ShortMixedZero.NegativeContact.speedD

def height (x : ℝ) : ℝ := vertical x-1/2

def Physical (x : ℝ) : Prop := x∈Icc start (7/10) ∧ height x≤outerDiagonal

lemma angle_mem {x : ℝ} (hx : x∈Icc start (7/10)) : x∈Icc 0 (7/10) :=
  ⟨by linarith [hx.1,show (0:ℝ)<start by norm_num [start,ShortMixedZero.NegativeContact.start]],hx.2⟩

lemma state {x : ℝ} (hx : Physical x) : OuterState (horizontal x-1/2) (height x) := by
  have hcoord := ShortMixedZero.NegativeContact.coordinates hx.1
  have hc := ShortMixedZero.NegativeContact.circle hx.1
  have hd := diagonal_circle
  have hV : vertical x≤outerDiagonal+1/2 := by
    have h2 := hx.2
    dsimp only [height] at h2
    linarith
  have hdiag0 : 0<outerDiagonal+1/2 := by linarith [outer_endpoint_bounds.2.2.1]
  have hVsq := pow_le_pow_left₀ (by linarith [hcoord.2.2.1] : 0≤vertical x) hV 2
  have horder : vertical x≤horizontal x := by
    nlinarith [hcoord.1,hcoord.2.2.1]
  refine ⟨?_,?_,?_⟩
  · dsimp only [height]
    linarith [hcoord.2.2.1]
  · dsimp only [height]
    linarith
  · dsimp only [height]
    rw [sub_add_cancel,sub_add_cancel]
    exact hc

lemma target_mem {x : ℝ} (hx : Physical x) : height x∈Icc 0 outerDiagonal :=
  ⟨(state hx).1,hx.2⟩

lemma original_arc {x : ℝ} (hx : Physical x) : arc (height x)=horizontal x-1/2 :=
  (ShortOuterOne.SameContact.actual_arc (state hx)).1

lemma contact {x : ℝ} (hx : Physical x) : plus (height x) x=0 := by
  have he := ShortMixedZero.NegativeContact.contact_equation x
  dsimp [plus,SecondWord.OppositeZero.plus]
  rw [original_arc hx]
  dsimp [height]
  nlinarith

lemma domain {x : ℝ} (hx : Physical x) : PlusDomain (height x) x := by
  refine ⟨target_mem hx,angle_mem hx.1,?_⟩
  have hz : SecondWord.OppositeZero.plus (height x) x=0 := contact hx
  show SecondWord.OppositeZero.plus (height x) x∈Icc 0 outerDiagonal
  rw [hz]
  exact outer_zero_mem

lemma original_angle {B x : ℝ} (hd : PlusDomain B x) (hz : plus B x=0) : start<x := by
  have tr := positive_trig hd.2.1
  have ht := ShortOuterOne.SameContact.arc_state hd.1
  have hproj := outer_diagonal_upper ht tr.2.2.1
    (show Real.sin x≤Real.cos x by linarith [tr.1,tr.2.2.2.1])
  have he : (1+Real.sin x+Real.cos x)/2=arc B*Real.sin x+B*Real.cos x := by
    dsimp [plus,SecondWord.OppositeZero.plus] at hz
    linarith
  have hcut : 0≤ShortMixedZero.NegativeContact.cut x := by
    dsimp [ShortMixedZero.NegativeContact.cut,ShortMixedZero.NegativeContact.m]
    nlinarith
  by_contra! hx
  have hm := ShortMixedZero.NegativeContact.m_monotone hd.2.1
    (by norm_num [start,ShortMixedZero.NegativeContact.start]) hx
  have hh := mul_le_mul_of_nonneg_left hm
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1])
  have hs := ShortMixedZero.NegativeContact.cut_start_neg
  dsimp [ShortMixedZero.NegativeContact.cut] at hcut hs
  linarith

lemma original_coordinates {B x : ℝ} (hd : PlusDomain B x) (hz : plus B x=0) :
    Physical x ∧ height x=B := by
  have hx : x∈Icc start (7/10) := ⟨(original_angle hd hz).le,hd.2.1.2⟩
  have ht := ShortOuterOne.SameContact.arc_state hd.1
  have tr := positive_trig hd.2.1
  have hZ : ShortMixedZero.NegativeContact.Z x=U B*Real.sin x+W B*Real.cos x := by
    dsimp [plus,SecondWord.OppositeZero.plus] at hz
    dsimp [ShortMixedZero.NegativeContact.Z,ShortMixedZero.NegativeContact.m,U,W]
    linarith
  have horth : 0<U B*Real.cos x-W B*Real.sin x := by
    have h1 := mul_pos (U_positive (outer_domain hd.1))
      (show 0<Real.cos x-Real.sin x by linarith [tr.1,tr.2.2.2.1])
    have h2 := mul_nonneg (show 0≤U B-W B by dsimp [U,W]; linarith [ht.2.1]) tr.2.2.1
    nlinarith
  have hY : ShortMixedZero.NegativeContact.Y x=U B*Real.cos x-W B*Real.sin x := by
    have hc := UW_circle (outer_domain hd.1)
    have hr := ShortMixedZero.NegativeContact.circle_base hx
    have he : (U B*Real.cos x-W B*Real.sin x)^2+(ShortMixedZero.NegativeContact.Z x)^2=Q0 := by
      rw [hZ]
      linear_combination hc+((U B)^2+(W B)^2)*(Real.sin_sq_add_cos_sq x)
    exact (sq_eq_sq₀ (ShortMixedZero.NegativeContact.Y_pos hx).le horth.le).mp (by linarith)
  have hheight : height x=B := by
    dsimp only [height,vertical,ShortMixedZero.NegativeContact.V]
    rw [hZ,hY]
    dsimp only [W]
    linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)
  exact ⟨⟨hx,by rw [hheight]; exact hd.1.2⟩,hheight⟩

lemma height_monotone : AntitoneOn height (Icc start (7/10)) := by
  intro x hx y hy hxy
  exact sub_le_sub_right (ShortMixedZero.NegativeContact.V_antitone hx hy hxy) (1/2)

lemma initial_height : outerDiagonal<height start := by
  by_contra! hh
  have hphysical : Physical start := ⟨by norm_num [start,ShortMixedZero.NegativeContact.start],hh⟩
  have ht := state hphysical
  have tr := positive_trig (angle_mem hphysical.1)
  have hproj := outer_diagonal_upper ht tr.2.2.1
    (show Real.sin start≤Real.cos start by linarith [tr.1,tr.2.2.2.1])
  have hcontact := ShortMixedZero.NegativeContact.contact_equation start
  have hcut : 0≤ShortMixedZero.NegativeContact.cut start := by
    dsimp [ShortMixedZero.NegativeContact.cut,ShortMixedZero.NegativeContact.m,height] at *
    nlinarith
  exact (not_lt_of_ge hcut) ShortMixedZero.NegativeContact.cut_start_neg

lemma entry {x : ℝ} (hx : Physical x) :
    ∃e, e∈Icc start x ∧ height e=outerDiagonal ∧
      ∀y∈Icc e (7/10), Physical y := by
  have hc : ContinuousOn height (Icc start x) := fun y hy =>
    ((ShortMixedZero.NegativeContact.V_hasDerivAt ⟨hy.1,hy.2.trans hx.1.2⟩).sub_const
      (1/2)).continuousAt.continuousWithinAt
  obtain ⟨e,he,heq'⟩ := intermediate_value_Icc' hx.1.1 hc
    (show outerDiagonal∈Icc (height x) (height start) from ⟨hx.2,initial_height.le⟩)
  refine ⟨e,he,heq',?_⟩
  intro y hy
  have hei : e∈Icc start (7/10) := ⟨he.1,he.2.trans hx.1.2⟩
  have hyi : y∈Icc start (7/10) := ⟨he.1.trans hy.1,hy.2⟩
  have hm := height_monotone hei hyi hy.1
  rw [heq'] at hm
  exact ⟨hyi,hm⟩

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Zero
