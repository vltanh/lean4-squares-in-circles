module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerCriticalParameters

/-!
# The actual curved exit of the reverse critical contact

The exit is where the recovered primary height equals the free
coordinate plus one.  Its marker is strictly decreasing on the whole
continued target interval, so every physical critical point occurs
before this aligned exit.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open LowerInverse LowerEnvelope

def exitMarker (B : ℝ) : ℝ := height B-B-3/2

lemma exitMarker_hasDerivAt {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    HasDerivAt exitMarker (-D B-1) B :=
  ((height_hasDerivAt hB).sub (hasDerivAt_id B)).sub_const (3/2)

lemma exitMarker_strictAnti : StrictAntiOn exitMarker (Icc (3/100) (3/20)) := by
  have hm : StrictMonoOn (fun B => -exitMarker B) (Icc (3/100) (3/20)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    · intro B hB
      exact (exitMarker_hasDerivAt hB).neg.continuousAt.continuousWithinAt
    · intro B hB
      exact (exitMarker_hasDerivAt (interior_subset hB)).neg.hasDerivWithinAt
    · intro B hB
      have hh := D_positive (mem_short (interior_subset hB))
      linarith
  intro B hB C hC hBC
  have hh := hm hB hC hBC
  linarith

lemma half_before_end : halfPoint<endPoint := by
  by_contra hn
  have hh := source_monotone end_domain.1 half_domain.1 (le_of_not_gt hn)
  rw [end_source,half_source] at hh
  norm_num at hh

lemma half_marker_positive : 0<exitMarker halfPoint := by
  have hu := (LowerGeometry.middle_U (by norm_num : (1/2:ℝ)∈Icc (2/5) (1/2))).1
  have he : height halfPoint=U (1/2) := by rw [←source_U half_domain.1,half_source]
  dsimp [exitMarker]
  rw [he]
  linarith [half_domain.1.2]

lemma end_marker_negative : exitMarker endPoint<0 := by
  by_contra hn
  have hm : 0≤exitMarker endPoint := le_of_not_gt hn
  have hu := source_U end_domain.1
  have hd : LowerContact.Domain endPoint (source endPoint) := by
    refine ⟨mem_outer end_domain.1,source_domain end_domain,?_⟩
    dsimp [exitMarker] at hm
    dsimp [U] at hu
    linarith
  have hv := LowerContact.physical_speed hd
  change W (source endPoint)≤LowerInverse.speed (z endPoint) (source endPoint) at hv
  rw [critical_speed end_domain.1,end_source] at hv
  norm_num [W] at hv
  have hp := p_positive (mem_outer end_domain.1)
  have hpl := (label_bounds end_domain.1).1
  have hh := (le_div_iff₀ hp).mp hv
  linarith

lemma exists_exit : ∃ B, B∈Icc halfPoint endPoint ∧ exitMarker B=0 := by
  have hdom {B : ℝ} (hB : B∈Icc halfPoint endPoint) : Domain B :=
    domain_between half_domain end_domain hB
  have hc : ContinuousOn (fun B => -exitMarker B) (Icc halfPoint endPoint) :=
    fun B hB => (exitMarker_hasDerivAt (hdom hB).1).neg.continuousAt.continuousWithinAt
  obtain ⟨B,hB,he⟩ := intermediate_value_Icc half_before_end.le hc
    (show (0:ℝ)∈Icc (-exitMarker halfPoint) (-exitMarker endPoint) from
      ⟨by linarith [half_marker_positive],by linarith [end_marker_negative]⟩)
  exact ⟨B,hB,by linarith⟩

def exitPoint : ℝ := Classical.choose exists_exit
lemma exit_mem : exitPoint∈Icc halfPoint endPoint := (Classical.choose_spec exists_exit).1
lemma exit_zero : exitMarker exitPoint=0 := (Classical.choose_spec exists_exit).2
lemma exit_domain : Domain exitPoint := domain_between half_domain end_domain exit_mem

lemma physical_before_exit {B : ℝ} (hB : Domain B) (hp : B≤arc (source B)-1) : B≤exitPoint := by
  have hm : 0≤exitMarker B := by
    have hu := source_U hB.1
    dsimp [U] at hu
    dsimp [exitMarker]
    linarith
  by_contra hn
  have hh := exitMarker_strictAnti exit_domain.1 hB.1 (lt_of_not_ge hn)
  rw [exit_zero] at hh
  linarith

lemma exit_aligned : exitPoint=arc (source exitPoint)-1 := by
  have hu := source_U exit_domain.1
  have he := exit_zero
  dsimp [U] at hu
  dsimp [exitMarker] at he
  linarith

lemma exit_value : (44889/50000:ℝ)<cost exitPoint := by
  have hd : LowerContact.Domain exitPoint (source exitPoint) :=
    ⟨mem_outer exit_domain.1,source_domain exit_domain,exit_aligned.le⟩
  exact LowerContact.aligned_lower true hd exit_aligned

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
