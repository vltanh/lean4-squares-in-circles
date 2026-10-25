module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerCriticalCalculus
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeWeightedMinimum

/-!
# Existence and location of the three critical-curve references

The scalar equation is solved by the intermediate value theorem on
the one complete target interval.  The chosen parameter is never
differentiated: all calculus belongs to the explicit source radical.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open LowerInverse LowerEnvelope

lemma q_monotone : MonotoneOn (fun b => q (U b)) (Icc 0 outerDiagonal) := by
  intro b hb B hB hle
  have hh := ShortOuterOne.SameContact.arc_antitone (outer_domain hb) (outer_domain hB) hle
  dsimp [q,NegativeTwo.Inverse.q,U]
  linarith

lemma exists_parameter {b : ℝ} (hb : b∈Icc 0 (3/5)) :
    ∃ B, B∈Icc (3/100) (3/20) ∧ S B=q (U b) := by
  have hbf := LowerGeometry.full_domain ⟨hb.1,by linarith [hb.2]⟩
  have hleft := q_monotone outer_zero_mem hbf hb.1
  have hright := q_monotone hbf
    (LowerGeometry.full_domain (by norm_num : (3/5:ℝ)∈Icc 0 (4/5))) hb.2
  have hc : ContinuousOn S (Icc (3/100) (3/20)) :=
    fun B hB => (S_hasDerivAt (mem_outer hB)).continuousAt.continuousWithinAt
  have he : q (U b)∈Icc (S (3/100)) (S (3/20)) :=
    ⟨(continuation_endpoints.1.trans_le hleft).le,(hright.trans_lt continuation_endpoints.2).le⟩
  obtain ⟨B,hB,hval⟩ := intermediate_value_Icc (by norm_num : (3/100:ℝ)≤3/20) hc he
  exact ⟨B,hB,hval⟩

def parameter (b : ℝ) (hb : b∈Icc 0 (3/5)) : ℝ := Classical.choose (exists_parameter hb)

lemma parameter_mem {b : ℝ} (hb : b∈Icc 0 (3/5)) : parameter b hb∈Icc (3/100) (3/20) :=
  (Classical.choose_spec (exists_parameter hb)).1
lemma parameter_equation {b : ℝ} (hb : b∈Icc 0 (3/5)) : S (parameter b hb)=q (U b) :=
  (Classical.choose_spec (exists_parameter hb)).2
lemma source_parameter {b : ℝ} (hb : b∈Icc 0 (3/5)) : source (parameter b hb)=b :=
  source_eq_of_S (parameter_mem hb) hb (parameter_equation hb)
lemma parameter_domain {b : ℝ} (hb : b∈Icc 0 (3/5)) : Domain (parameter b hb) :=
  ⟨parameter_mem hb,by rw [source_parameter hb]; exact hb⟩

lemma parameter_bracket {b l u : ℝ} (hb : b∈Icc 0 (3/5))
    (hl : l∈Icc (3/100) (3/20)) (hu : u∈Icc (3/100) (3/20))
    (hleft : S l<q (U b)) (hright : q (U b)<S u) :
    l<parameter b hb ∧ parameter b hb<u := by
  have hP := parameter_mem hb
  have he := parameter_equation hb
  constructor
  · by_contra hn
    have hm := S_monotone (mem_short hP) (mem_short hl) (le_of_not_gt hn)
    rw [he] at hm
    linarith
  · by_contra hn
    have hm := S_monotone (mem_short hu) (mem_short hP) (le_of_not_gt hn)
    rw [he] at hm
    linarith

def halfPoint : ℝ := parameter (1/2) (by norm_num)
def referencePoint : ℝ := parameter (99/200) (by norm_num)
def endPoint : ℝ := parameter (3/5) (by norm_num)

lemma half_domain : Domain halfPoint := parameter_domain (by norm_num)
lemma reference_domain : Domain referencePoint := parameter_domain (by norm_num)
lemma end_domain : Domain endPoint := parameter_domain (by norm_num)
lemma half_source : source halfPoint=(1/2:ℝ) := source_parameter (by norm_num)
lemma reference_source : source referencePoint=(99/200:ℝ) := source_parameter (by norm_num)
lemma end_source : source endPoint=(3/5:ℝ) := source_parameter (by norm_num)

lemma below_half_iff {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    B≤halfPoint ↔ source B≤1/2 := by
  constructor
  · intro hh
    have hm := source_monotone hB half_domain.1 hh
    rwa [half_source] at hm
  · intro hh
    by_contra hn
    have hm := source_strictMono half_domain.1 hB (lt_of_not_ge hn)
    rw [half_source] at hm
    linarith

lemma half_below_iff {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    halfPoint≤B ↔ 1/2≤ source B := by
  constructor
  · intro hh
    have hm := source_monotone half_domain.1 hB hh
    rwa [half_source] at hm
  · intro hh
    by_contra hn
    have hm := source_strictMono hB half_domain.1 (lt_of_not_ge hn)
    rw [half_source] at hm
    linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
