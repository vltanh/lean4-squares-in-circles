module

public import SquaresInCircles.Eight.TableFree.SourceAwarePreprocessing
public import SquaresInCircles.Eight.TableFree.BoundaryPreprocessing

/-!
# Actual boundary descendants with their original primary sources

Uncompiled reconstruction.  The source records are attached to the actual
same-radius boundary construction.  Already feasible hard axes leave the
corresponding point and frame literally fixed.  If a missing hard axis
becomes feasible, its original anchor total or strict neighboring contact
is retained on the actual composite cycle, including after the other
intermediate point is moved.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate

namespace SignedCycle.BoundaryInput

theorem g_source_output {q : ℝ} (I : BoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    Nonempty (GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A)) := by
  by_cases hhard : I.cycle.Feasible G 0
  · exact ⟨{
      output := I.hardG hhard
      fixed_if_hard := fun _ => ⟨rfl,rfl⟩
      source_obstruction := fun h _ => False.elim (h (I.hardG hhard).GA) }⟩
  have hprimary : I.cycle.Feasible G 1 := by
    have howner : I.witnesses.owner G=0 ∨ I.witnesses.owner G=1 := by
      simpa [normalOwners,G] using I.witnesses.allowed G
    rcases howner with he | he
    · exact (hhard (by simpa [he] using I.witnesses.feasible G)).elim
    · simpa [he] using I.witnesses.feasible G
  exact preprocess_G_pair_with_source hqL hqU (I.gPair hprimary)

theorem t_source_output {q : ℝ} (I : BoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    Nonempty (TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) := by
  by_cases hhard : I.cycle.Feasible B 2
  · exact ⟨{
      output := I.hardT hhard
      fixed_if_hard := fun _ => ⟨rfl,rfl⟩
      source_obstruction := fun h _ => False.elim (h (I.hardT hhard).BT) }⟩
  have hprimary : I.cycle.Feasible B 3 := by
    have howner : I.witnesses.owner B=2 ∨ I.witnesses.owner B=3 := by
      simpa [normalOwners,B] using I.witnesses.allowed B
    rcases howner with he | he
    · exact (hhard (by simpa [he] using I.witnesses.feasible B)).elim
    · simpa [he] using I.witnesses.feasible B
  exact preprocess_T_pair_with_source hqL hqU (I.tPair hprimary)

/-- Both original primary-source records accompany the actual ordered
boundary descendant.  All five anchors and both signed variations retain
their original values or bounds. -/
theorem pair_source_preprocessing {q : ℝ} (I : BoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    ∃ (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
        (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
      (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
        (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
      (J : BoundaryInput q),
      J=I.pairDescendant hqU SG.output ST.output ∧
      AnchorsUnchanged I.cycle J.cycle ∧
      positiveVariation J.cycle.theta≤positiveVariation I.cycle.theta ∧
      negativeVariation J.cycle.theta≤negativeVariation I.cycle.theta := by
  obtain ⟨SG⟩ := I.g_source_output hqL hqU
  obtain ⟨ST⟩ := I.t_source_output hqL hqU
  exact ⟨SG,ST,I.pairDescendant hqU SG.output ST.output,rfl,
    I.pairDescendant_anchors hqU SG.output ST.output,
    I.pairDescendant_variations hqU SG.output ST.output⟩

/-- Inserting the opposite endpoint does not erase strict HG slack. -/
theorem pairDescendant_g_source_obstruction {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hnot : ¬I.cycle.Feasible G 0)
    (hhard : (I.pairDescendant hq SG.output ST.output).cycle.Feasible G 0) :
    0<I.cycle.theta A-I.cycle.theta H ∨
      0<(I.pairDescendant hq SG.output ST.output).cycle.slack H SG.output.hgOwner := by
  have hnot' : ¬quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    intro h
    apply hnot
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible]
      using sub_nonneg.mpr h
  have hhard' : quarterFeasible SG.output.point (I.cycle.point A)
      (I.cycle.theta A-SG.output.theta) 0 := by
    change 0≤(I.pairDescendant hq SG.output ST.output).cycle.slack G 0 at hhard
    rw [pairDescendant_cycle] at hhard
    simpa [slack,edge,replacePoint,word,delta,next,G,A,T,quarterFeasible]
      using sub_nonneg.mp hhard
  rcases SG.source_obstruction hnot' hhard' with htotal | hstrict
  · exact Or.inl htotal
  · right
    rw [pairDescendant_cycle]
    simpa [slack,edge,replacePoint,word,delta,next,H,G,T]
      using sub_pos.mpr hstrict

/-- The TD source obstruction is proved on the same actual composite
cycle, with the original TD owner retained in the source record. -/
theorem pairDescendant_t_source_obstruction {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hnot : ¬I.cycle.Feasible B 2)
    (hhard : (I.pairDescendant hq SG.output ST.output).cycle.Feasible B 2) :
    0<I.cycle.theta D-I.cycle.theta B ∨
      0<(I.pairDescendant hq SG.output ST.output).cycle.slack T ST.output.tdOwner := by
  have hnot' : ¬quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta T-I.cycle.theta B) 2 := by
    intro h
    apply hnot
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible]
      using sub_nonneg.mpr h
  have hhard' : quarterFeasible (I.cycle.point B) ST.output.point
      (ST.output.theta-I.cycle.theta B) 2 := by
    change 0≤(I.pairDescendant hq SG.output ST.output).cycle.slack B 2 at hhard
    rw [pairDescendant_cycle] at hhard
    simpa [slack,edge,replacePoint,word,delta,next,B,T,G,quarterFeasible]
      using sub_nonneg.mp hhard
  rcases ST.source_obstruction hnot' hhard' with htotal | hstrict
  · exact Or.inl htotal
  · right
    rw [pairDescendant_cycle]
    simpa [slack,edge,replacePoint,word,delta,next,T,D,G]
      using sub_pos.mpr hstrict

/-- Already hard sources remain the literal original intermediates after
the two independent transports have been composed. -/
theorem pairDescendant_fixed_sources {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :
    (I.cycle.Feasible G 0 →
      (I.pairDescendant hq SG.output ST.output).cycle.point G=I.cycle.point G ∧
      (I.pairDescendant hq SG.output ST.output).cycle.theta G=I.cycle.theta G) ∧
    (I.cycle.Feasible B 2 →
      (I.pairDescendant hq SG.output ST.output).cycle.point T=I.cycle.point T ∧
      (I.pairDescendant hq SG.output ST.output).cycle.theta T=I.cycle.theta T) := by
  constructor
  · intro h
    change 0≤I.cycle.slack G 0 at h
    have h' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta G) 0 := by
      simpa [slack,edge,word,delta,next,G,A,quarterFeasible] using sub_nonneg.mp h
    obtain ⟨hp,ht⟩ := SG.fixed_if_hard h'
    rw [pairDescendant_cycle]
    simpa [replacePoint,G,T] using And.intro hp ht
  · intro h
    change 0≤I.cycle.slack B 2 at h
    have h' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
        (I.cycle.theta T-I.cycle.theta B) 2 := by
      simpa [slack,edge,word,delta,next,B,T,quarterFeasible] using sub_nonneg.mp h
    obtain ⟨hp,ht⟩ := ST.fixed_if_hard h'
    rw [pairDescendant_cycle]
    simpa [replacePoint,G,T] using And.intro hp ht

end SignedCycle.BoundaryInput

namespace SignedCycle.NormalizedBoundaryInput

theorem g_source_output {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    Nonempty (GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A)) :=
  I.toBoundaryInput.g_source_output hqL hqU

theorem t_source_output {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    Nonempty (TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :=
  I.toBoundaryInput.t_source_output hqL hqU

/-- E is the original signed point in the normalized descendant as well.
The source implications concern the actual hard primaries of that cycle,
not a choice of owner made for a different point. -/
theorem pair_source_preprocessing {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) :
    ∃ (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
        (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
      (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
        (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
      (J : NormalizedBoundaryInput q),
      J=I.pairDescendant hqU SG.output ST.output ∧
      AnchorsUnchanged I.cycle J.cycle ∧
      positiveVariation J.cycle.theta≤positiveVariation I.cycle.theta ∧
      negativeVariation J.cycle.theta≤negativeVariation I.cycle.theta := by
  obtain ⟨SG⟩ := I.g_source_output hqL hqU
  obtain ⟨ST⟩ := I.t_source_output hqL hqU
  exact ⟨SG,ST,I.pairDescendant hqU SG.output ST.output,rfl,
    I.toBoundaryInput.pairDescendant_anchors hqU SG.output ST.output,
    I.toBoundaryInput.pairDescendant_variations hqU SG.output ST.output⟩

end SignedCycle.NormalizedBoundaryInput
end SquaresInCircles.Eight.TableFree
