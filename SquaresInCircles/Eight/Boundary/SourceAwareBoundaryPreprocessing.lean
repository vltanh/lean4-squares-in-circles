module

public import SquaresInCircles.Eight.Boundary.SourceAwarePreprocessing
public import SquaresInCircles.Eight.Boundary.Preprocessing

/-!
# Eight squares: the pair moves with their sources

A boundary input at a level `qLow ≤ q ≤ qCap` has pair moves of G and of T that keep track of
their source (`BoundaryInput.g_source_output`, `t_source_output`). The move of G leaves its point
and frame unchanged when G–A is already separated along the axis zero; if that axis becomes
feasible only after the move, then `θA - θH > 0` or the contact H–G of the output is strict. The
move of T behaves in the same way, with B–T, the axis two, `θD - θB` and the contact T–D. On the
cycle after both moves (`pairDescendant`) these alternatives still hold, since the move of T
leaves H–G unchanged and the move of G leaves T–D unchanged (`pairDescendant_g_source_obstruction`,
`pairDescendant_t_source_obstruction`), and a point whose hard axis was feasible keeps its point
and frame (`pairDescendant_fixed_sources`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
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

/-- If G–A becomes separated along the axis zero only on the cycle after both moves, then
`θA - θH > 0` or the contact H–G is strict on that cycle. -/
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

/-- If B–T becomes separated along the axis two only on the cycle after both moves, then
`θD - θB > 0` or the contact T–D, along the owner of the output, is strict on that cycle. -/
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

/-- On the cycle after both moves, G keeps its point and frame when G–A is separated along the
axis zero, and T keeps them when B–T is separated along the axis two. -/
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

end SignedCycle.NormalizedBoundaryInput
end SquaresInCircles.Eight
