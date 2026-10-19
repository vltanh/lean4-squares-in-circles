module

public import SquaresInCircles.Eight.CycleActions
public import SquaresInCircles.Eight.Arithmetic.FourTypePairs
public import SquaresInCircles.Eight.WordGeometry
public import SquaresInCircles.Eight.ExactFamily.EqualityGeometry

/-!
# Arbitrary packing to the captured candidate frame

The original centers are retained in `source`. Boundary reduction is used at
`max q qMinus`; its representative is then expanded to Q1. The temporary Q0
expansion supplies only the frame and quarter-word conclusions. Actual
permutations, a possible reflection and a common rotation act on the original
packing and on both boundary cycles together.

Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight

/-- The geometric entry point consumed by the sharp terminal and original
stationary pullback. Original containment remains at the actual input q. -/
structure GlobalNormalization (S : Fin 8 → UnitSquare) (q : ℝ) where
  squares : Fin 8 → UnitSquare
  packing : SqPacking squares (0,0) q
  central_core : ContainsCore (squares 0)
  reflected : Bool
  congruent : Congruent S (0,0)
    (fun i => if reflected then reflectDiagonalSquare (squares i) else squares i)
  source : NeighborCycle (sourceLevel q)
  source_square : ∀ i,source.square i=squares i.succ
  source_order : PolarOrder source
  recovered : BoundaryCycle (sourceLevel q)
  expanded : BoundaryCycle Q1
  expansion : RadiusExpansion recovered expanded
  frame : Candidate.Frame expanded
  eHalf : Candidate.EHalf expanded
  source_frames : ∀ i,SameFrame (source.square i) (expanded.square i)
  source_selected : source.selected=expanded.selected

structure NormalizationData (S : Fin 8 → UnitSquare) (q : ℝ) where
  squares : Fin 8 → UnitSquare
  packing : SqPacking squares (0,0) q
  central_core : ContainsCore (squares 0)
  congruent : ∃ b : Bool,Congruent S (0,0) (fun i => reflectionSquare b (squares i))
  source : NeighborCycle (sourceLevel q)
  source_square : ∀ i,source.square i=squares i.succ
  source_order : PolarOrder source
  recovered : BoundaryCycle (sourceLevel q)
  expanded : BoundaryCycle Q1
  expansion : RadiusExpansion recovered expanded
  source_frames : ∀ i,SameFrame (source.square i) (expanded.square i)
  source_selected : source.selected=expanded.selected

lemma sameSquare_of_physical_center {K J : UnitSquare}
    (hc : K.center=J.center) (hf : SamePhysicalFrame K J) : SameSquare K J := by
  rcases hf with ⟨hcos,hsin⟩|⟨hcos,hsin⟩|⟨hcos,hsin⟩|⟨hcos,hsin⟩
  · constructor <;> intro p <;> simp [openSquare,closedSquare,localX,localY,hc,hcos,hsin]
  · have hx (p : Point) : localX K p=localY J p := by simp [localX,localY,hc,hcos,hsin]
    have hy (p : Point) : localY K p= -localX J p := by simp [localX,localY,hc,hcos,hsin]; ring
    constructor <;> intro p <;> simp [openSquare,closedSquare,hx,hy,abs_neg,and_comm]
  · have hx (p : Point) : localX K p= -localX J p := by simp [localX,hc,hcos,hsin]; ring
    have hy (p : Point) : localY K p= -localY J p := by simp [localY,hc,hcos,hsin]; ring
    constructor <;> intro p <;> simp [openSquare,closedSquare,hx,hy,abs_neg]
  · have hx (p : Point) : localX K p= -localY J p := by simp [localX,localY,hc,hcos,hsin]; ring
    have hy (p : Point) : localY K p=localX J p := by simp [localX,localY,hc,hcos,hsin]
    constructor <;> intro p <;> simp [openSquare,closedSquare,hx,hy,abs_neg,and_comm]

/-- The sixteen quarter-turn combinations turn the relative cosine and sine of a
pair by a common quarter turn. -/
private lemma relative_same_physical {K K' J J' : UnitSquare}
    (hK : SamePhysicalFrame K K') (hJ : SamePhysicalFrame J J') :
    (relativeC K J=relativeC K' J' ∧ relativeS K J=relativeS K' J') ∨
    (relativeC K J=relativeS K' J' ∧ relativeS K J= -relativeC K' J') ∨
    (relativeC K J= -relativeC K' J' ∧ relativeS K J= -relativeS K' J') ∨
    (relativeC K J= -relativeS K' J' ∧ relativeS K J=relativeC K' J') := by
  rcases hK with ⟨hc,hs⟩|⟨hc,hs⟩|⟨hc,hs⟩|⟨hc,hs⟩ <;>
    rcases hJ with ⟨hC,hS⟩|⟨hC,hS⟩|⟨hC,hS⟩|⟨hC,hS⟩ <;>
    first
    | (left; constructor <;> simp only [relativeC,relativeS,hc,hs,hC,hS] <;> ring1)
    | (right; left; constructor <;> simp only [relativeC,relativeS,hc,hs,hC,hS] <;> ring1)
    | (right; right; left; constructor <;> simp only [relativeC,relativeS,hc,hs,hC,hS] <;> ring1)
    | (right; right; right; constructor <;> simp only [relativeC,relativeS,hc,hs,hC,hS] <;> ring1)

lemma threshold_same_physical {K K' J J' : UnitSquare}
    (hK : SamePhysicalFrame K K') (hJ : SamePhysicalFrame J J') :
    SAT.threshold K J=SAT.threshold K' J' := by
  rcases relative_same_physical hK hJ with ⟨h₁,h₂⟩|⟨h₁,h₂⟩|⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;>
    simp only [SAT.threshold,h₁,h₂,abs_neg] <;> ring

def BoundaryNormalization.sourceSquare {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : BoundaryNormalization (S := S) q) (i : Vertex) : UnitSquare :=
  moveCenter (N.expanded.square i) (S (N.original.index i)).center

lemma BoundaryNormalization.sourceSquare_same {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : BoundaryNormalization (S := S) q) (i : Vertex) :
    SameSquare (N.sourceSquare i) (S (N.original.index i)) := by
  exact sameSquare_of_physical_center rfl (N.physical_frames i)

lemma BoundaryNormalization.sourceSquare_feasible {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : BoundaryNormalization (S := S) q) (i : Vertex) :
    (N.expanded.selected i).Feasible (N.sourceSquare i) (N.sourceSquare (next i)) := by
  have hp := N.original_selected_feasible i
  have ht := threshold_same_physical (N.physical_frames i) (N.physical_frames (next i))
  have hn := N.selected_normal i
  change SAT.threshold (N.sourceSquare i) (N.sourceSquare (next i)) ≤ _
  have hthreshold : SAT.threshold (N.sourceSquare i) (N.sourceSquare (next i))=
      SAT.threshold (S (N.original.index i)) (S (N.original.index (next i))) := ht
  rw [hthreshold]
  dsimp [SignedAxis.Feasible,SignedAxis.projection] at hp ⊢
  have hn' : (N.expanded.selected i).normal (N.sourceSquare i) (N.sourceSquare (next i))=
      (N.original.cycle.selected i).normal (S (N.original.index i)) (S (N.original.index (next i))) := hn
  rw [hn']
  exact hp

def BoundaryNormalization.source {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : BoundaryNormalization (S := S) q) : NeighborCycle (sourceLevel q) where
  square := N.sourceSquare
  contained i := by
    have h := N.original.cycle.contained i
    have hq : 0 ≤ sourceLevel q := by
      dsimp [sourceLevel]
      exact (by norm_num [qMinus] : (0:ℝ) ≤ qMinus).trans (le_max_right _ _)
    apply (SqContained.iff_points hq _).2
    intro p hp
    have hh := (SqContained.iff_points hq _).1 h p
    rw [N.original.square_eq i] at hh
    exact hh ((N.sourceSquare_same i).2 p |>.1 hp)
  core i := by
    intro p hp
    have h := N.original.cycle.core i
    rw [N.original.square_eq i] at h
    exact h p ((N.sourceSquare_same i).2 p |>.1 hp)
  selected := N.expanded.selected
  feasible := N.sourceSquare_feasible

def BoundaryNormalization.sourceOrder {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : BoundaryNormalization (S := S) q) : PolarOrder N.source where
  beta := N.original.original_order.beta
  center_cos i := by simpa [BoundaryNormalization.source,BoundaryNormalization.sourceSquare,
    moveCenter,N.original.square_eq i] using N.original.original_order.center_cos i
  center_sin i := by simpa [BoundaryNormalization.source,BoundaryNormalization.sourceSquare,
    moveCenter,N.original.square_eq i] using N.original.original_order.center_sin i
  positive := N.original.original_order.positive
  below_pi := N.original.original_order.below_pi

/-- Extend the central label and the seven actual exterior labels to a full
bijection. Surjectivity is part of the central-core enumeration. -/
def OrderedExterior.labels {S : Fin 8 → UnitSquare} {q : ℝ} (O : OrderedExterior (S := S) q) :
    Equiv.Perm (Fin 8) := Equiv.ofBijective
  (Fin.cases O.central (fun i => O.index i)) (by
    constructor
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          rfl
        · intro hij
          exact (O.misses_central j hij).elim
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact (O.misses_central i hij.symm).elim
        · intro hij
          simp only [Fin.cases_succ] at hij
          rw [O.index.injective hij]
    · intro j
      by_cases hj : j=O.central
      · exact ⟨0,hj.symm⟩
      · obtain ⟨i,hi⟩ := O.covers_exterior j hj
        exact ⟨i.succ,hi⟩)

def BoundaryNormalization.squares {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : BoundaryNormalization (S := S) q) : Fin 8 → UnitSquare :=
  Fin.cases (S N.original.central) N.sourceSquare

lemma BoundaryNormalization.squares_same {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : BoundaryNormalization (S := S) q) (i : Fin 8) :
    SameSquare (N.squares i) (S (N.original.labels i)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨fun _ => Iff.rfl,fun _ => Iff.rfl⟩
  · exact N.sourceSquare_same j

def BoundaryNormalization.data {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : BoundaryNormalization (S := S) q) (hp : SqPacking S (0,0) q) : NormalizationData S q where
  squares := N.squares
  packing := by
    refine ⟨hp.1,?_,?_⟩
    · intro i p h
      exact hp.2.1 (N.original.labels i) p ((N.squares_same i).2 p |>.1 h)
    · intro i j hij p h
      exact hp.2.2 _ _ (N.original.labels.injective.ne hij) p
        ⟨(N.squares_same i).1 p |>.1 h.1,(N.squares_same j).1 p |>.1 h.2⟩
  central_core := N.original.contains_core
  congruent := ⟨false,congruent_of_origin_sets N.original.labels
    (fun i p => (N.squares_same i).1 p |>.symm)
    (fun i p => (N.squares_same i).2 p |>.symm)⟩
  source := N.source
  source_square i := rfl
  source_order := N.sourceOrder
  recovered := N.reduction.result
  expanded := N.expanded
  expansion := N.expansion
  source_frames i := ⟨rfl,rfl⟩
  source_selected := rfl

lemma reflectionSquare_twice (K : UnitSquare) :
    reflectDiagonalSquare (reflectDiagonalSquare K)=K := by
  cases K
  rfl

def CycleAction.squares (G : CycleAction) (S : Fin 8 → UnitSquare) : Fin 8 → UnitSquare :=
  fun i => motionSquare G.rotation G.reversed (S (extendExteriorPerm G.index i))

lemma CycleAction.squares_packing {q : ℝ} (G : CycleAction) {S : Fin 8 → UnitSquare}
    (hp : SqPacking S (0,0) q) : SqPacking (G.squares S) (0,0) q := by
  have hpR := (sqPacking_iff_packing S (0,0) hp.1).1 hp
  have hl := packing_relabel hpR (extendExteriorPerm G.index)
  have hfinal : Packing (G.squares S) (0,0) (Real.sqrt q) := by
    change Packing (fun i => motionSquare G.rotation G.reversed (S (extendExteriorPerm G.index i)))
      (0,0) (Real.sqrt q)
    cases h : G.reversed
    · simpa [motionSquare,reflectionSquare] using
        packing_pull hl (G.rotation:Direction)
    · simpa [motionSquare,reflectionSquare] using
        packing_pull (packing_reflectDiagonal hl) (G.rotation:Direction)
  exact (sqPacking_iff_packing _ _ hp.1).2 hfinal

lemma CycleAction.squares_congruent (G : CycleAction) (S : Fin 8 → UnitSquare) :
    Congruent S (0,0) (fun i => reflectionSquare G.reversed (G.squares S i)) := by
  rcases G with ⟨s,rev,rot⟩
  cases rev
  · refine ⟨(rot:Direction),extendExteriorPerm (CycleAction.index ⟨s,false,rot⟩),?_⟩
    intro i p
    constructor
    · exact (pullSquare_open (0,0) (rot:Direction) _ p).symm
    · exact (pullSquare_closed (0,0) (rot:Direction) _ p).symm
  · refine ⟨(-rot:Direction),extendExteriorPerm (CycleAction.index ⟨s,true,rot⟩),?_⟩
    intro i p
    have he : diagonalPoint (frameEquiv (0,0) (rot:Direction) (diagonalPoint p))=
        pointInDirection (0,0) (-rot:Direction) p.1 p.2 := by
      simpa [frameEquiv_apply] using diagonal_conjugates_rotation (-rot:Direction) (diagonalPoint p)
    constructor
    · change _ ↔ openSquare (reflectDiagonalSquare (pullSquare (0,0) (rot:Direction)
        (reflectDiagonalSquare (S (extendExteriorPerm (CycleAction.index ⟨s,true,rot⟩) i))))) p
      rw [reflectDiagonal_open,pullSquare_open,reflectDiagonal_open,he]
    · change _ ↔ closedSquare (reflectDiagonalSquare (pullSquare (0,0) (rot:Direction)
        (reflectDiagonalSquare (S (extendExteriorPerm (CycleAction.index ⟨s,true,rot⟩) i))))) p
      rw [reflectDiagonal_closed,pullSquare_closed,reflectDiagonal_closed,he]

lemma reflection_congruent_trans {S T U : Fin 8 → UnitSquare}
    (hST : ∃ b : Bool,Congruent S (0,0) (fun i => reflectionSquare b (T i)))
    (hTU : ∃ b : Bool,Congruent T (0,0) (fun i => reflectionSquare b (U i))) :
    ∃ b : Bool,Congruent S (0,0) (fun i => reflectionSquare b (U i)) := by
  obtain ⟨b,hb⟩ := hST
  obtain ⟨c,hc⟩ := hTU
  cases b <;> cases c
  · exact ⟨false,congruent_trans hb hc⟩
  · exact ⟨true,congruent_trans hb hc⟩
  · exact ⟨true,congruent_trans hb (congruent_diagonal hc)⟩
  · refine ⟨false,congruent_trans hb ?_⟩
    simpa [reflectionSquare,reflectionSquare_twice] using congruent_diagonal hc

def NormalizationData.act {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : NormalizationData S q) (G : CycleAction) : NormalizationData S q where
  squares := G.squares N.squares
  packing := G.squares_packing N.packing
  central_core := motionSquare_containsCore _ _ N.central_core
  congruent := reflection_congruent_trans N.congruent ⟨G.reversed,G.squares_congruent N.squares⟩
  source := G.neighbor N.source
  source_square i := by simp [CycleAction.neighbor,CycleAction.squares,N.source_square,extendExteriorPerm]
  source_order := G.polarOrder N.source_order
  recovered := G.boundary N.recovered
  expanded := G.boundary N.expanded
  expansion := G.radiusExpansion N.expansion
  source_frames i := motionSquare_sameFrame _ _ (N.source_frames (G.index i))
  source_selected := by simp [CycleAction.neighbor,CycleAction.boundary,N.source_selected]

lemma candidate_quarter_cast (i : Vertex) :
    ((candidateQuarterWord i).val:ℤ)=Candidate.word i := by
  fin_cases i <;> norm_num [candidateQuarterWord,quarterRepresentatives,Candidate.word]

lemma quarter_eq_offsets {m : Vertex → ℤ}
    (hm : ∀ i,integerQuarterIncrement m i=Candidate.word i) (i : Vertex) :
    m i=m Candidate.A+Candidate.offsets i := by
  have h₀ := hm 0
  have h₁ := hm 1
  have h₂ := hm 2
  have h₃ := hm 3
  have h₄ := hm 4
  have h₅ := hm 5
  have h₆ := hm 6
  fin_cases i <;>
    norm_num [integerQuarterIncrement,Candidate.word,Candidate.offsets,Candidate.A,next] at * <;> omega

/-- The action giving the reflected candidate ordering; its edge permutation
is i ↦ 4−i and its vertex permutation is i ↦ 5−i. -/
def CycleAction.candidateMirror (G : CycleAction) : CycleAction :=
  ⟨G.index 5,!G.reversed,0⟩

lemma CycleAction.candidateMirror_edge (G : CycleAction) (i : Vertex) :
    G.candidateMirror.edge i=G.edge (4-i) := by
  have htable : ∀ (s : Vertex) (b : Bool) (i : Vertex),
      CycleAction.edge (CycleAction.candidateMirror ⟨s,b,0⟩) i=CycleAction.edge ⟨s,b,0⟩ (4-i) := by
    decide
  exact htable G.shift G.reversed i

lemma CycleAction.candidateMirror_E {q : ℝ} (G : CycleAction) (C : BoundaryCycle q) :
    (G.candidateMirror.boundary C).tangent Candidate.E= -(G.boundary C).tangent Candidate.E := by
  rw [G.candidateMirror.tangent,G.tangent]
  have htable : ∀ (s : Vertex) (b : Bool),
      CycleAction.index (CycleAction.candidateMirror ⟨s,b,0⟩) Candidate.E=
        CycleAction.index ⟨s,b,0⟩ Candidate.E := by
    decide
  have hidx : G.candidateMirror.index Candidate.E=G.index Candidate.E :=
    htable G.shift G.reversed
  have hsign : reflectionSign G.candidateMirror.reversed= -reflectionSign G.reversed := by
    cases h : G.reversed <;> simp [CycleAction.candidateMirror,reflectionSign,h]
  rw [hidx,hsign]
  ring

lemma candidate_word_mirror (i : Vertex) : Candidate.word (4-i)=Candidate.word i := by
  fin_cases i <;> norm_num [Candidate.word]

def normalizedCandidateAction {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C) (G : CycleAction) :
    CycleAction :=
  { G with rotation := G.rotation+(F.act G).theta Candidate.A+
      ((F.act G).quarter Candidate.A:ℝ)*(Real.pi/2) }

lemma normalizedCandidateAction_tangent {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (G : CycleAction) (i : Vertex) :
    ((normalizedCandidateAction F G).boundary C).tangent i=(G.boundary C).tangent i := rfl

/-- Subtract the actual A-frame angle, after the integer word has already
fixed all seven quarter offsets. No tangent or owner capture is assumed. -/
def candidateFrameOfWordAction {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (hq : q ≤ Q0) (G : CycleAction)
    (hword : ∀ i,integerQuarterIncrement (G.quarter F.quarter) i=Candidate.word i) :
    Candidate.Frame ((normalizedCandidateAction F G).boundary C) where
  theta i := (F.act G).theta i-(F.act G).theta Candidate.A
  theta_A := sub_self _
  canonical_eq i := by
    have h := (F.act G).represents i
    have hm := quarter_eq_offsets hword i
    have hm' : ((G.quarter F.quarter i:ℤ):ℝ)=
        ((G.quarter F.quarter Candidate.A:ℤ):ℝ)+(Candidate.offsets i:ℝ) := by exact_mod_cast hm
    rw [(normalizedCandidateAction F G).canonical]
    change (G.boundary C).canonicalAngle i=_ at h
    rw [G.canonical] at h
    have hrev : (normalizedCandidateAction F G).reversed=G.reversed := rfl
    have hidx : (normalizedCandidateAction F G).index=G.index := rfl
    have hwrap : (normalizedCandidateAction F G).wrap=G.wrap := rfl
    have hrot : (normalizedCandidateAction F G).rotation=G.rotation+(F.act G).theta Candidate.A+
        ((G.quarter F.quarter Candidate.A:ℤ):ℝ)*(Real.pi/2) := rfl
    have hquarter : (F.act G).quarter=G.quarter F.quarter := rfl
    rw [hrev,hidx,hwrap,hrot]
    rw [hquarter] at h
    linear_combination h+(Real.pi/2)*hm'
  spread i j := by
    have hi := (F.act G).theta_range i
    have hj := (F.act G).theta_range j
    have hsmall := (F.act G).small
    apply abs_lt.2
    constructor <;> linarith
  gap_lower := boundary_gap_lower _ hq
  gap_upper := boundary_gap_upper _ hq
  forward_complete := boundary_forward_complete _ hq

structure CandidateNormalization {q : ℝ} (C : BoundaryCycle q) where
  action : CycleAction
  frame : Candidate.Frame (action.boundary C)
  eHalf : Candidate.EHalf (action.boundary C)

lemma candidate_normalization_of_word {q : ℝ} (C : BoundaryCycle q) (F : QuarterLift C)
    (hq : q ≤ Q0) (hgap : ∀ i,19/25<angleGap C.beta i)
    (hw : (F.word hgap pi_lt_22_over_7).DihedralEquivalent candidateQuarterWord) :
    Nonempty (CandidateNormalization C) := by
  obtain ⟨s,b,hword⟩ := hw
  let G : CycleAction := ⟨if b then next s else -s,b,0⟩
  have hwordG (i : Vertex) : integerQuarterIncrement (G.quarter F.quarter) i=Candidate.word i := by
    rw [G.quarter_increment,← F.word_cast hgap pi_lt_22_over_7]
    have hw' := congrFun hword (G.edge i)
    have he : (F.word hgap pi_lt_22_over_7) (G.edge i)=candidateQuarterWord i := by
      rw [hw']
      cases hb : b <;>
        simp [quarterDihedral,G,CycleAction.edge,CycleAction.index,hb,next] <;>
        congr 1 <;> abel
    rw [he,candidate_quarter_cast]
  have hwordR (i : Vertex) :
      integerQuarterIncrement (G.candidateMirror.quarter F.quarter) i=Candidate.word i := by
    rw [G.candidateMirror.quarter_increment,G.candidateMirror_edge,
      ← G.quarter_increment,hwordG,candidate_word_mirror]
  by_cases he : (G.boundary C).tangent Candidate.E ≤ 0
  · exact ⟨⟨normalizedCandidateAction F G,candidateFrameOfWordAction F hq G hwordG,
      by simpa [Candidate.EHalf,normalizedCandidateAction_tangent] using he⟩⟩
  · have hneg : (G.candidateMirror.boundary C).tangent Candidate.E ≤ 0 := by
      rw [G.candidateMirror_E]
      linarith
    exact ⟨⟨normalizedCandidateAction F G.candidateMirror,
      candidateFrameOfWordAction F hq G.candidateMirror hwordR,
      by simpa [Candidate.EHalf,normalizedCandidateAction_tangent] using hneg⟩⟩

/-- The Q0 cycle is a temporary witness for frame concentration and the word
exclusion. The unchanged real rays, tangents and quarter lifts are then read
on the already-feasible Q1 cycle. -/
theorem boundary_candidate_normalization (C : BoundaryCycle Q1) :
    Nonempty (CandidateNormalization C) := by
  have hQ1 : Q1 ∈ Set.Icc (5/2) 4 :=
    ⟨radius_levels.1.le.trans radius_levels.2.1.le,
      (radius_levels.2.2.1.trans radius_levels.2.2.2).le⟩
  have hQ0 : Q0 ∈ Set.Icc (5/2) 4 :=
    ⟨hQ1.1.trans radius_levels.2.2.1.le,radius_levels.2.2.2.le⟩
  let D := C.expand hQ1 hQ0 radius_levels.2.2.1.le
  have hR : RadiusExpansion C D := C.expand_spec hQ1 hQ0 radius_levels.2.2.1.le
  obtain ⟨τ,ψ,hpair⟩ := four_type_pair_bound D
  have hcost := physical_cycle_width_bound τ D.beta
    (fun i => periodicFrameCost (D.canonicalAngle (next i)-D.canonicalAngle i)) ψ hpair
    (by linarith [Arithmetic.two_pi_lt_710_over_113])
  obtain ⟨F⟩ := quarterLift_of_cost D hcost
  have hgapD := boundary_gap_lower D le_rfl
  have hwordD := quarter_word_candidate D F hgapD
  let F' := F.pullback hR
  have hgapC := boundary_gap_lower C radius_levels.2.2.1.le
  have hw : F'.word hgapC pi_lt_22_over_7=F.word hgapD pi_lt_22_over_7 := by
    funext i
    apply Fin.ext
    rfl
  apply candidate_normalization_of_word C F' radius_levels.2.2.1.le hgapC
  simpa only [hw] using hwordD

theorem global_normalization_exists {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q ≤ Q1) : Nonempty (GlobalNormalization S q) := by
  obtain ⟨B⟩ := boundary_normalization_exists hp hq
  let N := B.data hp
  obtain ⟨K⟩ := boundary_candidate_normalization N.expanded
  let M := N.act K.action
  obtain ⟨b,hb⟩ := M.congruent
  exact ⟨{
    squares := M.squares
    packing := M.packing
    central_core := M.central_core
    reflected := b
    congruent := hb
    source := M.source
    source_square := M.source_square
    source_order := M.source_order
    recovered := M.recovered
    expanded := M.expanded
    expansion := M.expansion
    frame := K.frame
    eHalf := K.eHalf
    source_frames := M.source_frames
    source_selected := M.source_selected }⟩

/-! ## The original slider sectors, after stationary anchor recovery -/

lemma two_successive_gaps_lt_pi (β : Vertex → ℝ)
    (hgap : ∀ i,19/25<angleGap β i) (i : Vertex) :
    angleGap β i+angleGap β (next i)<Real.pi := by
  have hs := angleGap_sum β
  have h₀ := hgap 0
  have h₁ := hgap 1
  have h₂ := hgap 2
  have h₃ := hgap 3
  have h₄ := hgap 4
  have h₅ := hgap 5
  have h₆ := hgap 6
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ,angleGap,next] at * <;>
    linarith [pi_lt_22_over_7]

/-- A linear functional positive at both ends of an angular interval shorter
than pi remains positive at every positive-radius point strictly between
those rays. The sine interpolation identity supplies positive coefficients. -/
lemma dot_positive_between_polar {p₁ p₂ p₃ n : Point} {r₁ r₂ r₃ a b c : ℝ}
    (hr₁ : 0<r₁) (hr₂ : 0<r₂) (hr₃ : 0<r₃)
    (hp₁ : p₁=(r₁*Real.cos a,r₁*Real.sin a))
    (hp₂ : p₂=(r₂*Real.cos b,r₂*Real.sin b))
    (hp₃ : p₃=(r₃*Real.cos c,r₃*Real.sin c))
    (hab : a<b) (hbc : b<c) (hac : c-a<Real.pi)
    (hn₁ : 0<dot n p₁) (hn₃ : 0<dot n p₃) : 0<dot n p₂ := by
  have hs₁ : 0<Real.sin (c-b) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith)
  have hs₂ : 0<Real.sin (b-a) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith)
  have hs₃ : 0<Real.sin (c-a) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) hac
  have hid : dot n p₂*(r₁*r₃*Real.sin (c-a))=
      r₂*r₃*dot n p₁*Real.sin (c-b)+r₂*r₁*dot n p₃*Real.sin (b-a) := by
    rw [hp₁,hp₂,hp₃]
    dsimp [dot]
    rw [Real.sin_sub,Real.sin_sub,Real.sin_sub]
    ring
  have hright : 0<r₂*r₃*dot n p₁*Real.sin (c-b)+r₂*r₁*dot n p₃*Real.sin (b-a) := by
    exact add_pos (by positivity) (by positivity)
  have hfactor : 0<r₁*r₃*Real.sin (c-a) := by positivity
  rw [← hid] at hright
  nlinarith

lemma polarOrder_positive_three {q : ℝ} {C : NeighborCycle q} (O : PolarOrder C)
    {l m u : Vertex} {n : Point}
    (hlm : O.beta l<O.beta m) (hmu : O.beta m<O.beta u)
    (hspan : O.beta u-O.beta l<Real.pi)
    (hl : 0<dot n (C.square l).center) (hu : 0<dot n (C.square u).center) :
    0<dot n (C.square m).center := by
  apply dot_positive_between_polar
    (center_radius_pos (C.core l)) (center_radius_pos (C.core m)) (center_radius_pos (C.core u))
    (Prod.ext (O.center_cos l) (O.center_sin l))
    (Prod.ext (O.center_cos m) (O.center_sin m))
    (Prod.ext (O.center_cos u) (O.center_sin u)) hlm hmu hspan hl hu

lemma core_primary_of_small_secondary {K : UnitSquare} {a b : ℝ}
    (hcore : CoreAvoiding K) (ha : 0≤a) (hb : |b|≤1/2)
    (hα : alpha K (0,0)=a) (hβ : beta K (0,0)=|b|) : 7/12≤a := by
  have hc := (coreAvoiding_iff_distance K).1 hcore
  rw [coreDistanceSq,hα,hβ,max_eq_right (by linarith : |b|-1/2≤0)] at hc
  norm_num [coreRadius] at hc
  have haHalf : 1/2<a := by
    by_contra! hh
    rw [max_eq_right (by linarith)] at hc
    norm_num at hc
  rw [max_eq_left (by linarith)] at hc
  nlinarith

open ExactFamily ExactFamily.Coordinates in
/-- The side of each slider line is selected from the untouched original
cyclic order only after the five anchor centers have been fixed. No claim
about preserving individual rays during boundary reduction is used. -/
theorem GlobalNormalization.original_slider_sectors {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) {Z η : ℝ}
    (hcenters : ∀ i,(N.source.square i).center=sharpData.exteriorCenters Z η i)
    (hTframe : (N.source.square 4).cosine=0 ∧ (N.source.square 4).sine=1)
    (hGframe : (N.source.square 1).cosine=sharpData.s ∧ (N.source.square 1).sine= -sharpData.c) :
    7/12≤Z ∧ η≤ sharpData.etaMax := by
  have hq : sourceLevel qStar≤Q0 := by
    dsimp [sourceLevel,Q0,qMinus]
    exact max_le qStar_limits.2.2.le
      (by norm_num)
  have hg := polar_order_gap_lower N.source N.source_order hq
  have htspan := two_successive_gaps_lt_pi N.source_order.beta hg (3:Vertex)
  have hgspan := two_successive_gaps_lt_pi N.source_order.beta hg (0:Vertex)
  have h₀ := hg 0
  have h₁ := hg 1
  have h₃ := hg 3
  have h₄ := hg 4
  norm_num [angleGap,next] at htspan hgspan h₀ h₁ h₃ h₄
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hy := sharp_y
  have hdot_scale (t : ℝ) (v p : Point) : dot (scale t v) p=t*dot v p := by
    simp only [dot,scale]
    ring
  have hTpositive : 0<Z := by
    have h := polarOrder_positive_three N.source_order
      (l := 3) (m := 4) (u := 5) (n := (0,1))
      (by linarith) (by linarith) (by linarith)
      (by rw [hcenters]; norm_num [exteriorCenters,pB,dot]; linarith [hy.1])
      (by rw [hcenters]; norm_num [exteriorCenters,pD,dot]; linarith)
    simpa [hcenters,exteriorCenters,pT,dot] using h
  have hGnegative : sharpData.h₂+1/2+η<0 := by
    have hleft : 0<dot (scale (-1) sharpData.f) (N.source.square 0).center := by
      rw [hcenters]
      norm_num [exteriorCenters,pH,hdot_scale,sharpData.dot_f_inFrame]
      linarith
    have hright : 0<dot (scale (-1) sharpData.f) (N.source.square 2).center := by
      rw [hcenters]
      have hcp : 0<sharpData.c := by linarith
      have hsp : 0<sharpData.s := by linarith
      have hxp : 0<sharpData.x₁-1/2 := by linarith
      have hyp : 0< -sharpData.y-1/2 := by linarith [hy.2]
      norm_num [exteriorCenters,pA,Coordinates.f,scale,dot]
      nlinarith [mul_pos hsp hxp,mul_pos hcp hyp]
    have h := polarOrder_positive_three N.source_order
      (l := 0) (m := 1) (u := 2) (n := scale (-1) sharpData.f)
      (by linarith) (by linarith) (by linarith) hleft hright
    rw [hcenters] at h
    norm_num [exteriorCenters,pG,hdot_scale,sharpData.dot_f_inFrame] at h
    linarith
  have hxsmall : |sharpData.x₂-3/2|≤1/2 := by
    rw [abs_of_pos (by linarith : 0<sharpData.x₂-3/2)]
    linarith
  have hXsmall : |sharpData.h₁+3/2|≤1/2 := by
    rw [abs_of_pos (by linarith : 0<sharpData.h₁+3/2)]
    linarith
  have hTα : alpha (N.source.square 4) (0,0)=Z := by
    simp [alpha,localX,hTframe.1,hTframe.2,hcenters,exteriorCenters,pT,abs_of_pos hTpositive]
  have hTβ : beta (N.source.square 4) (0,0)=|sharpData.x₂-3/2| := by
    simp [beta,localY,hTframe.1,hTframe.2,hcenters,exteriorCenters,pT]
  have hGα : alpha (N.source.square 1) (0,0)= -(sharpData.h₂+1/2+η) := by
    have hlocal : localX (N.source.square 1) (0,0)=sharpData.h₂+1/2+η := by
      rw [localX,hGframe.1,hGframe.2,hcenters]
      norm_num [exteriorCenters,pG,inFrame]
      linear_combination (sharpData.h₂+1/2+η)*sharpData.unit
    rw [alpha,hlocal,abs_of_neg hGnegative]
  have hGβ : beta (N.source.square 1) (0,0)=|sharpData.h₁+3/2| := by
    have hlocal : localY (N.source.square 1) (0,0)= -(sharpData.h₁+3/2) := by
      rw [localY,hGframe.1,hGframe.2,hcenters]
      norm_num [exteriorCenters,pG,inFrame]
      linear_combination -(sharpData.h₁+3/2)*sharpData.unit
    rw [beta,hlocal,abs_neg]
  have hT := core_primary_of_small_secondary (N.source.core 4) hTpositive.le hxsmall hTα hTβ
  have hG := core_primary_of_small_secondary (N.source.core 1)
    (by linarith) hXsmall hGα hGβ
  exact ⟨hT,by dsimp [etaMax]; linarith⟩

end SquaresInCircles.Eight
