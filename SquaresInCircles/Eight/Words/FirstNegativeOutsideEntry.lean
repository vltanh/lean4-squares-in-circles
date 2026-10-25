module

public import SquaresInCircles.Eight.Words.Aligned.NegativeAssembly
public import SquaresInCircles.Eight.Words.Common.One
public import SquaresInCircles.Eight.Words.Common.Zero
public import SquaresInCircles.Eight.Words.FirstNegativeSlack
public import SquaresInCircles.Eight.Words.Outside.ECycle

/-!
# Eight squares: exhaustive original-E preparation for the first negative primary

EH0 and short EH1 reach the paid first GA0 contact
directly. The long-EH1 branch first moves E on its actual core/circle arc
using the original DE2 or DE3 witness. The original H--D span rules out
the aligned-long alternative. No BT2 availability is required.
-/

section
/-!
## Paid first-contact endpoints with the retained high-H bounds

The endpoint (`Source.first_mixed_endpoint`) is the rightmost hard-axis contact, followed by a
contraction paid by its strict mixed margin. Its H tangent stays greater than `.844` and its H
primary below 1. The negative-T transport at the original E uses these bounds, also when both
primary axes start with a negative error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace AlignedNegative
open PrimaryCap

structure FirstMixedEndpoint {q t : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (E : SignedPoint) (e : ℝ) (j : Fin 4) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  Hpoint : SignedPoint
  Gpoint : SignedPoint
  H_sorted : Hpoint.Sorted
  G_sorted : Gpoint.Sorted
  H_core : Hpoint.AvoidsCore
  G_core : Gpoint.Core
  H_circle_loss : Hpoint.circle<H.circle
  G_inside : Gpoint.circle<q
  H_high : 211/250<Hpoint.y
  H_primary_lt_one : Hpoint.a<1
  G_negative : Gpoint.y<0
  H_nondiagonal : |Hpoint.y|<Hpoint.a
  G_nondiagonal : |Gpoint.y|<Gpoint.a
  G_primary : Gpoint.a=7/12
  H_tangent_decreases : Hpoint.y<H.y
  HG0 : zeroFeasible Hpoint Gpoint 0 0
  HG2 : zeroFeasible Hpoint Gpoint 0 2
  GA0 : quarterFeasible Gpoint A (-angle) 0
  EH : quarterFeasible E Hpoint (e+angle) j
  EH_error : e+angle∈Icc 0 (7/10 : ℝ)
  EH_short : j=1 → e+angle≤11/50

theorem Source.first_mixed_endpoint {q t e : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) {j : Fin 4} (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEy : E.y≤0)
    (hj : j=0 ∨ j=1) (he : |e+t|≤7/10)
    (hshort : j=1 → |e+t|≤11/50)
    (hf : quarterFeasible E H (e+t) j) :
    Nonempty (FirstMixedEndpoint I E e j) := by
  obtain ⟨O⟩ := I.first_hard hq
  let x := O.angle
  let P := A.a-1/2
  let H₀ := movingAnchor H.circle P x
  let G₀ := point P x
  let margin := quarterProjection E H₀ (e+x) j-edgeWidth (e+x)
  have hcontact : e+x∈Icc 0 (7/10 : ℝ) ∧ 0<margin ∧
      (j=1 → e+x≤11/50) := by
    rcases hj with hj | hj
    · subst j
      have hh := O.low_mixed_slack hq hEy he hf
      refine ⟨hh.1,?_,by norm_num⟩
      dsimp [margin,H₀,P,x]
      rw [← lowMixedSlack_actual E hh.1]
      exact hh.2
    · subst j
      have hh := O.high_mixed_slack hq hEs hEc hEy (hshort rfl) hf
      have hwide : e+O.angle∈Icc 0 (7/10 : ℝ) :=
        ⟨hh.1.1,by linarith [hh.1.2]⟩
      refine ⟨hwide,?_,fun _ => hh.1.2⟩
      dsimp [margin,H₀,P,x]
      rw [← highMixedSlack_actual E hwide]
      exact hh.2
  obtain ⟨hHs,hHcircle,hHprimary,hHtangent,hHcore,hHy,hHrad⟩ :=
    I.path_geometry hq ⟨O.angle_mem.1,O.angle_mem.2.le⟩
  have hHtangentStrict := I.path_tangent_strict hq O.angle_mem
  have hHsort : H₀.y<H₀.a := by
    have hh := I.H_sorted.2
    rw [abs_of_nonneg I.H_nonneg] at hh
    exact hHtangentStrict.trans_le (hh.trans hHprimary)
  have hHhigh : 211/250<H₀.y := (O.high_anchor hq).2.1
  have hHupper : H₀.a<1 := (O.high_anchor hq).2.2
  let η := min ((H₀.a-H₀.y)/2) (min ((H₀.a-7/12)/2) (margin/2))
  have hη : 0<η := by
    apply lt_min
    · exact div_pos (sub_pos.mpr hHsort) (by norm_num)
    · apply lt_min
      · apply div_pos _ (by norm_num)
        linarith
      · exact div_pos hcontact.2.1 (by norm_num)
  have hηsort : η≤(H₀.a-H₀.y)/2 := min_le_left _ _
  have hηcore : η≤(H₀.a-7/12)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηslack : η≤margin/2 := (min_le_right _ _).trans (min_le_right _ _)
  let H' : SignedPoint := ⟨H₀.a-η,H₀.y⟩
  have hHs' : H'.Sorted := by
    constructor
    · dsimp [H']; linarith
    · dsimp [H']; rw [abs_of_pos hHy]; linarith
  have hHcore' : H'.AvoidsCore := by
    have ha : 7/12≤H'.a := by dsimp [H']; linarith
    unfold SignedPoint.AvoidsCore SignedPoint.coreDistance
    rw [max_eq_left (by linarith : 0≤H'.a-1/2)]
    have h1 : (1/12:ℝ)≤H'.a-1/2 := by linarith
    have h2 := pow_le_pow_left₀ (by norm_num) h1 2
    linarith [sq_nonneg (max (|H'.y|-1/2) 0)]
  have hHloss : H'.circle<H.circle := by
    have hp : 0<η*(2*(H₀.a+1/2)-η) := by
      apply mul_pos hη
      linarith
    have heq : H₀.circle=H.circle := hHcircle
    rw [← heq]
    dsimp [H',SignedPoint.circle]
    linarith
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hD := I.path_cap hq ⟨O.angle_mem.1,O.angle_mem.2.le⟩
  obtain ⟨hGs,hGcore,hGavoid,hGinside⟩ := point_geometric
    ⟨hPlo,hPup⟩ ⟨O.angle_mem.1,O.angle_mem.2.le.trans I.tilt_cap⟩
    (by linarith [hD.1]) (I.cuts hq).2.2.2.2.2.2.2
  have hGnegative : G₀.y<0 := by dsimp [G₀,point,P,x]; linarith [hD.1]
  have hHnondiagonal : |H'.y|<H'.a := by
    dsimp [H']; rw [abs_of_pos hHy]; linarith
  have hGnondiagonal : |G₀.y|<G₀.a := by
    rw [abs_of_neg hGnegative]
    dsimp [G₀,point,P,x]
    linarith [hD.2.1]
  have hHG0 : zeroFeasible H' G₀ 0 0 := by
    simp [zeroFeasible,zeroProjection,H',H₀,G₀,movingAnchor,anchorAt,point]
    ring_nf
    norm_num
  have hEH : quarterFeasible E H' (e+x) j := by
    have hm : margin=quarterProjection E H₀ (e+x) j-edgeWidth (e+x) := rfl
    rcases hj with hj | hj
    · subst j
      have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one (e+x)) hη.le
      change edgeWidth (e+x)≤quarterProjection E H' (e+x) 0
      simp only [quarterProjection,Matrix.cons_val_zero,H'] at hm ⊢
      linarith [hcontact.2.1]
    · subst j
      change edgeWidth (e+x)≤quarterProjection E H' (e+x) 1
      simp only [quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero,H'] at hm ⊢
      linarith [hcontact.2.1]
  exact ⟨{
    angle := x
    angle_mem := O.angle_mem
    Hpoint := H'
    Gpoint := G₀
    H_sorted := hHs'
    G_sorted := hGs
    H_core := hHcore'
    G_core := hGcore
    H_circle_loss := hHloss
    G_inside := hGinside
    H_high := hHhigh
    H_primary_lt_one := by dsimp [H']; linarith
    G_negative := hGnegative
    H_nondiagonal := hHnondiagonal
    G_nondiagonal := hGnondiagonal
    G_primary := rfl
    H_tangent_decreases := hHtangentStrict
    HG0 := hHG0
    HG2 := (zero_owner_tie _ _).1 hHG0
    GA0 := O.hard
    EH := hEH
    EH_error := hcontact.1
    EH_short := hcontact.2.2 }⟩

namespace FirstMixedEndpoint

variable {q t e : ℝ} {H G A E : SignedPoint} {I : Source q t H G A}

end FirstMixedEndpoint
end AlignedNegative
end SquaresInCircles.Eight
end
end
end

section
/-!
## First negative-primary conversion without a BT2 premise

The resulting cycle (`FirstGEntry`, `first_negative_g_mixed_entry`) keeps a high H anchor, the
original right-hand centers and frames, and all original BT axes (`FirstGEntry.BT_unchanged`).
Its E point stays on the boundary, on its circle or the core boundary. Thus a second
negative-primary conversion can start from this endpoint directly.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace AlignedNegative

structure FirstGEntry (q : ℝ) (C : SignedCycle) (w : C.Witnesses) where
  cycle : SignedCycle
  necessary : cycle.Necessary q
  normal : cycle.NormalAnchors
  witnesses : cycle.Witnesses
  zero_signs : cycle.ZeroSignImplications witnesses
  ordered : cycle.Ordered
  E_nonpos : (cycle.point E).y≤0
  E_boundary : (cycle.point E).Boundary q
  GA_hard : cycle.Feasible G 0
  H_high : 211/250<(cycle.point H).y
  H_primary_lt_one : (cycle.point H).a<1
  aligned : cycle.theta H=cycle.theta G
  above_A : C.theta A≤cycle.theta H
  H_retreat : cycle.theta H<C.theta H
  HG_original : cycle.Feasible H (w.owner H)
  H_nondiagonal : |(cycle.point H).y|<(cycle.point H).a
  G_nondiagonal : |(cycle.point G).y|<(cycle.point G).a
  H_circle_loss : (cycle.point H).circle<(C.point H).circle
  anchor_nonincrease : AnchorNonincrease C cycle
  strict_anchor_loss : StrictAnchorLoss C cycle
  right_owners : witnesses.owner B=w.owner B ∧ witnesses.owner T=w.owner T ∧
    witnesses.owner D=w.owner D
  unchanged : ∀ i, i≠H → i≠G → i≠E →
    cycle.point i=C.point i ∧ cycle.theta i=C.theta i

namespace FirstMixedEndpoint

variable {q : ℝ} {C : SignedCycle} {j : Fin 4}
variable {I : Source q (C.theta H-C.theta A) (C.point H) (C.point G) (C.point A)}

def cycle (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j) : SignedCycle :=
  replaceHG C O.Hpoint O.Gpoint O.angle

theorem unchanged (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (i : Vertex) (hiH : i≠H) (hiG : i≠G) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i :=
  replaceHG_unchanged C O.Hpoint O.Gpoint O.angle i hiH hiG

theorem necessary (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (hn : C.Necessary q) : O.cycle.Necessary q :=
  replaceHG_necessary hn O.H_sorted (O.H_circle_loss.le.trans (hn.contained H))
    O.H_core O.G_sorted O.G_inside.le O.G_core.ge
    ⟨O.angle_mem.1,O.angle_mem.2.le⟩

theorem normal (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (ha : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · have hh : 0≤O.Hpoint.y := by linarith [O.H_high]
    simpa [cycle,replaceHG,replacePoint,H,G] using hh
  · simpa [cycle,replaceHG,replacePoint,H,G,A] using ha.A_nonneg
  · simpa [cycle,replaceHG,replacePoint,H,G,B] using ha.B_nonpos
  · simpa [cycle,replaceHG,replacePoint,H,G,D] using ha.D_nonpos

def witnesses (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (hj : j=0 ∨ j=1) (w : C.Witnesses) : O.cycle.Witnesses where
  owner := ![w.owner H,0,w.owner A,w.owner B,w.owner T,w.owner D,j]
  feasible i := by
    fin_cases i
    · apply (replaceHG_HG C O.Hpoint O.Gpoint O.angle _).2
      have hh : w.owner H=0 ∨ w.owner H=2 := by
        simpa [SignedCycle.normalOwners,H] using w.allowed H
      rcases hh with hh | hh
      · simpa [hh] using O.HG0
      · simpa [hh] using O.HG2
    · exact (replaceHG_GA C O.Hpoint O.Gpoint O.angle 0).2 O.GA0
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle A
        (by decide) _).2 (w.feasible A)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle B
        (by decide) _).2 (w.feasible B)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle T
        (by decide) _).2 (w.feasible T)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle D
        (by decide) _).2 (w.feasible D)
    · exact (replaceHG_EH C O.Hpoint O.Gpoint O.angle j).2 O.EH
  allowed i := by
    fin_cases i
    · simpa [H] using w.allowed H
    · norm_num [SignedCycle.normalOwners,G]
    · simpa [A] using w.allowed A
    · simpa [B] using w.allowed B
    · simpa [T] using w.allowed T
    · simpa [D] using w.allowed D
    · simpa [SignedCycle.normalOwners,E] using hj

theorem zero_signs (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (hj : j=0 ∨ j=1) (w : C.Witnesses) (hz : C.ZeroSignImplications w) :
    O.cycle.ZeroSignImplications (O.witnesses hj w) := by
  constructor
  · intro _
    simpa [cycle,replaceHG,replacePoint] using O.G_negative
  · intro hh
    have hT : w.owner T=0 := by simpa [witnesses,T] using hh
    rw [(O.unchanged T (by decide) (by decide)).1]
    exact hz.TD_canceling hT

theorem anchor_nonincrease
    (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j) :
    AnchorNonincrease C O.cycle := by
  intro i hi
  by_cases hH : i=H
  · subst i
    simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss.le
  · have hG : i≠G := by
      rintro rfl
      simp [anchorVertices,H,A,B,D,E,G] at hi
    rw [(O.unchanged i hH hG).1]

theorem strict_anchor_loss
    (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j) :
    StrictAnchorLoss C O.cycle := by
  refine ⟨H,by simp [anchorVertices],?_⟩
  simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss

def entry (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (hj : j=0 ∨ j=1) (hn : C.Necessary q) (hq : q≤qCap)
    (ha : C.NormalAnchors) (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0) (hrE : (C.point E).Boundary q) : FirstGEntry q C w where
  cycle := O.cycle
  necessary := O.necessary hn
  normal := O.normal ha
  witnesses := O.witnesses hj w
  zero_signs := O.zero_signs hj w hz
  ordered := SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses hj w) (O.zero_signs hj w hz)
  E_nonpos := by rw [(O.unchanged E (by decide) (by decide)).1]; exact hyE
  E_boundary := by rw [(O.unchanged E (by decide) (by decide)).1]; exact hrE
  GA_hard := (replaceHG_GA C O.Hpoint O.Gpoint O.angle 0).2 O.GA0
  H_high := by simpa [cycle,replaceHG,replacePoint,H,G] using O.H_high
  H_primary_lt_one := by simpa [cycle,replaceHG,replacePoint,H,G] using O.H_primary_lt_one
  aligned := by simp [cycle,replaceHG,replacePoint,H,G]
  above_A := by
    have hh : C.theta A≤C.theta A+O.angle := by linarith [O.angle_mem.1]
    simpa [cycle,replaceHG,replacePoint,H,G] using hh
  H_retreat := by
    have hh : C.theta A+O.angle<C.theta H := by linarith [O.angle_mem.2]
    simpa [cycle,replaceHG,replacePoint,H,G] using hh
  HG_original := (O.witnesses hj w).feasible H
  H_nondiagonal := by simpa [cycle,replaceHG,replacePoint,H,G] using O.H_nondiagonal
  G_nondiagonal := by simpa [cycle,replaceHG,replacePoint] using O.G_nondiagonal
  H_circle_loss := by simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss
  anchor_nonincrease := O.anchor_nonincrease
  strict_anchor_loss := O.strict_anchor_loss
  right_owners := ⟨rfl,rfl,rfl⟩
  unchanged := fun i hiH hiG _ => O.unchanged i hiH hiG

end FirstMixedEndpoint

theorem first_negative_g_mixed_entry {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0) (hrE : (C.point E).Boundary q)
    (halign : C.theta G=C.theta H) (ht : C.theta A<C.theta H)
    (hyG : (C.point G).y≤0) (hGA : C.Feasible G 1)
    (hnot : ¬C.Feasible G 0) {j : Fin 4} (hj : j=0 ∨ j=1)
    (hEH : C.Feasible E j) (hshort : j=1 → |C.theta H-C.theta E|≤11/50) :
    Nonempty (FirstGEntry q C w) := by
  let I := sourceOfCycle hn ha w halign ht hyG hGA hnot
  have heq : (C.theta A-C.theta E)+(C.theta H-C.theta A)=C.theta H-C.theta E := by ring
  have he : |(C.theta A-C.theta E)+(C.theta H-C.theta A)|≤7/10 := by
    rw [heq]
    exact hn.spread H E
  have hf : quarterFeasible (C.point E) (C.point H)
      ((C.theta A-C.theta E)+(C.theta H-C.theta A)) j := by
    rw [heq]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  obtain ⟨O⟩ := I.first_mixed_endpoint hq (hn.sorted E) (hn.contained E) hyE hj he
    (by intro hj1; rw [heq]; exact hshort hj1) hf
  exact ⟨O.entry hj hn hq ha w hz hyE hrE⟩

namespace FirstGEntry

variable {q : ℝ} {C : SignedCycle} {w : C.Witnesses}

theorem BT_unchanged (J : FirstGEntry q C w) (j : Fin 4) :
    J.cycle.Feasible B j ↔ C.Feasible B j := by
  have hB := J.unchanged B (by decide) (by decide) (by decide)
  have hT := J.unchanged T (by decide) (by decide) (by decide)
  have hn : next B=T := by decide
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,delta,hn,
    hB.1,hB.2,hT.1,hT.2]

def prepend_outside (I : SignedCycle.NormalizedBoundaryInput q) (hq : q≤qCap)
    (O : OutsideE.CycleEndpoint q I.cycle (I.witnesses.owner D))
    (J : FirstGEntry q (O.boundaryInput I hq).cycle (O.boundaryInput I hq).witnesses) :
    FirstGEntry q I.cycle I.witnesses where
  cycle := J.cycle
  necessary := J.necessary
  normal := J.normal
  witnesses := J.witnesses
  zero_signs := J.zero_signs
  ordered := J.ordered
  E_nonpos := J.E_nonpos
  E_boundary := J.E_boundary
  GA_hard := J.GA_hard
  H_high := J.H_high
  H_primary_lt_one := J.H_primary_lt_one
  aligned := J.aligned
  above_A := by
    have hh := J.above_A
    change O.cycle.theta A≤J.cycle.theta H at hh
    rwa [(O.unchanged A (by decide)).2] at hh
  H_retreat := by
    have hh := J.H_retreat
    change J.cycle.theta H<O.cycle.theta H at hh
    rwa [(O.unchanged H (by decide)).2] at hh
  HG_original := by
    simpa [OutsideE.CycleEndpoint.boundaryInput,OutsideE.CycleEndpoint.witnesses,H,E]
      using J.HG_original
  H_nondiagonal := J.H_nondiagonal
  G_nondiagonal := J.G_nondiagonal
  H_circle_loss := by
    have hh := J.H_circle_loss
    change (J.cycle.point H).circle<(O.cycle.point H).circle at hh
    rwa [(O.unchanged H (by decide)).1] at hh
  anchor_nonincrease := O.anchor_nonincrease.trans J.anchor_nonincrease
  strict_anchor_loss := O.anchor_nonincrease.then_strict J.strict_anchor_loss
  right_owners := by
    simpa [OutsideE.CycleEndpoint.boundaryInput,OutsideE.CycleEndpoint.witnesses,B,T,D,E]
      using J.right_owners
  unchanged := by
    intro i hiH hiG hiE
    have hJ := J.unchanged i hiH hiG hiE
    exact ⟨hJ.1.trans (O.unchanged i hiE).1,hJ.2.trans (O.unchanged i hiE).2⟩

end FirstGEntry

end AlignedNegative
end SquaresInCircles.Eight
end
end
end

section
/-!
## The four double-increment words are impossible without tables

The complete continuous estimates for increments zero, one and two apply
to the actual source cycle and its original weak owner. Each original
vertex label cancels once. The remaining argument is the exact integer
classification already proved for quarter lifts, followed by a rational
comparison with `2*pi`.

Physical dihedral normalization is used only to express the four excluded
representatives; it preserves every original square and separator.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.QuarterWordGeometry

open Arithmetic WordProblems

/-- The full common cost inequality, with no radial, sign or owner case
left as an external assumption. -/
theorem common_pair (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (commonGamma (F.word hgap pi_lt_22_over_7 i):ℝ)<
      phaseValue F hgap i+commonMarker C i-commonMarker C (next i) := by
  generalize hk : F.word hgap pi_lt_22_over_7 i=k
  fin_cases k
  · simpa [commonGamma] using CommonQuarter.actual_zero C F hgap i hk j hj
  · simpa [commonGamma] using CommonQuarter.actual_one C F hgap i hk j hj
  · simpa [commonGamma] using CommonQuarter.actual_jump_two C F hgap i hk j hj

theorem commonGamma_numerator (k : Fin 3) :
    (commonGamma k:ℝ)=(doubleWordCostNumerator k:ℝ)/10000 := by
  fin_cases k <;> norm_num [commonGamma,doubleWordCostNumerator]

/-- Every actual cycle is binary: the four zero, two one and one double
costs would exceed its exact full-turn budget. -/
theorem no_double (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) :
    ¬∃i,F.word hgap pi_lt_22_over_7 i=2 := by
  apply no_double_word_of_cost_bound (F.word hgap pi_lt_22_over_7)
    (F.word_admissible hgap pi_lt_22_over_7)
    (fun i => phaseValue F hgap i+commonMarker C i-commonMarker C (next i))
  · intro i
    obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
    have hh := common_pair C F hgap i j (by simpa [← hj] using C.feasible i)
    rw [commonGamma_numerator] at hh
    exact hh.le
  · exact (marker_budget C F hgap (commonMarker C)).le
  · exact pi_lt_22_over_7

/-- All four representatives containing a double are excluded under every
actual cyclic relabeling and reflected orientation. -/
theorem four_double_exclusions (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (j : Fin 4) :
    ¬(F.word hgap pi_lt_22_over_7).DihedralEquivalent
      (quarterRepresentatives ⟨j.val,by omega⟩) := by
  intro heq
  obtain ⟨G,hword⟩ := normalize_word C F hgap
    (quarterRepresentatives ⟨j.val,by omega⟩) heq
  let D := G.boundary C
  let H := F.act G
  have hg : ∀i,19/25<angleGap D.beta i := boundary_gap_lower D le_rfl
  have he : H.word hg pi_lt_22_over_7=quarterRepresentatives ⟨j.val,by omega⟩ := hword
  apply no_double D H hg
  fin_cases j
  · exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩
  · exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩
  · exact ⟨4,by rw [he]; norm_num [quarterRepresentatives]⟩
  · exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩

/-- The actual physical word is now one of exactly the three binary
classes. The two remaining wrong binary classes are stated explicitly. -/
theorem three_binary_classes (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) :
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent (wrongWord .short) ∨
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent (wrongWord .second) ∨
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent candidateQuarterWord := by
  obtain ⟨j,hj⟩ := quarter_word_complete_classification _
    (F.word_admissible hgap pi_lt_22_over_7)
  have hs : wrongWord .short=quarterRepresentatives 4 := by
    funext i
    fin_cases i <;> rfl
  have hsec : wrongWord .second=quarterRepresentatives 5 := by
    funext i
    fin_cases i <;> rfl
  fin_cases j
  · exact (four_double_exclusions C F hgap 0 hj).elim
  · exact (four_double_exclusions C F hgap 1 hj).elim
  · exact (four_double_exclusions C F hgap 2 hj).elim
  · exact (four_double_exclusions C F hgap 3 hj).elim
  · left
    rw [hs]
    exact hj
  · right
    left
    rw [hsec]
    exact hj
  · right
    right
    exact hj

end SquaresInCircles.Eight.QuarterWordGeometry
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
namespace AlignedNegative

theorem aligned_negative_first_entry_of_span {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q) (hqL : qLow≤q) (hqU : q≤qCap)
    (halign : I.cycle.theta G=I.cycle.theta H)
    (ht : I.cycle.theta A<I.cycle.theta H)
    (hyG : (I.cycle.point G).y≤0) (hGA : I.cycle.Feasible G 1)
    (hnot : ¬I.cycle.Feasible G 0)
    (hspan : I.cycle.theta H-I.cycle.theta D≤11/50) :
    Nonempty (FirstGEntry q I.cycle I.witnesses) := by
  let S := sourceOfCycle I.necessary I.anchors_normal I.witnesses halign ht hyG hGA hnot
  by_cases hEH0 : I.cycle.Feasible E 0
  · exact first_negative_g_mixed_entry I.necessary hqU I.anchors_normal I.witnesses
      I.zero_signs I.E_nonpos (I.radial E) halign ht hyG hGA hnot
      (Or.inl rfl) hEH0 (by norm_num)
  have hEH1 : I.cycle.Feasible E 1 := by
    have hj : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [SignedCycle.normalOwners,E] using I.witnesses.allowed E
    rcases hj with hj | hj
    · exact False.elim (hEH0 (by simpa [hj] using I.witnesses.feasible E))
    · simpa [hj] using I.witnesses.feasible E
  have hpwidth : |I.cycle.theta H-I.cycle.theta E|≤7/10 := I.necessary.spread H E
  have hpactual : quarterFeasible (I.cycle.point E) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta E) 1 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH1
  have hppos := S.eh1_error_positive hqU (I.necessary.sorted E) I.E_nonpos hpwidth hpactual
  by_cases hpshort : I.cycle.theta H-I.cycle.theta E≤11/50
  · have hshort : |I.cycle.theta H-I.cycle.theta E|≤11/50 := by
      rwa [abs_of_pos hppos]
    exact first_negative_g_mixed_entry I.necessary hqU I.anchors_normal I.witnesses
      I.zero_signs I.E_nonpos (I.radial E) halign ht hyG hGA hnot
      (Or.inr rfl) hEH1 (fun _ => hshort)
  have hplong := lt_of_not_ge hpshort
  have hn : I.cycle.theta E<I.cycle.theta D := by linarith
  have hcuts := S.cuts hqU
  obtain ⟨O⟩ := OutsideE.cycle_endpoint I hqL hqU hcuts.2.2.2.1 hcuts.2.2.2.2.1
    hn hplong hEH1
  let K := O.boundaryInput I hqU
  have hKH : K.cycle.point H=I.cycle.point H ∧ K.cycle.theta H=I.cycle.theta H :=
    O.unchanged H (by decide)
  have hKG : K.cycle.point G=I.cycle.point G ∧ K.cycle.theta G=I.cycle.theta G :=
    O.unchanged G (by decide)
  have hKA : K.cycle.point A=I.cycle.point A ∧ K.cycle.theta A=I.cycle.theta A :=
    O.unchanged A (by decide)
  have hKal : K.cycle.theta G=K.cycle.theta H := by rw [hKG.2,hKH.2]; exact halign
  have hKt : K.cycle.theta A<K.cycle.theta H := by rw [hKA.2,hKH.2]; exact ht
  have hKyG : (K.cycle.point G).y≤0 := by rw [hKG.1]; exact hyG
  have hKGA : K.cycle.Feasible G 1 := (O.other_feasible G (by decide) (by decide) 1).2 hGA
  have hKnot : ¬K.cycle.Feasible G 0 := fun hh =>
    hnot ((O.other_feasible G (by decide) (by decide) 0).1 hh)
  rcases O.terminal_actual with hstop | hstop | hstop
  · obtain ⟨J⟩ := first_negative_g_mixed_entry K.necessary hqU K.anchors_normal K.witnesses
      K.zero_signs K.E_nonpos (K.radial E) hKal hKt hKyG hKGA hKnot
      (Or.inl rfl) hstop (by norm_num)
    exact ⟨J.prepend_outside I hqU O⟩
  · have hKEH : K.cycle.Feasible E 1 := (O.EH_actual 1).2 O.EH1
    obtain ⟨J⟩ := first_negative_g_mixed_entry K.necessary hqU K.anchors_normal K.witnesses
      K.zero_signs K.E_nonpos (K.radial E) hKal hKt hKyG hKGA hKnot
      (Or.inr rfl) hKEH (fun _ => hstop)
    exact ⟨J.prepend_outside I hqU O⟩
  · exact False.elim ((not_lt_of_ge hspan) hstop.2)

end AlignedNegative
end SquaresInCircles.Eight
end
end
end
