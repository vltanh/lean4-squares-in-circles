module

public import SquaresInCircles.Eight.TableFree.AlignedNegativeEH0
public import SquaresInCircles.Eight.TableFree.BoundaryPreprocessing

/-!
# Actual seven-cycle assembly of the retained-EH0 negative conversion

Uncompiled source. The H/G contact motion is inserted at its actual physical
frames. All other centers and frames, including E, are unchanged. The old
weak HG witness is retained even when it is owner 2. The new necessary cycle
has proved physical order, two strictly nondiagonal changed centers, and a
strict loss on H's own original circle.

An available BT2 axis then gives a genuine hard-class descendant. The proof
also works after earlier anchor losses: only containment and the actual
source radial alternative for E are used, and no anchor is lifted to q.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace AlignedNegative

/-- Both changed physical frames have tilt x above the retained A frame. -/
def replaceHG (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ) : SignedCycle :=
  replacePoint (replacePoint C H pH (C.theta A+x)) G pG (C.theta A+x)

theorem replaceHG_unchanged (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ)
    (i : Vertex) (hH : i≠H) (hG : i≠G) :
    (replaceHG C pH pG x).point i=C.point i ∧
      (replaceHG C pH pG x).theta i=C.theta i := by
  simp [replaceHG,replacePoint,hH,hG]

theorem replaceHG_HG (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ)
    (j : Fin 4) :
    (replaceHG C pH pG x).Feasible H j ↔ zeroFeasible pH pG 0 j := by
  simp [replaceHG,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,G,A,zeroFeasible,sub_nonneg]

theorem replaceHG_GA (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ)
    (j : Fin 4) :
    (replaceHG C pH pG x).Feasible G j ↔
      quarterFeasible pG (C.point A) (-x) j := by
  simp [replaceHG,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,G,A,quarterFeasible,sub_nonneg,
    show C.theta A-(C.theta A+x)= -x by ring]

theorem replaceHG_EH (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ)
    (j : Fin 4) :
    (replaceHG C pH pG x).Feasible E j ↔
      quarterFeasible (C.point E) pH (C.theta A-C.theta E+x) j := by
  rw [show C.theta A-C.theta E+x=C.theta A+x-C.theta E by ring]
  simp [replaceHG,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,G,A,E,quarterFeasible,sub_nonneg]

/-- In particular AB, BT, TD, and DE retain every original weak owner. -/
theorem replaceHG_other_feasible (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ)
    (i : Vertex) (hi : i≠H ∧ i≠G ∧ i≠E) (j : Fin 4) :
    (replaceHG C pH pG x).Feasible i j ↔ C.Feasible i j := by
  have hnH : next i≠H := by
    fin_cases i <;> norm_num [next,H,G,E] at hi ⊢
  have hnG : next i≠G := by
    fin_cases i <;> norm_num [next,H,G,E] at hi ⊢
  simp [replaceHG,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,delta,hi.1,hi.2.1,hnH,hnG]

private theorem replacement_frame_range {C : SignedCycle} {x : ℝ}
    (hx : x∈Icc 0 (C.theta H-C.theta A)) :
    C.theta A+x∈Icc (min (C.theta A) (C.theta H))
      (max (C.theta A) (C.theta H)) := by
  have hAH : C.theta A≤C.theta H := by linarith [hx.1,hx.2]
  simp only [min_eq_left hAH,max_eq_right hAH,mem_Icc]
  constructor <;> linarith [hx.1,hx.2]

theorem replaceHG_necessary {q x : ℝ} {C : SignedCycle} {pH pG : SignedPoint}
    (hn : C.Necessary q)
    (hHs : pH.Sorted) (hHc : pH.Contained q) (hHcore : pH.AvoidsCore)
    (hGs : pG.Sorted) (hGc : pG.Contained q) (hGcore : pG.AvoidsCore)
    (hx : x∈Icc 0 (C.theta H-C.theta A)) :
    (replaceHG C pH pG x).Necessary q := by
  have hnH := SignedCycle.necessary_replace_clamped (v := H) (a := A) (b := H)
    hn hHs hHc hHcore (Or.inr (replacement_frame_range hx))
  have hframe : C.theta A+x∈
      Icc (min ((replacePoint C H pH (C.theta A+x)).theta H)
          ((replacePoint C H pH (C.theta A+x)).theta H))
        (max ((replacePoint C H pH (C.theta A+x)).theta H)
          ((replacePoint C H pH (C.theta A+x)).theta H)) := by
    simp [replacePoint]
  exact SignedCycle.necessary_replace_clamped (v := G) (a := H) (b := H)
    hnH hGs hGc hGcore (Or.inr hframe)

theorem replaceHG_strictSpread {x : ℝ} {C : SignedCycle} (pH pG : SignedPoint)
    (hs : C.StrictSpread) (hx : x∈Icc 0 (C.theta H-C.theta A)) :
    (replaceHG C pH pG x).StrictSpread := by
  have hsH := SignedCycle.strictSpread_replace_clamped
    (v := H) (a := A) (b := H) (p := pH) hs
    (Or.inr (replacement_frame_range hx))
  apply SignedCycle.strictSpread_replace_clamped
    (v := G) (a := H) (b := H) (p := pG) hsH
  right
  simp [replacePoint]

/-- The local source is extracted from actual retained cycle witnesses.
Neither a normalized contact point nor a feasible path is an input. -/
def sourceOfCycle {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (ha : C.NormalAnchors) (w : C.Witnesses)
    (halign : C.theta G=C.theta H) (ht : C.theta A<C.theta H)
    (hy : (C.point G).y≤0) (hGA : C.Feasible G 1)
    (hnot : ¬C.Feasible G 0) :
    Source q (C.theta H-C.theta A) (C.point H) (C.point G) (C.point A) := by
  have hδH : delta C.theta H=0 := by
    simpa [delta,next,H,G] using sub_eq_zero.mpr halign
  have hδG : delta C.theta G= -(C.theta H-C.theta A) := by
    simp only [delta,next,G]
    change C.theta A-C.theta G= -(C.theta H-C.theta A)
    rw [halign]
    ring
  have hHG : zeroFeasible (C.point H) (C.point G) 0 (w.owner H) := by
    have hh := w.feasible H
    change 0≤C.slack H (w.owner H) at hh
    simpa [SignedCycle.slack,SignedCycle.edge,word,next,H,G,hδH,zeroFeasible]
      using sub_nonneg.mp hh
  have hHG0 : zeroFeasible (C.point H) (C.point G) 0 0 := by
    have hj : w.owner H=0 ∨ w.owner H=2 := by
      simpa [SignedCycle.normalOwners,H] using w.allowed H
    rcases hj with hj | hj
    · simpa [hj] using hHG
    · exact (zero_owner_tie _ _).2 (by simpa [hj] using hHG)
  exact {
    H_sorted := hn.sorted H
    G_sorted := hn.sorted G
    A_sorted := hn.sorted A
    H_contained := hn.contained H
    G_contained := hn.contained G
    A_contained := hn.contained A
    H_core := hn.core H
    G_core := hn.core G
    A_core := hn.core A
    H_nonneg := ha.H_nonneg
    G_nonpos := hy
    A_nonneg := ha.A_nonneg
    tilt_pos := sub_pos.mpr ht
    tilt_cap := by
      have hh := hn.spread H A
      dsimp [frameCap] at hh
      exact (le_abs_self _).trans hh
    HG := hHG0
    GA := by
      change 0≤C.slack G 1 at hGA
      simpa [SignedCycle.slack,SignedCycle.edge,word,next,G,A,hδG,quarterFeasible]
        using sub_nonneg.mp hGA
    no_hard := by
      intro hh
      apply hnot
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        word,next,G,A,hδG,quarterFeasible] using sub_nonneg.mpr hh }

namespace LowMixedEndpoint

variable {q : ℝ} {C : SignedCycle}
variable {I : Source q (C.theta H-C.theta A) (C.point H) (C.point G) (C.point A)}

def cycle (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E)) : SignedCycle :=
  replaceHG C O.Hpoint O.Gpoint O.angle

theorem unchanged (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (i : Vertex) (hiH : i≠H) (hiG : i≠G) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i :=
  replaceHG_unchanged C O.Hpoint O.Gpoint O.angle i hiH hiG

theorem necessary (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hn : C.Necessary q) : O.cycle.Necessary q :=
  replaceHG_necessary hn O.H_sorted (O.H_circle_loss.le.trans (hn.contained H))
    O.H_core O.G_sorted O.G_inside.le O.G_core.ge
    ⟨O.angle_mem.1,O.angle_mem.2.le⟩

theorem normal (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (ha : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · simpa [cycle,replaceHG,replacePoint,H,G] using O.H_positive.le
  · simpa [cycle,replaceHG,replacePoint,H,G,A] using ha.A_nonneg
  · simpa [cycle,replaceHG,replacePoint,H,G,B] using ha.B_nonpos
  · simpa [cycle,replaceHG,replacePoint,H,G,D] using ha.D_nonpos

/-- GA and EH use their newly proved hard and retained axes. Every other
selected normal, including the original weak HG owner, stays available. -/
def witnesses (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (w : C.Witnesses) : O.cycle.Witnesses where
  owner := ![w.owner H,0,w.owner A,w.owner B,w.owner T,w.owner D,0]
  feasible i := by
    fin_cases i
    · apply (replaceHG_HG C O.Hpoint O.Gpoint O.angle _).2
      have hj : w.owner H=0 ∨ w.owner H=2 := by
        simpa [SignedCycle.normalOwners,H] using w.allowed H
      rcases hj with hj | hj
      · simpa [hj] using O.HG0
      · simpa [hj] using O.HG2
    · exact (replaceHG_GA C O.Hpoint O.Gpoint O.angle 0).2 O.GA0
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle A
        (by decide) _).2 (w.feasible A)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle B
        (by decide) _).2 (w.feasible B)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle T
        (by decide) _).2 (w.feasible T)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle D
        (by decide) _).2 (w.feasible D)
    · exact (replaceHG_EH C O.Hpoint O.Gpoint O.angle 0).2 O.EH0
  allowed i := by
    fin_cases i
    · simpa [H] using w.allowed H
    · norm_num [SignedCycle.normalOwners,G]
    · simpa [A] using w.allowed A
    · simpa [B] using w.allowed B
    · simpa [T] using w.allowed T
    · simpa [D] using w.allowed D
    · norm_num [SignedCycle.normalOwners,E]

theorem zero_signs (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) :
    O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro _
    simpa [cycle,replaceHG,replacePoint] using O.G_negative
  · intro hh
    have hj : w.owner T=0 := by simpa [witnesses,T] using hh
    rw [(O.unchanged T (by decide) (by decide)).1]
    exact hz.TD_canceling hj

theorem ordered (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) : O.cycle.Ordered :=
  SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses w) (O.zero_signs w hz)

theorem strict_spread
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hs : C.StrictSpread) : O.cycle.StrictSpread :=
  replaceHG_strictSpread O.Hpoint O.Gpoint hs ⟨O.angle_mem.1,O.angle_mem.2.le⟩

/-- The two signed budgets lose exactly the physical frame movement. The
nonnegative EH error is proved at the constructed endpoint, not imposed on
an arbitrary interpolation. -/
theorem variations
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (halign : C.theta G=C.theta H) :
    positiveVariation C.theta-positiveVariation O.cycle.theta=
        C.theta H-C.theta A-O.angle ∧
      negativeVariation C.theta-negativeVariation O.cycle.theta=
        C.theta H-C.theta A-O.angle := by
  have hEHnew : 0≤C.theta A+O.angle-C.theta E := by
    linarith [O.EH_error.1]
  have hEHold : 0≤C.theta H-C.theta E := by
    linarith [O.angle_mem.2]
  have hGAold : positivePart (C.theta A-C.theta H)=0 := by
    exact max_eq_right (by linarith [I.tilt_pos])
  have hGAnew : positivePart (C.theta A-(C.theta A+O.angle))=0 := by
    exact max_eq_right (by linarith [O.angle_mem.1])
  have hEHold' : positivePart (C.theta H-C.theta E)=C.theta H-C.theta E :=
    max_eq_left hEHold
  have hEHnew' : positivePart (C.theta A+O.angle-C.theta E)=
      C.theta A+O.angle-C.theta E := max_eq_left hEHnew
  have hp : positiveVariation C.theta-positiveVariation O.cycle.theta=
      C.theta H-C.theta A-O.angle := by
    simp [positiveVariation,Fin.sum_univ_succ,delta,next,cycle,replaceHG,
      replacePoint,H,G,A,B,T,D,E,Function.update_apply,halign,
      hGAold,hGAnew,hEHold',hEHnew']
    ring
  constructor
  · exact hp
  · simpa only [← variations_equal C.theta,← variations_equal O.cycle.theta] using hp

theorem variation_strict
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (halign : C.theta G=C.theta H) :
    positiveVariation O.cycle.theta<positiveVariation C.theta ∧
      negativeVariation O.cycle.theta<negativeVariation C.theta := by
  have hh := O.variations halign
  constructor <;> linarith [O.angle_mem.2,hh.1,hh.2]

theorem anchor_nonincrease
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E)) :
    AnchorNonincrease C O.cycle := by
  intro i hi
  by_cases hH : i=H
  · subst i
    simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss.le
  · have hG : i≠G := by
      simp [anchorVertices,H,A,B,D,E,G] at hi ⊢
      omega
    rw [(O.unchanged i hH hG).1]

theorem strict_anchor_loss
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E)) :
    StrictAnchorLoss C O.cycle := by
  refine ⟨H,by simp [anchorVertices],?_⟩
  simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss

/-- The actual E point is retained. If its radial alternative was proved
before this move, decreasing the positive H tangent preserves that same
alternative even when H was already strictly inside the circle. -/
theorem radial_alternative
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hr : (C.point E).a≤7/12 ∨
      max |(C.point H).y| |(C.point D).y|≤(C.point E).a) :
    (O.cycle.point E).a≤7/12 ∨
      max |(O.cycle.point H).y| |(O.cycle.point D).y|≤(O.cycle.point E).a := by
  have hHy : |O.Hpoint.y|≤|(C.point H).y| := by
    rw [abs_of_pos O.H_positive,abs_of_nonneg I.H_nonneg]
    exact O.H_tangent_decreases.le
  rcases hr with hr | hr
  · left
    simpa [cycle,replaceHG,replacePoint,H,G,E] using hr
  · right
    have hh : max |O.Hpoint.y| |(C.point D).y|≤(C.point E).a :=
      (max_le_max_right _ hHy).trans hr
    simpa [cycle,replaceHG,replacePoint,H,G,D,E] using hh

def hardInput (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hn : C.Necessary q) (ha : C.NormalAnchors) (w : C.Witnesses)
    (hz : C.ZeroSignImplications w) (hyE : (C.point E).y≤0)
    (hBT : C.Feasible B 2)
    (hr : (C.point E).a≤7/12 ∨
      max |(C.point H).y| |(C.point D).y|≤(C.point E).a) :
    SignedCycle.HardInput q where
  cycle := O.cycle
  necessary := O.necessary hn
  anchors_normal := O.normal ha
  E_nonpos := by rw [(O.unchanged E (by decide) (by decide)).1]; exact hyE
  witnesses := O.witnesses w
  GA_hard := (replaceHG_GA C O.Hpoint O.Gpoint O.angle 0).2 O.GA0
  BT_hard := (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle B
    (by decide) 2).2 hBT
  zero_signs := O.zero_signs w hz
  E_radial := O.radial_alternative hr

end LowMixedEndpoint

/-- The retained-EH0 aligned negative branch reaches the actual hard class
at the original q, with a strict original-anchor loss and no changed E.
All endpoint and ordering facts are proved from the original inequalities. -/
theorem aligned_negative_eh0_hard_entry {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0)
    (hr : (C.point E).a≤7/12 ∨
      max |(C.point H).y| |(C.point D).y|≤(C.point E).a)
    (halign : C.theta G=C.theta H) (ht : C.theta A<C.theta H)
    (hyG : (C.point G).y≤0) (hGA : C.Feasible G 1)
    (hnot : ¬C.Feasible G 0) (hEH : C.Feasible E 0) (hBT : C.Feasible B 2) :
    ∃ J : SignedCycle.HardInput q,
      J.cycle.Ordered ∧ J.cycle.theta H=J.cycle.theta G ∧
      C.theta A≤J.cycle.theta H ∧ J.cycle.theta H<C.theta H ∧
      J.cycle.Feasible H (w.owner H) ∧ J.cycle.Feasible E 0 ∧
      |(J.cycle.point H).y|<(J.cycle.point H).a ∧
      |(J.cycle.point G).y|<(J.cycle.point G).a ∧
      (J.cycle.point H).circle<(C.point H).circle ∧
      AnchorNonincrease C J.cycle ∧ StrictAnchorLoss C J.cycle ∧
      (∀ i, i≠H → i≠G →
        J.cycle.point i=C.point i ∧ J.cycle.theta i=C.theta i) := by
  let I := sourceOfCycle hn ha w halign ht hyG hGA hnot
  have he : |(C.theta A-C.theta E)+(C.theta H-C.theta A)|≤7/10 := by
    rw [show (C.theta A-C.theta E)+(C.theta H-C.theta A)=
      C.theta H-C.theta E by ring]
    simpa [frameCap] using hn.spread H E
  have hf : quarterFeasible (C.point E) (C.point H)
      ((C.theta A-C.theta E)+(C.theta H-C.theta A)) 0 := by
    rw [show (C.theta A-C.theta E)+(C.theta H-C.theta A)=
      C.theta H-C.theta E by ring]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  obtain ⟨O⟩ := I.eh0_hard_endpoint hq hyE he hf
  let J := O.hardInput hn ha w hz hyE hBT hr
  refine ⟨J,O.ordered hn hq ha w hz,?_,?_,?_,?_,?_,?_,?_,?_,
    O.anchor_nonincrease,O.strict_anchor_loss,?_⟩
  · simp [J,LowMixedEndpoint.hardInput,LowMixedEndpoint.cycle,replaceHG,replacePoint,H,G]
  · change C.theta A≤(O.cycle.theta H)
    have hh : C.theta A≤C.theta A+O.angle := by linarith [O.angle_mem.1]
    simpa [LowMixedEndpoint.cycle,replaceHG,replacePoint,H,G] using hh
  · change O.cycle.theta H<C.theta H
    have hh := O.angle_mem.2
    simpa [LowMixedEndpoint.cycle,replaceHG,replacePoint,H,G] using
      (show C.theta A+O.angle<C.theta H by linarith)
  · exact (O.witnesses w).feasible H
  · exact (replaceHG_EH C O.Hpoint O.Gpoint O.angle 0).2 O.EH0
  · simpa [J,LowMixedEndpoint.hardInput,LowMixedEndpoint.cycle,
      replaceHG,replacePoint,H,G] using O.H_nondiagonal
  · simpa [J,LowMixedEndpoint.hardInput,LowMixedEndpoint.cycle,
      replaceHG,replacePoint] using O.G_nondiagonal
  · simpa [J,LowMixedEndpoint.hardInput,LowMixedEndpoint.cycle,
      replaceHG,replacePoint,H,G] using O.H_circle_loss
  · exact O.unchanged

end AlignedNegative
end SquaresInCircles.Eight.TableFree
