module

public import SquaresInCircles.Eight.TableFree.AlignedNegativeAssembly
public import SquaresInCircles.Eight.TableFree.AlignedNegativeEH1

/-!
# Seven-cycle and hard-class entry for short retained EH1

Uncompiled source. The explicit endpoint retains the original EH1 axis,
the original weak HG axis, and every unchanged neighboring witness. Its
strict H-circle loss and the retained E radial alternative hold at the
source's actual q, including after previous anchor losses.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace AlignedNegative
private theorem r38_positiveVariation_expand (θ : Vertex → ℝ) :
    positiveVariation θ=positivePart (θ G-θ H)+positivePart (θ A-θ G)+
      positivePart (θ B-θ A)+positivePart (θ T-θ B)+positivePart (θ D-θ T)+
      positivePart (θ E-θ D)+positivePart (θ H-θ E) := by
  simp only [positiveVariation,Fin.sum_univ_seven,delta]
  rfl

namespace HighMixedEndpoint

variable {q : ℝ} {C : SignedCycle}
variable {I : Source q (C.theta H-C.theta A) (C.point H) (C.point G) (C.point A)}

def cycle (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E)) : SignedCycle :=
  replaceHG C O.Hpoint O.Gpoint O.angle

theorem unchanged (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (i : Vertex) (hiH : i≠H) (hiG : i≠G) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i :=
  replaceHG_unchanged C O.Hpoint O.Gpoint O.angle i hiH hiG

theorem necessary (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hn : C.Necessary q) : O.cycle.Necessary q :=
  replaceHG_necessary hn O.H_sorted (O.H_circle_loss.le.trans (hn.contained H))
    O.H_core O.G_sorted O.G_inside.le O.G_core.ge
    ⟨O.angle_mem.1,O.angle_mem.2.le⟩

theorem normal (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (ha : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · simpa [cycle,replaceHG,replacePoint,H,G] using O.H_positive.le
  · simpa [cycle,replaceHG,replacePoint,H,G,A] using ha.A_nonneg
  · simpa [cycle,replaceHG,replacePoint,H,G,B] using ha.B_nonpos
  · simpa [cycle,replaceHG,replacePoint,H,G,D] using ha.D_nonpos

def witnesses (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (w : C.Witnesses) : O.cycle.Witnesses where
  owner := ![w.owner H,0,w.owner A,w.owner B,w.owner T,w.owner D,1]
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
    · exact (replaceHG_EH C O.Hpoint O.Gpoint O.angle 1).2 O.EH1
  allowed i := by
    fin_cases i
    · simpa [H] using w.allowed H
    · norm_num [SignedCycle.normalOwners,G]
    · simpa [A] using w.allowed A
    · simpa [B] using w.allowed B
    · simpa [T] using w.allowed T
    · simpa [D] using w.allowed D
    · norm_num [SignedCycle.normalOwners,E]

theorem zero_signs (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) :
    O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro _
    simpa [cycle,replaceHG,replacePoint] using O.G_negative
  · intro hh
    have hj : w.owner T=0 := by simpa [witnesses,T] using hh
    rw [(O.unchanged T (by decide) (by decide)).1]
    exact hz.TD_canceling hj

theorem ordered (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) : O.cycle.Ordered :=
  SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses w) (O.zero_signs w hz)

theorem strict_spread
    (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hs : C.StrictSpread) : O.cycle.StrictSpread :=
  replaceHG_strictSpread O.Hpoint O.Gpoint hs ⟨O.angle_mem.1,O.angle_mem.2.le⟩

theorem variations
    (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (halign : C.theta G=C.theta H) :
    positiveVariation C.theta-positiveVariation O.cycle.theta=
        C.theta H-C.theta A-O.angle ∧
      negativeVariation C.theta-negativeVariation O.cycle.theta=
        C.theta H-C.theta A-O.angle := by
  have hEHnew : 0≤C.theta A+O.angle-C.theta E := by linarith [O.EH_error.1]
  have hEHold : 0≤C.theta H-C.theta E := by linarith [O.angle_mem.2]
  have hGAold : positivePart (C.theta A-C.theta H)=0 :=
    max_eq_right (by linarith [I.tilt_pos])
  have hGAnew : positivePart (C.theta A-(C.theta A+O.angle))=0 :=
    max_eq_right (by linarith [O.angle_mem.1])
  have hEHold' : positivePart (C.theta H-C.theta E)=C.theta H-C.theta E :=
    max_eq_left hEHold
  have hEHnew' : positivePart (C.theta A+O.angle-C.theta E)=
      C.theta A+O.angle-C.theta E := max_eq_left hEHnew
  have hp : positiveVariation C.theta-positiveVariation O.cycle.theta=
      C.theta H-C.theta A-O.angle := by
    have t0 : O.cycle.theta H=C.theta A+O.angle := by
      simp [cycle,replaceHG,replacePoint,H,G]
    have t1 : O.cycle.theta G=C.theta A+O.angle := by
      simp [cycle,replaceHG,replacePoint]
    have tk : ∀ k : Vertex, k≠H → k≠G → O.cycle.theta k=C.theta k :=
      fun k hH hG => (O.unchanged k hH hG).2
    rw [r38_positiveVariation_expand,r38_positiveVariation_expand]
    change _ - (positivePart (O.cycle.theta G-O.cycle.theta H)+
      positivePart (O.cycle.theta A-O.cycle.theta G)+_+_+_+_+
      positivePart (O.cycle.theta H-O.cycle.theta E))=_
    rw [t0,t1,tk A (by decide) (by decide),tk B (by decide) (by decide),
      tk T (by decide) (by decide),tk D (by decide) (by decide),
      tk E (by decide) (by decide)]
    rw [halign,sub_self,sub_self,positivePart_zero,hGAold,hGAnew,hEHold',hEHnew']
    ring
  exact ⟨hp,by
    simpa only [← variations_equal C.theta,← variations_equal O.cycle.theta] using hp⟩

theorem anchor_nonincrease
    (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E)) :
    AnchorNonincrease C O.cycle := by
  intro i hi
  by_cases hH : i=H
  · subst i
    simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss.le
  · have hG : i≠G := by
      rintro rfl
      revert hi; decide
    rw [(O.unchanged i hH hG).1]

theorem strict_anchor_loss
    (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E)) :
    StrictAnchorLoss C O.cycle := by
  refine ⟨H,by simp [anchorVertices],?_⟩
  simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss

theorem radial_alternative
    (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E))
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

def hardInput (O : HighMixedEndpoint I (C.point E) (C.theta A-C.theta E))
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

end HighMixedEndpoint

theorem aligned_negative_short_eh1_hard_entry {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0)
    (hr : (C.point E).a≤7/12 ∨
      max |(C.point H).y| |(C.point D).y|≤(C.point E).a)
    (halign : C.theta G=C.theta H) (ht : C.theta A<C.theta H)
    (hyG : (C.point G).y≤0) (hGA : C.Feasible G 1)
    (hnot : ¬C.Feasible G 0) (hEH : C.Feasible E 1)
    (hshort : |C.theta H-C.theta E|≤11/50) (hBT : C.Feasible B 2) :
    ∃ J : SignedCycle.HardInput q,
      J.cycle.Ordered ∧ J.cycle.theta H=J.cycle.theta G ∧
      C.theta A≤J.cycle.theta H ∧ J.cycle.theta H<C.theta H ∧
      J.cycle.Feasible H (w.owner H) ∧ J.cycle.Feasible E 1 ∧
      |(J.cycle.point H).y|<(J.cycle.point H).a ∧
      |(J.cycle.point G).y|<(J.cycle.point G).a ∧
      (J.cycle.point H).circle<(C.point H).circle ∧
      AnchorNonincrease C J.cycle ∧ StrictAnchorLoss C J.cycle ∧
      (∀ i, i≠H → i≠G →
        J.cycle.point i=C.point i ∧ J.cycle.theta i=C.theta i) := by
  let I := sourceOfCycle hn ha w halign ht hyG hGA hnot
  have he : |(C.theta A-C.theta E)+(C.theta H-C.theta A)|≤11/50 := by
    rw [show (C.theta A-C.theta E)+(C.theta H-C.theta A)=
      C.theta H-C.theta E by ring]
    exact hshort
  have hf : quarterFeasible (C.point E) (C.point H)
      ((C.theta A-C.theta E)+(C.theta H-C.theta A)) 1 := by
    rw [show (C.theta A-C.theta E)+(C.theta H-C.theta A)=
      C.theta H-C.theta E by ring]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  obtain ⟨O⟩ := I.eh1_hard_endpoint hq (hn.sorted E) (hn.contained E) hyE he hf
  let J := O.hardInput hn ha w hz hyE hBT hr
  refine ⟨J,O.ordered hn hq ha w hz,?_,?_,?_,?_,?_,?_,?_,?_,
    O.anchor_nonincrease,O.strict_anchor_loss,?_⟩
  · simp [J,HighMixedEndpoint.hardInput,HighMixedEndpoint.cycle,replaceHG,replacePoint,H,G]
  · change C.theta A≤(O.cycle.theta H)
    have hh : C.theta A≤C.theta A+O.angle := by linarith [O.angle_mem.1]
    simpa [HighMixedEndpoint.cycle,replaceHG,replacePoint,H,G] using hh
  · change O.cycle.theta H<C.theta H
    have hh := O.angle_mem.2
    simpa [HighMixedEndpoint.cycle,replaceHG,replacePoint,H,G] using
      (show C.theta A+O.angle<C.theta H by linarith)
  · exact (O.witnesses w).feasible H
  · exact (replaceHG_EH C O.Hpoint O.Gpoint O.angle 1).2 O.EH1
  · simpa [J,HighMixedEndpoint.hardInput,HighMixedEndpoint.cycle,
      replaceHG,replacePoint,H,G] using O.H_nondiagonal
  · simpa [J,HighMixedEndpoint.hardInput,HighMixedEndpoint.cycle,
      replaceHG,replacePoint] using O.G_nondiagonal
  · simpa [J,HighMixedEndpoint.hardInput,HighMixedEndpoint.cycle,
      replaceHG,replacePoint,H,G] using O.H_circle_loss
  · exact O.unchanged

end AlignedNegative
end SquaresInCircles.Eight.TableFree
