module

public import SquaresInCircles.Eight.TableFree.PositiveCancelingOuter
public import SquaresInCircles.Eight.TableFree.HardCancelingOuterCycle

/-!
# Both signs of both canceling outer errors in an ordered common middle

Uncompiled source draft.  Once D ≤ A = B ≤ H, the actual canceling HG2
and TD0 pairs align at the same radius.  The larger middle tangent is
treated first only to prove that the opposite original tangent exceeds
one fifth.  Both concrete outputs are then constructed from the separate
original anchor circles.  No descendant circle equality is substituted
for a source circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate HardCancelingOuter PositiveCancelingOuter
namespace SignedCycle

theorem HardInput.ordered_canceling_HG_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hAy : 1/5≤(I.cycle.point A).y)
    (hHG : I.cycle.Feasible H 2) :
    Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A)
      ((I.cycle.theta H-I.cycle.theta A)-|I.cycle.theta G-I.cycle.theta H|/3)) := by
  have hΘ : I.cycle.theta H-I.cycle.theta A∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread H A
    refine ⟨sub_nonneg.mpr hAH,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have ht : I.cycle.theta G-I.cycle.theta A∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread G A
    refine ⟨sub_nonneg.mpr hAG,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      ((I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)) 2 := by
    rw [show (I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)=
      I.cycle.theta G-I.cycle.theta H by ring]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta G-I.cycle.theta A)) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  have hh := ordered_G_alignment hqL hq (I.necessary.sorted H) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core A) (I.necessary.contained H)
    (I.necessary.contained A) I.anchors_normal.H_nonneg hAy hΘ ht hHG' hGA'
  simpa [show (I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)=
    I.cycle.theta G-I.cycle.theta H by ring] using hh

theorem HardInput.ordered_canceling_TD_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hBy : (I.cycle.point B).y≤ -(1/5 : ℝ))
    (hTD : I.cycle.Feasible T 0) :
    Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D)
      ((I.cycle.theta B-I.cycle.theta D)-|I.cycle.theta T-I.cycle.theta D|/3)) := by
  have hΘ : I.cycle.theta B-I.cycle.theta D∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread B D
    refine ⟨sub_nonneg.mpr hDB,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have ht : I.cycle.theta B-I.cycle.theta T∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread B T
    refine ⟨sub_nonneg.mpr hTB,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have hTD' : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)) 0 := by
    rw [show (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)=
      I.cycle.theta D-I.cycle.theta T by ring]
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using hTD
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta B-I.cycle.theta T)) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,neg_sub]
      using I.BT_hard
  have hh := ordered_T_alignment hqL hq (I.necessary.sorted B) (I.necessary.sorted D)
    (I.necessary.core B) (I.necessary.core D) (I.necessary.contained B)
    (I.necessary.contained D) hBy I.anchors_normal.D_nonpos hΘ ht hBT' hTD'
  rw [show (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)=
    I.cycle.theta D-I.cycle.theta T by ring,abs_sub_comm] at hh
  exact hh

/-- Both error signs are now removed without imposing separate lower
bounds on the two original middle tangents.  The tangent sum supplies
the first large side; its original circle supplies the other side. -/
theorem HardInput.align_ordered_canceling_outer {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 2) (hTD : I.cycle.Feasible T 0) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point G).y< -(1/10 : ℝ) ∧ (1/10 : ℝ)<(J.cycle.point T).y ∧
      (J.cycle.point A).y∈Ioo (67/200) (133/200) ∧
      -(J.cycle.point B).y∈Ioo (67/200) (133/200) ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta G≠I.cycle.theta H ∨ I.cycle.theta T≠I.cycle.theta D) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠G → i≠T → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i∈({H,D,E} : Finset Vertex) → J.cycle.point i=I.cycle.point i) := by
  let TG := (I.cycle.theta H-I.cycle.theta A)-|I.cycle.theta G-I.cycle.theta H|/3
  let TT := (I.cycle.theta B-I.cycle.theta D)-|I.cycle.theta T-I.cycle.theta D|/3
  have houtputs : Nonempty
      (GAlignment q (I.cycle.point H) (I.cycle.point A)
        (I.cycle.theta H-I.cycle.theta A) TG ×
       TAlignment q (I.cycle.point B) (I.cycle.point D)
        (I.cycle.theta B-I.cycle.theta D) TT) := by
    by_cases ha : 1/2≤(I.cycle.point A).y
    · obtain ⟨OG⟩ := I.ordered_canceling_HG_output hqL hq hAH hAG (by linarith) hHG
      have hb : (I.cycle.point B).y≤ -(1/5 : ℝ) := by
        have hy := OG.A_tangent_upper
        rw [OG.A_tangent] at hy
        linarith
      obtain ⟨OT⟩ := I.ordered_canceling_TD_output hqL hq hDB hTB hb hTD
      exact ⟨⟨OG,OT⟩⟩
    · have hb : (I.cycle.point B).y≤ -(1/5 : ℝ) := by
        have ha' := lt_of_not_ge ha
        linarith
      obtain ⟨OT⟩ := I.ordered_canceling_TD_output hqL hq hDB hTB hb hTD
      have ha' : 1/5≤(I.cycle.point A).y := by
        have hy := OT.B_tangent_lower
        rw [OT.B_tangent] at hy
        linarith
      obtain ⟨OG⟩ := I.ordered_canceling_HG_output hqL hq hAH hAG ha' hHG
      exact ⟨⟨OG,OT⟩⟩
  obtain ⟨⟨OG,OT⟩⟩ := houtputs
  let K := I.fromCancelingHG hAB OG
  let J := K.fromCancelingTD hAB OT
  have hyA : OG.pointA.y=(I.cycle.point A).y := OG.A_tangent
  have hyB : OT.pointB.y=(I.cycle.point B).y := OT.B_tangent
  have hsum' : OG.pointA.y-OT.pointB.y=1 := by rw [hyA,hyB,hsum]
  refine ⟨J,rfl,rfl,hAB,hsum',OG.G_normal,OT.T_normal,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨by linarith [OT.B_tangent_lower],OG.A_tangent_upper⟩
  · exact ⟨by linarith [OG.A_tangent_upper],by linarith [OT.B_tangent_lower]⟩
  · intro i hi
    fin_cases i
    · exact le_rfl
    · simp [anchorVertices,H,G,A,B,D,E] at hi
    · exact OG.A_circle
    · exact OT.B_circle
    · simp [anchorVertices,H,T,A,B,D,E] at hi
    · exact le_rfl
    · exact le_rfl
  · rintro (hg | ht)
    · have hp : 0<|I.cycle.theta G-I.cycle.theta H| := abs_pos.mpr (sub_ne_zero.mpr hg)
      refine ⟨A,by simp [anchorVertices],OG.A_strict ?_⟩
      dsimp [TG]
      linarith
    · have hp : 0<|I.cycle.theta T-I.cycle.theta D| := abs_pos.mpr (sub_ne_zero.mpr ht)
      refine ⟨B,by simp [anchorVertices],OT.B_strict ?_⟩
      dsimp [TT]
      linarith
  · intro i hiG hiT
    change (alignBTCycle (alignGACycle I.cycle OG.pointG OG.pointA)
      OT.pointT OT.pointB).theta i=I.cycle.theta i
    rw [alignBTCycle_theta,if_neg hiT,alignGACycle_theta,if_neg hiG]
  · intro i hi
    fin_cases i <;> simp [H,G,A,B,T,D,E] at hi ⊢
    all_goals rfl

end SignedCycle
end SquaresInCircles.Eight.TableFree
