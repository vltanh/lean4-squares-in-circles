module

public import SquaresInCircles.Eight.TableFree.EInteriorReduction

/-!
# The actual E-only hard-cycle reduction

Uncompiled draft.  The E variational reduction is invoked on the retained
original mixed inequalities.  Every non-E point and frame stays literal,
so previously inherited H/A/B/D circle losses remain separate.  The
source-interior test is evaluated before the E move and charges its strict
loss to the original E circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate EInteriorGeometry
namespace SignedCycle

private theorem feasible_D_iff (C : SignedCycle) (j : Fin 4) :
    C.Feasible D j ↔ quarterFeasible (C.point D) (C.point E) (C.theta E-C.theta D) j := by
  rw [Feasible,slack,edge,ite_eq_right (show Candidate.word D≠0 by decide),delta,
    show next D=E from rfl,quarterFeasible,sub_nonneg]

private theorem feasible_E_iff (C : SignedCycle) (j : Fin 4) :
    C.Feasible E j ↔ quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) j := by
  rw [Feasible,slack,edge,ite_eq_right (show Candidate.word E≠0 by decide),delta,
    show next E=H from rfl,quarterFeasible,sub_nonneg]

def eInteriorCycle (C : SignedCycle) (P : State) : SignedCycle where
  point := ![C.point H,C.point G,C.point A,C.point B,C.point T,C.point D,⟨P.1,-P.2.1⟩]
  theta := ![C.theta H,C.theta G,C.theta A,C.theta B,C.theta T,C.theta D,C.theta D+P.2.2]

theorem eInteriorCycle_unchanged (C : SignedCycle) (P : State)
    (i : Vertex) (hi : i≠E) :
    (eInteriorCycle C P).point i=C.point i ∧
      (eInteriorCycle C P).theta i=C.theta i := by
  fin_cases i <;> simp [eInteriorCycle,H,G,A,B,T,D,E] at hi ⊢

theorem eInteriorCycle_theta (C : SignedCycle) (P : State) (i : Vertex) :
    (eInteriorCycle C P).theta i=if i=E then C.theta D+P.2.2 else C.theta i := by
  fin_cases i <;> simp [eInteriorCycle,H,G,A,B,T,D,E]

theorem eInteriorCycle_spread {C : SignedCycle} (hc : C.Spread) {P : State}
    (hp : P.2.2∈Icc 0 (C.theta H-C.theta D)) : (eInteriorCycle C P).Spread := by
  have he (j : Vertex) : |C.theta D+P.2.2-C.theta j|≤frameCap := by
    have hD := abs_le.mp (hc D j)
    have hH := abs_le.mp (hc H j)
    apply abs_le.mpr
    constructor <;> linarith [hp.1,hp.2]
  intro i j
  rw [eInteriorCycle_theta,eInteriorCycle_theta]
  by_cases hi : i=E <;> by_cases hj : j=E
  · norm_num [hi,hj,frameCap]
  · simpa [hi,hj] using he j
  · simpa [hi,hj,abs_sub_comm] using he i
  · simpa [hi,hj] using hc i j

theorem eInteriorCycle_circle {C : SignedCycle} {P : State} (hb : 0≤P.2.1) :
    ((eInteriorCycle C P).point E).circle=corner P := by
  simp [eInteriorCycle,E,SignedPoint.circle,corner,abs_neg,abs_of_nonneg hb]

theorem eInteriorCycle_DE {q : ℝ} {C : SignedCycle} {P : State}
    (hspan : C.theta H-C.theta D≤7/10)
    (hp : EInteriorGeometry.Feasible (C.point H).a (C.point D).a (C.theta H-C.theta D) q P) :
    (eInteriorCycle C P).Feasible D 3 := by
  have hu : P.2.2∈Icc 0 (7/10 : ℝ) :=
    ⟨hp.angle.1,hp.angle.2.trans hspan⟩
  have hh := hp.DE
  rw [show W P.2.2=edgeWidth P.2.2 by
    rw [edgeWidth_positive_formula hu]; rfl] at hh
  simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,D,E,
    deValue,quarterProjection,sub_nonneg] using hh

theorem eInteriorCycle_EH {q : ℝ} {C : SignedCycle} {P : State}
    (hspan : C.theta H-C.theta D≤7/10)
    (hp : EInteriorGeometry.Feasible (C.point H).a (C.point D).a (C.theta H-C.theta D) q P) :
    (eInteriorCycle C P).Feasible E 1 := by
  have hv : C.theta H-C.theta D-P.2.2∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith [hp.angle.2],by linarith [hp.angle.1]⟩
  have hh := hp.EH
  rw [show W (C.theta H-C.theta D-P.2.2)=edgeWidth (C.theta H-C.theta D-P.2.2) by
    rw [edgeWidth_positive_formula hv]; rfl] at hh
  have heq : C.theta H-(C.theta D+P.2.2)=C.theta H-C.theta D-P.2.2 := by ring
  rw [feasible_E_iff]
  have hpE : (eInteriorCycle C P).point E=⟨P.1,-P.2.1⟩ := rfl
  have hpH : (eInteriorCycle C P).point H=C.point H := rfl
  have htE : (eInteriorCycle C P).theta E=C.theta D+P.2.2 := rfl
  have htH : (eInteriorCycle C P).theta H=C.theta H := rfl
  rw [hpE,hpH,htE,htH,heq]
  simp only [quarterFeasible,quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero]
  dsimp only [ehValue] at hh
  linarith

def Witnesses.eInterior {q : ℝ} {C : SignedCycle} (w : C.Witnesses) {P : State}
    (hspan : C.theta H-C.theta D≤7/10)
    (hp : EInteriorGeometry.Feasible (C.point H).a (C.point D).a (C.theta H-C.theta D) q P) :
    (eInteriorCycle C P).Witnesses where
  owner i := if i=D then 3 else if i=E then 1 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,H,G,D,E]
        using w.feasible H
    · simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,G,A,D,E]
        using w.feasible G
    · simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,A,B,D,E]
        using w.feasible A
    · simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,B,T,D,E]
        using w.feasible B
    · simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,T,D,E]
        using w.feasible T
    · simpa [D,E] using eInteriorCycle_DE hspan hp
    · simpa [D,E] using eInteriorCycle_EH hspan hp
  allowed := by
    intro i
    by_cases hiD : i=D
    · subst i; norm_num [normalOwners,D,E]
    by_cases hiE : i=E
    · subst i; norm_num [normalOwners,D,E]
    · simpa [hiD,hiE] using w.allowed i

def HardInput.fromEInterior {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hb : AlignedChainBounds.Bounds I.cycle) {P : State}
    (hp : EInteriorGeometry.Feasible (I.cycle.point H).a (I.cycle.point D).a
      (I.cycle.theta H-I.cycle.theta D) q P) : HardInput q where
  cycle := eInteriorCycle I.cycle P
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=E
      · subst i
        have ha := primary_lower hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
        have hs := strict_sorting hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
        exact ⟨by simpa [eInteriorCycle,E] using (show 0<P.1 by linarith),
          by simpa [eInteriorCycle,E,abs_neg,abs_of_nonneg hp.b_nonneg] using hs.le⟩
      · rw [(eInteriorCycle_unchanged I.cycle P i hi).1]
        exact I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=E
      · subst i
        change ((eInteriorCycle I.cycle P).point E).circle≤q
        rw [eInteriorCycle_circle hp.b_nonneg]
        exact hp.circle
      · rw [(eInteriorCycle_unchanged I.cycle P i hi).1]
        exact I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=E
      · subst i
        have ha := primary_lower hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
        change (1/12 : ℝ)^2≤(max (P.1-1/2) 0)^2+(max (|-P.2.1|-1/2) 0)^2
        rw [abs_neg,abs_of_nonneg hp.b_nonneg,max_eq_left (by linarith : 0≤P.1-1/2)]
        nlinarith [sq_nonneg (max (P.2.1-1/2) 0)]
      · rw [(eInteriorCycle_unchanged I.cycle P i hi).1]
        exact I.necessary.core i
    spread := eInteriorCycle_spread I.necessary.spread hp.angle }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := I.anchors_normal.A_nonneg
    B_nonpos := I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  E_nonpos := by simpa [eInteriorCycle,E] using neg_nonpos.mpr hp.b_nonneg
  witnesses := I.witnesses.eInterior (by linarith [hb.span_lt]) hp
  GA_hard := by
    simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,G,A] using I.GA_hard
  BT_hard := by
    simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,B,T] using I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro h
      have hh : I.witnesses.owner H=2 := by simpa [Witnesses.eInterior,H,D,E] using h
      exact I.zero_signs.HG_canceling hh
    TD_canceling := by
      intro h
      have hh : I.witnesses.owner T=0 := by simpa [Witnesses.eInterior,T,D,E] using h
      exact I.zero_signs.TD_canceling hh }
  E_radial := by
    right
    have ha := primary_lower hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
    change max |(I.cycle.point H).y| |(I.cycle.point D).y|≤P.1
    apply max_le
    · rw [abs_of_nonneg I.anchors_normal.H_nonneg]
      linarith [hb.H_tangent.2]
    · rw [abs_of_nonpos I.anchors_normal.D_nonpos]
      linarith [hb.D_tangent.2]

theorem HardInput.E_source_relaxation {q : ℝ} (I : HardInput q)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    EInteriorGeometry.Feasible (I.cycle.point H).a (I.cycle.point D).a
      (I.cycle.theta H-I.cycle.theta D) q
      ((I.cycle.point E).a,-(I.cycle.point E).y,I.cycle.theta E-I.cycle.theta D) := by
  have hu : I.cycle.theta E-I.cycle.theta D∈Icc 0 (7/10 : ℝ) :=
    ⟨sub_nonneg.mpr hDEorder,(le_abs_self _).trans (I.necessary.spread E D)⟩
  have hv : I.cycle.theta H-I.cycle.theta E∈Icc 0 (7/10 : ℝ) :=
    ⟨sub_nonneg.mpr hEHorder,(le_abs_self _).trans (I.necessary.spread H E)⟩
  have hδ : I.cycle.theta H-I.cycle.theta D-(I.cycle.theta E-I.cycle.theta D)=
      I.cycle.theta H-I.cycle.theta E := by ring
  refine {
    b_nonneg := neg_nonneg.mpr I.E_nonpos
    sorted := by simpa [abs_of_nonpos I.E_nonpos] using (I.necessary.sorted E).2
    angle := ⟨hu.1,by linarith⟩
    circle := by
      simpa [corner,SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos I.E_nonpos]
        using I.necessary.contained E
    DE := ?_
    EH := ?_ }
  · have hh := (feasible_D_iff I.cycle 3).mp hDE
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_three,Matrix.tail_cons,
      Matrix.head_cons] at hh
    rw [edgeWidth_positive_formula hu] at hh
    dsimp only [W,deValue]
    linarith
  · have hh := (feasible_E_iff I.cycle 1).mp hEH
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero] at hh
    rw [edgeWidth_positive_formula hv] at hh
    dsimp only [W,ehValue]
    rw [hδ]
    linarith

/-- Actual E endpoint construction, with the original interior source
test and all other points and frames retained exactly. -/
theorem HardInput.reduce_ordered_E {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E∈Icc (I.cycle.theta D) (I.cycle.theta H) ∧
      ((J.cycle.point E).y=0 ∨ J.cycle.theta E=I.cycle.theta D ∨
        J.cycle.theta E=I.cycle.theta H) ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (((I.cycle.point E).y<0 ∧ I.cycle.theta D<I.cycle.theta E ∧
        I.cycle.theta E<I.cycle.theta H) → StrictAnchorLoss I.cycle J.cycle) ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hb := I.aligned_bounds hq hHG hAB hTD hleft hright
  have howners := I.aligned_primary_E_witnesses hq hHG hAB hTD hleft hright hDEorder hEHorder
  have hp := I.E_source_relaxation hDEorder hEHorder howners.1 howners.2
  obtain ⟨P,hP,hcircle,hboundary,hstrict⟩ := exists_boundary_minimum hq
    ⟨hb.span_nonneg,by linarith [hb.span_lt]⟩ hb.H_primary.1 hb.D_primary.1 hb.primary_sum hp
  let J := I.fromEInterior hq hb hP
  have hcircle_source : corner
      ((I.cycle.point E).a,-(I.cycle.point E).y,I.cycle.theta E-I.cycle.theta D)=
      (I.cycle.point E).circle := by
    simp [corner,SignedPoint.circle,abs_of_nonpos I.E_nonpos]
  have hcircleJ : (J.cycle.point E).circle=corner P := eInteriorCycle_circle hP.b_nonneg
  have hunchanged (i : Vertex) (hi : i≠E) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
    eInteriorCycle_unchanged I.cycle P i hi
  refine ⟨J,hunchanged,?_,?_,?_,?_,eInteriorCycle_DE (by linarith [hb.span_lt]) hP,
    eInteriorCycle_EH (by linarith [hb.span_lt]) hP⟩
  · change I.cycle.theta D+P.2.2∈Icc (I.cycle.theta D) (I.cycle.theta H)
    constructor <;> linarith [hP.angle.1,hP.angle.2]
  · rcases hboundary with hb0 | hδ0 | hε0
    · left
      change -P.2.1=0
      linarith
    · right; left
      change I.cycle.theta D+P.2.2=I.cycle.theta D
      linarith
    · right; right
      change I.cycle.theta D+P.2.2=I.cycle.theta H
      linarith
  · intro i hi
    by_cases hiE : i=E
    · subst i
      rw [hcircleJ,←hcircle_source]
      exact hcircle
    · rw [(hunchanged i hiE).1]
  · rintro ⟨hy,hD,hH⟩
    refine ⟨E,by norm_num [anchorVertices,E],?_⟩
    rw [hcircleJ,←hcircle_source]
    apply hstrict
    exact ⟨by simpa using neg_pos.mpr hy,by constructor <;> linarith⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
