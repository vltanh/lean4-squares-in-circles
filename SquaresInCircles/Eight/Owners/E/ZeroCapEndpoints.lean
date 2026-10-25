module

public import SquaresInCircles.Eight.Owners.E.ContactConcavity
public import SquaresInCircles.Eight.Owners.E.ZeroCapped
public import SquaresInCircles.Eight.Owners.Hard.SplitCycle
public import SquaresInCircles.Eight.Owners.Positive.SplitCalculus
public import SquaresInCircles.Eight.Words.Aligned.NegativeEH1

/-!
# Eight squares: both E-zero endpoint cap sums are strictly below two

The circular-cap rotation identity transfers the
proved coupled scalar bound to the cap sum.  No comparison packing is
assumed to exist, and no numerical derivative estimate is required for
this strict version of the transfer.
-/

section
/-!
## Moving an interior E to the boundary with a loss on its circle

A minimum of the relaxation is followed by radial descent or by the two-contact curve: every
feasible interior state has a feasible state with strictly smaller corner circle
(`interior_improves`), and a minimum lies on a face `b = 0`, `θ = 0` or `θ = α`
(`minimum_boundary`, `exists_boundary_minimum`). A neighbourhood is chosen only for the strict
sorting, sign and angle inequalities, and the circle bound at the endpoint follows from the strict
decrease of the energy. The span `27/100` of the negative composites is allowed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EInteriorGeometry

theorem contact_orientation_improves {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Ioo 0 (27/100 : ℝ))
    (hh : 1/2<h) (hd : 1/2<d)
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) (hb : 0<P.2.1)
    (hangle : P.2.2∈Ioo 0 α)
    (hDE : deSlack d P=0) (hEH : ehSlack h α P=0) :
    ∃Q, Feasible h d α q Q ∧ corner Q<corner P := by
  let m := h+d-1
  let n := h-d
  let z := α/2-P.2.2
  have hwide : α∈Icc 0 (7/10 : ℝ) := ⟨hα.1.le,by linarith [hα.2]⟩
  have hsin := (transport_trig hwide).2.2.1
  have hsum2 : h+d<2 := by linarith
  have hm : m∈Icc (0:ℝ) 1 := by dsimp [m]; constructor <;> linarith
  have hn : |n|≤1 := by rw [abs_le]; dsimp [n]; constructor <;> linarith
  have hmD : (m-n+1)/2=d := by dsimp [m,n]; ring
  have hmH : (m+n+1)/2=h := by dsimp [m,n]; ring
  have hz : z∈Ioo (-α/2) (α/2) := by dsimp [z]; constructor <;> linarith [hangle.1,hangle.2]
  have hδ : α/2-z=P.2.2 := by dsimp [z]; ring
  have hε : α/2+z=α-P.2.2 := by dsimp [z]; ring
  have hdeeq : deValue d P=W P.2.2 := sub_eq_zero.mp hDE
  have heheq : ehValue h α P=W (α-P.2.2) := sub_eq_zero.mp hEH
  have hu := EContactCurve.contact_unique (m := m) (n := n) (a := P.1)
    (β := P.2.1) (z := z) hα
    (by rw [hmD,hδ]; exact hdeeq)
    (by rw [hmH,hε]; exact heheq)
  have hcurve : EContactCurve.curve m n α z=P := by
    apply Prod.ext
    · exact hu.1.symm
    · apply Prod.ext
      · exact hu.2.symm
      · exact hδ
  have hsort := strict_sorting_wide hq ⟨hα.1.le,hα.2.le⟩ hsum hp
  let S : Set ℝ := {r |
    0<EContactCurve.b m n α r ∧
    EContactCurve.b m n α r<EContactCurve.x m n α r+1/2 ∧
    -α/2<r ∧ r<α/2}
  have hSopen : IsOpen S := by
    have h1 : IsOpen {r : ℝ | 0<EContactCurve.b m n α r} :=
      isOpen_lt continuous_const (by
        unfold EContactCurve.b EContactCurve.U EContactCurve.V
        fun_prop)
    have h2 : IsOpen {r : ℝ | EContactCurve.b m n α r<EContactCurve.x m n α r+1/2} :=
      isOpen_lt (by unfold EContactCurve.b EContactCurve.U EContactCurve.V; fun_prop)
        (by unfold EContactCurve.x EContactCurve.U EContactCurve.V; fun_prop)
    have h3 : IsOpen {r : ℝ | -α/2<r} := isOpen_lt continuous_const continuous_id
    have h4 : IsOpen {r : ℝ | r<α/2} := isOpen_lt continuous_id continuous_const
    simpa only [S,ofPred_and] using h1.inter (h2.inter (h3.inter h4))
  have hzS : z∈S := by
    change 0<EContactCurve.b m n α z ∧
      EContactCurve.b m n α z<EContactCurve.x m n α z+1/2 ∧ -α/2<z ∧ z<α/2
    exact ⟨by rw [←hu.2]; exact hb,by rw [←hu.2,←hu.1]; exact hsort,hz⟩
  obtain ⟨e,he,hball⟩ := Metric.isOpen_iff.mp hSopen z hzS
  have hnear {r : ℝ} (hr : |r-z|≤e/2) : r∈S := by
    apply hball
    change dist r z<e
    rw [Real.dist_eq]
    linarith
  have hlS : z-e/2∈S := by
    apply hnear
    rw [show z-e/2-z= -(e/2) by ring,abs_neg,abs_of_pos (by linarith : 0<e/2)]
  have huS : z+e/2∈S := by
    apply hnear
    rw [show z+e/2-z=e/2 by ring,abs_of_pos (by linarith : 0<e/2)]
  have himprove := EContactCurve.endpoint_improves hα hm hn
    hlS.2.2.1.le huS.2.2.2.le
    (show z∈Ioo (z-e/2) (z+e/2) by constructor <;> linarith)
  have hmake (r : ℝ) (hr : r∈S)
      (henergy : EContactCurve.energy m n α r<EContactCurve.energy m n α z) :
      Feasible h d α q (EContactCurve.curve m n α r) ∧
        corner (EContactCurve.curve m n α r)<corner P := by
    have hless : corner (EContactCurve.curve m n α r)<corner P := by
      rw [EContactCurve.corner_curve,←hcurve,EContactCurve.corner_curve]
      exact henergy
    have hcontacts := EContactCurve.curve_contacts hα m n r
    rw [hmD,hmH] at hcontacts
    refine ⟨{
      b_nonneg := hr.1.le
      sorted := hr.2.1.le
      angle := by
        dsimp [EContactCurve.curve]
        constructor <;> linarith [hr.2.2.1,hr.2.2.2]
      circle := hless.le.trans hp.circle
      DE := hcontacts.1.ge
      EH := ?_ },hless⟩
    change W (α-(α/2-r))≤ehValue h α (EContactCurve.curve m n α r)
    rw [show α-(α/2-r)=α/2+r by ring]
    exact hcontacts.2.ge
  rcases himprove with hl | hu'
  · exact ⟨_,hmake _ hlS hl⟩
  · exact ⟨_,hmake _ huS hu'⟩

/-- Every feasible state with positive tangent and interior angle has a feasible state with
strictly smaller corner circle; each contact case is settled by a geometric move. -/
theorem interior_improves {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Ioo 0 (27/100 : ℝ))
    (hh : 1/2<h) (hd : 1/2<d)
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) (hb : 0<P.2.1) (hangle : P.2.2∈Ioo 0 α) :
    ∃Q, Feasible h d α q Q ∧ corner Q<corner P := by
  have hde0 : 0≤deSlack d P := sub_nonneg.mpr hp.DE
  have heh0 : 0≤ehSlack h α P := sub_nonneg.mpr hp.EH
  rcases lt_or_eq_of_le hde0 with hde | hde
  · exact lower_tangent (by linarith [hα.2]) hp hb hde
  · rcases lt_or_eq_of_le heh0 with heh | heh
    · exact slide_DE (by linarith [hα.2]) hp
        (strict_sorting_wide hq ⟨hα.1.le,hα.2.le⟩ hsum hp) heh
    · exact contact_orientation_improves hq hα hh hd hsum hp hb hangle hde.symm heh.symm

theorem minimum_boundary {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Ico 0 (27/100 : ℝ))
    (hh : 1/2<h) (hd : 1/2<d)
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P)
    (hmin : IsMinOn corner (feasibleSet h d α q) P) :
    P.2.1=0 ∨ P.2.2=0 ∨ P.2.2=α := by
  by_cases hb : P.2.1=0
  · exact Or.inl hb
  by_cases hδ : P.2.2=0
  · exact Or.inr (Or.inl hδ)
  by_cases hε : P.2.2=α
  · exact Or.inr (Or.inr hε)
  have hbpos : 0<P.2.1 := lt_of_le_of_ne hp.b_nonneg (Ne.symm hb)
  have hδpos : 0<P.2.2 := lt_of_le_of_ne hp.angle.1 (Ne.symm hδ)
  have hδlt : P.2.2<α := lt_of_le_of_ne hp.angle.2 hε
  obtain ⟨Q,hQ,hless⟩ := interior_improves hq
    ⟨span_pos hα.1 hsum hp,hα.2⟩ hh hd hsum hp hbpos ⟨hδpos,hδlt⟩
  exact False.elim (not_lt_of_ge (hmin hQ) hless)

/-- From a feasible state, a feasible state on a face `b = 0`, `θ = 0` or `θ = α` with no larger
corner circle, and a strictly smaller one when the state is interior. The ceiling `q` and the
corner of E stay separate. -/
theorem exists_boundary_minimum {h d α q : ℝ} {P : State}
    (hq : q≤qCap) (hα : α∈Ico 0 (27/100 : ℝ))
    (hh : 1/2<h) (hd : 1/2<d)
    (hsum : h+d<1248/625-(359/500)*Real.sin α)
    (hp : Feasible h d α q P) :
    ∃Q, Feasible h d α q Q ∧ corner Q≤corner P ∧
      (Q.2.1=0 ∨ Q.2.2=0 ∨ Q.2.2=α) ∧
      ((0<P.2.1 ∧ P.2.2∈Ioo 0 α) → corner Q<corner P) := by
  obtain ⟨Q,hQ,hmin⟩ := exists_minimum hq ⟨P,hp⟩
  refine ⟨Q,hQ,hmin hp,minimum_boundary hq hα hh hd hsum hQ hmin,?_⟩
  rintro ⟨hb,hangle⟩
  obtain ⟨R,hR,hless⟩ := interior_improves hq
    ⟨span_pos hα.1 hsum hp,hα.2⟩ hh hd hsum hp hb hangle
  exact (hmin hR).trans_lt hless

end SquaresInCircles.Eight.EInteriorGeometry
end
end
end

section
/-!
## The reduction of a hard cycle at E alone

The variational reduction of E is applied to the mixed inequalities of the cycle
(`HardInput.E_source_relaxation`). The cycle `eInteriorCycle` changes only the point and frame of
E, so the losses already recorded on the circles of H, A, B, D stay separate. Whether the original
E is interior is tested before the move, and an interior E gives a strict loss on its original
circle (`HardInput.reduce_ordered_E`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
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

/-- On an aligned hard input with the frame of E between those of D and H, a hard input at the same
`q` that differs only at E, with E on a face `E.y = 0`, `θ_E = θ_D` or `θ_E = θ_H`, owners `3` on
DE and `1` on EH, no anchor circle larger, and a strict anchor loss when the original E is
interior. -/
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
end SquaresInCircles.Eight
end
end
end

section
/-!
## Ordered endpoints of a positive E pair

For a positive pair of primary projections with ordered anchor coordinates `D ≤ B`, the endpoint
at the same radius is an `OrderedEndpoint` (`ordered_endpoint`). The candidate with zero tangent is
removed by the alignment on the same circle with strict slack on the opposite side
(`maximal_guards`); a diagonal candidate stays an alternative, for the quarter-word argument. The
output includes the strict coordinate guards `-p.a < p.y` and, at zero first error, `p.y < p.a`,
needed for both positive quarter gaps.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EPairOrderedEndpoint
open PairedPrimary

structure OrderedEndpoint (q B D t : ℝ) extends PairedPrimary.Endpoint q B D t where
  lower_strict : -point.a<point.y
  aligned_upper_strict : firstError=0 → point.y<point.a

theorem maximal_guards {q B u y : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q)
    (hu : u∈Icc 0 (7/10:ℝ)) (hy : |y|≤diagonalCoordinate q)
    (hf : 0≤contact q B u y)
    (hmax : y=diagonalCoordinate q ∨ contact q B u y=0) :
    -(arc q y).a<y ∧ (u=0 → y<(arc q y).a) := by
  obtain ⟨hcl,hcu,hAl,hAu⟩ := uniform_circle_reserves hQL hQU
  obtain ⟨hs,ho,hcore⟩ := SignedPoint.outerAt_spec hQL hy
  have ha := (SignedPoint.outer_bounds hs ho).1
  have hylo : -diagonalCoordinate q<y := by
    have hh := (abs_le.mp hy).1
    apply lt_of_le_of_ne hh
    intro heq
    have heq' : y= -diagonalCoordinate q := heq.symm
    rcases hmax with hp | hz
    · linarith
    · have hstrict := lower_diagonal_strict hQL hQU hB.1 hu
      rw [heq'] at hz
      linarith
  refine ⟨by linarith,?_⟩
  intro hu0
  have hyB : y≤B-1 := by
    have h := hf
    simp [hu0,contact] at h
    linarith
  have hBupper : B<283/200 := by
    dsimp [axisCoordinate] at hB
    linarith [hB.2]
  linarith

theorem ordered_endpoint {q B D u v : ℝ} {p : SignedPoint}
    (hQL : qLow≤q) (hQU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q) (hDB : D≤B)
    (hu : 0≤u) (hv : 0≤v) (ht0 : 0<u+v) (ht : u+v≤7/10)
    (hs : p.Sorted) (hc : p.Contained q)
    (hfirst : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (hsecond : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    Nonempty (OrderedEndpoint q B D (u+v)) := by
  obtain ⟨hy0,hf0,hg0⟩ := outerization_preserves_pair hQL hs hc
    ⟨hu,by linarith⟩ ⟨hv,by linarith⟩ hfirst hsecond
  obtain ⟨u',y,hu',hy,hf,hg,hcases,hmax⟩ := intrinsic_endpoint
    hQL hQU hB ⟨ht0,ht⟩ ⟨hu,by linarith⟩ hy0 hf0 hg0
  obtain ⟨hps,hpo,hpc⟩ := SignedPoint.outerAt_spec hQL hy
  have hguard := maximal_guards hQL hQU hB ⟨hu'.1,hu'.2.trans ht⟩ hy hf hmax
  have hfirst' : edgeWidth u'≤B+(arc q y).a*Real.sin u'-y*Real.cos u' := by
    dsimp [contact] at hf
    linarith
  have hsecond' : edgeWidth (u+v-u')≤
      (arc q y).a*Real.sin (u+v-u')+y*Real.cos (u+v-u')+D := by
    dsimp [required] at hg
    linarith
  have make (he : u'=0 ∨ u'=u+v ∨ (arc q y).y=(arc q y).a) :
      Nonempty (OrderedEndpoint q B D (u+v)) := by
    exact ⟨{
      point := arc q y
      firstError := u'
      first_mem := hu'
      sorted := hps
      outer := hpo
      avoids_core := hpc
      first_feasible := hfirst'
      second_feasible := hsecond'
      endpoint := he
      lower_strict := hguard.1
      aligned_upper_strict := hguard.2 }⟩
  by_cases hu0 : u'=0
  · exact make (Or.inl hu0)
  by_cases hut : u'=u+v
  · exact make (Or.inr (Or.inl hut))
  rcases hcases with h | h | h | h
  · exact (hu0 h).elim
  · exact (hut h).elim
  · subst y
    have huPos : 0<u' := lt_of_le_of_ne hu'.1 (Ne.symm hu0)
    have hvPos : 0<u+v-u' := by linarith [lt_of_le_of_ne hu'.2 hut]
    have hcontact : contact q B u' 0=0 := by
      rcases hmax with hh | hh
      · have hdiag := (uniform_circle_reserves hQL hQU).1
        linarith
      · exact hh
    obtain ⟨hss,hoo,hcc,hyy,hfnew,hgnew⟩ := zero_tangent_alignment_ordered
      hQL hQU hB.1 hDB huPos hvPos (by linarith) hcontact (by simpa using hg)
    have hdiag := (uniform_circle_reserves hQL hQU).1
    have hyneg : B-1<0 := by simpa [arc,SignedPoint.outerAt] using hyy
    have hyinner : |B-1|<diagonalCoordinate q := by
      rw [abs_of_neg hyneg]
      linarith [hB.1]
    have hstrict := strict_sorting_of_inner_tangent hQL hyinner
    refine ⟨{
      point := arc q (B-1)
      firstError := 0
      first_mem := ⟨le_rfl,ht0.le⟩
      sorted := hss
      outer := hoo
      avoids_core := hcc
      first_feasible := by simpa using hfnew.ge
      second_feasible := by simpa using hgnew.le
      endpoint := Or.inl rfl
      lower_strict := ?_
      aligned_upper_strict := ?_ }⟩
    · have hh := (abs_lt.mp hstrict).1
      simpa [arc,SignedPoint.outerAt] using hh
    · intro _
      have hh := (abs_lt.mp hstrict).2
      simpa [arc,SignedPoint.outerAt] using hh
  · apply make
    right; right
    have ha := (arc_diagonal hQL).1
    simpa [h,arc,SignedPoint.outerAt] using ha.symm

end SquaresInCircles.Eight.EPairOrderedEndpoint
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EZeroCapEndpoints
open EZeroFunctions EZeroCapped HardSplitCap

theorem feasible {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    HardSplitCap.Feasible qCap (3/2-capped t) := by
  have hb := capped_bounds ht
  have hpos : 0≤5/2-capped t := by linarith
  have hupper : 5/2-capped t≤171/100 := by linarith
  have hsq := pow_le_pow_left₀ hpos hupper 2
  refine ⟨le_rfl,by linarith,?_⟩
  dsimp [qCap]
  nlinarith

theorem zero_cap (t : ℝ) : cap qCap (3/2-capped t) 0=W t := by
  simp [cap,root,contact,W]
  congr 2
  ring

theorem first_endpoint {e d : ℝ} (he : 0≤e) (hd : 0≤d) (ha : e+d≤7/10) :
    cap qCap (3/2-capped e) 0+cap qCap (3/2-capped d) (e+d)<2 := by
  by_contra! hbad
  have he' : e∈Icc 0 (7/10 : ℝ) := ⟨he,by linarith⟩
  have hd' : d∈Icc 0 (7/10 : ℝ) := ⟨hd,by linarith⟩
  have ha' : e+d∈Icc 0 (7/10 : ℝ) := ⟨by linarith,ha⟩
  let L := cap qCap (3/2-capped d) (e+d)
  let Z := cornerX qCap (3/2-capped d) (e+d)
  have hL : Yc e≤L := by
    rw [zero_cap] at hbad
    dsimp [Yc,L]
    linarith
  have hb := nested_bounds he'
  have hY : 0≤Yc e := by linarith [hb.2.2.1]
  have hYsq := pow_le_pow_left₀ hY hL 2
  have hnorm : Z^2+L^2=qCap := corner_norm (feasible hd') ha'
  have hcontact : (Z-1)*Real.cos (e+d)-L*Real.sin (e+d)=3/2-capped d :=
    corner_contact _ _ _
  have hZ : 0<Z := cornerX_pos (feasible hd') ha'
  have hcorner := corner_square he'
  have hX : Z≤Xc e+1 := by nlinarith [hb.2.2.2.2.1]
  obtain ⟨hc,hc1,hs,hs1,_⟩ := transport_trig ha'
  have hcos := mul_le_mul_of_nonneg_right hX (show 0≤Real.cos (e+d) by linarith)
  have hsin := mul_le_mul_of_nonneg_right hL hs
  have hF : (3/2 : ℝ)≤Fc e d := by
    dsimp [Fc]
    linarith
  linarith [EZeroCapped.maximum he hd ha]

theorem second_endpoint {e d : ℝ} (he : 0≤e) (hd : 0≤d) (ha : e+d≤7/10) :
    cap qCap (3/2-capped e) (e+d)+cap qCap (3/2-capped d) 0<2 := by
  have hh := first_endpoint hd he (by simpa [add_comm] using ha)
  simpa [add_comm] using hh

end SquaresInCircles.Eight.EZeroCapEndpoints
end
end
end
