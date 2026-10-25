module

public import SquaresInCircles.Eight.Owners.Direct.NegativeTLocal
public import SquaresInCircles.Eight.Frames.Pair.Order
public import SquaresInCircles.Eight.Frames.Pair.TransportAssembly

/-!
# Eight squares: hard entry by the direct negative-T transport

The transport `replaceTDE` changes only D, T and E; H, G, A and B keep their points and frames, so
a loss already spent on the circle of H is kept exactly. The resulting hard input is ordered and
keeps the selected normals of DE, EH and TD (`hardInput`, `direct_negative_t_hard_entry`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace DirectNegativeT

private theorem feasible_T_iff (C : SignedCycle) (j : Fin 4) :
    C.Feasible T j ↔
      edgeWidth (delta C.theta T)≤zeroProjection (C.point T) (C.point D) (delta C.theta T) j := by
  have hw : Candidate.word T=0 := by decide
  have hn : next T=D := by decide
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,hw,↓reduceIte,hn,sub_nonneg]

private theorem feasible_B_iff (C : SignedCycle) (j : Fin 4) :
    C.Feasible B j ↔
      edgeWidth (delta C.theta B)≤quarterProjection (C.point B) (C.point T) (delta C.theta B) j := by
  have hw : Candidate.word B=1 := by decide
  have hn : next B=T := by decide
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,hw,one_ne_zero,↓reduceIte,hn,
    sub_nonneg]

/-- The local source of the reflected D/T/B contact, which does not involve E; E and its mixed
witnesses keep their signed coordinates. -/
theorem sourceOfCycle {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (ha : C.NormalAnchors) (w : C.Witnesses)
    (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hy : 0≤(C.point T).y) (hBT : C.Feasible B 3) (hnot : ¬C.Feasible B 2) :
    Source q (C.theta B-C.theta D) (C.point D) (C.point T) (C.point B) := by
  have hδT : delta C.theta T=0 := by
    simpa [delta,next,T,D] using sub_eq_zero.mpr halign.symm
  have hδB : delta C.theta B= -(C.theta B-C.theta D) := by
    simp only [delta,next,B]
    change C.theta T-C.theta B= -(C.theta B-C.theta D)
    rw [halign]
    ring
  have hTD : zeroFeasible (C.point T) (C.point D) 0 (w.owner T) := by
    have h := (feasible_T_iff C _).1 (w.feasible T)
    rw [hδT] at h
    exact h
  have hTD2 : zeroFeasible (C.point T) (C.point D) 0 2 := by
    have hj : w.owner T=0 ∨ w.owner T=2 := by
      simpa [SignedCycle.normalOwners,T] using w.allowed T
    rcases hj with hj | hj
    · exact (zero_owner_tie _ _).1 (by simpa [hj] using hTD)
    · simpa [hj] using hTD
  have hBTr : quarterFeasible (C.point B) (C.point T) (-(C.theta B-C.theta D)) 3 := by
    have h := (feasible_B_iff C _).1 hBT
    rw [hδB] at h
    exact h
  exact {
    H_sorted := by simpa using hn.sorted D
    G_sorted := by simpa using hn.sorted T
    A_sorted := by simpa using hn.sorted B
    H_contained := by simpa using hn.contained D
    G_contained := by simpa using hn.contained T
    A_contained := by simpa using hn.contained B
    H_core := by simpa using hn.core D
    G_core := by simpa using hn.core T
    A_core := by simpa using hn.core B
    H_nonneg := by simpa [SignedPoint.reflect] using neg_nonneg.mpr ha.D_nonpos
    G_nonpos := by simpa [SignedPoint.reflect] using neg_nonpos.mpr hy
    A_nonneg := by simpa [SignedPoint.reflect] using neg_nonneg.mpr ha.B_nonpos
    tilt_pos := sub_pos.mpr ht
    tilt_cap := (le_abs_self _).trans (hn.spread B D)
    HG := by simpa [reflectedOwner] using (zeroFeasible_reflect _ _ 0 2).2 hTD2
    GA := by simpa [reflectedOwner] using (quarterFeasible_reflect _ _ _ 3).2 hBTr
    no_hard := by
      intro hh
      have hf : quarterFeasible (C.point B) (C.point T) (-(C.theta B-C.theta D)) 2 :=
        (quarterFeasible_reflect _ _ _ 2).1 (by simpa [reflectedOwner] using hh)
      apply hnot
      refine (feasible_B_iff C 2).2 ?_
      rw [hδB]
      exact hf }

def replaceTDE (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ) : SignedCycle :=
  replacePoint (replacePoint (replacePoint C E pE (C.theta B+ε))
    D pD (C.theta B-x)) T pT (C.theta B-x)

theorem replaceTDE_unchanged (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (i : Vertex) (hiD : i≠D) (hiT : i≠T) (hiE : i≠E) :
    (replaceTDE C pD pT pE x ε).point i=C.point i ∧
      (replaceTDE C pD pT pE x ε).theta i=C.theta i := by
  simp [replaceTDE,replacePoint,hiD,hiT,hiE]

theorem replaceTDE_BT (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (j : Fin 4) : (replaceTDE C pD pT pE x ε).Feasible B j ↔
      quarterFeasible (C.point B) pT (-x) j := by
  have heq : C.theta B-x-C.theta B= -x := by ring
  simp [replaceTDE,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,B,T,D,E,quarterFeasible,sub_nonneg]

theorem replaceTDE_TD (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (j : Fin 4) : (replaceTDE C pD pT pE x ε).Feasible T j ↔
      zeroFeasible pT pD 0 j := by
  simp [replaceTDE,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,B,T,D,E,zeroFeasible,sub_nonneg]

theorem replaceTDE_DE (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (j : Fin 4) : (replaceTDE C pD pT pE x ε).Feasible D j ↔
      quarterFeasible pD pE (ε+x) j := by
  have heq : C.theta B+ε-(C.theta B-x)=ε+x := by ring
  simp [replaceTDE,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,B,T,D,E,quarterFeasible,sub_nonneg]

theorem replaceTDE_EH (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (j : Fin 4) : (replaceTDE C pD pT pE x ε).Feasible E j ↔
      quarterFeasible pE (C.point H) (C.theta H-C.theta B-ε) j := by
  have heq : C.theta 0-(C.theta 3+ε)=C.theta 0-C.theta 3-ε := by ring
  simp [replaceTDE,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,B,T,D,E,quarterFeasible,sub_nonneg,heq]

theorem replaceTDE_other_feasible (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (i : Vertex) (hi : i=H ∨ i=G ∨ i=A) (j : Fin 4) :
    (replaceTDE C pD pT pE x ε).Feasible i j ↔ C.Feasible i j := by
  have hu : ∀ k : Vertex,k=H ∨ k=G ∨ k=A ∨ k=B →
      (replaceTDE C pD pT pE x ε).point k=C.point k ∧
        (replaceTDE C pD pT pE x ε).theta k=C.theta k := by
    intro k hk
    apply replaceTDE_unchanged <;> rcases hk with rfl | rfl | rfl | rfl <;> decide
  have h1 := hu i (by rcases hi with h | h | h <;> simp [h])
  have h2 := hu (next i) (by rcases hi with rfl | rfl | rfl <;> decide)
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,delta,h1.1,h1.2,h2.1,h2.2]

namespace LocalEndpoint

variable {q : ℝ} {C : SignedCycle}
variable {I : Source q (C.theta B-C.theta D) (C.point D) (C.point T) (C.point B)}
variable {jDE jEH : Fin 4}

def cycle (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH) : SignedCycle :=
  replaceTDE C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta

theorem unchanged (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (i : Vertex) (hiD : i≠D) (hiT : i≠T) (hiE : i≠E) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i :=
  replaceTDE_unchanged C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta i hiD hiT hiE

theorem necessary (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (hn : C.Necessary q) : O.cycle.Necessary q := by
  have hDB : C.theta D≤C.theta B := by linarith [I.tilt_pos]
  have hEframe : C.theta B+O.Etheta=C.theta E ∨
      C.theta B+O.Etheta∈Icc (min (C.theta D) (C.theta B)) (max (C.theta D) (C.theta B)) := by
    rcases O.E_frame with hh | hh
    · left; linarith
    · right
      rw [min_eq_left hDB,max_eq_right hDB]
      constructor <;> linarith [hh.1,hh.2]
  have hnE := SignedCycle.necessary_replace_clamped (v := E) (a := D) (b := B)
    hn O.E_sorted O.E_contained O.E_core hEframe
  have hDframe : C.theta B-O.angle∈
      Icc (min ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta D)
        ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta B))
      (max ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta D)
        ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta B)) := by
    simp only [replacePoint,Function.update_of_ne (by decide : D≠E),
      Function.update_of_ne (by decide : B≠E),min_eq_left hDB,max_eq_right hDB,mem_Icc]
    constructor <;> linarith [O.angle_mem.1,O.angle_mem.2]
  have hnD := SignedCycle.necessary_replace_clamped (v := D) (a := D) (b := B)
    hnE O.D_sorted (O.D_circle_loss.le.trans (hn.contained D)) O.D_core (Or.inr hDframe)
  apply SignedCycle.necessary_replace_clamped (v := T) (a := D) (b := D)
    hnD O.T_sorted O.T_inside.le O.T_core.ge
  right
  simp [replacePoint]

theorem normal (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (ha : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · rw [(O.unchanged H (by decide) (by decide) (by decide)).1]; exact ha.H_nonneg
  · rw [(O.unchanged A (by decide) (by decide) (by decide)).1]; exact ha.A_nonneg
  · rw [(O.unchanged B (by decide) (by decide) (by decide)).1]; exact ha.B_nonpos
  · simpa [cycle,replaceTDE,replacePoint,T,D,E] using O.D_negative.le

def witnesses (w : C.Witnesses)
    (O : LocalEndpoint I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E)) :
    O.cycle.Witnesses where
  owner := ![w.owner H,w.owner G,w.owner A,2,w.owner T,w.owner D,w.owner E]
  feasible i := by
    fin_cases i
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta H
        (Or.inl rfl) _).2 (w.feasible H)
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta G
        (Or.inr (Or.inl rfl)) _).2 (w.feasible G)
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta A
        (Or.inr (Or.inr rfl)) _).2 (w.feasible A)
    · exact (replaceTDE_BT C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta 2).2 O.BT2
    · apply (replaceTDE_TD C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta _).2
      have hj : w.owner T=0 ∨ w.owner T=2 := by
        simpa [SignedCycle.normalOwners,T] using w.allowed T
      rcases hj with hj | hj
      · simpa [hj] using O.TD0
      · simpa [hj] using O.TD2
    · exact (replaceTDE_DE C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta _).2 O.DE
    · exact (replaceTDE_EH C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta _).2 O.EH
  allowed i := by
    fin_cases i
    · simpa [H] using w.allowed H
    · simpa [G] using w.allowed G
    · simpa [A] using w.allowed A
    · norm_num [SignedCycle.normalOwners,B]
    · simpa [T] using w.allowed T
    · simpa [D] using w.allowed D
    · simpa [E] using w.allowed E

theorem zero_signs (w : C.Witnesses)
    (O : LocalEndpoint I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hz : C.ZeroSignImplications w) : O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro hj
    have hj' : w.owner H=2 := by simpa [witnesses,H] using hj
    rw [(O.unchanged G (by decide) (by decide) (by decide)).1]
    exact hz.HG_canceling hj'
  · intro _
    simpa [cycle,replaceTDE,replacePoint] using O.T_positive

theorem ordered (w : C.Witnesses)
    (O : LocalEndpoint I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (hz : C.ZeroSignImplications w) : O.cycle.Ordered :=
  SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses w) (O.zero_signs w hz)

theorem anchor_nonincrease (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH) :
    AnchorNonincrease C O.cycle := by
  intro i hi
  by_cases hiD : i=D
  · subst i
    simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.D_circle_loss.le
  · by_cases hiE : i=E
    · subst i
      simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.E_circle_nonincrease
    · have hiT : i≠T := by
        rintro rfl
        revert hi
        decide
      rw [(O.unchanged i hiD hiT hiE).1]

theorem strict_anchor_loss (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH) :
    StrictAnchorLoss C O.cycle := by
  refine ⟨D,by simp [anchorVertices],?_⟩
  simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.D_circle_loss

def hardInput (w : C.Witnesses)
    (O : LocalEndpoint I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hn : C.Necessary q) (ha : C.NormalAnchors) (hz : C.ZeroSignImplications w)
    (hGA : C.Feasible G 0) : SignedCycle.HardInput q where
  cycle := O.cycle
  necessary := O.necessary hn
  anchors_normal := O.normal ha
  E_nonpos := by simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.E_nonpos
  witnesses := O.witnesses w
  GA_hard := (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta G
    (Or.inr (Or.inl rfl)) 0).2 hGA
  BT_hard := (replaceTDE_BT C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta 2).2 O.BT2
  zero_signs := O.zero_signs w hz
  E_radial := by
    have hh := SignedPoint.boundary_radial_alternative O.E_sorted O.E_radial
      (hn.sorted H) O.D_sorted (hn.contained H)
      (O.D_circle_loss.le.trans (hn.contained D))
    simpa [cycle,replaceTDE,replacePoint,H,D,T,E] using hh

end LocalEndpoint

/-- The hard entry at the same `q`, keeping any loss already spent on the circle of H. Its inputs
are the cuts near H and the H–D span `θ_H - θ_D < 21/100`; E may be anywhere in the frame
interval. -/
theorem direct_negative_t_hard_entry {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hqL : qLow≤q) (hqU : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0) (hrE : (C.point E).Boundary q)
    (hHy : 211/250<(C.point H).y) (hHa : (C.point H).a<1)
    (hspan : C.theta H-C.theta D<21/100)
    (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3)
    (hnot : ¬C.Feasible B 2) (hGA : C.Feasible G 0) :
    ∃ J : SignedCycle.HardInput q,
      J.cycle.Ordered ∧ J.cycle.theta D=J.cycle.theta T ∧
      C.theta D<J.cycle.theta D ∧ J.cycle.theta D≤C.theta B ∧
      J.cycle.Feasible T (w.owner T) ∧ J.cycle.Feasible D (w.owner D) ∧
      J.cycle.Feasible E (w.owner E) ∧
      |(J.cycle.point D).y|<(J.cycle.point D).a ∧
      |(J.cycle.point T).y|<(J.cycle.point T).a ∧
      (J.cycle.point D).circle<(C.point D).circle ∧
      AnchorNonincrease C J.cycle ∧ StrictAnchorLoss C J.cycle ∧
      (∀ i, i≠D → i≠T → i≠E →
        J.cycle.point i=C.point i ∧ J.cycle.theta i=C.theta i) := by
  let I := sourceOfCycle hn ha w halign ht hyT hBT hnot
  have hHupper : (C.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (hn.sorted H) (hn.core H) (hn.contained H) hqU).2.2
  have hDEwidth : |(C.theta E-C.theta B)+(C.theta B-C.theta D)|≤7/10 := by
    rw [show (C.theta E-C.theta B)+(C.theta B-C.theta D)=C.theta E-C.theta D by ring]
    exact hn.spread E D
  have hEHwidth : |(C.theta H-C.theta B)-(C.theta E-C.theta B)|≤7/10 := by
    rw [show (C.theta H-C.theta B)-(C.theta E-C.theta B)=C.theta H-C.theta E by ring]
    exact hn.spread H E
  have hspan' : (C.theta H-C.theta B)+(C.theta B-C.theta D)<21/100 := by
    rw [show (C.theta H-C.theta B)+(C.theta B-C.theta D)=C.theta H-C.theta D by ring]
    exact hspan
  have hjDE : w.owner D=2 ∨ w.owner D=3 := by
    simpa [SignedCycle.normalOwners,D] using w.allowed D
  have hjEH : w.owner E=0 ∨ w.owner E=1 := by
    simpa [SignedCycle.normalOwners,E] using w.allowed E
  have hDE : quarterFeasible (C.point D) (C.point E)
      ((C.theta E-C.theta B)+(C.theta B-C.theta D)) (w.owner D) := by
    rw [show (C.theta E-C.theta B)+(C.theta B-C.theta D)=C.theta E-C.theta D by ring]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,D,E,quarterFeasible,sub_nonneg] using w.feasible D
  have hEH : quarterFeasible (C.point E) (C.point H)
      ((C.theta H-C.theta B)-(C.theta E-C.theta B)) (w.owner E) := by
    rw [show (C.theta H-C.theta B)-(C.theta E-C.theta B)=C.theta H-C.theta E by ring]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using w.feasible E
  obtain ⟨O⟩ := I.direct_endpoint hqL hqU ⟨hHy,hHupper⟩ (hn.sorted H) hHa
    (hn.sorted E) (hn.contained E) (hn.core E) hrE hyE hDEwidth hEHwidth hspan'
    (w.owner D) (w.owner E) hjDE hjEH hDE hEH
  let J := O.hardInput w hn ha hz hGA
  refine ⟨J,O.ordered w hn hqU ha hz,?_,?_,?_,(O.witnesses w).feasible T,
    (O.witnesses w).feasible D,(O.witnesses w).feasible E,?_,?_,?_,
    O.anchor_nonincrease,O.strict_anchor_loss,?_⟩
  · simp [J,LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
  · change C.theta D<O.cycle.theta D
    have hh : C.theta D<C.theta B-O.angle := by linarith [O.angle_mem.2]
    simpa [LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E] using hh
  · change O.cycle.theta D≤C.theta B
    have hh : C.theta B-O.angle≤C.theta B := by linarith [O.angle_mem.1]
    simpa [LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E] using hh
  · simpa [J,LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
      using O.D_nondiagonal
  · simpa [J,LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint]
      using O.T_nondiagonal
  · simpa [J,LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
      using O.D_circle_loss
  · exact O.unchanged

end DirectNegativeT
end SquaresInCircles.Eight
