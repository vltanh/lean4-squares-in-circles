module

public import SquaresInCircles.Eight.Owners.Direct.NegativeTCycle

/-!
# Eight squares: the actual cycle at an unconverted negative-T order barrier

A barrier is a complete necessary seven-cycle retaining
GA0, BT3, the original HG implication, and both original mixed witnesses.
Its H frame is at or below D. No assertion that such a state is impossible
is built into this construction; that is the separate global anchor-order
theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate

structure NegativeTBarrier (q : ℝ) where
  cycle : SignedCycle
  necessary : cycle.Necessary q
  anchors_normal : cycle.NormalAnchors
  E_nonpos : (cycle.point E).y≤0
  witnesses : cycle.Witnesses
  zero_signs : cycle.ZeroSignImplications witnesses
  GA_hard : cycle.Feasible G 0
  BT_secondary : cycle.Feasible B 3
  BT_unavailable : ¬cycle.Feasible B 2
  TD_aligned : cycle.theta T=cycle.theta D
  negative_BT : cycle.theta D<cycle.theta B
  T_nonneg : 0≤(cycle.point T).y
  H_not_above : cycle.theta H≤cycle.theta D

namespace DirectNegativeT

structure LocalBarrier {q t : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (E H : SignedPoint) (e h : ℝ) (jDE jEH : Fin 4) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  Dpoint : SignedPoint
  Tpoint : SignedPoint
  Epoint : SignedPoint
  Etheta : ℝ
  E_frame : Etheta=e ∨ Etheta∈Icc (-t) 0
  E_advance : e≤Etheta
  D_sorted : Dpoint.Sorted
  T_sorted : Tpoint.Sorted
  E_sorted : Epoint.Sorted
  D_core : Dpoint.AvoidsCore
  T_core : Tpoint.Core
  E_core : Epoint.AvoidsCore
  D_circle_nonincrease : Dpoint.circle≤D.circle
  T_inside : Tpoint.circle<q
  E_contained : Epoint.Contained q
  E_radial : Epoint.Boundary q
  E_circle_nonincrease : Epoint.circle≤E.circle
  D_negative : Dpoint.y<0
  T_positive : 0<Tpoint.y
  E_nonpos : Epoint.y≤0
  TD0 : zeroFeasible Tpoint Dpoint 0 0
  BT3 : quarterFeasible B Tpoint (-angle) 3
  BT_unavailable : ¬quarterFeasible B Tpoint (-angle) 2
  DE : quarterFeasible Dpoint Epoint (Etheta+angle) jDE
  EH : quarterFeasible Epoint H (h-Etheta) jEH
  bad_order : h+angle≤0

theorem LocalBarrier.angle_positive {q t e h : ℝ} {D T B E H : SignedPoint}
    {I : Source q t D T B} {jDE jEH : Fin 4}
    (O : LocalBarrier I E H e h jDE jEH) : 0<O.angle := by
  apply lt_of_le_of_ne O.angle_mem.1
  intro heq
  have hBT3 : quarterFeasible B O.Tpoint 0 3 := by simpa [← heq] using O.BT3
  have hBT2 : quarterFeasible B O.Tpoint 0 2 := (quarter_high_tie _ _).2 hBT3
  exact O.BT_unavailable (by simpa [← heq] using hBT2)

namespace LocalBarrier

variable {q : ℝ} {C : SignedCycle}
variable {I : Source q (C.theta B-C.theta D) (C.point D) (C.point T) (C.point B)}
variable {jDE jEH : Fin 4}

def cycle (O : LocalBarrier I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH) : SignedCycle :=
  replaceTDE C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta

theorem unchanged (O : LocalBarrier I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (i : Vertex) (hiD : i≠D) (hiT : i≠T) (hiE : i≠E) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i :=
  replaceTDE_unchanged C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta i hiD hiT hiE

theorem necessary (O : LocalBarrier I (C.point E) (C.point H)
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
    hnE O.D_sorted (O.D_circle_nonincrease.trans (hn.contained D)) O.D_core (Or.inr hDframe)
  apply SignedCycle.necessary_replace_clamped (v := T) (a := D) (b := D)
    hnD O.T_sorted O.T_inside.le O.T_core.ge
  right
  simp [replacePoint]

theorem normal (O : LocalBarrier I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (ha : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · rw [(O.unchanged H (by decide) (by decide) (by decide)).1]; exact ha.H_nonneg
  · rw [(O.unchanged A (by decide) (by decide) (by decide)).1]; exact ha.A_nonneg
  · rw [(O.unchanged B (by decide) (by decide) (by decide)).1]; exact ha.B_nonpos
  · simpa [cycle,replaceTDE,replacePoint,T,D,E] using O.D_negative.le

def witnesses (w : C.Witnesses)
    (O : LocalBarrier I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E)) :
    O.cycle.Witnesses where
  owner := ![w.owner H,w.owner G,w.owner A,3,w.owner T,w.owner D,w.owner E]
  feasible i := by
    fin_cases i
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta H
        (Or.inl rfl) _).2 (w.feasible H)
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta G
        (Or.inr (Or.inl rfl)) _).2 (w.feasible G)
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta A
        (Or.inr (Or.inr rfl)) _).2 (w.feasible A)
    · exact (replaceTDE_BT C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta 3).2 O.BT3
    · apply (replaceTDE_TD C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta _).2
      have hj : w.owner T=0 ∨ w.owner T=2 := by
        simpa [SignedCycle.normalOwners,T] using w.allowed T
      rcases hj with hj | hj
      · simpa [hj] using O.TD0
      · simpa [hj] using (zero_owner_tie _ _).1 O.TD0
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
    (O : LocalBarrier I (C.point E) (C.point H)
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
    (O : LocalBarrier I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (hz : C.ZeroSignImplications w) : O.cycle.Ordered :=
  SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses w) (O.zero_signs w hz)

def barrier (w : C.Witnesses)
    (O : LocalBarrier I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hn : C.Necessary q) (ha : C.NormalAnchors) (hz : C.ZeroSignImplications w)
    (hGA : C.Feasible G 0) : NegativeTBarrier q where
  cycle := O.cycle
  necessary := O.necessary hn
  anchors_normal := O.normal ha
  E_nonpos := by simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.E_nonpos
  witnesses := O.witnesses w
  zero_signs := O.zero_signs w hz
  GA_hard := (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta G
    (Or.inr (Or.inl rfl)) 0).2 hGA
  BT_secondary := (replaceTDE_BT C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta 3).2 O.BT3
  BT_unavailable := by
    intro hh
    exact O.BT_unavailable ((replaceTDE_BT C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta 2).1 hh)
  TD_aligned := by simp [cycle,replaceTDE,replacePoint,D,T,E]
  negative_BT := by
    have hh : C.theta B-O.angle<C.theta B := by linarith [O.angle_positive]
    simpa [cycle,replaceTDE,replacePoint,D,T,E,B] using hh
  T_nonneg := by simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.T_positive.le
  H_not_above := by
    have hh : C.theta H≤C.theta B-O.angle := by linarith [O.bad_order]
    simpa [cycle,replaceTDE,replacePoint,D,T,E,H] using hh

end LocalBarrier
end DirectNegativeT
end SquaresInCircles.Eight
