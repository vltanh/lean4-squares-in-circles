module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighBridgeCap

/-!
# Exclusion of the complete original all-high quarter branch

The actual DE cap, its complete owner theorem, all three repeated
quarter charges and the shared three-zero loss now telescope on one
physical cycle.  Fixed-ray expansion preserves every supplied original
weak axis, so the exclusion holds at the original radius.  Uncompiled
source draft.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

open Candidate FramePair GlobalOuterAnchor

theorem frame_DE_charge {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) :
    (957/1000:ℝ)<cycleCharge C F.theta D := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hD := GlobalQuarterOuter.frame_high_anchor F hq D (by norm_num [word,D])
    (owner D) (hhigh D (by norm_num [word,D])) (hf D)
  have hE := GlobalQuarterOuter.frame_high_anchor F hq E (by norm_num [word,E])
    (owner E) (hhigh E (by norm_num [word,E])) (hf E)
  have hDy := (state_negative_of_tangent C D hD.2).le
  have hEy := (state_negative_of_tangent C E hE.2).le
  have hcap := Bridge.original_cap F hDy hEy
  have haxis := frame_state_feasible F D (owner D) (hf D)
  have haxis' : (stateOf C D).Feasible (stateOf C E) (owner D)
      (Real.pi/2+delta F.theta D) := by
    simpa [Candidate.phi,word,D,E,next] using haxis
  have hh := Bridge.owner_charge (stateOf C D) (stateOf C E)
    (state_outer_of_kind C D hD.1) (state_outer_of_kind C E hE.1) hDy hEy
    (hhigh D (by norm_num [word,D]))
    (by simpa only [frameCap] using (F.delta_small D).le) haxis' hcap
  rw [cycleCharge_DE]
  exact hh

theorem strict_cyclic_reserve :
    Real.pi/2<6*kappa*(1-FramePair.c0)+19/20 := by
  have hc := Bridge.c0_precise.2
  have hp := Arithmetic.two_pi_lt_710_over_113
  dsimp [kappa]
  linarith

theorem ceiling_all_high_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) : False := by
  have hquarter := frame_three_quarters F owner hf hhigh
  have hzero := frame_three_zeros F owner hf hhigh
  have hDE := frame_DE_charge F owner hf hhigh
  have hsum := cycleCharge_sum C F.theta
  rw [Fin.sum_univ_seven] at hsum
  dsimp [H,G,A,B,T,D,E,gammaZero] at hquarter hzero hDE
  have hr := strict_cyclic_reserve
  linarith only [hquarter,hzero,hDE,hsum,hr]

/-- Every supplied axis survives the fixed-ray expansion.  The
contradiction therefore classifies the original witnesses at q. -/
theorem frame_all_high_false {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) : False := by
  let K := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C K := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame K := FramePhysicalTransport.candidatePushforward F hR le_rfl
  apply ceiling_all_high_false F' owner
  · intro i
    exact hR.preserves_all_axes i (forwardAxis (owner i)) (hf i)
  · exact hhigh

theorem frame_some_low_quarter {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i))) :
    ∃i,word i=1 ∧ (owner i=0 ∨ owner i=1) := by
  by_contra hn
  have splitOwner (j : Fin 4) : (j=0 ∨ j=1) ∨ (j=2 ∨ j=3) := by
    fin_cases j <;> simp
  apply frame_all_high_false F hq owner hf
  intro i hi
  rcases splitOwner (owner i) with hlo | hhi
  · exact (hn ⟨i,hi,hlo⟩).elim
  · exact hhi

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
