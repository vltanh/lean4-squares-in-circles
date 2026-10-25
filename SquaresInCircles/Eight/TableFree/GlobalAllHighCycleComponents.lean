module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighZero

/-!
# The actual cyclic quarter and zero components

One potential is assigned to each original physical vertex.  Original
owner classification, radial anchors, and the global variation theorem
supply all component hypotheses.  The six charged edges below are
ready for the remaining original outer DE bridge.  Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

open Candidate FramePair GlobalOuterAnchor

def cyclePotential (C : BoundaryCycle Q0) (i : Vertex) : ℝ :=
  if word i=0 then kappa*transverse (stateOf C i) else potential (stateOf C i)
def cycleCharge (C : BoundaryCycle Q0) (theta : Vertex→ℝ) (i : Vertex) : ℝ :=
  Candidate.phi theta i+(cyclePotential C i-cyclePotential C (next i))

theorem cycleCharge_sum (C : BoundaryCycle Q0) (theta : Vertex→ℝ) :
    (∑i,cycleCharge C theta i)=2*Real.pi := by
  simp only [cycleCharge,Finset.sum_add_distrib,sum_phi,sum_marker_difference,add_zero]

theorem cycleCharge_zero (C : BoundaryCycle Q0) (theta : Vertex→ℝ)
    (i : Vertex) (hi : word i=0) (hn : word (next i)=1) :
    cycleCharge C theta i=zeroCharge (stateOf C i) (stateOf C (next i)) (delta theta i) := by
  simp [cycleCharge,cyclePotential,Candidate.phi,hi,hn,zeroCharge] <;> ring

theorem cycleCharge_quarter (C : BoundaryCycle Q0) (theta : Vertex→ℝ)
    (i : Vertex) (hi : word i=1) (hn : word (next i)=0) :
    cycleCharge C theta i=Real.pi/2+
      quarterCharge (stateOf C i) (transverse (stateOf C (next i))) (delta theta i) := by
  simp [cycleCharge,cyclePotential,Candidate.phi,hi,hn,quarterCharge] <;> ring

theorem cycleCharge_DE (C : BoundaryCycle Q0) (theta : Vertex→ℝ) :
    cycleCharge C theta D=Real.pi/2+delta theta D+potential (stateOf C D)-potential (stateOf C E) := by
  simp [cycleCharge,cyclePotential,Candidate.phi,word,D,E,next] <;> ring

theorem state_outer_of_kind (C : BoundaryCycle Q0) (i : Vertex) (hi : C.kind i=.outer) :
    (stateOf C i).branch.type≠0 := by
  intro hc
  exact ((branchOf_core_iff C i).1 hc) hi

theorem state_transverse_eq (C : BoundaryCycle Q0) (i : Vertex) :
    transverse (stateOf C i)=C.a i*C.tangent i := by
  simp only [transverse,stateOf,signOf_spec,BoundaryCycle.tangent]
  field_simp [(C.a_pos i).ne']

theorem state_positive_of_tangent (C : BoundaryCycle Q0) (i : Vertex)
    (hi : 0<C.tangent i) : 0<transverse (stateOf C i) := by
  rw [state_transverse_eq]
  exact mul_pos (C.a_pos i) hi

theorem state_negative_of_tangent (C : BoundaryCycle Q0) (i : Vertex)
    (hi : C.tangent i<0) : transverse (stateOf C i)<0 := by
  rw [state_transverse_eq]
  exact mul_neg_of_pos_of_neg (C.a_pos i) hi

theorem frame_state_feasible {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (i : Vertex) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (stateOf C i).Feasible (stateOf C (next i)) j (Candidate.phi F.theta i) := by
  have hh := stateOf_feasible C i j haxis
  have hphase : pairAngle C i=Candidate.phi F.theta i :=
    (pairAngle_gap C i).trans (F.physical_angle i).symm
  rwa [hphase] at hh

/-- A high quarter followed by a zero supplies every domain condition
of the complete quarter theorem directly on the physical states. -/
theorem frame_quarter_charge {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (i : Vertex) (hi : word i=1) (hn : word (next i)=0)
    (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    Real.pi/2+kappa≤cycleCharge C F.theta i := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hs := GlobalQuarterOuter.frame_high_anchor F hq i hi j hj haxis
  have ht : (stateOf C (next i)).branch.type≠0 ∨
      0<transverse (stateOf C (next i)) := by
    by_cases hp : 0<C.tangent (next i)
    · exact Or.inr (state_positive_of_tangent C (next i) hp)
    · exact Or.inl (state_outer_of_kind C (next i)
        (GlobalZeroSourceOuter.frame_nonpositive_source_outer F hq (next i) hn
          (le_of_not_gt hp)))
  have hm := frame_state_feasible F i j haxis
  have hm' : (stateOf C i).Feasible (stateOf C (next i)) j
      (Real.pi/2+delta F.theta i) := by
    simpa [Candidate.phi,hi] using hm
  have hc := high_quarter_charge (stateOf C i) (stateOf C (next i))
    (state_outer_of_kind C i hs.1) (state_negative_of_tangent C i hs.2).le ht hj
    (by simpa only [frameCap] using (F.delta_small i).le) hm'
  rw [cycleCharge_quarter C F.theta i hi hn]
  linarith [hc.1]

/-- The following high quarter makes the zero target a negative outer
anchor.  Its original zero witness is then classified independently. -/
theorem frame_zero_charge {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (i : Vertex) (hi : word i=0) (hn : word (next i)=1)
    (j p : Fin 4) (hp : p=2 ∨ p=3)
    (hzero : (forwardAxis j).Feasible (C.square i) (C.square (next i)))
    (hquarter : (forwardAxis p).Feasible (C.square (next i)) (C.square (next (next i)))) :
    gammaZero-7/1000<cycleCharge C F.theta i ∧
      (delta F.theta i≤7/20 → gammaZero≤cycleCharge C F.theta i) := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have ht := GlobalQuarterOuter.frame_high_anchor F hq (next i) hn p hp hquarter
  have hj := GlobalZeroSign.of_frame F hq i hi j hzero
  have hjOwner : j=0 ∨ j=2 := hj.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hsource : j=0 → 0<transverse (stateOf C i) := by
    intro hj0
    rcases hj with ⟨_,hy⟩ | ⟨hj2,_⟩
    · exact state_positive_of_tangent C i hy
    · norm_num [hj0] at hj2
  have hm := frame_state_feasible F i j hzero
  have hm' : (stateOf C i).Feasible (stateOf C (next i)) j (delta F.theta i) := by
    simpa [Candidate.phi,hi] using hm
  have hc := zero_charge (stateOf C i) (stateOf C (next i))
    (state_outer_of_kind C (next i) ht.1) (state_negative_of_tangent C (next i) ht.2).le
    hjOwner (by simpa only [frameCap] using (F.delta_small i).le) hm' hsource
  rw [cycleCharge_zero C F.theta i hi hn]
  exact ⟨hc.1,fun hshort => hc.2 (Or.inl hshort)⟩

theorem frame_three_quarters {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) :
    3*(Real.pi/2+kappa)≤
      cycleCharge C F.theta E+cycleCharge C F.theta G+cycleCharge C F.theta B := by
  have hE := frame_quarter_charge F E (by norm_num [word,E])
    (by norm_num [word,E,next]) (owner E) (hhigh E (by norm_num [word,E])) (hf E)
  have hG := frame_quarter_charge F G (by norm_num [word,G])
    (by norm_num [word,G,next]) (owner G) (hhigh G (by norm_num [word,G])) (hf G)
  have hB := frame_quarter_charge F B (by norm_num [word,B])
    (by norm_num [word,B,next]) (owner B) (hhigh B (by norm_num [word,B])) (hf B)
  linarith

theorem frame_three_zeros {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) :
    3*gammaZero-7/1000<
      cycleCharge C F.theta H+cycleCharge C F.theta A+cycleCharge C F.theta T := by
  have hz (i : Vertex) (hi : word i=0) (hn : word (next i)=1) :=
    frame_zero_charge F i hi hn (owner i) (owner (next i)) (hhigh (next i) hn) (hf i) (hf (next i))
  have hH := hz H (by norm_num [word,H]) (by norm_num [word,H,next])
  have hA := hz A (by norm_num [word,A]) (by norm_num [word,A,next])
  have hT := hz T (by norm_num [word,T]) (by norm_num [word,T,next])
  have hv := (FramePhysicalTransport.candidate_variations F
    (by norm_num [Q0] : Q0∈Icc (5/2:ℝ) Q0)).1
  change positiveVariation F.theta<frameCap at hv
  have hpartial : max (delta F.theta H) 0+max (delta F.theta A) 0+
      max (delta F.theta T) 0<frameCap := by
    have hG := positivePart_nonneg (delta F.theta G)
    have hB := positivePart_nonneg (delta F.theta B)
    have hD := positivePart_nonneg (delta F.theta D)
    have hE := positivePart_nonneg (delta F.theta E)
    simp [positiveVariation,positivePart,Fin.sum_univ_succ] at hv
    dsimp [positivePart,G,B,D,E] at hG hB hD hE
    dsimp [H,A,T]
    linarith
  exact three_zero_charge_bound hpartial hH hA hT

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
