module

public import SquaresInCircles.Eight.TableFree.PairOrder
public import SquaresInCircles.Eight.TableFree.GlobalGASourceDomain
public import SquaresInCircles.Eight.TableFree.GlobalZeroSignBridge

/-!
# Actual high-GA boundary order after a T-only primary-pair move

Uncompiled transcription of the boundary-neighbor checks in the positive
paired-T and signed-cancellation hand proofs.  The five unchanged gaps
retain their original positive lifts.  The two changed gaps are checked
from the actual BT/TD projections, and the two-square central-band theorem
selects the positive lift.  No normal-GA owner premise is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.TTransport
open Candidate SignedCycle

/-- Only the actual selected axis on this edge is needed for the central
band; membership in a subsequently proved owner family is irrelevant. -/
theorem direction_separation {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (i : Vertex) (j : Fin 4)
    (hf : C.Feasible i j) :
    19/25<dist (C.polarAngle i : Direction) (C.polarAngle (next i) : Direction) := by
  have hr (k : Vertex) : 0<Real.sqrt ((C.point k).a^2+|(C.point k).y|^2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [(hn.sorted k).1,sq_nonneg |(C.point k).y|]
  have hcore (k : Vertex) : CoreAvoiding (C.actualSquare k) :=
    (SignedPoint.square_core_iff (hn.sorted k) (C.actualAngle k)).2 (hn.core k)
  have haxis : (forwardAxis j).Feasible (C.actualSquare i) (C.actualSquare (next i)) :=
    (C.actualSquare_feasible i j).2 hf
  exact exterior_pair_gap (by simpa [qCap,Q0] using hq)
    (actualSquare_contained hn.sorted hn.contained i)
    (actualSquare_contained hn.sorted hn.contained (next i))
    (hcore i) (hcore (next i)) (hr i) (hr (next i))
    (actualSquare_polar hn.sorted i).1 (actualSquare_polar hn.sorted i).2
    (actualSquare_polar hn.sorted (next i)).1
    (actualSquare_polar hn.sorted (next i)).2 (SignedAxis.disjoint haxis)

private theorem negative_gap_distance (β : Vertex → ℝ) (i : Vertex)
    (hp : angleGap β i≤0) (hu : -angleGap β i≤Real.pi) :
    dist (β i : Direction) (β (next i) : Direction)= -angleGap β i := by
  have he : ((angleGap β i : ℝ) : Direction)=
      (β (next i) : Direction)-(β i : Direction) := by
    by_cases hi : i=6 <;>
      simp [angleGap,hi,Real.Angle.coe_add,Real.Angle.coe_sub,Real.Angle.coe_two_pi]
  have hn : ((-angleGap β i : ℝ) : Direction)=
      (β i : Direction)-(β (next i) : Direction) := by
    rw [Real.Angle.coe_neg,he,neg_sub]
  rw [direction_dist,←hn]
  exact Real.Angle.abs_toReal_coe_eq_self_iff.2 ⟨neg_nonneg.mpr hp,hu⟩

/-- A real gap already above the negative central band must lie on the
positive branch when the neighboring squares are genuinely separated. -/
theorem positive_gap {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (i : Vertex) (j : Fin 4)
    (hf : C.Feasible i j) (hl : -(19/25:ℝ)<C.physicalGap i) :
    19/25<C.physicalGap i := by
  have hsep := direction_separation hn hq i j hf
  have hp : 0<C.physicalGap i := by
    by_contra! hnp
    have hg : angleGap C.polarAngle i≤0 := by rwa [polarAngle_gap]
    have hu : -angleGap C.polarAngle i≤Real.pi := by
      rw [polarAngle_gap]
      linarith [Real.pi_gt_three]
    rw [negative_gap_distance C.polarAngle i hg hu,polarAngle_gap] at hsep
    linarith
  by_contra! hsmall
  have hg : 0≤angleGap C.polarAngle i := by rw [polarAngle_gap]; exact hp.le
  have hu : angleGap C.polarAngle i≤Real.pi := by
    rw [polarAngle_gap]
    linarith [Real.pi_gt_three]
  rw [angleGap_direction_distance C.polarAngle i hg hu,polarAngle_gap] at hsep
  linarith

def owner {q : ℝ} {C : SignedCycle} (w : Vertex → Fin 4)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    Vertex → Fin 4 := ![w H,w G,w A,O.btOwner,O.tdOwner,w D,w E]

theorem feasible {q : ℝ} {C : SignedCycle} (w : Vertex → Fin 4)
    (hf : ∀i,C.Feasible i (w i))
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    ∀i,(O.cycle C).Feasible i (owner w O i) := by
  intro i
  fin_cases i
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,H,G,T] using hf H
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,G,A,T] using hf G
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,A,B,T] using hf A
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,B,T,D,quarterFeasible] using sub_nonneg.mpr O.BT
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,B,T,D,zeroFeasible] using sub_nonneg.mpr O.TD
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,T,D,E] using hf D
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,H,T,E] using hf E

theorem allowed {q : ℝ} {C : SignedCycle} (w : Vertex → Fin 4)
    (hw : ∀i,w i∈highGAOwners i)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    ∀i,owner w O i∈highGAOwners i := by
  intro i
  fin_cases i
  · simpa [owner,H] using hw H
  · simpa [owner,G] using hw G
  · simpa [owner,A] using hw A
  · rcases O.bt_allowed with h|h <;> simp [owner,h,highGAOwners,B]
  · rcases O.td_allowed with h|h <;> simp [owner,h,highGAOwners,T]
  · simpa [owner,D] using hw D
  · simpa [owner,E] using hw E

/-- The source order is used only for unchanged gaps.  The changing TD
gap uses the true output owner and its proven canceling-sign implication. -/
theorem ordered {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (ho : C.Ordered) (hq : q≤qCap)
    (hDy : (C.point D).y≤0) (w : Vertex → Fin 4)
    (hf : ∀i,C.Feasible i (w i))
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    (O.cycle C).Ordered := by
  let C' := O.cycle C
  have hn' : C'.Necessary q := O.necessary hn
  have hf' := feasible w hf O
  have hD' : (C'.point D).y≤0 := by
    simpa [C',TPairOutput.cycle,replacePoint,T,D] using hDy
  have hang := localAngle_mem hn'.sorted
  have hDangle := localAngle_nonpos (hn'.sorted D) hD'
  have hdelta (i : Vertex) : -(7/10:ℝ)≤delta C'.theta i :=
    (abs_le.mp (hn'.spread (next i) i)).1
  have hlow (i : Vertex) : -(19/25:ℝ)<C'.physicalGap i := by
    by_cases hiB : i=B
    · subst i
      have he : C'.physicalGap B=Real.pi/2+delta C'.theta B+
          C'.localAngle B-C'.localAngle T := by simp [physicalGap,word,next,B,T]
      rw [he]
      linarith [(hang B).1,(hang T).2,hdelta B]
    by_cases hiT : i=T
    · subst i
      have he : C'.physicalGap T=delta C'.theta T+C'.localAngle T-C'.localAngle D := by
        simp [physicalGap,word,next,T,D]
      rw [he]
      by_cases hy : 0≤(C'.point T).y
      · have hTangle := localAngle_nonneg (hn'.sorted T) hy
        linarith [hdelta T]
      · have hyneg : (C'.point T).y<0 := lt_of_not_ge hy
        have hj : O.tdOwner=2 := by
          rcases O.td_allowed with h|h
          · have hpos := O.canceling_normal h
            have hyO : O.point.y<0 := by
              simpa [C',TPairOutput.cycle,replacePoint] using hyneg
            linarith
          · exact h
        have hTD : zeroFeasible (C'.point T) (C'.point D) (delta C'.theta T) 2 := by
          simpa [C',TPairOutput.cycle,replacePoint,delta,next,T,D,hj] using O.TD
        have hDb := (SignedPoint.coordinate_bounds (hn'.sorted D)
          (hn'.core D) (hn'.contained D) hq).2.2
        have hTu := (SignedPoint.coordinate_bounds (hn'.sorted T)
          (hn'.core T) (hn'.contained T) hq).2.1
        have hd := td2_nonpositive_tangent_error_lower
          ((neg_le_abs _).trans_lt hDb) (hn'.sorted T).1 hTu hyneg.le
          (hn'.spread D T) hTD
        have hδ : delta C'.theta T=C'.theta D-C'.theta T := by simp [delta,next,T,D]
        linarith [(hang T).1,pi_lt_22_over_7]
    · have he : C'.physicalGap i=C.physicalGap i := by
        fin_cases i <;>
          simp [C',TPairOutput.cycle,replacePoint,physicalGap,localAngle,
            word,delta,next,B,T] at hiB hiT ⊢
      rw [he]
      linarith [ho.gap_pos i]
  have hlower (i : Vertex) : 19/25<C'.physicalGap i :=
    positive_gap hn' hq i (owner w O i) (hf' i) (hlow i)
  have hupper := seven_gaps_three_quarters C'.polarAngle (fun i => by
    rw [polarAngle_gap]
    exact hlower i)
  constructor
  · intro i
    linarith [hlower i]
  · intro i
    have hh := hupper i
    rw [polarAngle_gap] at hh
    linarith [Real.pi_pos]

end SquaresInCircles.Eight.TableFree.GlobalGA.TTransport
