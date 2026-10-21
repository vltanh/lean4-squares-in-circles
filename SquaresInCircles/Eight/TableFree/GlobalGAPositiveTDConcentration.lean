module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDStress

/-!
# The complete original-cycle positive-TD concentration invocation

Uncompiled source.  This is a necessary scalar inequality derived from
the actual seven weak axes, the original circle inequalities, and the
original signed variation.  Its continuous coefficient functions remain
free in their proved concavity domain, ready for the explicit weight
families and their scalar positivity proofs.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

def endpoint (k l c z : ℝ) (i j : Fin 4) : ℝ :=
  min (V R (pWeights k l (tilted c z) j) (qWeights k l (tilted c z) j) z)
    (if i=j then Hybrid.saturated R (diagonal-1/2)
      (pWeights k l (tilted c z)) (qWeights k l (tilted c z)) 3 i z
     else Hybrid.positive R (diagonal-1/2)
      (pWeights k l (tilted c z)) (qWeights k l (tilted c z)) 3 i (frameCap-z)+
        V R (pWeights k l (tilted c z) j) (qWeights k l (tilted c z) j) frameCap)

/-- For every permitted positive coefficient choice, one intrinsic scalar
alternative is nonpositive on an actual feasible original cycle. -/
theorem original_concentration {q k l c : ℝ} {C : SignedCycle} {hg : Fin 4}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T)
    (hhg : hg=0 ∨ hg=2)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G 2)
    (hAB : C.Feasible A 0) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0)
    (hk : k∈Icc (1/2) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*tilted c (delta C.theta T) ∧ tilted c (delta C.theta T)≤2*l) :
    ∃ i j : Fin 4, baseline k l c (delta C.theta T)+
      endpoint k l c (delta C.theta T) i j≤0 := by
  have hb := original_budgets hg k l c hvar hz
  have hw := coefficient_domain hk hl hcoef hb.1 hratio
  obtain ⟨i,j,hendpoint⟩ := Hybrid.concentrate R (diagonal-1/2)
    (pWeights k l (tilted c (delta C.theta T)))
    (qWeights k l (tilted c (delta C.theta T)))
    (fun i => (blocks C hg k l c i).P) (fun i => (blocks C hg k l c i).N) (3:Fin 4)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hw i).1) (fun i => (hw i).2.1) (fun i => (hw i).2.2)
    (fun i => (blocks C hg k l c i).P_nonneg)
    (fun i => (blocks C hg k l c i).N_nonneg) hb.1 hb.2.1 hb.2.2
  have hactual := original_stress_lower hs hc hq hHy hGy hBy hDy hvar hz hhg
    hk hl hcoef hratio
  have hnonpos := actual_stress_nonpos (show 0≤k by linarith [hk.1])
    (show 0≤l by linarith [hk.1,hl.1]) (show 0<c by linarith [hk.1,hcoef.1])
    hb.1 hHG hGA hAB hBT hTD hDE hEH
  refine ⟨i,j,?_⟩
  change endpoint k l c (delta C.theta T) i j≤_ at hendpoint
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
