module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDData

/-!
# The positive-TD stress on the original seven actual points

Uncompiled source.  The only intermediate-circle estimate is the support
of the actual T point in direction `(1,-eta)`.  H, G, B, and D keep their
original coordinates and signed tangents.  The decomposition below is an
identity of the original weighted physical separators.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

def actualStress (hg : Fin 4) (k l c : ℝ) (C : SignedCycle) : ℝ :=
  demand C (weights k l c (delta C.theta T))-
    ∑ i,work (force C (tdOwners hg) (weights k l c (delta C.theta T)) i) (C.point i)

def actualBlocks (C : SignedCycle) (hg : Fin 4) (k l c : ℝ) : Fin 4 → ℝ :=
  ![actualPairIncrement (blocks C hg k l c 0) (C.point H),
    actualPairIncrement (blocks C hg k l c 1) (C.point G).reflect,
    actualPairIncrement (blocks C hg k l c 2) (C.point B).reflect,
    actualDIncrement c (delta C.theta D) (C.point D).reflect]

def tReserve (C : SignedCycle) (c : ℝ) : ℝ :=
  c*Real.sin (delta C.theta T)*(sigma-((C.point T).a-eta*(C.point T).y))

theorem actual_T_support {q : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap) :
    P.a-eta*P.y≤sigma := by
  have hc' : P.Contained (R^2) := by rw [radius_sq]; exact hc.trans hq
  have h := work_le_circleSupport (Real.sqrt_nonneg qCap) hs hc' (1,-eta)
  norm_num [work,circleSupport,sigma,fullSupport,eta] at h ⊢
  exact h

theorem tReserve_nonneg {q c : ℝ} {C : SignedCycle}
    (hs : (C.point T).Sorted) (hc : (C.point T).Contained q) (hq : q≤qCap)
    (hc0 : 0≤c) (hz : delta C.theta T∈Icc 0 frameCap) : 0≤tReserve C c := by
  exact mul_nonneg (mul_nonneg hc0 (transport_trig hz).2.2.1)
    (sub_nonneg.mpr (actual_T_support hs hc hq))

theorem actual_stress_decomposition (C : SignedCycle) {hg : Fin 4}
    (hhg : hg=0 ∨ hg=2) (k l c : ℝ) :
    actualStress hg k l c C=baseline k l c (delta C.theta T)+
      (∑ i,actualBlocks C hg k l c i)+tReserve C c := by
  rcases hhg with rfl | rfl <;>
    simp [actualStress,demand,force,source,target,work,add,scale,
      previous,tdOwners,weights,blocks,actualBlocks,actualPairIncrement,
      actualDIncrement,pairF,pairG,tReserve,baseline,tilted,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,
      SignedPoint.reflect,edgeWidth,pairWidth] <;> ring

theorem actual_stress_nonpos {C : SignedCycle} {hg : Fin 4} {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c)
    (hz : delta C.theta T∈Icc 0 frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G 2)
    (hAB : C.Feasible A 0) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    actualStress hg k l c C≤0 := by
  have hf (i : Vertex) : C.Feasible i (tdOwners hg i) := by
    fin_cases i
    · simpa [tdOwners,H] using hHG
    · simpa [tdOwners,G] using hGA
    · simpa [tdOwners,A] using hAB
    · simpa [tdOwners,B] using hBT
    · simpa [tdOwners,T] using hTD
    · simpa [tdOwners,D] using hDE
    · simpa [tdOwners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonneg hk hl hc hz) hf)

theorem actual_block_family_lower {q k l c : ℝ} {C : SignedCycle} {hg : Fin 4}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T)
    (hk : k∈Icc (1/2) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*tilted c (delta C.theta T) ∧ tilted c (delta C.theta T)≤2*l)
    (i : Fin 4) :
    Hybrid.block R (diagonal-1/2)
      (pWeights k l (tilted c (delta C.theta T)))
      (qWeights k l (tilted c (delta C.theta T))) 3 i
      (blocks C hg k l c i).P (blocks C hg k l c i).N≤actualBlocks C hg k l c i := by
  have hz' := (original_budgets hg k l c hvar hz).1
  have hcoeff := coefficient_domain hk hl hcoef hz' hratio
  have hordinary (i : Fin 4) {P : SignedPoint}
      (hy : 0≤P.y) (hcP : P.Contained q) :
      mixedBlock R (pWeights k l (tilted c (delta C.theta T)) i)
        (qWeights k l (tilted c (delta C.theta T)) i)
        (blocks C hg k l c i).P (blocks C hg k l c i).N≤
          actualPairIncrement (blocks C hg k l c i) P := by
    have hco := block_coefficients (C:=C) (hg:=hg) (c:=c)
      (show k≤1 by linarith [hk.2]) hl.1 i
    have hp : 0≤(blocks C hg k l c i).p := by rw [hco.1]; exact (hcoeff i).1.le
    have hb := block_budgets hg k l c hvar hz i
    have h := actual_block_minorant hy hcP hq hp hb.1 hb.2
    rw [hco.1,hco.2] at h
    exact h
  fin_cases i
  · simpa [Hybrid.block,actualBlocks] using hordinary 0 hHy (hc H)
  · simpa [Hybrid.block,actualBlocks] using hordinary 1
      (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G)
  · simpa [Hybrid.block,actualBlocks] using hordinary 2
      (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B)
  · have hn : negativeVariation C.theta≤frameCap := by
      rw [← variations_equal]
      exact hvar
    have h := actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hs D)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hq hk hcoef (original_error_bound hvar hn D)
    simpa [Hybrid.block,actualBlocks,blocks,Block.P,Block.N,pWeights,qWeights] using h

/-- The original feasible stress dominates the full analytic four-block
expression at the actual removed TD error. -/
theorem original_stress_lower {q k l c : ℝ} {C : SignedCycle} {hg : Fin 4}
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T)
    (hhg : hg=0 ∨ hg=2)
    (hk : k∈Icc (1/2) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*tilted c (delta C.theta T) ∧ tilted c (delta C.theta T)≤2*l) :
    baseline k l c (delta C.theta T)+
      (∑ i,Hybrid.block R (diagonal-1/2)
        (pWeights k l (tilted c (delta C.theta T)))
        (qWeights k l (tilted c (delta C.theta T))) 3 i
        (blocks C hg k l c i).P (blocks C hg k l c i).N)≤actualStress hg k l c C := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => actual_block_family_lower hs hc hq hHy hGy hBy hDy hvar hz
      hk hl hcoef hratio i)
  have hT := tReserve_nonneg (hs T) (hc T) hq
    (show 0≤c by linarith [hk.1,hcoef.1]) (original_budgets hg k l c hvar hz).1
  rw [actual_stress_decomposition C hhg k l c]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
