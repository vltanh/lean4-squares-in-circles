module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2OriginalData

/-!
# The original negative-flat-A / TD2 weighted stress

Uncompiled transcription of equations (5)--(9) of the angle companion.
The negative A rotation is collected with its secant weight as an exact
identity. No replacement separator or modified geometric cycle is used.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

def actualStress (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c s : ℝ) : ℝ :=
  demand C (weights atG k l c s (delta C.theta T))-
    ∑ i,work (force C (owners hg atG) (weights atG k l c s (delta C.theta T)) i) (C.point i)
def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c s : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg atG k l c s 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg atG k l c s 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg atG k l c s 2) (C.point B).reflect,
    PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect]

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG : Bool) (k l c : ℝ) {s : ℝ}
    (hhg : hg=0 ∨ hg=2) (hs : s∈Icc 0 frameCap)
    (ha : aError C atG=-s) (hflat : (C.point A).a=7/12) :
    actualStress C hg atG k l c s=
      baseline atG k l c s (delta C.theta T)+
        (∑ i,actualBlocks C hg atG k l c s i)+PositiveTD.tReserve C c := by
  have hcos : Real.cos s≠0 := (show 0<Real.cos s by
    linarith [(transport_trig hs).1]).ne'
  cases atG <;> rcases hhg with rfl | rfl <;>
    simp only [aError,↓reduceIte] at ha <;>
    simp [actualStress,demand,force,source,target,work,add,scale,previous,
      owners,weights,blocks,actualBlocks,PositiveTD.actualPairIncrement,
      PositiveTD.actualDIncrement,pairF,pairG,PositiveTD.tReserve,baseline,
      PositiveTD.tilted,lambdaG,lambdaB,secant,Real.tan_eq_sin_div_cos,
      Fin.sum_univ_succ,word,next,H,G,A,B,T,D,E,SignedPoint.reflect,ha,hflat] <;>
    field_simp [hcos] <;> ring

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (atG : Bool) {k l c s : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c)
    (hs : s∈Icc 0 frameCap) (hz : delta C.theta T∈Icc 0 frameCap)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    actualStress C hg atG k l c s≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg atG i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonnegative atG hk hl hc hs hz) hf)

theorem block_family_lower {q k l c s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hsorted : ∀ i,(C.point i).Sorted) (hcontained : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤s)
    (ha : aError C atG=-s) (hz : 0≤delta C.theta T)
    (hk : k∈Icc (1/2:ℝ) (17/20:ℝ))
    (hG : lambdaG atG l s∈Icc k (2*k)) (hB : 0<lambdaB atG l s)
    (hcoef : c∈Icc k 2)
    (hratio : lambdaB atG l s≤2*PositiveTD.tilted c (delta C.theta T) ∧
      PositiveTD.tilted c (delta C.theta T)≤2*lambdaB atG l s) (i : Fin 4) :
    PositiveTD.Hybrid.block R (diagonal-1/2)
      (pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
      (qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s) 3 i
      (blocks C hg atG k l c s i).P (blocks C hg atG k l c s i).N≤
        actualBlocks C hg atG k l c s i := by
  have hz' := (original_budgets hg atG k l c hs ha hvar hz).1
  have hc0 : 0<c := by linarith [hk.1,hcoef.1]
  have hm := PositiveTD.tilted_pos hc0 hz'
  have hcoeff := coefficient_domain hk hG hB hm hratio
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s j)
        (qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s j)
        (blocks C hg atG k l c s j).P (blocks C hg atG k l c s j).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG k l c s j) P := by
    have hd := block_coefficients (C:=C) (hg:=hg) (atG:=atG) (c:=c)
      (show k≤1 by linarith [hk.2]) hG.1 j
    have hp : 0≤(blocks C hg atG k l c s j).p := by rw [hd.1]; exact (hcoeff j).1.le
    have hb := block_budgets hg atG k l c hs ha hvar hz j
    have hh := PositiveTD.actual_block_minorant hy hP hq hp hb.1 hb.2
    rw [hd.1,hd.2] at hh
    exact hh
  fin_cases i
  · simpa [PositiveTD.Hybrid.block,actualBlocks] using hordinary 0 hHy (hcontained H)
  · simpa [PositiveTD.Hybrid.block,actualBlocks] using hordinary 1
      (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hcontained G)
  · simpa [PositiveTD.Hybrid.block,actualBlocks] using hordinary 2
      (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hcontained B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
    have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hsorted D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hcontained D) hq hk hcoef (original_error_bound hvar hn D)
    simpa [PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,pWeights,qWeights] using hh

theorem original_stress_lower {q k l c s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hsorted : ∀ i,(C.point i).Sorted) (hcontained : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (hs : s∈Icc 0 frameCap)
    (ha : aError C atG=-s) (hflat : (C.point A).a=7/12)
    (hz : 0≤delta C.theta T) (hhg : hg=0 ∨ hg=2)
    (hk : k∈Icc (1/2:ℝ) (17/20:ℝ))
    (hG : lambdaG atG l s∈Icc k (2*k)) (hB : 0<lambdaB atG l s)
    (hcoef : c∈Icc k 2)
    (hratio : lambdaB atG l s≤2*PositiveTD.tilted c (delta C.theta T) ∧
      PositiveTD.tilted c (delta C.theta T)≤2*lambdaB atG l s) :
    baseline atG k l c s (delta C.theta T)+
      (∑ i,PositiveTD.Hybrid.block R (diagonal-1/2)
        (pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
        (qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s) 3 i
        (blocks C hg atG k l c s i).P (blocks C hg atG k l c s i).N)≤
          actualStress C hg atG k l c s := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    block_family_lower atG hsorted hcontained hq hHy hGy hBy hDy hvar hs.1 ha hz
      hk hG hB hcoef hratio i)
  have hT := PositiveTD.tReserve_nonneg (hsorted T) (hcontained T) hq
    (show 0≤c by linarith [hk.1,hcoef.1])
    (original_budgets hg atG k l c hs.1 ha hvar hz).1
  rw [decomposition C atG k l c hhg hs ha hflat]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Source
