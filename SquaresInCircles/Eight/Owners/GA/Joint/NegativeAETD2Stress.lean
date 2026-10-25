module

public import SquaresInCircles.Eight.Owners.GA.DMinorant
public import SquaresInCircles.Eight.Owners.GA.HybridConcentration
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2SourceData

/-!
# Eight squares: the original two-primary stress with positive TD2

Both secant cancellations take place in the original seven
physical inequalities. The four coefficient pairs still contain the
actual unremoved errors, and their signed budgets are those of
`Source.budgets`. The zero D block in the DE3 case contributes only its
actual sorted support reserve.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open Certificate (Row)

def exactBaseline (atG atH : Bool) (k c r s z : ℝ) : ℝ :=
  k+lambdaG atG r+lambdaB atG r+tilted c z+c*edgeWidth z+
    lambdaD atH s+lambdaH atH s-c*sigma*Real.sin z-
    fullSupport (lambdaH atH s) k-fullSupport (lambdaG atG r) k-
    fullSupport (tilted c z) (lambdaB atG r)-clippedSupport (lambdaD atH s) c+
    sec r*(edgeWidth r-1)+(7/12)*Real.tan r+
    sec s*(edgeWidth s-1)+(7/12)*Real.tan s

def actualStress (C : SignedCycle) (hg : Fin 4) (atG atH : Bool)
    (k c r s : ℝ) : ℝ :=
  demand C (weights atG atH k c r s (delta C.theta T))-
    ∑i,work (force C (owners hg atG atH)
      (weights atG atH k c r s (delta C.theta T)) i) (C.point i)

def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG atH : Bool)
    (k c r s : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg atG atH k c r s 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg atG atH k c r s 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg atG atH k c r s 2) (C.point B).reflect,
    if atH then PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect
    else clippedSupport (sec s) c-(sec s*(C.point D).a-c*(C.point D).y)]

def tReserve (C : SignedCycle) (c : ℝ) : ℝ :=
  c*Real.sin (delta C.theta T)*(sigma-((C.point T).a-eta*(C.point T).y))

theorem actual_T_support {q : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap) :
    P.a-eta*P.y≤ sigma := by
  have hC : P.Contained (R^2) := by rw [radius_sq]; exact hc.trans hq
  have hh := work_le_circleSupport (Real.sqrt_nonneg qCap) hs hC (1,-eta)
  norm_num [work,circleSupport,sigma,fullSupport,eta] at hh ⊢
  exact hh

theorem tReserve_nonnegative {q c : ℝ} {C : SignedCycle}
    (hs : (C.point T).Sorted) (hc : (C.point T).Contained q) (hq : q≤qCap)
    (hc0 : 0≤c) (hz : delta C.theta T∈Icc 0 frameCap) : 0≤tReserve C c := by
  exact mul_nonneg (mul_nonneg hc0 (transport_trig hz).2.2.1)
    (sub_nonneg.mpr (actual_T_support hs hc hq))

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG atH : Bool)
    (k c : ℝ) {r s : ℝ} (hhg : hg=0 ∨ hg=2)
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (ha : aError C atG= -r) (he : eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12) :
    actualStress C hg atG atH k c r s=
      exactBaseline atG atH k c r s (delta C.theta T)+
        (∑i,actualBlocks C hg atG atH k c r s i)+tReserve C c := by
  have hcr : Real.cos r≠0 := (show 0<Real.cos r by
    linarith [(transport_trig hr).1]).ne'
  have hcs : Real.cos s≠0 := (show 0<Real.cos s by
    linarith [(transport_trig hs).1]).ne'
  simp only [A,E] at hA hE
  cases atG <;> cases atH <;> rcases hhg with rfl|rfl <;>
    simp only [aError,eError,Bool.false_eq_true,↓reduceIte,G,A,D,E] at ha he <;>
    simp only [actualStress,demand,force,source,target,work,add,scale,previous,
      owners,weights,blocks,actualBlocks,PositiveTD.actualPairIncrement,
      PositiveTD.actualDIncrement,pairF,pairG,tReserve,exactBaseline,
      tilted,lambdaG,lambdaB,lambdaH,lambdaD,sec,SecantNormCurvature.secant,
      Real.tan_eq_sin_div_cos,Fin.sum_univ_succ,word,H,G,A,B,T,D,E,
      SignedPoint.reflect,ha,he,hA,hE,Bool.false_eq_true,Fin.default_eq_zero,Fin.isValue,
      Fin.reduceEq,Fin.reduceSucc,Fin.succ_one_eq_two,Fin.succ_zero_eq_one,Finset.card_singleton,
      Finset.sum_const,Finset.sum_singleton,Finset.univ_unique,
      Matrix.cons_val,Matrix.cons_val_fin_one,Matrix.cons_val_one,Matrix.cons_val_succ,
      Matrix.cons_val_zero,Nat.reduceAdd,Nat.succ_eq_add_one,Real.cos_neg,Real.cos_zero,
      Real.sin_neg,Real.sin_zero,add_zero,edgeWidth_neg,edgeWidth_zero,mul_neg,mul_one,mul_zero,
      neg_add_rev,neg_mul,neg_neg,one_div,one_mul,one_ne_zero,one_smul,smul_add,sub_self,zero_add,
      zero_sub,↓reduceIte] <;>
    field_simp [hcr,hcs] <;> ring

theorem weights_nonnegative (atG atH : Bool) {k c r s z : ℝ}
    (hk : 0≤k) (hc : 0≤c) (hr : r∈Icc 0 frameCap)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) (i : Vertex) :
    0≤weights atG atH k c r s z i := by
  have hcr : 0<Real.cos r := by linarith [(transport_trig hr).1]
  have hcs : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hr0 : 0≤ sec r := div_nonneg (by norm_num) hcr.le
  have hs0 : 0≤ sec s := div_nonneg (by norm_num) hcs.le
  have hm : 0≤tilted c z := mul_nonneg hc
    (show 0≤Explicit.tiltFactor z by linarith [(Explicit.tiltFactor_bounds hz).1])
  cases atG <;> cases atH <;> fin_cases i <;>
    simp [weights,lambdaG,lambdaB,lambdaH,lambdaD] <;> positivity

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (atG atH : Bool)
    {k c r s : ℝ} (hk : 0≤k) (hc : 0≤c)
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hz : delta C.theta T∈Icc 0 frameCap)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if atH then 2 else 3))
    (hEH : C.Feasible E (if atH then 1 else 0)) :
    actualStress C hg atG atH k c r s≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg atG atH i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonnegative atG atH hk hc hr hs hz) hf)

theorem block_family_lower {q r s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Row) (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hz : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (i : Fin 4) :
    PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
      (pWeights atG atH (Explicit.k f (delta C.theta T)) (Explicit.m f (delta C.theta T)) r s)
      (qWeights atG atH (Explicit.k f (delta C.theta T)) (Explicit.m f (delta C.theta T)) r s)
      3 i (blocks C hg atG atH (Explicit.k f (delta C.theta T)) (Explicit.c f (delta C.theta T)) r s i).P
        (blocks C hg atG atH (Explicit.k f (delta C.theta T)) (Explicit.c f (delta C.theta T)) r s i).N≤
      actualBlocks C hg atG atH (Explicit.k f (delta C.theta T)) (Explicit.c f (delta C.theta T)) r s i := by
  let k := Explicit.k f (delta C.theta T)
  let c := Explicit.c f (delta C.theta T)
  have hc := Explicit.ranges f hz
  have hl := lambda_bounds atG atH hr hs hH
  have hz0 := Explicit.frame_domain f hz
  have hcoeff := pair_domain f atG atH hz hr hs hH
  have hd (j : Fin 4) := block_coefficients (C:=C) (hg:=hg) (c:=c)
    atG atH (show k≤1 by dsimp [k]; linarith [hc.1.2])
    (show k≤lambdaG atG r by dsimp [k]; linarith [hc.1.2,hl.1.1])
    (show k≤lambdaH atH s by dsimp [k]; linarith [hc.1.2,hl.2.2.1.1]) j
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (pWeights atG atH k (tilted c (delta C.theta T)) r s j)
        (qWeights atG atH k (tilted c (delta C.theta T)) r s j)
        (blocks C hg atG atH k c r s j).P (blocks C hg atG atH k c r s j).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG atH k c r s j) P := by
    have hp : 0≤(blocks C hg atG atH k c r s j).p := by
      rw [(hd j).1]; exact (hcoeff j).1.le
    have hb := block_budgets hg atG atH k c hr.1 hs.1 ha he hvar hz0.1 j
    have hh := PositiveTD.actual_block_minorant hy hP hq hp hb.1 hb.2
    rw [(hd j).1,(hd j).2] at hh
    exact hh
  fin_cases i
  · simpa [PositiveTD.Hybrid.block,actualBlocks,Explicit.m,k,c] using
      hordinary 0 hHy (hcontained H)
  · simpa [PositiveTD.Hybrid.block,actualBlocks,Explicit.m,k,c] using
      hordinary 1 (P:=(C.point G).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hcontained G)
  · simpa [PositiveTD.Hybrid.block,actualBlocks,Explicit.m,k,c] using
      hordinary 2 (P:=(C.point B).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hcontained B)
  · cases atH
    · have hh := actual_clipped_support (P:=(C.point D).reflect)
        (by simpa using hsorted D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
        (by simpa using hcontained D) hq
        (show 0≤ sec s+c by
          have hh := SecantNormCurvature.secant_ge_one
            (show 0<Real.cos s by linarith [(transport_trig hs).1])
          dsimp [c]; linarith [hc.1.1,hc.2.1])
      simpa [PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,pWeights,qWeights,
        V,pairNorm,SignedPoint.reflect,positivePart,negativePart,Explicit.m,k,c] using
        sub_nonneg.mpr hh
    · have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
      have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
        (by simpa using hsorted D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
        (by simpa using hcontained D) hq
        (show k∈Icc (1/2:ℝ) (17/20) by dsimp [k]; constructor <;> linarith [hc.1.1,hc.1.2])
        (show c∈Icc k 2 by exact ⟨hc.2.1,by dsimp [c]; linarith [hc.2.2.1]⟩)
        (original_error_bound hvar hn D)
      simpa [PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,pWeights,qWeights,
        Explicit.m,k,c] using hh

theorem original_stress_lower {q r s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Row) (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12)
    (hhg : hg=0 ∨ hg=2)
    (hz : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    exactBaseline atG atH (Explicit.k f (delta C.theta T)) (Explicit.c f (delta C.theta T))
      r s (delta C.theta T)+
      (∑i,PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
        (pWeights atG atH (Explicit.k f (delta C.theta T)) (Explicit.m f (delta C.theta T)) r s)
        (qWeights atG atH (Explicit.k f (delta C.theta T)) (Explicit.m f (delta C.theta T)) r s)
        3 i (blocks C hg atG atH (Explicit.k f (delta C.theta T)) (Explicit.c f (delta C.theta T)) r s i).P
          (blocks C hg atG atH (Explicit.k f (delta C.theta T)) (Explicit.c f (delta C.theta T)) r s i).N)≤
      actualStress C hg atG atH (Explicit.k f (delta C.theta T)) (Explicit.c f (delta C.theta T)) r s := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    block_family_lower (hg:=hg) f atG atH hsorted hcontained hq hHy hGy hBy hDy
      hvar hr hs hH ha he hz i)
  have hc := Explicit.ranges f hz
  have hT := tReserve_nonnegative (hsorted T) (hcontained T) hq
    (show 0≤Explicit.c f (delta C.theta T) by linarith [hc.1.1,hc.2.1])
    (Explicit.frame_domain f hz)
  rw [decomposition C atG atH _ _ hhg
    (show r∈Icc 0 frameCap by exact ⟨hr.1,by norm_num [frameCap] at *; linarith [hr.2]⟩)
    hs ha he hA hE]
  linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Source
