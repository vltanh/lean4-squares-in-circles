module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3Stress
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3BlockBounds
public import SquaresInCircles.Eight.Owners.GA.Secant.DSingleAngle
public import SquaresInCircles.Eight.Owners.GA.Sorted.DSevenFifthsActual

/-!
# Eight squares: the joint-negative BT3 block minorant at the original points

The negative DE3 case uses the exact one-angle secant-D comparison.
The negative EH1 case uses the ordinary D pair below c=1 and the wider
sorted two-angle envelope above it. Both retain the original TD0 error.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open Certificate (Row)

theorem family_rotation (f : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    Explicit.c f z=Explicit.m f z*tilt (Explicit.eta f z) z := by
  have hf : Explicit.f f z≠0 := (show 0<Explicit.f f z by
    linarith [(Explicit.ranges f hz).f_domain.1]).ne'
  simpa [Explicit.m,Explicit.f] using (div_mul_cancel₀ (Explicit.c f z) hf).symm

theorem ordinary_D_identity {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (k m r s : ℝ) {c : ℝ} (hc : c<1) :
    actualD C true c s=
      PositiveTD.actualPairIncrement (blocks C hg atG true k m c r s 3) (C.point D).reflect := by
  simp [actualD,blocks,PositiveTD.actualPairIncrement,lambdaD,
    JointNegativeAETD2.Source.lambdaD,clippedSupport,not_le.mpr hc,SignedPoint.reflect] <;> ring

theorem single_D_identity {C : SignedCycle} {c s : ℝ}
    (hs : s∈Icc 0 frameCap) (hc : c∈Icc (7/10:ℝ) (7/5)) :
    actualD C false c s=SecantD.actualIncrement (sec s) c (delta C.theta T) (C.point D) := by
  have hbase := SecantD.baseline_clipped (JointNegativeAETD2.CommonGain.full_secant_domain hs) hc
  simp [actualD,SecantD.actualIncrement,lambdaD,JointNegativeAETD2.Source.lambdaD,
    pairF,pairG,hbase,edgeWidth,pairWidth]

theorem diagonal_D_identity {C : SignedCycle} {c s : ℝ} (hc : 1≤c) :
    actualD C true c s=
      c*(edgeWidth (delta C.theta T)-1)+edgeWidth (delta C.theta D)-1+(1+c)*GlobalGA.Secondary.diagonal-
        (PositiveBT3.forceA c (delta C.theta T) (delta C.theta D)*(C.point D).a+
          PositiveBT3.forceB c (delta C.theta T) (delta C.theta D)*(-(C.point D).y)) := by
  simp [actualD,lambdaD,JointNegativeAETD2.Source.lambdaD,
    pairF,pairG,PositiveBT3.forceA,PositiveBT3.forceB,clippedSupport,hc,diagonalSupport] <;> ring

theorem block_family_lower {q r s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Row) (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hz : delta C.theta B∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (i : Fin 5) :
    PositiveTD.Hybrid.block R (Penalty.cost (Explicit.c f (delta C.theta B)) (r+s))
      (pWeights atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s)
      (qWeights atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s)
      (distinguished atH (Explicit.c f (delta C.theta B))) i
      (blocks C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s i).P
      (blocks C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s i).N≤
      actualBlocks C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s i := by
  let k := Explicit.k f (delta C.theta B)
  let m := Explicit.m f (delta C.theta B)
  let c := Explicit.c f (delta C.theta B)
  have hc := Explicit.ranges f hz
  have hl := JointNegativeAETD2.Source.lambda_bounds atG atH hr hs hH
  have hz0 := Explicit.frame_domain f hz
  have hb := budgets hg atG atH k m c hr.1 hs.1 ha he hvar hz0.1
  have hcoeff := pair_domain f atG atH hz hr hs hH
  have hordinary (j : Fin 5) (hj : j≠distinguished atH c) {P : SignedPoint}
      (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (pWeights atG atH k m c r s j) (qWeights atG atH k m c r s j)
        (blocks C hg atG atH k m c r s j).P (blocks C hg atG atH k m c r s j).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG atH k m c r s j) P := by
    have hd := ordinary_coefficients (C:=C) (hg:=hg) (m:=m) (c:=c)
      atG atH (show k≤1 by dsimp [k]; linarith [hc.k_domain.2])
      (show k≤lambdaG atG r by dsimp [k]; linarith [hc.k_domain.2,hl.1.1])
      (show k≤lambdaH atH s by dsimp [k]; linarith [hc.k_domain.2,hl.2.2.1.1]) j hj
    have hp : 0≤(blocks C hg atG atH k m c r s j).p := by
      rw [hd.1]; exact (hcoeff j).1.le
    have hbudget := block_budgets hg atG atH k m c hr.1 hs.1 ha he hvar hz0.1 j
    have hh := PositiveTD.actual_block_minorant hy hP hq hp hbudget.1 hbudget.2
    rw [hd.1,hd.2] at hh
    exact hh
  have hn0 : (0:Fin 5)≠distinguished atH c := by unfold distinguished; split_ifs <;> decide
  have hn1 : (1:Fin 5)≠distinguished atH c := by unfold distinguished; split_ifs <;> decide
  have hn2 : (2:Fin 5)≠distinguished atH c := by unfold distinguished; split_ifs <;> decide
  fin_cases i <;> try simp only [Fin.reduceFinMk,Fin.zero_eta,Fin.mk_one,Fin.isValue]
  · simpa [PositiveTD.Hybrid.block,actualBlocks,hn0,k,m,c] using hordinary 0 hn0 hHy (hcontained H)
  · simpa [PositiveTD.Hybrid.block,actualBlocks,hn1,k,m,c] using hordinary 1 hn1
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hcontained G)
  · simpa [PositiveTD.Hybrid.block,actualBlocks,hn2,k,m,c] using hordinary 2 hn2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hcontained B)
  · by_cases ho : ordinaryD atH c
    · have htrue : atH=true := ho.1
      subst htrue
      have hn3 : (3:Fin 5)≠distinguished true c := by simp [distinguished,ho]
      have hh := hordinary 3 hn3 (P:=(C.point D).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy) (by simpa using hcontained D)
      rw [←ordinary_D_identity (C:=C) (hg:=hg) atG k m r s ho.2] at hh
      simpa [PositiveTD.Hybrid.block,actualBlocks,hn3,k,m,c] using hh
    · have hd : distinguished atH c=3 := by simp [distinguished,ho]
      have hk' : k∈Icc (1/2:ℝ) (17/20) := by
        dsimp [k]; constructor <;> linarith [hc.k_domain.1,hc.k_domain.2]
      cases atH
      · have hneg : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
        have hh := SecantD.actual_minorant (hsorted D) hDy (hcontained D) hq
          (JointNegativeAETD2.CommonGain.full_secant_domain hs) hk' hc.c_domain
          (hc.k_le_m.trans hc.m_le_c) (original_error_bound hvar hneg T)
        rw [←single_D_identity (C:=C) hs hc.c_domain] at hh
        have hsec := Penalty.secant_monotone hs hb.total_domain (by linarith [hr.1])
        have hmax := max_le_max hsec (le_rfl : c≤c)
        have hcost := (mul_le_mul_of_nonneg_left hmax (show (0:ℝ)≤109/200 by norm_num)).trans
          (BlockBounds.cost_max_coefficient (c:=c) hb.total_domain)
        have hcharge := mul_le_mul_of_nonneg_right hcost (positivePart_nonneg (delta C.theta T))
        simp only [PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,
          pWeights,qWeights,Matrix.cons_val,Fin.isValue,
          Bool.false_eq_true,↓reduceIte,positivePart_zero,negativePart_zero,add_zero]
        dsimp [SecantD.slope] at hh
        change -Penalty.cost c (r+s)*positivePart (delta C.theta T)+
          V R k 1 (negativePart (delta C.theta T))≤actualD C false c s
        linarith
      · have h1c : 1≤c := by
          by_contra hn
          exact ho ⟨rfl,lt_of_not_ge hn⟩
        have hsmall := hc.diagonal_cut h1c
        have hD := block_budgets hg atG true k m c hr.1 hs.1 ha he hvar hz0.1 (3:Fin 5)
        have hdom : PositiveBT3.SignedDomain (delta C.theta T) (delta C.theta D) := by
          simpa [PositiveBT3.SignedDomain,PositiveBT3.positiveTotal,PositiveBT3.negativeTotal,
            blocks,Block.P,Block.N] using hD
        have hh := SortedDSevenFifths.actual_minorant_for (hsorted D) hDy (hcontained D) hq
          (show k∈Icc (1/2:ℝ) SortedDSevenFifths.K from ⟨hk'.1,hsmall.2⟩)
          (show c∈Icc 1 SortedDSevenFifths.Cmax from ⟨h1c,hc.c_domain.2⟩) hdom
        rw [←diagonal_D_identity (C:=C) (s:=s) h1c] at hh
        have hcost : (13/20:ℝ)≤Penalty.cost c (r+s) := by
          simp only [Penalty.cost,ite_eq_right (not_lt.mpr h1c)]
          exact le_max_left _ _
        have hcharge := mul_le_mul_of_nonneg_right hcost
          (add_nonneg (positivePart_nonneg (delta C.theta T)) (positivePart_nonneg (delta C.theta D)))
        have hd' : distinguished true (Explicit.c f (delta C.theta B))=3 := hd
        have ho' : ¬ordinaryD true (Explicit.c f (delta C.theta B)) := ho
        simp only [PositiveTD.Hybrid.block,hd',actualBlocks,blocks,Block.P,Block.N,
          pWeights,qWeights,Matrix.cons_val,Fin.isValue,↓reduceIte,ho']
        dsimp [SortedDSevenFifths.slope,PositiveBT3.positiveTotal,PositiveBT3.negativeTotal] at hh
        change -Penalty.cost c (r+s)*(positivePart (delta C.theta T)+positivePart (delta C.theta D))+
          V R k 1 (negativePart (delta C.theta T)+negativePart (delta C.theta D))≤actualD C true c s
        linarith
  · by_cases ho : ordinaryD atH c <;>
      simp [PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,
        pWeights,qWeights,distinguished,ho,c]

theorem original_stress_lower {q r s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Row) (atG atH : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12) (hhg : hg=0 ∨ hg=2)
    (hz : delta C.theta B∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    exactBaseline atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
      (Explicit.c f (delta C.theta B)) (Explicit.eta f (delta C.theta B)) r s (delta C.theta B)+
      (∑i,PositiveTD.Hybrid.block R (Penalty.cost (Explicit.c f (delta C.theta B)) (r+s))
        (pWeights atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
          (Explicit.c f (delta C.theta B)) r s)
        (qWeights atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
          (Explicit.c f (delta C.theta B)) r s)
        (distinguished atH (Explicit.c f (delta C.theta B))) i
        (blocks C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
          (Explicit.c f (delta C.theta B)) r s i).P
        (blocks C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
          (Explicit.c f (delta C.theta B)) r s i).N)≤
      actualStress C hg atG atH (Explicit.k f (delta C.theta B)) (Explicit.m f (delta C.theta B))
        (Explicit.c f (delta C.theta B)) r s := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    block_family_lower (hg:=hg) f atG atH hsorted hcontained hq hHy hGy hBy hDy hvar hr hs hH
      ha he hz i)
  have hc := Explicit.ranges f hz
  have hT := tReserve_nonnegative (hsorted T) (hcontained T) hq
    (show 0≤Explicit.m f (delta C.theta B) by linarith [hc.k_domain.1,hc.k_le_m])
    hc.eta_domain.1 (Explicit.frame_domain f hz)
  rw [decomposition C atG atH _ _ _ hhg
    (show r∈Icc 0 frameCap by exact ⟨hr.1,by norm_num [frameCap] at *; linarith [hr.2]⟩)
    hs ha he hA hE (family_rotation f hz)]
  linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Source
