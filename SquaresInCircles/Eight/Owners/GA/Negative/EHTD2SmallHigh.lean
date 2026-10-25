module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Source
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Data
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Low
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.Flat.EExclusion
public import SquaresInCircles.Eight.Owners.GA.Paired.ENegativeSource
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Stress
public import SquaresInCircles.Eight.Owners.Negative.CoreEReduction

/-!
# Eight squares: complete small-EH high-total scalar exclusion

The two signed
budgets imply negative surplus. Every common positive/negative mass is
removed using the original pair ratios, including the distinguished D
singleton. The remaining negative block is concave in the actual EH
magnitude, with its two proved intrinsic endpoints at zero and .1.
-/

section
/-!
## The unchanged secondary-E reference cycle for negative A and BT3

The A secant multiplier and the rotating
TD0 multiplier have different arguments. Deleting the negative A
primary and the positive BT3 error leaves both exact signed budgets.
The arbitrary TD0 error remains in the two-angle D block.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

abbrev aError := NegativeAPositiveTD.Source.aError

def owners (hg : Fin 4) (atG : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,3,0,2,0]

def weights (atG : Bool) (k l m s z : ℝ) : Vertex→ℝ :=
  ![k,lambdaG atG l s,lambdaB atG l s,m,PositiveBT3.tilted m z,1,1]

def blocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l m s : ℝ) : Fin 4→Block :=
  ![⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨k,lambdaG atG l s,if hg=0 then delta C.theta H else 0,
      if atG then 0 else delta C.theta G⟩,
    ⟨lambdaB atG l s,m,if atG then delta C.theta A else 0,0⟩,
    ⟨PositiveBT3.tilted m (delta C.theta B),1,delta C.theta T,delta C.theta D⟩]

theorem weights_nonnegative (atG : Bool) {k l m s z : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0< m)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) (i : Vertex) :
    0≤weights atG k l m s z i := by
  have hp := NegativeAPositiveTD.Source.secant_nonnegative hl hs
  have hc := (PositiveTD.tilted_pos hm hz).le
  cases atG <;> fin_cases i <;>
    simp [weights,lambdaG,lambdaB,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,
      PositiveBT3.tilted] <;> positivity

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} {atG : Bool} {k l m s : ℝ}
    (f : Certificate.Family) (hk : k≤1) (hG : k≤lambdaG atG l s)
    (i : Fin 4) (hi : f=.high∨i≠3) :
    (blocks C hg atG k l m s i).p=pWeights f atG k l m
      (PositiveBT3.tilted m (delta C.theta B)) s i ∧
    (blocks C hg atG k l m s i).q=qWeights f atG k l m
      (PositiveBT3.tilted m (delta C.theta B)) s i := by
  cases f <;> fin_cases i <;>
    simp_all [blocks,Block.p,Block.q,pWeights,qWeights,
      min_comm,max_comm]

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l m s : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG k l m s i).u+f (blocks C hg atG k l m s i).v))=
      (∑j,f (delta C.theta j))-f (delta C.theta B)-f (aError C atG) := by
  cases atG <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,NegativeAPositiveTD.Source.aError,hhg,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem original_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l m : ℝ) {s : ℝ}
    (hs : 0≤ s) (ha : aError C atG= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta B) :
    delta C.theta B∈Icc 0 frameCap ∧
    (∑i,(blocks C hg atG k l m s i).P)=positiveVariation C.theta-delta C.theta B ∧
    (∑i,(blocks C hg atG k l m s i).N)=negativeVariation C.theta-s ∧
    (∑i,(blocks C hg atG k l m s i).P)≤frameCap-delta C.theta B ∧
    (∑i,(blocks C hg atG k l m s i).N)≤frameCap-s ∧
    (∑i,(blocks C hg atG k l m s i).N)-
      (∑i,(blocks C hg atG k l m s i).P)=delta C.theta B-s := by
  have hp := sum_parts C hg atG k l m s positivePart positivePart_zero
  have hn := sum_parts C hg atG k l m s negativePart negativePart_zero
  have hpz : positivePart (delta C.theta B)=delta C.theta B := max_eq_left hz
  have hnz : negativePart (delta C.theta B)=0 := max_eq_right (by linarith)
  have hpa : positivePart (aError C atG)=0 := by
    rw [ha]
    exact max_eq_right (by linarith)
  have hna : negativePart (aError C atG)=s := by
    rw [ha]
    simpa [negativePart] using max_eq_left hs
  have hp' : (∑i,(blocks C hg atG k l m s i).P)=
      positiveVariation C.theta-delta C.theta B := by
    simpa only [Block.P,hpz,hpa,positiveVariation,sub_zero] using hp
  have hn' : (∑i,(blocks C hg atG k l m s i).N)=negativeVariation C.theta-s := by
    simpa only [Block.N,hnz,hna,negativeVariation,sub_zero] using hn
  have hp0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg atG k l m s i).P_nonneg)
  have heq := variations_equal C.theta
  exact ⟨⟨hz,by linarith⟩,hp',hn',by linarith,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l m : ℝ) {s : ℝ}
    (hs : 0≤ s) (ha : aError C atG= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta B) (i : Fin 4) :
    (blocks C hg atG k l m s i).P≤frameCap ∧ (blocks C hg atG k l m s i).N≤frameCap := by
  have hb := original_budgets hg atG k l m hs ha hvar hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l m s j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l m s j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.2.2.2.1],by linarith [hb.2.2.2.2.1]⟩

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.Source
end
end
end

section
/-!
## Reference weighted stress on the original points

The reference stress is an algebraic sum on
the unchanged seven points. Its positivity requires no reference edge
to be feasible. The two-angle D term uses the diagonal support at low
z and the complete-circle support at high z, exactly as in the note.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

def actualStress (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l m s : ℝ) : ℝ :=
  demand C (weights atG k l m s (delta C.theta B))-
    ∑i,work (force C (owners hg atG) (weights atG k l m s (delta C.theta B)) i) (C.point i)

def actualD (C : SignedCycle) (m : ℝ) : ℝ :=
  let c := PositiveBT3.tilted m (delta C.theta B)
  let x := delta C.theta T
  let y := delta C.theta D
  c*(edgeWidth x-1)+edgeWidth y-1+clippedSupport 1 c-
    (PositiveBT3.forceA c x y*(C.point D).a+PositiveBT3.forceB c x y*(-(C.point D).y))

def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l m s : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg atG k l m s 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg atG k l m s 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg atG k l m s 2) (C.point B).reflect,
    actualD C m]

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG : Bool) (k l m : ℝ) {s : ℝ}
    (hhg : hg=0∨hg=2) (hs : s∈Icc 0 frameCap)
    (ha : aError C atG= -s) (hflat : (C.point A).a=7/12) :
    actualStress C hg atG k l m s=
      baseline atG k l m s (delta C.theta B)+
        (∑i,actualBlocks C hg atG k l m s i)+PositiveBT3.Source.tReserve C m := by
  have hcos : Real.cos s≠0 := (show 0<Real.cos s by
    linarith [(transport_trig hs).1]).ne'
  have hfs (a : ℝ) : fullSupport m a=fullSupport a m := by
    simp only [fullSupport]; ring_nf
  simp only [A] at hflat
  cases atG <;> rcases hhg with rfl|rfl <;>
    simp only [aError,NegativeAPositiveTD.Source.aError,Bool.false_eq_true,↓reduceIte,G,A] at ha <;>
    simp only [actualStress,demand,weights,lambdaG,NegativeAPositiveTD.lambdaG,Bool.false_eq_true,
      ↓reduceIte,lambdaB,NegativeAPositiveTD.lambdaB,NegativeAPositiveTD.secant,
      PositiveBT3.tilted,B,Fin.isValue,Fin.sum_univ_succ,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,ha,edgeWidth_neg,
      Fin.reduceSucc,one_mul,Finset.univ_unique,Fin.default_eq_zero,Matrix.cons_val_fin_one,
      Finset.sum_singleton,work,force,add,scale,source,word,Nat.succ_eq_add_one,Nat.reduceAdd,
      owners,previous,target,mul_zero,Matrix.cons_val,one_ne_zero,zero_add,mul_one,mul_neg,
      Real.cos_neg,Real.sin_neg,Matrix.cons_val_one,add_zero,hflat,neg_mul,neg_neg,zero_mul,
      add_neg_cancel,Finset.sum_const_zero,baseline,secant,Real.tan_eq_sin_div_cos,actualBlocks,
      PositiveTD.actualPairIncrement,blocks,E,H,G,T,D,edgeWidth_zero,sub_self,pairF,Real.sin_zero,
      pairG,Real.cos_zero,SignedPoint.reflect,zero_sub,neg_add_rev,hfs,actualD,PositiveBT3.forceA,
      PositiveBT3.forceB,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_singleton,smul_add,
      one_smul,smul_neg,PositiveBT3.Source.tReserve,Fin.reduceEq,A] <;>
    field_simp [hcos] <;> ring

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (atG : Bool) {k l m s : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0< m)
    (hs : s∈Icc 0 frameCap) (hz : delta C.theta B∈Icc 0 frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    actualStress C hg atG k l m s≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg atG i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonnegative atG hk hl hm hs hz) hf)

theorem family_blocks_lower {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Certificate.Family) (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : aError C atG= -s)
    (hz : delta C.theta B∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4) :
    Concentration.block f (Explicit.p f atG (delta C.theta B) s)
      (Explicit.q f atG (delta C.theta B) s) i
      (blocks C hg atG (Explicit.k f (delta C.theta B)) (Explicit.l f (delta C.theta B))
        (Explicit.m f (delta C.theta B)) s i).P
      (blocks C hg atG (Explicit.k f (delta C.theta B)) (Explicit.l f (delta C.theta B))
        (Explicit.m f (delta C.theta B)) s i).N≤
      actualBlocks C hg atG (Explicit.k f (delta C.theta B)) (Explicit.l f (delta C.theta B))
        (Explicit.m f (delta C.theta B)) s i := by
  let z := delta C.theta B
  let k := Explicit.k f z
  let l := Explicit.l f z
  let m := Explicit.m f z
  have hzf := Explicit.frame_domain f hz
  have hcoeff := Explicit.ordered_pair_domain f atG hz hs
  have hk : k≤1 := by dsimp [k,z]; linarith [(Explicit.basic_domain f hz).1.2]
  have hG : k≤lambdaG atG l s := (hcoeff 1).2.1
  have hordinary (j : Fin 4) (hj : f=.high∨j≠3)
      {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (Explicit.p f atG z s j) (Explicit.q f atG z s j)
        (blocks C hg atG k l m s j).P (blocks C hg atG k l m s j).N≤
        PositiveTD.actualPairIncrement (blocks C hg atG k l m s j) P := by
    have hd := block_coefficients (C:=C) (hg:=hg) (atG:=atG) (m:=m) (s:=s) f hk hG j hj
    change (blocks C hg atG k l m s j).p=Explicit.p f atG z s j ∧
      (blocks C hg atG k l m s j).q=Explicit.q f atG z s j at hd
    have hp : 0≤(blocks C hg atG k l m s j).p := by rw [hd.1]; exact (hcoeff j).1.le
    have hb := block_budgets hg atG k l m hs.1 ha hvar hzf.1 j
    have hh := PositiveTD.actual_block_minorant hy hP hq hp hb.1 hb.2
    rwa [hd.1,hd.2] at hh
  fin_cases i
  · have hh := hordinary 0 (Or.inr (by decide)) hHy (hcontained H)
    cases f <;> simpa [Concentration.block,PositiveTD.Hybrid.block,actualBlocks,z,k,l,m] using hh
  · have hh := hordinary 1 (Or.inr (by decide)) (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hcontained G)
    cases f <;> simpa [Concentration.block,PositiveTD.Hybrid.block,actualBlocks,z,k,l,m] using hh
  · have hh := hordinary 2 (Or.inr (by decide)) (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hcontained B)
    cases f <;> simpa [Concentration.block,PositiveTD.Hybrid.block,actualBlocks,z,k,l,m] using hh
  · cases f
    · have hb := block_budgets hg atG k l m hs.1 ha hvar hzf.1 3
      have hdom : PositiveBT3.SignedDomain (delta C.theta T) (delta C.theta D) := by
        simpa [blocks,Block.P,Block.N,PositiveBT3.SignedDomain,
          PositiveBT3.positiveTotal,PositiveBT3.negativeTotal] using hb
      have hc := Explicit.low_rotation (by
        have h := hz; norm_num [Certificate.left,Certificate.right,Certificate.split] at h; exact h)
      have hD := DEnvelope.actual_minorant (hsorted D) hDy (hcontained D) hq
        (show Explicit.c .low z∈Icc 1 DEnvelope.Cmax from ⟨hc.1.le,hc.2.le⟩) hdom
      have hN : (blocks C hg atG k l m s 3).N∈Icc 0 frameCap :=
        ⟨(blocks C hg atG k l m s 3).N_nonneg,hb.2⟩
      have hkRange := (Explicit.low_ranges (by
        have h := hz; norm_num [Certificate.left,Certificate.right,Certificate.split] at h; exact h)).1
      have hv := OrdinaryNegativeEnvelope.V_monotone_smaller (R:=R) (Real.sqrt_nonneg _) (q:=1)
        (by norm_num) hN
        (show k∈Icc (1/2:ℝ) 1 by dsimp [k,z]; constructor <;> linarith [hkRange.1,hkRange.2])
        (show (17/25:ℝ)∈Icc (1/2:ℝ) 1 by norm_num)
        (show k≤17/25 by dsimp [k,z]; linarith [hkRange.2])
      have hc1 : 1≤Explicit.c .low z := hc.1.le
      have hsupp : clippedSupport 1 (Explicit.c .low z)=(1+Explicit.c .low z)*Secondary.diagonal := by
        rw [clippedSupport,ite_eq_left hc1,diagonalSupport]
      change -DEnvelope.slope*(blocks C hg atG k l m s 3).P+
        V R DEnvelope.K 1 (blocks C hg atG k l m s 3).N≤_ at hD
      simp only [Concentration.block,PositiveTD.Hybrid.block,↓reduceIte]
      change -(67/100)*(blocks C hg atG k l m s 3).P+
        V R k 1 (blocks C hg atG k l m s 3).N≤actualD C m
      dsimp [actualD]
      change -(67/100)*(blocks C hg atG k l m s 3).P+
        V R k 1 (blocks C hg atG k l m s 3).N≤
        Explicit.c .low z*(edgeWidth (delta C.theta T)-1)+edgeWidth (delta C.theta D)-1+
          clippedSupport 1 (Explicit.c .low z)-_
      rw [hsupp]
      dsimp [DEnvelope.slope,DEnvelope.K] at hD
      simp only at hv
      have hcz : Explicit.c .low z=PositiveBT3.tilted m (delta C.theta B) := rfl
      rw [hcz] at hD ⊢
      linarith
    · have hc := Explicit.high_rotation (by
        have h := hz; norm_num [Certificate.left,Certificate.right,Certificate.split] at h; exact h)
      have hnot : ¬1≤Explicit.c .high z := not_le.mpr hc.2.2
      have hh := hordinary 3 (Or.inl rfl) (P:=(C.point D).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy) (by simpa using hcontained D)
      have heq : actualBlocks C hg atG k l m s 3=
          PositiveTD.actualPairIncrement (blocks C hg atG k l m s 3) (C.point D).reflect := by
        have hnot' : ¬1≤PositiveBT3.tilted m (delta C.theta B) := hnot
        simp only [actualBlocks,actualD,PositiveTD.actualPairIncrement,blocks,pairF,pairG,
          PositiveBT3.forceA,PositiveBT3.forceB,clippedSupport,SignedPoint.reflect,
          Matrix.cons_val,ite_eq_right hnot']
        ring
      have hb : Concentration.block .high (Explicit.p .high atG z s) (Explicit.q .high atG z s) 3
          (blocks C hg atG k l m s 3).P (blocks C hg atG k l m s 3).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG k l m s 3) (C.point D).reflect := by
        simpa only [Concentration.block,reduceCtorEq,↓reduceIte] using hh
      exact hb.trans_eq heq.symm

theorem family_stress_positive {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Certificate.Family) (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : aError C atG= -s)
    (hflat : (C.point A).a=7/12)
    (hz : delta C.theta B∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hhg : hg=0∨hg=2) :
    0<actualStress C hg atG (Explicit.k f (delta C.theta B))
      (Explicit.l f (delta C.theta B)) (Explicit.m f (delta C.theta B)) s := by
  let k := Explicit.k f (delta C.theta B)
  let l := Explicit.l f (delta C.theta B)
  let m := Explicit.m f (delta C.theta B)
  have hzf := Explicit.frame_domain f hz
  have hb := original_budgets hg atG k l m hs.1 ha hvar hzf.1
  have hp := reference_scalar_positive f atG hz hs
    (fun i => (blocks C hg atG k l m s i).P) (fun i => (blocks C hg atG k l m s i).N)
    (fun i => (blocks C hg atG k l m s i).P_nonneg)
    (fun i => (blocks C hg atG k l m s i).N_nonneg)
    hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    family_blocks_lower (hg:=hg) f atG hsorted hcontained hq hHy hGy hBy hDy hvar hs ha hz i)
  have hT := PositiveBT3.Source.tReserve_nonnegative (hsorted T) (hcontained T) hq
    (Explicit.family_positive f hz).2.2.2.le hzf
  rw [decomposition C atG k l m hhg (Explicit.angle_domain atG hs).2 ha hflat]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.Source
end
end
end

section
/-!
## The negative-total reduction of a core E and the nonpositive A and T case

`reduce_negative_total` moves a core E with a negative selected total using only the necessary
conditions of the cycle, the outer anchors D and H and the DE and EH owners (`Input`). No low GA
owner and no normalized hard input is used to move E. The resulting cycle keeps every point,
frame and selected separator of G, A, B and T.

`actual_false` excludes every sign of a core E and both E owners when the selected A and T primary
errors are each nonpositive.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.CoreENegativeTotal
open Candidate ActualCoreEBlocks NegativeCoreE

/-- The local move of E needs only the D, E, H part of the geometry of the boundary cycle. A
high-GA source domain gives these fields from its points and its weak separators. -/
structure Input (q : ℝ) where
  cycle : SignedCycle
  necessary : cycle.Necessary q
  E_nonpos : (cycle.point E).y≤0
  H_nonneg : 0≤(cycle.point H).y
  D_outer : (cycle.point D).Outer q
  H_outer : (cycle.point H).Outer q
  de : Fin 4
  eh : Fin 4
  de_allowed : de=2 ∨ de=3
  eh_allowed : eh=0 ∨ eh=1
  DE : cycle.Feasible D de
  EH : cycle.Feasible E eh

/-- The selection of feasible DE and EH owners at the same state of E. No other owner or frame
changes. -/
def identityMove {q : ℝ} (I : Input q)
    (hc : (I.cycle.point E).Core) (de eh : Fin 4)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hDE : I.cycle.Feasible D de) (hEH : I.cycle.Feasible E eh) : CycleMove q I.cycle where
  point := I.cycle.point E
  theta := I.cycle.theta E
  sorted := I.necessary.sorted E
  contained := I.necessary.contained E
  core := hc
  nonpos := I.E_nonpos
  frame_range := ⟨min_le_left _ _,le_max_left _ _⟩
  de := de
  eh := eh
  de_allowed := hde
  eh_allowed := heh
  DE := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,D,E,quarterFeasible,sub_nonneg] using hDE
  EH := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  positive_nonincrease := by simp

structure Reduction (q : ℝ) (I : Input q) where
  move : CycleMove q I.cycle
  flat : move.point.a=7/12
  normal_form : 0≤eTotal move.cycle move.de move.eh ∨
    (move.point.a=7/12 ∧ primaryDE move.cycle move.de≤0 ∧ primaryEH move.cycle move.eh≤0)

/-- With EH0 feasible, E selects EH0 at the same state. The sign of the remaining DE error then
decides between the two alternatives of the normal form; that error is kept. -/
theorem reduce_with_secondary {q : ℝ} (I : Input q)
    (hq : q≤qCap) (hc : (I.cycle.point E).Core)
    (hEH : I.cycle.Feasible E 0) : Nonempty (Reduction q I) := by
  let de := I.de
  have hde : de=2 ∨ de=3 := by
    simpa [de] using I.de_allowed
  let O := identityMove I hc de 0 hde (Or.inl rfl) (I.DE) hEH
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta E) 0 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  have hf := (secondary_flat (I.necessary.sorted E) I.E_nonpos hc
    (I.necessary.sorted H) (I.necessary.contained H) hq hEH').1
  refine ⟨⟨O,hf,?_⟩⟩
  by_cases hpos : 0≤primaryDE O.cycle O.de
  · left
    rw [eTotal,O.primary_EH]
    simpa [O,identityMove] using hpos
  · right
    refine ⟨hf,le_of_lt (lt_of_not_ge hpos),?_⟩
    rw [O.primary_EH]
    norm_num [O,identityMove]

/-- The split over owners and signs at the same `q`. The two mixed cases use the compact core-arc
endpoint and the flat-gap endpoint; no feasibility or terminal-event hypothesis is assumed. -/
theorem reduce_negative_total {q : ℝ} (I : Input q)
    (hqL : qLow≤q) (hqU : q≤qCap) (hc : (I.cycle.point E).Core)
    (hneg : eTotal I.cycle (I.de) (I.eh)<0) :
    Nonempty (Reduction q I) := by
  by_cases hEH0 : I.cycle.Feasible E 0
  · exact reduce_with_secondary I hqU hc hEH0
  let C := I.cycle
  have heh : I.eh=1 := by
    have hh : I.eh=0 ∨ I.eh=1 := by
      exact I.eh_allowed
    rcases hh with hh | hh
    · exact False.elim (hEH0 (by simpa [hh] using I.EH))
    · exact hh
  have hde : I.de=2 ∨ I.de=3 := by
    exact I.de_allowed
  have hEH : quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 1 := by
    have hh : C.Feasible E 1 := by simpa [C,heh] using I.EH
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hh
  have hnot : ¬quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 0 := by
    intro hh
    apply hEH0
    simpa [C,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hh
  have hsmall (i : Vertex) : |delta C.theta i|≤frameCap := I.necessary.spread (next i) i
  have hflat {n : ℝ} (hn : n∈Ioc 0 frameCap)
      (heq : C.theta H-C.theta E= -n) : (C.point E).a=7/12 :=
    (genuine_negative_flat (I.necessary.sorted E) I.E_nonpos hc
      (I.necessary.sorted H) I.H_nonneg (I.necessary.contained H)
      hqU hn (by simpa only [heq] using hEH)
      (by simpa only [heq] using hnot)).1
  rcases hde with hde | hde
  · have hr : C.theta H-C.theta E<0 := by
      simpa [eTotal,primaryDE,primaryEH,hde,heh,C,delta,next,H,D,E] using hneg
    have hn : C.theta E-C.theta H∈Ioc 0 frameCap :=
      ⟨by linarith,(le_abs_self _).trans (I.necessary.spread E H)⟩
    have hf := hflat hn (by ring)
    let O := identityMove I hc 2 1 (Or.inl rfl) (Or.inr rfl)
      (by simpa [hde] using I.DE)
      (by simpa [heh] using I.EH)
    refine ⟨⟨O,hf,Or.inr ⟨hf,?_,?_⟩⟩⟩
    · rw [O.primary_DE]; norm_num [O,identityMove]
    · rw [O.primary_EH]; simpa [O,identityMove,C] using hr.le
  · have hsum : C.theta H-C.theta D<0 := by
      have hh := hneg
      simp [eTotal,primaryDE,primaryEH,hde,heh,delta,next,D,E] at hh
      show I.cycle.theta 0-I.cycle.theta 5<0
      linarith
    have hDE : quarterFeasible (C.point D) (C.point E) (C.theta E-C.theta D) 3 := by
      have hh : C.Feasible D 3 := by simpa [C,hde] using I.DE
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
        delta,next,D,E,quarterFeasible,sub_nonneg] using hh
    by_cases hEHneg : C.theta H<C.theta E
    · have hn : C.theta E-C.theta H∈Ioc 0 frameCap :=
        ⟨sub_pos.mpr hEHneg,(le_abs_self _).trans (I.necessary.spread E H)⟩
      have hf := hflat hn (by ring)
      by_cases hDEpos : C.theta D<C.theta E
      · obtain ⟨P⟩ := negative_EH_endpoint hqL hqU
          (I.necessary.sorted D) (I.necessary.core D) I.D_outer
          (I.necessary.sorted H) (I.necessary.core H) I.H_nonneg
          (I.necessary.contained H) (I.necessary.sorted E) I.E_nonpos hc hn
          ⟨sub_pos.mpr hDEpos,by linarith⟩ hDE
          (by simpa only [neg_sub] using hEH) (by simpa only [neg_sub] using hnot)
        let O := P.toCycle hDEpos
        refine ⟨⟨O,P.flat,Or.inr ⟨P.flat,?_,?_⟩⟩⟩
        · rw [O.primary_DE]; norm_num [O,NegativeEHEndpoint.toCycle]
        · rw [O.primary_EH]
          simpa [O,NegativeEHEndpoint.toCycle] using hsum.le
      · let O := identityMove I hc 3 1 (Or.inr rfl) (Or.inr rfl)
          (by simpa [hde] using I.DE)
          (by simpa [heh] using I.EH)
        refine ⟨⟨O,hf,Or.inr ⟨hf,?_,?_⟩⟩⟩
        · rw [O.primary_DE]
          simpa [O,identityMove,C] using sub_nonpos.mpr (le_of_not_gt hDEpos)
        · rw [O.primary_EH]
          simpa [O,identityMove,C] using (sub_neg.mpr hEHneg).le
    · have hp : 0<C.theta H-C.theta E := by
        have hr0 : 0≤C.theta H-C.theta E := sub_nonneg.mpr (le_of_not_gt hEHneg)
        apply lt_of_le_of_ne hr0
        intro heq
        apply hnot
        simpa [heq.symm,quarterFeasible,quarterProjection,add_comm] using hEH
      have hn : C.theta D-C.theta E∈Ioc 0 frameCap :=
        ⟨by linarith,(le_abs_self _).trans (I.necessary.spread D E)⟩
      obtain ⟨P⟩ := negative_DE_endpoint hqL hqU (I.necessary.sorted H)
        I.H_nonneg I.H_outer
        (I.necessary.sorted E) I.E_nonpos hc hn ⟨hp,by linarith⟩
        (by simpa only [neg_sub] using hDE) hEH
      let O := P.toCycle
      refine ⟨⟨O,P.flat,Or.inr ⟨P.flat,?_,?_⟩⟩⟩
      · rw [O.primary_DE]
        simp only [O,NegativeDEEndpoint.toCycle,ite_true]
        linarith [P.negative_remaining]
      · rw [O.primary_EH]; norm_num [O,NegativeDEEndpoint.toCycle]
/-- A core point with `a = 7/12` and `y ≤ 0` has `y ∈ [-1/2, 0]`, by its core equation. -/
theorem flat_tangent {P : SignedPoint} (hc : P.Core) (hf : P.a=7/12)
    (hy : P.y≤0) : P.y∈Icc (-(1/2:ℝ)) 0 := by
  have h := hc
  norm_num [SignedPoint.Core,SignedPoint.coreDistance,hf] at h
  have hm : |P.y|-1/2≤ max (|P.y|-1/2) 0 := le_max_left _ _
  have hn : 0≤ max (|P.y|-1/2) 0 := le_max_right _ _
  rw [abs_of_nonpos hy] at h hm hn
  constructor
  · nlinarith
  · exact hy

theorem selected_total (C : SignedCycle) (de eh : Bool) :
    eTotal C (if de then 3 else 2) (if eh then 1 else 0)=
      PairedE.cycleTotal C de eh := by
  cases de <;> cases eh <;>
    simp [eTotal,primaryDE,primaryEH,PairedE.cycleTotal,PairedE.total,PairedE.selected]

/-- Every owner and signed total of a core E is covered. The two mixed signs are moved at the same
`q`, and the paired-negative endpoint goes directly into the simultaneous flat-core stress. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hn : C.Necessary q) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hHo : (C.point H).Outer q) (hDo : (C.point D).Outer q)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (hga : ga=true → delta C.theta G≤0)
    (hab : ab=true → delta C.theta A≤0)
    (htd : td=true → delta C.theta T≤0) : False := by
  let I : Input q :=
    { cycle := C
      necessary := hn
      E_nonpos := hEy
      H_nonneg := hHy
      D_outer := hDo
      H_outer := hHo
      de := if de then 3 else 2
      eh := if eh then 1 else 0
      de_allowed := by cases de <;> simp
      eh_allowed := by cases eh <;> simp
      DE := hDE
      EH := hEH }
  by_cases he : 0≤PairedE.cycleTotal C de eh
  · exact PairedE.Negative.actual_false ga ab td de eh hn.sorted hn.contained
      hn.core hqU hHy hGy hBy hDy hvar hHG hGA hAB hBT hTD hDE hEH hga hab htd he
  have hnegative : eTotal I.cycle I.de I.eh<0 := by
    change eTotal C (if de then 3 else 2) (if eh then 1 else 0)<0
    rw [selected_total]
    exact lt_of_not_ge he
  obtain ⟨R⟩ := reduce_negative_total I hqL hqU hEc hnegative
  let O := R.move
  have hn' : O.cycle.Necessary q := O.necessary hn
  have hv' : positiveVariation O.cycle.theta≤frameCap :=
    O.positive_nonincrease.trans hvar
  have hHy' : 0≤(O.cycle.point H).y := by
    rw [(O.unchanged H (by decide)).1]; exact hHy
  have hGy' : (O.cycle.point G).y≤0 := by
    rw [(O.unchanged G (by decide)).1]; exact hGy
  have hBy' : (O.cycle.point B).y≤0 := by
    rw [(O.unchanged B (by decide)).1]; exact hBy
  have hDy' : (O.cycle.point D).y≤0 := by
    rw [(O.unchanged D (by decide)).1]; exact hDy
  have hHG' : O.cycle.Feasible H 0 ∨ O.cycle.Feasible H 2 :=
    hHG.imp ((O.other_feasible H (by decide) (by decide) 0).2)
      ((O.other_feasible H (by decide) (by decide) 2).2)
  have hGA' := (O.other_feasible G (by decide) (by decide) (if ga then 3 else 2)).2 hGA
  have hAB' := (O.other_feasible A (by decide) (by decide) (if ab then 2 else 0)).2 hAB
  have hBT' := (O.other_feasible B (by decide) (by decide) 2).2 hBT
  have hTD' := (O.other_feasible T (by decide) (by decide) (if td then 2 else 0)).2 hTD
  have hga' : ga=true → delta O.cycle.theta G≤0 := by
    intro hh; rw [O.other_delta G (by decide) (by decide)]; exact hga hh
  have hab' : ab=true → delta O.cycle.theta A≤0 := by
    intro hh; rw [O.other_delta A (by decide) (by decide)]; exact hab hh
  have htd' : td=true → delta O.cycle.theta T≤0 := by
    intro hh; rw [O.other_delta T (by decide) (by decide)]; exact htd hh
  obtain ⟨de',hde'⟩ : ∃de' : Bool,O.de=(if de' then 3 else 2) := by
    rcases O.de_allowed with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  obtain ⟨eh',heh'⟩ : ∃eh' : Bool,O.eh=(if eh' then 1 else 0) := by
    rcases O.eh_allowed with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have hDE' : O.cycle.Feasible D (if de' then 3 else 2) := by
    simpa only [hde'] using O.DE_actual
  have hEH' : O.cycle.Feasible E (if eh' then 1 else 0) := by
    simpa only [heh'] using O.EH_actual
  rcases R.normal_form with hnonneg | ⟨hflat,hdenonpos,hehnonpos⟩
  · have he' : 0≤PairedE.cycleTotal O.cycle de' eh' := by
      rw [←selected_total]
      change 0≤eTotal O.cycle O.de O.eh at hnonneg
      rwa [hde',heh'] at hnonneg
    exact PairedE.Negative.actual_false ga ab td de' eh' hn'.sorted hn'.contained
      hn'.core hqU hHy' hGy' hBy' hDy' hv' hHG' hGA' hAB' hBT' hTD'
      hDE' hEH' hga' hab' htd' he'
  · have hflat' : (O.cycle.point E).a=7/12 := by
      simpa [CycleMove.cycle,replacePoint] using hflat
    have hEy' : (O.cycle.point E).y∈Icc (-(1/2:ℝ)) 0 := by
      simpa [CycleMove.cycle,replacePoint] using flat_tangent O.core hflat O.nonpos
    have hde0 : de'=true → delta O.cycle.theta D≤0 := by
      intro hh
      change primaryDE O.cycle O.de≤0 at hdenonpos
      simpa [primaryDE,hde',hh] using hdenonpos
    have heh0 : eh'=true → delta O.cycle.theta E≤0 := by
      intro hh
      change primaryEH O.cycle O.eh≤0 at hehnonpos
      simpa [primaryEH,heh',hh] using hehnonpos
    exact NegativeFlatE.actual_false ga ab td de' eh' hn'.sorted hn'.contained
      hn'.core hqU hHy' hGy' hBy' hDy' hflat' hEy' hv' hHG' hGA' hAB'
      hBT' hTD' hDE' hEH' hga' hab' htd' hde0 heh0

end SquaresInCircles.Eight.GlobalGA.CoreENegativeTotal
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.SmallHigh
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open OrdinaryAngleConcentration

theorem pair_data {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (i : Fin 4) :
    0<Blocks.p .small .high θ z i ∧ Blocks.p .small .high θ z i≤Blocks.q .small .high θ z i ∧
      (2/3)*Blocks.q .small .high θ z i<Blocks.p .small .high θ z i := by
  have hp := NegativeDEPositiveTD.Explicit.high_pairs hθ hz
  fin_cases i
  · exact ⟨(hp 0).1,(hp 0).2.1,(hp 0).2.2.1⟩
  · exact ⟨(hp 1).1,(hp 1).2.1,(hp 1).2.2.1⟩
  · exact ⟨(hp 2).1,(hp 2).2.1,(hp 2).2.2.1⟩
  · exact ⟨(hp 0).1,(hp 0).2.1,(hp 0).2.2.1⟩

theorem q_ratio {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (i j : Fin 4) :
    Blocks.q .small .high θ z i<(29/25)*Blocks.q .small .high θ z j := by
  have hh := NegativeDEPositiveTD.Explicit.high_q_ratio hθ hz (Blocks.ordinaryIndex i) (Blocks.ordinaryIndex j)
  fin_cases i <;> fin_cases j <;> exact hh

theorem positive_lower {θ z P : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : P∈Icc 0 frameCap) (i : Fin 4) :
    -(109/200)*Blocks.q .small .high θ z i*P≤Blocks.positive .small .high θ z P i := by
  have hp := pair_data hθ hz i
  by_cases hi : i=3
  · subst i
    rw [Blocks.positive_D]
    change -(109/200)*1*P≤ -(Blocks.dCost+0)*P
    have hh := mul_le_mul_of_nonneg_right
      (show Blocks.dCost≤109/200 by dsimp [Blocks.dCost]; linarith [diagonal_bounds.2]) hP.1
    nlinarith
  · have hh := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1
      (show Blocks.q .small .high θ z i≤2*Blocks.p .small .high θ z i by linarith [hp.2.2]) hP
    simpa only [Blocks.positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,
      ite_eq_right hi,Explicit.errorCharge,zero_mul,sub_zero] using hh

theorem separated_lower {θ z P N : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) (i j : Fin 4) :
    Blocks.negative .small .high θ z (N-P) j≤
      Blocks.positive .small .high θ z P i+Blocks.negative .small .high θ z N j := by
  have hi := pair_data hθ hz i
  have hj := pair_data hθ hz j
  have hqj := hj.1.trans_le hj.2.1
  have hu := positive_lower hθ hz ⟨hP,hPN.trans hN⟩ i
  have hv := V_growth hj.1 hj.2.1 hj.2.2.le
    (show N-P∈Icc 0 frameCap from ⟨by linarith,by linarith⟩)
    (show N∈Icc 0 frameCap from ⟨hP.trans hPN,hN⟩) (by linarith)
  have hratio := q_ratio hθ hz i j
  have hpay := mul_nonneg (show 0≤(2/3)*Blocks.q .small .high θ z j-
      (109/200)*Blocks.q .small .high θ z i by nlinarith) hP
  dsimp [Blocks.negative]
  nlinarith

theorem same_lower {θ z P N : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) (i : Fin 4) :
    Blocks.negative .small .high θ z (N-P) i≤Blocks.block .small .high θ z P N i := by
  by_cases hi : i=3
  · subst i
    rw [Blocks.block_D]
    exact separated_lower hθ hz hP hPN hN 3 3
  · have hp := pair_data hθ hz i
    have hNc : N∈Icc 0 frameCap := ⟨hP.trans hPN,hN⟩
    have hsine : Blocks.q .small .high θ z i*Real.sin N≤Blocks.p .small .high θ z i := by
      have hh := mul_le_mul_of_nonneg_left (transport_trig hNc).2.2.2.1.le
        ((hp.1.trans_le hp.2.1).le)
      nlinarith [hp.2.2]
    have hh := NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le ⟨hP,hPN⟩ hNc hsine
    simpa only [Blocks.block,Blocks.negative,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      ite_eq_right hi,Explicit.errorCharge,zero_mul,sub_zero] using hh

theorem sum_to_negative {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (hs : s∈Icc (0:ℝ) (1/10))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃j : Fin 3,Explicit.V .small .high θ z j (θ-s)≤
      ∑i,Blocks.block .small .high θ z (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .small .high P N hθ hz hs hP hN hPb hNb hbalance
  have horder : s≤θ := by linarith [hθ.1,hs.2]
  have hPcap : 0≤frameCap-θ := by norm_num [frameCap]; linarith [hθ.2]
  have hPN : frameCap-θ≤frameCap-s := by linarith
  have hNcap : frameCap-s≤frameCap := by linarith [hs.1]
  have hsat : Blocks.negative .small .high θ z (θ-s) j≤Blocks.saturated .small .high θ z s i j := by
    by_cases hsame : i=j
    · subst j
      have hh := same_lower hθ hz hPcap hPN hNcap i
      rw [show frameCap-s-(frameCap-θ)=θ-s by ring] at hh
      rw [Blocks.saturated,ChargedHybridConcentration.saturated,ite_eq_left rfl]
      exact hh
    · have hh := separated_lower hθ hz hPcap hPN hNcap i j
      simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,ite_eq_right hsame,
        Blocks.positive,Blocks.negative,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
  have hpure : Blocks.pure .small .high θ z s i j=Blocks.negative .small .high θ z (θ-s) j := by
    simp [Blocks.pure,ChargedHybridConcentration.pure,horder,Blocks.negative]
  rw [hpure,min_eq_left hsat,Blocks.negative_to_ordinary] at hij
  exact ⟨Blocks.ordinaryIndex j,hij⟩

theorem negative_positive {a z s : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (0:ℝ) (1/10)) (i : Fin 3) :
    0<Explicit.baseline .small .high a z+NegativeEH.g s+
      Explicit.V .small .high (a+z) z i (a+z-s) := by
  have hp := NegativeDEPositiveTD.Explicit.high_pairs hθ ⟨hz,by linarith⟩ i
  have hg := NegativeEH.g_concave.subset
    (Icc_subset_Icc le_rfl (by norm_num [frameCap] : (1/10:ℝ)≤frameCap)) (convex_Icc 0 (1/10))
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1 (by linarith [hp.2.2.1]))
    (a:=-1) (b:=a+z) (l:=0) (u:=1/10)
    (fun s hs => ⟨by linarith [hs.2,hθ.1],by simp only [frameCap]; linarith [hs.1,hθ.2]⟩)
  have hc := TwoPositive.Split.add_constant (hg.add hv) (Explicit.baseline .small .high a z)
  have hg0 : NegativeEH.g 0=0 := by simp [NegativeEH.g]
  have h0 : 0<NegativeEH.g 0+V R (NegativeDEPositiveTD.Explicit.p .high (a+z) z i)
      (NegativeDEPositiveTD.Explicit.q .high (a+z) z i) (-1*0+(a+z))+
      Explicit.baseline .small .high a z := by
    have h : 0<Explicit.baseline .small .high a z+V R (NegativeDEPositiveTD.Explicit.p .high (a+z) z i)
        (NegativeDEPositiveTD.Explicit.q .high (a+z) z i) (a+z) :=
      HighSplit.small_zero_positive hθ ha hz i
    rw [hg0,show -1*(0:ℝ)+(a+z)=a+z by ring]
    linarith
  have h1 : 0<NegativeEH.g (1/10)+V R (NegativeDEPositiveTD.Explicit.p .high (a+z) z i)
      (NegativeDEPositiveTD.Explicit.q .high (a+z) z i) (-1*(1/10)+(a+z))+
      Explicit.baseline .small .high a z := by
    have h : 0<Explicit.baseline .small .high a z+NegativeEH.g (1/10)+
        V R (NegativeDEPositiveTD.Explicit.p .high (a+z) z i)
        (NegativeDEPositiveTD.Explicit.q .high (a+z) z i) (a+z-1/10) :=
      HighSplit.small_v_positive hθ ha hz i
    rw [show -1*(1/10:ℝ)+(a+z)=a+z-1/10 by ring]
    linarith
  have hh := concave_gt_of_endpoints (c:=0) hc hs h0 h1
  simp only [Pi.add_apply,show -1*s+(a+z)=a+z-s by ring] at hh
  change 0<Explicit.baseline .small .high a z+NegativeEH.g s+
    V R (NegativeDEPositiveTD.Explicit.p .high (a+z) z i)
      (NegativeDEPositiveTD.Explicit.q .high (a+z) z i) (a+z-s)
  linarith

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.stressBase .small .high a z s+
      ∑i,Blocks.block .small .high (a+z) z (P i) (N i) i := by
  obtain ⟨i,hi⟩ := sum_to_negative P N hθ ⟨hz,by linarith⟩ hs hP hN hPb hNb hbalance
  have hh := negative_positive hθ ha hz hs i
  dsimp [Explicit.stressBase,Explicit.gain]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.SmallHigh
end
end
end
