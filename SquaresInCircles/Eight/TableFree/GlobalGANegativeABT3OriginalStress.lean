module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3OriginalData
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3DActual

/-!
# Reference weighted stress on the original points

Uncompiled Sections 2--8. The reference stress is an algebraic sum on
the unchanged seven points. Its positivity requires no reference edge
to be feasible. The two-angle D term uses the diagonal support at low
z and the complete-circle support at high z, exactly as in the note.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Source
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
  cases atG <;> rcases hhg with rfl|rfl <;>
    simp only [aError,NegativeAPositiveTD.Source.aError,↓reduceIte] at ha <;>
    simp [actualStress,demand,force,source,target,work,add,scale,previous,
      owners,weights,blocks,actualBlocks,actualD,PositiveTD.actualPairIncrement,
      pairF,pairG,PositiveBT3.Source.tReserve,PositiveBT3.forceA,PositiveBT3.forceB,
      baseline,PositiveBT3.tilted,lambdaG,lambdaB,secant,
      NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,NegativeAPositiveTD.secant,
      Real.tan_eq_sin_div_cos,Fin.sum_univ_succ,word,next,H,G,A,B,T,D,E,
      SignedPoint.reflect,ha,hflat,fullSupport,add_comm,add_left_comm,add_assoc] <;>
    field_simp [hcos] <;> ring

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (atG : Bool) {k l m s : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0<m)
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
      have hc := Explicit.low_rotation hz
      have hD := DEnvelope.actual_minorant (hsorted D) hDy (hcontained D) hq
        (show Explicit.c .low z∈Icc 1 DEnvelope.Cmax from ⟨hc.1.le,hc.2.le⟩) hdom
      have hN : (blocks C hg atG k l m s 3).N∈Icc 0 frameCap :=
        ⟨(blocks C hg atG k l m s 3).N_nonneg,hb.2⟩
      have hkRange := (Explicit.low_ranges hz).1
      have hv := OrdinaryNegativeEnvelope.V_monotone_smaller (Real.sqrt_nonneg _) (q:=1)
        (by norm_num) hN
        (show k∈Icc (1/2:ℝ) 1 by dsimp [k,z]; constructor <;> linarith [hkRange.1,hkRange.2])
        (show (17/25:ℝ)∈Icc (1/2:ℝ) 1 by norm_num)
        (show k≤17/25 by dsimp [k,z]; linarith [hkRange.2])
      have hsupp : clippedSupport 1 (Explicit.c .low z)=(1+Explicit.c .low z)*diagonal := by
        simp [clippedSupport,diagonalSupport,hc.1.le]
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
      linarith
    · have hc := Explicit.high_rotation hz
      have hnot : ¬1≤Explicit.c .high z := not_le.mpr hc.2.2
      have hh := hordinary 3 (Or.inl rfl) (P:=(C.point D).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy) (by simpa using hcontained D)
      simpa [Concentration.block,actualBlocks,actualD,PositiveTD.actualPairIncrement,
        blocks,pairF,pairG,PositiveBT3.forceA,PositiveBT3.forceB,clippedSupport,
        SignedPoint.reflect,Explicit.c,hnot,z,k,l,m,add_comm,add_left_comm,add_assoc] using hh

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
    family_blocks_lower f atG hsorted hcontained hq hHy hGy hBy hDy hvar hs ha hz i)
  have hT := PositiveBT3.Source.tReserve_nonnegative (hsorted T) (hcontained T) hq
    (Explicit.family_positive f hz).2.2.2.le hzf
  rw [decomposition C atG k l m hhg (Explicit.angle_domain atG hs).2 ha hflat]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Source
