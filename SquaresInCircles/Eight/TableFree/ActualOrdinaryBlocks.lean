module

public import SquaresInCircles.Eight.TableFree.CorrelatedSameBlock
public import SquaresInCircles.Eight.TableFree.PositivePrimaryBaselines

/-!
# The original seven angles as four ordinary signed blocks

Uncompiled source draft. The AB angle is assigned to its actual weak
owner. A primary G or T angle is removed only from the ordinary budget;
it remains in the exact primary baseline. The two sign totals are exact
finite sums of the original angles, including zero angles and weak ties.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ActualOrdinaryBlocks
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity
open PositivePrimaryBaselines CorrelatedSameBlock

structure Block where
  alpha : ℝ
  beta : ℝ
  u : ℝ
  v : ℝ

namespace Block

def p (B : Block) : ℝ := min B.alpha B.beta
def q (B : Block) : ℝ := max B.alpha B.beta
def P (B : Block) : ℝ := positivePart B.u+positivePart B.v
def N (B : Block) : ℝ := negativePart B.u+negativePart B.v
def increment (B : Block) (R : ℝ) : ℝ :=
  B.alpha*psi B.u+B.beta*psi B.v-
    R*(pairNorm B.alpha B.beta (B.u+B.v)-pairNorm B.alpha B.beta 0)

theorem P_nonneg (B : Block) : 0≤B.P :=
  add_nonneg (positivePart_nonneg _) (positivePart_nonneg _)
theorem N_nonneg (B : Block) : 0≤B.N :=
  add_nonneg (negativePart_nonneg _) (negativePart_nonneg _)
theorem signed_total (B : Block) : B.P-B.N=B.u+B.v := by
  dsimp [P,N]
  linarith [positive_sub_negative B.u,positive_sub_negative B.v]

theorem norm_min_max (B : Block) (t : ℝ) :
    pairNorm B.alpha B.beta t=pairNorm B.p B.q t := by
  rcases le_total B.alpha B.beta with h | h
  · simp [p,q,min_eq_left h,max_eq_right h]
  · simp [p,q,min_eq_right h,max_eq_left h,pairNorm_symm]

end Block

theorem concave_zero_subadditive {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc 0 frameCap) f)
    (hf0 : f 0=0) {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b≤frameCap) :
    f (a+b)≤f a+f b := by
  by_cases hz : a+b=0
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0,hb0,hf0]
  have hp : 0<a+b := by linarith
  have htotal : a+b∈Icc 0 frameCap := ⟨hp.le,hab⟩
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hca := hf.2 hzero htotal (div_nonneg hb hp.le) (div_nonneg ha hp.le)
    (by field_simp [hz]; ring)
  have hcb := hf.2 hzero htotal (div_nonneg ha hp.le) (div_nonneg hb hp.le)
    (by field_simp [hz]; ring)
  have hea : (b/(a+b))*0+(a/(a+b))*(a+b)=a := by field_simp [hz]; ring
  have heb : (a/(a+b))*0+(b/(a+b))*(a+b)=b := by field_simp [hz]; ring
  simp only [smul_eq_mul,hea,hf0,mul_zero,zero_add] at hca
  simp only [smul_eq_mul,heb,hf0,mul_zero,zero_add] at hcb
  have he : (a/(a+b))*f (a+b)+(b/(a+b))*f (a+b)=f (a+b) := by
    field_simp [hz]
    ring
  linarith

theorem phi_increment_concave :
    ConcaveOn ℝ (Icc 0 frameCap) (fun t => phi t-1) := by
  apply concave_of_deriv2
    (f' := fun t => Real.cos t-Real.sin t)
    (f'' := fun t => -Real.sin t-Real.cos t)
  · intro t _
    exact (phi_hasDerivAt t).sub_const 1
  · intro t _
    exact (Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t)
  · intro t ht
    obtain ⟨hc,_,hs,_,_⟩ := transport_trig ht
    linarith

theorem cosine_increment_concave :
    ConcaveOn ℝ (Icc 0 frameCap) (fun t => Real.cos t-1) := by
  apply concave_of_deriv2
    (f' := fun t => -Real.sin t) (f'' := fun t => -Real.cos t)
  · intro t _
    exact (Real.hasDerivAt_cos t).sub_const 1
  · intro t _
    exact (Real.hasDerivAt_sin t).neg
  · intro t ht
    have hc := (transport_trig ht).1
    linarith

theorem psi_signed {t : ℝ}
    (hP : positivePart t≤frameCap) (hN : negativePart t≤frameCap) :
    psi t=(phi (positivePart t)-1)+(Real.cos (negativePart t)-1) := by
  by_cases ht : 0≤t
  · have hp : positivePart t=t := max_eq_left ht
    have hn : negativePart t=0 := max_eq_right (by linarith : -t≤0)
    rw [hp,hn]
    simp only [Real.cos_zero,sub_self,add_zero]
    exact psi_positive ⟨ht,by simpa [hp] using hP⟩
  · have ht' : t≤0 := (lt_of_not_ge ht).le
    have hp : positivePart t=0 := max_eq_right ht'
    have hn : negativePart t= -t := max_eq_left (by linarith : 0≤-t)
    rw [hp,hn]
    simp only [phi_zero,sub_self,zero_add]
    simpa only [neg_neg] using psi_negative
      (show -t∈Icc 0 frameCap from ⟨by linarith,by simpa [hn] using hN⟩)

theorem weighted_psi_minorant {p q a t : ℝ} (hpa : p≤a) (haq : a≤q)
    (hP : positivePart t≤frameCap) (hN : negativePart t≤frameCap) :
    p*(phi (positivePart t)-1)+q*(Real.cos (negativePart t)-1)≤a*psi t := by
  rw [psi_signed hP hN]
  have hf := sub_nonneg.mpr (one_le_phi ⟨positivePart_nonneg t,hP⟩)
  have hg : Real.cos (negativePart t)-1≤0 := by linarith [Real.cos_le_one (negativePart t)]
  have h1 := mul_le_mul_of_nonneg_right hpa hf
  have h2 := mul_le_mul_of_nonpos_right haq hg
  nlinarith

theorem Block.minorant (B : Block) (R : ℝ) (hp : 0≤B.p)
    (hP : B.P≤frameCap) (hN : B.N≤frameCap) :
    mixedBlock R B.p B.q B.P B.N≤B.increment R := by
  have hpq : B.p≤B.q := min_le_max
  have hq : 0≤B.q := hp.trans hpq
  have hPu : positivePart B.u≤frameCap := by
    have h := positivePart_nonneg B.v
    dsimp [Block.P] at hP
    linarith
  have hPv : positivePart B.v≤frameCap := by
    have h := positivePart_nonneg B.u
    dsimp [Block.P] at hP
    linarith
  have hNu : negativePart B.u≤frameCap := by
    have h := negativePart_nonneg B.v
    dsimp [Block.N] at hN
    linarith
  have hNv : negativePart B.v≤frameCap := by
    have h := negativePart_nonneg B.u
    dsimp [Block.N] at hN
    linarith
  have hu := weighted_psi_minorant (min_le_left B.alpha B.beta) (le_max_left B.alpha B.beta) hPu hNu
  have hv := weighted_psi_minorant (min_le_right B.alpha B.beta) (le_max_right B.alpha B.beta) hPv hNv
  have hpositive := concave_zero_subadditive phi_increment_concave (by simp)
    (positivePart_nonneg B.u) (positivePart_nonneg B.v) hP
  have hnegative := concave_zero_subadditive cosine_increment_concave (by simp)
    (negativePart_nonneg B.u) (negativePart_nonneg B.v) hN
  have hpMul := mul_le_mul_of_nonneg_left hpositive hp
  have hqMul := mul_le_mul_of_nonneg_left hnegative hq
  dsimp [mixedBlock,Block.increment]
  rw [B.signed_total,B.norm_min_max (B.u+B.v),B.norm_min_max 0]
  change B.p*(phi B.P-1)+B.q*(Real.cos B.N-1)-
      R*(pairNorm B.p B.q (B.u+B.v)-pairNorm B.p B.q 0)≤_
  dsimp [Block.p,Block.q,Block.P,Block.N] at *
  nlinarith

def blocks (C : SignedCycle) (ab bt td : Fin 4) (n k l b t : ℝ) : Fin 4 → Block :=
  ![⟨n,1,delta C.theta H,delta C.theta E⟩,
    ⟨l,k,if ab=0 then 0 else delta C.theta A,0⟩,
    ⟨l,b,if ab=0 then delta C.theta A else 0,if bt=2 then delta C.theta B else 0⟩,
    ⟨1,t,delta C.theta D,if td=0 then delta C.theta T else 0⟩]

def removed (C : SignedCycle) (bt td : Fin 4) : ℝ :=
  delta C.theta G+(if bt=3 then delta C.theta B else 0)+
    (if td=2 then delta C.theta T else 0)

theorem sum_parts (C : SignedCycle) {ab bt td : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (n k l b t : ℝ) (f : ℝ → ℝ) (hf0 : f 0=0) :
    (∑ i,f (blocks C ab bt td n k l b t i).u+f (blocks C ab bt td n k l b t i).v)=
      (∑ j,f (delta C.theta j))-f (delta C.theta G)-
        (if bt=3 then f (delta C.theta B) else 0)-
        (if td=2 then f (delta C.theta T) else 0) := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;> rcases htd with rfl | rfl <;>
    simp [blocks,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf0] <;> ring

theorem block_budgets {C : SignedCycle} {ab bt td : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (n k l b t : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G)
    (hBT : bt=3 → 0≤delta C.theta B) (hTD : td=2 → 0≤delta C.theta T) :
    removed C bt td∈Icc 0 frameCap ∧
    (∑ i,(blocks C ab bt td n k l b t i).P)≤frameCap-removed C bt td ∧
    (∑ i,(blocks C ab bt td n k l b t i).N)=
      removed C bt td+∑ i,(blocks C ab bt td n k l b t i).P := by
  have hp := sum_parts C hab hbt htd n k l b t positivePart positivePart_zero
  have hn := sum_parts C hab hbt htd n k l b t negativePart negativePart_zero
  have heq := variations_equal C.theta
  have hP0 := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => (blocks C ab bt td n k l b t i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => (blocks C ab bt td n k l b t i).N_nonneg)
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hG
  have hNG : negativePart (delta C.theta G)=0 := max_eq_right (by linarith : -delta C.theta G≤0)
  have hPB : (if bt=3 then positivePart (delta C.theta B) else 0)=
      (if bt=3 then delta C.theta B else 0) := by
    by_cases hb : bt=3
    · simp [hb,positivePart,max_eq_left (hBT hb)]
    · simp [hb]
  have hPT : (if td=2 then positivePart (delta C.theta T) else 0)=
      (if td=2 then delta C.theta T else 0) := by
    by_cases ht : td=2
    · simp [ht,positivePart,max_eq_left (hTD ht)]
    · simp [ht]
  have hNB : (if bt=3 then negativePart (delta C.theta B) else 0)=0 := by
    by_cases hb : bt=3
    · simp [hb,negativePart,max_eq_right (by linarith [hBT hb] : -delta C.theta B≤0)]
    · simp [hb]
  have hNT : (if td=2 then negativePart (delta C.theta T) else 0)=0 := by
    by_cases ht : td=2
    · simp [ht,negativePart,max_eq_right (by linarith [hTD ht] : -delta C.theta T≤0)]
    · simp [ht]
  have hremoved : 0≤removed C bt td := by
    unfold removed
    have hB : 0≤(if bt=3 then delta C.theta B else 0) := by
      split_ifs with hb
      · exact hBT hb
      · rfl
    have hT : 0≤(if td=2 then delta C.theta T else 0) := by
      split_ifs with ht
      · exact hTD ht
      · rfl
    linarith
  have hp' : (∑ i,(blocks C ab bt td n k l b t i).P)=
      positiveVariation C.theta-removed C bt td := by
    change (∑ i,positivePart (blocks C ab bt td n k l b t i).u+
      positivePart (blocks C ab bt td n k l b t i).v)=_
    rw [hp,hPG,hPB,hPT]
    dsimp [removed,positiveVariation]
    ring
  have hn' : (∑ i,(blocks C ab bt td n k l b t i).N)=negativeVariation C.theta := by
    change (∑ i,negativePart (blocks C ab bt td n k l b t i).u+
      negativePart (blocks C ab bt td n k l b t i).v)=_
    rw [hn,hNG,hNB,hNT]
    simp [negativeVariation]
  exact ⟨⟨hremoved,by linarith⟩,by linarith,by linarith⟩

theorem td_increment_eq (C : SignedCycle) {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (R k l η : ℝ) :
    tdIncrement C ab R k l η=
      ∑ i,(blocks C ab 2 2
        (SecondaryEStress.tiltedWeight k η (delta C.theta G)) k l
        (SecondaryEStress.tiltedWeight k η (delta C.theta T)) k i).increment R := by
  rcases hab with rfl | rfl <;>
    simp [tdIncrement,blocks,Block.increment,anchorNormSum,zeroNorms,Fin.sum_univ_succ,
      pairNorm_symm k l] <;> ring

theorem bt_increment_eq (C : SignedCycle) {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (R k l η : ℝ) :
    btIncrement C ab R k l η=
      ∑ i,(blocks C ab 3 0
        (SecondaryEStress.tiltedWeight k η (delta C.theta G)) k l k
        (SecondaryEStress.tiltedWeight k η (delta C.theta B)) i).increment R := by
  rcases hab with rfl | rfl <;>
    simp [btIncrement,blocks,Block.increment,anchorNormSum,zeroNorms,Fin.sum_univ_succ,
      pairNorm_symm k l] <;> ring

theorem secondary_increment_eq (C : SignedCycle) {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (R k l c η : ℝ) :
    secondaryIncrement C ab R k l c η=
      ∑ i,(blocks C ab 2 0
        (SecondaryEStress.tiltedWeight k η (delta C.theta G)) k l c c i).increment R := by
  rcases hab with rfl | rfl <;>
    simp [secondaryIncrement,blocks,Block.increment,anchorNormSum,zeroNorms,Fin.sum_univ_succ,
      pairNorm_symm k l] <;> ring

end SquaresInCircles.Eight.TableFree.ActualOrdinaryBlocks
