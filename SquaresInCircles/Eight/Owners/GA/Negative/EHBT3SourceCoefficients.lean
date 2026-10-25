module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3FarLowScalar
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3HighScalar
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3SmallLowSlopes

/-!
# Eight squares: coefficients needed at the original EH1/BT3 source

The H comparison needs the literal
interval [1/2,17/20], and the far multiplier needs [3/5,4/5]. These are
proved for the actual selected family, independently of any endpoint
allocation or favorable source owner.
-/

section
/-!
## Complete small-EH, low-total BT3 scalar exclusion

Both surplus signs and every same/separated
allocation are included. The D positive penalty and H negative minorant
remain paired in the distinguished block. The original A/BT split is
held fixed during the EH-magnitude comparisons.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

lemma pure_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (a+z) (1/10:ℝ)) (i : Fin 4) :
    0<baseline .smallLow (a+z) a z+gain s+positive (a+z) (s-(a+z)) i := by
  have ht : a+z∈Icc (0:ℝ) (1/10) := ⟨hθ.1,hs.1.trans hs.2⟩
  have hh := positive_monotone hθ i (show a+z∈Icc (a+z) (1/10:ℝ) from ⟨le_rfl,ht.2⟩)
    hs hs.1
  simp only [sub_self,positive,PositiveTD.Hybrid.positive_zero,add_zero] at hh
  have he := equal_positive ht ha hz
  simp only [positive]
  linarith

lemma pure_negative {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (0:ℝ) (1/10))
    (horder : s≤a+z) (i : Fin 4) :
    0<baseline .smallLow (a+z) a z+gain s+negative (a+z) (a+z-s) i := by
  have hk := low_k_range hθ
  have hg := NegativeEH.g_concave.subset
    (Icc_subset_Icc le_rfl
      ((min_le_right (a+z) (1/10:ℝ)).trans (by norm_num [frameCap])))
    (convex_Icc 0 (min (a+z) (1/10:ℝ)))
  have hv := concave_affine_argument
    (V_concave (R:=R) (p:=k (a+z)) (q:=1) (Real.sqrt_nonneg qCap) radius_sq.le
      (by linarith [hk.1]) (by linarith [hk.2]) (by linarith [hk.1]))
    (a:=-1) (b:=a+z) (l:=0) (u:=min (a+z) (1/10))
    (fun t ht => ⟨by linarith [ht.2,min_le_left (a+z) (1/10:ℝ)],
      by norm_num [frameCap]; linarith [ht.1,hθ.2]⟩)
  have hc : ConcaveOn ℝ (Icc 0 (min (a+z) (1/10)))
      (fun t => baseline .smallLow (a+z) a z+gain t+V R (k (a+z)) 1 (a+z-t)) := by
    refine ((hg.add hv).add_const (baseline .smallLow (a+z) a z)).congr ?_
    intro t _
    simp only [Pi.add_apply,neg_one_mul,neg_add_eq_sub,gain_eq]
    ring
  have h0 : 0<baseline .smallLow (a+z) a z+gain 0+V R (k (a+z)) 1 (a+z-0) := by
    simpa [gain] using zero_positive hθ ha hz
  have h1 : 0<baseline .smallLow (a+z) a z+gain (min (a+z) (1/10))+
      V R (k (a+z)) 1 (a+z-min (a+z) (1/10)) := by
    by_cases ht : a+z≤1/10
    · rw [min_eq_left ht,sub_self]
      have hV : V R (k (a+z)) 1 0=0 := by simp [V]
      rw [hV,add_zero]
      exact equal_positive ⟨hθ.1,ht⟩ ha hz
    · rw [min_eq_right (lt_of_not_ge ht).le]
      exact negative_at_v_positive ⟨(lt_of_not_ge ht).le,hθ.2⟩ ha hz
  have hH := concave_gt_of_endpoints hc ⟨hs.1,le_min horder hs.2⟩ h0 h1
  have hcmp := H_le_negative hθ
    (show a+z-s∈Icc 0 frameCap from ⟨by linarith,
      by norm_num [frameCap]; linarith [hs.1,hθ.2]⟩) i
  linarith

lemma separated_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (0:ℝ) (1/10)) (i j : Fin 4) :
    0<baseline .smallLow (a+z) a z+gain s+
      positive (a+z) (frameCap-(a+z)) i+negative (a+z) (frameCap-s) j := by
  have hm := separated_monotone hθ (show (0:ℝ)∈Icc 0 (1/10:ℝ) by norm_num) hs hs.1
  simp only [gain,Real.sin_zero,Real.cos_zero,mul_zero,sub_self,sub_zero,zero_add] at hm
  have hcmp := H_le_negative hθ
    (show frameCap-s∈Icc 0 frameCap by
      norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2]) j
  have hzero := zero_separated_lower hθ i 0
  change V R (k (a+z)) 1 (a+z)≤
    positive (a+z) (frameCap-(a+z)) i+V R (k (a+z)) 1 frameCap at hzero
  have hp := zero_positive hθ ha hz
  dsimp only [gain]
  linarith

lemma same_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (0:ℝ) (1/10)) (i : Fin 4) :
    0<baseline .smallLow (a+z) a z+gain s+
      block (a+z) (frameCap-(a+z)) (frameCap-s) i := by
  have hP : frameCap-(a+z)∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap := by
    norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2]
  fin_cases i
  · have hm := HG_same_monotone hθ (show (0:ℝ)∈Icc 0 (1/10:ℝ) by norm_num) hs hs.1
    have hzero := zero_same_lower hθ 0
    have hp := zero_positive hθ ha hz
    simp only [HG_same,gain,Real.sin_zero,Real.cos_zero,mul_zero,sub_self,sub_zero,zero_add] at hm
    change V R (k (a+z)) 1 (a+z)≤ mixedBlock R (k (a+z)) 1 (frameCap-(a+z)) frameCap at hzero
    change 0<baseline .smallLow (a+z) a z+gain s+
      mixedBlock R (k (a+z)) 1 (frameCap-(a+z)) (frameCap-s)
    dsimp only [gain]
    linarith
  · have hm := HG_same_monotone hθ (show (0:ℝ)∈Icc 0 (1/10:ℝ) by norm_num) hs hs.1
    have hzero := zero_same_lower hθ 1
    have hp := zero_positive hθ ha hz
    simp only [HG_same,gain,Real.sin_zero,Real.cos_zero,mul_zero,sub_self,sub_zero,zero_add] at hm
    change V R (k (a+z)) 1 (a+z)≤ mixedBlock R (k (a+z)) 1 (frameCap-(a+z)) frameCap at hzero
    change 0<baseline .smallLow (a+z) a z+gain s+
      mixedBlock R (k (a+z)) 1 (frameCap-(a+z)) (frameCap-s)
    dsimp only [gain]
    linarith
  · have hc := coefficients hθ 2
    have hmq : m (a+z)≤5821/5000 := hc.2.2.2
    have hm : 0≤ m (a+z) := by change 0≤q (a+z) 2; exact (hc.1.trans_le hc.2.1).le
    by_cases horder : s≤a+z
    · have hsin := mul_le_mul_of_nonneg_left (transport_trig hN).2.2.2.1.le hm
      have hcmp := NegativeAPositiveTD.SameBlock.negative_surplus
        (by norm_num : (0:ℝ)≤1)
        (show frameCap-(a+z)∈Icc 0 (frameCap-s) from ⟨hP.1,by linarith⟩) hN
        (show m (a+z)*Real.sin (frameCap-s)≤1 by
          nlinarith [hmq])
      have hp := pure_negative hθ ha hz hs horder 2
      change 0<baseline .smallLow (a+z) a z+gain s+
        mixedBlock R 1 (m (a+z)) (frameCap-(a+z)) (frameCap-s)
      change 0<baseline .smallLow (a+z) a z+gain s+V R 1 (m (a+z)) (a+z-s) at hp
      rw [show frameCap-s-(frameCap-(a+z))=a+z-s by ring] at hcmp
      linarith
    · have hcmp := NegativeAPositiveTD.SameBlock.positive_surplus
        (by norm_num : (0:ℝ)≤1)
        (show m (a+z)≤(17/10)*1 by linarith [hmq]) hP
        (show frameCap-s∈Icc 0 (frameCap-(a+z)) from ⟨hN.1,by linarith⟩)
      have hp := pure_positive hθ ha hz ⟨(lt_of_not_ge horder).le,hs.2⟩ 2
      change 0<baseline .smallLow (a+z) a z+gain s+U R 1 (m (a+z)) (s-(a+z)) at hp
      change 0<baseline .smallLow (a+z) a z+gain s+
        mixedBlock R 1 (m (a+z)) (frameCap-(a+z)) (frameCap-s)
      rw [show frameCap-(a+z)-(frameCap-s)=s-(a+z) by ring] at hcmp
      linarith
  · simpa [block,positive,negative,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive,
      add_assoc] using separated_positive hθ ha hz hs 3 3

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<baseline .smallLow (a+z) a z+charge .smallLow s+
      ∑i,block (a+z) (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := concentrate P N hθ hs hP hN hPb hNb hbalance
  have hp : 0<baseline .smallLow (a+z) a z+gain s+pure (a+z) s i j := by
    by_cases horder : s≤a+z
    · simpa [pure,ChargedHybridConcentration.pure,horder,negative] using
        pure_negative hθ ha hz hs horder j
    · simpa [pure,ChargedHybridConcentration.pure,horder,
        ChargedHybridConcentration.positive,positive] using
        pure_positive hθ ha hz ⟨(lt_of_not_ge horder).le,hs.2⟩ i
  have ht : 0<baseline .smallLow (a+z) a z+gain s+saturated (a+z) s i j := by
    by_cases he : i=j
    · subst j
      simpa [saturated,ChargedHybridConcentration.saturated,ChargedHybridConcentration.block,block] using
        same_positive hθ ha hz hs i
    · simpa [saturated,ChargedHybridConcentration.saturated,ChargedHybridConcentration.positive,
        positive,negative,he,add_assoc] using separated_positive hθ ha hz hs i j
  have hm : -(baseline .smallLow (a+z) a z+gain s)<
      min (pure (a+z) s i j) (saturated (a+z) s i j) := lt_min (by linarith) (by linarith)
  simp only [charge,far,Bool.false_eq_true,ite_false]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.SmallLow
end
end
end

section
/-!
## The negative-EH1 / BT3 scalar domain

The small-low family keeps its sorted-D baseline and the distinguished two-sign D minorant; all
other families use four ordinary full-circle blocks. The charge of the EH multiplier is subtracted
from the positive mass. Both signed caps and the signed balance are hypotheses of
`scalar_positive`.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Scalar
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def left : Family→ℝ
  | .smallLow => 0 | .smallHigh => 1/6 | .farLow => 0 | .farHigh => 1/4
def right : Family→ℝ
  | .smallLow => 1/6 | .smallHigh => frameCap | .farLow => 1/4 | .farHigh => frameCap
def eLeft (f : Family) : ℝ := if far f then 1/10 else 0
def eRight (f : Family) : ℝ := if far f then 1/4 else 1/10

def block (f : Family) (θ z P N : ℝ) (i : Fin 4) : ℝ :=
  if f=.smallLow then SmallLow.block θ P N i else Blocks.block f θ z P N i

lemma frame_domain (f : Family) {θ : ℝ} (hθ : θ∈Icc (left f) (right f)) :
    θ∈Icc 0 frameCap := by
  cases f <;> norm_num [left,right,frameCap] at hθ ⊢ <;>
    exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

theorem family_cover {θ s : ℝ} (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc (0:ℝ) (1/4)) :
    ∃f : Family,θ∈Icc (left f) (right f) ∧ s∈Icc (eLeft f) (eRight f) := by
  by_cases he : s≤1/10
  · by_cases ht : θ≤1/6
    · exact ⟨.smallLow,⟨hθ.1,ht⟩,⟨hs.1,he⟩⟩
    · exact ⟨.smallHigh,⟨(lt_of_not_ge ht).le,hθ.2⟩,⟨hs.1,he⟩⟩
  · by_cases ht : θ≤1/4
    · exact ⟨.farLow,⟨hθ.1,ht⟩,⟨(lt_of_not_ge he).le,hs.2⟩⟩
    · exact ⟨.farHigh,⟨(lt_of_not_ge ht).le,hθ.2⟩,⟨(lt_of_not_ge he).le,hs.2⟩⟩

/-- The four-block inequality. This is a scalar theorem; the budgets come from the errors of the
cycle in `scalar_nonpositive`. -/
theorem scalar_positive (f : Family) {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (left f) (right f)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (eLeft f) (eRight f)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<baseline f (a+z) a z+charge f s+∑i,block f (a+z) z (P i) (N i) i := by
  cases f
  · exact SmallLow.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact HighScalar.small_high_scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact FarLow.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact HighScalar.far_high_scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Scalar
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

lemma small_high_k {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.k .smallHigh θ∈Icc (1/2:ℝ) (17/20) := by
  let x : ℝ := θ-1/6
  have hx : x∈Icc (0:ℝ) (8/15) := ⟨by dsimp [x]; linarith [hθ.1],by dsimp [x]; linarith [hθ.2]⟩
  have hlow : 0≤(2609/5000:ℝ)-(1489/2500)*x+(527/1250)*x^2 := by
    nlinarith [sq_nonneg ((527/625:ℝ)*x-1489/2500)]
  have hupp : 0≤(2609/5000:ℝ)-(1489/2500)*(8/15+x)+
      (527/1250)*((8/15)^2+(8/15)*x+x^2) := by
    nlinarith [sq_nonneg ((527/625:ℝ)*x-(1489/2500-(527/1250)*(8/15)))]
  have hprod0 := mul_nonneg hx.1 hlow
  have hprod1 := mul_nonneg (sub_nonneg.mpr hx.2) hupp
  have h0 : Explicit.k .smallHigh θ-1673/2500=
      x*((2609/5000)-(1489/2500)*x+(527/1250)*x^2) := by
    dsimp [Explicit.k,L,x]; ring
  have h1 : (7104683/8437500:ℝ)-Explicit.k .smallHigh θ=
      (8/15-x)*((2609/5000)-(1489/2500)*(8/15+x)+
        (527/1250)*((8/15)^2+(8/15)*x+x^2)) := by
    dsimp [Explicit.k,L,x]; ring
  exact ⟨by linarith,by linarith⟩

lemma coefficients (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (Scalar.left f) (Scalar.right f)) (hz : z∈Icc 0 θ) :
    Explicit.k f θ∈Icc (1/2:ℝ) (17/20) ∧
    0<Explicit.l f θ ∧ 0<Explicit.m f θ ∧ Explicit.k f θ≤Explicit.l f θ := by
  cases f <;> simp only [Scalar.left,Scalar.right,frameCap] at hθ
  · refine ⟨⟨?_,?_⟩,by norm_num [Explicit.l],?_,?_⟩
    all_goals dsimp [Explicit.k,Explicit.l,Explicit.m]; linarith [hθ.1,hθ.2]
  · have hb := NonnegativeTotals.Explicit.base_bounds .triangle (Blocks.small_high_domain hθ)
    have el : Explicit.l .smallHigh θ=NonnegativeTotals.Explicit.l .triangle (θ-1/6) 0 := by
      simp only [Explicit.l,NonnegativeTotals.Explicit.l,L]; ring
    have em : Explicit.m .smallHigh θ=NonnegativeTotals.Explicit.c .triangle (θ-1/6) 0 := by
      simp only [Explicit.m,NonnegativeTotals.Explicit.c,L]; ring
    exact ⟨small_high_k hθ,by rw [el]; exact hb.l_positive,by rw [em]; exact hb.c_positive,
      (Blocks.small_high_pairs hθ hz 1).2.1⟩
  · have hr := FarLow.coefficient_ranges hθ hz
    exact ⟨by norm_num [Explicit.k],by linarith [hr.2.1.1],
      by linarith [hr.2.2.1.1],by rw [hr.1]; linarith [hr.2.1.1]⟩
  · have hr := NegativeEHPositiveTD.Explicit.far_high_ranges hθ
    have ek : Explicit.k .farHigh θ=NegativeEHPositiveTD.Explicit.k .far .high θ := rfl
    have el : Explicit.l .farHigh θ=NegativeEHPositiveTD.Explicit.l .far .high θ := rfl
    have em : Explicit.m .farHigh θ=NegativeEHPositiveTD.Explicit.c .far .high θ := rfl
    rw [ek,el,em]
    exact ⟨⟨by linarith [hr.1.1],by linarith [hr.1.2]⟩,
      by linarith [hr.2.1.1],by linarith [hr.2.2.1.1],
      by linarith [hr.1.2,hr.2.1.1]⟩

lemma far_k (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (Scalar.left f) (Scalar.right f)) (hf : far f=true) :
    Explicit.k f θ∈Icc (3/5:ℝ) (4/5) := by
  cases f <;> simp only [Scalar.left,Scalar.right,frameCap] at hθ
  · simp [far] at hf
  · simp [far] at hf
  · norm_num [Explicit.k]
  · have hr := (NegativeEHPositiveTD.Explicit.far_high_ranges hθ).1
    have ek : Explicit.k .farHigh θ=NegativeEHPositiveTD.Explicit.k .far .high θ := rfl
    rw [ek]
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
end
end
end
