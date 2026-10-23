module

public import SquaresInCircles.Eight.TableFree.SolePositiveTOrdinaryData

/-!
# Complete signed ordinary-angle envelope with a positive T primary

Uncompiled source. Continuous concentration applies to the original
positive and negative ordinary budgets. Every separated and same-anchor
endpoint lies above a pure charge; no ordering of the ordinary angles
or strict owner selection is assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SolePositiveTEnvelope
open SoleTScalarModel SolePositiveTCoefficients SolePositiveTOrdinaryData
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity SolePositiveTGrowth

theorem growth_pays (s : ScalarCase) {R t z : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    (109/200)*(SolePositiveTCoefficients.cap s.family:ℝ)*(frameCap-t)≤
      pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) frameCap-
        pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t := by
  rw [pure_eq s ht hz,pure_eq s ht hz]
  have hp := small_pos s ht hz i
  have hpq := small_le_large s t z i
  have hq := hp.trans_le hpq
  have hnu := (nu_between s t z i).2
  have hr := ratio_lower s ht hz i
  change ratio s.family t i*large s t z i≤small s t z i at hr
  have hlo := larger_lower s ht hz i
  change (largeFloor s.family:ℝ)≤large s t z i at hlo
  have hsmall := smaller_lower s ht hz i
  change (smallFloor s.family:ℝ)≤small s t z i at hsmall
  have ht' := angle ht
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hlen : 0≤frameCap-t := by linarith [ht'.2]
  cases hf : s.family
  · have hratio : (117/200)*large s t z i≤small s t z i := by
      simp [ratio,hf] at hr
      nlinarith [mul_nonneg ht'.1 hq.le]
    have htg : t∈Icc 0 (1/5:ℝ) := by simpa [domain,hf,left,right] using ht
    have hfloor : 431/500≤large s t z i := by simpa [largeFloor,hf] using hlo
    have hg := low_growth hR hQL hp hpq hratio hfloor hnu htg
    have hc : (109/200)*(SolePositiveTCoefficients.cap s.family:ℝ)≤121/200 := by norm_num [cap,hf]
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (13/20)*large s t z i≤small s t z i := by simpa [ratio,hf] using hr
    have htg : t∈Icc 0 (7/20:ℝ) := by
      have hu := ht.2
      norm_num [domain,hf,right] at hu
      exact ⟨ht'.1,hu⟩
    have hfloor : 923/1000≤large s t z i := by simpa [largeFloor,hf] using hlo
    have hg := middle_growth hR hQL hp hpq hratio hfloor hnu htg
    have hc : (109/200)*(SolePositiveTCoefficients.cap s.family:ℝ)≤7/10 := by norm_num [cap,hf]
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (18/25)*large s t z i≤small s t z i := by simpa [ratio,hf] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hc : (109/200)*(SolePositiveTCoefficients.cap s.family:ℝ)≤small s t z i := by
      norm_num [smallFloor,hf] at hsmall
      norm_num [cap,hf]
      linarith
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have htg : t∈Icc 0 (7/20:ℝ) := by simpa [domain,hf,left,right] using ht
    by_cases hA : i=1
    · subst i
      obtain ⟨hs,hl,hn,hrA⟩ := DE_A_data s hf ht hz
      have hd := de_A s hf ht hz
      have hg := DE_A_growth hR hQL hQU hd.1
        (by rw [← hs,← hl]; exact hpq) hrA ht'
      rw [hs,hl,hn]
      have hc : (109/200)*(SolePositiveTCoefficients.cap s.family:ℝ)≤18/25 := by norm_num [cap,hf]
      exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
    · by_cases hB : i=2
      · subst i
        have hratio : (5/8+27/100*t)*large s t z 2≤small s t z 2 := by
          simpa [ratio,hf] using hr
        have hg := SolePositiveTDEChord.growth hR hQL hp hpq hratio
          (DE_B_large s hf ht hz) hnu htg
        have hc : (109/200)*(SolePositiveTCoefficients.cap s.family:ℝ)≤7/10 := by norm_num [cap,hf]
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
      · have hi : i=0 ∨ i=3 := by fin_cases i <;> simp_all
        have hratio : (18/25)*large s t z i≤small s t z i := by
          simpa [ratio,hf,hA,hB] using hr
        have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
        have hsmall := DE_outer_small s hf ht hz i hi
        have hc : (109/200)*(SolePositiveTCoefficients.cap s.family:ℝ)≤small s t z i := by
          norm_num [cap,hf]
          linarith
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (18/25)*large s t z i≤small s t z i := by simpa [ratio,hf] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hc : (109/200)*(SolePositiveTCoefficients.cap s.family:ℝ)≤small s t z i := by
      norm_num [smallFloor,hf] at hsmall
      norm_num [cap,hf]
      linarith
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg

theorem same_block (s : ScalarCase) {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) (hi : single s i=false) :
    pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t≤
      M R (small s t z i) (large s t z i) t := by
  simp only [pure,hi,if_false]
  have hp := small_pos s ht hz i
  have hq := hp.trans_le (small_le_large s t z i)
  have hr := ratio_lower s ht hz i
  change ratio s.family t i*large s t z i≤small s t z i at hr
  have ht' := angle ht
  cases hf : s.family
  · apply SolePositiveTSameBlock.EH_low hq.le _ ht'
    simpa [ratio,hf] using hr
  · apply SolePositiveTSameBlock.EH_middle hq.le _ ht'
    simpa [ratio,hf] using hr
  · apply M_ge_V hp.le hq.le _ ht'
    simp [ratio,hf] at hr
    linarith
  · have hindices : i=0 ∨ i=2 := by
      fin_cases i <;> simp_all [single,hf,isDE]
    rcases hindices with rfl | rfl
    · apply M_ge_V hp.le hq.le _ ht'
      simp [ratio,hf] at hr
      linarith
    · apply SolePositiveTSameBlock.DE_low_B hq.le
        (by simp [ratio,hf] at hr; nlinarith [mul_nonneg ht'.1 hq.le])
      simpa [domain,hf,left,right] using ht
  · apply M_ge_V hp.le hq.le _ ht'
    simp [ratio,hf] at hr
    linarith

theorem ordinary_lower (s : ScalarCase) (P N : Fin 4 → ℝ) {R t z L : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t+∑i,P i)
    (hsingle : ∀ i,single s i=true → P i=0 ∨ N i=0)
    (hpure : ∀ i,L≤pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t) :
    L≤∑i,F (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) (P i) (N i) := by
  have hhalf (i : Fin 4) : large s t z i≤2*small s t z i := half_ratio s ht hz i
  apply SingleAngleConcentration.lower_from_endpoints (single s) R
    (small s t z) (large s t z) (actualNu s t z) P N hR hQU
    (small_pos s ht hz) (small_le_large s t z) hhalf
    (fun i => (nu_between s t z i).1) hP hN (angle ht) hbudget hbalance hsingle hpure
  · intro i hi
    exact (hpure i).trans (same_block s ht hz i hi)
  · intro i j _
    have hlen : 0≤frameCap-t := by linarith [(angle ht).2]
    have hU := OrdinaryPositiveEnvelope.U_lower hR hQU (small_pos s ht hz i)
      (small_le_large s t z i) (hhalf i)
      (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [(angle ht).1]⟩)
    have hV := growth_pays s hR hQL hQU ht hz j
    have hcap := pair_upper s ht hz i
    change large s t z i≤(SolePositiveTCoefficients.cap s.family:ℝ) at hcap
    have hpay := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcap (by norm_num : (0:ℝ)≤109/200)) hlen
    linarith [hpure j]

end SquaresInCircles.Eight.TableFree.SolePositiveTEnvelope
