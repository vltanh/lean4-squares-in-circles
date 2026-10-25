module

public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTOrdinaryData

/-!
# The complete outside-strip ordinary envelope at arbitrary EH contact

Uncompiled source. The full original signed domain is concentrated
before any scalar coefficient is enlarged. H and TD B are the only
possible mixed blocks. Their same-block alternatives and every
separated alternative dominate their respective pure charge at t.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTEnvelope
open ExceptionalPositiveTScalarModel ExceptionalPositiveTCoefficients
open ExceptionalPositiveTOrdinaryData ExceptionalPositiveTGrowth
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity

theorem growth_pays (s : ScalarCase) {R t z : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    (109/200)*(cap s.family:ℝ)*(frameCap-t)≤
      pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) frameCap-
        pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t := by
  rw [pure_eq,pure_eq]
  have hp := small_pos s ht hz i
  have hpq := small_le_large s t z i
  have hq := hp.trans_le hpq
  have hnu := (nu_between s t z i).2
  have hr := ratio_lower s ht hz i
  change ratio s.family t i*large s t z i≤ small s t z i at hr
  have hlo := larger_lower s ht hz i
  change (largeFloor s.family:ℝ)≤large s t z i at hlo
  have hsmall := smaller_lower s ht hz i
  change (smallFloor s.family i:ℝ)≤ small s t z i at hsmall
  have ht' := angle ht
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hlen : 0≤frameCap-t := by linarith [ht'.2]
  cases hf : s.family
  · have hratio : (117/200)*large s t z i≤ small s t z i := by
      simp [ratio,hf] at hr
      split_ifs at hr <;> nlinarith [mul_nonneg ht'.1 hq.le]
    have htg : t∈Icc 0 (9/50:ℝ) := by
      simp [domain,hf,left,right] at ht
      exact ⟨ht'.1,by linarith [ht.2]⟩
    have hg := low_growth hR hQL hQU hp hpq hratio
      (by simpa [largeFloor,hf] using hlo) hnu htg
    have hc : (109/200)*(cap s.family:ℝ)≤(431/500)*(7/10) := by norm_num [cap,hf]
    rw [hf] at hc
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (117/200)*large s t z i≤ small s t z i := by
      simp [ratio,hf] at hr
      split_ifs at hr <;> nlinarith [mul_nonneg ht'.1 hq.le]
    have htg : t∈Icc 0 (9/50:ℝ) := by
      simp [domain,hf,left,right] at ht
      exact ⟨ht'.1,ht.2⟩
    have hg := low_growth hR hQL hQU hp hpq hratio
      (by simpa [largeFloor,hf] using hlo) hnu htg
    have hc : (109/200)*(cap s.family:ℝ)≤(431/500)*(7/10) := by norm_num [cap,hf]
    rw [hf] at hc
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · by_cases hA : i=1
    · subst i
      obtain ⟨hs,hl,hn,hrA⟩ := middle_A_data s hf ht hz
      have hd := middle_A s hf ht hz
      have hg := middle_A_growth hR hQL hQU hd.1
        (by rw [← hs,← hl]; exact hpq) hrA ht'
      rw [hs,hl,hn]
      have hc : (109/200)*(cap s.family:ℝ)≤4/5 := by norm_num [cap,hf]
      rw [hf] at hc
      exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
    · by_cases hB : i=2
      · subst i
        have hratio : (2/3)*large s t z 2≤ small s t z 2 := by simpa [ratio,hf] using hr
        have hg := balanced_growth hR hQL hp hpq hratio hnu ht' hh ht'.2
        have hfloor : (911/1000:ℝ)≤large s t z 2 := by simpa [largeFloor,hf] using hlo
        have hc : (109/200)*(cap s.family:ℝ)≤(337/500)*large s t z 2 := by
          norm_num [cap,hf]
          nlinarith
        rw [hf] at hc
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
      · have hi : i=0 ∨ i=3 := by fin_cases i <;> simp_all
        have hratio : (71/100)*large s t z i≤ small s t z i := by
          simpa [ratio,hf,hA,hB] using hr
        have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
        have hfloor : (911/1000:ℝ)≤ small s t z i := by
          simpa [smallFloor,hf,hi] using hsmall
        have hc : (109/200)*(cap s.family:ℝ)≤ small s t z i := by norm_num [cap,hf]; linarith
        rw [hf] at hc
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (71/100)*large s t z i≤ small s t z i := by simpa [ratio,hf] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hfloor : (731/1000:ℝ)≤ small s t z i := by simpa [smallFloor,hf] using hsmall
    have hc : (109/200)*(cap s.family:ℝ)≤ small s t z i := by norm_num [cap,hf]; linarith
    rw [hf] at hc
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg

theorem same_block (s : ScalarCase) {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) (hi : single s i=false) :
    pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t≤
      M R (small s t z i) (large s t z i) t := by
  simp only [SingleAngleConcavity.pure,hi,Bool.false_eq_true,↓reduceIte]
  have hp := small_pos s ht hz i
  have hq := hp.trans_le (small_le_large s t z i)
  have hr := ratio_lower s ht hz i
  change ratio s.family t i*large s t z i≤ small s t z i at hr
  have hindices : i=0 ∨ i=2 := by
    fin_cases i <;> simp_all [single,ExceptionalPositiveTBlocks.single]
  have ht' := angle ht
  rcases hindices with rfl | rfl
  · apply M_ge_V hp.le hq.le _ (angle ht)
    cases hf : s.family <;> simp [ratio,hf] at hr <;> nlinarith
  · cases hf : s.family
    · apply low_same_block hq.le (by simpa [ratio,hf] using hr)
      simp [domain,hf,left,right] at ht
      exact ⟨ht'.1,by linarith [ht.2]⟩
    · apply low_same_block hq.le (by simpa [ratio,hf] using hr)
      simp [domain,hf,left,right] at ht
      exact ⟨by linarith [ht.1],ht.2⟩
    · apply M_ge_V hp.le hq.le _ (angle ht)
      simp [ratio,hf] at hr
      linarith
    · apply M_ge_V hp.le hq.le _ (angle ht)
      simp [ratio,hf] at hr
      nlinarith

theorem original_increment {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {R t z L : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (ha : ∀ i,|Candidate.delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤Candidate.delta C.theta Candidate.G) (hD : 0≤Candidate.delta C.theta Candidate.D)
    (hT : 0≤ExceptionalPositiveTStress.primary C s.td)
    (htotal : Candidate.delta C.theta Candidate.G+Candidate.delta C.theta Candidate.D+ExceptionalPositiveTStress.primary C s.td=t)
    (hpure : ∀ i,L≤pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t) :
    L≤ExceptionalPositiveTBlocks.increment C ab s.td (weights s t z) R := by
  have hhalf (i : Fin 4) : large s t z i≤2*small s t z i := half_ratio s ht hz i
  apply ExceptionalPositiveTBlocks.original_lower s.td (weights s t z) hab hR hQU
    (small_pos s ht hz) hhalf ha hvar hG hD hT htotal hpure
  · intro i hi
    exact (hpure i).trans (same_block s ht hz i hi)
  · intro i j _
    have hlen : 0≤frameCap-t := by linarith [(angle ht).2]
    have hU := OrdinaryPositiveEnvelope.U_lower hR hQU (small_pos s ht hz i)
      (small_le_large s t z i) (hhalf i)
      (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [(angle ht).1]⟩)
    have hV := growth_pays s hR hQL hQU ht hz j
    have hcap := pair_upper s ht hz i
    change large s t z i≤(cap s.family:ℝ) at hcap
    have hpay := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcap (by norm_num : (0:ℝ)≤109/200)) hlen
    have hj := hpure j
    show L≤U R (small s t z i) (large s t z i) (frameCap-t)+
      SingleAngleConcavity.pure (single s j) R (small s t z j) (large s t z j) (actualNu s t z j)
        frameCap
    simp only [frameCap] at hU hV hpay hlen ⊢
    linarith

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTEnvelope
