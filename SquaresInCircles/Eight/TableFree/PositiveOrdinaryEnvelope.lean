module

public import SquaresInCircles.Eight.TableFree.PositiveOrdinaryParameters
public import SquaresInCircles.Eight.TableFree.OrdinaryPositiveEnvelope

/-!
# The complete ordinary angular lower bound with no negative primary removed

Uncompiled source draft. Both signs are concentrated only in an analytic
minorant of the original sum. Correlated same-block saturation and the
two exact coefficient regimes cover every resulting endpoint. This file
then applies the result to the four blocks of the original seven angles.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.PositiveOrdinaryEnvelope
open Candidate PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryAngleConcentration CorrelatedSameBlock
open OrdinaryPositiveEnvelope OrdinaryNegativeEnvelope OrdinaryNegativeSlope
open VaryingBComparison PositiveStressCoefficients PositiveOrdinaryParameters
open ActualOrdinaryBlocks

def ps (n l t : ℝ) : Fin 4 → ℝ := ![n,l,l,min 1 t]
def qs (b t : ℝ) : Fin 4 → ℝ := ![1,k,b,max 1 t]

theorem block_coefficients {d l n b t : ℝ} (h : Bounds d l n b t)
    (C : SignedCycle) (ab bt td : Fin 4) (i : Fin 4) :
    (blocks C ab bt td n k l b t i).p=ps n l t i ∧
    (blocks C ab bt td n k l b t i).q=qs b t i := by
  have hlb : l≤b := h.ell_upper.le.trans h.B_lower
  fin_cases i <;>
    simp [blocks,Block.p,Block.q,ps,qs,min_eq_left h.H_upper,max_eq_right h.H_upper,
      min_eq_left h.ell_upper.le,max_eq_right h.ell_upper.le,min_eq_left hlb,max_eq_right hlb]

theorem domains {d l n b t : ℝ} (h : Bounds d l n b t) (i : Fin 4) :
    0<ps n l t i ∧ ps n l t i≤qs b t i ∧ qs b t i≤2*ps n l t i ∧
    ratio d*qs b t i≤ps n l t i ∧ k≤qs b t i ∧ qs b t i≤2069/2000 := by
  have hk : k=(863/1000 : ℝ) := rfl
  have hr0 : 117/200≤ratio d := by dsimp [ratio]; linarith [h.angle.1]
  have hr1 : ratio d≤1527/2000 := by dsimp [ratio]; linarith [h.angle.2]
  have hDlo : k≤min 1 t := le_min (by norm_num [k]) h.D_lower
  have hDhi : max 1 t≤2069/2000 := max_le (by norm_num) h.D_upper
  have hDq0 : 0≤max 1 t := (by norm_num : (0:ℝ)≤1).trans (le_max_left 1 t)
  have hDcorr : ratio d*max 1 t≤min 1 t := by
    have hp := mul_le_mul hr1 hDhi hDq0 (by norm_num : (0:ℝ)≤1527/2000)
    norm_num [k] at hDlo
    nlinarith
  have hAcorr : ratio d*k≤l :=
    (mul_le_mul_of_nonneg_left h.B_lower (by linarith)).trans h.correlated
  have hB0 : 0≤b := by linarith [h.B_lower]
  have hBtwice : b≤2*l := by
    have hp := mul_le_mul_of_nonneg_right hr0 hB0
    nlinarith [h.correlated]
  have hAtwice : k≤2*l := by norm_num [k]; linarith [h.ell_lower]
  have hDtwice : max 1 t≤2*min 1 t := by
    norm_num [k] at hDlo
    linarith
  fin_cases i
  · simp only [ps,qs,Matrix.cons_val_zero]
    norm_num [k] at *
    exact ⟨by linarith [h.H_lower],h.H_upper,by linarith [h.H_lower],
      by linarith [h.H_lower],by norm_num,by norm_num⟩
  · simpa [ps,qs] using And.intro (by linarith [h.ell_lower] : 0<l)
      ⟨h.ell_upper.le,hAtwice,hAcorr,le_rfl,by norm_num [k]⟩
  · simpa [ps,qs] using And.intro (by linarith [h.ell_lower] : 0<l)
      ⟨h.ell_upper.le.trans h.B_lower,hBtwice,h.correlated,h.B_lower,h.B_upper⟩
  · simpa [ps,qs] using And.intro (by norm_num [k] at hDlo; linarith : 0<min 1 t)
      ⟨min_le_max,hDtwice,hDcorr,hDlo.trans min_le_max,hDhi⟩

theorem high_domains {d l n b t : ℝ} (h : Bounds d l n b t) (hd : 3/10≤d)
    (i : Fin 4) : (2/3)*qs b t i≤ps n l t i := by
  have hk : k=(863/1000 : ℝ) := rfl
  have hH : (2/3 : ℝ)≤n := by linarith [h.H_lower]
  have hA : (2/3)*k≤l :=
    (mul_le_mul_of_nonneg_left h.B_lower (by norm_num)).trans (h.high hd)
  have hDlo : k≤min 1 t := le_min (by norm_num [k]) h.D_lower
  have hDhi : max 1 t≤2069/2000 := max_le (by norm_num) h.D_upper
  have hD : (2/3)*max 1 t≤min 1 t := by norm_num [k] at hDlo; linarith
  fin_cases i
  · simpa [ps,qs] using hH
  · simpa [ps,qs] using hA
  · simpa [ps,qs] using h.high hd
  · simpa [ps,qs] using hD

theorem low_domains {d l n b t : ℝ} (h : Bounds d l n b t) (hd : d≤3/10)
    (i : Fin 4) : lP d≤ps n l t i ∧ qs b t i≤1 := by
  have hl := h.low hd
  have hlk : lP d≤k := hl.2.2.1.trans h.ell_upper.le
  have hDlo : k≤min 1 t := le_min (by norm_num [k]) h.D_lower
  fin_cases i
  · simpa [ps,qs] using And.intro (hlk.trans h.H_lower) le_rfl
  · simpa [ps,qs] using And.intro hl.2.2.1 (by norm_num [k] : k≤1)
  · simpa [ps,qs] using And.intro hl.2.2.1 hl.1
  · simpa [ps,qs] using And.intro (hlk.trans hDlo) (max_le le_rfl hl.2.1)

theorem single_negative_lower {d l n b t w : ℝ} (h : Bounds d l n b t)
    (hw : w∈Icc 0 d) (i : Fin 4) :
    V (Real.sqrt qCap) l k w≤V (Real.sqrt qCap) (ps n l t i) (qs b t i) w := by
  have hw' : w∈Icc 0 frameCap := ⟨hw.1,hw.2.trans h.angle.2⟩
  have hlhalf : k/2≤l := by norm_num [k]; linarith [h.ell_lower]
  have hchainH := near_equal_chain (by norm_num [k] : (43/50 : ℝ)≤k)
    h.H_lower h.H_upper hlhalf h.ell_upper.le hw'
  have hH := hchainH.1.trans (hchainH.2.1.trans hchainH.2.2)
  have hB := V_larger_coefficient (by linarith [h.ell_lower]) h.ell_upper.le
    h.B_lower h.correlated h.angle hw
  have hD : V (Real.sqrt qCap) l k w≤
      V (Real.sqrt qCap) (min 1 t) (max 1 t) w := by
    by_cases ht : t≤1
    · have hc := near_equal_chain (by norm_num [k] : (43/50 : ℝ)≤k)
        h.D_lower ht hlhalf h.ell_upper.le hw'
      simpa [min_eq_right ht,max_eq_left ht] using hc.1.trans (hc.2.1.trans hc.2.2)
    · have ht1 : 1≤t := (lt_of_not_ge ht).le
      have hc := near_equal_chain (by norm_num [k] : (43/50 : ℝ)≤k)
        (by norm_num [k] : k≤1) le_rfl hlhalf h.ell_upper.le hw'
      have hlarge := V_larger_coefficient (l := 1) (k := 1) (q := t)
        (by norm_num) le_rfl ht1
        (by dsimp [ratio,frameCap]; nlinarith [h.D_upper])
        (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl) hw'
      simpa [min_eq_left ht1,max_eq_right ht1] using
        (hc.1.trans (hc.2.1.trans hc.2.2)).trans hlarge
  fin_cases i
  · simpa [ps,qs] using hH
  · simp [ps,qs]
  · simpa [ps,qs] using hB
  · simpa [ps,qs] using hD

theorem target_zero_slope {l : ℝ} (hl : 1/2<l) (hlu : l≤1631/2500) :
    Vd (Real.sqrt qCap) l k 0<26/25 := by
  have hl0 : 0<l := by linarith
  have hk0 : 0<k := by norm_num [k]
  have hN := pairNorm_pos (p := l) (q := k) (t := 0) hl0 hk0 (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p := l) (q := k) (t := 0) hl0 hk0 (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_zero,mul_zero,add_zero] at hN2
  have hl2 := pow_le_pow_left₀ hl0.le hlu 2
  have hQ := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hnum : (Real.sqrt qCap*l*k)^2=qCap*l^2*k^2 := by rw [mul_pow,mul_pow,hQ]; ring
  have hstrict : qCap*l^2*k^2<(26/25 : ℝ)^2*(l^2+k^2) := by
    norm_num [qCap,k] at *
    nlinarith
  have hcross : Real.sqrt qCap*l*k<(26/25)*pairNorm l k 0 := by
    nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) hl0.le) hk0.le]
  have hdiv := (div_lt_iff₀ hN).2 hcross
  simpa [Vd,mixedNDerivative,normD1,pairProduct] using hdiv

theorem target_low_upper {d l n b t : ℝ} (h : Bounds d l n b t) (hd : d≤3/10) :
    V (Real.sqrt qCap) l k d≤(26/25)*d := by
  have hp : 0<l := by linarith [h.ell_lower]
  have hqp : k≤2*l := by norm_num [k]; linarith [h.ell_lower]
  exact (V_tangent_zero hp h.ell_upper.le hqp h.angle).trans
    (mul_le_mul_of_nonneg_right (target_zero_slope h.ell_lower (h.low hd).2.2.2).le h.angle.1)

theorem low_reserve {d : ℝ} (hd : d∈Icc 0 (3/10)) :
    0<(87/100)*lP d-(26/25)*d-(109/200)*(frameCap-d) := by
  have hd2 := pow_le_pow_left₀ hd.1 hd.2 2
  dsimp [lP,frameCap]
  nlinarith

theorem separated_saturated_lower {d l n b t : ℝ} (h : Bounds d l n b t)
    (i j : Fin 4) :
    V (Real.sqrt qCap) l k d≤
      U (Real.sqrt qCap) (ps n l t i) (qs b t i) (frameCap-d)+
        V (Real.sqrt qCap) (ps n l t j) (qs b t j) frameCap := by
  have hi := domains h i
  have hj := domains h j
  have ha : frameCap-d∈Icc 0 frameCap :=
    ⟨by linarith [h.angle.2],by linarith [h.angle.1]⟩
  have hU := U_lower (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hi.1 hi.2.1 hi.2.2.1 ha
  by_cases hd : d≤3/10
  · have hloi := low_domains h hd i
    have hloj := low_domains h hd j
    have hV := V_endpoint_lower sqrt_cap_lower hj.1 hj.2.1 hj.2.2.1
    have hqmul := mul_le_mul_of_nonneg_right hloi.2 ha.1
    have hpl := mul_le_mul_of_nonneg_left hloj.1 (by norm_num : (0:ℝ)≤87/100)
    have htarget := target_low_upper h hd
    have hreserve := low_reserve ⟨h.angle.1,hd⟩
    nlinarith
  · have hlarge : 3/10≤d := (lt_of_not_ge hd).le
    have hV := V_growth hj.1 hj.2.1 (high_domains h hlarge j) h.angle
      (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl) h.angle.2
    have hsingle := single_negative_lower h ⟨h.angle.1,le_rfl⟩ j
    have hqi := mul_le_mul_of_nonneg_right hi.2.2.2.2.2 ha.1
    have hqj := mul_le_mul_of_nonneg_right hj.2.2.2.2.1 ha.1
    have hreserve : 0≤((2/3)*k-(109/200)*(2069/2000))*
        (frameCap-d) := mul_nonneg (by norm_num [k]) ha.1
    nlinarith

theorem mixed_sum_lower {d l n b t : ℝ} (h : Bounds d l n b t)
    (P N : Fin 4 → ℝ) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d) (hbalance : (∑ i,N i)=d+∑ i,P i) :
    V (Real.sqrt qCap) l k d≤
      ∑ i,mixedBlock (Real.sqrt qCap) (ps n l t i) (qs b t i) (P i) (N i) := by
  obtain ⟨i,j,hconc⟩ := ordinary_concentration (Real.sqrt qCap) (ps n l t) (qs b t) P N
    (Real.sqrt_nonneg qCap) (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (fun i => (domains h i).1) (fun i => (domains h i).2.1)
    (fun i => (domains h i).2.2.1) hP hN h.angle hbudget hbalance
  apply le_trans _ hconc
  apply le_min
  · exact single_negative_lower h ⟨h.angle.1,le_rfl⟩ j
  · by_cases hij : i=j
    · simp only [if_pos hij]
      have hi := domains h i
      have hsame := negative_surplus (R := Real.sqrt qCap)
        (hi.1.trans_le hi.2.1).le hi.2.2.2.1 h.angle
        (show (0:ℝ)∈Icc 0 d from ⟨le_rfl,h.angle.1⟩)
      have he : mixedBlock (Real.sqrt qCap) (ps n l t i) (qs b t i) (frameCap-d) frameCap=
          M (Real.sqrt qCap) (ps n l t i) (qs b t i) d := by
        dsimp [mixedBlock,M]
        rw [show frameCap-d-frameCap= -d by ring]
      simp only [sub_zero,he] at hsame
      exact (single_negative_lower h ⟨h.angle.1,le_rfl⟩ i).trans hsame
    · simpa only [if_neg hij] using separated_saturated_lower h i j

/-- The completed lower bound is applied to the actual four block sums,
with the exact original seven-angle budget. -/
theorem increment_lower {C : SignedCycle} {ab bt td : Fin 4} {l n b t : ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hBT : bt=3 → 0≤delta C.theta B)
    (hTD : td=2 → 0≤delta C.theta T)
    (h : Bounds (removed C bt td) l n b t) :
    V (Real.sqrt qCap) l k (removed C bt td)≤
      ∑ i,(blocks C ab bt td n k l b t i).increment (Real.sqrt qCap) := by
  let Bs := blocks C ab bt td n k l b t
  have hb := block_budgets hab hbt htd n k l b t hvar hG hBT hTD
  have hP : ∀ i,0≤(Bs i).P := fun i => (Bs i).P_nonneg
  have hN : ∀ i,0≤(Bs i).N := fun i => (Bs i).N_nonneg
  have hsumP : (∑ i,(Bs i).P)≤frameCap := by linarith [hb.1.1,hb.2.1]
  have hsumN : (∑ i,(Bs i).N)≤frameCap := by linarith [hb.2.1,hb.2.2]
  have hPi (i : Fin 4) : (Bs i).P≤frameCap :=
    (Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ i)).trans hsumP
  have hNi (i : Fin 4) : (Bs i).N≤frameCap :=
    (Finset.single_le_sum (fun j _ => hN j) (Finset.mem_univ i)).trans hsumN
  have hsum := mixed_sum_lower h (fun i => (Bs i).P) (fun i => (Bs i).N)
    hP hN hb.2.1 hb.2.2
  refine hsum.trans (Finset.sum_le_sum fun i _ => ?_)
  have hc := block_coefficients h C ab bt td i
  have hminor := (Bs i).minorant (Real.sqrt qCap)
    (by rw [hc.1]; exact (domains h i).1.le) (hPi i) (hNi i)
  simpa only [hc.1,hc.2] using hminor

end SquaresInCircles.Eight.TableFree.PositiveOrdinaryEnvelope
