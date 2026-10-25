module

public import SquaresInCircles.Eight.TableFree.ActualOrdinaryBlocks
public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeEnvelope
public import SquaresInCircles.Eight.TableFree.OrdinaryPositiveEnvelope

/-!
# The original one-angle force after a negative E secant

Uncompiled source. The full-circle increment suffices on the actual
shortened negative-angle budget. If e is the removed E angle and s the
total removed negative mass, then e≤s and the remaining negative angle
is at most h-s. This correlation proves the required coefficient
comparison without assigning a new angle or a new support point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NegativeEOneAngle
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open OrdinaryPositiveEnvelope PositiveStressCoefficients VaryingBComparison ActualOrdinaryBlocks

def gamma (s : ℝ) : ℝ := (109/200)*(2069/2000)/Real.cos s

def increment (c e t : ℝ) : ℝ :=
  c*psi t-Real.sqrt qCap*
    (pairNorm c (1/Real.cos e) t-pairNorm c (1/Real.cos e) 0)

theorem secant_bounds {e : ℝ} (he : e∈Icc 0 frameCap) :
    1≤1/Real.cos e ∧ 1/Real.cos e<327/250 := by
  have ht := transport_trig he
  have hc : 0<Real.cos e := by linarith [ht.1]
  exact ⟨(one_le_div hc).2 ht.2.1,(div_lt_iff₀ hc).2 (by linarith [ht.1])⟩

theorem shortened_ratio {s e : ℝ} (hs : s∈Icc 0 frameCap) (he : e∈Icc 0 s) :
    ratio (frameCap-s)*(1/Real.cos e)≤k := by
  have he' : e∈Icc 0 frameCap := ⟨he.1,he.2.trans hs.2⟩
  have hc : 0<Real.cos e := by linarith [(transport_trig he').1]
  have he2 := pow_le_pow_left₀ he.1 he.2 2
  have hs2 : s^2≤frameCap*s := by nlinarith [hs.1,hs.2]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := e)
  have hmul := mul_le_mul_of_nonneg_left hcos (show 0≤k by norm_num [k])
  have hpoly : ratio (frameCap-s)≤k*(1-e^2/2) := by
    dsimp [ratio,k,frameCap] at *
    nlinarith
  rw [mul_one_div]
  exact (div_le_iff₀ hc).2 (hpoly.trans hmul)

theorem modified_negative {c e s t : ℝ}
    (hc : k≤c ∧ c≤2069/2000) (hs : s∈Icc 0 frameCap)
    (he : e∈Icc 0 s) (ht : t∈Icc 0 (frameCap-s)) :
    V (Real.sqrt qCap) k 1 t≤
      V (Real.sqrt qCap) (min c (1/Real.cos e)) (max c (1/Real.cos e)) t := by
  have he' : e∈Icc 0 frameCap := ⟨he.1,he.2.trans hs.2⟩
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by linarith [ht.2,hs.1]⟩
  have hsec := secant_bounds he'
  have hc0 : 0<c := by norm_num [k] at hc; linarith
  by_cases hc1 : c≤1
  · have horder : c≤1/Real.cos e := hc1.trans hsec.1
    rw [min_eq_left horder,max_eq_right horder]
    have hsmall := V_monotone_smaller (Real.sqrt_nonneg qCap) (by norm_num : (0:ℝ)<1) ht'
      (show k∈Icc (1/2) 1 by norm_num [k])
      (show c∈Icc (1/2) 1 by constructor; norm_num [k] at hc; linarith; exact hc1) hc.1
    have hlarge := V_larger_coefficient hc0 hc1 hsec.1
      ((shortened_ratio hs he).trans hc.1)
      (show frameCap-s∈Icc 0 frameCap from ⟨by linarith [hs.2],by linarith [hs.1]⟩) ht
    exact hsmall.trans hlarge
  · let p := min c (1/Real.cos e)
    let q := max c (1/Real.cos e)
    have hp : 1≤p := le_min (le_of_not_ge hc1) hsec.1
    have hpq : p≤q := min_le_max
    have hq : q≤327/250 := max_le (by linarith [hc.2]) hsec.2.le
    have hq0 : 0<q := by linarith
    have hfirst := V_monotone_smaller (Real.sqrt_nonneg qCap) (by norm_num : (0:ℝ)<1) ht'
      (show k∈Icc (1/2) 1 by norm_num [k]) (by norm_num : (1:ℝ)∈Icc (1/2) 1)
      (by norm_num [k] : k≤1)
    have hratio : ratio frameCap*q≤1 := by
      dsimp [ratio,frameCap]
      linarith
    have hsecond := V_larger_coefficient (l := (1:ℝ)) (k := 1) (q := q)
      (by norm_num) le_rfl (hp.trans hpq) hratio
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht'
    have hthird := V_monotone_smaller (Real.sqrt_nonneg qCap) hq0 ht'
      (show (1:ℝ)∈Icc (q/2) q by constructor <;> linarith)
      (show p∈Icc (q/2) q by constructor; linarith; exact hpq) hp
    exact hfirst.trans (hsecond.trans hthird)

theorem modified_coefficient {c e s : ℝ} (hc : c≤2069/2000)
    (hs : s∈Icc 0 frameCap) (he : e∈Icc 0 s) :
    max c (1/Real.cos e)≤(2069/2000)/Real.cos s := by
  have he' : e∈Icc 0 frameCap := ⟨he.1,he.2.trans hs.2⟩
  have hcs : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hce : 0<Real.cos e := by linarith [(transport_trig he').1]
  have hs2 : s≤7/10 := hs.2
  have hmono : Real.cos s≤Real.cos e := Real.cos_le_cos_of_nonneg_of_le_pi he.1
    (by linarith [Real.pi_gt_three]) he.2
  apply max_le
  · exact hc.trans ((le_div_iff₀ hcs).2 (by nlinarith [Real.cos_le_one s]))
  · apply (div_le_div_iff₀ hce hcs).2
    nlinarith

theorem gamma_bound {s : ℝ} (hs : s∈Icc 0 frameCap) :
    0≤gamma s ∧ gamma s<369/500 := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  refine ⟨by dsimp [gamma]; positivity,?_⟩
  have hsec := (secant_bounds hs).2
  dsimp [gamma]
  rw [show (109/200:ℝ)*(2069/2000)/Real.cos s=(109/200)*(2069/2000)*(1/Real.cos s) by ring]
  linarith

/-- The one remaining physical angle keeps its original sign. The
two-variable expression is an analytic lower bound, ready for the same
finite concavity argument as the unmodified ordinary blocks. -/
theorem actual_minorant {c e s t : ℝ}
    (hc : k≤c ∧ c≤2069/2000) (hs : s∈Icc 0 frameCap)
    (he : e∈Icc 0 s) (ht : |t|≤frameCap)
    (hbudget : negativePart t≤frameCap-s) :
    -gamma s*positivePart t+V (Real.sqrt qCap) k 1 (negativePart t)≤ increment c e t := by
  let B : Block := ⟨c,1/Real.cos e,t,0⟩
  have hsec := secant_bounds (show e∈Icc 0 frameCap from ⟨he.1,he.2.trans hs.2⟩)
  have hcp : 0<c := by norm_num [k] at hc; linarith
  have hp : 0<B.p := lt_min hcp (by linarith [hsec.1])
  have hpq : B.p≤B.q := min_le_max
  have hqp : B.q≤2*B.p := by
    have hl : k≤B.p := le_min hc.1 (by norm_num [k]; linarith [hsec.1])
    have hu : B.q≤327/250 := max_le (by linarith [hc.2]) hsec.2.le
    norm_num [k] at hl
    linarith
  have hP : B.P≤frameCap := by
    simpa [B,Block.P,positivePart] using max_le ((le_abs_self t).trans ht) (by norm_num [frameCap])
  have hN : B.N≤frameCap := by
    simpa [B,Block.N,negativePart] using max_le ((neg_le_abs t).trans ht) (by norm_num [frameCap])
  have hm := B.minorant (Real.sqrt qCap) hp.le hP hN
  have heq : B.increment (Real.sqrt qCap)=increment c e t := by
    simp [B,Block.increment,increment,psi]
  rw [heq] at hm
  by_cases hsign : 0≤t
  · have hpos : positivePart t=t := max_eq_left hsign
    have hneg : negativePart t=0 := max_eq_right (neg_nonpos.mpr hsign)
    have ht' : t∈Icc 0 frameCap := ⟨hsign,(le_abs_self t).trans ht⟩
    have hu := U_lower (Real.sqrt_nonneg qCap)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hp hpq hqp ht'
    have hcq : B.q≤(2069/2000)/Real.cos s := modified_coefficient hc.2 hs he
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcq (by norm_num : (0:ℝ)≤109/200)) hsign
    simp only [B,Block.P,Block.N,positivePart_zero,negativePart_zero,add_zero,hpos,hneg,
      mixedBlock_zero_right] at hm
    simp only [B] at hu hmul
    rw [hpos,hneg,V_zero,add_zero]
    dsimp only [gamma]
    rw [show -((109/200:ℝ)*(2069/2000)/Real.cos s)*t=-((109/200)*((2069/2000)/Real.cos s)*t) by ring]
    linarith
  · have ht0 : t≤0 := (lt_of_not_ge hsign).le
    have hpos : positivePart t=0 := max_eq_right ht0
    have hneg : negativePart t= -t := max_eq_left (neg_nonneg.mpr ht0)
    have hv := modified_negative hc hs he
      (show -t∈Icc 0 (frameCap-s) from ⟨neg_nonneg.mpr ht0,by simpa [hneg] using hbudget⟩)
    simp only [B,Block.P,Block.N,positivePart_zero,negativePart_zero,add_zero,hpos,hneg,
      mixedBlock_zero_left] at hm
    rw [hpos,hneg,mul_zero,zero_add]
    exact hv.trans hm

end SquaresInCircles.Eight.TableFree.NegativeEOneAngle
