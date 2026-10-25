module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2PolynomialData
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: whole-domain ranges of the negative-DE weight families

The ranges are polynomial bounds in the angle, of degree at most four. The low tilted ratio and
the two high ratios are cubics with positive Bernstein coefficients on their intervals; the high
l/c lower bounds add the square of `t - 19/20`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD
open Candidate Secondary PositiveAngularEnvelope

namespace Explicit

theorem low_ranges {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (2/3:ℝ)<k .low θ ∧ k .low θ<757/1000 ∧
      1<l .low θ ∧ l .low θ<1352/1000 ∧
      (10389/10000:ℝ)≤c .low θ ∧ c .low θ<1864/1000 ∧
      l .low θ≤c .low θ ∧ l .low θ<2*k .low θ := by
  let x : ℝ := 1/6-θ
  have hx : x∈Icc (0:ℝ) (1/6) := ⟨by dsimp [x]; linarith [hθ.2],by dsimp [x]; linarith [hθ.1]⟩
  have hx2 : x^2≤x/6 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hk : k .low θ=6708/10000-(3/20)*x+4*x^2 := by dsimp [k,L,x]; ring
  have hl : l .low θ=10073/10000+(17/10)*x+(11/5)*x^2 := by dsimp [l,L,x]; ring
  have hc : c .low θ=10389/10000+(69/20)*x+9*x^2 := by dsimp [c,L,x]; ring
  have hratio : 2*k .low θ-l .low θ=72935/450000+θ/15+(29/5)*θ^2 := by
    dsimp [k,l,L]
    ring
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith [sq_nonneg (x-3/160)]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hθ.1,sq_nonneg θ]

theorem high_parameter {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) : t θ∈Icc (0:ℝ) 1 := by
  dsimp [t,L]
  exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

theorem high_ranges {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (670158/1000000:ℝ)≤k .high θ ∧ k .high θ≤800408/1000000 ∧
      (863/1000:ℝ)<l .high θ ∧ l .high θ≤1005069/1000000 ∧
      (862/1000:ℝ)<c .high θ ∧ c .high θ≤1021248/1000000 ∧
      l .high θ<(3/2)*k .high θ ∧ c .high θ≤1073/1000-(3/10)*θ := by
  have ht := high_parameter hθ
  have hpow (n : ℕ) : 0≤(t θ)^n ∧ (t θ)^n≤1 :=
    ⟨pow_nonneg ht.1 n,by simpa using pow_le_pow_left₀ ht.1 ht.2 n⟩
  have h2 : (t θ)^2≤t θ := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have h3 : (t θ)^3≤(t θ)^2 := by nlinarith [mul_nonneg (sq_nonneg (t θ)) (sub_nonneg.mpr ht.2)]
  have hu := sub_nonneg.2 ht.2
  have hs := mul_nonneg (sq_nonneg (t θ-19/20)) ht.1
  have hl : (863/1000:ℝ)<1005069/1000000-146411/1000000*t θ-
      157739/1000000*(t θ)^2+162815/1000000*(t θ)^3 := by
    linarith [pow_nonneg hu 2,pow_nonneg hu 3]
  have hc : (862/1000:ℝ)<1021248/1000000-168873/1000000*t θ-
      165381/1000000*(t θ)^2+175944/1000000*(t θ)^3 := by
    linarith [pow_nonneg hu 2,pow_nonneg hu 3]
  have hratio : (3/2)*k .high θ-l .high θ=
      168/1000000+(316988/1000000)*t θ+(167498/1000000)*(t θ)^2-
        (149276/1000000)*(t θ)^3+(15/10000)*(t θ)^4 := by dsimp [k,l]; ring
  have hcorrelation : 1073/1000-(3/10)*θ-c .high θ=
      (1752/1000000)*(1-t θ)+(62/1000000)*t θ+
        t θ*(1-t θ)*(10563/1000000+(175944/1000000)*t θ) := by
    dsimp [c,t,L]
    ring
  have hlast := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    (show 0≤10563/1000000+(175944/1000000)*t θ by linarith [ht.1])
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [k]; nlinarith [(hpow 1).1,(hpow 2).1,(hpow 3).1,(hpow 4).1]
  · dsimp [k]; nlinarith [(hpow 1).2,(hpow 2).2,(hpow 3).2,(hpow 4).2]
  · dsimp [l]; linarith
  · dsimp [l]; nlinarith [ht.1]
  · dsimp [c]; linarith
  · dsimp [c]; nlinarith [ht.1]
  · nlinarith [ht.1,(hpow 2).1,(hpow 4).1]
  · nlinarith [ht.1,ht.2]

theorem low_tilted {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) :
    c .low θ≤ m .low θ z ∧ m .low θ z<(69/50)*l .low θ := by
  have hr := low_ranges hθ
  have hc : 0<c .low θ := by linarith [hr.2.2.2.2.1]
  have hz' : z∈Icc 0 PositiveTD.Explicit.split := ⟨hz.1,hz.2.trans hθ.2⟩
  have hf := PositiveTD.Explicit.low_factor hz'
  have hlow := mul_le_mul_of_nonneg_left hf.1 hc.le
  have hupper := mul_le_mul_of_nonneg_left
    (show Real.cos z+eta*Real.sin z≤1+eta*θ by
      have he : PositiveTD.eta=eta := rfl
      rw [he] at hf
      dsimp [eta] at *
      linarith [hz.2,hf.2]) hc.le
  have hcert : (11909/16000000:ℝ)≤69/50*l .low θ-c .low θ*(1+293/1000*θ) := by
    have h2 : 0≤1/6-θ := sub_nonneg.2 hθ.2
    simp only [l,c,L]
    linarith [pow_nonneg hθ.1 3,mul_nonneg (pow_nonneg hθ.1 2) h2,
      mul_nonneg hθ.1 (pow_nonneg h2 2),pow_nonneg h2 3]
  refine ⟨by simpa [m,eta,PositiveTD.eta] using hlow,?_⟩
  dsimp [m,eta]
  dsimp [eta] at hupper
  nlinarith

theorem high_ratios {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (9/10)*l .high θ<c .high θ ∧ c .high θ<(1017/1000)*l .high θ := by
  have ht := high_parameter hθ
  have hu := sub_nonneg.2 ht.2
  simp only [l,c]
  constructor <;> linarith [pow_nonneg ht.1 3,mul_nonneg (pow_nonneg ht.1 2) hu,
    mul_nonneg ht.1 (pow_nonneg hu 2),pow_nonneg hu 3]

theorem high_tilted {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) :
    k .high θ< m .high θ z ∧ m .high θ z<(1061/1000)*l .high θ ∧
      m .high θ z<(1066/1000:ℝ) ∧ (2/3)*l .high θ< m .high θ z := by
  have hr := high_ranges hθ
  have hrat := high_ratios hθ
  have hc : 0<c .high θ := by linarith [hr.2.2.2.2.1]
  have hl : 0<l .high θ := by linarith [hr.2.2.1]
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by norm_num [frameCap]; linarith [hz.2,hθ.2]⟩
  have hlow₀ := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_lower hz') hc
  have hupper := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_upper z) hc
  have hlow : (19/20)*c .high θ< m .high θ z := by
    simpa [m,eta,PositiveTD.eta,mul_comm] using hlow₀
  change m .high θ z<c .high θ*(1043/1000) at hupper
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith [hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,
      hr.2.2.2.2.2.1,hrat.1,hrat.2]

theorem family_positive (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (left f) (right f)) (hz : z∈Icc 0 θ) :
    0<k f θ ∧ 0<l f θ ∧ 0<c f θ ∧ 0< m f θ z := by
  cases f
  · have hr := low_ranges hθ
    have hm := low_tilted hθ hz
    exact ⟨by linarith [hr.1],by linarith [hr.2.2.1],
      by linarith [hr.2.2.2.2.1],by linarith [hr.2.2.2.2.1,hm.1]⟩
  · have hr := high_ranges hθ
    have hm := high_tilted hθ hz
    exact ⟨by linarith [hr.1],by linarith [hr.2.2.1],
      by linarith [hr.2.2.2.2.1],by linarith [hr.1,hm.1]⟩

theorem high_pairs {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (i : Fin 3) : 0<p .high θ z i ∧ p .high θ z i≤q .high θ z i ∧
      (2/3)*q .high θ z i<p .high θ z i ∧
      (863/1000:ℝ)<q .high θ z i ∧ q .high θ z i<(1066/1000:ℝ) := by
  have hr := high_ranges hθ
  have hm := high_tilted hθ hz
  have hk : 0<k .high θ := by linarith [hr.1]
  have hl : 0<l .high θ := by linarith [hr.2.2.1]
  have hm0 : 0< m .high θ z := hk.trans hm.1
  have hkl : k .high θ<l .high θ := by linarith [hr.2.1,hr.2.2.1]
  fin_cases i
  · show 0<k .high θ ∧ k .high θ≤1 ∧ (2/3)*1<k .high θ ∧ (863/1000:ℝ)<1 ∧ (1:ℝ)<1066/1000
    exact ⟨hk,by linarith [hr.2.1],by linarith [hr.1],by norm_num,by norm_num⟩
  · show 0<k .high θ ∧ k .high θ≤l .high θ ∧ (2/3)*l .high θ<k .high θ ∧
      (863/1000:ℝ)<l .high θ ∧ l .high θ<1066/1000
    exact ⟨hk,hkl.le,by linarith [hr.2.2.2.2.2.2.1],hr.2.2.1,
      by linarith [hr.2.2.2.1]⟩
  · show 0 < min (l .high θ) (m .high θ z) ∧
      min (l .high θ) (m .high θ z) ≤ max (l .high θ) (m .high θ z) ∧
      (2/3)*max (l .high θ) (m .high θ z) < min (l .high θ) (m .high θ z) ∧
      (863/1000:ℝ) < max (l .high θ) (m .high θ z) ∧
      max (l .high θ) (m .high θ z) < 1066/1000
    refine ⟨lt_min hl hm0,min_le_max,?_,?_,?_⟩
    · rcases le_total (l .high θ) (m .high θ z) with hh | hh
      · rw [min_eq_left hh,max_eq_right hh]
        nlinarith [hm.2.1]
      · rw [min_eq_right hh,max_eq_left hh]
        exact hm.2.2.2
    · exact hr.2.2.1.trans_le (le_max_left _ _)
    · exact max_lt (by linarith [hr.2.2.2.1]) hm.2.2.1

theorem high_q_ratio {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (i j : Fin 3) : q .high θ z i<(29/25)*q .high θ z j := by
  have hi := high_pairs hθ hz i
  have hj := high_pairs hθ hz j
  have hr := high_ranges hθ
  have hm := high_tilted hθ hz
  have hq (n : Fin 3) : q .high θ z n=1 ∨ q .high θ z n=l .high θ ∨
      q .high θ z n=max (l .high θ) (m .high θ z) := by
    fin_cases n
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  by_cases hl : 1≤l .high θ
  · have hj1 : 1≤q .high θ z j := by
      rcases hq j with h|h|h <;> rw [h]
      · exact hl
      · exact hl.trans (le_max_left _ _)
    nlinarith [hi.2.2.2.2]
  · by_cases hm1 : m .high θ z≤1
    · have hi1 : q .high θ z i≤1 := by
        rcases hq i with h|h|h <;> rw [h]
        · exact (lt_of_not_ge hl).le
        · exact max_le (lt_of_not_ge hl).le hm1
      nlinarith [hj.2.2.2.1]
    · have hiM : q .high θ z i≤ m .high θ z := by
        rcases hq i with h|h|h <;> rw [h]
        · exact (lt_of_not_ge hm1).le
        · linarith [lt_of_not_ge hl,lt_of_not_ge hm1]
        · exact max_le (by linarith [lt_of_not_ge hl,lt_of_not_ge hm1]) le_rfl
      have hjL : l .high θ≤q .high θ z j := by
        rcases hq j with h|h|h <;> rw [h]
        · exact (lt_of_not_ge hl).le
        · exact le_max_left _ _
      nlinarith [hm.2.1,hr.2.2.1]

/-- The late interval used by the shared secant-coordinate shape proof.
The cubic upper estimate for l and the affine c/theta correlation are
kept before taking the maximum in the original B pair. -/
theorem high_late_q_le_one {θ z : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (_hz : z∈Icc 0 θ)
    (hlate : (11/20:ℝ)≤θ) (i : Fin 3) : q .high θ z i≤1 := by
  have ht := high_parameter hθ
  have htlate : (23/32:ℝ)≤t θ := by dsimp [t,L]; linarith
  have h2 : (t θ)^2≤t θ := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have h3 : (t θ)^3≤(t θ)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (t θ)) (sub_nonneg.mpr ht.2)]
  have hl : l .high θ≤1005069/1000000-(141335/1000000)*t θ := by
    dsimp [l]
    nlinarith
  have hl1 : l .high θ≤1 := by linarith
  have hr := high_ranges hθ
  have hc : c .high θ≤227/250 := by linarith [hr.2.2.2.2.2.2.2]
  have hcpos : 0<c .high θ := by linarith [hr.2.2.2.2.1]
  have hm := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_upper z) hcpos
  have hm1 : m .high θ z≤1 := by
    change c .high θ*(Real.cos z+PositiveTD.eta*Real.sin z)<
      c .high θ*(1043/1000) at hm
    dsimp [m,eta,PositiveTD.eta]
    dsimp [PositiveTD.eta] at hm
    nlinarith
  fin_cases i <;> simp only [q]
  · exact le_rfl
  · exact hl1
  · exact max_le hl1 hm1

end Explicit
end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD
