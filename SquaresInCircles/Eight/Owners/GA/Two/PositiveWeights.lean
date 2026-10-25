module

public import SquaresInCircles.Eight.Owners.GA.Two.PositiveWeightBounds

/-!
# Eight squares: explicit weights are admissible for every split of the fixed total

The coefficients depend on the actual total A/T angle and stay fixed
while that angle is split.  Their ratio bounds hold over the entire
split interval.  The high family also satisfies the balanced envelope
conditions for every ordinary block, without assuming all large
coefficients are at least one.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalGA.TwoPositive

open Candidate Secondary PositiveTD

def highK (t : ℝ) : ℝ := Polynomial.aeval t Certificate.highK
def highL (t : ℝ) : ℝ := Polynomial.aeval t Certificate.highL
def highC (t : ℝ) : ℝ := Polynomial.aeval t Certificate.highC

theorem low_factor_monotone :
    MonotoneOn (fun z : ℝ => Real.cos z+eta*Real.sin z) (Icc 0 (1/6)) := by
  apply monoOn_of_hasDeriv_nonneg (d := fun z => -Real.sin z+eta*Real.cos z)
  · exact (Real.continuous_cos.add (continuous_const.mul Real.continuous_sin)).continuousOn
  · intro z _
    exact (Real.hasDerivAt_cos z).add ((Real.hasDerivAt_sin z).const_mul eta)
  · intro z hz
    have hz' : z∈Icc 0 frameCap := ⟨hz.1.le,by simp only [frameCap]; linarith [hz.2]⟩
    have hc := (transport_trig hz').1
    have hs := Real.sin_le hz.1.le
    simp only [eta]
    linarith [hz.2]

theorem low_split_domain {t z : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) (hz : z∈Icc 0 t) :
    Explicit.lowK t∈Icc (1/2:ℝ) (17/20) ∧
      Explicit.lowL t∈Icc (Explicit.lowK t) (2*Explicit.lowK t) ∧
      Explicit.lowC t∈Icc (Explicit.lowK t) 2 ∧
      (Explicit.lowL t≤2*tilted (Explicit.lowC t) z ∧
        tilted (Explicit.lowC t) z≤2*Explicit.lowL t) ∧
      Explicit.lowC t≤(3/2)*Explicit.lowL t ∧
        tilted (Explicit.lowC t) z≤(3/2)*Explicit.lowL t := by
  have hd := Explicit.low_domain ht
  have hr := Explicit.low_ranges ht
  have hz' : z∈Icc 0 (1/6:ℝ) := ⟨hz.1,hz.2.trans ht.2⟩
  have hc : 0≤Explicit.lowC t := by linarith [hd.1.1,hd.2.2.1.1]
  have hmlo₀ := mul_le_mul_of_nonneg_left (Explicit.low_factor hz').1 hc
  have hmhi := mul_le_mul_of_nonneg_left (low_factor_monotone hz' ht hz.2) hc
  have htotal := (Explicit.low_tilted ht).2
  have hmlo : Explicit.lowC t≤tilted (Explicit.lowC t) z := by
    simpa [tilted] using hmlo₀
  change tilted (Explicit.lowC t) z≤tilted (Explicit.lowC t) t at hmhi
  exact ⟨hd.1,hd.2.1,hd.2.2.1,⟨by linarith [hr.2.2.1,hr.2.2.2.1],
    by linarith [hr.2.2.1]⟩,by linarith,by linarith⟩

theorem high_ranges {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    (669/1000:ℝ)<highK t ∧ highK t<843/1000 ∧
      (89/100:ℝ)<highL t ∧ highL t<5001/5000 ∧
      (89/100:ℝ)<highC t ∧ highC t≤10163/10000 ∧
      (9/10)*highL t<highC t ∧ highC t<(11/10)*highL t :=
  Certificate.high_ranges ht

theorem high_tilted {t z : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) (hz : z∈Icc 0 t) :
    (2/3)*highL t<tilted (highC t) z ∧
      tilted (highC t) z<(3/2)*highL t ∧
      tilted (highC t) z<1061/1000 := by
  have hr := high_ranges ht
  have hc : 0<highC t := by linarith [hr.2.2.2.2.1]
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans ht.2⟩
  have hlow₀ := mul_lt_mul_of_pos_left (Explicit.factor_lower hz') hc
  have hhigh := mul_lt_mul_of_pos_left (Explicit.factor_upper z) hc
  have hlow : (19/20)*highC t<tilted (highC t) z := by
    simpa [tilted,mul_comm] using hlow₀
  change tilted (highC t) z<highC t*(1043/1000) at hhigh
  exact ⟨by linarith [hr.2.2.1,hr.2.2.2.2.2.2.1],
    by linarith [hr.2.2.1,hr.2.2.2.2.2.2.2],by linarith [hr.2.2.2.2.2.1]⟩

theorem high_split_domain {t z : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) (hz : z∈Icc 0 t) :
    highK t∈Icc (1/2:ℝ) (17/20) ∧
      highL t∈Icc (highK t) (2*highK t) ∧
      highC t∈Icc (highK t) 2 ∧
      (highL t≤2*tilted (highC t) z ∧ tilted (highC t) z≤2*highL t) ∧
      (9/10)*highL t≤highC t ∧ highC t≤(11/10)*highL t := by
  have hr := high_ranges ht
  have hm := high_tilted ht hz
  refine ⟨⟨by linarith [hr.1],by linarith [hr.2.1]⟩,
    ⟨by linarith [hr.2.1,hr.2.2.1],by linarith [hr.1,hr.2.2.2.1]⟩,
    ⟨by linarith [hr.2.1,hr.2.2.2.2.1],by linarith [hr.2.2.2.2.2.1]⟩,
    ⟨by linarith [hr.2.2.1,hm.1],by linarith [hr.2.2.1,hm.2.1]⟩,
    hr.2.2.2.2.2.2.1.le,hr.2.2.2.2.2.2.2.le⟩

theorem high_balanced {t z : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) (hz : z∈Icc 0 t) :
    (∀i : Fin 4,2*qWeights (highK t) (highL t) (tilted (highC t) z) i≤
      3*pWeights (highK t) (highL t) (tilted (highC t) z) i) ∧
    (∀i j : Fin 4,5*qWeights (highK t) (highL t) (tilted (highC t) z) i≤
      6*qWeights (highK t) (highL t) (tilted (highC t) z) j) := by
  have hr := high_ranges ht
  have hm := high_tilted ht hz
  have hq (i : Fin 4) :
      (89/100:ℝ)<qWeights (highK t) (highL t) (tilted (highC t) z) i ∧
        qWeights (highK t) (highL t) (tilted (highC t) z) i<1061/1000 := by
    fin_cases i
    · norm_num [qWeights]
    · exact ⟨hr.2.2.1,by simpa [qWeights] using
        (show highL t<1061/1000 by linarith [hr.2.2.2.1])⟩
    · change (89/100:ℝ) < max (highL t) (tilted (highC t) z) ∧
        max (highL t) (tilted (highC t) z)<1061/1000
      exact ⟨hr.2.2.1.trans_le (le_max_left _ _),
        max_lt (by linarith [hr.2.2.2.1]) hm.2.2⟩
    · norm_num [qWeights]
  constructor
  · intro i
    fin_cases i
    · simp [qWeights,pWeights]
      linarith [hr.1]
    · simp [qWeights,pWeights]
      linarith [hr.1,hr.2.2.2.1]
    · change 2*max (highL t) (tilted (highC t) z)≤
        3*min (highL t) (tilted (highC t) z)
      rcases le_total (highL t) (tilted (highC t) z) with hh | hh
      · rw [max_eq_right hh,min_eq_left hh]
        linarith [hm.2.1]
      · rw [max_eq_left hh,min_eq_right hh]
        linarith [hm.1]
    · simp [qWeights,pWeights]
      linarith [hr.1]
  · intro i j
    linarith [(hq i).2,(hq j).1]

end SquaresInCircles.Eight.GlobalGA.TwoPositive
