module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3Tilt

/-!
# Whole-domain coefficient bounds for the two original BT3 stresses

Uncompiled equations (18), (25), and (26). The high polynomial family
is the previously proved DE family with its base coefficient renamed m.
Only the total-dependent tilt is new. Every larger ordinary coefficient
is kept separate, so the spread bounds also cover l below one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Explicit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

structure HighBounds (θ : ℝ) : Prop where
  k_lower : (670158/1000000:ℝ)≤k .high θ
  k_upper : k .high θ≤800408/1000000
  l_lower : (863/1000:ℝ)<l .high θ
  l_upper : l .high θ≤1005069/1000000
  m_lower : (862/1000:ℝ)< m .high θ
  m_upper : m .high θ≤1021248/1000000
  l_ratio : l .high θ<(3/2)*k .high θ
  m_l_lower : (9/10)*l .high θ< m .high θ
  m_l_upper : m .high θ<(1017/1000)*l .high θ

theorem high_bounds {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) : HighBounds θ := by
  have hh := NegativeDEPositiveTD.Explicit.high_ranges hθ
  have hr := NegativeDEPositiveTD.Explicit.high_ratios hθ
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,
    hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.1,hr.1,hr.2⟩

theorem low_bounds {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    k .low θ∈Icc (2933/5000:ℝ) (1673/2500) ∧
      m .low θ∈Icc (10163/10000:ℝ) (5821/5000) := by
  dsimp [k,m,PositiveBT3.lowK,PositiveBT3.lowM,PositiveBT3.Cmax]
  exact ⟨⟨by linarith [hθ.1],by linarith [hθ.2]⟩,
    ⟨by linarith [hθ.2],by linarith [hθ.1]⟩⟩

theorem low_c {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) :
    m .low θ≤c .low θ z ∧ c .low θ z≤5821/5000 := by
  have hm := (low_bounds hθ).2
  have hz' : z∈Icc (0:ℝ) (1/6) := ⟨hz.1,hz.2.trans hθ.2⟩
  have hf := PositiveTD.Explicit.low_factor hz'
  have hm0 : 0 ≤ m .low θ := by linarith [hm.1]
  have hlo := mul_le_mul_of_nonneg_left hf.1 hm0
  have hfactor : Real.cos z+eta .low θ*Real.sin z≤1+(293/1000)*θ := by
    dsimp [eta]
    linarith [Real.cos_le_one z,Real.sin_le hz.1,hz.2]
  have hhi := mul_le_mul_of_nonneg_left hfactor hm0
  have hmdef : m .low θ = 5821/5000-(4437/5000)*θ := by
    simp [m,PositiveBT3.lowM,PositiveBT3.Cmax]
  constructor
  · simpa [c,eta,PositiveTD.eta] using hlo
  · change m .low θ*(Real.cos z+eta .low θ*Real.sin z)≤5821/5000
    rw [hmdef] at hhi ⊢
    nlinarith [hhi,hθ.1,sq_nonneg θ]

theorem high_c {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) :
    m .high θ≤c .high θ z ∧ c .high θ z<(213/200)*m .high θ := by
  have hm := (high_bounds hθ).m_lower
  have hp : 0< m .high θ := by linarith
  have hlo := mul_le_mul_of_nonneg_left (high_factor_lower hθ hz) hp.le
  have hhi := mul_lt_mul_of_pos_left (high_factor_upper (z:=z) hθ) hp
  exact ⟨by simpa [c] using hlo,by simpa [c,mul_comm] using hhi⟩

theorem high_pairs {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    0<p .high θ i ∧ p .high θ i≤q .high θ i ∧ (2/3)*q .high θ i<p .high θ i := by
  have hb := high_bounds hθ
  fin_cases i
  · change 0<k .high θ ∧ k .high θ≤1 ∧ (2/3)*1<k .high θ
    exact ⟨by linarith [hb.k_lower],by linarith [hb.k_upper],by linarith [hb.k_lower]⟩
  · change 0<k .high θ ∧ k .high θ≤l .high θ ∧ (2/3)*l .high θ<k .high θ
    exact ⟨by linarith [hb.k_lower],by linarith [hb.k_upper,hb.l_lower],by linarith [hb.l_ratio]⟩
  · change 0 < min (l .high θ) (m .high θ) ∧
      min (l .high θ) (m .high θ) ≤ max (l .high θ) (m .high θ) ∧
      (2/3)*max (l .high θ) (m .high θ) < min (l .high θ) (m .high θ)
    rcases le_total (l .high θ) (m .high θ) with h|h
    · rw [min_eq_left h,max_eq_right h]
      exact ⟨by linarith [hb.l_lower],h,by linarith [hb.m_l_upper,hb.l_lower]⟩
    · rw [min_eq_right h,max_eq_left h]
      exact ⟨by linarith [hb.m_lower],h,by linarith [hb.m_l_lower,hb.l_lower]⟩

theorem high_q_bounds {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    (431/500:ℝ)<q .high θ i ∧ q .high θ i<(533/500:ℝ) := by
  have hb := high_bounds hθ
  fin_cases i
  · change (431/500:ℝ)<1 ∧ (1:ℝ)<533/500
    norm_num
  · change (431/500:ℝ)<l .high θ ∧ l .high θ<(533/500:ℝ)
    exact ⟨by linarith [hb.l_lower],by linarith [hb.l_upper]⟩
  · change (431/500:ℝ) < max (l .high θ) (m .high θ) ∧ max (l .high θ) (m .high θ) < (533/500:ℝ)
    exact ⟨by linarith [hb.l_lower,le_max_left (l .high θ) (m .high θ)],
      max_lt (by linarith [hb.l_upper]) (by linarith [hb.m_upper])⟩

theorem high_spread {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i j : Fin 3) :
    q .high θ i<(29/25)*q .high θ j := by
  have hb := high_bounds hθ
  have hl : 0<l .high θ := by linarith [hb.l_lower]
  have hscaled : q .high θ i<(29/25)*l .high θ := by
    fin_cases i
    · norm_num [q]
      linarith [hb.l_lower]
    · change l .high θ<(29/25)*l .high θ
      linarith
    · change max (l .high θ) (m .high θ)<(29/25)*l .high θ
      exact max_lt (by linarith) (by linarith [hb.m_l_upper])
  fin_cases j
  · change q .high θ i<(29/25)*1
    linarith [(high_q_bounds hθ i).2]
  · exact hscaled
  · exact hscaled.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))

theorem high_c_ratio {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (j : Fin 3) : c .high θ z<(109/100)*q .high θ j := by
  have hb := high_bounds hθ
  have hc := (high_c hθ hz).2
  fin_cases j
  · change c .high θ z<(109/100)*1
    linarith [hb.m_upper]
  · change c .high θ z<(109/100)*l .high θ
    linarith [hb.m_l_upper,hb.l_lower]
  · change c .high θ z<(109/100)*max (l .high θ) (m .high θ)
    have hh := le_max_right (l .high θ) (m .high θ)
    linarith [hb.m_lower]

theorem family_pairs (f : Family) {θ : ℝ} (hθ : θ∈Icc (left f) (right f)) (i : Fin 3) :
    0<p f θ i ∧ p f θ i≤q f θ i ∧ q f θ i≤2*p f θ i := by
  cases f
  · have hb := low_bounds hθ
    have hk1 := hb.1.1
    have hk2 := hb.1.2
    have hm1 := hb.2.1
    have hm2 := hb.2.2
    fin_cases i
    · change 0<k .low θ ∧ k .low θ≤1 ∧ 1≤2*k .low θ
      exact ⟨by linarith,by linarith,by linarith⟩
    · change 0<k .low θ ∧ k .low θ≤1 ∧ 1≤2*k .low θ
      exact ⟨by linarith,by linarith,by linarith⟩
    · change 0 < min 1 (m .low θ) ∧ min 1 (m .low θ) ≤ max 1 (m .low θ) ∧
        max 1 (m .low θ) ≤ 2*min 1 (m .low θ)
      rw [min_eq_left (show 1 ≤ m .low θ by linarith [hb.2.1]),
        max_eq_right (show 1 ≤ m .low θ by linarith [hb.2.1])]
      exact ⟨by norm_num,by linarith [hb.2.1],by linarith [hb.2.2]⟩
  · have hh := high_pairs hθ i
    exact ⟨hh.1,hh.2.1,by linarith [hh.1,hh.2.2]⟩

theorem source_coefficients (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (left f) (right f)) (hz : z∈Icc 0 θ) :
    k f θ∈Icc (1/2:ℝ) (17/20) ∧ k f θ≤l f θ ∧
      0<l f θ ∧ 0< m f θ ∧
      c f θ z∈Icc SecantD.PositiveEndpoint.d SecantD.cUpper ∧ k f θ≤c f θ z := by
  cases f
  · have hb := low_bounds hθ
    have hc := low_c hθ hz
    refine ⟨⟨by linarith [hb.1.1],by linarith [hb.1.2]⟩,
      by dsimp [l]; linarith [hb.1.2],by norm_num [l],by linarith [hb.2.1],?_,?_⟩
    · norm_num [SecantD.PositiveEndpoint.d,SecantD.cUpper]
      exact ⟨by linarith [hb.2.1,hc.1],by linarith [hc.2]⟩
    · linarith [hb.1.2,hb.2.1,hc.1]
  · have hb := high_bounds hθ
    have hc := high_c hθ hz
    refine ⟨⟨by linarith [hb.k_lower],by linarith [hb.k_upper]⟩,
      by linarith [hb.k_upper,hb.l_lower],by linarith [hb.l_lower],
      by linarith [hb.m_lower],?_,?_⟩
    · norm_num [SecantD.PositiveEndpoint.d,SecantD.cUpper]
      exact ⟨by linarith [hb.m_lower,hc.1],by linarith [hb.m_upper,hc.2]⟩
    · linarith [hb.k_upper,hb.m_lower,hc.1]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Explicit
