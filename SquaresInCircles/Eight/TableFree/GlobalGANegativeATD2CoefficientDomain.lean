module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2OriginalStress

/-!
# Coefficient-pair domains after the original negative-A secant weight

Uncompiled transcription of equations (12)--(14) in the scalar companion.
The ordered H/G/B pairs, including either possible secant assignment,
satisfy the coefficient hypotheses of the proved concentration lemmas.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Explicit
open Candidate Secondary
open Certificate (Family)

def angleCut (atG : Bool) : ℝ := if atG then 1/4 else 19/50

theorem angle_domain (atG : Bool) {s : ℝ} (hs : s∈Icc 0 (angleCut atG)) :
    s∈Icc 0 (19/50:ℝ) ∧ s∈Icc 0 frameCap := by
  cases atG <;> dsimp [angleCut,frameCap] at hs ⊢ <;>
    exact ⟨⟨hs.1,by linarith [hs.2]⟩,⟨hs.1,by linarith [hs.2]⟩⟩

theorem family_basic_domain (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    k f z∈Icc (1/2:ℝ) (17/20:ℝ) ∧
      c f z∈Icc (k f z) 2 ∧ 1<l f z ∧ k f z<l f z ∧
      (11/20)*l f z<k f z ∧ (77/100)*l f z<m f z ∧ m f z<(71/50)*l f z := by
  cases f
  · obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := low_ranges hz
    have hkl := (low_ratio hz).1
    have hm := low_tilted hz
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
      by linarith,by linarith,hkl,by linarith [hm.1],hm.2⟩
  · obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi,hkc,hkl⟩ := high_ranges hz
    have hkr := high_ratio_lower hz
    have hm := high_tilted hz
    exact ⟨⟨by linarith,by linarith⟩,⟨hkc.le,by linarith⟩,
      by linarith,hkl,by linarith,hm.1,by linarith [hm.2.1]⟩

theorem secant_bounds (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) :
    l f z≤secant (l f z) s ∧ secant (l f z) s<2*k f z ∧
      secant (l f z) s<2*m f z := by
  have hr := family_basic_domain f hz
  have hl : 0<l f z := by linarith [hr.2.2.1]
  have hcos := AB_cut_cosine (angle_domain atG hs).1
  have hc : 0<Real.cos s := by linarith
  have hp : l f z≤secant (l f z) s := by
    apply (le_div_iff₀ hc).2
    nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one s) hl.le]
  have hK₁ := mul_lt_mul_of_pos_right hr.2.2.2.2.1 hc
  have hK₂ := mul_lt_mul_of_pos_left hcos
    (show 0<(11/20)*l f z by positivity)
  have hM₁ := mul_lt_mul_of_pos_right hr.2.2.2.2.2.1 hc
  have hM₂ := mul_lt_mul_of_pos_left hcos
    (show 0<(77/100)*l f z by positivity)
  refine ⟨hp,?_,?_⟩
  · apply (div_lt_iff₀ hc).2
    nlinarith
  · apply (div_lt_iff₀ hc).2
    nlinarith

theorem family_coefficient_domain (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) :
    k f z∈Icc (1/2:ℝ) (17/20:ℝ) ∧
    lambdaG atG (l f z) s∈Icc (k f z) (2*k f z) ∧
    0<lambdaB atG (l f z) s ∧ c f z∈Icc (k f z) 2 ∧
    (lambdaB atG (l f z) s≤2*m f z ∧ m f z≤2*lambdaB atG (l f z) s) := by
  have hr := family_basic_domain f hz
  obtain ⟨hp,hpk,hpm⟩ := secant_bounds f atG hz hs
  have hl : 0<l f z := by linarith [hr.2.2.1]
  have hupper : m f z<2*l f z := by linarith [hr.2.2.2.2.2.2]
  cases atG <;> simp only [lambdaG,lambdaB,↓reduceIte]
  · exact ⟨hr.1,⟨hr.2.2.2.1.le,by linarith⟩,hl.trans_le hp,hr.2.1,
      hpm.le,by linarith⟩
  · exact ⟨hr.1,⟨hr.2.2.2.1.le.trans hp,hpk.le⟩,hl,hr.2.1,
      by linarith, hupper.le⟩

theorem ordered_pair_domain (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (i : Fin 4) :
    0<Source.pWeights atG (k f z) (l f z) (m f z) s i ∧
      Source.pWeights atG (k f z) (l f z) (m f z) s i≤
        Source.qWeights atG (k f z) (l f z) (m f z) s i ∧
      Source.qWeights atG (k f z) (l f z) (m f z) s i≤
        2*Source.pWeights atG (k f z) (l f z) (m f z) s i := by
  obtain ⟨hk,hG,hB,_,hm⟩ := family_coefficient_domain f atG hz hs
  exact Source.coefficient_domain hk hG hB (family_positive f hz).2.2.2 hm i

theorem minmax_ratio {a b r : ℝ} (hab : r*a<b) (hba : r*b<a) :
    r*max a b<min a b := by
  rcases le_total a b with hh | hh
  · simpa [max_eq_right hh,min_eq_left hh] using hba
  · simpa [max_eq_left hh,min_eq_right hh] using hab

theorem high_GA_pair_bounds {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) (i : Fin 4) :
    (51/80)*Source.qWeights true (k .high z) (l .high z) (m .high z) s i<
      Source.pWeights true (k .high z) (l .high z) (m .high z) s i ∧
    1≤Source.qWeights true (k .high z) (l .high z) (m .high z) s i ∧
    Source.qWeights true (k .high z) (l .high z) (m .high z) s i<11/10 := by
  obtain ⟨hklo,hkhi,hllo,hlhi,_,_,_,_⟩ := high_ranges hz
  have hkr := high_ratio_lower hz
  have hmr := high_tilted hz
  have hcos := GA_cut_cosine hs
  have hc : 0<Real.cos s := by linarith
  have hl : 0<l .high z := by linarith
  have hsec := (secant_bounds .high true hz hs).1
  have hsecHi : secant (l .high z) s<11/10 := by
    apply (div_lt_iff₀ hc).2
    nlinarith
  have hG : (51/80)*secant (l .high z) s<k .high z := by
    have hp₁ := mul_lt_mul_of_pos_right hkr hc
    have hp₂ := mul_lt_mul_of_pos_left hcos (show 0<(659/1000)*l .high z by positivity)
    dsimp [secant]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hc).2
    nlinarith
  have hB := minmax_ratio
    (show (51/80)*l .high z<m .high z by linarith [hmr.1])
    (show (51/80)*m .high z<l .high z by nlinarith [hmr.2.1])
  have hmaxLo : 1≤max (l .high z) (m .high z) :=
    (by linarith : (1:ℝ)≤l .high z).trans (le_max_left _ _)
  have hmaxHi : max (l .high z) (m .high z)<11/10 := by
    apply max_lt
    · linarith
    · nlinarith [hmr.2.1]
  fin_cases i
  · simp [Source.pWeights,Source.qWeights]
    linarith
  · simpa [Source.pWeights,Source.qWeights,lambdaG] using
      ⟨hG,(by linarith : (1:ℝ)≤secant (l .high z) s),hsecHi⟩
  · simpa [Source.pWeights,Source.qWeights,lambdaB] using ⟨hB,hmaxLo,hmaxHi⟩
  · simp [Source.pWeights,Source.qWeights]
    linarith

theorem high_AB_pair_bounds {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) (i : Fin 4) :
    (13/20)*Source.qWeights false (k .high z) (l .high z) (m .high z) s i<
      Source.pWeights false (k .high z) (l .high z) (m .high z) s i ∧
    1≤Source.qWeights false (k .high z) (l .high z) (m .high z) s i ∧
    Source.qWeights false (k .high z) (l .high z) (m .high z) s i<23/20 := by
  obtain ⟨hklo,hkhi,hllo,hlhi,_,_,_,_⟩ := high_ranges hz
  have hkr := high_ratio_lower hz
  have hmr := high_tilted hz
  have hcos := AB_cut_cosine hs
  have hc : 0<Real.cos s := by linarith
  have hl : 0<l .high z := by linarith
  have hsec := (secant_bounds .high false hz hs).1
  have hsecHi : secant (l .high z) s<23/20 := by
    apply (div_lt_iff₀ hc).2
    nlinarith
  have hB₁ : (13/20)*secant (l .high z) s<m .high z := by
    have hp₁ := mul_lt_mul_of_pos_right hmr.1 hc
    have hp₂ := mul_lt_mul_of_pos_left hcos (show 0<(77/100)*l .high z by positivity)
    dsimp [secant]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hc).2
    nlinarith
  have hB₂ : (13/20)*m .high z<secant (l .high z) s := by
    nlinarith [hmr.2.1]
  have hB := minmax_ratio hB₁ hB₂
  have hmaxLo : 1≤max (secant (l .high z) s) (m .high z) :=
    (by linarith : (1:ℝ)≤secant (l .high z) s).trans (le_max_left _ _)
  have hmaxHi : max (secant (l .high z) s) (m .high z)<23/20 := by
    apply max_lt hsecHi
    nlinarith [hmr.2.1]
  fin_cases i
  · simp [Source.pWeights,Source.qWeights]
    linarith
  · simp [Source.pWeights,Source.qWeights,lambdaG]
    exact ⟨by linarith,by linarith,by linarith⟩
  · simpa [Source.pWeights,Source.qWeights,lambdaB] using ⟨hB,hmaxLo,hmaxHi⟩
  · simp [Source.pWeights,Source.qWeights]
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Explicit
