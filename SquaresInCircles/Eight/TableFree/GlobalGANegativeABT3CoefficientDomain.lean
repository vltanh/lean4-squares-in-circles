module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Endpoints

/-!
# Ordered coefficient domains including the actual A secant

Uncompiled Section 4. The high family retains D as a fourth ordinary
pair. On the low family D uses H's negative envelope and its separate
linear positive cost. Every bound includes the entire actual A cut.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Explicit
open Candidate Secondary
open Certificate (Family)

abbrev GA_cut_cosine := @NegativeAPositiveTD.Explicit.GA_cut_cosine
abbrev AB_cut_cosine := @NegativeAPositiveTD.Explicit.AB_cut_cosine

def p (f : Family) (atG : Bool) (z s : ℝ) : Fin 4→ℝ :=
  pWeights f atG (k f z) (l f z) (m f z) (c f z) s
def q (f : Family) (atG : Bool) (z s : ℝ) : Fin 4→ℝ :=
  qWeights f atG (k f z) (l f z) (m f z) (c f z) s

theorem basic_domain (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    k f z∈Icc (1/2:ℝ) (17/20:ℝ) ∧ (1023/1000:ℝ)<l f z ∧
    (11/20)*l f z<k f z ∧ k f z<(17/20)*l f z ∧
    (4/5)*l f z<m f z ∧ m f z<(113/100)*l f z ∧
    k f z<c f z ∧ c f z<6/5 := by
  cases f
  · obtain ⟨hk,hl,hm₀,hm₁⟩ := low_ranges hz
    obtain ⟨hkl₀,hkl₁,hml₀,hml₁,hkm⟩ := low_ratios hz
    obtain ⟨hc₀,hc₁⟩ := low_rotation hz
    exact ⟨⟨by linarith [hk.1],by linarith [hk.2]⟩,by linarith [hl.1],
      hkl₀,by linarith [hl.1],by linarith [hl.1],hml₁,by linarith [hk.2],hc₁⟩
  · obtain ⟨hk,hl,hm₀,hm₁⟩ := high_ranges hz
    obtain ⟨hkl₀,hkl₁,hml₀,hml₁,hml⟩ := high_ratios hz
    obtain ⟨hc₀,hkc,hc₁⟩ := high_rotation hz
    exact ⟨⟨by linarith [hk.1],by linarith [hk.2]⟩,by linarith [hl.1],
      by linarith [hl.1],by linarith [hl.1],hml₀,by linarith [hl.1],hkc,by linarith⟩

theorem secant_bounds (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) :
    l f z≤secant (l f z) s ∧ secant (l f z) s<2*k f z ∧
      secant (l f z) s<2*m f z := by
  have hb := basic_domain f hz
  have hl : 0<l f z := by linarith [hb.2.1]
  have hcos := AB_cut_cosine (angle_domain atG hs).1
  have hc : 0<Real.cos s := by linarith
  have hw : l f z≤secant (l f z) s := by
    apply (le_div_iff₀ hc).2
    nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one s) hl.le]
  have hk₁ := mul_lt_mul_of_pos_right hb.2.2.1 hc
  have hk₂ := mul_lt_mul_of_pos_left hcos (show 0<(11/20)*l f z by positivity)
  have hm₁ := mul_lt_mul_of_pos_right hb.2.2.2.2.1 hc
  have hm₂ := mul_lt_mul_of_pos_left hcos (show 0<(4/5)*l f z by positivity)
  refine ⟨hw,?_,?_⟩
  · exact (div_lt_iff₀ hc).2 (by nlinarith)
  · exact (div_lt_iff₀ hc).2 (by nlinarith)

theorem ordered_pair_domain (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (i : Fin 4) :
    0<p f atG z s i ∧ p f atG z s i≤q f atG z s i ∧
      q f atG z s i≤2*p f atG z s i := by
  have hb := basic_domain f hz
  have hl : 0<l f z := by linarith [hb.2.1]
  have hm : 0<m f z := by linarith [hb.2.2.2.2.1]
  have hk : 0<k f z := by linarith [hb.1.1]
  obtain ⟨hw,hwk,hwm⟩ := secant_bounds f atG hz hs
  have hkl : k f z<l f z := by linarith [hb.2.2.2.1]
  have hml : m f z<2*l f z := by linarith [hb.2.2.2.2.2.1]
  have hB : 0<lambdaB atG (l f z) s ∧
      lambdaB atG (l f z) s≤2*m f z ∧ m f z≤2*lambdaB atG (l f z) s := by
    cases atG <;> simp only [lambdaB,NegativeAPositiveTD.lambdaB,↓reduceIte]
    · exact ⟨hl.trans_le hw,hwm.le,by linarith⟩
    · exact ⟨hl,by linarith,by linarith⟩
  have hG : 0<k f z ∧ k f z≤lambdaG atG (l f z) s ∧
      lambdaG atG (l f z) s≤2*k f z := by
    cases atG <;> simp only [lambdaG,NegativeAPositiveTD.lambdaG,↓reduceIte]
    · exact ⟨hk,hkl.le,by linarith⟩
    · exact ⟨hk,hkl.le.trans hw,hwk.le⟩
  fin_cases i
  · simpa [p,q,pWeights,qWeights] using And.intro hk
      (And.intro (by linarith [hb.1.2] : k f z≤1) (by linarith [hb.1.1] : 1≤2*k f z))
  · simpa [p,q,pWeights,qWeights] using hG
  · simp only [p,q,pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero]
    rcases le_total (lambdaB atG (l f z) s) (m f z) with hh|hh
    · simpa [min_eq_left hh,max_eq_right hh] using ⟨hB.1,hh,hB.2.2⟩
    · simpa [min_eq_right hh,max_eq_left hh] using ⟨hm,hh,hB.2.1⟩
  · cases f
    · simpa [p,q,pWeights,qWeights] using And.intro hk
        (And.intro (by linarith [hb.1.2] : k .low z≤1) (by linarith [hb.1.1] : 1≤2*k .low z))
    · have hc := high_rotation hz
      simpa [p,q,pWeights,qWeights,min_eq_right hc.2.2.le,max_eq_left hc.2.2.le] using
        And.intro (by linarith [hc.1] : 0<c .high z)
          (And.intro hc.2.2.le (by linarith [hc.1] : 1≤2*c .high z))

theorem low_q_upper (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (i : Fin 4) : q .low atG z s i<5/4 := by
  have hb := low_ranges hz
  have hc := AB_cut_cosine (angle_domain atG hs).1
  have hcos : 0<Real.cos s := by linarith
  have hsec : secant (l .low z) s<5/4 := (div_lt_iff₀ hcos).2 (by nlinarith [hb.2.1.2])
  cases atG <;> fin_cases i <;> simp only [q,qWeights,lambdaG,lambdaB,
    NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,↓reduceIte,
    Matrix.cons_val_succ,Matrix.cons_val_zero] <;>
    first | exact hsec | norm_num | apply max_lt <;> first | exact hsec | linarith [hb.2.1.2,hb.2.2.2]

theorem low_G_ratio (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) : lambdaG atG (l .low z) s<(5/3)*k .low z := by
  have hb := low_ranges hz
  cases atG
  · simp only [lambdaG,NegativeAPositiveTD.lambdaG,↓reduceIte]
    linarith [hb.1.1,hb.2.1.2]
  · have hc := GA_cut_cosine hs
    have hcos : 0<Real.cos s := by linarith
    simp only [lambdaG,NegativeAPositiveTD.lambdaG,↓reduceIte]
    exact (div_lt_iff₀ hcos).2 (by nlinarith [hb.1.1,hb.2.1.2])

theorem low_HB_ratio (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (i : Fin 4) (hi : i=0∨i=2) :
    q .low atG z s i≤(3/2)*p .low atG z s i := by
  have hb := low_ranges hz
  have hsec := (secant_bounds .low atG hz hs).1
  have hc := AB_cut_cosine (angle_domain atG hs).1
  have hcos : 0<Real.cos s := by linarith
  have hw : secant (l .low z) s<(3/2)*m .low z :=
    (div_lt_iff₀ hcos).2 (by nlinarith [hb.2.1.2,hb.2.2.1])
  rcases hi with rfl|rfl
  · simp [p,q,pWeights,qWeights]
    linarith [hb.1.1]
  · cases atG <;> simp only [p,q,pWeights,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,
      ↓reduceIte,Matrix.cons_val_succ,Matrix.cons_val_zero]
    · rcases le_total (secant (l .low z) s) (m .low z) with hh|hh
      · rw [min_eq_left hh,max_eq_right hh]
        linarith [hb.2.1.1,hb.2.2.2]
      · rw [min_eq_right hh,max_eq_left hh]
        exact hw.le
    · rcases le_total (l .low z) (m .low z) with hh|hh
      · rw [min_eq_left hh,max_eq_right hh]
        linarith [hb.2.1.1,hb.2.2.2]
      · rw [min_eq_right hh,max_eq_left hh]
        linarith [hb.2.1.2,hb.2.2.1]

theorem high_GA_pair_bounds {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) (i : Fin 4) :
    (51/80)*q .high true z s i<p .high true z s i ∧
    1≤q .high true z s i ∧ q .high true z s i<11/10 := by
  have hb := high_ranges hz
  have hr := high_ratios hz
  have hc := high_rotation hz
  have hcos := GA_cut_cosine hs
  have hcos0 : 0<Real.cos s := by linarith
  have hl : 0<l .high z := by linarith [hb.2.1.1]
  have hw := (secant_bounds .high true hz hs).1
  have hwHi : secant (l .high z) s<11/10 :=
    (div_lt_iff₀ hcos0).2 (by nlinarith [hb.2.1.2])
  have hG : (51/80)*secant (l .high z) s<k .high z := by
    have h₁ := mul_lt_mul_of_pos_right hr.1 hcos0
    have h₂ := mul_lt_mul_of_pos_left hcos (show 0<(659/1000)*l .high z by positivity)
    dsimp [secant,NegativeAPositiveTD.secant]
    rw [←mul_div_assoc]
    exact (div_lt_iff₀ hcos0).2 (by nlinarith)
  fin_cases i
  · simp [p,q,pWeights,qWeights]
    linarith [hb.1.1]
  · simpa [p,q,pWeights,qWeights,lambdaG,NegativeAPositiveTD.lambdaG] using
      ⟨hG,(by linarith [hb.2.1.1] : (1:ℝ)≤secant (l .high z) s),hwHi⟩
  · simp only [p,q,pWeights,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,↓reduceIte,
      Matrix.cons_val_succ,Matrix.cons_val_zero,min_eq_right hr.2.2.2.2.le,max_eq_left hr.2.2.2.2.le]
    exact ⟨by linarith [hr.2.2.1],by linarith [hb.2.1.1],by linarith [hb.2.1.2]⟩
  · simp [p,q,pWeights,qWeights,min_eq_right hc.2.2.le,max_eq_left hc.2.2.le]
    linarith [hc.1]

theorem high_AB_pair_bounds {s z : ℝ}
    (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) (i : Fin 4) :
    (13/20)*q .high false z s i<p .high false z s i ∧
    1≤q .high false z s i ∧ q .high false z s i<23/20 := by
  have hb := high_ranges hz
  have hr := high_ratios hz
  have hc := high_rotation hz
  have hcos := AB_cut_cosine hs
  have hcos0 : 0<Real.cos s := by linarith
  have hl : 0<l .high z := by linarith [hb.2.1.1]
  have hw := (secant_bounds .high false hz hs).1
  have hwHi : secant (l .high z) s<23/20 :=
    (div_lt_iff₀ hcos0).2 (by nlinarith [hb.2.1.2])
  have hB : (13/20)*secant (l .high z) s<m .high z := by
    have h₁ := mul_lt_mul_of_pos_right hr.2.2.1 hcos0
    have h₂ := mul_lt_mul_of_pos_left hcos (show 0<(4/5)*l .high z by positivity)
    dsimp [secant,NegativeAPositiveTD.secant]
    rw [←mul_div_assoc]
    exact (div_lt_iff₀ hcos0).2 (by nlinarith)
  have hmw : m .high z≤secant (l .high z) s := hr.2.2.2.2.le.trans hw
  fin_cases i
  · simp [p,q,pWeights,qWeights]
    linarith [hb.1.1]
  · simp only [p,q,pWeights,qWeights,lambdaG,NegativeAPositiveTD.lambdaG,↓reduceIte,
      Matrix.cons_val_succ,Matrix.cons_val_zero]
    exact ⟨by linarith [hr.1],by linarith [hb.2.1.1],by linarith [hb.2.1.2]⟩
  · simpa [p,q,pWeights,qWeights,lambdaB,NegativeAPositiveTD.lambdaB,
      min_eq_right hmw,max_eq_left hmw] using
      ⟨hB,(by linarith [hb.2.1.1] : (1:ℝ)≤secant (l .high z) s),hwHi⟩
  · simp [p,q,pWeights,qWeights,min_eq_right hc.2.2.le,max_eq_left hc.2.2.le]
    linarith [hc.1]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Explicit
