module

public import SquaresInCircles.Eight.Words.Common.ZeroCritical

/-!
# Eight squares: all equal-sign source-secondary zero-quarter contacts

The original contact cuts force the needed side, coordinate and angle
regimes. The outer/outer negative case has a direct quadratic reserve.
The narrow mixed negative case uses one monotone quintic obtained from
global sine and cosine Taylor bounds, on its entire forced interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

lemma negative_secondary_positive_angle {a b A B φ : ℝ}
    (hs : State .outer a b ∨ CorePairGeometry.CoreState a b)
    (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) : 0<φ := by
  have hb : 0≤b := by
    rcases hs with hs | hs
    · exact (state_bounds hs).2.2.1
    · exact (CoreAngleEndpoint.state_bounds hs).2.2.1
  have hto := outer_bounds ht
  have hc := signed_cos hφ
  have hBc := mul_le_mul_of_nonneg_left hc.2 ht.1
  have hw := width_ge_one φ
  by_contra! hbad
  have hsin : Real.sin φ≤0 := by
    have ht := positive_trig (x := -φ)
      ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    simpa only [Real.sin_neg,neg_nonneg] using ht.2.2.1
  have hAs := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤A by linarith [ht.1,ht.2.1]) hsin
  norm_num [forwardMargin] at hm
  nlinarith [hto.2.2.2.1,outer_endpoint_bounds.2.2.2]

lemma negative_source_core_target_false {a b A B φ : ℝ} (τ : Bool)
    (hb : 0≤b) (ht : CorePairGeometry.CoreState A B)
    (hm : 0≤forwardMargin 0 a b A B (-1) (WordProblems.sign τ) φ) : False := by
  have hcore := CorePairGeometry.core_radius_sq ht
  have hw := width_ge_one φ
  cases τ
  · have hproj : 1≤A*Real.sin φ+B*Real.cos φ := by
      norm_num [forwardMargin,WordProblems.sign] at hm
      linarith
    have hid : (A*Real.sin φ+B*Real.cos φ)^2+
        (A*Real.cos φ-B*Real.sin φ)^2=A^2+B^2 := by
      linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
    nlinarith [sq_nonneg (A*Real.cos φ-B*Real.sin φ),
      sq_nonneg (A*Real.sin φ+B*Real.cos φ-1)]
  · have hproj : 1≤A*Real.sin φ-B*Real.cos φ := by
      norm_num [forwardMargin,WordProblems.sign] at hm
      linarith
    have hid : (A*Real.sin φ-B*Real.cos φ)^2+
        (A*Real.cos φ+B*Real.sin φ)^2=A^2+B^2 := by
      linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
    nlinarith [sq_nonneg (A*Real.cos φ+B*Real.sin φ),
      sq_nonneg (A*Real.sin φ-B*Real.cos φ-1)]

lemma zero_positive_core_core_false {a b A B φ : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : CorePairGeometry.CoreState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) : False := by
  have hsa := CoreAngleEndpoint.state_bounds hs
  have hta := CoreAngleEndpoint.state_bounds ht
  have hc : 0≤Real.cos φ := by linarith [(signed_cos hφ).1]
  have hsin : Real.sin φ≤13/20 := by linarith [signed_sin hφ,le_abs_self (Real.sin φ)]
  have hA : 0≤A := by linarith [hta.1]
  have hAs := mul_le_mul_of_nonneg_left hsin hA
  have hAc := mul_le_mul_of_nonneg_right hta.2.1 (show (0:ℝ)≤13/20 by norm_num)
  have hBc := mul_nonneg hta.2.2.1 hc
  have hw := width_ge_one φ
  norm_num [forwardMargin] at hm
  nlinarith [hsa.2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]

lemma zero_outer_core_positive {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (391/400:ℝ)<φ+outerLabel a b-coreLabel A B := by
  have hs' : State .outer a b := by simpa [State] using hs
  have ht' : State .coreSide A B := by simpa [State] using ht
  have hp := zero_positive_secondary_angle hs' ht' hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have hso := outer_bounds hs
  have hco := CoreAngleEndpoint.state_bounds ht
  have hb : b<9/10 := hso.2.2.2.1.trans_lt outer_endpoint_bounds.2.2.2
  have hAs := mul_le_mul_of_nonneg_right hco.2.1 tr.2.2.1
  have hw := width_ge_one φ
  have hBsmall : B<1/2 := by
    by_contra! hn
    have hBc := mul_le_mul_of_nonneg_right hn (by linarith [tr.1] : 0≤Real.cos φ)
    norm_num [forwardMargin] at hm
    nlinarith [tr.1,tr.2.2.2.1]
  obtain ⟨hA,hlabel⟩ := core_small_side ht hBsmall
  have hwidth : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
  have hBc0 := mul_nonneg hco.2.2.1 (by linarith [tr.1] : 0≤Real.cos φ)
  have hphi : (2/5:ℝ)<φ := by
    by_contra! hn
    have hc := Real.one_sub_sq_div_two_le_cos (x := φ)
    have hs := Real.sin_le hx.1
    have hsq := pow_le_pow_left₀ hx.1 hn 2
    norm_num [forwardMargin,hA] at hm
    rw [hwidth] at hm
    nlinarith
  have hBcos := mul_le_mul_of_nonneg_right hBsmall.le
    (by linarith [tr.2.1] : 0≤1-Real.cos φ)
  have herror := (outer_label_error hs).1
  norm_num [forwardMargin,hA] at hm
  rw [hwidth] at hm
  rw [hlabel]
  nlinarith [tr.1,tr.2.2.2.1]

lemma zero_outer_outer_negative {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) :
    (391/400:ℝ)<φ-outerLabel a b+outerLabel A B := by
  have hs' : State .outer a b := by simpa [State] using hs
  have hp := negative_secondary_positive_angle (Or.inl hs') ht hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have hto := outer_bounds ht
  have hA : A<283/200 := hto.2.1.trans_lt outer_endpoint_bounds.2.1
  have hAs := mul_le_mul_of_nonneg_right hA.le tr.2.2.1
  have hBc := mul_le_mul_of_nonneg_left tr.2.1 ht.1
  have hwidth : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
  have hB : (7/25:ℝ)<B := by
    norm_num [forwardMargin] at hm
    rw [hwidth] at hm
    nlinarith [hs.1,tr.1,tr.2.2.2.1]
  have hBremainder := mul_le_mul_of_nonneg_right hB.le
    (by linarith [tr.2.1] : 0≤1-Real.cos φ)
  have hse := (outer_label_error hs).2
  have hte := (outer_label_error ht).1
  have hc := Real.one_sub_sq_div_two_le_cos (x := φ)
  have hsq := mul_le_mul_of_nonneg_right hx.2 hx.1
  norm_num [forwardMargin] at hm
  rw [hwidth] at hm
  nlinarith [tr.2.2.2.2.1]

/-- The only narrow mixed equal-sign scalar is monotone on the complete
interval forced by the source contact. -/
def coreNegativePolynomial (x : ℝ) : ℝ :=
  99017/100000+(17/200)*x-x^2/4+(61/400)*x^3-(61/8000)*x^5

lemma coreNegativePolynomial_antitone :
    AntitoneOn coreNegativePolynomial (Icc (1/4) (7/10)) := by
  have hd : ∀ x:ℝ, HasDerivAt coreNegativePolynomial
      (17/200-x/2+(183/400)*x^2-(61/1600)*x^4) x := by
    intro x
    unfold coreNegativePolynomial
    convert (((((hasDerivAt_id' x).const_mul (17/200:ℝ)).const_add (99017/100000:ℝ)).fun_sub
      ((hasDerivAt_pow 2 x).div_const 4)).fun_add
        ((hasDerivAt_pow 3 x).const_mul (61/400:ℝ))).fun_sub
          ((hasDerivAt_pow 5 x).const_mul (61/8000:ℝ)) using 1
    ring
  apply antiOn_of_hasDeriv_nonpos
    (d := fun x => 17/200-x/2+(183/400)*x^2-(61/1600)*x^4)
  · exact fun x _ => (hd x).continuousAt.continuousWithinAt
  · exact fun x _ => hd x
  · intro x hx
    have hb := mul_nonneg (show 0≤x-1/4 by linarith [hx.1])
      (show 0≤7/10-x by linarith [hx.2])
    nlinarith [sq_nonneg (x^2)]

lemma core_negative_scalar {x : ℝ} (hx : x∈Icc (1/4) (7/10)) :
    (391/400:ℝ)<x+49017/100000+(1/2)*Real.cos x-(183/200)*Real.sin x := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hs := sin_upper_five hx0
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hpoly := coreNegativePolynomial_antitone hx (by norm_num) hx.2
  have hend : (391/400:ℝ)<coreNegativePolynomial (7/10) := by
    norm_num [coreNegativePolynomial]
  dsimp [coreNegativePolynomial] at hpoly hend
  linarith

lemma zero_core_outer_negative {a b A B φ : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) :
    (391/400:ℝ)<φ-coreLabel a b+outerLabel A B := by
  have hp := negative_secondary_positive_angle (Or.inr hs) ht hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have hs0 := (CoreAngleEndpoint.state_bounds hs).2.2.1
  have ht0 := outer_bounds ht
  have hwidth : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
  have htarget := outer_diagonal_upper (X := Real.sin φ) (Y := Real.cos φ) ht
    tr.2.2.1 (by linarith [tr.1,tr.2.2.2.1])
  have hsum : Real.sin φ+Real.cos φ<(57/40:ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq φ,sq_nonneg (Real.sin φ-Real.cos φ)]
  have hcap := mul_lt_mul_of_pos_right outer_endpoint_bounds.2.2.2
    (show 0<Real.sin φ+Real.cos φ by linarith [tr.2.2.2.2.2])
  norm_num [forwardMargin] at hm
  rw [hwidth] at hm
  have hb : b<7/100 := by nlinarith
  obtain ⟨ha,hl⟩ := core_small_side hs (by linarith)
  have hquarter : (1/4:ℝ)<φ := by
    by_contra! hn
    nlinarith [tr.2.1,tr.2.2.2.2.1]
  have hsl := (positive_taylor_reserves hx).1
  have hu : (13/200)-Real.sin φ≤0 := by linarith
  have hv : 0≤(203/200)-Real.cos φ := by linarith [tr.2.1]
  have hAterm := mul_le_mul_of_nonpos_left ht0.2.1 hu
  have hBterm := mul_nonneg hv ht.1
  have hsa := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.1.le tr.2.2.1
  have hplower := mul_le_mul_of_nonneg_left outer_endpoint_bounds.1.le
    (show (0:ℝ)≤13/200 by norm_num)
  have hscalar := core_negative_scalar (show φ∈Icc (1/4) (7/10) from ⟨hquarter.le,hx.2⟩)
  rw [hl]
  dsimp [outerLabel]
  nlinarith

/-- The original source-secondary axis, with both equal-sign choices. -/
theorem zero_same_secondary {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ : Bool)
    (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (WordProblems.sign σ) (WordProblems.sign σ) φ) :
    (391/400:ℝ)<cost source target σ σ a b A B φ := by
  cases σ
  · have hm' : 0≤forwardMargin 0 a b A B (-1) (-1) φ := by
      simpa [WordProblems.sign] using hm
    by_cases hto : target=.outer
    · have ht' : OuterState A B := by simpa [State,hto] using ht
      by_cases hso : source=.outer
      · have hs' : OuterState a b := by simpa [State,hso] using hs
        have h := zero_outer_outer_negative hs' ht' hφ hm'
        simp [cost,WordProblems.sign,label,hso,hto]
        linarith
      · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
        have h := zero_core_outer_negative hs' ht' hφ hm'
        simp [cost,WordProblems.sign,label,hso,hto]
        linarith
    · have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
      exact (negative_source_core_target_false false (state_bounds hs).2.2.1 ht'
        (by simpa [WordProblems.sign] using hm)).elim
  · have hm' : 0≤forwardMargin 0 a b A B 1 1 φ := by simpa [WordProblems.sign] using hm
    by_cases hso : source=.outer <;> by_cases hto : target=.outer
    · have hs' : OuterState a b := by simpa [State,hso] using hs
      have ht' : OuterState A B := by simpa [State,hto] using ht
      simpa [cost,WordProblems.sign,label,hso,hto] using
        zero_outer_outer_positive hs' ht' hφ hm'
    · have hs' : OuterState a b := by simpa [State,hso] using hs
      have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
      simpa [cost,WordProblems.sign,label,hso,hto] using
        zero_outer_core_positive hs' ht' hφ hm'
    · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
      have ht' : OuterState A B := by simpa [State,hto] using ht
      simpa [cost,WordProblems.sign,label,hso,hto] using
        zero_core_outer_positive hs' ht' hφ hm'
    · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
      have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
      exact (zero_positive_core_core_false hs' ht' hφ hm').elim

end SquaresInCircles.Eight.CommonQuarter
