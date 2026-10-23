module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroUnfavorable

/-!
# The positive-primary-label favorable outer zero family

A single constant multiplier handles the complete original domain.
The source arc minimum is axial; the target's axial derivative is
positive throughout the angle range forced by the actual separator.
The resulting scalar increases from its single rational endpoint.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortOuterZero

open CommonQuarter CorePairGeometry WrongWordCircleSupport

lemma fine_axial_bounds : (1414575671/1000000000:ℝ)<outerAxial ∧
    outerAxial<176821959/125000000 := by
  have he := axial_circle
  have ha : 0<outerAxial+1/2 := by linarith [outer_endpoint_bounds.1]
  norm_num [Q0] at he
  constructor <;> nlinarith

/-- The actual positive zero owner starts beyond `.107`, regardless of
which increasing role labels will be attached to its two outer states. -/
lemma positive_original_angle {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) : (107/1000:ℝ)<φ := by
  have hs' : State .outer a b := by simpa [State] using hs
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := zero_positive_secondary_angle hs' ht' hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have hAs := mul_le_mul_of_nonneg_right (outer_bounds ht).2.1 tr.2.2.1
  have ha := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.1.le tr.2.2.1
  have hBc := mul_nonneg ht.1 (show 0≤Real.cos φ by linarith [tr.1])
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  by_contra! hn
  have hsine := Real.sin_le hx.1
  have hcos := cos_lower_two hx.1
  have hs2 := pow_le_pow_left₀ hx.1 hn 2
  nlinarith [(outer_bounds hs).2.2.2.1,ShortMixedZero.fine_diagonal_bounds.2]

namespace PositivePrimary

def multiplier : ℝ := 45181/50000
def envelope (x : ℝ) : ℝ := x-75097/100000+(25777/50000)*outerAxial+
  multiplier/2+(multiplier/2)*Real.cos x+multiplier*(1/2-outerAxial)*Real.sin x
def envelopeD (x : ℝ) : ℝ :=
  1-multiplier*(Real.sin x/2+(outerAxial-1/2)*Real.cos x)

lemma source_endpoints : (25777/50000:ℝ)*outerAxial≤
    (25777/50000+119909/100000-multiplier)*outerDiagonal := by
  have ha := fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  norm_num [multiplier]
  linarith [ha.2,hd.1]

lemma initial_trig : Real.sin (107/1000:ℝ)<133495/1250000 ∧
    (1242851/1250000:ℝ)<Real.cos (107/1000:ℝ) := by
  have hs := sin_upper_five (x := (107/1000:ℝ)) (by norm_num)
  have hc := cos_lower_six (x := (107/1000:ℝ)) (by norm_num)
  norm_num at hs hc
  exact ⟨by linarith,by linarith⟩

lemma initial_value : (449/500:ℝ)<envelope (107/1000) := by
  have ha := fine_axial_bounds
  have ht := initial_trig
  have hs := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤outerAxial-1/2 by linarith [ha.1])
  have hu := mul_le_mul_of_nonneg_right ha.2.le
    (show (0:ℝ)≤133495/1250000 by norm_num)
  norm_num [envelope,multiplier]
  nlinarith [ha.1,ht.2]

lemma envelope_hasDerivAt (x : ℝ) : HasDerivAt envelope (envelopeD x) x := by
  convert ((((((hasDerivAt_id x).sub_const (75097/100000)).add_const
    ((25777/50000)*outerAxial)).add_const (multiplier/2)).add
      ((Real.hasDerivAt_cos x).const_mul (multiplier/2))).add
        ((Real.hasDerivAt_sin x).const_mul (multiplier*(1/2-outerAxial)))) using 1 <;>
    dsimp [envelope,envelopeD] <;> ring

lemma envelopeD_pos (x : ℝ) : 0<envelopeD x := by
  have hh := mul_lt_mul_of_pos_left (ShortMixedZero.axial_projection_bound x)
    (show 0<multiplier by norm_num [multiplier])
  norm_num [envelopeD,multiplier] at hh ⊢
  linarith

lemma envelope_lower {x : ℝ} (hx : x∈Icc (107/1000) (7/10)) :
    (449/500:ℝ)<envelope x := by
  have hm : MonotoneOn envelope (Icc (107/1000) (7/10)) :=
    monoOn_of_hasDeriv_nonneg (fun z _ => (envelope_hasDerivAt z).continuousAt.continuousWithinAt)
      (fun z _ => envelope_hasDerivAt z) (fun z _ => (envelopeD_pos z).le)
  exact initial_value.trans_le (hm (by norm_num) hx hx.1)

lemma target_axial_derivative {x : ℝ} (hx : x∈Icc (107/1000) (7/10)) :
    0≤(outerAxial+1/2)*(multiplier*Real.cos x-71553/100000)+multiplier*Real.sin x/2 := by
  have hx' : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have tr := positive_trig hx'
  have hs0 := Real.sin_ge_sub_cube (show (0:ℝ)≤107/1000 by norm_num)
  have hm := sin_mono (show (107/1000:ℝ)∈Icc 0 (7/10) by norm_num) hx' hx.1
  have hs : (1067/10000:ℝ)<Real.sin x := by norm_num at hs0; linarith
  have hY : -(1/40:ℝ)<multiplier*Real.cos x-71553/100000 := by
    norm_num [multiplier]
    linarith [tr.1]
  have hp := mul_nonneg (show 0≤outerAxial+1/2 by linarith [outer_endpoint_bounds.1])
    (show 0≤multiplier*Real.cos x-71553/100000+1/40 by linarith)
  norm_num [multiplier] at hp ⊢
  nlinarith [outer_endpoint_bounds.2.1]

/-- The complete favorable tuple `(-.75097,.51554,1.19909,0,.71553)`.
The separating axis and both outer states are the originals. -/
theorem original_cost {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (449/500:ℝ)<φ-75097/100000+(25777/50000)*a+(119909/100000)*b-(71553/100000)*B := by
  have hx : φ∈Icc (107/1000) (7/10) :=
    ⟨(positive_original_angle hs ht hφ hm).le,(abs_le.mp hφ).2⟩
  have tr := positive_trig (show φ∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩)
  have hsource := outer_concave_lower hs (X := (25777/50000:ℝ))
    (Y := (119909/100000)-multiplier) (by norm_num) le_rfl source_endpoints
  have hX : -multiplier*Real.sin φ≤0 :=
    neg_nonpos.mpr (mul_nonneg (by norm_num [multiplier]) tr.2.2.1)
  have htarget := outer_axial_lower ht hX
    (Y := multiplier*Real.cos φ-71553/100000) (by
      have hh := target_axial_derivative hx
      linarith)
  have hmargin := mul_nonneg (show 0≤multiplier by norm_num [multiplier]) hm
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  norm_num [forwardMargin] at hmargin
  rw [hw] at hmargin
  have hscalar := envelope_lower hx
  dsimp [envelope] at hscalar
  nlinarith only [hsource,htarget,hmargin,hscalar]

end PositivePrimary

end SquaresInCircles.Eight.TableFree.ShortOuterZero
