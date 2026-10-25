module

public import SquaresInCircles.Eight.Owners.CircularNorm
public import SquaresInCircles.Eight.Words.Common.JumpTwo
public import SquaresInCircles.Eight.Words.Common.QuarterState
public import SquaresInCircles.Eight.Words.Common.ZeroEndpoint

/-!
# Eight squares: all equal-sign source-secondary zero-quarter contacts

The original contact cuts force the needed side, coordinate and angle
regimes. The outer/outer negative case has a direct quadratic reserve.
The narrow mixed negative case uses one monotone quintic obtained from
global sine and cosine Taylor bounds, on its entire forced interval.
-/

section
/-!
## The common sine-support envelope on its whole contact interval

One harmonic lower support bounds the norm/sine ratio, `N l x < (15/8) sin x`, for every
multiplier `l` in `[.9695,1.05]` (`norm_sine_bound`). Together with the exact norm curvature this
proves that `base l` is concave on all of `[.1,.7]` (`base_concave`). The applications, at fixed
multipliers, are the critical positive outer zero edge (`zero_outer_positive`), the positive
core/outer zero edge (`zero_core_outer_positive`) and the remaining positive quarter-primary
outer edge (`one_outer_primary`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter.SineEnvelope

open Arithmetic

def mass (l : ℝ) : ℝ := (13/200)^2+(203/200)^2+l^2
def cosCoeff (l : ℝ) : ℝ := -2*l*(203/200)
def sinCoeff (l : ℝ) : ℝ := 2*l*(13/200)
def N (l x : ℝ) : ℝ := CircularNorm.norm (mass l) (cosCoeff l) (sinCoeff l) x

def base (l x : ℝ) : ℝ := x+l*Real.sin x-radius*N l x

def baseD (l x : ℝ) : ℝ :=
  1+l*Real.cos x-radius*CircularNorm.d1 (mass l) (cosCoeff l) (sinCoeff l) x

def baseDD (l x : ℝ) : ℝ :=
  -l*Real.sin x-radius*CircularNorm.d2 (mass l) (cosCoeff l) (sinCoeff l) x

theorem sine_lower {x : ℝ} (hx : x∈Icc (1/10) (7/10)) :
    (99/1000:ℝ)<Real.sin x := by
  have hm := sin_mono (show (1/10:ℝ)∈Icc 0 (7/10) by norm_num)
    (show x∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩) hx.1
  linarith [tenth_trig.1]

theorem energy_identity (l x : ℝ) :
    CircularNorm.energy (mass l) (cosCoeff l) (sinCoeff l) x=
      ((13/200)+l*Real.sin x)^2+((203/200)-l*Real.cos x)^2 := by
  dsimp [CircularNorm.energy,mass,cosCoeff,sinCoeff]
  linear_combination -(l^2)*(Real.sin_sq_add_cos_sq x)

theorem energy_pos {l x : ℝ} (hl : 1939/2000≤l)
    (hx : x∈Icc (1/10) (7/10)) :
    0<CircularNorm.energy (mass l) (cosCoeff l) (sinCoeff l) x := by
  have hs : 0<Real.sin x := by linarith [sine_lower hx]
  have hp : 0<(13/200:ℝ)+l*Real.sin x := by positivity
  rw [energy_identity]
  nlinarith [sq_pos_of_pos hp,sq_nonneg ((203/200:ℝ)-l*Real.cos x)]

theorem N_pos {l x : ℝ} (hl : 1939/2000≤l)
    (hx : x∈Icc (1/10) (7/10)) : 0<N l x :=
  CircularNorm.norm_pos (energy_pos hl hx)

theorem N_sq {l x : ℝ} (hl : 1939/2000≤l)
    (hx : x∈Icc (1/10) (7/10)) :
    (N l x)^2=(13/200:ℝ)^2+(203/200)^2+l^2+
      2*l*((13/200)*Real.sin x-(203/200)*Real.cos x) := by
  rw [N,CircularNorm.norm_sq (energy_pos hl hx).le]
  simp only [CircularNorm.energy,mass,cosCoeff,sinCoeff]
  ring

/-- One harmonic support bounds the ratio uniformly; this looser ratio still gives strict
concavity of the envelope. -/
theorem norm_sine_bound {l x : ℝ} (hl : l∈Icc (1939/2000) (21/20))
    (hx : x∈Icc (1/10) (7/10)) : N l x<(15/8)*Real.sin x := by
  have hs := sine_lower hx
  have ht := positive_trig (show x∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩)
  have hl0 : 0≤l := by linarith [hl.1]
  have hcos := mul_le_mul_of_nonneg_left ht.2.1 hl0
  have hsin := mul_le_mul_of_nonneg_right hl.2 ht.2.2.1
  have hu := ratio_harmonic hx hl.1
  have huL : -(3/5)*Real.sin x≤(203/200:ℝ)-l*Real.cos x := by linarith [hl.2]
  have huU : (203/200:ℝ)-l*Real.cos x≤(3/5)*Real.sin x := by linarith
  have hv0 : 0≤(13/200:ℝ)+l*Real.sin x := by positivity
  have hvU : (13/200:ℝ)+l*Real.sin x<(7/4)*Real.sin x := by linarith
  have hu2 := mul_nonneg (sub_nonneg.mpr huU) (by linarith :
    0≤(3/5)*Real.sin x+((203/200:ℝ)-l*Real.cos x))
  have hv2 := mul_pos (sub_pos.mpr hvU) (by linarith :
    0<(7/4)*Real.sin x+((13/200:ℝ)+l*Real.sin x))
  have hNsq : (N l x)^2=((13/200)+l*Real.sin x)^2+
      ((203/200)-l*Real.cos x)^2 := by
    exact (CircularNorm.norm_sq (energy_pos hl.1 hx).le).trans (energy_identity l x)
  have hsq : (N l x)^2<((15/8)*Real.sin x)^2 := by linarith [sq_nonneg (Real.sin x)]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

theorem coefficient_square (l : ℝ) :
    (cosCoeff l)^2+(sinCoeff l)^2≤(mass l)^2 := by
  have hid : (mass l)^2-(cosCoeff l)^2-(sinCoeff l)^2=
      ((13/200:ℝ)^2+(203/200)^2-l^2)^2 := by
    dsimp [mass,cosCoeff,sinCoeff]
    ring
  nlinarith [sq_nonneg ((13/200:ℝ)^2+(203/200)^2-l^2)]

theorem base_hasDerivAt {l x : ℝ} (hl : 1939/2000≤l)
    (hx : x∈Icc (1/10) (7/10)) : HasDerivAt (base l) (baseD l x) x := by
  have hn := CircularNorm.norm_hasDerivAt (energy_pos hl hx)
  exact ((hasDerivAt_id x).add ((Real.hasDerivAt_sin x).const_mul l)).sub
    (hn.const_mul radius)

theorem baseD_hasDerivAt {l x : ℝ} (hl : 1939/2000≤l)
    (hx : x∈Icc (1/10) (7/10)) : HasDerivAt (baseD l) (baseDD l x) x := by
  have hn := CircularNorm.d1_hasDerivAt (energy_pos hl hx)
  have e : baseDD l x=l*-Real.sin x-
      radius*CircularNorm.d2 (mass l) (cosCoeff l) (sinCoeff l) x := by
    unfold baseDD; ring
  rw [e]
  exact (((Real.hasDerivAt_cos x).const_mul l).const_add 1).sub (hn.const_mul radius)

theorem baseDD_neg {l x : ℝ} (hl : l∈Icc (1939/2000) (21/20))
    (hx : x∈Icc (1/10) (7/10)) : baseDD l x<0 := by
  have hs : 0<Real.sin x := by linarith [sine_lower hx]
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hnorm := norm_sine_bound hl hx
  have hN := CircularNorm.curvature_lower (energy_pos hl.1 hx) (coefficient_square l)
  have hmul := mul_le_mul_of_nonneg_left hN hR.le
  have hRN := mul_lt_mul_of_pos_left hnorm hR
  have hRsin := mul_lt_mul_of_pos_right (show radius<2 by linarith [radius_bounds.2]) hs
  have hls := mul_le_mul_of_nonneg_right hl.1 hs.le
  change radius*(-(N l x)/4)≤radius*
    CircularNorm.d2 (mass l) (cosCoeff l) (sinCoeff l) x at hmul
  dsimp only [baseDD]
  nlinarith

theorem base_concave {l : ℝ} (hl : l∈Icc (1939/2000) (21/20)) :
    ConcaveOn ℝ (Icc (1/10) (7/10)) (base l) :=
  concave_of_deriv2 (fun _ hx => base_hasDerivAt hl.1 hx)
    (fun _ hx => baseD_hasDerivAt hl.1 hx) (fun _ hx => (baseDD_neg hl hx).le)

theorem base_endpoint_min {l x : ℝ} (hl : l∈Icc (1939/2000) (21/20))
    (hx : x∈Icc (1/10) (7/10)) :
    min (base l (1/10)) (base l (7/10))≤base l x :=
  (base_concave hl).min_le_of_mem_Icc (by norm_num) (by norm_num) hx

lemma scaled_norm_bound {l x u : ℝ} (hl : 1939/2000≤l)
    (hx : x∈Icc (1/10) (7/10)) (hu : N l x<u) :
    radius*N l x<(1979/1000)*u := by
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hu0 : 0<u := (N_pos hl hx).trans hu
  exact (mul_lt_mul_of_pos_left hu hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 hu0)

/-- Six norm endpoint comparisons for the three multipliers used. -/
theorem endpoint_norms :
    N (1939/2000) (1/10)<17/100 ∧ N (1939/2000) (7/10)<371/500 ∧
    N (21/20) (1/10)<173/1000 ∧ N (21/20) (7/10)<193/250 ∧
    N (39/40) (1/10)<337/2000 ∧ N (39/40) (7/10)<1859/2500 := by
  have hsmall := tenth_trig
  have hcap := cap_trig
  have key : ∀ {l x c : ℝ},1939/2000≤l → x∈Icc (1/10) (7/10) → 0≤c →
      (13/200:ℝ)^2+(203/200)^2+l^2+
        2*l*((13/200)*Real.sin x-(203/200)*Real.cos x)<c^2 → N l x<c :=
    fun hl hx hc h => lt_of_pow_lt_pow_left₀ 2 hc ((N_sq hl hx).trans_lt h)
  refine ⟨key (by norm_num) (by norm_num) (by norm_num) ?_,
    key (by norm_num) (by norm_num) (by norm_num) ?_,
    key (by norm_num) (by norm_num) (by norm_num) ?_,
    key (by norm_num) (by norm_num) (by norm_num) ?_,
    key (by norm_num) (by norm_num) (by norm_num) ?_,
    key (by norm_num) (by norm_num) (by norm_num) ?_⟩
  · linarith [hsmall.2.1,hsmall.2.2]
  · linarith [hcap.2.1,hcap.2.2.1]
  · linarith [hsmall.2.1,hsmall.2.2]
  · linarith [hcap.2.1,hcap.2.2.1]
  · linarith [hsmall.2.1,hsmall.2.2]
  · linarith [hcap.2.1,hcap.2.2.1]

theorem zero_outer_positive {x : ℝ} (hx : x∈Icc (1/10) (7/10)) :
    (391/400:ℝ)<4489/4000+base (1939/2000) x := by
  have h₀ := scaled_norm_bound (l := (1939/2000:ℝ)) (x := (1/10:ℝ))
    (by norm_num) (by norm_num) endpoint_norms.1
  have h₁ := scaled_norm_bound (l := (1939/2000:ℝ)) (x := (7/10:ℝ))
    (by norm_num) (by norm_num) endpoint_norms.2.1
  have hleft : (391/400:ℝ)<4489/4000+base (1939/2000) (1/10) := by
    dsimp [base]
    linarith [tenth_trig.1]
  have hright : (391/400:ℝ)<4489/4000+base (1939/2000) (7/10) := by
    dsimp [base]
    linarith [cap_trig.1]
  have hm := base_endpoint_min (l := (1939/2000:ℝ)) (by norm_num) hx
  have hmin : (391/400:ℝ)-4489/4000<
      min (base (1939/2000) (1/10)) (base (1939/2000) (7/10)) :=
    lt_min (by linarith) (by linarith)
  linarith

theorem zero_core_outer_positive {x : ℝ} (hx : x∈Icc (1/10) (7/10)) :
    (391/400:ℝ)<231/200+base (21/20) x := by
  have h₀ := scaled_norm_bound (l := (21/20:ℝ)) (x := (1/10:ℝ))
    (by norm_num) (by norm_num) endpoint_norms.2.2.1
  have h₁ := scaled_norm_bound (l := (21/20:ℝ)) (x := (7/10:ℝ))
    (by norm_num) (by norm_num) endpoint_norms.2.2.2.1
  have hleft : (391/400:ℝ)<231/200+base (21/20) (1/10) := by
    dsimp [base]
    linarith [tenth_trig.1]
  have hright : (391/400:ℝ)<231/200+base (21/20) (7/10) := by
    dsimp [base]
    linarith [cap_trig.1]
  have hm := base_endpoint_min (l := (21/20:ℝ)) (by norm_num) hx
  have hmin : (391/400:ℝ)-231/200<
      min (base (21/20) (1/10)) (base (21/20) (7/10)) :=
    lt_min (by linarith) (by linarith)
  linarith

def primaryNorm : ℝ := Real.sqrt ((26/25:ℝ)^2+(203/200)^2)

theorem primaryNorm_lt : primaryNorm<145322/100000 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤(26/25)^2+(203/200)^2 by norm_num)
  have hn := Real.sqrt_nonneg ((26/25:ℝ)^2+(203/200)^2)
  dsimp [primaryNorm]
  nlinarith

theorem one_outer_primary {x : ℝ} (hx : x∈Icc (1/10) (7/10)) :
    (157/200:ℝ)<Real.pi/2+63/50+39/40-radius*primaryNorm+base (39/40) x := by
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hRN := (mul_lt_mul_of_pos_left primaryNorm_lt hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<145322/100000))
  have h₀ := scaled_norm_bound (l := (39/40:ℝ)) (x := (1/10:ℝ))
    (by norm_num) (by norm_num) endpoint_norms.2.2.2.2.1
  have h₁ := scaled_norm_bound (l := (39/40:ℝ)) (x := (7/10:ℝ))
    (by norm_num) (by norm_num) endpoint_norms.2.2.2.2.2
  have hleft : (157/200:ℝ)<
      (Real.pi/2+63/50+39/40-radius*primaryNorm)+base (39/40) (1/10) := by
    dsimp only [base]
    linarith [tenth_trig.1,pi_hand_enclosure.1]
  have hright : (157/200:ℝ)<
      (Real.pi/2+63/50+39/40-radius*primaryNorm)+base (39/40) (7/10) := by
    dsimp only [base]
    linarith [cap_trig.1,pi_hand_enclosure.1]
  have hm := base_endpoint_min (l := (39/40:ℝ)) (by norm_num) hx
  have hmin : (157/200:ℝ)-(Real.pi/2+63/50+39/40-radius*primaryNorm) <
      min (base (39/40) (1/10)) (base (39/40) (7/10)) :=
    lt_min (by linarith) (by linarith)
  linarith

end SquaresInCircles.Eight.CommonQuarter.SineEnvelope
end
end
end

section
/-!
## The critical positive source-secondary zero-quarter regimes

The original weak separator forces the frame angle above one tenth. In
the outer/outer case it also forces a transverse coordinate above `.28`;
one convex quadratic then supplies the stronger source-circle support.
The target is bounded by its full circle at the same original angle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

/-- All positive/positive source-secondary zero contacts lie in the same
complete positive-angle interval. -/
theorem zero_positive_secondary_angle {source target : RadialKind}
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (1/10:ℝ)<φ := by
  have hs' := state_bounds hs
  have ht' := state_bounds ht
  have hc : 0<Real.cos φ := by linarith [(signed_cos hφ).1]
  have hw := width_ge_one φ
  have hφpos : 0<φ := by
    by_contra! hn
    have hsin : Real.sin φ≤0 := by
      have hp := positive_trig (x := -φ)
        ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
      simpa only [Real.sin_neg,neg_nonneg] using hp.2.2.1
    have hAs := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤A by linarith [ht'.1]) hsin
    have hBc := mul_nonneg ht'.2.2.1 hc.le
    norm_num [forwardMargin] at hm
    nlinarith [hs'.2.2.2.2]
  by_contra! hsmall
  have hx : φ∈Icc 0 (7/10) := ⟨hφpos.le,(abs_le.mp hφ).2⟩
  have hsin := positive_trig hx
  have hcos := Real.one_sub_sq_div_two_le_cos (x := φ)
  have hφ2 := pow_le_pow_left₀ hx.1 hsmall 2
  have hAc := mul_le_mul_of_nonneg_right ht'.2.1.le hsin.2.2.1
  have hBc := mul_nonneg ht'.2.2.1 hc.le
  have hwidth : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg hsin.2.2.1]
  norm_num [forwardMargin] at hm
  rw [hwidth] at hm
  nlinarith [hs'.2.2.2.2,hsin.2.2.2.2.1]

/-- Actual target-circle support for the entire sine-norm family. -/
theorem sine_target_support {A B l x : ℝ} (ht : OuterState A B) :
    ((13/200:ℝ)+(203/200)+l*(Real.sin x-Real.cos x))/2-
      radius*SineEnvelope.N l x≤
        (-(13/200)-l*Real.sin x)*A+(l*Real.cos x-(203/200))*B := by
  have hh := outer_circle_lower (X := -(13/200)-l*Real.sin x)
    (Y := l*Real.cos x-(203/200)) ht
  have hr : (-(13/200)-l*Real.sin x)^2+(l*Real.cos x-(203/200))^2=
      CircularNorm.energy (SineEnvelope.mass l) (SineEnvelope.cosCoeff l)
        (SineEnvelope.sinCoeff l) x := by
    rw [SineEnvelope.energy_identity]
    ring
  rw [hr] at hh
  change -((-(13/200)-l*Real.sin x)+(l*Real.cos x-(203/200)))/2-
    radius*SineEnvelope.N l x≤_ at hh
  linarith

/-- Positive core source and positive outer target, with the original
secondary axis and the complete closed core boundary. -/
theorem zero_core_outer_positive {a b A B φ : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (391/400:ℝ)<φ+coreLabel a b-outerLabel A B := by
  have hs' : State .coreSide a b := by simpa [State] using hs
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := zero_positive_secondary_angle hs' ht' hφ hm
  have hx : φ∈Icc (1/10) (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have htrig := positive_trig (show φ∈Icc 0 (7/10) from ⟨by linarith,hx.2⟩)
  have hw : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg htrig.2.2.1]
  have hsource := core_label_lower hs
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  have htarget := sine_target_support (l := (21/20:ℝ)) (x := φ) ht
  have hmul := mul_nonneg (show (0:ℝ)≤21/20 by norm_num) hm
  norm_num [forwardMargin] at hmul
  rw [hw] at hmul
  have hlower : 231/200+SineEnvelope.base (21/20) φ≤
      φ+coreLabel a b-outerLabel A B := by
    dsimp [SineEnvelope.base,outerLabel]
    nlinarith
  exact (SineEnvelope.zero_core_outer_positive hx).trans_le hlower

/-- The positive outer source coordinate is bounded away from its axis by
the original separator, before choosing the support multiplier. -/
theorem zero_outer_positive_source_cut {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 1 φ) : (7/25:ℝ)<b := by
  have hs' : State .outer a b := by simpa [State] using hs
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := zero_positive_secondary_angle hs' ht' hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hφ).2⟩
  have htrig := positive_trig hx
  have hA := (state_bounds ht').2.1
  have hAs := mul_le_mul_of_nonneg_right hA.le htrig.2.2.1
  have hBc := mul_nonneg ht.1 (show 0≤Real.cos φ by linarith [htrig.1])
  have hw : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg htrig.2.2.1]
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  nlinarith [htrig.1,htrig.2.2.2.1]

/-- One convex quadratic proves the sloping source support on the entire
closed coordinate range forced by the original contact. -/
theorem outer_source_sloping_lower {a b : ℝ} (hs : OuterState a b)
    (hb : (7/25:ℝ)≤b) : (3/2:ℝ)<a+(7/10)*b := by
  have h := outer_bounds hs
  have hbu : b≤9/10 := h.2.2.2.1.trans outer_endpoint_bounds.2.2.2.le
  have hpoly := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hbu)
  have hquadratic : (b+1/2)^2+(2-(7/10)*b)^2<Q0 := by
    norm_num [Q0]
    nlinarith
  by_contra! hbad
  have ha0 : 0≤a+1/2 := by linarith [hs.1,hs.2.1]
  have hasq := pow_le_pow_left₀ ha0
    (show a+1/2≤2-(7/10)*b by linarith) 2
  nlinarith [hs.2.2]

/-- The critical positive outer/outer zero-quarter regime is closed on the
whole actual circle and angle interval. -/
theorem zero_outer_outer_positive {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (391/400:ℝ)<φ+outerLabel a b-outerLabel A B := by
  have hs' : State .outer a b := by simpa [State] using hs
  have ht' : State .outer A B := by simpa [State] using ht
  have hp := zero_positive_secondary_angle hs' ht' hφ hm
  have hx : φ∈Icc (1/10) (7/10) := ⟨hp.le,(abs_le.mp hφ).2⟩
  have hb := zero_outer_positive_source_cut hs ht hφ hm
  have hsource := outer_source_sloping_lower hs hb.le
  have htrig := positive_trig (show φ∈Icc 0 (7/10) from ⟨by linarith,hx.2⟩)
  have hw : pairWidth φ=(1+Real.cos φ+Real.sin φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg htrig.2.2.1]
  have htarget := sine_target_support (l := (1939/2000:ℝ)) (x := φ) ht
  have hmul := mul_nonneg (show (0:ℝ)≤1939/2000 by norm_num) hm
  norm_num [forwardMargin] at hmul
  rw [hw] at hmul
  have hlower : 4489/4000+SineEnvelope.base (1939/2000) φ<
      φ+outerLabel a b-outerLabel A B := by
    dsimp [SineEnvelope.base,outerLabel]
    nlinarith
  exact (SineEnvelope.zero_outer_positive hx).trans hlower

end SquaresInCircles.Eight.CommonQuarter
end
end
end

section
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
end
end
end
