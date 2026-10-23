module

public import SquaresInCircles.Eight.TableFree.CommonQuarterTrig
public import SquaresInCircles.Eight.TableFree.CircularNorm

/-!
# The common sine-support envelope on its whole contact interval

A single harmonic lower support bounds the norm/sine ratio for every
multiplier in `[.9695,1.05]`. Together with the exact norm curvature this
proves concavity on all of `[.1,.7]`. The fixed applications cover the
critical positive outer zero edge, the positive core/outer zero edge,
and the remaining positive quarter-primary outer edge.
Uncompiled source draft.
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
  have hh := CircularNorm.norm_sq (energy_pos hl hx).le
  simpa [N,CircularNorm.energy,mass,cosCoeff,sinCoeff] using hh

/-- One harmonic support replaces the ratio's stationary-point analysis.
The looser uniform ratio still gives strict envelope concavity. -/
theorem norm_sine_bound {l x : ℝ} (hl : l∈Icc (1939/2000) (21/20))
    (hx : x∈Icc (1/10) (7/10)) : N l x<(15/8)*Real.sin x := by
  have hs := sine_lower hx
  have ht := positive_trig (show x∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩)
  have hl0 : 0≤l := by linarith [hl.1]
  have hcos := mul_le_mul_of_nonneg_left ht.2.1 hl0
  have hsin := mul_le_mul_of_nonneg_right hl.2 ht.2.2.1
  have hu := ratio_harmonic hx hl.1
  have huL : -(3/5)*Real.sin x≤(203/200:ℝ)-l*Real.cos x := by linarith
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
  nlinarith [N_pos hl.1 hx]

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
  convert ((hasDerivAt_id x).add ((Real.hasDerivAt_sin x).const_mul l)).sub
    (hn.const_mul radius) using 1 <;> dsimp [base,baseD,N] <;> ring

theorem baseD_hasDerivAt {l x : ℝ} (hl : 1939/2000≤l)
    (hx : x∈Icc (1/10) (7/10)) : HasDerivAt (baseD l) (baseDD l x) x := by
  have hn := CircularNorm.d1_hasDerivAt (energy_pos hl hx)
  convert (((Real.hasDerivAt_cos x).const_mul l).const_add 1).sub
    (hn.const_mul radius) using 1 <;> dsimp [baseD,baseDD] <;> ring

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
  concave_of_deriv2 (fun x hx => base_hasDerivAt hl.1 hx)
    (fun x hx => baseD_hasDerivAt hl.1 hx) (fun x hx => (baseDD_neg hl hx).le)

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

/-- Six norm endpoint comparisons for the three actual multiplier choices. -/
theorem endpoint_norms :
    N (1939/2000) (1/10)<17/100 ∧ N (1939/2000) (7/10)<371/500 ∧
    N (21/20) (1/10)<173/1000 ∧ N (21/20) (7/10)<193/250 ∧
    N (39/40) (1/10)<337/2000 ∧ N (39/40) (7/10)<1859/2500 := by
  have hsmall := tenth_trig
  have hcap := cap_trig
  have h₁ := N_sq (l := (1939/2000:ℝ)) (x := (1/10:ℝ)) (by norm_num) (by norm_num)
  have h₂ := N_sq (l := (1939/2000:ℝ)) (x := (7/10:ℝ)) (by norm_num) (by norm_num)
  have h₃ := N_sq (l := (21/20:ℝ)) (x := (1/10:ℝ)) (by norm_num) (by norm_num)
  have h₄ := N_sq (l := (21/20:ℝ)) (x := (7/10:ℝ)) (by norm_num) (by norm_num)
  have h₅ := N_sq (l := (39/40:ℝ)) (x := (1/10:ℝ)) (by norm_num) (by norm_num)
  have h₆ := N_sq (l := (39/40:ℝ)) (x := (7/10:ℝ)) (by norm_num) (by norm_num)
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

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
  let c : ℝ := Real.pi/2+63/50+39/40-radius*primaryNorm
  have hleft : (157/200:ℝ)<c+base (39/40) (1/10) := by
    dsimp [c,base]
    linarith [tenth_trig.1,pi_hand_enclosure.1]
  have hright : (157/200:ℝ)<c+base (39/40) (7/10) := by
    dsimp [c,base]
    linarith [cap_trig.1,pi_hand_enclosure.1]
  have hm := base_endpoint_min (l := (39/40:ℝ)) (by norm_num) hx
  have hmin : (157/200:ℝ)-c<min (base (39/40) (1/10)) (base (39/40) (7/10)) :=
    lt_min (by linarith) (by linarith)
  change (157/200:ℝ)<c+base (39/40) x
  linarith

end SquaresInCircles.Eight.CommonQuarter.SineEnvelope
