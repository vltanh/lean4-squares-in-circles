module

public import SquaresInCircles.Eight.TableFree.CommonQuarterTrig
public import SquaresInCircles.Eight.TableFree.CircularNorm

/-!
# The three-endpoint envelope for common quarter-one secondary owners

The same exact norm curvature proves concavity on both complete signed
halves. Uniform norm bounds `N<3l/2` and `N<2l` give the two curvature
signs. The three actual multiplier choices are then evaluated only at
`-.7`, zero and `.7`.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter.OneEnvelope

open Arithmetic

inductive Weight | outerPositive | outerNegative | core
  deriving DecidableEq

instance : Fintype Weight where
  elems := {.outerPositive, .outerNegative, .core}
  complete x := by cases x <;> decide

def weight : Weight→ℝ
  | .outerPositive => 39/40
  | .outerNegative => 203/200
  | .core => 291/250

def offset : Weight→ℝ
  | .outerPositive => 919/10000
  | .outerNegative => 11/125
  | .core => 9/100

def mass (l : ℝ) : ℝ := (13/200)^2+(203/200)^2+l^2
def cosCoeff (l : ℝ) : ℝ := 2*l*(13/200)
def sinCoeff (l : ℝ) : ℝ := 2*l*(203/200)
def N (l x : ℝ) : ℝ := CircularNorm.norm (mass l) (cosCoeff l) (sinCoeff l) x

def negativeBase (l x : ℝ) : ℝ := x+l*Real.cos x-radius*N l x

def positiveBase (l x : ℝ) : ℝ := x+l*(Real.cos x+Real.sin x)-radius*N l x

def negativeD (l x : ℝ) : ℝ :=
  1-l*Real.sin x-radius*CircularNorm.d1 (mass l) (cosCoeff l) (sinCoeff l) x

def positiveD (l x : ℝ) : ℝ :=
  1+l*(Real.cos x-Real.sin x)-radius*CircularNorm.d1 (mass l) (cosCoeff l) (sinCoeff l) x

def negativeDD (l x : ℝ) : ℝ :=
  -l*Real.cos x-radius*CircularNorm.d2 (mass l) (cosCoeff l) (sinCoeff l) x

def positiveDD (l x : ℝ) : ℝ :=
  -l*(Real.cos x+Real.sin x)-radius*CircularNorm.d2 (mass l) (cosCoeff l) (sinCoeff l) x

def envelope (w : Weight) (x : ℝ) : ℝ :=
  Real.pi/2+x+offset w+((27/25)+weight w)/2+
    weight w*Real.cos x+weight w*max (Real.sin x) 0-radius*N (weight w) x

theorem weight_bounds (w : Weight) : weight w∈Icc (39/40) (291/250) := by
  cases w <;> norm_num [weight]

theorem energy_identity (l x : ℝ) :
    CircularNorm.energy (mass l) (cosCoeff l) (sinCoeff l) x=
      ((13/200)+l*Real.cos x)^2+((203/200)+l*Real.sin x)^2 := by
  dsimp [CircularNorm.energy,mass,cosCoeff,sinCoeff]
  linear_combination -(l^2)*(Real.sin_sq_add_cos_sq x)

theorem energy_pos {l x : ℝ} (hl : l∈Icc (39/40) (291/250)) (hx : |x|≤7/10) :
    0<CircularNorm.energy (mass l) (cosCoeff l) (sinCoeff l) x := by
  have hc : 0<Real.cos x := by linarith [(signed_cos hx).1]
  have hl0 : 0<l := by linarith [hl.1]
  have hpos : 0<(13/200:ℝ)+l*Real.cos x := by positivity
  rw [energy_identity]
  nlinarith [sq_pos_of_pos hpos,sq_nonneg ((203/200:ℝ)+l*Real.sin x)]

theorem N_pos {l x : ℝ} (hl : l∈Icc (39/40) (291/250)) (hx : |x|≤7/10) : 0<N l x :=
  CircularNorm.norm_pos (energy_pos hl hx)

theorem N_sq {l x : ℝ} (hl : l∈Icc (39/40) (291/250)) (hx : |x|≤7/10) :
    (N l x)^2=(13/200:ℝ)^2+(203/200)^2+l^2+
      2*l*((13/200)*Real.cos x+(203/200)*Real.sin x) := by
  have hh := CircularNorm.norm_sq (energy_pos hl hx).le
  rw [N,hh]
  simp only [CircularNorm.energy,mass,cosCoeff,sinCoeff]
  ring

theorem coefficient_square (l : ℝ) :
    (cosCoeff l)^2+(sinCoeff l)^2≤(mass l)^2 := by
  have hid : (mass l)^2-(cosCoeff l)^2-(sinCoeff l)^2=
      ((13/200:ℝ)^2+(203/200)^2-l^2)^2 := by
    dsimp [mass,cosCoeff,sinCoeff]
    ring
  nlinarith [sq_nonneg ((13/200:ℝ)^2+(203/200)^2-l^2)]

theorem negative_norm_bound {l x : ℝ} (hl : l∈Icc (39/40) (291/250))
    (hx : x∈Icc (-(7/10)) 0) : N l x<(3/2)*l := by
  have ha : |x|≤7/10 := abs_le.mpr ⟨hx.1,by linarith [hx.2]⟩
  have hs : Real.sin x≤0 := by
    have hh := positive_trig (x := -x) ⟨by linarith [hx.2],by linarith [hx.1]⟩
    simpa only [Real.sin_neg,neg_nonneg] using hh.2.2.1
  have hc := Real.cos_le_one x
  have hl0 : 0≤l := by linarith [hl.1]
  have hsin := mul_nonpos_of_nonneg_of_nonpos (show 0≤(203/100)*l by positivity) hs
  have hcos := mul_le_mul_of_nonneg_left hc (show 0≤(13/100)*l by positivity)
  have hl2 := pow_le_pow_left₀ (show (0:ℝ)≤39/40 by norm_num) hl.1 2
  have hN := N_sq hl ha
  nlinarith [N_pos hl ha,hl.2]

theorem positive_norm_bound {l x : ℝ} (hl : l∈Icc (39/40) (291/250))
    (hx : x∈Icc 0 (7/10)) : N l x<2*l := by
  have ha : |x|≤7/10 := by rw [abs_of_nonneg hx.1]; exact hx.2
  have ht := positive_trig hx
  have hl0 : 0≤l := by linarith [hl.1]
  have hsin := mul_le_mul_of_nonneg_left ht.2.2.2.1.le
    (show 0≤(203/100)*l by positivity)
  have hcos := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤(13/100)*l by positivity)
  have hl2 := pow_le_pow_left₀ (show (0:ℝ)≤39/40 by norm_num) hl.1 2
  have hN := N_sq hl ha
  nlinarith [N_pos hl ha,hl.2]

theorem negative_hasDerivAt {l x : ℝ} (hl : l∈Icc (39/40) (291/250)) (hx : |x|≤7/10) :
    HasDerivAt (negativeBase l) (negativeD l x) x := by
  have hn := CircularNorm.norm_hasDerivAt (energy_pos hl hx)
  have h := ((hasDerivAt_id x).add ((Real.hasDerivAt_cos x).const_mul l)).sub
    (hn.const_mul radius)
  convert h using 1
  · funext y
    simp only [negativeBase,N,Pi.add_apply,Pi.sub_apply,id]
  · simp only [negativeD]
    ring

theorem positive_hasDerivAt {l x : ℝ} (hl : l∈Icc (39/40) (291/250)) (hx : |x|≤7/10) :
    HasDerivAt (positiveBase l) (positiveD l x) x := by
  have hn := CircularNorm.norm_hasDerivAt (energy_pos hl hx)
  have h := ((hasDerivAt_id x).add
    (((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).const_mul l)).sub
    (hn.const_mul radius)
  convert h using 1
  · funext y
    simp only [positiveBase,N,Pi.add_apply,Pi.sub_apply,id]
  · simp only [positiveD]
    ring

theorem negativeD_hasDerivAt {l x : ℝ} (hl : l∈Icc (39/40) (291/250)) (hx : |x|≤7/10) :
    HasDerivAt (negativeD l) (negativeDD l x) x := by
  have hn := CircularNorm.d1_hasDerivAt (energy_pos hl hx)
  have h := (((Real.hasDerivAt_sin x).const_mul l).const_sub 1).sub
    (hn.const_mul radius)
  convert h using 1
  · funext y
    simp only [negativeD,Pi.sub_apply]
  · simp only [negativeDD]
    ring

theorem positiveD_hasDerivAt {l x : ℝ} (hl : l∈Icc (39/40) (291/250)) (hx : |x|≤7/10) :
    HasDerivAt (positiveD l) (positiveDD l x) x := by
  have hn := CircularNorm.d1_hasDerivAt (energy_pos hl hx)
  have h := ((((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).const_mul l).const_add 1).sub
    (hn.const_mul radius)
  convert h using 1
  · funext y
    simp only [positiveD,Pi.sub_apply]
  · simp only [positiveDD]
    ring

theorem negativeDD_neg {l x : ℝ} (hl : l∈Icc (39/40) (291/250))
    (hx : x∈Icc (-(7/10)) 0) : negativeDD l x<0 := by
  have ha : |x|≤7/10 := abs_le.mpr ⟨hx.1,by linarith [hx.2]⟩
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hl0 : 0<l := by linarith [hl.1]
  have hc := mul_lt_mul_of_pos_left (signed_cos ha).1 hl0
  have hN := CircularNorm.curvature_lower (energy_pos hl ha) (coefficient_square l)
  have hmul := mul_le_mul_of_nonneg_left hN hR.le
  have hRN := mul_lt_mul_of_pos_left (negative_norm_bound hl hx) hR
  have hRl := mul_lt_mul_of_pos_right (show radius<2 by linarith [radius_bounds.2]) hl0
  change radius*(-(N l x)/4)≤radius*
    CircularNorm.d2 (mass l) (cosCoeff l) (sinCoeff l) x at hmul
  dsimp [negativeDD]
  nlinarith

theorem positiveDD_neg {l x : ℝ} (hl : l∈Icc (39/40) (291/250))
    (hx : x∈Icc 0 (7/10)) : positiveDD l x<0 := by
  have ha : |x|≤7/10 := by rw [abs_of_nonneg hx.1]; exact hx.2
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hl0 : 0<l := by linarith [hl.1]
  have ht := mul_le_mul_of_nonneg_left (positive_trig hx).2.2.2.2.2 hl0.le
  have hN := CircularNorm.curvature_lower (energy_pos hl ha) (coefficient_square l)
  have hmul := mul_le_mul_of_nonneg_left hN hR.le
  have hRN := mul_lt_mul_of_pos_left (positive_norm_bound hl hx) hR
  have hRl := mul_lt_mul_of_pos_right (show radius<2 by linarith [radius_bounds.2]) hl0
  change radius*(-(N l x)/4)≤radius*
    CircularNorm.d2 (mass l) (cosCoeff l) (sinCoeff l) x at hmul
  dsimp [positiveDD]
  nlinarith

theorem negative_concave {l : ℝ} (hl : l∈Icc (39/40) (291/250)) :
    ConcaveOn ℝ (Icc (-(7/10)) 0) (negativeBase l) :=
  concave_of_deriv2
    (fun x hx => negative_hasDerivAt hl (abs_le.mpr ⟨hx.1,by linarith [hx.2]⟩))
    (fun x hx => negativeD_hasDerivAt hl (abs_le.mpr ⟨hx.1,by linarith [hx.2]⟩))
    (fun x hx => (negativeDD_neg hl hx).le)

theorem positive_concave {l : ℝ} (hl : l∈Icc (39/40) (291/250)) :
    ConcaveOn ℝ (Icc 0 (7/10)) (positiveBase l) :=
  concave_of_deriv2
    (fun x hx => positive_hasDerivAt hl (by rw [abs_of_nonneg hx.1]; exact hx.2))
    (fun x hx => positiveD_hasDerivAt hl (by rw [abs_of_nonneg hx.1]; exact hx.2))
    (fun x hx => (positiveDD_neg hl hx).le)

def leftNorm : Weight→ℝ
  | .outerPositive => 9/10 | .outerNegative => 229/250 | .core => 124/125

def middleNorm : Weight→ℝ
  | .outerPositive => 727/500 | .outerNegative => 1483/1000 | .core => 797/500

def rightNorm : Weight→ℝ
  | .outerPositive => 37/20 | .outerNegative => 187/100 | .core => 2007/1000

theorem endpoint_norms (w : Weight) :
    N (weight w) (-(7/10))<leftNorm w ∧ N (weight w) 0< middleNorm w ∧
      N (weight w) (7/10)<rightNorm w := by
  have hL := N_sq (weight_bounds w) (x := -(7/10:ℝ)) (by norm_num)
  have hM := N_sq (weight_bounds w) (x := (0:ℝ)) (by norm_num)
  have hU := N_sq (weight_bounds w) (x := (7/10:ℝ)) (by norm_num)
  have ht := cap_trig
  simp only [Real.sin_neg,Real.cos_neg,Real.sin_zero,Real.cos_zero] at hL hM
  cases w <;> norm_num [weight,leftNorm,middleNorm,rightNorm] at * <;>
    refine ⟨?_,?_,?_⟩ <;> nlinarith

lemma scaled_endpoint_norms (w : Weight) :
    radius*N (weight w) (-(7/10))<(1979/1000)*leftNorm w ∧
      radius*N (weight w) 0<(1979/1000)*middleNorm w ∧
      radius*N (weight w) (7/10)<(1979/1000)*rightNorm w := by
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hl : 0<leftNorm w := by cases w <;> norm_num [leftNorm]
  have hm : 0< middleNorm w := by cases w <;> norm_num [middleNorm]
  have hu : 0<rightNorm w := by cases w <;> norm_num [rightNorm]
  exact ⟨(mul_lt_mul_of_pos_left (endpoint_norms w).1 hR).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 hl),
    (mul_lt_mul_of_pos_left (endpoint_norms w).2.1 hR).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 hm),
    (mul_lt_mul_of_pos_left (endpoint_norms w).2.2 hR).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 hu)⟩

theorem endpoint_envelopes (w : Weight) :
    (157/200:ℝ)<envelope w (-(7/10)) ∧
      (157/200:ℝ)<envelope w 0 ∧ (157/200:ℝ)<envelope w (7/10) := by
  have hs := scaled_endpoint_norms w
  have ht := cap_trig
  have hneg : max (Real.sin (-(7/10:ℝ))) 0=0 :=
    max_eq_right (by rw [Real.sin_neg]; linarith [ht.1])
  have hpos : max (Real.sin (7/10:ℝ)) 0=Real.sin (7/10) := max_eq_left (by linarith [ht.1])
  have hzero : max (Real.sin (0:ℝ)) 0=0 := by simp
  simp only [envelope,hneg,hpos,hzero,Real.cos_neg,Real.cos_zero]
  cases w <;> simp only [weight,offset,leftNorm,middleNorm,rightNorm] at hs ⊢ <;>
    refine ⟨?_,?_,?_⟩ <;> linarith [pi_hand_enclosure.1]

/-- Complete three-endpoint conclusion for each actual multiplier. -/
theorem envelope_gt (w : Weight) {x : ℝ} (hx : |x|≤7/10) :
    (157/200:ℝ)<envelope w x := by
  let c : ℝ := Real.pi/2+offset w+((27/25)+weight w)/2
  have hends := endpoint_envelopes w
  by_cases hp : 0≤x
  · have hx' : x∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hx).2⟩
    have ht := positive_trig hx'
    have he : envelope w x=c+positiveBase (weight w) x := by
      dsimp [envelope,c,positiveBase]
      rw [max_eq_left ht.2.2.1]
      ring
    have h₀ : (157/200:ℝ)-c<positiveBase (weight w) 0 := by
      have hh := hends.2.1
      simp only [envelope,Real.cos_zero,Real.sin_zero,max_self] at hh
      dsimp only [c,positiveBase]
      simp only [Real.cos_zero,Real.sin_zero]
      linarith
    have h₁ : (157/200:ℝ)-c<positiveBase (weight w) (7/10) := by
      have ht7 : 0≤Real.sin (7/10:ℝ) := by linarith [cap_trig.1]
      dsimp [envelope] at hends
      rw [max_eq_left ht7] at hends
      dsimp [c,positiveBase]
      linarith [hends.2.2]
    have hm := (positive_concave (weight_bounds w)).min_le_of_mem_Icc
      (by norm_num) (by norm_num) hx'
    rw [he]
    linarith [lt_min h₀ h₁]
  · have hx' : x∈Icc (-(7/10)) 0 := ⟨(abs_le.mp hx).1,by linarith⟩
    have hs : Real.sin x≤0 := by
      have ht := positive_trig (x := -x) ⟨by linarith,by linarith [hx'.1]⟩
      simpa only [Real.sin_neg,neg_nonneg] using ht.2.2.1
    have he : envelope w x=c+negativeBase (weight w) x := by
      dsimp [envelope,c,negativeBase]
      rw [max_eq_right hs]
      ring
    have h₀ : (157/200:ℝ)-c<negativeBase (weight w) (-(7/10)) := by
      have ht7 : Real.sin (-(7/10:ℝ))≤0 := by rw [Real.sin_neg]; linarith [cap_trig.1]
      have hh := hends.1
      dsimp [envelope] at hh
      rw [max_eq_right ht7] at hh
      dsimp [c,negativeBase]
      linarith
    have h₁ : (157/200:ℝ)-c<negativeBase (weight w) 0 := by
      have hh := hends.2.1
      norm_num [envelope,c,negativeBase] at hh ⊢
      linarith
    have hm := (negative_concave (weight_bounds w)).min_le_of_mem_Icc
      (by norm_num) (by norm_num) hx'
    rw [he]
    linarith [lt_min h₀ h₁]

/-- The stronger aligned baseline used by the mixed primary regimes. -/
theorem core_baseline : (792269/1000000:ℝ)<envelope .core 0 := by
  have h := (scaled_endpoint_norms .core).2.1
  norm_num [envelope,weight,offset,middleNorm] at h ⊢
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.CommonQuarter.OneEnvelope
