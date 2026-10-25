module

public import SquaresInCircles.Eight.Owners.CircularNorm
public import SquaresInCircles.Eight.Words.Common.QuarterState
public import SquaresInCircles.Eight.Words.Common.ZeroEndpoint
public import SquaresInCircles.Eight.Words.Common.ZeroSame

/-!
# Eight squares: all original secondary contacts with one quarter increment

The complete signed secondary matrix follows from three continuous circle
supports. Negative sources force the actual source transverse coordinate
below one half; hence a core source is on its original side. The remaining
negative-target and core-target supports have direct whole-angle bounds.
No preferred owner or new radial state is selected.
-/

section
/-!
## The three-endpoint envelope for common quarter-one secondary owners

The same exact norm curvature proves concavity on both complete signed
halves. Uniform norm bounds `N<3l/2` and `N<2l` give the two curvature
signs. The three actual multiplier choices are then evaluated only at
`-.7`, zero and `.7`.
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
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open WordProblems Arithmetic

def oneWidth (x : ℝ) : ℝ := (1+Real.cos x+|Real.sin x|)/2

theorem one_secondary_margin {x a b A B σ τ : ℝ} (hx : |x|≤7/10) :
    forwardMargin 0 a b A B σ τ (Real.pi/2+x)=
      σ*b+A*Real.cos x+τ*B*Real.sin x-oneWidth x := by
  simp [forwardMargin,quarter_width hx,oneWidth,Real.sin_add,Real.cos_add]

theorem one_primary_margin {x a b A B σ τ : ℝ} (hx : |x|≤7/10) :
    forwardMargin 3 a b A B σ τ (Real.pi/2+x)=
      a+A*Real.sin x-τ*B*Real.cos x-oneWidth x := by
  simp [forwardMargin,quarter_width hx,oneWidth,Real.sin_add,Real.cos_add]

theorem oneWidth_ge_one {x : ℝ} (hx : |x|≤7/10) : 1≤oneWidth x := by
  simpa [oneWidth,quarter_width hx] using width_ge_one (Real.pi/2+x)

theorem fine_outer_endpoint_bounds :
    2829/2000<outerAxial ∧ 899/1000<outerDiagonal := by
  constructor
  · dsimp only [outerAxial]
    have h : (3829/2000:ℝ)<Real.sqrt (Q0-1/4) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num [Q0]
    linarith
  · dsimp only [outerDiagonal]
    have h : (1399/1000:ℝ)<Real.sqrt (Q0/2) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num [Q0]
    linarith

theorem sine_max_identity (x : ℝ) :
    2*max (Real.sin x) 0=Real.sin x+|Real.sin x| := by
  by_cases hs : 0≤Real.sin x
  · rw [max_eq_left hs,abs_of_nonneg hs]
    ring
  · rw [max_eq_right (le_of_not_ge hs),abs_of_nonpos (le_of_not_ge hs)]
    ring

/-- The positive-to-negative marker signs already give a strict reserve. -/
theorem one_positive_negative {source target : RadialKind} {a b A B x : ℝ}
    (hs : State source a b) (ht : State target A B) (hx : |x|≤7/10) :
    (157/200:ℝ)<cost source target true false a b A B (Real.pi/2+x) := by
  have hsL := (state_label_bounds hs).1
  have htL := (state_label_bounds ht).1
  norm_num [cost,sign]
  linarith [(abs_le.mp hx).1,pi_hand_enclosure.1]

/-- An original negative secondary source has transverse coordinate below
one half, for either target tangent sign. -/
theorem one_negative_source_small {a b A B x : ℝ} (ht : OuterState A B)
    (τ : Bool) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (-1) (sign τ) (Real.pi/2+x)) : b<1/2 := by
  have hc := signed_cos hx
  have hcircle := outer_circle_lower (X := -Real.cos x) (Y := -|Real.sin x|) ht
  have hnorm : Real.sqrt ((-Real.cos x)^2+(-|Real.sin x|)^2)=1 := by
    have he : (-Real.cos x)^2+(-|Real.sin x|)^2=1 := by
      nlinarith [Real.sin_sq_add_cos_sq x,sq_abs (Real.sin x)]
    rw [he]
    norm_num
  rw [hnorm] at hcircle
  have hw := oneWidth_ge_one hx
  have hs₁ := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin x)) ht.1
  have hs₂ := mul_le_mul_of_nonneg_left (neg_le_abs (Real.sin x)) ht.1
  rw [one_secondary_margin hx] at hm
  dsimp [oneWidth] at hw hm
  cases τ <;> norm_num [sign] at hm <;> nlinarith [radius_bounds.2]

/-- The actual outer circle supplies exactly the norm in the three-point
secondary envelope; the minimizer is not required to lie on the arc. -/
lemma one_positive_target_support {A B x l : ℝ} (ht : OuterState A B) :
    ((27/25)+l*(Real.cos x+Real.sin x))/2-radius*OneEnvelope.N l x≤
      (-(13/200)-l*Real.cos x)*A+(-(203/200)-l*Real.sin x)*B := by
  have hh := outer_circle_lower (X := -(13/200)-l*Real.cos x)
    (Y := -(203/200)-l*Real.sin x) ht
  have he : Real.sqrt ((-(13/200)-l*Real.cos x)^2+
      (-(203/200)-l*Real.sin x)^2)=OneEnvelope.N l x := by
    dsimp [OneEnvelope.N,CircularNorm.norm]
    rw [OneEnvelope.energy_identity]
    congr 1
    ring
  rw [he] at hh
  linarith

lemma one_positive_outer_target {source : RadialKind} {a b A B x : ℝ}
    (_hs : State source a b) (ht : OuterState A B) (σ : Bool)
    (w : OneEnvelope.Weight) (hx : |x|≤7/10)
    (hsource : OneEnvelope.offset w≤(sign σ:ℝ)*label source a b-
      OneEnvelope.weight w*(sign σ:ℝ)*b+9/100)
    (hm : 0≤forwardMargin 0 a b A B (sign σ) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x+(sign σ:ℝ)*label source a b-outerLabel A B := by
  have htL := one_positive_target_support (x := x) (l := OneEnvelope.weight w) ht
  have hw := OneEnvelope.weight_bounds w
  have hl0 : 0≤OneEnvelope.weight w := by linarith [hw.1]
  rw [one_secondary_margin hx] at hm
  have hmul := mul_nonneg hl0 hm
  have hen := OneEnvelope.envelope_gt w hx
  have hmax := sine_max_identity x
  dsimp [OneEnvelope.envelope,oneWidth,outerLabel] at *
  nlinarith

lemma one_outer_positive_source_support {a b : ℝ} (hs : OuterState a b) :
    (919/10000:ℝ)≤outerLabel a b-(39/40)*b+9/100 := by
  have hh := outer_endpoints_lower (X := (13/200:ℝ)) (Y := (1/25:ℝ))
    (m := (919/10000:ℝ)) hs (by norm_num)
    (by linarith [fine_outer_endpoint_bounds.1])
    (by linarith [fine_outer_endpoint_bounds.2])
  dsimp [outerLabel]
  linarith

lemma one_outer_negative_source_support {a b : ℝ} (hs : OuterState a b) :
    (11/125:ℝ)≤ -outerLabel a b+(203/200)*b+9/100 := by
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  dsimp [outerLabel]
  linarith

/-- The weak original contact bounds the entire negative-target scalar,
even after the coarser common axial estimate. -/
lemma one_negative_target_scalar {x l : ℝ}
    (hl : l∈Icc (203/200) (291/250)) (hx : |x|≤7/10) :
    (157/200:ℝ)<Real.pi/2+x+l*oneWidth x-l*outerAxial*Real.cos x := by
  have hl0 : 0≤l := by linarith [hl.1]
  have ha : 9/10<outerAxial-1/2 := by linarith [fine_outer_endpoint_bounds.1]
  have hbase : (107/100:ℝ)<Real.pi/2+l-l*outerAxial := by
    have h₁ := mul_le_mul_of_nonneg_left outer_endpoint_bounds.2.1.le hl0
    have h₂ := mul_le_mul_of_nonneg_right hl.2 (show (0:ℝ)≤83/200 by norm_num)
    nlinarith [pi_hand_enclosure.1]
  by_cases hp : 0≤x
  · have ht := positive_trig ⟨hp,(abs_le.mp hx).2⟩
    have hsin := mul_nonneg hl0 ht.2.2.1
    have hcos := mul_nonneg (mul_nonneg hl0 (by linarith : 0≤outerAxial-1/2))
      (by linarith [ht.2.1] : 0≤1-Real.cos x)
    dsimp [oneWidth]
    rw [abs_of_nonneg ht.2.2.1]
    nlinarith
  · let z : ℝ := -x
    have hz : z∈Icc 0 (7/10) := ⟨by dsimp [z]; linarith,
      by dsimp [z]; linarith [(abs_le.mp hx).1]⟩
    have ht := positive_trig hz
    have hr := positive_taylor_reserves hz
    have hsin : (9/20)*z≤(l/2)*Real.sin z := by
      have h₁ := mul_le_mul_of_nonneg_left hr.1 (show 0≤l/2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_right (show (1:ℝ)≤l by linarith [hl.1]) hz.1
      nlinarith
    have hc : (2/5)*z^2≤l*(outerAxial-1/2)*(1-Real.cos z) := by
      have hc0 : 0≤1-Real.cos z := by linarith [ht.2.1]
      have h₁ := mul_le_mul_of_nonneg_right ha.le hc0
      have h₂ := mul_le_mul_of_nonneg_left h₁ hl0
      have h₃ := mul_le_mul_of_nonneg_left hr.2.1 (show 0≤(9/10)*l by positivity)
      have h₄ := mul_le_mul_of_nonneg_right (show (1:ℝ)≤l by linarith [hl.1]) (sq_nonneg z)
      nlinarith
    have hquad : -(121/640:ℝ)≤ -(11/20)*z+(2/5)*z^2 := by
      nlinarith [sq_nonneg (16*z-11)]
    have he : x= -z := by dsimp [z]; ring
    rw [he]
    dsimp [oneWidth]
    rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg ht.2.2.1]
    nlinarith

lemma one_negative_outer_target {source : RadialKind} {a b A B x l : ℝ}
    (_hs : State source a b) (ht : OuterState A B)
    (hl : l∈Icc (203/200) (291/250)) (hx : |x|≤7/10)
    (hsource : 0≤ -label source a b+l*b+outerLabel outerAxial 0)
    (hm : 0≤forwardMargin 0 a b A B (-1) (-1) (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-label source a b+outerLabel A B := by
  have hc := signed_cos hx
  have hsin := signed_sin hx
  have hl0 : 0≤l := by linarith [hl.1]
  have hX : (13/200)-l*Real.cos x≤0 := by
    have hh := mul_le_mul_of_nonneg_right hl.1 (by linarith [hc.1] : 0≤Real.cos x)
    nlinarith
  have hY : 0≤(203/200)+l*Real.sin x := by
    have hs : -(16106/25000:ℝ)<Real.sin x := by
      linarith [neg_le_abs (Real.sin x)]
    have hh := mul_le_mul_of_nonneg_left hs.le hl0
    nlinarith [hl.2]
  have ha := mul_le_mul_of_nonpos_left (outer_bounds ht).2.1 hX
  have hb := mul_nonneg hY ht.1
  rw [one_secondary_margin hx] at hm
  have hm' := mul_nonneg hl0 hm
  have hscalar := one_negative_target_scalar hl hx
  dsimp [outerLabel] at *
  nlinarith

lemma one_positive_source_uniform {source : RadialKind} {a b : ℝ}
    (hs : State source a b) :
    -(9/100)-(21/250)*outerDiagonal≤label source a b-(291/250)*b := by
  by_cases hk : source=.outer
  · have hs' : OuterState a b := by simpa [State,hk] using hs
    have hb := outer_bounds hs'
    simp only [label,ite_eq_left hk,outerLabel]
    nlinarith [hb.1,hb.2.2.2.1]
  · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hk] using hs
    simp only [label,ite_eq_right hk]
    linarith [core_label_lower hs',outer_endpoint_bounds.2.2.1]

lemma one_core_target_change {x : ℝ} (hx : |x|≤7/10) :
    0≤x+(291/250)*(oneWidth x-1)-
      (291/250)*CoreAngleEndpoint.diagonal*(Real.cos x+Real.sin x-1) := by
  have hd := CoreAngleEndpoint.diagonal_bounds
  by_cases hp : 0≤x
  · have ht := positive_trig ⟨hp,(abs_le.mp hx).2⟩
    have hsum : 0≤Real.sin x+Real.cos x-1 := by linarith [ht.2.2.2.2.2]
    have hupper : Real.sin x+Real.cos x-1≤x := by
      linarith [ht.2.1,ht.2.2.2.2.1]
    have hm := mul_le_mul_of_nonneg_left hupper
      (show 0≤(291/250)*(CoreAngleEndpoint.diagonal-1/2) by nlinarith [hd.1])
    have hx' := mul_nonneg hp (show 0≤1-(291/250)*(CoreAngleEndpoint.diagonal-1/2) by nlinarith [hd.2])
    dsimp [oneWidth]
    rw [abs_of_nonneg ht.2.2.1]
    nlinarith
  · let z : ℝ := -x
    have hz : z∈Icc 0 (7/10) := ⟨by dsimp [z]; linarith,
      by dsimp [z]; linarith [(abs_le.mp hx).1]⟩
    have ht := positive_trig hz
    have hs := (positive_taylor_reserves hz).1
    have hsin := mul_le_mul_of_nonneg_left hs
      (show 0≤(291/250)*(CoreAngleEndpoint.diagonal+1/2) by nlinarith [hd.1])
    have hcoef := mul_nonneg hz.1
      (show 0≤(9/10)*(291/250)*(CoreAngleEndpoint.diagonal+1/2)-1 by nlinarith [hd.1])
    have hcos := mul_nonneg
      (show 0≤(291/250)*(CoreAngleEndpoint.diagonal-1/2) by nlinarith [hd.1])
      (by linarith [ht.2.1] : 0≤1-Real.cos z)
    have he : x= -z := by dsimp [z]; ring
    rw [he]
    dsimp [oneWidth]
    rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg ht.2.2.1]
    nlinarith

lemma one_positive_core_target {source : RadialKind} {a b A B x : ℝ}
    (hs : State source a b) (ht : CorePairGeometry.CoreState A B)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x+label source a b-coreLabel A B := by
  have hc := signed_cos hx
  have hsin := signed_sin hx
  have hX : 0≤(73/10)-(291/250)*Real.cos x := by linarith [hc.2]
  have hY : -(291/250)*(1+Real.sin x)≤0 := by
    have hs : -(16106/25000:ℝ)<Real.sin x := by
      linarith [neg_le_abs (Real.sin x)]
    linarith
  have htarget := core_diagonal_lower (X := (73/10)-(291/250)*Real.cos x)
    (Y := -(291/250)*(1+Real.sin x)) ht hX hY
  have hsource := one_positive_source_uniform hs
  have hchange := one_core_target_change hx
  have hdiag : CorePairGeometry.CoreState CoreAngleEndpoint.diagonal CoreAngleEndpoint.diagonal :=
    JumpTwo.diagonal_core
  have hlabel := (core_label_bounds hdiag).2
  rw [one_secondary_margin hx] at hm
  have hm' := mul_nonneg (show (0:ℝ)≤291/250 by norm_num) hm
  dsimp [coreLabel] at *
  nlinarith [outer_endpoint_bounds.2.2.2,CoreAngleEndpoint.diagonal_bounds.2,
    pi_hand_enclosure.1]

/-- Every original source-secondary owner with a quarter increment of one.
The side/corner join and both tangent tie choices are included. -/
theorem one_secondary_cost {source target : RadialKind} {a b A B x : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (sign σ) (sign τ) (Real.pi/2+x)) :
    (157/200:ℝ)<cost source target σ τ a b A B (Real.pi/2+x) := by
  by_cases hto : target=.outer
  · have ht' : OuterState A B := by simpa [State,hto] using ht
    cases σ <;> cases τ
    · have hm' : 0≤forwardMargin 0 a b A B (-1) (-1) (Real.pi/2+x) := by
        simpa [sign] using hm
      have hb := one_negative_source_small ht' false hx (by simpa [sign] using hm')
      by_cases hso : source=.outer
      · have hs' : OuterState a b := by simpa [State,hso] using hs
        have hsupport : 0≤ -label source a b+(203/200)*b+outerLabel outerAxial 0 := by
          simp only [label,ite_eq_left hso,outerLabel]
          nlinarith [(outer_bounds hs').2.1]
        have hh := one_negative_outer_target hs ht' (l := (203/200:ℝ))
          (by norm_num) hx hsupport hm'
        simp [cost,sign,label,hto,hso] at hh ⊢
        linarith
      · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
        have hside := (core_small_side hs' hb).2
        have hsupport : 0≤ -label source a b+(291/250)*b+outerLabel outerAxial 0 := by
          simp only [label,ite_eq_right hso,hside,outerLabel]
          linarith [fine_outer_endpoint_bounds.1]
        have hh := one_negative_outer_target hs ht' (l := (291/250:ℝ))
          (by norm_num) hx hsupport hm'
        simp [cost,sign,label,hto,hso] at hh ⊢
        linarith
    · have hm' : 0≤forwardMargin 0 a b A B (-1) 1 (Real.pi/2+x) := by
        simpa [sign] using hm
      have hb := one_negative_source_small ht' true hx (by simpa [sign] using hm')
      by_cases hso : source=.outer
      · have hs' : OuterState a b := by simpa [State,hso] using hs
        have hh := one_positive_outer_target hs ht' false .outerNegative hx
          (by simpa [OneEnvelope.offset,OneEnvelope.weight,sign,label,hso] using
            one_outer_negative_source_support hs') (by simpa [sign] using hm)
        simpa [cost,sign,label,hto] using hh
      · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
        have hside := (core_small_side hs' hb).2
        have hh := one_positive_outer_target hs ht' false .core hx
          (by simp [OneEnvelope.offset,OneEnvelope.weight,sign,label,hso,hside])
          (by simpa [sign] using hm)
        simpa [cost,sign,label,hto] using hh
    · exact one_positive_negative hs ht hx
    · have hm' : 0≤forwardMargin 0 a b A B 1 1 (Real.pi/2+x) := by
        simpa [sign] using hm
      by_cases hso : source=.outer
      · have hs' : OuterState a b := by simpa [State,hso] using hs
        have hh := one_positive_outer_target hs ht' true .outerPositive hx
          (by simpa [OneEnvelope.offset,OneEnvelope.weight,sign,label,hso] using
            one_outer_positive_source_support hs') (by simpa [sign] using hm)
        simpa [cost,sign,label,hto] using hh
      · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
        have hh := one_positive_outer_target hs ht' true .core hx
          (by simp only [OneEnvelope.offset,OneEnvelope.weight,sign,label,ite_eq_right hso,
              ↓reduceIte,Rat.cast_one,one_mul]
              linarith [core_label_lower hs']) (by simpa [sign] using hm)
        simpa [cost,sign,label,hto] using hh
  · have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
    cases σ
    · exact (negative_source_core_target_false τ (state_bounds hs).2.2.1 ht'
        (by simpa [sign] using hm)).elim
    · cases τ
      · exact one_positive_negative hs ht hx
      · have hh := one_positive_core_target hs ht' hx (by simpa [sign] using hm)
        simpa [cost,sign,label,hto] using hh

end SquaresInCircles.Eight.CommonQuarter
end
end
end
