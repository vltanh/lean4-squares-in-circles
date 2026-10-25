module

public import SquaresInCircles.Eight.Frames.High.LowAxialScalars
public import SquaresInCircles.Eight.Frames.Low.HighPositiveLate

/-!
# Eight squares: both high-source primary target signs below the quarter turn

The original weak margin bounds one explicit contact height.  On
the full angle interval `[-.4,0]` this height decreases to its aligned
value, and its cost has strictly negative derivative.  The continued
upper marker supplies a scalar comparison even when the contact
passes below the intrinsic diagonal; no physical recoding is used.
-/

section
/-!
## The original high-source primary axis in its quarter-rotated chart

The rotation is an identity for the original margin and cost.  It
does not choose a new separating owner or move either original
square.  The closed source chart includes both intrinsic cut ties.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowPrimaryGeometry
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus

def sourceDomain : Set ℝ := Icc c0 a2
def upperMargin (k : Bool) (z B x : ℝ) : ℝ :=
  z+A B*Real.sin x-sign k*B*Real.cos x-pairWidth x
def upperCost (k : Bool) (z B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+G z-sign k*L B

theorem source_extended {z : ℝ} (hz : z∈sourceDomain) : z∈extendedDomain := by
  constructor <;> linarith [hz.1,hz.2,c0_bounds.1,a2_bounds.2]

theorem source_chart {b : ℝ} (hb : b∈Icc b2 c0) : A b∈sourceDomain :=
  A_high_bounds hb

theorem rotated_margin (k : Bool) (b B x : ℝ) :
    primary k b B (Real.pi/2+x)=upperMargin k (A b) B x := by
  dsimp [primary,FrameLowMidGeometry.primary,upperMargin]
  rw [FrameLowHighQuarterStrip.quarter_width]
  simp only [Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,zero_sub]
  ring

theorem rotated_cost (k : Bool) {b : ℝ} (hb : b∈Icc b2 c0) (B x : ℝ) :
    highLowCost false k b B (Real.pi/2+x)=upperCost k (A b) B x := by
  dsimp [highLowCost,upperCost,sign]
  rw [FrameLowHighQuarterStrip.quarter_charge,quarter_label hb]
  ring

theorem rotated_angle {b B x : ℝ} (k : Bool)
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : -(34/125:ℝ)≤x) (hm : 0≤primary k b B x) :
    -(2/5:ℝ)<x-Real.pi/2 := by
  have hh := high_low_primary_cut k hb hB hx hm
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem Gd_monotone : MonotoneOn Gd extendedDomain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z hz => (Gd_deriv hz).continuousAt.continuousWithinAt
  · exact fun z hz => Gd_deriv (Ioo_subset_Icc_self hz)
  · intro z hz
    exact mul_nonneg (by norm_num [FrameHighArc.v])
      (slopeD_positive (Ioo_subset_Icc_self hz)).le

theorem source_Gd_lower {z : ℝ} (hz : z∈sourceDomain) :
    (480179/500000:ℝ)≤Gd z := by
  have hc : c0∈extendedDomain := by constructor <;> linarith [c0_bounds.1,c0_bounds.2]
  have hh := Gd_monotone hc (source_extended hz) hz.1
  simp only [Gd,FrameLowHighAligned.slope_c0] at hh ⊢
  norm_num [FrameHighArc.u,FrameHighArc.v] at hh ⊢
  linarith

theorem source_G_lower {z : ℝ} (hz : z∈sourceDomain) : Real.pi/4≤G z := by
  have hc : c0∈extendedDomain := by constructor <;> linarith [c0_bounds.1,c0_bounds.2]
  have hh := FrameLowHighQuarterCalculus.G_monotone hc (source_extended hz) hz.1
  simpa only [G_c0] using hh

theorem low_Ld_upper {B : ℝ} (hB : B∈Icc 0 b1) : Ld B<197/200 := by
  have hh := (slope_bounds hB).1
  dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
  linarith

theorem negative_target_tail {z B x : ℝ} (hz : z∈sourceDomain)
    (hB : B∈Icc 0 b1) (hx : (27/250:ℝ)≤x) :
    (8833/10000:ℝ)<upperCost false z B x := by
  have hc := FrameLowHighPositiveLate.charge_linear (show 0≤x by linarith)
  have hg := source_G_lower hz
  have hl := (L_bounds hB).1
  dsimp [upperCost,sign]
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem positive_target_tail {z B x : ℝ} (hz : z∈sourceDomain)
    (hB : B∈Icc 0 b1) (hx : (23/50:ℝ)≤x) :
    (8833/10000:ℝ)<upperCost true z B x := by
  have hc := CorePairGeometry.charge_upper x
  have hg := source_G_lower hz
  have hl := (L_bounds hB).2.2
  dsimp [upperCost,sign]
  linarith [Arithmetic.pi_hand_enclosure.1,L1_precise.2]

end SquaresInCircles.Eight.FrameHighLowPrimaryGeometry
end
end
end

section
/-!
## Aligned bounds for the continued upper high marker

The upper marker is evaluated analytically below its intrinsic
diagonal only in scalar comparisons.  The input squares keep their
original type coordinates.  Both target signs have a strict aligned
reserve on every low coordinate permitted by the contact.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowUpperAligned
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighAligned
open FrameHighLowPrimaryGeometry

def lowerDomain : Set ℝ := Icc (27/40:ℝ) a2

theorem lower_extended {z : ℝ} (hz : z∈lowerDomain) : z∈extendedDomain := by
  constructor <;> linarith [hz.1,hz.2,a2_bounds.2]

theorem lower_shift_upper {z : ℝ} (hz : z∈lowerDomain) : A z+1/2<8/5 := by
  have hc := extended_circle (lower_extended hz)
  have hzsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤47/40)
    (show (47/40:ℝ)≤z+1/2 by linarith [hz.1]) 2
  by_contra! hbad
  have hAsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8/5) hbad 2
  norm_num [Q0] at hc
  nlinarith

theorem lower_Gd {z : ℝ} (hz : z∈lowerDomain) : (17/20:ℝ)<Gd z := by
  have hp := extended_shift_pos (lower_extended hz)
  have hr : (47/64:ℝ)<slope z := by
    apply (lt_div_iff₀ hp).2
    linarith [lower_shift_upper hz,hz.1]
  dsimp [Gd,FrameHighArc.u,FrameHighArc.v]
  linarith

theorem lower_slopeD {z : ℝ} (hz : z∈lowerDomain) : (19/20:ℝ)<slopeD z := by
  have hp := extended_shift_pos (lower_extended hz)
  have hcube := pow_le_pow_left₀ hp.le (lower_shift_upper hz).le 3
  dsimp [slopeD]
  apply (lt_div_iff₀ (pow_pos hp 3)).2
  norm_num [Q0] at *
  nlinarith

theorem one_Gd : (1023/1000:ℝ)<Gd 1 := by
  have hz : (1:ℝ)∈extendedDomain := by constructor <;> norm_num [extendedDomain]
  have hp := extended_shift_pos hz
  have hc := extended_circle hz
  have hA : A 1+1/2<1291/1000 := by
    by_contra! hbad
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1291/1000) hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hr : (1500/1291:ℝ)<slope 1 := by
    apply (lt_div_iff₀ hp).2
    linarith
  dsimp [Gd,FrameHighArc.u,FrameHighArc.v]
  linarith

theorem one_G : (8833/10000:ℝ)<G 1 := by
  have hh := FrameHighLowAxialScalars.upper_lower
    (show (0:ℝ)∈FrameHighLowAxialGeometry.upperDomain by
      constructor <;> norm_num [FrameHighLowAxialGeometry.upperDomain])
  have he : FrameHighLowAxialCalculus.upperF 0=G 1 := by
    simp only [FrameHighLowAxialCalculus.upperF,FrameHighLowAxialGeometry.Z_zero,
      Real.sin_zero,Real.cos_zero]
    ring
  rwa [he] at hh

theorem positive_aligned {B : ℝ} (hB : B∈Icc 0 b1)
    (hz : 1+B≤a2) : (8833/10000:ℝ)<G (1+B)-L B := by
  have hm : MonotoneOn (fun t => G (1+t)-L t) (Icc 0 B) := by
    have hd : ∀ t∈Icc 0 B, HasDerivAt (fun t => G (1+t)-L t) (Gd (1+t)-Ld t) t := by
      intro t ht
      have htlow : t∈Icc 0 b1 := ⟨ht.1,ht.2.trans hB.2⟩
      have htext : 1+t∈extendedDomain := by
        constructor <;> linarith [ht.1,ht.2,hz,a2_bounds.2]
      exact (((G_deriv htext).comp t ((hasDerivAt_id' t).const_add 1)).fun_sub
        (extended_L_deriv (low_extended htlow))).congr_deriv (by ring)
    apply monoOn_of_hasDeriv_nonneg (d := fun t => Gd (1+t)-Ld t)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => hd t (Ioo_subset_Icc_self ht)
    · intro t ht
      have htlow : t∈Icc 0 b1 := ⟨ht.1.le,ht.2.le.trans hB.2⟩
      have htext : 1+t∈extendedDomain := by
        constructor <;> linarith [ht.1,ht.2,hz,a2_bounds.2]
      have hg := Gd_monotone
        (show (1:ℝ)∈extendedDomain by constructor <;> norm_num [extendedDomain])
        htext (by linarith [ht.1] : (1:ℝ)≤1+t)
      show 0≤Gd (1+t)-Ld t
      linarith [one_Gd,low_Ld_upper htlow]
  have hh := hm ⟨le_rfl,hB.1⟩ ⟨hB.1,le_rfl⟩ hB.1
  have hzero : G 1≤G (1+B)-L B := by simpa [L,A_zero] using hh
  exact one_G.trans_le hzero

theorem quarter_late_domain {B : ℝ} (hB : B∈Icc b0 b1) :
    B∈Icc 0 b1 ∧ 1-B∈lowerDomain := by
  exact ⟨⟨b0_low.1.trans hB.1,hB.2⟩,
    ⟨by linarith [hB.2,b1_bounds.2],by linarith [hB.1,b0_bounds.1,a2_bounds.1]⟩⟩

theorem quarter_late_deriv {B : ℝ} (hB : B∈Icc b0 b1) :
    HasDerivAt quarter (quarterD B) B := by
  have hd := quarter_late_domain hB
  have h := (extended_L_deriv (low_extended hd.1)).fun_add
    ((G_deriv (lower_extended hd.2)).comp B ((hasDerivAt_id' B).const_sub 1))
  exact h.congr_deriv (by simp only [quarterD]; ring)

theorem quarter_lateD_deriv {B : ℝ} (hB : B∈Icc b0 b1) :
    HasDerivAt quarterD (quarterDD B) B := by
  have hd := quarter_late_domain hB
  have h := (extended_Ld_deriv (low_extended hd.1)).fun_sub
    ((Gd_deriv (lower_extended hd.2)).comp B ((hasDerivAt_id' B).const_sub 1))
  exact h.congr_deriv (by simp only [quarterDD,Gdd]; ring)

theorem quarter_late_curvature {B : ℝ} (hB : B∈Icc b0 b1) :
    (9/100:ℝ)<quarterDD B := by
  have hd := quarter_late_domain hB
  have hs := low_slopeD_upper hd.1
  have ht := lower_slopeD hd.2
  dsimp [quarterDD,FrameLowArc.u,FrameHighArc.v]
  linarith

theorem quarter_late_lower {B : ℝ} (hB : B∈Icc b0 b1) : F0≤quarter B := by
  have hh := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (9/100:ℝ)) (fun t ht => quarter_late_deriv ht)
    (fun t ht => quarter_lateD_deriv ht) (fun t ht => (quarter_late_curvature ht).le)
    (show b0∈Icc b0 b1 from ⟨le_rfl,b0_low.2⟩) hB
  rw [quarter_initial.1,quarter_initial.2] at hh
  have hproduct := mul_nonneg d0_bounds.1.le (sub_nonneg.mpr hB.1)
  nlinarith [sq_nonneg (B-b0)]

theorem negative_aligned {B : ℝ} (hB : B∈Icc 0 b1) :
    (8833/10000:ℝ)<G (1-B)+L B := by
  by_cases he : B≤b0
  · have hh := quarter_reserve.trans_le (quarter_lower ⟨hB.1,he⟩)
    simpa [quarter,add_comm] using hh
  · have hh := quarter_late_lower ⟨le_of_not_ge he,hB.2⟩
    dsimp [quarter] at hh
    linarith [F0_lower]

end SquaresInCircles.Eight.FrameHighLowUpperAligned
end
end
end

section
/-!
## Exact upper-high / low circle support from the original primary margin

For every nonnegative multiplier below the actual upper-marker
slope, the source functional selects its intrinsic diagonal.  The
target is bounded by its complete shifted circle.  This identity is
shared by the constant and affine whole-angle scalar arguments.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowUpperSupport
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameHighLowPrimaryGeometry

def K : ℝ := 480179/500000
def energy (lam x : ℝ) : ℝ := FrameLowArc.u^2+FrameLowArc.v^2+lam^2+
  2*lam*(FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x)
def N (lam x : ℝ) : ℝ := Real.sqrt (energy lam x)
def F (lam x : ℝ) : ℝ :=
  x+9/100+Real.pi/4+FrameLowArc.u*a0+(FrameLowArc.u+FrameLowArc.v)/2+
    (1/2-c0)*lam+(lam-9/100)*Real.sin x-(9/100)*Real.cos x-R*N lam x

theorem energy_squares (lam x : ℝ) : energy lam x=
    (FrameLowArc.u+lam*Real.sin x)^2+(FrameLowArc.v-lam*Real.cos x)^2 := by
  dsimp [energy]
  linear_combination -lam^2*(Real.sin_sq_add_cos_sq x)

theorem N_nonneg (lam x : ℝ) : 0≤N lam x := Real.sqrt_nonneg _

theorem N_square (lam x : ℝ) : (N lam x)^2=energy lam x := by
  apply Real.sq_sqrt
  rw [energy_squares]
  positivity

theorem source_support {lam z : ℝ} (hlam : lam∈Icc 0 K) (hz : z∈sourceDomain) :
    Real.pi/4-lam*c0≤G z-lam*z := by
  have hm : MonotoneOn (fun t => G t-lam*t) sourceDomain := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => ((G_deriv (source_extended ht)).sub
        ((hasDerivAt_id t).const_mul lam)).continuousAt.continuousWithinAt
    · exact fun t ht => (G_deriv (source_extended (Ioo_subset_Icc_self ht))).sub
        ((hasDerivAt_id t).const_mul lam)
    · intro t ht
      have hh := source_Gd_lower (Ioo_subset_Icc_self ht)
      dsimp [K] at hlam
      linarith [hlam.2]
  have hstart : c0∈sourceDomain := ⟨le_rfl,by linarith [c0_bounds.2,a2_bounds.1]⟩
  simpa only [G_c0] using hm hstart hz hz.1

theorem circle_support {lam z B x : ℝ} (hlam : lam∈Icc 0 K)
    (hz : z∈sourceDomain) (hB : B∈Icc 0 b1) (hx : x∈Icc 0 (Real.pi/2))
    (hm : 0≤upperMargin true z B x) : F lam x≤upperCost true z B x := by
  have hsource := source_support hlam hz
  have hscaled := mul_nonneg hlam.1 hm
  have htarget := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (-FrameLowArc.u-lam*Real.sin x) (lam*Real.cos x-FrameLowArc.v)
  have hnorm : Real.sqrt ((-FrameLowArc.u-lam*Real.sin x)^2+
      (lam*Real.cos x-FrameLowArc.v)^2)=N lam x := by
    dsimp [N]
    congr 1
    rw [energy_squares]
    ring
  rw [hnorm] at htarget
  dsimp [upperMargin,sign] at hscaled
  rw [(first_width hx).1] at hscaled
  dsimp [F,upperCost,L,sign]
  rw [(first_width hx).2]
  nlinarith

end SquaresInCircles.Eight.FrameHighLowUpperSupport
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowPrimaryNegative
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus
open FrameHighLowPrimaryGeometry FrameHighLowUpperAligned

def domain : Set ℝ := Icc (-(2/5:ℝ)) 0
def W (x : ℝ) : ℝ := (1-Real.sin x+Real.cos x)/2
def height (k : Bool) (B x : ℝ) : ℝ :=
  W x-A B*Real.sin x+sign k*B*Real.cos x
def P (k : Bool) (B x : ℝ) : ℝ :=
  (A B+1/2)*Real.cos x+(1/2+sign k*B)*Real.sin x
def F (k : Bool) (B x : ℝ) : ℝ :=
  x-(9/50)*(W x-1)+G (height k B x)-sign k*L B
def Fd (k : Bool) (B x : ℝ) : ℝ :=
  1+(9/100)*(Real.cos x+Real.sin x)-Gd (height k B x)*P k B x

theorem width_actual {x : ℝ} (hx : x∈domain) :
    W x=pairWidth x ∧ W x-1=periodicFrameCost x := by
  have hh := negative_width
    (show x∈Icc (-(54/125:ℝ)) 0 from ⟨by linarith [hx.1],hx.2⟩)
  constructor
  · simpa [W] using hh.1.symm
  · rw [hh.2]
    dsimp [W]
    ring

theorem trig_bounds {x : ℝ} (hx : x∈domain) :
    -(2/5:ℝ)≤Real.sin x ∧ Real.sin x≤0 ∧ (23/25:ℝ)≤Real.cos x := by
  have hz : -x∈Icc (0:ℝ) (2/5) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,FrameLowPair.pi_lower])
  have hu := Real.sin_le hz.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hz.1 hz.2 2
  simp only [Real.sin_neg,neg_sq] at hs hu hsq
  refine ⟨?_,?_,?_⟩ <;> linarith [hz.2]

theorem height_deriv (k : Bool) (B x : ℝ) :
    HasDerivAt (height k B) (-P k B x) x := by
  have hw := (((Real.hasDerivAt_sin x).const_sub 1).fun_add (Real.hasDerivAt_cos x)).div_const 2
  have h := (hw.fun_sub ((Real.hasDerivAt_sin x).const_mul (A B))).fun_add
    ((Real.hasDerivAt_cos x).const_mul (sign k*B))
  exact h.congr_deriv (by simp only [P]; ring)

@[simp] theorem height_zero (k : Bool) (B : ℝ) : height k B 0=1+sign k*B := by
  simp [height,W]

theorem P_lower (k : Bool) {B x : ℝ} (hB : B∈Icc 0 b1) (hx : x∈domain) :
    (33/25:ℝ)<P k B x := by
  have ht := trig_bounds hx
  have hA := A_low_bounds hB
  have hAc := mul_le_mul
    (show (899/500:ℝ)≤A B+1/2 by linarith [hA.1,a1_precise.1]) ht.2.2
    (by norm_num : (0:ℝ)≤23/25) (by linarith [hA.1,a1_precise.1] : 0≤A B+1/2)
  have hcoef : 0≤1/2+sign k*B ∧ 1/2+sign k*B≤33/40 := by
    cases k <;> dsimp [sign] <;> constructor <;> linarith [hB.1,hB.2,b1_bounds.2]
  have hprod := mul_le_mul hcoef.2
    (show -Real.sin x≤2/5 by linarith [ht.1])
    (by linarith [ht.2.1] : 0≤-Real.sin x) (by norm_num : (0:ℝ)≤33/40)
  dsimp [P]
  nlinarith

theorem height_antitone (k : Bool) {B : ℝ} (hB : B∈Icc 0 b1) :
    AntitoneOn (height k B) domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (height_deriv k B x).continuousAt.continuousWithinAt
  · exact fun x _ => height_deriv k B x
  · intro x hx
    linarith [P_lower k hB (Ioo_subset_Icc_self hx)]

theorem contact_le (k : Bool) {z B x : ℝ} (hx : x∈domain)
    (hm : 0≤upperMargin k z B x) : height k B x≤z := by
  dsimp [height,upperMargin] at *
  rw [(width_actual hx).1]
  linarith

theorem contact_domain (k : Bool) {z B x t : ℝ}
    (hz : z∈sourceDomain) (hB : B∈Icc 0 b1) (hx : x∈domain)
    (hm : 0≤upperMargin k z B x) (ht : t∈Icc x 0) :
    height k B t∈lowerDomain := by
  have htd : t∈domain := ⟨hx.1.trans ht.1,ht.2⟩
  have hzero := height_antitone k hB htd
    (show (0:ℝ)∈domain by constructor <;> norm_num [domain]) ht.2
  have hstart := height_antitone k hB hx htd ht.1
  rw [height_zero] at hzero
  have hweak := contact_le k hx hm
  constructor
  · cases k <;> dsimp [sign] at hzero <;> linarith [hB.1,hB.2,b1_bounds.2]
  · linarith [hz.2]

theorem F_deriv (k : Bool) {B x : ℝ} (hz : height k B x∈lowerDomain) :
    HasDerivAt (F k B) (Fd k B x) x := by
  have hw := (((Real.hasDerivAt_sin x).const_sub 1).fun_add (Real.hasDerivAt_cos x)).div_const 2
  have h := (((hasDerivAt_id' x).fun_sub ((hw.sub_const 1).const_mul (9/50))).fun_add
    ((G_deriv (lower_extended hz)).comp x (height_deriv k B x))).sub_const (sign k*L B)
  exact h.congr_deriv (by simp only [Fd]; ring)

theorem Fd_negative (k : Bool) {B x : ℝ} (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hz : height k B x∈lowerDomain) : Fd k B x<0 := by
  have hp := P_lower k hB hx
  have hg := lower_Gd hz
  have hm := mul_le_mul hg.le hp.le (by norm_num : (0:ℝ)≤33/25)
    (by linarith : 0≤Gd (height k B x))
  dsimp [Fd]
  linarith [(trig_bounds hx).2.1,Real.cos_le_one x]

theorem move_to_zero (k : Bool) {z B x : ℝ} (hz : z∈sourceDomain)
    (hB : B∈Icc 0 b1) (hx : x∈domain) (hm : 0≤upperMargin k z B x) :
    F k B 0≤F k B x := by
  have ha : AntitoneOn (F k B) (Icc x 0) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun t ht => (F_deriv k (contact_domain k hz hB hx hm ht)).continuousAt.continuousWithinAt
    · exact fun t ht => F_deriv k (contact_domain k hz hB hx hm (Ioo_subset_Icc_self ht))
    · intro t ht
      exact (Fd_negative k hB ⟨hx.1.trans ht.1.le,ht.2.le⟩
        (contact_domain k hz hB hx hm (Ioo_subset_Icc_self ht))).le
  exact ha ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2

theorem weak_separator (k : Bool) {z B x : ℝ} (hz : z∈sourceDomain)
    (hB : B∈Icc 0 b1) (hx : x∈domain) (hm : 0≤upperMargin k z B x) :
    (8833/10000:ℝ)<upperCost k z B x := by
  have hzero := contact_domain k hz hB hx hm (show (0:ℝ)∈Icc x 0 from ⟨hx.2,le_rfl⟩)
  rw [height_zero] at hzero
  have hF0 : F k B 0=G (1+sign k*B)-sign k*L B := by
    simp only [F,height_zero,W,Real.sin_zero,Real.cos_zero]; ring
  have haligned : (8833/10000:ℝ)<F k B 0 := by
    rw [hF0]
    cases k
    · have hh := negative_aligned hB
      have he : (1:ℝ)+sign false*B=1-B := by simp only [sign]; norm_num; ring
      rw [he]
      simp only [sign]
      norm_num
      linarith
    · have he : (1:ℝ)+sign true*B=1+B := by simp [sign]
      rw [he] at hzero ⊢
      have hh := positive_aligned hB hzero.2
      simp only [sign]
      norm_num
      linarith
  have hpath := move_to_zero k hz hB hx hm
  have hcontact := contact_domain k hz hB hx hm ⟨le_rfl,hx.2⟩
  have hG := FrameLowHighQuarterCalculus.G_monotone (lower_extended hcontact)
    (source_extended hz) (contact_le k hx hm)
  have hcomparison : F k B x≤upperCost k z B x := by
    dsimp only [F,upperCost]
    rw [(width_actual hx).2]
    linarith
  exact haligned.trans_le (hpath.trans hcomparison)

end SquaresInCircles.Eight.FrameHighLowPrimaryNegative
end
end
end
