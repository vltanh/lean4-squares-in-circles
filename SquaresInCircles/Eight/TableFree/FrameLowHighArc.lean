module

public import SquaresInCircles.Eight.TableFree.FrameHighArc
public import SquaresInCircles.Eight.TableFree.FrameLowMidArc

/-!
# Circle calculus for the complete low/high pair

The ordinary low and high arcs and the continued circle used at a
quarter-turn contact share the same exact shifted-circle chart.
The continued interval is analytic data only; actual states retain
their original intrinsic type cuts.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighArc
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc

def extendedDomain : Set ℝ := Icc (-(1/4:ℝ)) (6/5)
def slopeD (b : ℝ) : ℝ := Q0/(A b+1/2)^3
def G (b : ℝ) : ℝ := Real.pi/4-(FrameHighArc.u-FrameHighArc.v)*c0-
  FrameHighArc.v*A b+FrameHighArc.u*b
def Gd (b : ℝ) : ℝ := FrameHighArc.v*slope b+FrameHighArc.u
def Gdd (b : ℝ) : ℝ := FrameHighArc.v*slopeD b

theorem diagonal_precise : (179842813/200000000:ℝ)<c0 ∧ c0<449607033/500000000 := by
  have hc := c0_circle
  have hp := c0_bounds.1
  norm_num [Q0] at hc
  constructor <;> by_contra! hbad <;> nlinarith

theorem high_constant_lower : (9459/10000:ℝ)<FrameHighArc.k := by
  dsimp [FrameHighArc.k,FrameHighArc.u,FrameHighArc.v]
  linarith [diagonal_precise.1,Arithmetic.pi_hand_enclosure.1]

theorem high_label_endpoint : (23197/50000:ℝ)<FrameHighArc.H2 := by
  have hp := Arithmetic.pi_hand_enclosure.1
  have hc := diagonal_precise.1
  have ha := a2_bounds
  dsimp [FrameHighArc.H2,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v,b2]
  linarith

theorem extended_radicand {b : ℝ} (hb : b∈extendedDomain) :
    0<Q0-(b+1/2)^2 := by
  have hbl : (1/4:ℝ)≤b+1/2 := by dsimp [extendedDomain] at hb; linarith [hb.1]
  have hbu : b+1/2≤17/10 := by dsimp [extendedDomain] at hb; linarith [hb.2]
  have hh := pow_le_pow_left₀ (by linarith : 0≤b+1/2) hbu 2
  norm_num [Q0]
  nlinarith

theorem extended_shift_pos {b : ℝ} (hb : b∈extendedDomain) : 0<A b+1/2 := by
  simpa [A] using Real.sqrt_pos.mpr (extended_radicand hb)

theorem extended_circle {b : ℝ} (hb : b∈extendedDomain) :
    (A b+1/2)^2+(b+1/2)^2=Q0 := by
  have hh := Real.sq_sqrt (extended_radicand hb).le
  dsimp [A]
  nlinarith

theorem extended_A_deriv {b : ℝ} (hb : b∈extendedDomain) : HasDerivAt A (Ad b) b := by
  have hh := ((hasDerivAt_const b Q0).sub
    (((hasDerivAt_id b).add_const (1/2)).pow 2)).sqrt (extended_radicand hb).ne'
  convert hh.sub_const (1/2) using 1
  · rfl
  · dsimp [Ad,A]; ring

theorem extended_Ad_deriv {b : ℝ} (hb : b∈extendedDomain) :
    HasDerivAt Ad (Add b) b := by
  have hd := extended_A_deriv hb
  have hn := (extended_shift_pos hb).ne'
  have hc := extended_circle hb
  have hh := (((hasDerivAt_id' b).add_const (1/2)).fun_neg).fun_div (hd.add_const (1/2)) hn
  unfold Ad
  convert hh using 1
  simp only [FrameCircleArc.Add,Ad]
  rw [← hc]
  field_simp
  ring

theorem slope_deriv {b : ℝ} (hb : b∈extendedDomain) :
    HasDerivAt slope (slopeD b) b := by
  have he : FrameLowArc.slope=fun y => -Ad y := by
    funext y
    simp only [FrameLowArc.slope,Ad,neg_div,neg_neg]
  rw [he]
  convert (extended_Ad_deriv hb).fun_neg using 1
  simp only [slopeD,FrameCircleArc.Add,neg_div,neg_neg]

theorem slopeD_positive {b : ℝ} (hb : b∈extendedDomain) : 0<slopeD b := by
  exact div_pos (by norm_num [Q0]) (pow_pos (extended_shift_pos hb) 3)

theorem extended_A_antitone : AntitoneOn A extendedDomain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => (extended_A_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => extended_A_deriv (Ioo_subset_Icc_self hb)
  · intro b hb
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith [hb.1]
    · exact (extended_shift_pos (Ioo_subset_Icc_self hb)).le

theorem extended_slope_monotone : MonotoneOn slope extendedDomain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (slope_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => slope_deriv (Ioo_subset_Icc_self hb)
  · exact fun b hb => (slopeD_positive (Ioo_subset_Icc_self hb)).le

theorem low_extended {b : ℝ} (hb : b∈Icc 0 b1) : b∈extendedDomain := by
  constructor <;> linarith [hb.1,hb.2,b1_bounds.2]

theorem high_extended {b : ℝ} (hb : b∈Icc b2 c0) : b∈extendedDomain := by
  constructor <;> linarith [hb.1,hb.2,b2_bounds.1,c0_bounds.2]

theorem low_slopeD_upper {b : ℝ} (hb : b∈Icc 0 b1) : slopeD b<27/40 := by
  have hA := A_low_bounds hb
  have hp := extended_shift_pos (low_extended hb)
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤899/500)
    (show (899/500:ℝ)≤A b+1/2 by linarith [a1_precise.1,hA.1]) 3
  dsimp [slopeD]
  apply (div_lt_iff₀ (pow_pos hp 3)).2
  norm_num [Q0] at *
  nlinarith

theorem high_Hd_lower {b : ℝ} (hb : b∈Icc b2 c0) :
    (73/100:ℝ)<FrameHighArc.Hd b := by
  have hh := FrameHighArc.slope_high_bounds hb
  dsimp [FrameHighArc.Hd,FrameHighArc.u,FrameHighArc.v]
  linarith

theorem high_Hdd_lower {b : ℝ} (hb : b∈Icc b2 c0) :
    (453/1000:ℝ)<FrameHighArc.u*slopeD b := by
  have hp := extended_shift_pos (high_extended hb)
  have hA := FrameHighArc.A_high_bounds hb
  have hcube := pow_le_pow_left₀ hp.le
    (show A b+1/2≤17/10 by linarith [hA.2,a2_bounds.2]) 3
  rw [slopeD,← mul_div_assoc]
  apply (lt_div_iff₀ (pow_pos hp 3)).2
  norm_num [FrameHighArc.u,Q0] at *
  nlinarith

theorem extended_L_deriv {b : ℝ} (hb : b∈extendedDomain) : HasDerivAt L (Ld b) b := by
  unfold FrameLowArc.L
  convert (((extended_A_deriv hb).sub_const a0).const_mul FrameLowArc.u).fun_add
    ((hasDerivAt_id' b).const_mul FrameLowArc.v) using 1
  simp only [FrameLowArc.Ld,Ad,FrameLowArc.slope]
  ring

theorem extended_Ld_deriv {b : ℝ} (hb : b∈extendedDomain) :
    HasDerivAt Ld (-FrameLowArc.u*slopeD b) b := by
  unfold FrameLowArc.Ld
  convert ((slope_deriv hb).const_mul FrameLowArc.u).const_sub FrameLowArc.v using 1
  ring

theorem extended_H_deriv {b : ℝ} (hb : b∈extendedDomain) :
    HasDerivAt FrameHighArc.H (FrameHighArc.Hd b) b := by
  unfold FrameHighArc.H
  convert (((extended_A_deriv hb).const_mul FrameHighArc.u).const_sub FrameHighArc.k).fun_add
    ((hasDerivAt_id' b).const_mul FrameHighArc.v) using 1
  simp only [FrameHighArc.Hd,Ad,FrameLowArc.slope]
  ring

theorem extended_Hd_deriv {b : ℝ} (hb : b∈extendedDomain) :
    HasDerivAt FrameHighArc.Hd (FrameHighArc.u*slopeD b) b := by
  exact ((slope_deriv hb).const_mul FrameHighArc.u).add_const FrameHighArc.v

theorem G_deriv {b : ℝ} (hb : b∈extendedDomain) : HasDerivAt G (Gd b) b := by
  unfold G
  convert (((extended_A_deriv hb).const_mul FrameHighArc.v).const_sub
    (Real.pi/4-(FrameHighArc.u-FrameHighArc.v)*c0)).fun_add
      ((hasDerivAt_id' b).const_mul FrameHighArc.u) using 1
  simp only [Gd,Ad,FrameLowArc.slope]
  ring

theorem Gd_deriv {b : ℝ} (hb : b∈extendedDomain) : HasDerivAt Gd (Gdd b) b :=
  ((slope_deriv hb).const_mul FrameHighArc.v).add_const FrameHighArc.u

@[simp] theorem G_c0 : G c0=Real.pi/4 := by rw [G,A_c0]; ring

theorem extended_involution {b : ℝ} (hb : b∈extendedDomain) : A (A b)=b := by
  have hc := extended_circle hb
  have he : Q0-(A b+1/2)^2=(b+1/2)^2 := by linarith
  have hp : 0≤b+1/2 := by dsimp [extendedDomain] at hb; linarith [hb.1]
  change Real.sqrt (Q0-(A b+1/2)^2)-1/2=b
  rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]
  ring

theorem quarter_label {b : ℝ} (hb : b∈Icc b2 c0) :
    G (A b)=Real.pi/2-FrameHighArc.H b := by
  rw [G,extended_involution (high_extended hb)]
  dsimp [FrameHighArc.H,FrameHighArc.k]
  ring

theorem low_norm_upper {b : ℝ} (hb : b∈Icc 0 b1) :
    (A b)^2+b^2<(283/200:ℝ)^2 := by
  have hc := A_circle ⟨hb.1,hb.2.trans b1_mem.2⟩
  have hax := A_circle (show (0:ℝ)∈Icc 0 c0 from
    ⟨le_rfl,by linarith [c0_bounds.1]⟩)
  simp only [A_zero] at hax
  have hsum := linear_endpoint_lower (p := (1:ℝ)) (q := (1:ℝ))
    (by norm_num) (by norm_num) b1_mem.2 hb
  simp only [linear,A_zero,A_b1,one_mul,mul_zero,add_zero] at hsum
  have he : a0≤a1+b1 := by linarith [a0_precise.2,a1_precise.1,b1_bounds.1]
  rw [min_eq_left he] at hsum
  have ha0 := a0_precise
  nlinarith

theorem low_projection_lt (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) (x : ℝ) :
    A b*Real.sin x-sign i*b*Real.cos x<(283/200:ℝ) := by
  have hh := low_norm_upper hb
  cases i
  · have hp := FrameCoreArc.projection_lt (b := b) (by norm_num : (0:ℝ)<283/200) hh x
    simp only [sign]
    norm_num
    linarith
  · have he : (A b)^2+(-b)^2<(283/200:ℝ)^2 := by nlinarith
    have hp := FrameCoreArc.projection_lt (b := -b) (by norm_num : (0:ℝ)<283/200) he x
    simp only [sign]
    norm_num
    linarith

end SquaresInCircles.Eight.TableFree.FrameLowHighArc
