module

public import SquaresInCircles.Eight.TableFree.GlobalBTAlignedPrefixPath

/-!
# The exact high-primary cap supplied by a negative BT1 prefix

The domain is the original corner disk with primary at least the
explicit cap.  The cap increases, every feasible error is below one
third, and its radical remains positive on the entire preceding
interval.  These facts are derived from the necessary prefix bound;
no optimizer or transition point is assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def L : ℝ := 3/2-c0
def K : ℝ := 13/12
def «prefix» (z : ℝ) : ℝ := 3/2+(1/2)/Real.cos z+K*Real.sin z/Real.cos z
def X (z : ℝ) : ℝ := 1+L*Real.cos z+K*Real.sin z
def Xd (z : ℝ) : ℝ := K*Real.cos z-L*Real.sin z
def Z (z : ℝ) : ℝ := Real.sqrt (Q0-(X z)^2)
def OnCap (z : ℝ) : Prop := z∈Icc 0 frameCap ∧ (X z)^2+1/4≤Q0

theorem L_bounds : (3/5:ℝ)<L ∧ L<601/1000 := by
  dsimp [L]
  constructor <;> linarith [c0_bounds.1,c0_bounds.2]

theorem X_deriv (z : ℝ) : HasDerivAt X (Xd z) z := by
  have hc : HasDerivAt (fun y => L*Real.cos y) (L*(-Real.sin z)) z :=
    (Real.hasDerivAt_cos z).const_mul L
  have hs : HasDerivAt (fun y => K*Real.sin y) (K*Real.cos z) z :=
    (Real.hasDerivAt_sin z).const_mul K
  have h := ((hasDerivAt_const z (1:ℝ)).fun_add hc).fun_add hs
  unfold X Xd
  exact h.congr_deriv (by ring)

theorem Xd_deriv (z : ℝ) : HasDerivAt Xd (1-X z) z := by
  have hc : HasDerivAt (fun y => K*Real.cos y) (K*(-Real.sin z)) z :=
    (Real.hasDerivAt_cos z).const_mul K
  have hs : HasDerivAt (fun y => L*Real.sin y) (L*Real.cos z) z :=
    (Real.hasDerivAt_sin z).const_mul L
  have h := hc.fun_sub hs
  unfold X Xd
  exact h.congr_deriv (by ring)

theorem Xd_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<Xd z := by
  have tr := transport_trig hz
  have hprod := mul_le_mul L_bounds.2.le
    (show Real.sin z≤13/20 by linarith [tr.2.2.2.1]) tr.2.2.1
    (by norm_num : (0:ℝ)≤601/1000)
  dsimp [Xd,K]
  nlinarith only [tr.1,hprod]

theorem X_monotone : MonotoneOn X (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z _ => (X_deriv z).continuousAt.continuousWithinAt
  · exact fun z _ => X_deriv z
  · exact fun z hz => (Xd_positive (Ioo_subset_Icc_self hz)).le

theorem X_lower {z : ℝ} (hz : z∈Icc 0 frameCap) : (8/5:ℝ)<X z := by
  have hm := X_monotone (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hz.1
  simp only [X,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero] at hm ⊢
  linarith [L_bounds.1]

theorem cap_X_upper {z : ℝ} (hz : OnCap z) : X z<383/200 := by
  have hl := X_lower hz.1
  have hc := hz.2
  norm_num [Q0] at hc
  nlinarith

theorem X_third_lower : (383/200:ℝ)<X (1/3) := by
  have ht : (1/3:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1/3:ℝ))
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤1/3 by norm_num)
  have hmul := mul_lt_mul_of_pos_right L_bounds.1
    (show 0<Real.cos (1/3:ℝ) by linarith [(transport_trig ht).1])
  norm_num at hc hs
  dsimp [X,K]
  nlinarith only [hc,hs,hmul]

theorem cap_error_lt {z : ℝ} (hz : OnCap z) : z<1/3 := by
  by_contra! hn
  have hm := X_monotone (show (1/3:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.1 hn
  linarith [X_third_lower,cap_X_upper hz]

theorem cap_down {z w : ℝ} (hz : OnCap z) (hw : w∈Icc 0 z) : OnCap w := by
  have hw' : w∈Icc 0 frameCap := ⟨hw.1,hw.2.trans hz.1.2⟩
  have hm := X_monotone hw' hz.1 hw.2
  have hp : 0≤X w := by linarith [X_lower hw']
  have hsq := pow_le_pow_left₀ hp hm 2
  exact ⟨hw',by linarith [hz.2]⟩

theorem cap_radicand {z : ℝ} (hz : OnCap z) : (1/4:ℝ)≤Q0-(X z)^2 := by
  linarith [hz.2]

theorem Z_pos {z : ℝ} (hz : OnCap z) : 0<Z z :=
  Real.sqrt_pos.mpr (by linarith [cap_radicand hz])

theorem Z_sq {z : ℝ} (hz : OnCap z) : (Z z)^2=Q0-(X z)^2 :=
  Real.sq_sqrt (by linarith [cap_radicand hz])

theorem Z_bounds {z : ℝ} (hz : OnCap z) : (1/2:ℝ)≤Z z ∧ Z z<233/200 := by
  have hsq := Z_sq hz
  have hl := X_lower hz.1
  have hn := Z_pos hz
  have hrad := cap_radicand hz
  norm_num [Q0] at hsq hrad
  constructor <;> nlinarith

theorem cap_trig {z : ℝ} (hz : OnCap z) :
    (17/18:ℝ)≤Real.cos z ∧ Real.sin z≤1/3 := by
  have hsmall := cap_error_lt hz
  have hsin := Real.sin_le hz.1.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := z)
  have hsquare := pow_le_pow_left₀ hz.1.1 hsmall.le 2
  constructor <;> nlinarith

theorem cap_Xd_lower {z : ℝ} (hz : OnCap z) : (41/50:ℝ)<Xd z := by
  have htr := cap_trig hz
  have hsin := (transport_trig hz.1).2.2.1
  have hp := mul_le_mul L_bounds.2.le htr.2 hsin
    (by norm_num : (0:ℝ)≤601/1000)
  dsimp [Xd,K]
  nlinarith only [htr.1,hp]

theorem X_eighth_lower : (173/100:ℝ)<X (1/8) := by
  have ht : (1/8:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1/8:ℝ))
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤1/8 by norm_num)
  have hmul := mul_lt_mul_of_pos_right L_bounds.1
    (show 0<Real.cos (1/8:ℝ) by linarith [(transport_trig ht).1])
  norm_num at hc hs
  dsimp [X,K]
  nlinarith only [hc,hs,hmul]

theorem Xd_eighth_lower : (99/100:ℝ)<Xd (1/8) := by
  have ht : (1/8:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1/8:ℝ))
  have hs := Real.sin_le (show (0:ℝ)≤1/8 by norm_num)
  have hp := mul_le_mul L_bounds.2.le hs (transport_trig ht).2.2.1
    (by norm_num : (0:ℝ)≤601/1000)
  norm_num at hc
  dsimp [Xd,K]
  nlinarith only [hc,hp]

theorem cap_large_bounds {z : ℝ} (hz : OnCap z) (hlarge : (1/8:ℝ)≤z) :
    (173/100:ℝ)<X z ∧ Z z<97/100 := by
  have hm := X_monotone (show (1/8:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.1 hlarge
  have hx : (173/100:ℝ)<X z := X_eighth_lower.trans_le hm
  have hsq := Z_sq hz
  have hpos := Z_pos hz
  norm_num [Q0] at hsq
  exact ⟨hx,by nlinarith⟩

/-- The explicit prefix restricts the unchanged T circle. -/
theorem cap_of_prefix (a t : State) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hpref : «prefix» z≤a.b+t.a/Real.cos z) :
    X z≤t.a+1/2 ∧ OnCap z := by
  have hcos : 0<Real.cos z := by linarith [(transport_trig hz).1]
  have hab : a.b≤c0 := by
    have hh := state_sum_sharp a
    linarith [a.canonical]
  have hm := mul_le_mul_of_nonneg_right hpref hcos.le
  have hid : «prefix» z*Real.cos z=(3/2)*Real.cos z+1/2+K*Real.sin z := by
    dsimp [«prefix»]
    field_simp
  rw [hid] at hm
  have hdiv : (a.b+t.a/Real.cos z)*Real.cos z=a.b*Real.cos z+t.a := by
    field_simp
  rw [hdiv] at hm
  have hprod := mul_le_mul_of_nonneg_right hab hcos.le
  have hx : X z≤t.a+1/2 := by dsimp [X,L] at *; nlinarith only [hm,hprod]
  have hc := state_circle t
  have hs := pow_le_pow_left₀ (show 0≤X z by linarith [X_lower hz]) hx 2
  have hb := t.b_nonneg
  exact ⟨hx,⟨hz,by nlinarith only [hc,hs,hb,sq_nonneg t.b]⟩⟩

end SquaresInCircles.Eight.TableFree.GlobalBT.HighPrimary
