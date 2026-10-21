module

public import SquaresInCircles.Eight.TableFree.FrameLowHighParallel
public import SquaresInCircles.Eight.TableFree.FrameLowHighCuts

/-!
# The low-positive/high-negative branch at every negative angle

Away from the parallel strip, the original high-target functional
decreases on its whole intrinsic arc.  Its diagonal support gives one
explicit increasing trigonometric function.  The comparison retains
the original weak secondary margin and its low-source loss.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighNegativeAngles
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus

def domain : Set ℝ := Icc (1/50:ℝ) (34/125)
def target (x B : ℝ) : ℝ := H B+(189/200)*A B*Real.sin x-(189/200)*B*Real.cos x
def targetD (x B : ℝ) : ℝ :=
  (FrameHighArc.u-(189/200)*Real.sin x)*slope B+FrameHighArc.v-(189/200)*Real.cos x
def F (x : ℝ) : ℝ :=
  -x+Real.pi/4-1/100000+9/16+
    (153/400-(189/200)*c0)*Real.cos x+(153/400+(189/200)*c0)*Real.sin x
def Fd (x : ℝ) : ℝ :=
  -1-(153/400-(189/200)*c0)*Real.sin x+(153/400+(189/200)*c0)*Real.cos x

theorem trig_bounds {x : ℝ} (hx : x∈domain) :
    0≤Real.sin x ∧ Real.sin x≤34/125 ∧
      (963/1000:ℝ)<Real.cos x ∧ Real.cos x≤1 ∧
        (10197/10000:ℝ)<Real.sin x+Real.cos x := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hxp : x≤Real.pi/2 := by linarith [hx.2,FrameLowPair.pi_lower]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [hxp,Real.pi_pos])
  have hsu := Real.sin_le_self hx0
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx0 hx.2 2
  have hmono : MonotoneOn (fun z => Real.sin z+Real.cos z) (Icc (0:ℝ) (34/125)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => ((Real.hasDerivAt_sin z).add
        (Real.hasDerivAt_cos z)).continuousAt.continuousWithinAt
    · exact fun z _ => (Real.hasDerivAt_sin z).add (Real.hasDerivAt_cos z)
    · intro z hz
      have hzs := Real.sin_le_self hz.1.le
      have hzc := Real.one_sub_sq_div_two_le_cos (x := z)
      have hzsq := pow_le_pow_left₀ hz.1.le hz.2.le 2
      nlinarith
  have hsum := hmono (show (1/50:ℝ)∈Icc 0 (34/125) by constructor <;> norm_num)
    ⟨hx0,hx.2⟩ hx.1
  have hs0 := sin_lower_seven (show (0:ℝ)≤1/50 by norm_num)
  have hc0 := cos_lower_six (show (0:ℝ)≤1/50 by norm_num)
  norm_num at hs0 hc0
  exact ⟨hs,by linarith [hx.2],by nlinarith,Real.cos_le_one x,by linarith⟩

theorem target_deriv {x B : ℝ} (hB : B∈Icc b2 c0) :
    HasDerivAt (target x) (targetD x B) B := by
  convert ((extended_H_deriv (high_extended hB)).add
    ((extended_A_deriv (high_extended hB)).const_mul ((189/200)*Real.sin x))).sub
      ((hasDerivAt_id B).const_mul ((189/200)*Real.cos x)) using 1
  all_goals dsimp [target,targetD,Hd,Ad,slope]; ring

theorem targetD_negative {x B : ℝ} (hx : x∈domain) (hB : B∈Icc b2 c0) :
    targetD x B<0 := by
  have ht := trig_bounds hx
  have hr := slope_high_bounds hB
  have hp : 0≤FrameHighArc.u-(189/200)*Real.sin x := by
    dsimp [FrameHighArc.u]
    linarith [ht.2.1]
  have hmul := mul_le_mul_of_nonneg_left hr.2 hp
  dsimp [targetD,FrameHighArc.u,FrameHighArc.v] at *
  linarith [ht.2.2.2.2]

theorem target_antitone {x : ℝ} (hx : x∈domain) : AntitoneOn (target x) (Icc b2 c0) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun B hB => (target_deriv hB).continuousAt.continuousWithinAt
  · exact fun B hB => target_deriv (Ioo_subset_Icc_self hB)
  · exact fun B hB => (targetD_negative hx (Ioo_subset_Icc_self hB)).le

theorem F_deriv (x : ℝ) : HasDerivAt F (Fd x) x := by
  convert (((((hasDerivAt_id x).neg).add_const (Real.pi/4)).sub_const (1/100000)).add_const
    (9/16)).add (((Real.hasDerivAt_cos x).const_mul (153/400-(189/200)*c0)).add
      ((Real.hasDerivAt_sin x).const_mul (153/400+(189/200)*c0))) using 1
  all_goals dsimp [F,Fd]; ring

theorem Fd_positive {x : ℝ} (hx : x∈domain) : 0<Fd x := by
  have ht := trig_bounds hx
  have hc : 153/400-(189/200)*c0≤0 := by linarith [c0_bounds.1]
  have hs := mul_nonneg (neg_nonneg.mpr hc) ht.1
  have hp : (123/100:ℝ)≤153/400+(189/200)*c0 := by linarith [c0_bounds.1]
  have hm := mul_le_mul hp ht.2.2.1.le (by norm_num : (0:ℝ)≤963/1000)
    (by linarith : 0≤153/400+(189/200)*c0)
  dsimp [Fd]
  nlinarith

theorem F_monotone : MonotoneOn F domain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (F_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv x
  · exact fun x hx => (Fd_positive (Ioo_subset_Icc_self hx)).le

theorem initial_lower : (8833/10000:ℝ)<F (1/50) := by
  have hc : 153/400-(189/200)*c0≤0 := by linarith [c0_bounds.1]
  have hscoef : 0≤153/400+(189/200)*c0 := by linarith [c0_bounds.1]
  have hcos := mul_le_mul_of_nonpos_left (Real.cos_le_one (1/50)) hc
  have hs := sin_lower_seven (show (0:ℝ)≤1/50 by norm_num)
  have hs0 : (19998/1000000:ℝ)≤Real.sin (1/50) := by norm_num at hs; linarith
  have hsin := mul_le_mul
    (show (123225/100000:ℝ)≤153/400+(189/200)*c0 by linarith [diagonal_precise.1]) hs0
    (by norm_num : (0:ℝ)≤19998/1000000) hscoef
  dsimp [F]
  nlinarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.2]

theorem lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F x :=
  initial_lower.trans_le (F_monotone ⟨le_rfl,by norm_num⟩ hx hx.1)

theorem support {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈domain) (hm : 0≤secondary true false b B (-x)) :
    F x≤lowHighCost true false b B (-x) := by
  have hs := low_positive_source hb
  have ht := target_antitone hx hB ⟨b2_mem.2,le_rfl⟩ hB.2
  have hscaled := mul_nonneg (show (0:ℝ)≤189/200 by norm_num) hm
  have hxn : -x∈Icc (-(54/125:ℝ)) 0 := by constructor <;> linarith [hx.1,hx.2]
  have hw := negative_width hxn
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
  rw [hw.1] at hscaled
  dsimp [target] at ht
  rw [H_c0,A_c0] at ht
  dsimp [F,lowHighCost,sign]
  rw [hw.2]
  simp only [Real.sin_neg,Real.cos_neg] at hscaled ⊢
  nlinarith

theorem weak_separator {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(34/125:ℝ)) (-(1/50:ℝ)))
    (hm : 0≤secondary true false b B x) :
    (8833/10000:ℝ)<lowHighCost true false b B x := by
  have hz : -x∈domain := by constructor <;> linarith [hx.1,hx.2]
  have hmargin : 0≤secondary true false b B (-(-x)) := by simpa using hm
  simpa only [neg_neg] using (lower hz).trans_le (support hb hB hz hmargin)

/-- The complete original positive-low, negative-high secondary branch. -/
theorem positive_negative_secondary {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤secondary true false b B x) :
    (8833/10000:ℝ)<lowHighCost true false b B x := by
  by_cases htail : (23/50:ℝ)≤x
  · exact low_high_tail true false hb hB htail
  by_cases hleft : x≤-(1/50:ℝ)
  · exact weak_separator hb hB ⟨hx,hleft⟩ hm
  by_cases hstrip : x≤1/50
  · exact FrameLowHighParallel.low_high_strip hb hB ⟨by linarith,hstrip⟩ hm
  · exact FrameLowHighSecondaryNegative.weak_separator true hb hB
      ⟨by simpa [FrameLowHighSecondaryNegative.left] using le_of_lt (lt_of_not_ge hstrip),
        by simpa [FrameLowHighSecondaryNegative.right] using le_of_lt (lt_of_not_ge htail)⟩ hm

end SquaresInCircles.Eight.TableFree.FrameLowHighNegativeAngles
