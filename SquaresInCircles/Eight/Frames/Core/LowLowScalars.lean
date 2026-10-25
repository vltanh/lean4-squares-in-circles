module

public import SquaresInCircles.Eight.Frames.Core.LowCancellation
public import SquaresInCircles.Eight.Frames.Core.LowCorePrimary

/-!
# Eight squares: the two remaining whole-interval low-source scalar bounds

The short-angle functions have opposite fixed derivative signs.  The
rounded-target envelope retains the actual circle radical and has negative
derivative throughout its complete interval.  No angle cells are used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreLowLowScalars
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreLowCorePrimary

def sourceFloor : ℝ :=
  u*(2829/2000)+(u+3+v)/2-(1979/1000)*(1787/500)
def shortConstant : ℝ := 159/100+sourceFloor-1/200
def Hminus (x : ℝ) : ℝ :=
  x+shortConstant+g/2+(79/25)*Real.cos x-(9/100)*Real.sin x
def Hplus (x : ℝ) : ℝ :=
  x+shortConstant-g/2+(79/25)*Real.cos x+(291/100)*Real.sin x

theorem Hminus_deriv (x : ℝ) :
    HasDerivAt Hminus (1-(79/25)*Real.sin x-(9/100)*Real.cos x) x := by
  have h := (((((hasDerivAt_id' x).add_const shortConstant).add_const (g/2)).fun_add
    ((Real.hasDerivAt_cos x).const_mul (79/25))).fun_sub
    ((Real.hasDerivAt_sin x).const_mul (9/100)))
  have e : 1-(79/25)*Real.sin x-(9/100)*Real.cos x=
      1+(79/25)*-Real.sin x-(9/100)*Real.cos x := by ring
  rw [e]
  exact h

theorem Hplus_deriv (x : ℝ) :
    HasDerivAt Hplus (1-(79/25)*Real.sin x+(291/100)*Real.cos x) x := by
  have h := (((((hasDerivAt_id' x).add_const shortConstant).sub_const (g/2)).fun_add
    ((Real.hasDerivAt_cos x).const_mul (79/25))).fun_add
    ((Real.hasDerivAt_sin x).const_mul (291/100)))
  have e : 1-(79/25)*Real.sin x+(291/100)*Real.cos x=
      1+(79/25)*-Real.sin x+(291/100)*Real.cos x := by ring
  rw [e]
  exact h

theorem short_trig {x : ℝ} (hx : x∈Icc (3/10:ℝ) (3/5)) :
    (591/2000:ℝ)≤Real.sin x ∧ Real.sin x≤3/5 ∧ (41/50:ℝ)≤Real.cos x := by
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(3/10:ℝ))
    (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  have hs0 := Real.sin_ge_sub_cube (show (0:ℝ)≤3/10 by norm_num)
  have hsU := Real.sin_le (show 0≤x by linarith [hx.1])
  have hx2 := pow_le_pow_left₀ (show 0≤x by linarith [hx.1]) hx.2 2
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  norm_num at hs0
  refine ⟨?_,?_,?_⟩ <;> linarith [hx.2]

theorem Hminus_antitone : AntitoneOn Hminus (Icc (3/10:ℝ) (3/5)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (Hminus_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => Hminus_deriv x
  · intro x hx
    have ht := short_trig (Ioo_subset_Icc_self hx)
    linarith

theorem Hplus_monotone : MonotoneOn Hplus (Icc (3/10:ℝ) (3/5)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (Hplus_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => Hplus_deriv x
  · intro x hx
    have ht := short_trig (Ioo_subset_Icc_self hx)
    linarith

theorem short_lower {x : ℝ} (hx : x∈Icc (3/10:ℝ) (3/5)) :
    (91/100:ℝ)< min (Hminus x) (Hplus x) := by
  have hm := Hminus_antitone hx ⟨by norm_num,le_rfl⟩ hx.2
  have hp := Hplus_monotone ⟨le_rfl,by norm_num⟩ hx hx.1
  have ht := short_trig (show (3/5:ℝ)∈Icc (3/10:ℝ) (3/5) by constructor <;> norm_num)
  have hc0 := Real.one_sub_sq_div_two_le_cos (x := (3/10:ℝ))
  have hs0 := Real.sin_ge_sub_cube (show (0:ℝ)≤3/10 by norm_num)
  have hleft : (1:ℝ)<Hminus (3/5) := by
    dsimp [Hminus,shortConstant,sourceFloor,u,v,g]
    linarith [ht.2.1,ht.2.2]
  have hright : (121/125:ℝ)<Hplus (3/10) := by
    dsimp [Hplus,shortConstant,sourceFloor,u,v,g]
    norm_num at hc0 hs0
    linarith
  apply lt_min <;> linarith

def capK (x : ℝ) : ℝ := 1+Real.sin x+Real.cos x/12
def capY (x : ℝ) : ℝ := Real.sqrt (Q0-(capK x)^2)
def capB (x : ℝ) : ℝ := capY x-1/2
def capD (x : ℝ) : ℝ := capK x*(-Real.cos x+Real.sin x/12)/capY x
def J (x : ℝ) : ℝ := x-4119/5000-v*capB x

theorem sine_second_antitone : AntitoneOn Real.sin (Icc (Real.pi/2) Real.pi) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (Real.hasDerivAt_sin x).continuousAt.continuousWithinAt
  · exact fun x _ => Real.hasDerivAt_sin x
  · exact fun x hx => (second_signs (Ioo_subset_Icc_self hx)).2

theorem rounded_trig {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    (887/1000:ℝ)<Real.sin x ∧ Real.sin x<947/1000 ∧
      (8/25:ℝ)< -Real.cos x ∧ -Real.cos x<231/500 := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hsecond := FrameCoreLowCancellation.second_trig ⟨hxq.1,hx.2⟩
  have hs := sine_second_antitone
    (show (19/10:ℝ)∈Icc (Real.pi/2) Real.pi by
      constructor <;> linarith [Arithmetic.pi_hand_enclosure.2,FrameLowPair.pi_lower])
    hxq hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤19/10)
    hxq.2 hx.1
  exact ⟨hsecond.1,hs.trans_lt trig_nineteen_tenths.2.1,
    by linarith [trig_nineteen_tenths.2.2.2],by linarith [hsecond.2.1]⟩

theorem capK_bounds {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    (3697/2000:ℝ)<capK x ∧ capK x<1921/1000 := by
  have ht := rounded_trig hx
  dsimp [capK]
  constructor <;> linarith

theorem cap_radicand_pos {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    0<Q0-(capK x)^2 := by
  have hk := capK_bounds hx
  norm_num [Q0]
  nlinarith

theorem capY_bounds {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    0<capY x ∧ capY x<73/100 := by
  have hk := capK_bounds hx
  have hy0 : 0<capY x := Real.sqrt_pos.mpr (cap_radicand_pos hx)
  have hysq : (capY x)^2=Q0-(capK x)^2 := Real.sq_sqrt (cap_radicand_pos hx).le
  refine ⟨hy0,?_⟩
  norm_num [Q0] at hysq
  nlinarith

theorem capK_deriv (x : ℝ) : HasDerivAt capK (Real.cos x-Real.sin x/12) x := by
  have h := ((Real.hasDerivAt_sin x).const_add 1).fun_add
    ((Real.hasDerivAt_cos x).div_const 12)
  have e : Real.cos x-Real.sin x/12=Real.cos x+-Real.sin x/12 := by ring
  rw [e]
  exact h

theorem capB_deriv {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    HasDerivAt capB (capD x) x := by
  have hd := ((hasDerivAt_const x Q0).sub ((capK_deriv x).pow 2)).sqrt
    (cap_radicand_pos hx).ne'
  convert hd.sub_const (1/2) using 1
  · rfl
  · dsimp [capD,capY]
    ring

theorem cap_gain {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) : 1<v*capD x := by
  have ht := rounded_trig hx
  have hk := capK_bounds hx
  have hy := capY_bounds hx
  have hs : (8/25:ℝ)+(887/1000)/12< -Real.cos x+Real.sin x/12 := by linarith
  have hprod := mul_lt_mul'' hk.1 hs (by norm_num) (by norm_num)
  have hscaled := mul_lt_mul_of_pos_left hprod (show 0<v by norm_num [v])
  have hn : capY x<v*(capK x*(-Real.cos x+Real.sin x/12)) := by
    dsimp only [v] at hscaled ⊢
    linarith [hy.2]
  dsimp [capD]
  rw [← mul_div_assoc,lt_div_iff₀ hy.1]
  linarith

theorem J_deriv {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    HasDerivAt J (1-v*capD x) x := by
  exact ((hasDerivAt_id x).sub_const (4119/5000)).sub ((capB_deriv hx).const_mul v)

theorem J_antitone : AntitoneOn J (Icc (19/10:ℝ) (41/20)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (J_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => J_deriv (Ioo_subset_Icc_self hx)
  · exact fun x hx => by linarith [cap_gain (Ioo_subset_Icc_self hx)]

theorem J_lower {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) : (39/40:ℝ)<J x := by
  have hm := J_antitone hx ⟨by norm_num,le_rfl⟩ hx.2
  have hy := capY_bounds (show (41/20:ℝ)∈Icc (19/10:ℝ) (41/20) by
    constructor <;> norm_num)
  have he : (39/40:ℝ)<J (41/20) := by
    dsimp [J,capB,v]
    linarith [hy.2]
  exact he.trans_le hm

end SquaresInCircles.Eight.FrameCoreLowLowScalars
