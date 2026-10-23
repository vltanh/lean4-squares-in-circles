module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighPrimaryContinuation

/-!
# The whole rounded-core target envelope for a high source

The circle cap is kept as an actual radical.  A single decreasing quartic
proves the uniform derivative bound for its radical term; the resulting
cost envelope increases on the whole interval `[2.28,2.5]`.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighCorner
open FramePair FrameCircleArc FrameHighArc FramePairCalculus

def z (x : ℝ) : ℝ := Real.sin x+Real.cos x/12
def D (x : ℝ) : ℝ := -Real.cos x+Real.sin x/12
def capK (x : ℝ) : ℝ := 1+z x
def capY (x : ℝ) : ℝ := Real.sqrt (Q0-(capK x)^2)
def J (x : ℝ) : ℝ :=
  x-4119/5000-k+u*(capK x-1/2)-v*(capY x-1/2)
def Jd (x : ℝ) : ℝ := 1-u*D x-v*D x*capK x/capY x
def P (t : ℝ) : ℝ :=
  (123/100)^2*Q0-(145/144+(123/100)^2-t^2)*(1+t)^2

theorem endpoint_trig :
    (379/500:ℝ)<Real.sin (57/25:ℝ) ∧ Real.sin (57/25:ℝ)<759/1000 ∧
      -(163/250:ℝ)<Real.cos (57/25:ℝ) ∧ Real.cos (57/25:ℝ)<-(13/20) := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤57/25 by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤57/25 by norm_num)
  have hcL := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤57/25 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤57/25 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,
    HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  repeat' constructor <;> linarith

theorem domain {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) :
    (53/100:ℝ)<z x ∧ z x<71/100 ∧ 0<D x ∧ D x<43/50 := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := second_signs hxq
  have hsL := FrameCoreHighPrimaryContinuation.interval_sine
    (show x∈Icc (3/4:ℝ) (5/2) from ⟨by linarith [hx.1],hx.2⟩)
  have hsin : Real.sin x≤Real.sin (57/25:ℝ) := by
    have hm : AntitoneOn Real.sin (Icc (Real.pi/2) Real.pi) := by
      apply antiOn_of_hasDeriv_nonpos
      · exact fun t _ => (Real.hasDerivAt_sin t).continuousAt.continuousWithinAt
      · exact fun t _ => Real.hasDerivAt_sin t
      · exact fun t ht => (second_signs (Ioo_subset_Icc_self ht)).2
    exact hm ⟨by linarith [Arithmetic.pi_hand_enclosure.2],
      by linarith [FrameLowPair.pi_lower]⟩ hxq hx.1
  have hcL := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hx.2
  have hcU := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤57/25) hxq.2 hx.1
  have hzL : (53/100:ℝ)<z x := by
    dsimp [z]
    linarith [FrameCoreHighCorePrimary.trig_endpoints.2.2.2.2]
  have hzU : z x<(71/100:ℝ) := by
    dsimp [z]
    linarith [endpoint_trig.2.1,endpoint_trig.2.2.2]
  have hD0 : 0<D x := by dsimp [D]; linarith
  have hid : (D x)^2+(z x)^2=(145/144:ℝ) := by
    dsimp [D,z]
    linear_combination (145/144:ℝ)*(Real.sin_sq_add_cos_sq x)
  refine ⟨hzL,hzU,hD0,?_⟩
  nlinarith

theorem cap_radicand_pos {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) :
    0<Q0-(capK x)^2 := by
  have hz := domain hx
  dsimp [capK]
  norm_num [Q0]
  nlinarith

theorem capY_pos {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) : 0<capY x :=
  Real.sqrt_pos.mpr (cap_radicand_pos hx)

theorem capY_sq {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) :
    (capY x)^2=Q0-(capK x)^2 := Real.sq_sqrt (cap_radicand_pos hx).le

theorem P_deriv (t : ℝ) : HasDerivAt P
    (2*(1+t)*(2*t^2+t-145/144-(123/100)^2)) t := by
  have hd := (show DifferentiableAt ℝ P t by dsimp [P]; fun_prop).hasDerivAt
  convert hd using 1
  simp (disch := fun_prop) [P]
  ring

theorem P_antitone : AntitoneOn P (Icc (53/100:ℝ) (71/100)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun t _ => (P_deriv t).continuousAt.continuousWithinAt
  · exact fun t _ => P_deriv t
  · intro t ht
    have ht0 : 0≤t := by linarith [ht.1]
    have hs := pow_le_pow_left₀ ht0 ht.2.le 2
    apply mul_nonpos_of_nonneg_of_nonpos
    · positivity
    · nlinarith

theorem ratio_bound {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) :
    D x*capK x/capY x<(123/100:ℝ) := by
  have hz := domain hx
  have hp := P_antitone ⟨hz.1.le,hz.2.le⟩ ⟨by norm_num,le_rfl⟩ hz.2.le
  have he : 0<P (71/100) := by norm_num [P,Q0]
  have hp0 : 0<P (z x) := he.trans_le hp
  have hid : (D x)^2+(z x)^2=(145/144:ℝ) := by
    dsimp [D,z]
    linear_combination (145/144:ℝ)*(Real.sin_sq_add_cos_sq x)
  have hy := capY_sq hx
  have hY0 := capY_pos hx
  have hK0 : 0≤capK x := by dsimp [capK]; linarith [hz.1]
  have hsq : (D x*capK x)^2<((123/100)*capY x)^2 := by
    have hid' := congrArg (fun w : ℝ => (1+z x)^2*w) hid
    rw [mul_pow,mul_pow,hy]
    dsimp [P,capK] at hp0 ⊢
    nlinarith [hid']
  apply (div_lt_iff₀ hY0).2
  have hprod := mul_nonneg hz.2.2.1.le hK0
  nlinarith

theorem capK_deriv (x : ℝ) : HasDerivAt capK (-D x) x := by
  convert ((Real.hasDerivAt_sin x).add ((Real.hasDerivAt_cos x).div_const 12)).const_add 1 using 1 <;>
    dsimp [capK,z,D] <;> ring

theorem capY_deriv {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) :
    HasDerivAt capY (capK x*D x/capY x) x := by
  have hd := ((hasDerivAt_const x Q0).sub ((capK_deriv x).pow 2)).sqrt
    (cap_radicand_pos hx).ne'
  convert hd using 1 <;> dsimp [capY] <;> ring

theorem J_deriv {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) : HasDerivAt J (Jd x) x := by
  have hd := (((((hasDerivAt_id x).sub_const (4119/5000)).sub_const k).add
    (((capK_deriv x).sub_const (1/2)).const_mul u))).sub
    (((capY_deriv hx).sub_const (1/2)).const_mul v)
  convert hd using 1 <;> dsimp [J,Jd] <;> ring

theorem Jd_positive {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) : 0<Jd x := by
  have hD := (domain hx).2.2.2
  have hG := ratio_bound hx
  have hDu := mul_lt_mul_of_pos_left hD (show 0<u by norm_num [u])
  have hGv := mul_lt_mul_of_pos_left hG (show 0<v by norm_num [v])
  dsimp [Jd,u,v] at *
  nlinarith

theorem J_lower {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) : (99/100:ℝ)<J x := by
  have hm : MonotoneOn J (Icc (57/25:ℝ) (5/2)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (J_deriv ht).continuousAt.continuousWithinAt
    · exact fun t ht => J_deriv (Ioo_subset_Icc_self ht)
    · exact fun t ht => (Jd_positive (Ioo_subset_Icc_self ht)).le
  have ht0 : (57/25:ℝ)∈Icc (57/25:ℝ) (5/2) := ⟨le_rfl,by norm_num⟩
  have hh := hm ht0 hx hx.1
  have hK : (17/10:ℝ)<capK (57/25) := by
    dsimp [capK,z]
    linarith [endpoint_trig.1,endpoint_trig.2.2.1]
  have hY : capY (57/25)<(507/500:ℝ) := by
    have hy := capY_sq ht0
    have hy0 := capY_pos ht0
    norm_num [Q0] at hy
    nlinarith
  have he : (99/100:ℝ)<J (57/25) := by
    dsimp [J,u,v]
    linarith [k_bounds.2.1]
  exact he.trans_le hh

end SquaresInCircles.Eight.TableFree.FrameCoreHighCorner
