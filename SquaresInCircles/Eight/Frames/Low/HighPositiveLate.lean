module

public import SquaresInCircles.Eight.Frames.Low.HighCuts
public import SquaresInCircles.Eight.Frames.Low.HighPositiveCircle
public import SquaresInCircles.Eight.Frames.Low.HighQuarterStrip

/-!
# Eight squares: the positive low/high diagonal support after the quarter strip

The high-target functional decreases over the entire original high
arc.  Its diagonal support is increasing in the frame error.  The
global width estimate supplies the remaining unbounded angular tail.
The final theorem joins every positive/positive secondary angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighPositiveLate
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus

def domain : Set ℝ := Icc (1/50:ℝ) (27/250)
def F (e : ℝ) : ℝ := Real.pi/4+e-1/100000+9/16+
  (153/400-(189/200)*c0)*(Real.cos e+Real.sin e)
def Fd (e : ℝ) : ℝ := 1+(153/400-(189/200)*c0)*(Real.cos e-Real.sin e)

theorem trig_bounds {e : ℝ} (he : e∈domain) :
    0≤Real.sin e ∧ Real.sin e≤27/250 ∧
      (994/1000:ℝ)<Real.cos e ∧ Real.cos e≤1 := by
  have he0 : 0≤e := by linarith [he.1]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi he0 (by linarith [he.2,FrameLowPair.pi_lower])
  have hsu := Real.sin_le he0
  have hc := Real.one_sub_sq_div_two_le_cos (x := e)
  have hsq := pow_le_pow_left₀ he0 he.2 2
  exact ⟨hs,by linarith [he.2],by nlinarith,Real.cos_le_one e⟩

theorem target_minimum {B e : ℝ} (hB : B∈Icc b2 c0) (he : e∈domain) :
    linear (FrameHighArc.u-(189/200)*Real.cos e) (-(189/200)*Real.sin e-FrameHighArc.v) c0≤
      linear (FrameHighArc.u-(189/200)*Real.cos e) (-(189/200)*Real.sin e-FrameHighArc.v) B := by
  have ht := trig_bounds he
  have hp : 0≤(189/200)*Real.cos e-FrameHighArc.u := by
    dsimp [FrameHighArc.u]
    linarith [ht.2.2.1]
  have ha : AntitoneOn
      (linear (FrameHighArc.u-(189/200)*Real.cos e) (-(189/200)*Real.sin e-FrameHighArc.v))
      (Icc b2 c0) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z hz => (linear_hasDerivAt ⟨b2_mem.1.trans hz.1,hz.2⟩ _ _).continuousAt.continuousWithinAt
    · exact fun z hz => linear_hasDerivAt ⟨b2_mem.1.trans hz.1.le,hz.2.le⟩ _ _
    · intro z hz
      have hr := slope_high_bounds (Ioo_subset_Icc_self hz)
      have hh := mul_le_mul_of_nonneg_left hr.2 hp
      simp only [Ad,FrameLowArc.slope,FrameHighArc.u,FrameHighArc.v,neg_div] at hh hp ⊢
      nlinarith [ht.1,ht.2.2.2]
  exact ha hB ⟨b2_mem.2,le_rfl⟩ hB.2

theorem F_deriv (e : ℝ) : HasDerivAt F (Fd e) e := by
  have h := ((((hasDerivAt_id' e).const_add (Real.pi/4)).sub_const (1/100000)).add_const
    (9/16)).fun_add (((Real.hasDerivAt_cos e).fun_add (Real.hasDerivAt_sin e)).const_mul
      (153/400-(189/200)*c0))
  refine h.congr_deriv ?_
  simp only [Fd]
  ring

theorem Fd_positive {e : ℝ} (he : e∈domain) : 0<Fd e := by
  have ht := trig_bounds he
  have hp : 153/400-(189/200)*c0≤0 := by linarith [c0_bounds.1]
  have hh := mul_le_mul_of_nonpos_left
    (show Real.cos e-Real.sin e≤1 by linarith [ht.1,ht.2.2.2]) hp
  dsimp [Fd]
  nlinarith [c0_bounds.2]

theorem F_monotone : MonotoneOn F domain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun e _ => (F_deriv e).continuousAt.continuousWithinAt
  · exact fun e _ => F_deriv e
  · exact fun e he => (Fd_positive (Ioo_subset_Icc_self he)).le

theorem initial_lower : (8833/10000:ℝ)<F (1/50) := by
  have hs := Real.sin_le (show (0:ℝ)≤1/50 by norm_num)
  have hc := Real.cos_le_one (1/50)
  have hp : 153/400-(189/200)*c0≤0 := by linarith [c0_bounds.1]
  have hh := mul_le_mul_of_nonpos_left
    (show Real.cos (1/50)+Real.sin (1/50)≤51/50 by linarith) hp
  dsimp [F]
  nlinarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.2]

theorem lower {e : ℝ} (he : e∈domain) : (8833/10000:ℝ)<F e :=
  initial_lower.trans_le (F_monotone ⟨le_rfl,by norm_num⟩ he he.1)

theorem support {b B e : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (he : e∈domain) (hm : 0≤ secondary true true b B (Real.pi/2+e)) :
    F e≤lowHighCost true true b B (Real.pi/2+e) := by
  have hs := low_positive_source hb
  have ht := target_minimum hB he
  dsimp [linear] at ht
  rw [A_c0] at ht
  have hscaled := mul_nonneg (show (0:ℝ)≤189/200 by norm_num) hm
  have hq : e∈Icc 0 (Real.pi/2) := ⟨by linarith [he.1],by linarith [he.2,FrameLowPair.pi_lower]⟩
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
  rw [FrameLowHighQuarterStrip.quarter_width,(first_width hq).1] at hscaled
  simp only [Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,zero_sub] at hscaled
  dsimp [F,lowHighCost,sign,H,k]
  rw [FrameLowHighQuarterStrip.quarter_charge,(first_width hq).2]
  nlinarith

theorem weak_separator {b B e : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (he : e∈domain) (hm : 0≤ secondary true true b B (Real.pi/2+e)) :
    (8833/10000:ℝ)<lowHighCost true true b B (Real.pi/2+e) :=
  (lower he).trans_le (support hb hB he hm)

theorem charge_linear {e : ℝ} (he : 0≤e) : periodicFrameCost e≤e/2 := by
  have hs := Real.abs_sin_le_abs (x := e)
  rw [abs_of_nonneg he] at hs
  have hc := Real.abs_cos_le_one e
  dsimp [periodicFrameCost]
  linarith

theorem tail {b B e : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (he : (27/250:ℝ)≤e) : (8833/10000:ℝ)<lowHighCost true true b B (Real.pi/2+e) := by
  have hc := charge_linear (show 0≤e by linarith)
  have hl := (L_bounds hb).1
  have hh := (H_bounds hB).2
  dsimp [lowHighCost,sign]
  rw [FrameLowHighQuarterStrip.quarter_charge]
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem positive_positive_secondary {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary true true b B x) :
    (8833/10000:ℝ)<lowHighCost true true b B x := by
  have hcut : (11/10:ℝ)<x := by
    simpa [FrameLowHighCuts.positiveCut] using
      FrameLowHighCuts.positive_secondary_cut true hb hB hx hm
  by_cases hearly : x≤27/20
  · exact FrameLowHighPositiveEarly.weak_separator hb hB ⟨hcut.le,hearly⟩ hm
  by_cases hcircle : x≤Real.pi/2-1/50
  · exact FrameLowHighPositiveCircle.weak_separator hb hB ⟨by linarith,hcircle⟩ hm
  by_cases hstrip : x≤Real.pi/2+1/50
  · exact FrameLowHighQuarterStrip.actual_angle hb hB ⟨by linarith,hstrip⟩ hm
  have hid : Real.pi/2+(x-Real.pi/2)=x := by ring
  by_cases htail : (27/250:ℝ)≤x-Real.pi/2
  · simpa only [hid] using tail hb hB htail
  · have he : x-Real.pi/2∈domain := by constructor <;> linarith
    have hmargin : 0≤ secondary true true b B (Real.pi/2+(x-Real.pi/2)) := by rwa [hid]
    simpa only [hid] using weak_separator hb hB he hmargin

end SquaresInCircles.Eight.FrameLowHighPositiveLate
