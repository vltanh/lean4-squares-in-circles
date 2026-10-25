module

public import SquaresInCircles.Eight.Frames.High.LowDiagonalCurvature
public import SquaresInCircles.Eight.Frames.Low.HighAligned

/-!
# Eight squares: the entire high-diagonal contact scalar is strictly above the pair cost

The exact contact second derivative makes the scalar strictly concave.
The aligned endpoint uses the original proved reserve; the other
endpoint follows from directed Taylor bounds and the circle equation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowDiagonalScalar
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus
open FrameHighLowDiagonalCurve FrameHighLowDiagonalCurvature

def J (x : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x+Real.cos x-1)+Real.pi/4+L (z x)
def Jd (x : ℝ) : ℝ := 1-(9/100)*(Real.cos x-Real.sin x)+Ld (z x)*zd x
def Jdd (x : ℝ) : ℝ := (9/100)*(Real.sin x+Real.cos x)-
  FrameLowArc.u*slopeD (z x)*(zd x)^2+Ld (z x)*zdd x

theorem J_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt J (Jd x) x := by
  have h := ((((hasDerivAt_id' x).fun_sub
    ((((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).sub_const 1).const_mul
      (9/100))).add_const (Real.pi/4)).fun_add
        ((extended_L_deriv (source_chart hx)).comp x (z_deriv hx)))
  exact h.congr_deriv (by simp only [Jd]; ring)

theorem Jd_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt Jd (Jdd x) x := by
  have h := ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul
    (9/100:ℝ)).const_sub 1).fun_add
      (((extended_Ld_deriv (source_chart hx)).comp x (z_deriv hx)).fun_mul (zd_deriv hx))
  exact h.congr_deriv (by simp only [Jdd,Function.comp_apply]; ring)

theorem Jdd_negative {x : ℝ} (hx : x∈domain) : Jdd x<0 := by
  have ht := trig_bounds hx
  have hd := marker_derivative_lower hx
  have hz := contact_second_upper hx
  have hc : 0≤FrameLowArc.u*slopeD (z x)*(zd x)^2 :=
    mul_nonneg (mul_nonneg (by norm_num [FrameLowArc.u])
      (slopeD_positive (source_chart hx)).le) (sq_nonneg _)
  have hprod := mul_le_mul_of_nonpos_right hd.le (by linarith : zdd x≤0)
  have hlast := mul_le_mul_of_nonneg_left hz.le (by norm_num : (0:ℝ)≤19/20)
  dsimp [Jdd]
  linarith [ht.2.1,ht.2.2.2.1]

theorem J_concave : ConcaveOn ℝ domain J :=
  concave_of_deriv2 (fun _ hx => J_deriv hx) (fun _ hx => Jd_deriv hx)
    (fun _ hx => (Jdd_negative hx).le)

@[simp] theorem J_zero : J 0=FrameLowHighAligned.F0 := by
  simp [J,z_zero,FrameLowHighAligned.F0,FrameLowHighAligned.b0]
  ring

theorem final_primary_lower : (283057/200000:ℝ)<A (z (11/100)) := by
  have hx : (11/100:ℝ)∈domain := by constructor <;> norm_num
  have hc := extended_circle (source_chart hx)
  have hp := extended_shift_pos (source_chart hx)
  have hz := final_bounds
  have hsq := pow_le_pow_left₀
    (show 0≤z (11/100)+1/2 by linarith [hz.1])
    (show z (11/100)+1/2≤49727/100000 by linarith [hz.2]) 2
  by_contra! hbad
  have hA := pow_le_pow_left₀ hp.le
    (show A (z (11/100))+1/2≤383057/200000 by linarith) 2
  norm_num [Q0] at hc
  nlinarith

theorem final_lower : (8833/10000:ℝ)<J (11/100) := by
  have ht := final_trig
  have hz := final_bounds
  have ha := final_primary_lower
  dsimp [J,L,FrameLowArc.u,FrameLowArc.v]
  linarith [Arithmetic.pi_hand_enclosure.1,a0_precise.2]

theorem lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<J x := by
  apply concave_gt_of_endpoints J_concave hx
  · rw [J_zero]
    linarith [FrameLowHighAligned.F0_lower]
  · exact final_lower

end SquaresInCircles.Eight.FrameHighLowDiagonalScalar
