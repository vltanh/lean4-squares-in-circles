module

public import SquaresInCircles.Eight.Frames.High.LowAxialGeometry

/-!
# Eight squares: curvature of the two exact low-axial contact costs

The ordinary high cost has second derivative greater than `.12` on
`[.11,.46]`.  The continued quarter marker has positive second
derivative on `[0,.11]`.  The same explicit contact curve supplies both
statements.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowAxialCalculus
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameHighLowAxialGeometry

def normalF (x : ℝ) : ℝ := x-(9/100)*(Real.sin x+Real.cos x-1)+H (Z x)
def normalD (x : ℝ) : ℝ := 1-(9/100)*(Real.cos x-Real.sin x)-Hd (Z x)*P x
def normalDD (x : ℝ) : ℝ := (9/100)*(Real.sin x+Real.cos x)+
  FrameHighArc.u*slopeD (Z x)*(P x)^2-Hd (Z x)*Pd x
def upperF (x : ℝ) : ℝ := x-(9/100)*(Real.sin x+Real.cos x-1)+G (Z x)
def upperD (x : ℝ) : ℝ := 1-(9/100)*(Real.cos x-Real.sin x)-Gd (Z x)*P x
def upperDD (x : ℝ) : ℝ := (9/100)*(Real.sin x+Real.cos x)+Gdd (Z x)*(P x)^2-Gd (Z x)*Pd x

theorem normal_deriv {x : ℝ} (hx : x∈normalDomain) : HasDerivAt normalF (normalD x) x := by
  have he := Z_extended (show x∈domain from ⟨by linarith [hx.1],hx.2⟩)
  have h := ((hasDerivAt_id' x).fun_sub
    ((((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).sub_const 1).const_mul
      (9/100))).fun_add ((extended_H_deriv he).comp x (Z_deriv x))
  have hv : normalD x=1-9/100*(Real.cos x+-Real.sin x)+FrameHighArc.Hd (Z x)*-P x := by
    simp only [normalD]; ring
  rw [hv]
  exact h

theorem normalD_deriv {x : ℝ} (hx : x∈normalDomain) : HasDerivAt normalD (normalDD x) x := by
  have he := Z_extended (show x∈domain from ⟨by linarith [hx.1],hx.2⟩)
  have h := ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul
    (9/100:ℝ)).const_sub 1).fun_sub
      (((extended_Hd_deriv he).comp x (Z_deriv x)).fun_mul (P_deriv x))
  have hv : normalDD x=-(9/100*(-Real.sin x-Real.cos x))-
      (FrameHighArc.u*slopeD (Z x)*-P x*P x+FrameHighArc.Hd (Z x)*Pd x) := by
    simp only [normalDD]; ring
  rw [hv]
  exact h

theorem upper_deriv {x : ℝ} (hx : x∈upperDomain) : HasDerivAt upperF (upperD x) x := by
  have he := Z_extended (show x∈domain from ⟨hx.1,by linarith [hx.2]⟩)
  have h := ((hasDerivAt_id' x).fun_sub
    ((((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).sub_const 1).const_mul
      (9/100))).fun_add ((G_deriv he).comp x (Z_deriv x))
  have hv : upperD x=1-9/100*(Real.cos x+-Real.sin x)+Gd (Z x)*-P x := by
    simp only [upperD]; ring
  rw [hv]
  exact h

theorem upperD_deriv {x : ℝ} (hx : x∈upperDomain) : HasDerivAt upperD (upperDD x) x := by
  have he := Z_extended (show x∈domain from ⟨hx.1,by linarith [hx.2]⟩)
  have h := ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul
    (9/100:ℝ)).const_sub 1).fun_sub
      (((Gd_deriv he).comp x (Z_deriv x)).fun_mul (P_deriv x))
  have hv : upperDD x=-(9/100*(-Real.sin x-Real.cos x))-
      (Gdd (Z x)*-P x*P x+Gd (Z x)*Pd x) := by
    simp only [upperDD]; ring
  rw [hv]
  exact h

theorem normal_curvature {x : ℝ} (hx : x∈normalDomain) : (3/25:ℝ)<normalDD x := by
  have hq := quadrant (show x∈domain from ⟨by linarith [hx.1],hx.2⟩)
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width hq).1] at hw
  have hz := normal_chart hx
  have hPd := normal_Pd hx
  have hP := normal_P_lower hx
  have hP2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤24/25) hP.le 2
  have hcurv := high_Hdd_lower hz
  have hm := mul_le_mul hcurv.le hP2
    (by norm_num : (0:ℝ)≤(24/25)^2) (by linarith : 0≤FrameHighArc.u*slopeD (Z x))
  have hHd : Hd (Z x)≤480179/500000 := by
    have hr := (slope_high_bounds hz).2
    dsimp [Hd,FrameHighArc.u,FrameHighArc.v]
    linarith
  have hlast := mul_le_mul hHd hPd.2.le hPd.1.le (by norm_num : (0:ℝ)≤480179/500000)
  dsimp [normalDD]
  nlinarith

theorem upper_curvature {x : ℝ} (hx : x∈upperDomain) : 0<upperDD x := by
  have hdom : x∈domain := ⟨hx.1,by linarith [hx.2]⟩
  have hq := quadrant hdom
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width hq).1] at hw
  have hmarker := upper_marker_bounds hx
  have hP := P_lower hdom
  have hP2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1829/2000) hP.le 2
  have hm := mul_le_mul hmarker.2.2.le hP2
    (by norm_num : (0:ℝ)≤(1829/2000)^2) (by linarith [hmarker.2.2] : 0≤Gdd (Z x))
  have hPd : 0≤Pd x ∧ Pd x≤1/2 := by
    rw [Pd_eq]
    constructor <;> linarith [(Z_bounds hdom).1,(Z_bounds hdom).2]
  have hlast := mul_le_mul hmarker.2.1.le hPd.2 hPd.1 (by norm_num : (0:ℝ)≤41/40)
  dsimp [upperDD]
  nlinarith

end SquaresInCircles.Eight.FrameHighLowAxialCalculus
