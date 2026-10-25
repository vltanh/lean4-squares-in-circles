module

public import SquaresInCircles.Eight.TableFree.FrameHighLowUpperAligned

/-!
# Positive-target upper contact calculus on the first positive strip

At fixed angle the contact height increases with the original low
coordinate.  The target derivative of the contact cost is bounded
below by one explicit axial gain, whose derivative is proved on the
whole interval.  All endpoints are retained.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowUpperPositiveSurface
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus
open FrameHighLowPrimaryGeometry

def domain : Set ℝ := Icc (0:ℝ) (2/25)
def height (x B : ℝ) : ℝ :=
  (1+Real.sin x+Real.cos x)/2-A B*Real.sin x+B*Real.cos x
def D (x B : ℝ) : ℝ := Real.cos x+slope B*Real.sin x
def F (x B : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x+Real.cos x-1)+G (height x B)-L B
def FB (x B : ℝ) : ℝ := Gd (height x B)*D x B-Ld B
def gain (x : ℝ) : ℝ := Gd (FrameHighLowAxialGeometry.Z x)*D x 0
def gainD (x : ℝ) : ℝ :=
  -Gdd (FrameHighLowAxialGeometry.Z x)*FrameHighLowAxialGeometry.P x*D x 0+
    Gd (FrameHighLowAxialGeometry.Z x)*(-Real.sin x+slope 0*Real.cos x)

theorem axial_domain {x : ℝ} (hx : x∈domain) : x∈FrameHighLowAxialGeometry.upperDomain :=
  ⟨hx.1,by linarith [hx.2]⟩

theorem trig_bounds {x : ℝ} (hx : x∈domain) :
    0≤Real.sin x ∧ Real.sin x≤2/25 ∧ (623/625:ℝ)≤Real.cos x ∧ Real.cos x≤1 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,FrameLowPair.pi_lower])
  have hu := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  exact ⟨hs,by linarith [hx.2],by linarith,Real.cos_le_one x⟩

theorem zero_slope : (13/50:ℝ)<slope 0 ∧ slope 0<131/500 := by
  have hz : (0:ℝ)∈Icc 0 b1 := ⟨le_rfl,b1_mem.1⟩
  refine ⟨(slope_bounds hz).1,?_⟩
  rw [FrameLowArc.slope,A_zero]
  apply (div_lt_iff₀ (by linarith [a0_precise.1] : 0<a0+1/2)).2
  linarith [a0_precise.1]

theorem axial_height {x : ℝ} (hx : x∈domain) :
    (37/40:ℝ)<FrameHighLowAxialGeometry.Z x ∧ FrameHighLowAxialGeometry.Z x≤1 := by
  have ht := trig_bounds hx
  have hproduct := mul_le_mul
    (show a0-1/2≤183/200 by linarith [a0_precise.2]) ht.2.1 ht.1
    (by norm_num : (0:ℝ)≤183/200)
  have hupper := (FrameHighLowAxialGeometry.upper_chart (axial_domain hx)).2.1
  refine ⟨?_,hupper⟩
  dsimp [FrameHighLowAxialGeometry.Z]
  nlinarith

theorem D_zero_lower {x : ℝ} (hx : x∈domain) : 1≤D x 0 := by
  have ht := trig_bounds hx
  have hs := Real.sin_ge_sub_cube hx.1
  have hxsq : x^2≤(2/25)*x := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hxcube : x^3≤(4/625)*x := by
    have hm := mul_le_mul_of_nonneg_right hxsq hx.1
    nlinarith
  have hsin : (99/100)*x≤Real.sin x := by nlinarith
  have hprod := mul_le_mul zero_slope.1.le hsin
    (mul_nonneg (by norm_num : (0:ℝ)≤99/100) hx.1)
    (by linarith [zero_slope.1] : 0≤ slope 0)
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  dsimp [D]
  nlinarith

theorem D_positive {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b1) : 0<D x B := by
  have ht := trig_bounds hx
  have hh := mul_nonneg (by linarith [(slope_bounds hB).1] : 0≤ slope B) ht.1
  dsimp [D]
  linarith [ht.2.2.1]

theorem height_deriv {B : ℝ} (hB : B∈Icc 0 b1) (x : ℝ) :
    HasDerivAt (height x) (D x B) B := by
  have h := (((extended_A_deriv (low_extended hB)).const_mul (Real.sin x)).const_sub
    ((1+Real.sin x+Real.cos x)/2)).fun_add ((hasDerivAt_id' B).const_mul (Real.cos x))
  have hf : height x=fun y => ((1+Real.sin x+Real.cos x)/2-Real.sin x*A y)+Real.cos x*y := by
    funext y; simp only [height]; ring
  rw [hf]
  exact h.congr_deriv (by simp only [D,Ad,FrameLowArc.slope]; ring)

theorem height_monotone {x : ℝ} (hx : x∈domain) : MonotoneOn (height x) (Icc 0 b1) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun B hB => (height_deriv hB x).continuousAt.continuousWithinAt
  · exact fun B hB => height_deriv (Ioo_subset_Icc_self hB) x
  · exact fun B hB => (D_positive hx (Ioo_subset_Icc_self hB)).le

@[simp] theorem height_zero (x : ℝ) : height x 0=FrameHighLowAxialGeometry.Z x := by
  rw [height,A_zero]
  dsimp [FrameHighLowAxialGeometry.Z]
  ring

theorem F_deriv {x B : ℝ} (hB : B∈Icc 0 b1) (hz : height x B∈extendedDomain) :
    HasDerivAt (F x) (FB x B) B :=
  (((G_deriv hz).comp B (height_deriv hB x)).const_add
    (x-(9/100)*(Real.sin x+Real.cos x-1))).fun_sub (extended_L_deriv (low_extended hB))

theorem gain_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt gain (gainD x) x := by
  have hax := FrameHighLowAxialGeometry.Z_extended
    (show x∈FrameHighLowAxialGeometry.domain from ⟨hx.1,by linarith [hx.2]⟩)
  have h := ((Gd_deriv hax).comp x (FrameHighLowAxialGeometry.Z_deriv x)).fun_mul
    ((Real.hasDerivAt_cos x).fun_add ((Real.hasDerivAt_sin x).const_mul (FrameLowArc.slope 0)))
  exact h.congr_deriv (by simp only [gainD,D,Function.comp_apply]; ring)

theorem gain_derivative_negative {x : ℝ} (hx : x∈domain) : gainD x<0 := by
  have hg := FrameHighLowAxialGeometry.upper_marker_bounds (axial_domain hx)
  have hp := FrameHighLowAxialGeometry.P_lower
    (show x∈FrameHighLowAxialGeometry.domain from ⟨hx.1,by linarith [hx.2]⟩)
  have hD := D_zero_lower hx
  have ht := trig_bounds hx
  have hGP := mul_le_mul hg.2.2.le hp.le (by norm_num : (0:ℝ)≤1829/2000)
    (by linarith [hg.2.2] : 0≤Gdd (FrameHighLowAxialGeometry.Z x))
  have hGPD := mul_le_mul_of_nonneg_left hD
    (mul_nonneg (by linarith [hg.2.2] : 0≤Gdd (FrameHighLowAxialGeometry.Z x))
      (by linarith : 0≤FrameHighLowAxialGeometry.P x))
  have hrc := mul_le_mul_of_nonneg_left ht.2.2.2
    (by linarith [zero_slope.1] : 0≤ slope 0)
  have hfactor : -Real.sin x+slope 0*Real.cos x≤131/500 := by linarith [ht.1,zero_slope.2]
  have hwork := mul_le_mul_of_nonneg_left hfactor hg.1.le
  have hwork0 := mul_le_mul_of_nonneg_right hg.2.1.le (by norm_num : (0:ℝ)≤131/500)
  dsimp [gainD]
  nlinarith

theorem gain_antitone : AntitoneOn gain domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (gain_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => gain_deriv (Ioo_subset_Icc_self hx)
  · exact fun x hx => (gain_derivative_negative (Ioo_subset_Icc_self hx)).le

end SquaresInCircles.Eight.TableFree.FrameHighLowUpperPositiveSurface
