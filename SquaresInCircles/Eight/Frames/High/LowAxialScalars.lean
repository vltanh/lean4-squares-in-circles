module

public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Frames.High.LowAxialReferences

/-!
# Eight squares: both complete low-axial boundary inequalities

The ordinary high marker uses its quantitative second derivative and
one interior tangent.  The upper marker decreases throughout its
interval because its derivative increases to a negative endpoint.
Both conclusions are strict on the entire closed interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowAxialScalars
open FramePairCalculus FrameHighLowAxialGeometry FrameHighLowAxialCalculus
open FrameHighLowAxialReferences

theorem normal_lower {x : ℝ} (hx : x∈normalDomain) :
    (8833/10000:ℝ)<normalF x := by
  have href : (23/200:ℝ)∈normalDomain := by constructor <;> norm_num [normalDomain]
  have ht := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (3/25:ℝ)) (fun z hz => normal_deriv hz)
    (fun z hz => normalD_deriv hz) (fun z hz => (normal_curvature hz).le) href hx
  have hd := abs_lt.mp normal_derivative
  have hs := mul_pos (sub_pos.mpr hd.2)
    (show 0<normalD (23/200)+3/1000 by linarith [hd.1])
  nlinarith [normal_value,sq_nonneg (x-23/200+(25/3)*normalD (23/200))]

theorem upper_derivative_monotone : MonotoneOn upperD upperDomain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x hx => (upperD_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => upperD_deriv (Ioo_subset_Icc_self hx)
  · exact fun x hx => (upper_curvature (Ioo_subset_Icc_self hx)).le

theorem upper_antitone : AntitoneOn upperF upperDomain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (upper_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => upper_deriv (Ioo_subset_Icc_self hx)
  · intro x hx
    have hh := upper_derivative_monotone (Ioo_subset_Icc_self hx)
      (show (11/100:ℝ)∈upperDomain by constructor <;> norm_num [upperDomain]) hx.2.le
    exact hh.trans upper_derivative.le

theorem upper_lower {x : ℝ} (hx : x∈upperDomain) :
    (8833/10000:ℝ)<upperF x := by
  have hh := upper_antitone hx
    (show (11/100:ℝ)∈upperDomain by constructor <;> norm_num [upperDomain]) hx.2
  linarith [upper_value]

end SquaresInCircles.Eight.FrameHighLowAxialScalars
