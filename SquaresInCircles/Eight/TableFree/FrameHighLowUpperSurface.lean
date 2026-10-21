module

public import SquaresInCircles.Eight.TableFree.FrameHighLowPrimaryNegative
public import SquaresInCircles.Eight.TableFree.FrameHighLowContactSelection
public import SquaresInCircles.Eight.TableFree.ContactArcMinimum

/-!
# The upper-marker contact surface and its actual line derivatives

The negative target contact is the same explicit circle height as
the high/low secondary surface.  Here its source marker is `G`.
The line `(x+t,B-t)` supplies an exact second derivative, including
the signed mixed term, without a Hessian eigenvalue assumption.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowUpperSurface
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighAligned FramePairCalculus
open FrameHighLowPrimaryGeometry FrameHighLowUpperAligned

def domain : Set ℝ := Icc (0:ℝ) (27/250)
abbrev height := FrameHighLowContactSurface.height
abbrev D := FrameHighLowContactSurface.D
def P (x B : ℝ) : ℝ := (A B-1/2)*Real.cos x+(1/2-B)*Real.sin x
def E (x B : ℝ) : ℝ := slope B*Real.cos x+Real.sin x
def F (x B : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x+Real.cos x-1)+G (height x B)+L B
def lineD (x B : ℝ) : ℝ :=
  1-(9/100)*(Real.cos x-Real.sin x)+Gd (height x B)*(D x B-P x B)-Ld B
def lineDD (x B : ℝ) : ℝ :=
  (9/100)*(Real.sin x+Real.cos x)+Gdd (height x B)*(D x B-P x B)^2+
    Gd (height x B)*(1/2-height x B+slopeD B*Real.sin x-2*E x B)-
      FrameLowArc.u*slopeD B

theorem domain_axial {x : ℝ} (hx : x∈domain) : x∈FrameHighLowAxialGeometry.domain :=
  ⟨hx.1,by linarith [hx.2]⟩

theorem domain_diagonal {x : ℝ} (hx : x∈domain) : x∈FrameHighLowDiagonalCurve.domain :=
  ⟨hx.1,by linarith [hx.2]⟩

theorem target_extended {B : ℝ} (hB : B∈Icc 0 b1) :
    B∈FrameHighLowContactSurface.lowDomain := ⟨by linarith [hB.1],hB.2⟩

theorem trig_bounds {x : ℝ} (hx : x∈domain) :
    0≤Real.sin x ∧ Real.sin x≤27/250 ∧ (497/500:ℝ)<Real.cos x ∧ Real.cos x≤1 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,FrameLowPair.pi_lower])
  have hu := Real.sin_le_self hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  exact ⟨hs,by linarith [hx.2],by nlinarith,Real.cos_le_one x⟩

theorem height_x_deriv (x B : ℝ) : HasDerivAt (fun t => height t B) (-P x B) x := by
  convert (((((Real.hasDerivAt_sin x).const_add 1).add
    (Real.hasDerivAt_cos x)).div_const 2).sub
      ((Real.hasDerivAt_sin x).const_mul (A B))).sub
        ((Real.hasDerivAt_cos x).const_mul B) using 1
  all_goals dsimp [height,FrameHighLowContactSurface.height,P]; ring

theorem P_positive {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b1) : 0<P x B := by
  have ht := trig_bounds hx
  have hA := A_low_bounds hB
  have hp := mul_pos (show 0<A B-1/2 by linarith [hA.1,a1_precise.1])
    (show 0<Real.cos x by linarith [ht.2.2.1])
  have hn := mul_nonneg (show 0≤1/2-B by linarith [hB.2,b1_bounds.2]) ht.1
  dsimp [P]
  linarith

theorem height_angle_antitone {B : ℝ} (hB : B∈Icc 0 b1) :
    AntitoneOn (fun x => height x B) domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (height_x_deriv x B).continuousAt.continuousWithinAt
  · exact fun x _ => height_x_deriv x B
  · intro x hx
    exact neg_nonpos.mpr (P_positive (Ioo_subset_Icc_self hx) hB).le

@[simp] theorem height_at_zero (B : ℝ) : height 0 B=1-B := by
  simp [height,FrameHighLowContactSurface.height]

theorem height_upper {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b1) : height x B≤1-B := by
  have hh := height_angle_antitone hB
    (show (0:ℝ)∈domain by constructor <;> norm_num [domain]) hx hx.1
  simpa only [height_at_zero] using hh

theorem physical_contact_bounds {x B : ℝ} (hx : x∈domain)
    (hB : B∈Icc 0 b1) (hz : c0≤height x B) :
    B∈Icc 0 b0 ∧ height x B∈Icc c0 1 := by
  have hu := height_upper hx hB
  exact ⟨⟨hB.1,by dsimp [b0]; linarith⟩,⟨hz,by linarith [hB.1]⟩⟩

theorem height_continuous : Continuous (fun p : ℝ×ℝ => height p.1 p.2) := by
  unfold height FrameHighLowContactSurface.height A
  fun_prop

theorem F_continuous : Continuous (fun p : ℝ×ℝ => F p.1 p.2) := by
  unfold F height FrameHighLowContactSurface.height G L A
  fun_prop

theorem height_line_deriv {x B t : ℝ} (hB : B-t∈extendedDomain) :
    HasDerivAt (fun s => height (x+s) (B-s))
      (D (x+t) (B-t)-P (x+t) (B-t)) t := by
  have hx := (hasDerivAt_id t).const_add x
  have hb := (hasDerivAt_const t B).sub (hasDerivAt_id t)
  have hs := (Real.hasDerivAt_sin (x+t)).comp t hx
  have hc := (Real.hasDerivAt_cos (x+t)).comp t hx
  have ha := (extended_A_deriv hB).comp t hb
  convert ((((hs.const_add 1).add hc).div_const 2).sub (ha.mul hs)).sub (hb.mul hc) using 1
  all_goals dsimp [height,FrameHighLowContactSurface.height,D,FrameHighLowContactSurface.D,P,Ad,slope]; ring

theorem direction_height_deriv {x B t : ℝ} (hB : B-t∈extendedDomain) :
    HasDerivAt (fun s => D (x+s) (B-s)-P (x+s) (B-s))
      (1/2-height (x+t) (B-t)+slopeD (B-t)*Real.sin (x+t)-2*E (x+t) (B-t)) t := by
  have hx := (hasDerivAt_id t).const_add x
  have hb := (hasDerivAt_const t B).sub (hasDerivAt_id t)
  have hs := (Real.hasDerivAt_sin (x+t)).comp t hx
  have hc := (Real.hasDerivAt_cos (x+t)).comp t hx
  have ha := (extended_A_deriv hB).comp t hb
  have hr := (slope_deriv hB).comp t hb
  convert (hc.sub (hr.mul hs)).sub (((ha.sub_const (1/2)).mul hc).add
    (((hasDerivAt_const t (1/2:ℝ)).sub hb).mul hs)) using 1
  all_goals dsimp [height,FrameHighLowContactSurface.height,D,FrameHighLowContactSurface.D,P,E,Ad,slope]; ring

theorem F_line_deriv {x B t : ℝ} (hB : B-t∈extendedDomain)
    (hz : height (x+t) (B-t)∈extendedDomain) :
    HasDerivAt (fun s => F (x+s) (B-s)) (lineD (x+t) (B-t)) t := by
  have hx := (hasDerivAt_id t).const_add x
  have hb := (hasDerivAt_const t B).sub (hasDerivAt_id t)
  have hs := (Real.hasDerivAt_sin (x+t)).comp t hx
  have hc := (Real.hasDerivAt_cos (x+t)).comp t hx
  have hg := (G_deriv hz).comp t (height_line_deriv hB)
  have hl := (extended_L_deriv hB).comp t hb
  convert ((hx.sub (((hs.add hc).sub_const 1).const_mul (9/100))).add hg).add hl using 1
  all_goals dsimp [F,lineD]; ring

theorem lineD_line_deriv {x B t : ℝ} (hB : B-t∈extendedDomain)
    (hz : height (x+t) (B-t)∈extendedDomain) :
    HasDerivAt (fun s => lineD (x+s) (B-s)) (lineDD (x+t) (B-t)) t := by
  have hx := (hasDerivAt_id t).const_add x
  have hb := (hasDerivAt_const t B).sub (hasDerivAt_id t)
  have hs := (Real.hasDerivAt_sin (x+t)).comp t hx
  have hc := (Real.hasDerivAt_cos (x+t)).comp t hx
  have hg := (Gd_deriv hz).comp t (height_line_deriv hB)
  have hl := (extended_Ld_deriv hB).comp t hb
  convert ((((hc.sub hs).const_mul (-(9/100:ℝ))).const_add 1).add
    (hg.mul (direction_height_deriv hB))).sub hl using 1
  all_goals dsimp [lineD,lineDD]; ring

end SquaresInCircles.Eight.TableFree.FrameHighLowUpperSurface
