module

public import SquaresInCircles.Eight.Frames.High.LowAxialScalars
public import SquaresInCircles.Eight.Frames.High.LowPrimaryNegative
public import SquaresInCircles.Eight.Frames.Low.HighExtendedQuarter
public import SquaresInCircles.Eight.Frames.Low.HighGeometry

/-!
# Eight squares: every physical secondary contact is bounded by the diagonal or axial boundary

The short-angle surface is convex in its low target coordinate.  Its
first feasible diagonal coordinate has positive cost derivative; after
`.11`, the axial coordinate does.  On the remaining interval a direct
derivative bound selects the same axial boundary.
-/

section
/-!
## Exact high/low secondary contact surface

The target coordinate is explicit, including the short analytic
extension used by the diagonal boundary.  Partial derivatives and all
circle-domain bounds are proved on the complete target rectangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowContactSurface
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus

def lowDomain : Set ℝ := Icc (-(3/1000:ℝ)) b1
def height (x B : ℝ) : ℝ :=
  (1+Real.sin x+Real.cos x)/2-A B*Real.sin x-B*Real.cos x
def D (x B : ℝ) : ℝ := Real.cos x-slope B*Real.sin x
def F (x B : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x+Real.cos x-1)+H (height x B)+L B
def FB (x B : ℝ) : ℝ := Ld B-Hd (height x B)*D x B
def FBB (x B : ℝ) : ℝ :=
  FrameHighArc.u*slopeD (height x B)*(D x B)^2+
    Hd (height x B)*slopeD B*Real.sin x-FrameLowArc.u*slopeD B

theorem low_extended {B : ℝ} (hB : B∈lowDomain) : B∈extendedDomain :=
  ⟨by linarith [hB.1],by linarith [hB.2,b1_bounds.2]⟩

theorem low_bounds {B : ℝ} (hB : B∈lowDomain) :
    0<slope B ∧ slope B<23/50 ∧ 0<slopeD B ∧ slopeD B<27/40 := by
  have he := low_extended hB
  have hp := extended_shift_pos he
  have hr0 : 0<slope B := div_pos (by linarith [hB.1]) hp
  have hb1 : b1∈Icc 0 b1 := ⟨b1_mem.1,le_rfl⟩
  have hcmp := extended_slope_monotone he (FrameLowHighArc.low_extended hb1) hB.2
  have hA := extended_A_antitone he (FrameLowHighArc.low_extended hb1) hB.2
  rw [A_b1] at hA
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤899/500)
    (show (899/500:ℝ)≤A B+1/2 by linarith [a1_precise.1]) 3
  refine ⟨hr0,hcmp.trans_lt (slope_bounds hb1).2,slopeD_positive he,?_⟩
  dsimp [slopeD]
  apply (div_lt_iff₀ (pow_pos hp 3)).2
  norm_num [Q0] at *
  nlinarith

theorem D_bounds {x B : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain) (hB : B∈lowDomain) :
    (17/25:ℝ)<D x B ∧ D x B≤1 := by
  have ht := FrameLowPair.quadrant (FrameHighLowAxialGeometry.quadrant hx)
  have hr := low_bounds hB
  have hs := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hm := mul_le_mul hr.2.1.le (show Real.sin x≤23/50 by linarith [hx.2]) ht.1
    (by norm_num : (0:ℝ)≤23/50)
  have hpos := mul_nonneg hr.1.le ht.1
  dsimp only [D]
  constructor <;> linarith [ht.2.2.2]

theorem D_short_lower {x B : ℝ} (hx : x∈Icc (0:ℝ) (1/5)) (hB : B∈lowDomain) :
    (111/125:ℝ)≤D x B := by
  have ht := FrameLowPair.quadrant (show x∈Icc 0 (Real.pi/2) from
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  have hr := low_bounds hB
  have hs := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hm := mul_le_mul hr.2.1.le (show Real.sin x≤1/5 by linarith [hx.2]) ht.1
    (by norm_num : (0:ℝ)≤23/50)
  dsimp only [D]
  linarith

theorem height_deriv {B : ℝ} (hB : B∈lowDomain) (x : ℝ) :
    HasDerivAt (height x) (-D x B) B := by
  have h := (((extended_A_deriv (low_extended hB)).const_mul (Real.sin x)).const_sub
    ((1+Real.sin x+Real.cos x)/2)).fun_sub ((hasDerivAt_id' B).const_mul (Real.cos x))
  have hf : height x=fun y => ((1+Real.sin x+Real.cos x)/2-Real.sin x*A y)-Real.cos x*y := by
    funext y; simp only [height]; ring
  have hv : -D x B=-(Real.sin x*Ad B)-Real.cos x*1 := by
    simp only [D,Ad,FrameLowArc.slope]; ring
  rw [hf,hv]
  exact h

theorem D_deriv {B : ℝ} (hB : B∈lowDomain) (x : ℝ) :
    HasDerivAt (D x) (-slopeD B*Real.sin x) B := by
  have h := ((slope_deriv (low_extended hB)).mul_const (Real.sin x)).const_sub (Real.cos x)
  rw [show -slopeD B*Real.sin x=-(slopeD B*Real.sin x) by ring]
  exact h

theorem height_antitone {x : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain) :
    AntitoneOn (height x) lowDomain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun B hB => (height_deriv hB x).continuousAt.continuousWithinAt
  · exact fun B hB => height_deriv (Ioo_subset_Icc_self hB) x
  · intro B hB
    linarith [(D_bounds hx (Ioo_subset_Icc_self hB)).1]

theorem height_between {x l B u : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain)
    (hl : l∈lowDomain) (hu : u∈lowDomain) (hB : B∈Icc l u) :
    height x u≤height x B ∧ height x B≤height x l := by
  have hb : B∈lowDomain := ⟨hl.1.trans hB.1,hB.2.trans hu.2⟩
  exact ⟨height_antitone hx hb hu hB.2,height_antitone hx hl hb hB.1⟩

@[simp] theorem height_zero (x : ℝ) : height x 0=FrameHighLowAxialGeometry.Z x := by
  rw [height,A_zero]
  dsimp [FrameHighLowAxialGeometry.Z]
  ring

theorem height_diagonal {x : ℝ} (hx : x∈FrameHighLowDiagonalCurve.domain) :
    height x (FrameHighLowDiagonalCurve.z x)=c0 := by
  have hh := FrameHighLowDiagonalCurve.contact hx
  rw [(first_width (FrameHighLowDiagonalCurve.quadrant hx)).1] at hh
  dsimp [height]
  linarith

theorem F_deriv {x B : ℝ} (hB : B∈lowDomain) (hz : height x B∈Icc b2 c0) :
    HasDerivAt (F x) (FB x B) B := by
  have h := (((extended_H_deriv (high_extended hz)).comp B (height_deriv hB x)).const_add
    (x-(9/100)*(Real.sin x+Real.cos x-1))).fun_add (extended_L_deriv (low_extended hB))
  have hv : FB x B=FrameHighArc.Hd (height x B)*-D x B+Ld B := by
    simp only [FB]; ring
  rw [hv]
  exact h

theorem FB_deriv {x B : ℝ} (hB : B∈lowDomain) (hz : height x B∈Icc b2 c0) :
    HasDerivAt (FB x) (FBB x B) B := by
  have h := (extended_Ld_deriv (low_extended hB)).fun_sub
    (((extended_Hd_deriv (high_extended hz)).comp B (height_deriv hB x)).fun_mul (D_deriv hB x))
  have hv : FBB x B=-FrameLowArc.u*slopeD B-(FrameHighArc.u*slopeD (height x B)*-D x B*D x B+
      FrameHighArc.Hd (height x B)*(-slopeD B*Real.sin x)) := by
    simp only [FBB]; ring
  rw [hv]
  exact h

theorem curvature_positive {x B : ℝ} (hx : x∈Icc (0:ℝ) (1/5))
    (hB : B∈lowDomain) (hz : height x B∈Icc b2 c0) : (2/25:ℝ)<FBB x B := by
  have ht := FrameLowPair.quadrant (show x∈Icc 0 (Real.pi/2) from
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  have hD := D_short_lower hx hB
  have hD2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤111/125) hD 2
  have hH := high_Hdd_lower hz
  have hh := mul_le_mul hH.le hD2 (by norm_num : (0:ℝ)≤(111/125)^2)
    (by linarith : 0≤FrameHighArc.u*slopeD (height x B))
  have hr := low_bounds hB
  have hmiddle : 0≤Hd (height x B)*slopeD B*Real.sin x :=
    mul_nonneg (mul_nonneg (by linarith [high_Hd_lower hz]) hr.2.2.1.le) ht.1
  dsimp [FBB,FrameLowArc.u]
  nlinarith [hr.2.2.2]

theorem height_le_source {b B x : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain)
    (hm : 0≤FrameLowHighGeometry.secondary true false b B x) : height x B≤b := by
  dsimp [FrameLowHighGeometry.secondary,FrameLowMidGeometry.secondary,sign] at hm
  rw [(first_width (FrameHighLowAxialGeometry.quadrant hx)).1] at hm
  dsimp [height]
  linarith

end SquaresInCircles.Eight.FrameHighLowContactSurface
end
end
end

section
/-!
## The entire high-diagonal contact scalar is strictly above the pair cost

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
end
end
end

section
/-!
## The upper-marker contact surface and its actual line derivatives

The negative target contact is the same explicit circle height as
the high/low secondary surface.  Here its source marker is `G`.
The line `(x+t,B-t)` supplies an exact second derivative, including
the signed mixed term, without a Hessian eigenvalue assumption.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowUpperSurface
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
  have hu := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  exact ⟨hs,by linarith [hx.2],by nlinarith,Real.cos_le_one x⟩

theorem height_x_deriv (x B : ℝ) : HasDerivAt (fun t => height t B) (-P x B) x := by
  have hs := Real.hasDerivAt_sin x
  have hc := Real.hasDerivAt_cos x
  have h := ((((hs.const_add 1).fun_add hc).div_const 2).fun_sub
    (hs.const_mul (A B))).fun_sub (hc.const_mul B)
  refine h.congr_deriv ?_
  simp only [P]
  ring

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
  have hx : HasDerivAt (fun s => x+s) 1 t := (hasDerivAt_id' t).const_add x
  have hb : HasDerivAt (fun s => B-s) (-1) t := (hasDerivAt_id' t).const_sub B
  have hs := hx.sin
  have hc := hx.cos
  have ha : HasDerivAt (fun s => A (B-s)) (Ad (B-t)*(-1)) t :=
    (extended_A_deriv hB).comp t hb
  have h := ((((hs.const_add 1).fun_add hc).div_const 2).fun_sub (ha.fun_mul hs)).fun_sub
    (hb.fun_mul hc)
  refine h.congr_deriv ?_
  simp only [D,FrameHighLowContactSurface.D,P,Ad,FrameLowArc.slope]
  ring

theorem direction_height_deriv {x B t : ℝ} (hB : B-t∈extendedDomain) :
    HasDerivAt (fun s => D (x+s) (B-s)-P (x+s) (B-s))
      (1/2-height (x+t) (B-t)+slopeD (B-t)*Real.sin (x+t)-2*E (x+t) (B-t)) t := by
  have hx : HasDerivAt (fun s => x+s) 1 t := (hasDerivAt_id' t).const_add x
  have hb : HasDerivAt (fun s => B-s) (-1) t := (hasDerivAt_id' t).const_sub B
  have hs := hx.sin
  have hc := hx.cos
  have ha : HasDerivAt (fun s => A (B-s)) (Ad (B-t)*(-1)) t :=
    (extended_A_deriv hB).comp t hb
  have hr : HasDerivAt (fun s => FrameLowArc.slope (B-s)) (slopeD (B-t)*(-1)) t :=
    (slope_deriv hB).comp t hb
  have h := (hc.fun_sub (hr.fun_mul hs)).fun_sub (((ha.sub_const (1/2)).fun_mul hc).fun_add
    ((hb.const_sub (1/2)).fun_mul hs))
  refine h.congr_deriv ?_
  simp only [height,FrameHighLowContactSurface.height,E,Ad,FrameLowArc.slope]
  ring

theorem F_line_deriv {x B t : ℝ} (hB : B-t∈extendedDomain)
    (hz : height (x+t) (B-t)∈extendedDomain) :
    HasDerivAt (fun s => F (x+s) (B-s)) (lineD (x+t) (B-t)) t := by
  have hx : HasDerivAt (fun s => x+s) 1 t := (hasDerivAt_id' t).const_add x
  have hb : HasDerivAt (fun s => B-s) (-1) t := (hasDerivAt_id' t).const_sub B
  have hs := hx.sin
  have hc := hx.cos
  have hg := (G_deriv hz).comp t (height_line_deriv (x := x) hB)
  have hl : HasDerivAt (fun s => L (B-s)) (Ld (B-t)*(-1)) t :=
    (extended_L_deriv hB).comp t hb
  have h := ((hx.fun_sub (((hs.fun_add hc).sub_const 1).const_mul (9/100))).fun_add hg).fun_add hl
  refine h.congr_deriv ?_
  simp only [lineD]
  ring

theorem lineD_line_deriv {x B t : ℝ} (hB : B-t∈extendedDomain)
    (hz : height (x+t) (B-t)∈extendedDomain) :
    HasDerivAt (fun s => lineD (x+s) (B-s)) (lineDD (x+t) (B-t)) t := by
  have hx : HasDerivAt (fun s => x+s) 1 t := (hasDerivAt_id' t).const_add x
  have hb : HasDerivAt (fun s => B-s) (-1) t := (hasDerivAt_id' t).const_sub B
  have hs := hx.sin
  have hc := hx.cos
  have hg := (Gd_deriv hz).comp t (height_line_deriv (x := x) hB)
  have hl : HasDerivAt (fun s => Ld (B-s)) (-FrameLowArc.u*slopeD (B-t)*(-1)) t :=
    (extended_Ld_deriv hB).comp t hb
  have h := ((((hc.fun_sub hs).const_mul (9/100)).const_sub 1).fun_add
    (hg.fun_mul (direction_height_deriv (x := x) hB))).fun_sub hl
  refine h.congr_deriv ?_
  simp only [lineDD,Function.comp_apply]
  ring

end SquaresInCircles.Eight.FrameHighLowUpperSurface
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowContactSelection
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameHighLowContactSurface

theorem height_strict_antitone {x : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain) :
    StrictAntiOn (height x) lowDomain := by
  have hs : StrictMonoOn (fun B => -height x B) lowDomain := by
    apply strict_increase_of_reserve (k := (17/25:ℝ))
    · exact fun B hB => (height_deriv hB x).fun_neg.continuousAt.continuousWithinAt
    · intro B hB
      simpa only [neg_neg] using (height_deriv (Ioo_subset_Icc_self hB) x).fun_neg
    · norm_num
    · exact fun B hB => (D_bounds hx (Ioo_subset_Icc_self hB)).1.le
  intro B hB C hC hBC
  have hh := hs hB hC hBC
  linarith

theorem contact_path {x l B t : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain)
    (hl : l∈lowDomain) (hB : B∈lowDomain) (hzl : height x l∈Icc b2 c0)
    (hzB : height x B∈Icc b2 c0) (ht : t∈Icc l B) : height x t∈Icc b2 c0 := by
  have hh := height_between hx hl hB ht
  exact ⟨hzB.1.trans hh.1,hh.2.trans hzl.2⟩

theorem convex_boundary_minimum {x l B : ℝ} (hx : x∈Icc (0:ℝ) (1/5))
    (hl : l∈lowDomain) (hB : B∈lowDomain) (horder : l≤B)
    (hzl : height x l∈Icc b2 c0) (hzB : height x B∈Icc b2 c0)
    (hstart : 0≤FB x l) : F x l≤F x B := by
  have hdom : x∈FrameHighLowAxialGeometry.domain := ⟨hx.1,by linarith [hx.2]⟩
  have htDom t (ht : t∈Icc l B) : t∈lowDomain := ⟨hl.1.trans ht.1,ht.2.trans hB.2⟩
  have hzDom t (ht : t∈Icc l B) : height x t∈Icc b2 c0 :=
    contact_path hdom hl hB hzl hzB ht
  have hFB : MonotoneOn (FB x) (Icc l B) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (FB_deriv (htDom t ht) (hzDom t ht)).continuousAt.continuousWithinAt
    · exact fun t ht => FB_deriv (htDom t (Ioo_subset_Icc_self ht)) (hzDom t (Ioo_subset_Icc_self ht))
    · intro t ht
      linarith [curvature_positive hx (htDom t (Ioo_subset_Icc_self ht)) (hzDom t (Ioo_subset_Icc_self ht))]
  have hF : MonotoneOn (F x) (Icc l B) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (F_deriv (htDom t ht) (hzDom t ht)).continuousAt.continuousWithinAt
    · exact fun t ht => F_deriv (htDom t (Ioo_subset_Icc_self ht)) (hzDom t (Ioo_subset_Icc_self ht))
    · intro t ht
      exact hstart.trans (hFB ⟨le_rfl,horder⟩ (Ioo_subset_Icc_self ht) ht.1.le)
  exact hF ⟨le_rfl,horder⟩ ⟨horder,le_rfl⟩ horder

theorem diagonal_domain {x : ℝ} (hx : x∈FrameHighLowDiagonalCurve.domain) :
    FrameHighLowDiagonalCurve.z x∈lowDomain := by
  have hh := FrameHighLowDiagonalCurve.z_bounds hx
  exact ⟨hh.1.le,by linarith [hh.2,b1_bounds.1]⟩

theorem diagonal_le_contact {x B : ℝ} (hx : x∈FrameHighLowDiagonalCurve.domain)
    (hB : B∈lowDomain) (hz : height x B≤c0) : FrameHighLowDiagonalCurve.z x≤B := by
  by_contra! hbad
  have hdom : x∈FrameHighLowAxialGeometry.domain := ⟨hx.1,by linarith [hx.2]⟩
  have hh := height_strict_antitone hdom hB (diagonal_domain hx) hbad
  rw [height_diagonal hx] at hh
  linarith

theorem diagonal_derivative_positive {x : ℝ} (hx : x∈FrameHighLowDiagonalCurve.domain) :
    0<FB x (FrameHighLowDiagonalCurve.z x) := by
  have hd := diagonal_domain hx
  have hdom : x∈FrameHighLowAxialGeometry.domain := ⟨hx.1,by linarith [hx.2]⟩
  have hD := (D_bounds hdom hd).2
  have hcoord := FrameHighLowDiagonalCurve.z_antitone
    (show (0:ℝ)∈FrameHighLowDiagonalCurve.domain by constructor <;> norm_num) hx hx.1
  rw [FrameHighLowDiagonalCurve.z_zero] at hcoord
  have hr := extended_slope_monotone (low_extended hd)
    (FrameLowHighArc.low_extended FrameLowHighAligned.b0_low) hcoord
  have hmul := mul_le_mul_of_nonneg_left hD
    (show 0≤FrameHighArc.u+FrameHighArc.v by norm_num [FrameHighArc.u,FrameHighArc.v])
  rw [FB,height_diagonal hx]
  dsimp [Hd]
  rw [FrameLowHighAligned.slope_c0]
  have hpos := FrameLowHighAligned.d0_bounds.1
  dsimp [Ld,FrameLowHighAligned.d0] at *
  norm_num [FrameLowArc.u,FrameLowArc.v,FrameHighArc.u,FrameHighArc.v] at *
  nlinarith

theorem diagonal_minimum {x B : ℝ} (hx : x∈FrameHighLowDiagonalCurve.domain)
    (hB : B∈Icc 0 b1) (hz : height x B∈Icc b2 c0) :
    FrameHighLowDiagonalScalar.J x≤F x B := by
  have hd := diagonal_domain hx
  have hBl : B∈lowDomain := ⟨by linarith [hB.1],hB.2⟩
  have horder := diagonal_le_contact hx hBl hz.2
  have hzd : height x (FrameHighLowDiagonalCurve.z x)∈Icc b2 c0 := by
    rw [height_diagonal hx]
    exact ⟨b2_mem.2,le_rfl⟩
  have hh := convex_boundary_minimum (show x∈Icc (0:ℝ) (1/5) from
    ⟨hx.1,by linarith [hx.2]⟩) hd hBl horder hzd hz (diagonal_derivative_positive hx).le
  rw [F,height_diagonal hx,H_c0] at hh
  simpa [FrameHighLowDiagonalScalar.J] using hh

theorem zero_marker_lower : (983/1000:ℝ)<Ld 0 := by
  have hp : 0<a0+1/2 := by linarith [a0_precise.1]
  have hr : slope 0<131/500 := by
    rw [FrameLowArc.slope,A_zero]
    apply (div_lt_iff₀ hp).2
    linarith [a0_precise.1]
  dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
  linarith

theorem zero_derivative_positive {x : ℝ} (hx : x∈FrameHighLowAxialGeometry.normalDomain) :
    0<FB x 0 := by
  have hdom : x∈FrameHighLowAxialGeometry.domain := ⟨by linarith [hx.1],hx.2⟩
  have hzero : (0:ℝ)∈lowDomain := ⟨by norm_num,b1_mem.1⟩
  have hD := D_bounds hdom hzero
  have hH := Hd_bounds (FrameHighLowAxialGeometry.normal_chart hx)
  have hm := mul_le_mul hH.2 hD.2 (by linarith [hD.1] : 0≤D x 0)
    (by norm_num [FrameHighArc.u,FrameHighArc.v] : 0≤FrameHighArc.u+FrameHighArc.v)
  rw [FB,height_zero]
  norm_num [FrameHighArc.u,FrameHighArc.v] at hm
  linarith [zero_marker_lower]

theorem late_D_upper {x B : ℝ} (hx : x∈Icc (1/5:ℝ) (23/50))
    (hB : B∈Icc 0 b1) : D x B<93/100 := by
  have hdom : x∈FrameHighLowAxialGeometry.domain := ⟨by linarith [hx.1],hx.2⟩
  have hq := FrameHighLowAxialGeometry.quadrant hdom
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(1/5:ℝ)) hq.2 hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤1/5)
    (by linarith [hq.2,Real.pi_pos]) hx.1
  have hs0 := Real.sin_ge_sub_cube (show (0:ℝ)≤1/5 by norm_num)
  have hc0 := cos_upper_four (show (0:ℝ)≤1/5 by norm_num)
  have hsin : (99/500:ℝ)<Real.sin x := by norm_num at hs0; linarith
  have hcos : Real.cos x<981/1000 := by norm_num at hc0; linarith
  have hm := mul_le_mul (slope_bounds hB).1.le hsin.le
    (by norm_num : (0:ℝ)≤99/500) (by linarith [(slope_bounds hB).1] : 0≤ slope B)
  dsimp [D]
  nlinarith

theorem late_derivative_positive {x B : ℝ} (hx : x∈Icc (1/5:ℝ) (23/50))
    (hB : B∈Icc 0 b1) (hz : height x B∈Icc b2 c0) : 0<FB x B := by
  have hD := D_bounds (show x∈FrameHighLowAxialGeometry.domain from
    ⟨by linarith [hx.1],hx.2⟩) ⟨by linarith [hB.1],hB.2⟩
  have hDu := late_D_upper hx hB
  have hH := Hd_bounds hz
  have hm := mul_le_mul hH.2 hDu.le (by linarith [hD.1] : 0≤D x B)
    (by norm_num [FrameHighArc.u,FrameHighArc.v] : 0≤FrameHighArc.u+FrameHighArc.v)
  have hr := (slope_bounds hB).2
  dsimp [FB,Ld,FrameLowArc.u,FrameLowArc.v]
  norm_num [FrameHighArc.u,FrameHighArc.v] at hm
  nlinarith

theorem axial_minimum {x B : ℝ} (hx : x∈FrameHighLowAxialGeometry.normalDomain)
    (hB : B∈Icc 0 b1) (hz : height x B∈Icc b2 c0) :
    FrameHighLowAxialCalculus.normalF x≤F x B := by
  have hdom : x∈FrameHighLowAxialGeometry.domain := ⟨by linarith [hx.1],hx.2⟩
  have hzero : (0:ℝ)∈lowDomain := ⟨by norm_num,b1_mem.1⟩
  have hBl : B∈lowDomain := ⟨by linarith [hB.1],hB.2⟩
  have hz0 : height x 0∈Icc b2 c0 := by
    rw [height_zero]
    exact FrameHighLowAxialGeometry.normal_chart hx
  have hmin : F x 0≤F x B := by
    by_cases hshort : x≤1/5
    · exact convex_boundary_minimum ⟨by linarith [hx.1],hshort⟩ hzero hBl hB.1 hz0 hz
        (zero_derivative_positive hx).le
    · have hm : MonotoneOn (F x) (Icc 0 B) := by
        apply monoOn_of_hasDeriv_nonneg
        · intro t ht
          exact (F_deriv (show t∈lowDomain from ⟨by linarith [ht.1],ht.2.trans hB.2⟩)
            (contact_path hdom hzero hBl hz0 hz ht)).continuousAt.continuousWithinAt
        · intro t ht
          exact F_deriv ⟨by linarith [ht.1],ht.2.le.trans hB.2⟩
            (contact_path hdom hzero hBl hz0 hz (Ioo_subset_Icc_self ht))
        · intro t ht
          exact (late_derivative_positive ⟨le_of_not_ge hshort,hx.2⟩
            ⟨ht.1.le,ht.2.le.trans hB.2⟩
              (contact_path hdom hzero hBl hz0 hz (Ioo_subset_Icc_self ht))).le
      exact hm ⟨le_rfl,hB.1⟩ ⟨hB.1,le_rfl⟩ hB.1
  rw [F,height_zero,L_zero,add_zero] at hmin
  simpa [FrameHighLowAxialCalculus.normalF] using hmin

theorem contact_lower {x B : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain)
    (hB : B∈Icc 0 b1) (hz : height x B∈Icc b2 c0) : (8833/10000:ℝ)<F x B := by
  by_cases hshort : x≤11/100
  · exact (FrameHighLowDiagonalScalar.lower ⟨hx.1,hshort⟩).trans_le
      (diagonal_minimum ⟨hx.1,hshort⟩ hB hz)
  · exact (FrameHighLowAxialScalars.normal_lower ⟨le_of_not_ge hshort,hx.2⟩).trans_le
      (axial_minimum ⟨le_of_not_ge hshort,hx.2⟩ hB hz)

end SquaresInCircles.Eight.FrameHighLowContactSelection
end
end
end
