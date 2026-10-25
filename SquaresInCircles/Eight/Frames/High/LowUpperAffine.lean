module

public import SquaresInCircles.Eight.Frames.High.LowAxialScalars
public import SquaresInCircles.Eight.Frames.High.LowPrimaryNegative

/-!
# Eight squares: directed Taylor transfer for the complete affine support interval

The positive polynomial proved in the preceding module bounds the
actual circle norm from above after squaring.  The sign of the
unsquared Taylor expression is proved explicitly, so the argument
does not introduce a spurious root branch.
-/

section
/-!
## The upper contact for a positive target on the first strip

On the strip `0 ≤ x ≤ 2/25`, at a fixed angle, the contact height `height x B` increases with the
low coordinate `B` (`height_deriv`, `height_monotone`), from the axial height `Z x` at `B = 0`
(`height_zero`, `axial_height`). The derivative of the contact cost `F x` in `B` is `FB x B`
(`F_deriv`), and it is compared with the axial gain `gain x = Gd (Z x) · D x 0`, whose
derivative is negative on the whole strip (`gain_deriv`, `gain_derivative_negative`,
`gain_antitone`). The ends of the strip are included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowUpperPositiveSurface
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

end SquaresInCircles.Eight.FrameHighLowUpperPositiveSurface
end
end
end

section
/-!
## The actual positive-target primary on the whole first positive strip

The axial gain exceeds `.99` at the right endpoint, and its proved
negative derivative transfers that reserve to every angle.  This
selects the original low axial boundary by monotonicity, retaining
the original weak separating inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowPrimaryPositiveEarly
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus
open FrameHighLowPrimaryGeometry FrameHighLowUpperPositiveSurface

theorem gain_endpoint : (99/100:ℝ)<gain (2/25) := by
  have hx : (2/25:ℝ)∈domain := by constructor <;> norm_num [domain]
  have hz := axial_height hx
  have hze := FrameHighLowAxialGeometry.Z_extended
    (show (2/25:ℝ)∈FrameHighLowAxialGeometry.domain by constructor <;> norm_num)
  have hc := extended_circle hze
  have hp := extended_shift_pos hze
  have hzsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤57/40)
    (show (57/40:ℝ)≤FrameHighLowAxialGeometry.Z (2/25)+1/2 by linarith [hz.1]) 2
  have hA : A (FrameHighLowAxialGeometry.Z (2/25))+1/2<687/500 := by
    by_contra! hbad
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤687/500) hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hr : (475/458:ℝ)<slope (FrameHighLowAxialGeometry.Z (2/25)) := by
    apply (lt_div_iff₀ hp).2
    linarith [hz.1]
  have hg : (487/500:ℝ)<Gd (FrameHighLowAxialGeometry.Z (2/25)) := by
    dsimp [Gd,FrameHighArc.u,FrameHighArc.v]
    linarith
  have ht := trig_bounds hx
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤2/25 by norm_num)
  norm_num at hs
  have hs0 : (799/10000:ℝ)<Real.sin (2/25) := by linarith
  have hm := mul_le_mul zero_slope.1.le hs0.le
    (by norm_num : (0:ℝ)≤799/10000) (by linarith [zero_slope.1] : 0≤ slope 0)
  have hD : (1017/1000:ℝ)<D (2/25) 0 := by
    dsimp [D]
    nlinarith [ht.2.2.1]
  have hproduct := mul_le_mul hg.le hD.le
    (by norm_num : (0:ℝ)≤1017/1000)
    (by linarith : 0≤Gd (FrameHighLowAxialGeometry.Z (2/25)))
  dsimp [gain]
  nlinarith

theorem gain_lower {x : ℝ} (hx : x∈domain) : (99/100:ℝ)<gain x :=
  gain_endpoint.trans_le (gain_antitone hx
    (show (2/25:ℝ)∈domain by constructor <;> norm_num [domain]) hx.2)

theorem source_contact_le {z B x : ℝ} (hx : x∈domain)
    (hm : 0≤upperMargin true z B x) : height x B≤z := by
  dsimp [upperMargin,sign] at hm
  rw [(first_width (show x∈Icc 0 (Real.pi/2) from
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)).1] at hm
  dsimp [height]
  linarith

theorem contact_path {z B x t : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤upperMargin true z B x) (ht : t∈Icc 0 B) :
    height x t∈sourceDomain := by
  have htlow : t∈Icc 0 b1 := ⟨ht.1,ht.2.trans hB.2⟩
  have hzero := height_monotone hx (show (0:ℝ)∈Icc 0 b1 from ⟨le_rfl,b1_mem.1⟩)
    htlow ht.1
  have hupper := height_monotone hx htlow hB ht.2
  rw [height_zero] at hzero
  have hweak := source_contact_le hx hm
  exact ⟨by linarith [(axial_height hx).1,c0_bounds.2],by linarith [hz.2]⟩

theorem target_derivative_positive {x B : ℝ} (hx : x∈domain)
    (hB : B∈Icc 0 b1) (hz : height x B∈sourceDomain) : 0<FB x B := by
  have hzero := height_monotone hx (show (0:ℝ)∈Icc 0 b1 from ⟨le_rfl,b1_mem.1⟩)
    hB hB.1
  rw [height_zero] at hzero
  have hax := FrameHighLowAxialGeometry.Z_extended
    (show x∈FrameHighLowAxialGeometry.domain from ⟨hx.1,by linarith [hx.2]⟩)
  have hG := Gd_monotone hax (source_extended hz) hzero
  have hr := extended_slope_monotone
    (low_extended (show (0:ℝ)∈Icc 0 b1 from ⟨le_rfl,b1_mem.1⟩))
    (low_extended hB) hB.1
  have ht := trig_bounds hx
  have hD : D x 0≤D x B := by
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_right hr ht.1]
  have hproduct := mul_le_mul hG hD
    (by linarith [D_zero_lower hx] : 0≤D x 0)
    (by linarith [source_Gd_lower hz] : 0≤Gd (height x B))
  have hl := low_Ld_upper hB
  have hgain := gain_lower hx
  dsimp [FB,gain] at *
  linarith

theorem axial_minimum {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤upperMargin true z B x) : F x 0≤F x B := by
  have hmono : MonotoneOn (F x) (Icc 0 B) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro t ht
      exact (F_deriv ⟨ht.1,ht.2.trans hB.2⟩
        (source_extended (contact_path hz hB hx hm ht))).continuousAt.continuousWithinAt
    · intro t ht
      exact F_deriv ⟨ht.1.le,ht.2.le.trans hB.2⟩
        (source_extended (contact_path hz hB hx hm (Ioo_subset_Icc_self ht)))
    · intro t ht
      exact (target_derivative_positive hx ⟨ht.1.le,ht.2.le.trans hB.2⟩
        (contact_path hz hB hx hm (Ioo_subset_Icc_self ht))).le
  exact hmono ⟨le_rfl,hB.1⟩ ⟨hB.1,le_rfl⟩ hB.1

theorem weak_separator {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤upperMargin true z B x) :
    (8833/10000:ℝ)<upperCost true z B x := by
  have haxial := FrameHighLowAxialScalars.upper_lower (axial_domain hx)
  have hstart : (8833/10000:ℝ)<F x 0 := by
    simpa [F,height_zero,L_zero,FrameHighLowAxialCalculus.upperF] using haxial
  have hmove := axial_minimum hz hB hx hm
  have hc := contact_path hz hB hx hm (show B∈Icc 0 B from ⟨hB.1,le_rfl⟩)
  have hG := FrameLowHighQuarterCalculus.G_monotone (source_extended hc)
    (source_extended hz) (source_contact_le hx hm)
  have hcost : F x B≤upperCost true z B x := by
    dsimp [F,upperCost,sign]
    rw [(first_width (show x∈Icc 0 (Real.pi/2) from
      ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)).2]
    linarith
  exact hstart.trans_le (hmove.trans hcost)

end SquaresInCircles.Eight.FrameHighLowPrimaryPositiveEarly
end
end
end

section
/-!
## One positive quadratic for the affine upper-high support

The displayed Taylor expression is expanded about `.135`.  On
each sign of that centered variable its remainder has nonnegative
coefficients.  A single geometric power bound absorbs all powers
from degree eight onward.  The resulting positive quadratic holds
throughout the whole interval `[.11,.46]`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowUpperPolynomial
open FrameCircleArc FrameLowMidArc FrameHighLowUpperSupport

def domain : Set ℝ := Icc (11/100:ℝ) (23/50)
def lam (x : ℝ) : ℝ := 201/200-(407/1000)*x
def T (x : ℝ) : ℝ :=
  x+9/100+(314159/100000)/4+FrameLowArc.u*(141457567/100000000)+
    (FrameLowArc.u+FrameLowArc.v)/2-8833/10000+
      (1/2-449607033/500000000)*lam x+
        (lam x-9/100)*Arithmetic.sin7 x-(9/100)*Arithmetic.cos8 x
def V (x : ℝ) : ℝ := FrameLowArc.u^2+FrameLowArc.v^2+(lam x)^2+
  2*lam x*(FrameLowArc.u*Arithmetic.sin9 x-FrameLowArc.v*Arithmetic.cos10 x)
def P (x : ℝ) : ℝ := (T x)^2-Q0*V x
def tail (u : ℝ) : ℝ := u^6+u^7+u^8+u^9+u^10+u^11+u^12+u^13+u^14
def positiveCoefficient (u : ℝ) : ℝ :=
  163/625-(111/1000)*u^2-(7/250)*u^4-(29/1000)*u^5-tail u
def negativeCoefficient (u : ℝ) : ℝ :=
  163/625-(207/500)*u-(111/1000)*u^2-(26/125)*u^3-(7/250)*u^4-tail u
def positiveLower (u : ℝ) : ℝ :=
  173/500000-(169/125000)*u+positiveCoefficient u*u^2
def negativeLower (u : ℝ) : ℝ :=
  173/500000-(169/125000)*u+negativeCoefficient u*u^2

theorem lam_bounds {x : ℝ} (hx : x∈domain) : (9/100:ℝ)<lam x ∧ lam x≤K := by
  dsimp [lam,K]
  constructor <;> linarith [hx.1,hx.2]

theorem positive_remainder {u : ℝ} (hu : 0≤u) : positiveLower u<P (27/200+u) := by
  simp only [positiveLower,positiveCoefficient,tail,P,T,V,lam,Q0,
    FrameLowArc.u,FrameLowArc.v,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8]
  linarith [hu,pow_nonneg hu 2,pow_nonneg hu 3,pow_nonneg hu 4,pow_nonneg hu 5,pow_nonneg hu 6,pow_nonneg hu 7,pow_nonneg hu 8,pow_nonneg hu 9,pow_nonneg hu 10,pow_nonneg hu 11,pow_nonneg hu 12,pow_nonneg hu 13,pow_nonneg hu 14,pow_nonneg hu 15,pow_nonneg hu 16]

theorem negative_remainder {u : ℝ} (hu : 0≤u) : negativeLower u<P (27/200-u) := by
  simp only [negativeLower,negativeCoefficient,tail,P,T,V,lam,Q0,
    FrameLowArc.u,FrameLowArc.v,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8]
  linarith [hu,pow_nonneg hu 2,pow_nonneg hu 3,pow_nonneg hu 4,pow_nonneg hu 5,pow_nonneg hu 6,pow_nonneg hu 7,pow_nonneg hu 8,pow_nonneg hu 9,pow_nonneg hu 10,pow_nonneg hu 11,pow_nonneg hu 12,pow_nonneg hu 13,pow_nonneg hu 14,pow_nonneg hu 15,pow_nonneg hu 16]

theorem tail_bound {u : ℝ} (hu : u∈Icc (0:ℝ) (1/3)) : tail u<1/400 := by
  have ht : 0≤tail u := by
    simp only [tail]
    linarith [pow_nonneg hu.1 6,pow_nonneg hu.1 7,pow_nonneg hu.1 8,pow_nonneg hu.1 9,pow_nonneg hu.1 10,pow_nonneg hu.1 11,pow_nonneg hu.1 12,pow_nonneg hu.1 13,pow_nonneg hu.1 14]
  have hid : (1-u)*tail u=u^6-u^15 := by simp only [tail]; ring
  have h6 := pow_le_pow_left₀ hu.1 hu.2 6
  have h15 := pow_nonneg hu.1 15
  have hm := mul_nonneg (show 0≤1/3-u by linarith [hu.2]) ht
  linarith

theorem positive_coefficient {u : ℝ} (hu : u∈Icc (0:ℝ) (13/40)) :
    (119/500:ℝ)<positiveCoefficient u := by
  have h2 := pow_le_pow_left₀ hu.1 hu.2 2
  have h4 := pow_le_pow_left₀ hu.1 hu.2 4
  have h5 := pow_le_pow_left₀ hu.1 hu.2 5
  have ht := tail_bound (show u∈Icc (0:ℝ) (1/3) from ⟨hu.1,by linarith [hu.2]⟩)
  dsimp [positiveCoefficient]
  linarith

theorem negative_coefficient {u : ℝ} (hu : u∈Icc (0:ℝ) (1/40)) :
    (119/500:ℝ)<negativeCoefficient u := by
  have h2 := pow_le_pow_left₀ hu.1 hu.2 2
  have h3 := pow_le_pow_left₀ hu.1 hu.2 3
  have h4 := pow_le_pow_left₀ hu.1 hu.2 4
  have ht := tail_bound (show u∈Icc (0:ℝ) (1/3) from ⟨hu.1,by linarith [hu.2]⟩)
  dsimp [negativeCoefficient]
  linarith [hu.2]

theorem quadratic_reserve (u : ℝ) :
    (1/3000:ℝ)<173/500000-(169/125000)*u+(119/500)*u^2 := by
  nlinarith [sq_nonneg ((119/250:ℝ)*u-169/125000)]

theorem positive_lower {u : ℝ} (hu : u∈Icc (0:ℝ) (13/40)) :
    (1/3000:ℝ)<positiveLower u := by
  have hm := mul_le_mul_of_nonneg_right (positive_coefficient hu).le (sq_nonneg u)
  dsimp [positiveLower]
  nlinarith [quadratic_reserve u]

theorem negative_lower {u : ℝ} (hu : u∈Icc (0:ℝ) (1/40)) :
    (1/3000:ℝ)<negativeLower u := by
  have hm := mul_le_mul_of_nonneg_right (negative_coefficient hu).le (sq_nonneg u)
  dsimp [negativeLower]
  nlinarith [quadratic_reserve u]

theorem polynomial_positive {x : ℝ} (hx : x∈domain) : (1/3000:ℝ)<P x := by
  by_cases hsign : (27/200:ℝ)≤x
  · have hu : x-27/200∈Icc (0:ℝ) (13/40) := by constructor <;> linarith [hx.2]
    have hh := (positive_lower hu).trans (positive_remainder hu.1)
    simpa only [show 27/200+(x-27/200)=x by ring] using hh
  · have hu : 27/200-x∈Icc (0:ℝ) (1/40) := by constructor <;> linarith [hx.1]
    have hh := (negative_lower hu).trans (negative_remainder hu.1)
    simpa only [show 27/200-(27/200-x)=x by ring] using hh

theorem taylor_signs {x : ℝ} (hx : x∈domain) :
    0≤Arithmetic.sin7 x ∧ Arithmetic.cos8 x≤2 := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hx1 : x≤1 := by linarith [hx.2]
  have h2 := pow_le_pow_left₀ hx0 hx1 2
  have h4 := pow_le_pow_left₀ hx0 hx1 4
  have h6 := pow_le_pow_left₀ hx0 hx1 6
  have h8 := pow_le_pow_left₀ hx0 hx1 8
  have hcoef : 0≤1-x^2/6+x^4/120-x^6/5040 := by
    nlinarith [pow_nonneg hx0 4]
  have hm := mul_nonneg hx0 hcoef
  constructor
  · dsimp [Arithmetic.sin7]
    nlinarith only [hm]
  · dsimp [Arithmetic.cos8]
    nlinarith [sq_nonneg x,pow_nonneg hx0 6]

theorem T_positive {x : ℝ} (hx : x∈domain) : 0<T x := by
  have hl := lam_bounds hx
  have ht := taylor_signs hx
  have hs := mul_nonneg (sub_nonneg.mpr hl.1.le) ht.1
  have hm := mul_le_mul_of_nonpos_left hl.2
    (by norm_num : (1/2-449607033/500000000:ℝ)≤0)
  dsimp [T,K,FrameLowArc.u,FrameLowArc.v] at *
  nlinarith [hx.1]

end SquaresInCircles.Eight.FrameHighLowUpperPolynomial
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowUpperAffine
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameHighLowPrimaryGeometry
open FrameHighLowUpperSupport FrameHighLowUpperPolynomial

theorem energy_taylor {x : ℝ} (hx : x∈domain) : (N (lam x) x)^2≤V x := by
  have ht := Arithmetic.trig_taylor_bounds (show 0≤x by linarith [hx.1])
  have hl := lam_bounds hx
  have htrig : FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x≤
      FrameLowArc.u*Arithmetic.sin9 x-FrameLowArc.v*Arithmetic.cos10 x := by
    dsimp [FrameLowArc.u,FrameLowArc.v]
    linarith [ht.2.1,ht.2.2.1]
  have hm := mul_le_mul_of_nonneg_left htrig (show 0≤2*lam x by linarith [hl.1])
  rw [N_square]
  dsimp [energy,V]
  nlinarith only [hm]

theorem scalar_taylor {x : ℝ} (hx : x∈domain) :
    T x<F (lam x) x+R*N (lam x) x-8833/10000 := by
  have ht := Arithmetic.trig_taylor_bounds (show 0≤x by linarith [hx.1])
  have hl := lam_bounds hx
  have hsin := mul_le_mul_of_nonneg_left ht.1 (sub_nonneg.mpr hl.1.le)
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2 (by norm_num : (0:ℝ)≤9/100)
  have hdiag := mul_le_mul_of_nonneg_right diagonal_precise.2.le
    (show 0≤lam x by linarith [hl.1])
  have ha := a0_precise.1
  have hpi := Arithmetic.pi_hand_enclosure.1
  dsimp [T,F,FrameLowArc.u,FrameLowArc.v]
  nlinarith

theorem root_comparison {x : ℝ} (hx : x∈domain) : R*N (lam x) x<T x := by
  have hp := polynomial_positive hx
  have hT := T_positive hx
  have hV := mul_le_mul_of_nonneg_left (energy_taylor hx)
    (show 0≤Q0 by norm_num [Q0])
  have hroot : 0≤R*N (lam x) x := mul_nonneg R_pos.le (N_nonneg _ _)
  have hsq : (R*N (lam x) x)^2=Q0*(N (lam x) x)^2 := by rw [mul_pow,R_sq]
  dsimp [P] at hp
  by_contra! hbad
  have hh := pow_le_pow_left₀ hT.le hbad 2
  rw [hsq] at hh
  nlinarith

theorem lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F (lam x) x := by
  have hs := scalar_taylor hx
  have hn := root_comparison hx
  linarith

theorem weak_separator {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤upperMargin true z B x) :
    (8833/10000:ℝ)<upperCost true z B x := by
  have hl := lam_bounds hx
  exact (lower hx).trans_le (circle_support
    (show lam x∈Icc 0 FrameHighLowUpperSupport.K from ⟨by linarith [hl.1],hl.2⟩) hz hB
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm)

end SquaresInCircles.Eight.FrameHighLowUpperAffine
end
end
end
