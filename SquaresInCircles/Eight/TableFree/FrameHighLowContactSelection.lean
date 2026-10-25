module

public import SquaresInCircles.Eight.TableFree.FrameHighLowContactSurface

/-!
# Every physical secondary contact is bounded by the diagonal or axial boundary

The short-angle surface is convex in its low target coordinate.  Its
first feasible diagonal coordinate has positive cost derivative; after
`.11`, the axial coordinate does.  On the remaining interval a direct
derivative bound selects the same axial boundary.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowContactSelection
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

end SquaresInCircles.Eight.TableFree.FrameHighLowContactSelection
