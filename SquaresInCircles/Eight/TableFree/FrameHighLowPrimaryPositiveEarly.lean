module

public import SquaresInCircles.Eight.TableFree.FrameHighLowUpperPositiveSurface

/-!
# The actual positive-target primary on the whole first positive strip

The axial gain exceeds `.99` at the right endpoint, and its proved
negative derivative transfers that reserve to every angle.  This
selects the original low axial boundary by monotonicity, retaining
the original weak separating inequality.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowPrimaryPositiveEarly
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

end SquaresInCircles.Eight.TableFree.FrameHighLowPrimaryPositiveEarly
