module

public import SquaresInCircles.Eight.TableFree.FrameHighLowPrimaryGeometry

/-!
# Aligned bounds for the continued upper high marker

The upper marker is evaluated analytically below its intrinsic
diagonal only in scalar comparisons.  The input squares keep their
original type coordinates.  Both target signs have a strict aligned
reserve on every low coordinate permitted by the contact.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowUpperAligned
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighAligned
open FrameHighLowPrimaryGeometry

def lowerDomain : Set ℝ := Icc (27/40:ℝ) a2

theorem lower_extended {z : ℝ} (hz : z∈lowerDomain) : z∈extendedDomain := by
  constructor <;> linarith [hz.1,hz.2,a2_bounds.2]

theorem lower_shift_upper {z : ℝ} (hz : z∈lowerDomain) : A z+1/2<8/5 := by
  have hc := extended_circle (lower_extended hz)
  have hzsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤47/40)
    (show (47/40:ℝ)≤z+1/2 by linarith [hz.1]) 2
  by_contra! hbad
  have hAsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8/5) hbad 2
  norm_num [Q0] at hc
  nlinarith

theorem lower_Gd {z : ℝ} (hz : z∈lowerDomain) : (17/20:ℝ)<Gd z := by
  have hp := extended_shift_pos (lower_extended hz)
  have hr : (47/64:ℝ)<slope z := by
    apply (lt_div_iff₀ hp).2
    linarith [lower_shift_upper hz,hz.1]
  dsimp [Gd,FrameHighArc.u,FrameHighArc.v]
  linarith

theorem lower_slopeD {z : ℝ} (hz : z∈lowerDomain) : (19/20:ℝ)<slopeD z := by
  have hp := extended_shift_pos (lower_extended hz)
  have hcube := pow_le_pow_left₀ hp.le (lower_shift_upper hz).le 3
  dsimp [slopeD]
  apply (lt_div_iff₀ (pow_pos hp 3)).2
  norm_num [Q0] at *
  nlinarith

theorem one_Gd : (1023/1000:ℝ)<Gd 1 := by
  have hz : (1:ℝ)∈extendedDomain := by constructor <;> norm_num [extendedDomain]
  have hp := extended_shift_pos hz
  have hc := extended_circle hz
  have hA : A 1+1/2<1291/1000 := by
    by_contra! hbad
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1291/1000) hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hr : (1500/1291:ℝ)<slope 1 := by
    apply (lt_div_iff₀ hp).2
    linarith
  dsimp [Gd,FrameHighArc.u,FrameHighArc.v]
  linarith

theorem one_G : (8833/10000:ℝ)<G 1 := by
  have hh := FrameHighLowAxialScalars.upper_lower
    (show (0:ℝ)∈FrameHighLowAxialGeometry.upperDomain by
      constructor <;> norm_num [FrameHighLowAxialGeometry.upperDomain])
  have he : FrameHighLowAxialCalculus.upperF 0=G 1 := by
    simp only [FrameHighLowAxialCalculus.upperF,FrameHighLowAxialGeometry.Z_zero,
      Real.sin_zero,Real.cos_zero]
    ring
  rwa [he] at hh

theorem positive_aligned {B : ℝ} (hB : B∈Icc 0 b1)
    (hz : 1+B≤a2) : (8833/10000:ℝ)<G (1+B)-L B := by
  have hm : MonotoneOn (fun t => G (1+t)-L t) (Icc 0 B) := by
    have hd : ∀ t∈Icc 0 B, HasDerivAt (fun t => G (1+t)-L t) (Gd (1+t)-Ld t) t := by
      intro t ht
      have htlow : t∈Icc 0 b1 := ⟨ht.1,ht.2.trans hB.2⟩
      have htext : 1+t∈extendedDomain := by
        constructor <;> linarith [ht.1,ht.2,hz,a2_bounds.2]
      exact (((G_deriv htext).comp t ((hasDerivAt_id' t).const_add 1)).fun_sub
        (extended_L_deriv (low_extended htlow))).congr_deriv (by ring)
    apply monoOn_of_hasDeriv_nonneg (d := fun t => Gd (1+t)-Ld t)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => hd t (Ioo_subset_Icc_self ht)
    · intro t ht
      have htlow : t∈Icc 0 b1 := ⟨ht.1.le,ht.2.le.trans hB.2⟩
      have htext : 1+t∈extendedDomain := by
        constructor <;> linarith [ht.1,ht.2,hz,a2_bounds.2]
      have hg := Gd_monotone
        (show (1:ℝ)∈extendedDomain by constructor <;> norm_num [extendedDomain])
        htext (by linarith [ht.1] : (1:ℝ)≤1+t)
      show 0≤Gd (1+t)-Ld t
      linarith [one_Gd,low_Ld_upper htlow]
  have hh := hm ⟨le_rfl,hB.1⟩ ⟨hB.1,le_rfl⟩ hB.1
  have hzero : G 1≤G (1+B)-L B := by simpa [L,A_zero] using hh
  exact one_G.trans_le hzero

theorem quarter_late_domain {B : ℝ} (hB : B∈Icc b0 b1) :
    B∈Icc 0 b1 ∧ 1-B∈lowerDomain := by
  exact ⟨⟨b0_low.1.trans hB.1,hB.2⟩,
    ⟨by linarith [hB.2,b1_bounds.2],by linarith [hB.1,b0_bounds.1,a2_bounds.1]⟩⟩

theorem quarter_late_deriv {B : ℝ} (hB : B∈Icc b0 b1) :
    HasDerivAt quarter (quarterD B) B := by
  have hd := quarter_late_domain hB
  have h := (extended_L_deriv (low_extended hd.1)).fun_add
    ((G_deriv (lower_extended hd.2)).comp B ((hasDerivAt_id' B).const_sub 1))
  exact h.congr_deriv (by simp only [quarterD]; ring)

theorem quarter_lateD_deriv {B : ℝ} (hB : B∈Icc b0 b1) :
    HasDerivAt quarterD (quarterDD B) B := by
  have hd := quarter_late_domain hB
  have h := (extended_Ld_deriv (low_extended hd.1)).fun_sub
    ((Gd_deriv (lower_extended hd.2)).comp B ((hasDerivAt_id' B).const_sub 1))
  exact h.congr_deriv (by simp only [quarterDD,Gdd]; ring)

theorem quarter_late_curvature {B : ℝ} (hB : B∈Icc b0 b1) :
    (9/100:ℝ)<quarterDD B := by
  have hd := quarter_late_domain hB
  have hs := low_slopeD_upper hd.1
  have ht := lower_slopeD hd.2
  dsimp [quarterDD,FrameLowArc.u,FrameHighArc.v]
  linarith

theorem quarter_late_lower {B : ℝ} (hB : B∈Icc b0 b1) : F0≤quarter B := by
  have hh := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (9/100:ℝ)) (fun t ht => quarter_late_deriv ht)
    (fun t ht => quarter_lateD_deriv ht) (fun t ht => (quarter_late_curvature ht).le)
    (show b0∈Icc b0 b1 from ⟨le_rfl,b0_low.2⟩) hB
  rw [quarter_initial.1,quarter_initial.2] at hh
  have hproduct := mul_nonneg d0_bounds.1.le (sub_nonneg.mpr hB.1)
  nlinarith [sq_nonneg (B-b0)]

theorem negative_aligned {B : ℝ} (hB : B∈Icc 0 b1) :
    (8833/10000:ℝ)<G (1-B)+L B := by
  by_cases he : B≤b0
  · have hh := quarter_reserve.trans_le (quarter_lower ⟨hB.1,he⟩)
    simpa [quarter,add_comm] using hh
  · have hh := quarter_late_lower ⟨le_of_not_ge he,hB.2⟩
    dsimp [quarter] at hh
    linarith [F0_lower]

end SquaresInCircles.Eight.TableFree.FrameHighLowUpperAligned
