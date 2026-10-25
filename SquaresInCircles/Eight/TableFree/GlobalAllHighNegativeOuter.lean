module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighPositiveTransfer

/-!
# Every negative high-primary error with an outer target

For a nonpositive target, a division-free circle comparison proves the
actual secondary projection as well.  For a positive target, the same
original primary projection forces a short angle and pays the full
common primary charge.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

open FramePair ZeroPrimary FrameCircleArc FrameLowArc GlobalZeroSign GlobalOuterAnchor

theorem cosine_drop_small {z : ℝ} (hz : z∈Icc 0 frameCap) :
    1-Real.cos z≤(2/5)*Real.sin z := by
  have tr := transport_trig hz
  have hs := mul_nonneg tr.2.2.1
    (show 0≤(13/20:ℝ)-Real.sin z by linarith [tr.2.2.2.1])
  have hc := mul_nonneg (sub_nonneg.mpr tr.2.1)
    (show 0≤Real.cos z-(19/25:ℝ) by linarith [tr.1])
  nlinarith [Real.sin_sq_add_cos_sq z]

theorem sorted_diagonal_support (s : State) {f g : ℝ}
    (hf : 0≤f) (hfg : f≤g) : f*s.a+g*s.b≤c0*(f+g) := by
  have hc := state_circle s
  have hsum : s.a+s.b≤2*c0 := by
    have hpositive : 0≤ s.a+s.b+1 := by linarith [s.a_pos,s.b_nonneg]
    nlinarith [c0_circle,sq_nonneg (s.a-s.b),c0_bounds.1]
  have hp := mul_nonneg (sub_nonneg.mpr hfg) (sub_nonneg.mpr s.canonical)
  have hq := mul_le_mul_of_nonneg_left hsum (show 0≤f+g by linarith)
  nlinarith only [hp,hq]

theorem negative_outer_projection_comparison (s t : State)
    (htOuter : t.branch.type≠0) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    s.a-t.a*Real.sin z+t.b*Real.cos z≤
      s.a*Real.cos z-s.b*Real.sin z+t.b := by
  have tr := transport_trig hz
  have hdrop := cosine_drop_small hz
  have hsource := sorted_diagonal_support s
    (sub_nonneg.mpr tr.2.1) (show 1-Real.cos z≤Real.sin z by linarith [tr.2.2.1])
  have ht := state_outer_chart t htOuter
  have hdiag : c0*(Real.sin z+(1-Real.cos z))≤
      linear (Real.sin z) (1-Real.cos z) t.b := by
    have hfirst : c0*(Real.sin z+(1-Real.cos z))≤
        linear (Real.sin z) (1-Real.cos z) 0 := by
      have hsmall := mul_le_mul_of_nonneg_left hdrop
        (show 0≤c0 by linarith [c0_bounds.1])
      have hgap := mul_nonneg (show 0≤a0-(7/5)*c0 by
        linarith [a0_bounds.1,c0_bounds.2]) tr.2.2.1
      simp only [linear,A_zero,mul_zero,add_zero]
      nlinarith only [hsmall,hgap]
    have hlast : c0*(Real.sin z+(1-Real.cos z))≤
        linear (Real.sin z) (1-Real.cos z) c0 := by
      simp only [linear,A_c0]
      exact le_of_eq (by ring)
    exact (le_min hfirst hlast).trans
      (linear_endpoint_lower tr.2.2.1 (by norm_num) le_rfl ht.2)
  dsimp [linear] at hdiag
  rw [← ht.1] at hdiag
  nlinarith only [hsource,hdiag]

theorem negative_primary_nonpositive_outer (s t : State)
    (hs : s.branch.type≠0) (htOuter : t.branch.type≠0)
    (ht : transverse t≤0) {z : ℝ} (hz : z∈Ioc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    kappa<quarterCharge s (transverse t) (-z) := by
  have hy : transverse t= -t.b := transverse_nonpos_eq t ht
  have hc := negative_outer_projection_comparison s t htOuter (Ioc_subset_Icc_self hz)
  have hm' : GlobalOuterAnchor.width (-z)≤ s.a-t.a*Real.sin z+t.b*Real.cos z := by
    simp only [Real.sin_neg,Real.cos_neg,hy,mul_neg,neg_mul,sub_neg_eq_add] at hm
    linarith
  have hsecondary : GlobalOuterAnchor.width (-z)≤
      s.a*Real.cos (-z)+s.b*Real.sin (-z)-transverse t := by
    rw [Real.cos_neg,Real.sin_neg,hy]
    nlinarith only [hm',hc]
  have hcharge := secondary_charge s hs
    (show |-z|≤frameCap by rw [abs_neg,abs_of_pos hz.1]; exact hz.2) hsecondary
  exact hcharge.2 (by linarith [hz.1])

theorem outer_primary_negative_gain (s t : State)
    (hs : s.branch.type≠0) (htOuter : t.branch.type≠0)
    (ht : 0≤transverse t) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    (c0+1/2)*(Real.sin z+Real.cos z-1)≤ s.a-transverse t-1 := by
  have tr := transport_trig hz
  have hty := transverse_of_nonneg t ht
  have htchart := state_outer_chart t htOuter
  have hA := (A_bounds htchart.2).1
  rw [← htchart.1] at hA
  have ha := mul_nonneg (sub_nonneg.mpr hA) tr.2.2.1
  have hb := mul_nonneg (sub_nonneg.mpr htchart.2.2) (sub_nonneg.mpr tr.2.1)
  simp only [GlobalOuterAnchor.width,Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg tr.2.2.1,
    hty,mul_neg] at hm ⊢
  nlinarith only [hm,ha,hb]

theorem outer_primary_negative_short (s t : State)
    (hs : s.branch.type≠0) (htOuter : t.branch.type≠0)
    (ht : 0≤transverse t) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    z<1/2 := by
  have hgain := outer_primary_negative_gain s t hs htOuter ht hz hm
  have hchart := state_outer_chart s hs
  have ha := (A_bounds hchart.2).2
  rw [← hchart.1] at ha
  by_contra! hn
  have hmono := sine_cosine_monotone (by norm_num [frameCap] : (1/2:ℝ)∈Icc 0 frameCap) hz hn
  simp only at hmono
  have hsin := Real.sin_ge_sub_cube (show (0:ℝ)≤1/2 by norm_num)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := (1/2:ℝ))
  norm_num at hsin hcos
  have hsum : (17/48:ℝ)≤Real.sin z+Real.cos z-1 := by linarith
  have hproduct := mul_le_mul_of_nonneg_left hsum
    (show 0≤c0+1/2 by linarith [c0_bounds.1])
  nlinarith [a0_bounds.2,diagonal_bounds.1]

theorem sine_cosine_short_chord {z : ℝ} (hz : z∈Icc 0 (1/2:ℝ)) :
    (17/24)*z≤Real.sin z+Real.cos z-1 := by
  have h2 := mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
  have h3 := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz.2)
  nlinarith [Real.sin_ge_sub_cube hz.1,Real.one_sub_sq_div_two_le_cos (x := z)]

theorem negative_primary_nonnegative_outer (s t : State)
    (hs : s.branch.type≠0) (htOuter : t.branch.type≠0)
    (ht : 0≤transverse t) {z : ℝ} (hz : z∈Ioc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    kappa<quarterCharge s (transverse t) (-z) := by
  have hgain := outer_primary_negative_gain s t hs htOuter ht (Ioc_subset_Icc_self hz) hm
  have hshort := outer_primary_negative_short s t hs htOuter ht (Ioc_subset_Icc_self hz) hm
  have hchord := sine_cosine_short_chord ⟨hz.1.le,hshort.le⟩
  have hprod := mul_le_mul_of_nonneg_left hchord
    (show 0≤c0+1/2 by linarith [c0_bounds.1])
  have hdiag := mul_nonneg hz.1.le (show 0≤c0+1/2-(1399/1000:ℝ) by
    linarith [diagonal_bounds.1])
  have hJ := J_nonnegative s hs
  dsimp [quarterCharge,potential,kappa,rho]
  nlinarith only [hgain,hprod,hdiag,hJ,hz.1]

theorem negative_primary_outer (s t : State)
    (hs : s.branch.type≠0) (htOuter : t.branch.type≠0)
    {z : ℝ} (hz : z∈Ioc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    kappa<quarterCharge s (transverse t) (-z) := by
  rcases le_total (transverse t) 0 with ht | ht
  · exact negative_primary_nonpositive_outer s t hs htOuter ht hz hm
  · exact negative_primary_nonnegative_outer s t hs htOuter ht hz hm

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
