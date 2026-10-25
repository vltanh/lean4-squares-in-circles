module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighCoreScalar

/-!
# The remaining actual positive-core target

The original negative primary forces the target onto its own flat side.
For angles above `3/10`, that same projection forces the original outer
source below transverse coordinate `33/100`, where its retained marker
correction pays the uniform scalar loss.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

open FramePair ZeroPrimary FrameCircleArc FrameLowArc GlobalZeroSign
open GlobalOuterAnchor GlobalQuarterSign

theorem negative_core_domain (s t : State) (htCore : t.branch.type=0)
    (ht : 0<transverse t) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    t.a=7/12 ∧ z<1/2 := by
  have hy := transverse_of_nonneg t ht.le
  have tr := transport_trig hz
  have hm' : (1+Real.cos z+Real.sin z)/2≤ s.a-t.a*Real.sin z-t.b*Real.cos z := by
    simp only [GlobalOuterAnchor.width,Real.sin_neg,Real.cos_neg,abs_neg,
      abs_of_nonneg tr.2.2.1,hy,mul_neg] at hm
    linarith
  have hd := one_negative_negative_domain t s hz hm'
  exact ⟨(CommonQuarter.core_small_side (FrameCoreArc.state_core_chart t htCore) hd.1).1,hd.2⟩

def coreSourceThreshold (z : ℝ) : ℝ :=
  1/2+(1/2)*Real.cos z+(13/12)*Real.sin z

theorem coreSourceThreshold_monotone :
    MonotoneOn coreSourceThreshold (Icc 0 frameCap) := by
  have hd (z : ℝ) : HasDerivAt coreSourceThreshold
      (-(1/2)*Real.sin z+(13/12)*Real.cos z) z := by
    have h := ((hasDerivAt_const z (1/2:ℝ)).add
      ((Real.hasDerivAt_cos z).const_mul (1/2))).add
      ((Real.hasDerivAt_sin z).const_mul (13/12))
    convert h using 1
    · funext y
      simp only [coreSourceThreshold,Pi.add_apply]
    · ring
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z _ => (hd z).continuousAt.continuousWithinAt
  · exact fun z _ => hd z
  · intro z hz
    have tr := transport_trig (Ioo_subset_Icc_self hz)
    linarith [tr.1,tr.2.2.2.1]

theorem negative_core_small_source (s t : State) (hs : s.branch.type≠0)
    (ht : 0<transverse t) (hflat : t.a=7/12)
    {z : ℝ} (hz : z∈Icc (3/10:ℝ) frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    s.b<33/100 := by
  have hz' : z∈Icc 0 frameCap := ⟨by linarith [hz.1],hz.2⟩
  have tr := transport_trig hz'
  have hyprod := mul_pos ht (show 0<Real.cos z by linarith [tr.1])
  have hmargin : coreSourceThreshold z<s.a := by
    simp only [GlobalOuterAnchor.width,Real.sin_neg,Real.cos_neg,abs_neg,
      abs_of_nonneg tr.2.2.1,hflat,mul_neg] at hm
    dsimp [coreSourceThreshold]
    linarith
  have hmono := coreSourceThreshold_monotone
    (by norm_num [frameCap] : (3/10:ℝ)∈Icc 0 frameCap) hz' hz.1
  have hsin := Real.sin_ge_sub_cube (show (0:ℝ)≤3/10 by norm_num)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := (3/10:ℝ))
  have ha : (10381/8000:ℝ)<s.a := by
    dsimp [coreSourceThreshold] at hmono hmargin
    norm_num at hsin hcos
    linarith
  have hc := s.outer_eq hs
  by_contra! hb
  have hsource : (14381/8000:ℝ)^2<(s.a+1/2)^2 := by
    nlinarith [s.a_pos]
  have htangent : (83/100:ℝ)^2≤(s.b+1/2)^2 := by
    nlinarith [s.b_nonneg]
  norm_num [Q0] at hc hsource htangent
  linarith

theorem negative_primary_core (s t : State) (hs : s.branch.type≠0)
    (htCore : t.branch.type=0) (ht : 0<transverse t)
    {z : ℝ} (hz : z∈Ioc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+t.a*Real.sin (-z)-transverse t*Real.cos (-z)) :
    kappa<quarterCharge s (transverse t) (-z) := by
  have hd := negative_core_domain s t htCore ht (Ioc_subset_Icc_self hz) hm
  have hmFlat : GlobalOuterAnchor.width (-z)≤ s.a+(7/12)*Real.sin (-z)-transverse t*Real.cos (-z) := by
    simpa only [hd.1] using hm
  have htransfer := core_primary_scaled_transfer s hs ⟨hz.1.le,hd.2.le⟩ hmFlat
  have hc : 0<Real.cos z := by linarith [(transport_trig (Ioc_subset_Icc_self hz)).1]
  have hscalar : 0<coreL z+rho*J s := by
    by_cases hsmall : z≤3/10
    · have hL := coreL_positive_short ⟨hz.1,hsmall⟩
      have hJ := mul_nonneg (show 0≤rho by norm_num [rho]) (J_nonnegative s hs)
      linarith
    · have hsource := negative_core_small_source s t hs ht hd.1
        ⟨(lt_of_not_ge hsmall).le,hz.2⟩ hm
      have hJ := J_small_transverse s hs hsource.le
      have hL := coreL_lower ⟨hz.1.le,hd.2.le⟩
      dsimp [rho]
      linarith
  have hpositive := (mul_pos hscalar hc).trans_le htransfer
  have hgap := (mul_pos_iff_of_pos_right hc).1 hpositive
  linarith

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
