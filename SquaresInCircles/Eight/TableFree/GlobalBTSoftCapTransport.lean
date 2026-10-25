module

public import SquaresInCircles.Eight.TableFree.GlobalBTSoftCapSlope

/-!
# Complete pointwise soft-cap transport on the original T disk

T remains fixed throughout the comparison.  If its primary is below
the initial cap, the slope-two charge increases from zero.  Otherwise
the intermediate-value theorem supplies the exact cap crossing of
that same T point; high-primary transport applies there and the
slope-two charge increases afterward.  This covers the whole error
interval without an optimizer or active-set assumption.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.SoftCap

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem onCap_of_primary (t : State) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hprimary : HighPrimary.X z≤t.a+1/2) : HighPrimary.OnCap z := by
  have hc := state_circle t
  have hx : 0≤HighPrimary.X z := by linarith [HighPrimary.X_lower hz]
  have hs := pow_le_pow_left₀ hx hprimary 2
  have hb := t.b_nonneg
  exact ⟨hz,by nlinarith only [hc,hs,hb,sq_nonneg t.b]⟩

theorem transport (t : State) {c eta z : ℝ} (hc : (3/5:ℝ)≤c)
    (heta : eta∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) :
    HighPrimary.aligned c eta≤value c eta z t.a t.b := by
  have ha := (ZeroPrimary.coordinates t).2.1.le
  by_cases hhigh : HighPrimary.X z≤t.a+1/2
  · have hh := HighPrimary.circle_transport (state_circle t) ha hhigh hc heta
      (onCap_of_primary t hz hhigh)
    exact hh.trans (first_le_value c eta z t.a t.b)
  · have hlow : t.a+1/2≤HighPrimary.X z := le_of_not_ge hhigh
    have hmono := low_monotone c eta t.b ha
    by_cases hstart : t.a+1/2≤HighPrimary.X 0
    · have hbase := low_zero_lower t c eta hstart
      have hm := hmono (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hz.1
      exact hbase.trans (hm.trans (low_le_value c eta z t.a t.b))
    · have hcont : Continuous HighPrimary.X := by unfold HighPrimary.X; fun_prop
      obtain ⟨s,hs,hcross⟩ := intermediate_value_Icc hz.1 hcont.continuousOn
        (show t.a+1/2∈Icc (HighPrimary.X 0) (HighPrimary.X z) from
          ⟨le_of_not_ge hstart,hlow⟩)
      have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hz.2⟩
      have hcap : HighPrimary.OnCap s := onCap_of_primary t hs' hcross.le
      have hbase := HighPrimary.circle_transport (state_circle t) ha hcross.le hc heta hcap
      rw [← low_eq_first_at_cap hs' hcross] at hbase
      exact hbase.trans ((hmono hs' hz hs.2).trans (low_le_value c eta z t.a t.b))

/-- The original two prefix witnesses now give the same explicit T
force bound as the aligned prefix, with the soft penalty discharged. -/
theorem transported_prefix (a b t : State) {v z c eta : ℝ}
    (ha : 0≤transverse a) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hc : (3/5:ℝ)≤c) (heta : eta∈Icc 0 frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 2)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    2*kappa-R*tailNorm kappa c eta+(kappa-c*Real.sin eta+c*Real.cos eta)/2≤
      v-z+kappa*a.b+c*Real.sin eta*t.a-c*Real.cos eta*t.b := by
  have hpref := AB2_prefix a b t ha hv hz hAB hBT
  have ht := transport t hc heta hz
  rw [HighPrimary.aligned_formula] at ht
  dsimp [value] at ht
  linarith only [hpref,ht]

end SquaresInCircles.Eight.TableFree.GlobalBT.SoftCap
