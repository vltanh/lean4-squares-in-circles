module

public import SquaresInCircles.Eight.TableFree.GlobalGASecantDPositiveEndpoint
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2HighSecant

/-!
# Uniform growth of the actual secant-D correction

Uncompiled equation (22) of the negative-DE / positive-BT3 companion.
Both smooth branches have the same value at sec(s)=c. Their .96 slope
reserve is transported across that actual transition by the continuous
switch theorem. Neither a global derivative at the switch nor a fixed
support branch is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.SecantD.PositiveEndpoint
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

@[simp] theorem correction_zero (c : ℝ) : correction c 0=0 := by
  simp [correction,sec,NegativeELargeA.secant]

theorem correction_switch {c s : ℝ} (hc : c∈Icc d cUpper)
    (hs : s∈Icc 0 frameCap) :
    (if 1-c*Real.cos s≤0 then NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s-(24/25)*s
      else fullCorrection c s-(24/25)*s)=correction c s-(24/25)*s := by
  have hcos := NegativeESecant.cos_pos hs
  by_cases he : 1-c*Real.cos s≤0
  · have hsc : sec s≤c := (div_le_iff₀ hcos).2 (by linarith)
    rw [if_pos he,correction_diagonal hc hs hsc]
  · have hcs : c≤ sec s := (le_div_iff₀ hcos).2 (by linarith)
    rw [if_neg he,correction_full hc hs hcs]

/-- The interval includes both original angle endpoints and the support tie. -/
theorem correction_growth {c x y : ℝ} (hc : c∈Icc d cUpper)
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    (24/25)*(y-x)≤correction c y-correction c x := by
  have hd : MonotoneOn
      (fun s => NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s-(24/25)*s) (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro s hs
      exact ((NegativeESecant.gain_hasDerivAt (GlobalGA.Secondary.diagonal-1/2) hs).sub
        ((hasDerivAt_id s).const_mul (24/25))).continuousAt.continuousWithinAt
    · intro s hs
      exact (NegativeESecant.gain_hasDerivAt (GlobalGA.Secondary.diagonal-1/2) (Ioo_subset_Icc_self hs)).sub
        ((hasDerivAt_id s).const_mul (24/25))
    · intro s hs
      have hh := NegativeELargeA.diagonal_derivative_lower (Ioo_subset_Icc_self hs)
      dsimp [NegativeELargeA.M] at hh
      linarith
  have hf : MonotoneOn (fun s => fullCorrection c s-(24/25)*s) (Icc 0 frameCap) := by
    have hder {s : ℝ} (hs : s∈Icc 0 frameCap) :
        HasDerivAt (fun s => fullCorrection c s-(24/25)*s)
          (secantGainDeriv qCap c s-24/25) s := by
      have h1 := secantGain_hasDerivAt qCap c (NegativeESecant.cos_pos hs).ne'
      have h2 := ((h1.add_const (sortedSupport 1 c)).sub_const (fullSupport 1 c)).sub
        ((hasDerivAt_id' s).const_mul (24/25:ℝ))
      convert h2 using 1
      · funext x; simp only [fullCorrection,Pi.sub_apply]
      · ring
    apply monoOn_of_hasDeriv_nonneg
      (fun s hs => (hder hs).continuousAt.continuousWithinAt)
      (fun s hs => hder (Ioo_subset_Icc_self hs))
    intro s hs
    have hh := NegativeDEPositiveTD.HighSecant.full_derivative_lower
      (show (43/50:ℝ)≤c by dsimp [d] at hc; linarith [hc.1]) (Ioo_subset_Icc_self hs)
    linarith
  have hm := monotone_continuous_switch (e:=fun s => 1-c*Real.cos s)
    (by fun_prop) hd hf (fun s hs he => by
      have hsc : sec s=c := (div_eq_iff (NegativeESecant.cos_pos hs).ne').2 (by linarith)
      have hdiag := correction_diagonal hc hs hsc.le
      have hfull := correction_full hc hs hsc.ge
      linarith)
  have hh := hm hx hy hxy
  dsimp only at hh
  rw [correction_switch hc hx,correction_switch hc hy] at hh
  linarith

theorem correction_lower {c s : ℝ} (hc : c∈Icc d cUpper) (hs : s∈Icc 0 frameCap) :
    (24/25)*s≤correction c s := by
  have hh := correction_growth hc (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hs hs.1
  simpa only [correction_zero,sub_zero] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.SecantD.PositiveEndpoint
