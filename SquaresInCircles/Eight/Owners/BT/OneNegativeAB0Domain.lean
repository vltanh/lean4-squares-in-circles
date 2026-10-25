module

public import SquaresInCircles.Eight.Owners.BT.OneNegativePrefix

/-!
# Eight squares: the original B chart for the effective AB0--BT1 cap

For 0 <= AB <= -BT, both signed B cases have transverse magnitude
below one half.  The positive case is excluded by exact whole-range
projection bounds on either side of 41/100.  The true B radial chart
then gives its primary bound, including the core side endpoint.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OneNegative

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem sin_monotone : MonotoneOn Real.sin (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · fun_prop
  · exact fun x _ => Real.hasDerivAt_sin x
  · intro x hx
    linarith [(transport_trig (Ioo_subset_Icc_self hx)).1]

theorem cos_antitone : AntitoneOn Real.cos (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · fun_prop
  · exact fun x _ => Real.hasDerivAt_cos x
  · intro x hx
    have hh := (transport_trig (Ioo_subset_Icc_self hx)).2.2.1
    linarith

theorem half_secondary_primary_upper (b : State) (hb : (1/2:ℝ)≤b.b) : b.a<151/125 := by
  have hc := state_circle b
  have ha := b.a_pos
  have hsq := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num)
    (show 1≤b.b+1/2 by linarith) 2
  norm_num [Q0] at hc
  nlinarith

theorem width_cut_lower : (463/200:ℝ)<1+Real.cos (41/100)+Real.sin (41/100) := by
  have hc := cos_lower_six (show (0:ℝ)≤41/100 by norm_num)
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤41/100 by norm_num)
  norm_num at hc hs
  linarith

theorem AB0_intermediate_B_small (a b t : State) {v z : ℝ}
    (ha : 0≤transverse a) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hvz : v≤z) (hAB : GlobalOuterAnchor.width v≤projection false a b v 0)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) : b.b<1/2 := by
  by_cases hy : transverse b≤0
  · exact negative_B_small b t hz hy hBT
  · have hby := transverse_of_nonneg b (le_of_not_ge hy)
    have hay := transverse_of_nonneg a ha
    have hvtr := transport_trig hv
    have hztr := transport_trig hz
    have hAB' := hAB
    have hBT' := hBT
    rw [width_positive hv] at hAB'
    rw [width_negative hz] at hBT'
    dsimp [projection] at hAB' hBT'
    rw [hay,hby] at hAB'
    rw [hby] at hBT'
    simp only [Real.sin_neg,Real.cos_neg] at hBT'
    by_contra! hb
    have haB := half_secondary_primary_upper b hb
    have hav := (ZeroPrimary.coordinates a).2.2.2.2
    have hat := (ZeroPrimary.coordinates t).2.1
    have hwidth : (1:ℝ)≤(1+Real.cos v+Real.sin v)/2 := by
      have hh := sine_cosine_monotone
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hv hv.1
      simp only [Real.sin_zero,Real.cos_zero,zero_add] at hh
      linarith
    by_cases hcut : v≤41/100
    · have hs : Real.sin v≤41/100 := (Real.sin_le hv.1).trans hcut
      have hc := Real.one_sub_sq_div_two_le_cos (x := v)
      have hsq := pow_le_pow_left₀ hv.1 hcut 2
      have hcos : (18319/20000:ℝ)≤Real.cos v := by nlinarith only [hc,hsq]
      have hp1 := mul_le_mul haB.le hs hvtr.2.2.1
        (by norm_num : (0:ℝ)≤151/125)
      have hp2 := mul_le_mul hb hcos (by norm_num : (0:ℝ)≤18319/20000) b.b_nonneg
      nlinarith only [hAB',hav,hwidth,hp1,hp2]
    · have hsin := sin_monotone hv hz hvz
      have hcos := cos_antitone hv hz hvz
      have hp1 := mul_nonneg b.a_pos.le (sub_nonneg.mpr hsin)
      have hp2 := mul_nonneg b.b_nonneg (sub_nonneg.mpr hcos)
      have hwidthOrder := sine_cosine_monotone hv hz hvz
      have hcutOrder := sine_cosine_monotone
        (show (41/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hv (by linarith)
      have hlarge : (463/200:ℝ)<1+Real.cos v+Real.sin v := by
        linarith [width_cut_lower]
      nlinarith only [hAB',hBT',hp1,hp2,hwidthOrder,hlarge,hav,hat]

end SquaresInCircles.Eight.GlobalBT.OneNegative
