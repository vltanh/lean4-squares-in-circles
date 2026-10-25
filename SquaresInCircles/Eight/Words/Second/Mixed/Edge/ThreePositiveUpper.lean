module

public import SquaresInCircles.Eight.Words.Second.Mixed.LFiniteGrowth

/-!
# Eight squares: every upper positive-core to positive-outer original owner

The two possible primary witnesses are compared directly with the
aligned pair. The finite source displacement is at most .4x or .2x;
the added frame angle pays for either displacement. The other two
original axes are excluded from their actual signed projections.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.EdgeThreeAligned
open CommonQuarter CorePairGeometry Arithmetic

lemma positive_upper_compare {b A B x k : ℝ} (ht : OuterState A B)
    (hb : 0≤b) (hx : 0≤x) (_hk : 0≤k) (hkg : gp*k≤1)
    (hdisp : 1-A-k*x≤b) :
    (89779/100000:ℝ)<positiveCost b B (Real.pi/2+x) := by
  have hBd : B∈Icc (0:ℝ) outerDiagonal :=
    ⟨(outer_bounds ht).2.2.1,(outer_bounds ht).2.2.2.1⟩
  by_cases hA : 1≤A
  · have hL := L_monotone hBd B1_domain ((unit_target_cut ht).1 hA)
    have hp := mul_nonneg (by norm_num [gp] : (0:ℝ)≤gp) hb
    have hz := positive_zero_cost
    dsimp [positiveCost] at *
    linarith
  · have hb0 : 0≤1-A := by linarith
    have hh := positive_aligned (b := 1-A) ht hb0 (by linarith)
    have hp := mul_nonneg (by norm_num [gp] : (0:ℝ)≤gp)
      (show 0≤b-(1-A)+k*x by linarith)
    have hxg := mul_nonneg (sub_nonneg.mpr hkg) hx
    dsimp [positiveCost] at *
    nlinarith

lemma positive_upper_first {b A B x : ℝ} (ht : OuterState A B)
    (hb : 0≤b) (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+B*Real.sin x) :
    (89779/100000:ℝ)<positiveCost b B (Real.pi/2+x) := by
  have htr := upper_trig hx
  have hA : 1/2≤A := by linarith [(outer_bounds ht).1,outer_endpoint_bounds.2.2.1]
  have hB : B≤9/10 := (outer_bounds ht).2.2.2.1.trans outer_endpoint_bounds.2.2.2.le
  have hp := mul_nonneg (sub_nonneg.mpr hA) htr.2.2.2.2.1
  have hq := mul_nonneg (sub_nonneg.mpr hB) htr.2.2.1
  have hd : 1-A-(2/5)*x≤b := by nlinarith [htr.2.2.2.1]
  exact positive_upper_compare ht hb hx.1 (by norm_num) (by norm_num [gp]) hd

lemma positive_upper_second {a b A B x : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (11/100))
    (hsep : (1+Real.cos x+Real.sin x)/2≤A+a*Real.sin x+b*Real.cos x) :
    (89779/100000:ℝ)<positiveCost b B (Real.pi/2+x) := by
  have hxs : x∈Icc (0:ℝ) (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have htr := upper_trig hxs
  have hshort := short_upper_trig hx
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hA : A≤283/200 := (outer_bounds ht).2.1.trans outer_endpoint_bounds.2.1.le
  have hAc := mul_nonneg (sub_nonneg.mpr hA) htr.2.2.2.2.1
  have has := mul_nonneg (sub_nonneg.mpr hcore.2.1) htr.2.2.1
  have hxc := mul_nonneg hx.1 (sub_nonneg.mpr hshort.1)
  have hd : 1-A-(1/5)*x≤b := by
    by_contra hbad
    have hn := mul_neg_of_neg_of_pos
      (show b-(1-A)+(1/5)*x<0 by linarith)
      (show 0<Real.cos x by linarith [htr.1])
    nlinarith [hshort.2,htr.2.2.2.1]
  exact positive_upper_compare ht hcore.2.2.1 hx.1
    (by norm_num) (by norm_num [gp]) hd

/-- All four original weak separating axes, including aligned ties. -/
theorem positive_upper_original {a b A B x : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (7/10))
    (j : Fin 4) (hm : 0≤forwardMargin j a b A B 1 1 (Real.pi/2+x)) :
    threshold<positiveCost b B (Real.pi/2+x) := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  by_cases hlarge : (42/25:ℝ)≤Real.pi/2+x
  · exact positive_large_angle ht hcore.2.2.1 hlarge
  have hsmall : x∈Icc (0:ℝ) (11/100) :=
    ⟨hx.1,by linarith [pi_hand_enclosure.1]⟩
  have htr := upper_trig hx
  have hshort := short_upper_trig hsmall
  have hc0 : 0≤Real.cos x := by linarith [htr.1]
  have hs0 := htr.2.2.1
  have hA : A<(283/200:ℝ) := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hBc := mul_nonneg ht.1 hc0
  have hbs := mul_nonneg hcore.2.2.1 hs0
  have hw := edgeWidth_positive_formula hx
  fin_cases j
  · have hh : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+B*Real.sin x := by
      norm_num [forwardMargin,Real.sin_add,Real.cos_add,abs_of_nonneg hc0,
        abs_of_nonneg hs0,hw] at hm
      linarith
    have hv := positive_upper_first ht hcore.2.2.1 hx hh
    norm_num [threshold] at *
    linarith
  · have hh : (1+Real.cos x+Real.sin x)/2≤A+a*Real.sin x+b*Real.cos x := by
      norm_num [forwardMargin,Real.sin_add,Real.cos_add,abs_of_nonneg hc0,
        abs_of_nonneg hs0,hw] at hm
      linarith
    have hv := positive_upper_second hs ht hsmall hh
    norm_num [threshold] at *
    linarith
  · have hh : 0≤a*Real.cos x-b*Real.sin x-B-
        (1+Real.cos x+Real.sin x)/2 := by
      norm_num [forwardMargin,Real.sin_add,Real.cos_add,abs_of_nonneg hc0,
        abs_of_nonneg hs0,hw] at hm
      linarith
    have hac := mul_nonneg (show 0≤7/12-a by linarith [hcore.2.1]) hc0
    have hcu := htr.2.1
    nlinarith [ht.1]
  · have hh : 0≤a+A*Real.sin x-B*Real.cos x-
        (1+Real.cos x+Real.sin x)/2 := by
      norm_num [forwardMargin,Real.sin_add,Real.cos_add,abs_of_nonneg hc0,
        abs_of_nonneg hs0,hw] at hm
      linarith
    have hAs := mul_nonneg (show 0≤283/200-A by linarith) hs0
    nlinarith [hcore.2.1,hshort.1,htr.2.2.2.1,hsmall.2]

end SquaresInCircles.Eight.SecondWord.EdgeThreeAligned
