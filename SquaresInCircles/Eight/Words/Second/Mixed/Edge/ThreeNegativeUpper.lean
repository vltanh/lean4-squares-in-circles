module

public import SquaresInCircles.Eight.Words.Second.Mixed.LFiniteGrowth

/-!
# Eight squares: every upper negative-core to positive-outer original owner

Each primary inequality controls the total change in the original two
labels from an aligned pair. The proof treats the complete core corner,
including the weak side join, and keeps all four original SAT owners.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.EdgeThreeAligned
open CommonQuarter CorePairGeometry Arithmetic

lemma negative_upper_unit {a b B x : ℝ} (hs : CoreState a b) (_hx : 0≤x)
    (hbudget : gn*b+L B-L B1≤x) :
    (4489/5000:ℝ)<negativeCost a b B (Real.pi/2+x) := by
  have hu := negative_core_upper hs
  have hz := negative_zero_cost
  dsimp [negativeCost,negativeSideCost,sideH] at *
  linarith

lemma negative_upper_side_compare {a b A B x k : ℝ} (ht : OuterState A B)
    (hb : 0≤b) (ha : a=7/12) (hA : 1≤A)
    (hx : 0≤x) (hk : 0≤k) (hkg : gn*k≤1)
    (hdisp : b≤A-1+k*x) :
    (44889/50000:ℝ)<negativeCost a b B (Real.pi/2+x) := by
  have hAhi := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hb0 : A-1∈Icc (0:ℝ) (1/2) := ⟨by linarith,by linarith⟩
  have hh := negative_side_aligned (b := A-1) ht hb0.1 (by linarith)
  have hd := sideH_increment hb hb0 hx hk hdisp
  have hxg := mul_nonneg (sub_nonneg.mpr hkg) hx
  have he : MixedThree.negativeCore a b=sideH b := by simpa [ha] using (sideH_eq (b := b))
  dsimp [negativeCost,negativeSideCost] at *
  rw [he]
  nlinarith

lemma negative_upper_large_compare {a b A B x : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hA : 1≤A) (hx : (3/10:ℝ)≤x)
    (hdisp : b≤A-1+(53/100)*x) :
    (44889/50000:ℝ)<negativeCost a b B (Real.pi/2+x) := by
  have hAhi := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hb0 : 0≤A-1 := by linarith
  have hb0h : A-1≤83/200 := by linarith
  have hsq := pow_le_pow_left₀ hb0 hb0h 2
  have hh := negative_side_aligned (b := A-1) ht hb0 (by linarith)
  have hu := negative_core_upper hs
  have hp := mul_nonneg (by norm_num [gn] : (0:ℝ)≤gn)
    (show 0≤A-1+(53/100)*x-b by linarith)
  dsimp [negativeCost,negativeSideCost,sideH,gn,zn] at *
  nlinarith

lemma negative_first_small {b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤-b+A*Real.cos x+B*Real.sin x) :
    b<1/2 := by
  have ht0 := positive_trig hx
  have hcs : Real.cos x^2+Real.sin x^2=1 := by nlinarith [Real.sin_sq_add_cos_sq x]
  have he :
      ((A+1/2)*Real.cos x+(B+1/2)*Real.sin x)^2+
        ((A+1/2)*Real.sin x-(B+1/2)*Real.cos x)^2=Q0 := by
    calc
      _ = ((A+1/2)^2+(B+1/2)^2)*(Real.cos x^2+Real.sin x^2) := by ring
      _ = Q0 := by rw [ht.2.2,hcs]; ring
  by_contra hn
  have hb : 1/2≤b := le_of_not_gt hn
  have hd : 2≤(A+1/2)*Real.cos x+(B+1/2)*Real.sin x := by
    nlinarith [ht0.2.2.2.2.2]
  have hp := mul_nonneg (sub_nonneg.mpr hd)
    (show 0≤(A+1/2)*Real.cos x+(B+1/2)*Real.sin x+2 by linarith)
  have hq := sq_nonneg ((A+1/2)*Real.sin x-(B+1/2)*Real.cos x)
  norm_num [Q0] at he
  nlinarith

lemma negative_upper_first {a b A B x : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤-b+A*Real.cos x+B*Real.sin x) :
    threshold<negativeCost a b B (Real.pi/2+x) := by
  have htr := upper_trig hx
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hB : B≤9/10 := (outer_bounds ht).2.2.2.1.trans outer_endpoint_bounds.2.2.2.le
  have hBs := mul_nonneg (sub_nonneg.mpr hB) htr.2.2.1
  by_cases hA : 1≤A
  · have hAc := mul_nonneg (show 0≤A-1/2 by linarith) htr.2.2.2.2.1
    have hdisp : b≤A-1+(2/5)*x := by nlinarith [htr.2.2.2.1]
    have ha := (CommonQuarter.core_small_side hs (negative_first_small ht hx hsep)).1
    have hh := negative_upper_side_compare ht hcore.2.2.1 ha hA hx.1
      (show (0:ℝ)≤2/5 by norm_num) (by norm_num [gn]) hdisp
    norm_num [threshold] at *
    linarith
  · have hdelta : 0≤1-A := by linarith
    have hl := unit_label_increment ht (by linarith)
    have hp := mul_nonneg hcore.2.2.1
      (show 0≤(9/5:ℝ)-gn by norm_num [gn])
    have hc := mul_nonneg hdelta
      (show 0≤(9/5)*Real.cos x-343/250 by linarith [htr.1])
    have hcut : b+(1-A)*Real.cos x≤(2/5)*x := by
      nlinarith [htr.2.2.2.1,htr.2.2.2.2.1]
    have hbudget : gn*b+L B-L B1≤x := by nlinarith [hx.1]
    have hh := negative_upper_unit hs hx.1 hbudget
    norm_num [threshold] at *
    linarith

lemma negative_second_displacement {a b A B x : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤A+a*Real.sin x-b*Real.cos x) :
    b≤A-1+(53/100)*x := by
  have htr := upper_trig hx
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hA : A≤283/200 := (outer_bounds ht).2.1.trans outer_endpoint_bounds.2.1.le
  have hp := mul_nonneg (sub_nonneg.mpr hA) htr.2.2.2.2.1
  have hq := mul_nonneg (sub_nonneg.mpr hcore.2.1) htr.2.2.1
  have hr := mul_nonneg hx.1 (show 0≤Real.cos x-19121/25000 by linarith [htr.1])
  by_contra hbad
  have hn := mul_pos (show 0<b-(A-1)-(53/100)*x by linarith)
    (show 0<Real.cos x by linarith [htr.1])
  nlinarith [htr.2.2.2.1,htr.2.2.2.2.2]

lemma negative_second_corner_angle {a b A B x : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (7/10)) (hb : 1/2≤b)
    (hsep : (1+Real.cos x+Real.sin x)/2≤A+a*Real.sin x-b*Real.cos x) :
    (3/10:ℝ)<x := by
  have htr := upper_trig hx
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hA := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  by_contra hn
  have hxhi : x≤3/10 := le_of_not_gt hn
  have hsq := pow_le_pow_left₀ hx.1 hxhi 2
  have hc : (191/200:ℝ)≤Real.cos x := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hp := mul_nonneg (sub_nonneg.mpr hb) (show 0≤Real.cos x by linarith [htr.1])
  have hq := mul_nonneg (sub_nonneg.mpr hcore.2.1) htr.2.2.1
  nlinarith [htr.2.2.2.1]

lemma negative_upper_second {a b A B x : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤A+a*Real.sin x-b*Real.cos x) :
    threshold<negativeCost a b B (Real.pi/2+x) := by
  have htr := upper_trig hx
  have hcore := CoreAngleEndpoint.state_bounds hs
  by_cases hA : 1≤A
  · have hd := negative_second_displacement hs ht hx hsep
    by_cases hb : b<1/2
    · have ha := (CommonQuarter.core_small_side hs hb).1
      have hh := negative_upper_side_compare ht hcore.2.2.1 ha hA hx.1
        (show (0:ℝ)≤53/100 by norm_num) (by norm_num [gn]) hd
      norm_num [threshold] at *
      linarith
    · have ha := negative_second_corner_angle hs ht hx (by linarith) hsep
      have hh := negative_upper_large_compare hs ht hA ha.le hd
      norm_num [threshold] at *
      linarith
  · have hdelta : 0≤1-A := by linarith
    have hl := unit_label_increment ht (by linarith)
    have hp := mul_nonneg hcore.2.2.1
      (show 0≤(7/5)*Real.cos x-gn by norm_num [gn]; linarith [htr.1])
    have hq := mul_nonneg hdelta (show 0≤(7/5:ℝ)-343/250 by norm_num)
    have hr := mul_nonneg (sub_nonneg.mpr hcore.2.1) htr.2.2.1
    have hcut : b*Real.cos x+(1-A)≤(1/2)*(1-Real.cos x)+(1/12)*Real.sin x := by
      nlinarith
    have hbudget : gn*b+L B-L B1≤x := by
      nlinarith [htr.2.2.2.1,htr.2.2.2.2.2,hx.1]
    have hh := negative_upper_unit hs hx.1 hbudget
    norm_num [threshold] at *
    linarith

lemma negative_upper_fourth {a b A B x : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x-B*Real.cos x) :
    threshold<negativeCost a b B (Real.pi/2+x) := by
  have htr := upper_trig hx
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hA := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hcoef := mul_nonneg (show 0≤283/200-A by linarith) htr.2.2.1
  have hc0 : 0<Real.cos x := by linarith [htr.1]
  have hxc := mul_nonneg hx.1 (show 0≤Real.cos x-19121/25000 by linarith [htr.1])
  have hsec : 1≤(1+(23/50)*x)*Real.cos x := by
    nlinarith [htr.2.2.2.2.2]
  have htan : Real.sin x≤(131/100)*x*Real.cos x := by
    nlinarith [htr.2.2.2.1]
  have hB :
      B≤(1/12)*(1+(23/50)*x)+(183/200)*(131/100)*x-1/2 := by
    apply (mul_le_mul_iff_left₀ hc0).mp
    nlinarith [hcore.2.1]
  have hL := L_global_affine
    (show B∈Icc (0:ℝ) outerDiagonal from
      ⟨(outer_bounds ht).2.2.1,(outer_bounds ht).2.2.2.1⟩)
  have hH := negative_core_coarse hs
  dsimp [negativeCost,threshold]
  nlinarith [pi_hand_enclosure.1,hx.2]

theorem negative_upper_original {a b A B x : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (7/10))
    (j : Fin 4) (hm : 0≤forwardMargin j a b A B (-1) 1 (Real.pi/2+x)) :
    threshold<negativeCost a b B (Real.pi/2+x) := by
  have htr := upper_trig hx
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hc0 : 0≤Real.cos x := by linarith [htr.1]
  have hs0 := htr.2.2.1
  have hw := edgeWidth_positive_formula hx
  fin_cases j
  · apply negative_upper_first hs ht hx
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,abs_of_nonneg hc0,
      abs_of_nonneg hs0,hw] at hm
    linarith
  · apply negative_upper_second hs ht hx
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,abs_of_nonneg hc0,
      abs_of_nonneg hs0,hw] at hm
    linarith
  · have hac := mul_nonneg (show 0≤7/12-a by linarith [hcore.2.1]) hc0
    have hbs := mul_nonneg (show 0≤7/12-b by linarith [hcore.2.1,hcore.2.2.2.1]) hs0
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,abs_of_nonneg hc0,
      abs_of_nonneg hs0,hw] at hm
    nlinarith [htr.2.1,Real.sin_le_one x,ht.1]
  · apply negative_upper_fourth hs ht hx
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,abs_of_nonneg hc0,
      abs_of_nonneg hs0,hw] at hm
    linarith

end SquaresInCircles.Eight.SecondWord.EdgeThreeAligned
