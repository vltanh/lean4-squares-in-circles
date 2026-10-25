module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveATD0DFunctions

/-!
# The positive-A fixed stress minimizes the actual D term at alignment

Uncompiled transcription of Section 3.2 of the positive-A/TD0 hand proof.  Both
original angles remain in the norm and in their common variation
constraint.  The concluding inequality is for the original contained
sorted point, at any source radius below the fixed ceiling.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveATD0
open Secondary PositiveAngularEnvelope

theorem d_positive_error_comparison {z d : ℝ}
    (hz : |z|≤frameCap) (hd : d∈Icc 0 frameCap) : dStress z 0≤dStress z d := by
  have hdi : |d|≤frameCap := by rw [abs_of_nonneg hd.1]; exact hd.2
  have hforce := d_force_positive hz hdi
  let P := clippedPoint hforce.1.le hforce.2
  have hzero := d_force_positive hz (d:=0) (by norm_num [frameCap])
  have hs0 := raw_clipped_support (f:=dF z 0) (g:=dG z 0) P.circle.le P.sorted
    (show 0≤P.a+P.b+1 by linarith [P.corners_nonneg.1,P.corners_nonneg.2]) hzero.1.le
  have hsupport : clippedSupport (dF z d) (dG z d)-clippedSupport (dF z 0) (dG z 0)≤
      P.a*(Real.cos d-1)+P.b*Real.sin d := by
    rw [P.supports]
    simp only [dF,dG,Real.cos_zero,Real.sin_zero,add_zero] at hs0 ⊢
    linarith
  have htrig := transport_trig hd
  have hsin := Real.sin_le hd.1
  have ha : 0≤P.a-1/2 := by linarith [P.primary_lower,diagonal_bounds.1]
  have hfirst := mul_nonneg ha (sub_nonneg.mpr (Real.cos_le_one d))
  have hsecond := mul_nonneg (sub_nonneg.mpr P.tangent_upper) htrig.2.2.1
  have hthird := mul_nonneg
    (show 0≤GlobalGA.Secondary.diagonal-1/2 by linarith [diagonal_bounds.1])
    (show 0≤d-Real.sin d by linarith)
  have hcharge := mul_nonneg
    (show 0≤charge-GlobalGA.Secondary.diagonal+1/2 by
      dsimp [charge]; linarith [diagonal_bounds.2]) hd.1
  have hchange : 0≤edgeWidth d-1-P.a*(Real.cos d-1)-P.b*Real.sin d+charge*d := by
    rw [edgeWidth_positive_formula hd]
    nlinarith
  dsimp [dStress]
  have hwidth0 : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
  rw [hwidth0]
  nlinarith

theorem d_negative_error_comparison {z w : ℝ}
    (hz : |z|≤frameCap) (hw : w∈Icc 0 frameCap)
    (hs : |z-w|≤frameCap) : dStress z 0≤dStress z (-w) := by
  have hxcap {x : ℝ} (hx : x∈Icc 0 w) : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hw.2⟩
  have hxsum {x : ℝ} (hx : x∈Icc 0 w) : |z-x|≤frameCap := by
    have hz' := abs_le.mp hz
    have hs' := abs_le.mp hs
    exact abs_le.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hmonoD : MonotoneOn (dNegativeDiagonal z) (Icc 0 w) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (dNegativeDiagonal_hasDerivAt z x).continuousAt.continuousWithinAt
    · intro x hx
      exact dNegativeDiagonal_hasDerivAt z x
    · intro x hx
      exact (dNegativeDiagonal_slope (hxcap (Ioo_subset_Icc_self hx))).le
  have hmonoF : MonotoneOn (dNegativeFull z) (Icc 0 w) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (dNegativeFull_hasDerivAt (hxsum hx)).continuousAt.continuousWithinAt
    · intro x hx
      exact dNegativeFull_hasDerivAt (hxsum (Ioo_subset_Icc_self hx))
    · intro x hx
      have hxi := hxcap (Ioo_subset_Icc_self hx)
      have hh := dVelocity_sine_lower (abs_le.mp (hxsum (Ioo_subset_Icc_self hx))) hxi
        (show z-x+x≤frameCap by linarith [(abs_le.mp hz).2])
      linarith
  have hmatch (x : ℝ) (hx : x∈Icc 0 w)
      (he : dF z (-x)-dG z (-x)=0) : dNegativeDiagonal z x=dNegativeFull z x := by
    have hh := d_force_positive hz (d:= -x)
      (by rw [abs_neg,abs_of_nonneg hx.1]; exact (hxcap hx).2)
    rw [dNegativeDiagonal_eq z (hxcap hx),dNegativeFull_eq z (hxcap hx),
      full_at_diagonal (sub_eq_zero.mp he) hh.1.le]
  have hmono := monotone_continuous_switch
    (e:=fun x => dF z (-x)-dG z (-x))
    (by dsimp [dF,dG]; fun_prop) hmonoD hmonoF hmatch
  have h0 := dStress_negative_eq z (w:=0) (by norm_num [frameCap])
  have h1 := dStress_negative_eq z hw
  have hh := hmono ⟨le_rfl,hw.1⟩ ⟨hw.1,le_rfl⟩ hw.1
  simp only [neg_zero] at h0 hh
  rw [h0,h1]
  exact hh

theorem d_positive_zero_comparison {z : ℝ} (hz : z∈Icc 0 frameCap) :
    dStress 0 0≤dStress z 0 := by
  have hmonoD : MonotoneOn dPositiveDiagonal (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (dPositiveDiagonal_hasDerivAt x).continuousAt.continuousWithinAt
    · intro x hx
      exact dPositiveDiagonal_hasDerivAt x
    · intro x hx
      exact (dPositiveDiagonal_slope (Ioo_subset_Icc_self hx)).le
  have hmonoF : MonotoneOn dPositiveFull (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (dPositiveFull_hasDerivAt
        (by rw [abs_of_nonneg hx.1]; exact hx.2)).continuousAt.continuousWithinAt
    · intro x hx
      exact dPositiveFull_hasDerivAt (by rw [abs_of_pos hx.1]; exact hx.2.le)
    · intro x hx
      exact (dPositiveFull_slope (Ioo_subset_Icc_self hx)).le
  have hmatch (x : ℝ) (hx : x∈Icc 0 frameCap)
      (he : dF x 0-dG x 0=0) : dPositiveDiagonal x=dPositiveFull x := by
    have hh := d_force_positive (z:=x) (d:=0)
      (by rw [abs_of_nonneg hx.1]; exact hx.2) (by norm_num [frameCap])
    rw [dPositiveDiagonal_eq hx,dPositiveFull_eq hx,
      full_at_diagonal (sub_eq_zero.mp he) hh.1.le]
  have hmono := monotone_continuous_switch
    (e:=fun x => dF x 0-dG x 0)
    (by dsimp [dF,dG]; fun_prop) hmonoD hmonoF hmatch
  rw [dStress_positive_zero_eq (z:=0) (by norm_num [frameCap]),dStress_positive_zero_eq hz]
  exact hmono (by norm_num [frameCap]) hz hz.1

theorem d_negative_zero_comparison {z : ℝ} (hz : z∈Icc (-frameCap) 0) :
    dStress 0 0≤dStress z 0 := by
  obtain ⟨w,hwz⟩ : ∃ w : ℝ, w= -z := ⟨_,rfl⟩
  have hw : w∈Icc 0 frameCap := ⟨by rw [hwz]; linarith [hz.2],by rw [hwz]; linarith [hz.1]⟩
  have hzw : z= -w := by rw [hwz]; ring
  have ht := transport_trig hw
  have hfg : dF z 0≤dG z 0 := by
    rw [hzw]
    dsimp [dF,dG,lowC]
    simp only [Real.cos_zero,Real.sin_zero,Real.cos_neg,Real.sin_neg,add_zero]
    linarith [ht.1,ht.2.2.1]
  have hid : dStress z 0-((1+lowC)*(1-GlobalGA.Secondary.diagonal))=
      lowC*(GlobalGA.Secondary.diagonal+1/2)*Real.sin w+
        lowC*(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos w)-charge*w := by
    rw [dStress,clippedSupport,ite_eq_left hfg,hzw,edgeWidth_negative_formula hw]
    norm_num [diagonalSupport,dF,dG,edgeWidth,pairWidth,lowC]
    ring
  have hs := Real.sin_ge_sub_cube hw.1
  have hw2 : w^2≤(7/10:ℝ)^2 :=
    pow_le_pow_left₀ hw.1 (by simpa [frameCap] using hw.2) 2
  have hw3 := mul_le_mul_of_nonneg_right hw2 hw.1
  have hsin : (9/10)*w≤Real.sin w := by nlinarith
  have hsinmul := mul_le_mul_of_nonneg_left hsin
    (show 0≤lowC*(GlobalGA.Secondary.diagonal+1/2) by
      dsimp [lowC]; linarith [diagonal_bounds.1])
  have hcosmul := mul_nonneg
    (show 0≤lowC*(GlobalGA.Secondary.diagonal-1/2) by
      dsimp [lowC]; linarith [diagonal_bounds.1])
    (sub_nonneg.mpr (Real.cos_le_one w))
  have hlinear := mul_nonneg
    (show 0≤(9/10)*(lowC*(GlobalGA.Secondary.diagonal+1/2))-charge by
      dsimp [charge,lowC]; linarith [diagonal_bounds.1]) hw.1
  rw [dStress_zero]
  simp only [charge,lowC] at hid hlinear hsinmul hcosmul ⊢
  linarith

/-- Full signed-hexagon support bound.  In particular, opposite signs
are governed by the original sum, rather than independent angle caps. -/
theorem dStress_lower {z d : ℝ}
    (hz : |z|≤frameCap) (hd : |d|≤frameCap) (hs : |z+d|≤frameCap) :
    (1+lowC)*(1-GlobalGA.Secondary.diagonal)≤dStress z d := by
  have hbase : dStress 0 0≤dStress z 0 := by
    rcases le_total 0 z with h | h
    · exact d_positive_zero_comparison ⟨h,(abs_le.mp hz).2⟩
    · exact d_negative_zero_comparison ⟨(abs_le.mp hz).1,h⟩
  rw [← dStress_zero]
  by_cases hd0 : 0≤d
  · exact hbase.trans (d_positive_error_comparison hz ⟨hd0,(abs_le.mp hd).2⟩)
  · have hw : -d∈Icc 0 frameCap :=
      ⟨by linarith [lt_of_not_ge hd0],by linarith [(abs_le.mp hd).1]⟩
    have h := d_negative_error_comparison hz hw
      (by simpa only [sub_neg_eq_add] using hs)
    simpa only [neg_neg] using hbase.trans h

/-- The final D inequality concerns the unchanged original anchor.
Containment, rather than an artificial outer-circle equality, suffices. -/
theorem actual_D_lower {q z d : ℝ} {P : SignedPoint}
    (hsort : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hz : |z|≤frameCap) (hd : |d|≤frameCap) (hsum : |z+d|≤frameCap) :
    (1+lowC)*(1-GlobalGA.Secondary.diagonal)≤lowC*edgeWidth z+edgeWidth d-
      (dF z d*P.a+dG z d*P.y)+charge*(z+d) := by
  have hsupport := actual_clipped_support hsort hy hc hq (d_force_positive hz hd).1.le
  have h := dStress_lower hz hd hsum
  dsimp [dStress] at h
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveATD0
