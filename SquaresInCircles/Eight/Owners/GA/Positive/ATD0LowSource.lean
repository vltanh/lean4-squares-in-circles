module

public import SquaresInCircles.Eight.Owners.GA.ClippedCircle
public import SquaresInCircles.Eight.Owners.GA.Positive.ATD0DVelocity
public import SquaresInCircles.Eight.Owners.GA.Sorted.Support
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveSource

/-!
# Eight squares: the positive-A/TD0 low-angle contradiction

The A-primary error is deleted only from the analytic circle block. All other signed errors and all
seven weak axes are kept (`low_actual_false`). The states of A, T and E need neither a sign nor an
outer radius.
-/

section
/-!
## The fixed positive-A stress at the two original D errors

The two branch expressions agree at the intrinsic
diagonal event.  Their derivatives are identities of the actual force
norm and the original width, and their signs hold on full intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveATD0
open Secondary PositiveAngularEnvelope PairNormCalculus

def dF (z d : ℝ) : ℝ := Real.cos d+lowC*Real.sin z
def dG (z d : ℝ) : ℝ := lowC*Real.cos z+Real.sin d
def dStress (z d : ℝ) : ℝ :=
  lowC*edgeWidth z+edgeWidth d-clippedSupport (dF z d) (dG z d)+charge*(z+d)

theorem d_force_positive {z d : ℝ} (hz : |z|≤frameCap) (hd : |d|≤frameCap) :
    0<dF z d+dG z d ∧ 0<dG z d := by
  have hz' := small_angle hz
  have hd' := small_angle hd
  have hsz := (abs_le.mp hz'.2).1
  have hsd := (abs_le.mp hd'.2).1
  dsimp [frameCap] at hz' hd' hsz hsd
  dsimp [dF,dG,lowC]
  constructor <;> linarith

theorem d_force_norm (z d : ℝ) :
    Real.sqrt ((dF z d)^2+(dG z d)^2)=pairNorm 1 lowC (z+d) := by
  simpa [dF,dG,rotatedPair,add_comm] using rotatedPair_norm 1 lowC z d

theorem dStress_zero : dStress 0 0=(1+lowC)*(1-GlobalGA.Secondary.diagonal) := by
  norm_num [dStress,dF,dG,clippedSupport,diagonalSupport,edgeWidth,pairWidth,lowC]
  ring

def dNegativeDiagonal (z w : ℝ) : ℝ :=
  lowC*edgeWidth z+(1+Real.cos w+Real.sin w)/2-
    GlobalGA.Secondary.diagonal*(Real.cos w-Real.sin w+lowC*(Real.sin z+Real.cos z))+charge*(z-w)

def dNegativeFull (z w : ℝ) : ℝ :=
  lowC*edgeWidth z+(1+Real.cos w+Real.sin w)/2-R*pairNorm 1 lowC (z-w)+
    (Real.cos w-Real.sin w+lowC*(Real.sin z+Real.cos z))/2+charge*(z-w)

def dPositiveDiagonal (z : ℝ) : ℝ :=
  lowC*(1+Real.cos z+Real.sin z)/2+1-
    GlobalGA.Secondary.diagonal*(1+lowC*Real.sin z+lowC*Real.cos z)+charge*z

def dPositiveFull (z : ℝ) : ℝ :=
  lowC*(1+Real.cos z+Real.sin z)/2+1-R*pairNorm 1 lowC z+
    (1+lowC*Real.sin z+lowC*Real.cos z)/2+charge*z

theorem dNegativeDiagonal_eq (z : ℝ) {w : ℝ} (hw : w∈Icc 0 frameCap) :
    dNegativeDiagonal z w=lowC*edgeWidth z+edgeWidth (-w)-
      diagonalSupport (dF z (-w)) (dG z (-w))+charge*(z+(-w)) := by
  rw [edgeWidth_negative_formula hw]
  simp only [dNegativeDiagonal,diagonalSupport,dF,dG,Real.cos_neg,Real.sin_neg]
  ring

theorem dNegativeFull_eq (z : ℝ) {w : ℝ} (hw : w∈Icc 0 frameCap) :
    dNegativeFull z w=lowC*edgeWidth z+edgeWidth (-w)-
      fullSupport (dF z (-w)) (dG z (-w))+charge*(z+(-w)) := by
  rw [edgeWidth_negative_formula hw]
  unfold fullSupport
  rw [d_force_norm]
  simp only [dNegativeFull,dF,dG,Real.cos_neg,Real.sin_neg,sub_eq_add_neg]
  ring

theorem dStress_negative_eq (z : ℝ) {w : ℝ} (hw : w∈Icc 0 frameCap) :
    dStress z (-w)=if dF z (-w)-dG z (-w)≤0 then dNegativeDiagonal z w else dNegativeFull z w := by
  rw [dNegativeDiagonal_eq z hw,dNegativeFull_eq z hw]
  simp only [dStress,clippedSupport,sub_nonpos]
  split_ifs <;> rfl

theorem dPositiveDiagonal_eq {z : ℝ} (hz : z∈Icc 0 frameCap) :
    dPositiveDiagonal z=lowC*edgeWidth z+edgeWidth 0-
      diagonalSupport (dF z 0) (dG z 0)+charge*(z+0) := by
  rw [edgeWidth_positive_formula hz]
  norm_num [dPositiveDiagonal,diagonalSupport,dF,dG,edgeWidth,pairWidth]
  ring

theorem dPositiveFull_eq {z : ℝ} (hz : z∈Icc 0 frameCap) :
    dPositiveFull z=lowC*edgeWidth z+edgeWidth 0-
      fullSupport (dF z 0) (dG z 0)+charge*(z+0) := by
  rw [edgeWidth_positive_formula hz]
  unfold fullSupport
  rw [d_force_norm]
  norm_num [dPositiveFull,dF,dG,edgeWidth,pairWidth]
  ring

theorem dStress_positive_zero_eq {z : ℝ} (hz : z∈Icc 0 frameCap) :
    dStress z 0=if dF z 0-dG z 0≤0 then dPositiveDiagonal z else dPositiveFull z := by
  rw [dPositiveDiagonal_eq hz,dPositiveFull_eq hz]
  simp only [dStress,clippedSupport,sub_nonpos]
  split_ifs <;> rfl

theorem dNegativeDiagonal_hasDerivAt (z w : ℝ) :
    HasDerivAt (dNegativeDiagonal z)
      ((GlobalGA.Secondary.diagonal+1/2)*Real.cos w+(GlobalGA.Secondary.diagonal-1/2)*Real.sin w-charge) w := by
  have h := (((hasDerivAt_const w (lowC*edgeWidth z)).fun_add
      ((((Real.hasDerivAt_cos w).const_add 1).fun_add (Real.hasDerivAt_sin w)).div_const 2)).fun_sub
      ((((Real.hasDerivAt_cos w).fun_sub (Real.hasDerivAt_sin w)).add_const
        (lowC*(Real.sin z+Real.cos z))).const_mul GlobalGA.Secondary.diagonal)).fun_add
      (((hasDerivAt_const w z).fun_sub (hasDerivAt_id w)).const_mul charge)
  convert h using 1
  · funext x
    simp only [dNegativeDiagonal,id]
  · ring

theorem dNegativeFull_hasDerivAt {z w : ℝ} (hs : |z-w|≤frameCap) :
    HasDerivAt (dNegativeFull z) (dVelocity (z-w)-Real.sin w-charge) w := by
  have hn := (pairNorm_hasDerivAt (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC]) hs).comp w
    ((hasDerivAt_const w z).fun_sub (hasDerivAt_id w))
  have hfirst := (((Real.hasDerivAt_cos w).const_add 1).fun_add (Real.hasDerivAt_sin w)).div_const 2
  have hlast := (((Real.hasDerivAt_cos w).fun_sub (Real.hasDerivAt_sin w)).add_const
    (lowC*(Real.sin z+Real.cos z))).div_const 2
  have h := ((((hasDerivAt_const w (lowC*edgeWidth z)).fun_add hfirst).fun_sub
    (hn.const_mul R)).fun_add hlast).fun_add
      (((hasDerivAt_const w z).fun_sub (hasDerivAt_id w)).const_mul charge)
  convert h using 1
  · funext x
    simp only [dNegativeFull,id,Function.comp_apply]
  · simp only [dVelocity]
    ring

theorem dNegativeDiagonal_slope {w : ℝ} (hw : w∈Icc 0 frameCap) :
    0<(GlobalGA.Secondary.diagonal+1/2)*Real.cos w+(GlobalGA.Secondary.diagonal-1/2)*Real.sin w-charge := by
  obtain ⟨hc,_,hs,_,_⟩ := transport_trig hw
  have hm := mul_le_mul (show (1399/1000:ℝ)≤GlobalGA.Secondary.diagonal+1/2 by linarith [diagonal_bounds.1])
    hc.le (by norm_num : (0:ℝ)≤7648/10000) (by linarith [diagonal_bounds.1])
  have hp := mul_nonneg (show 0≤GlobalGA.Secondary.diagonal-1/2 by linarith [diagonal_bounds.1]) hs
  norm_num [charge]
  nlinarith

theorem dPositiveDiagonal_hasDerivAt (z : ℝ) :
    HasDerivAt dPositiveDiagonal
      ((lowC*(1/2-GlobalGA.Secondary.diagonal))*(Real.cos z-Real.sin z)+charge) z := by
  have hfirst := (((((Real.hasDerivAt_cos z).const_add 1).fun_add
    (Real.hasDerivAt_sin z)).const_mul lowC).div_const 2).add_const 1
  have hsecond := (((((Real.hasDerivAt_sin z).const_mul lowC).const_add 1).fun_add
    ((Real.hasDerivAt_cos z).const_mul lowC)).const_mul GlobalGA.Secondary.diagonal)
  have h := (hfirst.fun_sub hsecond).fun_add ((hasDerivAt_id z).const_mul charge)
  convert h using 1
  · funext x
    simp only [dPositiveDiagonal,id]
  · ring

theorem dPositiveFull_hasDerivAt {z : ℝ} (hz : |z|≤frameCap) :
    HasDerivAt dPositiveFull
      (lowC*(Real.cos z-Real.sin z)-dVelocity z+charge) z := by
  have hn := pairNorm_hasDerivAt (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC]) hz
  have ht := ((Real.hasDerivAt_cos z).fun_add (Real.hasDerivAt_sin z)).const_mul lowC
  have h := ((((((ht.const_add lowC).div_const 2).add_const 1).fun_sub (hn.const_mul R)).fun_add
    ((ht.const_add 1).div_const 2))).fun_add ((hasDerivAt_id z).const_mul charge)
  convert h using 1
  · funext x
    simp only [dPositiveFull,id]
    ring
  · simp only [dVelocity]
    ring

theorem dPositiveDiagonal_slope {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<(lowC*(1/2-GlobalGA.Secondary.diagonal))*(Real.cos z-Real.sin z)+charge := by
  obtain ⟨_,hc,hs,_,_⟩ := transport_trig hz
  have hm := mul_le_mul_of_nonneg_left
    (show Real.cos z-Real.sin z≤1 by linarith)
    (show 0≤lowC*(GlobalGA.Secondary.diagonal-1/2) by dsimp [lowC]; linarith [diagonal_bounds.1])
  dsimp [charge,lowC]
  nlinarith [diagonal_bounds.2]

/-- The full-circle derivative is positive on the complete positive
interval. The two comparisons use the sine threshold in (30)--(31). -/
theorem dPositiveFull_slope {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<lowC*(Real.cos z-Real.sin z)-dVelocity z+charge := by
  have hzi : |z|≤frameCap := by rw [abs_of_nonneg hz.1]; exact hz.2
  have hN := pairNorm_pos (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC]) hzi
  have hN2 := dNorm_sq hzi
  obtain ⟨hc,_,hs0,hs,_⟩ := transport_trig hz
  have hR : R^2=9789/2500 := by rw [radius_sq]
  have hR0 : 0≤R := Real.sqrt_nonneg _
  have hvel : dVelocity z=lowC*(R/pairNorm 1 lowC z)*Real.cos z := by
    dsimp [dVelocity,normD1,pairProduct]
    ring
  rw [hvel]
  by_cases hsmall : Real.sin z≤7/20
  · have hratio : R/pairNorm 1 lowC z<1 := by
      rw [div_lt_iff₀ hN]
      refine (pow_lt_pow_iff_left₀ hR0 (by positivity) two_ne_zero).1 ?_
      rw [hR,mul_pow,hN2]
      linarith
    have hp := mul_lt_mul_of_pos_right hratio (by linarith : 0<Real.cos z)
    dsimp [charge,lowC]
    linarith
  · have hlarge : 7/20≤Real.sin z := (lt_of_not_ge hsmall).le
    have hratio : R/pairNorm 1 lowC z<17/20 := by
      rw [div_lt_iff₀ hN]
      refine (pow_lt_pow_iff_left₀ hR0 (by positivity) two_ne_zero).1 ?_
      rw [hR,mul_pow,hN2]
      linarith
    have hp := mul_lt_mul_of_pos_right hratio (by linarith : 0<Real.cos z)
    dsimp [charge,lowC]
    linarith

end SquaresInCircles.Eight.GlobalGA.PositiveATD0
end
end
end

section
/-!
## The positive-A fixed stress minimizes the actual D term at alignment

Both
original angles remain in the norm and in their common variation
constraint.  The concluding inequality is for the original contained
sorted point, at any source radius below the fixed ceiling.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveATD0
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

end SquaresInCircles.Eight.GlobalGA.PositiveATD0
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PositiveATD0
namespace Source
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks SignedStress
open TwoPositive.Source (aError aWork aReserve a_reserve_nonneg)

def owners (hg : Fin 4) (atG : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,2,0,2,0]

def weights (k l c : ℝ) : Vertex→ℝ := ![k,l,l,c,c,1,1]

def blocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ) : Fin 4→Block :=
  ![⟨k,l,if hg=0 then delta C.theta H else 0,if atG then 0 else delta C.theta G⟩,
    ⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨l,c,if atG then delta C.theta A else 0,delta C.theta B⟩,
    ⟨c,1,delta C.theta T,delta C.theta D⟩]

def actualStress (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ) : ℝ :=
  demand C (weights k l c)-
    ∑i,work (force C (owners hg atG) (weights k l c) i) (C.point i)

def dIncrement (z d : ℝ) (P : SignedPoint) : ℝ :=
  lowC*edgeWidth z+edgeWidth d-(dF z d*P.a+dG z d*P.y)+
    charge*(z+d)-(1+lowC)*(1-GlobalGA.Secondary.diagonal)

def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) : Fin 4→ℝ :=
  ![pairIncrement lowK lowL (blocks C hg atG lowK lowL lowC 0).u
      (blocks C hg atG lowK lowL lowC 0).v (C.point G).reflect,
    pairIncrement lowK 1 (blocks C hg atG lowK lowL lowC 1).u
      (blocks C hg atG lowK lowL lowC 1).v (C.point H),
    pairIncrement lowL lowC (blocks C hg atG lowK lowL lowC 2).u
      (blocks C hg atG lowK lowL lowC 2).v (C.point B).reflect,
    dIncrement (delta C.theta T) (delta C.theta D) (C.point D).reflect]

theorem weights_nonneg {k l c : ℝ} (hk : 0≤k) (hl : 0≤l) (hc : 0≤c)
    (i : Vertex) : 0≤weights k l c i := by
  fin_cases i <;> simp [weights,hk,hl,hc]

theorem stress_nonpos {C : SignedCycle} {hg : Fin 4} (atG : Bool) {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0≤c)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    actualStress C hg atG k l c≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg atG i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonneg hk hl hc) hf)

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG : Bool)
    (hhg : hg=0 ∨ hg=2) :
    actualStress C hg atG lowK lowL lowC=
      lowBaseline+charge*aError C atG+lowL*TwoPositive.ASupport.charge (aError C atG)+
        (∑i,actualBlocks C hg atG i)+aReserve C atG lowL := by
  cases atG <;> rcases hhg with rfl | rfl <;>
    simp [actualStress,demand,force,source,target,work,add,scale,
      previous,owners,weights,blocks,actualBlocks,pairIncrement,dIncrement,
      pairF,pairG,dF,dG,lowBaseline,aReserve,aWork,aError,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,
      SignedPoint.reflect,edgeWidth,pairWidth,lowK,lowL,lowC,charge] <;> ring

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG k l c i).u+f (blocks C hg atG k l c i).v))=
      (∑j,f (delta C.theta j))-f (aError C atG) := by
  cases atG <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

/-- The primary error removes exactly its positive variation; every other error of the cycle stays
as it is, and none is concentrated. -/
theorem original_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG) :
    aError C atG∈Icc 0 frameCap ∧
      (∑i,(blocks C hg atG k l c i).P)≤frameCap-aError C atG ∧
      (∑i,(blocks C hg atG k l c i).N)=aError C atG+∑i,(blocks C hg atG k l c i).P := by
  have hp := sum_parts C hg atG k l c positivePart positivePart_zero
  have hn := sum_parts C hg atG k l c negativePart negativePart_zero
  have hpa : positivePart (aError C atG)=aError C atG := max_eq_left ha
  have hna : negativePart (aError C atG)=0 := max_eq_right (by linarith)
  have hp' : (∑i,(blocks C hg atG k l c i).P)=positiveVariation C.theta-aError C atG := by
    change (∑i,(positivePart (blocks C hg atG k l c i).u+
      positivePart (blocks C hg atG k l c i).v))=_
    simpa only [hpa,positiveVariation] using hp
  have hn' : (∑i,(blocks C hg atG k l c i).N)=negativeVariation C.theta := by
    change (∑i,(negativePart (blocks C hg atG k l c i).u+
      negativePart (blocks C hg atG k l c i).v))=_
    simpa only [hna,negativeVariation,sub_zero] using hn
  have hp0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg atG k l c i).P_nonneg)
  have heq := variations_equal C.theta
  exact ⟨⟨ha,by linarith⟩,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG) (i : Fin 4) :
    (blocks C hg atG k l c i).P≤frameCap ∧ (blocks C hg atG k l c i).N≤frameCap := by
  have hb := original_budgets hg atG k l c hvar ha
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c j).N_nonneg) (Finset.mem_univ i)
  constructor <;> linarith [hb.1.1,hb.2.1,hb.2.2]

theorem actual_blocks_nonneg {q : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG)
    (i : Fin 4) : 0≤actualBlocks C hg atG i := by
  have hb := block_budgets hg atG lowK lowL lowC hvar ha
  fin_cases i
  · have hh := actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
      (a:=(blocks C hg atG lowK lowL lowC 0).u)
      (b:=(blocks C hg atG lowK lowL lowC 0).v)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq (hb 0).1 (hb 0).2
    simpa [actualBlocks,coefficientP,coefficientQ] using hh
  · have hh := actual_fixed_pair_nonneg 1 (P:=C.point H)
      (a:=(blocks C hg atG lowK lowL lowC 1).u)
      (b:=(blocks C hg atG lowK lowL lowC 1).v)
      hHy (hc H) hq (hb 1).1 (hb 1).2
    simpa [actualBlocks,coefficientP,coefficientQ] using hh
  · have hh := actual_fixed_pair_nonneg 2 (P:=(C.point B).reflect)
      (a:=(blocks C hg atG lowK lowL lowC 2).u)
      (b:=(blocks C hg atG lowK lowL lowC 2).v)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B) hq (hb 2).1 (hb 2).2
    simpa [actualBlocks,coefficientP,coefficientQ] using hh
  · have he := pair_error_bounds (hb 3).1 (hb 3).2
    have hh := actual_D_lower (P:=(C.point D).reflect)
      (z:=delta C.theta T) (d:=delta C.theta D)
      (by simpa using hs D)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hq he.1 he.2.1 he.2.2
    simpa [actualBlocks,dIncrement,sub_nonneg] using hh

/-- The low-angle exclusion on the cycle. The only hypotheses are the weak owners and the signed
variation of the cycle. -/
theorem low_actual_false {q : ℝ} {C : SignedCycle} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aError C atG∈Icc 0 (1/6:ℝ))
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0 ∨ hg=2) ∧ C.Feasible H hg := by
    rcases hHG with hh | hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hu := stress_nonpos (k:=lowK) (l:=lowL) (c:=lowC) atG (by norm_num [lowK])
    (by norm_num [lowL]) (by norm_num [lowC]) hHG hGA hAB hBT hTD hDE hEH
  have hb := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => actual_blocks_nonneg atG hs hc hq hHy hGy hBy hDy hvar ha.1 i (hg:=hg))
  have hA := a_reserve_nonneg (l:=lowL) atG (hs A) (hc A) hq (by norm_num [lowL])
    ⟨ha.1,ha.2.trans (by norm_num [frameCap])⟩
  have hp := low_scalar_positive ha
  have he := decomposition C atG hhg
  simp only [lowL,charge] at hp he
  linarith

end Source
open Candidate

end SquaresInCircles.Eight.GlobalGA.PositiveATD0
end
end
end
