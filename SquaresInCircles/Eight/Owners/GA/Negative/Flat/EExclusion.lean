module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.GA.ClippedCircle
public import SquaresInCircles.Eight.Owners.GA.Negative.Flat.EDVelocity
public import SquaresInCircles.Eight.Owners.GA.Negative.Primary.Reserve
public import SquaresInCircles.Eight.Owners.GA.ChargedPairs
public import SquaresInCircles.Eight.Owners.GA.Sorted.Support
public import SquaresInCircles.Eight.Owners.SplitConcavityTools

/-!
# Eight squares: simultaneous nonpositive A, T, and flat-core-E primary owners

The two E gains are added before the decreasing ratio comparison is applied (`gains_reserve`).
Every multiplier is positive, whereas the necessary inequalities make the collected stress
nonpositive (`actual_false`). The statement is about signed cycles with the necessary conditions,
so it applies after the moves of the cycle; no marker theorem is applied after a move.
-/

section
/-!
## The original D block with angular charge 473/500

The whole negative-angle reductions use the unchanged velocity argument.
The positive interior branch uses the stated new root ratio 211/250 and
the exact whole-interval sine and cosine reserves.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeFlatE
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
    have hratio : R/pairNorm 1 lowC z<211/250 := by
      rw [div_lt_iff₀ hN]
      refine (pow_lt_pow_iff_left₀ hR0 (by positivity) two_ne_zero).1 ?_
      rw [hR,mul_pow,hN2]
      linarith
    have hp := mul_lt_mul_of_pos_right hratio (by linarith : 0<Real.cos z)
    dsimp [charge,lowC]
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeFlatE
end
end
end

section
/-!
## The lower charged D block minimizes at alignment

Both signed errors and their common hexagon are kept. The support branches meet at their diagonal
event. The lower charge still leaves the required positive derivative on every branch
(`dStress_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeFlatE
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

/-- The support bound on the whole signed hexagon. Opposite signs are governed by the sum
`z + d`, not by separate angle caps. -/
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

/-- The D inequality at the anchor D of the cycle itself; containment in the disk suffices, with no
outer-circle equality. -/
theorem actual_D_lower {q z d : ℝ} {P : SignedPoint}
    (hsort : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hz : |z|≤frameCap) (hd : |d|≤frameCap) (hsum : |z+d|≤frameCap) :
    (1+lowC)*(1-GlobalGA.Secondary.diagonal)≤lowC*edgeWidth z+edgeWidth d-
      (dF z d*P.a+dG z d*P.y)+charge*(z+d) := by
  have hsupport := actual_clipped_support hsort hy hc hq (d_force_positive hz hd).1.le
  have h := dStress_lower hz hd hsum
  dsimp [dStress] at h
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeFlatE
end
end
end

section
/-!
## The baseline pays the whole E angle

The reserve multiplied by the cosine, `F`, has a convex first derivative (`Fd_convex`). Its
derivative at `frameCap` is negative (`Fd_cap_negative`), so its minimum is at an intrinsic
endpoint. Both endpoint values are exact fractions (`F_zero`, `F_cap_positive`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeFlatE
open Arithmetic

def F (s : ℝ) : ℝ := (baseline+a-charge*s)*Real.cos s+K*Real.sin s-a
def Fd (s : ℝ) : ℝ := (K-charge)*Real.cos s+(charge*s-baseline-a)*Real.sin s
def Fdd (s : ℝ) : ℝ := (2*charge-K)*Real.sin s+(charge*s-baseline-a)*Real.cos s
def Fddd (s : ℝ) : ℝ := (3*charge-K)*Real.cos s+(baseline+a-charge*s)*Real.sin s

theorem F_hasDerivAt (s : ℝ) : HasDerivAt F (Fd s) s := by
  have hh := (((((hasDerivAt_id s).const_mul charge).const_sub (baseline+a)).fun_mul
    (Real.hasDerivAt_cos s)).fun_add ((Real.hasDerivAt_sin s).const_mul K)).sub_const a
  refine (show HasDerivAt F _ s from hh).congr_deriv ?_
  simp only [Fd,id]
  ring

theorem Fd_hasDerivAt (s : ℝ) : HasDerivAt Fd (Fdd s) s := by
  have hh := ((Real.hasDerivAt_cos s).const_mul (K-charge)).fun_add
    (((((hasDerivAt_id s).const_mul charge).sub_const baseline).sub_const a).fun_mul
      (Real.hasDerivAt_sin s))
  refine (show HasDerivAt Fd _ s from hh).congr_deriv ?_
  simp only [Fdd,id]
  ring

theorem Fdd_hasDerivAt (s : ℝ) : HasDerivAt Fdd (Fddd s) s := by
  have hh := ((Real.hasDerivAt_sin s).const_mul (2*charge-K)).fun_add
    (((((hasDerivAt_id s).const_mul charge).sub_const baseline).sub_const a).fun_mul
      (Real.hasDerivAt_cos s))
  refine (show HasDerivAt Fdd _ s from hh).congr_deriv ?_
  simp only [Fddd,id]
  ring

theorem Fddd_positive {s : ℝ} (hs : s∈Icc 0 frameCap) : 0<Fddd s := by
  have hc := cosine_pos hs
  have ht := transport_trig hs
  have hfirst : 0<(3*charge-K)*Real.cos s := mul_pos (by norm_num [charge,K]) hc
  have hcoeff : 0≤baseline+a-charge*s := by
    dsimp [baseline,a,charge,frameCap] at *
    linarith [hs.2]
  have hsecond := mul_nonneg hcoeff ht.2.2.1
  dsimp [Fddd]
  linarith

theorem Fd_convex : ConvexOn ℝ (Icc 0 frameCap) Fd := by
  have hh : ConcaveOn ℝ (Icc 0 frameCap) (fun s => -Fd s) :=
    concave_of_deriv2 (fun s _ => (Fd_hasDerivAt s).neg)
      (fun s _ => (Fdd_hasDerivAt s).neg)
      (fun s hs => by linarith [Fddd_positive hs])
  convert hh.neg using 1
  funext s
  simp

theorem Fd_cap_negative : Fd frameCap<0 := by
  have ht := cap_trig_bounds
  have hp := mul_le_mul_of_nonneg_left ht.2.2.2.2
    (by norm_num [K,charge] : 0≤K-charge)
  have hn := mul_le_mul_of_nonpos_left ht.2.1
    (by norm_num [charge,baseline,a,frameCap] : charge*frameCap-baseline-a≤0)
  have he : (K-charge)*capC8+(charge*frameCap-baseline-a)*capS7=
      -(34023000872689/432000000000000:ℝ) := by
    norm_num [K,charge,baseline,a,capC8,capS7,cos8,sin7,frameCap]
  dsimp only [Fd]
  simp only [K,charge,baseline,a,frameCap] at hp hn he ⊢
  linarith

theorem F_zero : F 0=baseline := by norm_num [F]

theorem F_cap_positive : (1/1000:ℝ)<F frameCap := by
  have ht := cap_trig_bounds
  have hc := mul_le_mul_of_nonneg_left ht.2.2.2.1
    (by norm_num [baseline,a,charge,frameCap] : 0≤baseline+a-charge*frameCap)
  have hs := mul_le_mul_of_nonneg_left ht.2.1 (by norm_num [K] : 0≤K)
  have he : (baseline+a-charge*frameCap)*capC6+K*capS7-a=
      (24007209959/21600000000000:ℝ) := by
    norm_num [baseline,a,charge,K,capC6,capS7,sin7,frameCap]
  dsimp [F]
  linarith

theorem F_positive {s : ℝ} (hs : s∈Icc 0 frameCap) : 0<F s := by
  have hh := SplitConcavityTools.minimum_of_convex_derivative
    (fun s _ => F_hasDerivAt s) Fd_convex Fd_cap_negative.le hs
  have hmin : 0< min (F 0) (F frameCap) := lt_min
    (by rw [F_zero]; norm_num [baseline]) (by linarith [F_cap_positive])
  exact hmin.trans_le hh

theorem baseline_gain_positive {s : ℝ} (hs : s∈Icc 0 frameCap) :
    0<baseline+g s-charge*s := by
  have hc := cosine_pos hs
  have he : Real.cos s*(baseline+g s-charge*s)=F s := by
    dsimp [g,F]
    field_simp [hc.ne']
    ring
  have hh := F_positive hs
  rw [← he] at hh
  exact (mul_pos_iff_of_pos_left hc).1 hh

end SquaresInCircles.Eight.GlobalGA.NegativeFlatE
end
end
end

section
/-!
## The separate A and T gains at the lower E charge

The A quadratic has its exact positive completed
square reserve; the TD gain uses the complete concave sine-cosine arc.
The E gains keep their own secant and exact flat-core primary 7/12.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeFlatE
open Secondary Arithmetic

def commonJ (s : ℝ) : ℝ := ((847/800)*Real.sin s-a*(1-Real.cos s))/Real.cos s
def commonJd (s : ℝ) : ℝ := ((847/800)-a*Real.sin s)/Real.cos s^2
def primaryGain (d A B : ℝ) : ℝ :=
  lowL/Real.cos d*(edgeWidth d-B-A*Real.sin d)-lowL*(1-B)
def tdGain (d : ℝ) (T : SignedPoint) : ℝ :=
  lowC*(edgeWidth d-1-T.a*Real.sin d-T.y*(Real.cos d-1))
def eGain (d A : ℝ) : ℝ :=
  (edgeWidth d-A-(7/12)*Real.sin d)/Real.cos d-(1-A)

theorem commonJ_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt commonJ (commonJd s) s := by
  have hc := (cosine_pos hs).ne'
  have hh := (((Real.hasDerivAt_sin s).const_mul (847/800:ℝ)).sub
    (((Real.hasDerivAt_cos s).const_sub 1).const_mul a)).div (Real.hasDerivAt_cos s) hc
  convert hh using 1
  · rfl
  · dsimp [commonJd]
    field_simp [hc]
    nlinarith only [congrArg (fun x : ℝ => (847/800)*x) (Real.sin_sq_add_cos_sq s)]

theorem commonJ_quadratic (x : ℝ) :
    (79/100)*x^2-(183/200)*x+847/800-79/100=
      (79/100)*(x-183/316)^2+481/126400 := by ring

theorem commonJd_lower {s : ℝ} (hs : s∈Icc 0 frameCap) : (79/100:ℝ)<commonJd s := by
  have hc := cosine_pos hs
  have hunit := Real.sin_sq_add_cos_sq s
  have hq := commonJ_quadratic (Real.sin s)
  dsimp [commonJd,a]
  apply (lt_div_iff₀ (sq_pos_of_pos hc)).2
  nlinarith [sq_nonneg (Real.sin s-183/316)]

theorem commonJ_lower {s : ℝ} (hs : s∈Icc 0 frameCap) : (79/100)*s≤commonJ s := by
  have hm : MonotoneOn (fun z => commonJ z-(79/100)*z) (Icc 0 frameCap) :=
    monoOn_of_hasDeriv_nonneg
      (fun z hz => ((commonJ_hasDerivAt hz).sub
        ((hasDerivAt_id z).const_mul (79/100:ℝ))).continuousAt.continuousWithinAt)
      (fun z hz => (commonJ_hasDerivAt (Ioo_subset_Icc_self hz)).sub
        ((hasDerivAt_id z).const_mul (79/100:ℝ)))
      (fun z hz => by
        simp only [mul_one]
        linarith [commonJd_lower (Ioo_subset_Icc_self hz)])
  have hh := hm (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hs hs.1
  have h0 : commonJ 0=0 := by norm_num [commonJ]
  simp only [h0,mul_zero,sub_zero] at hh
  linarith

theorem primaryGain_lower {s A B : ℝ} (hs : s∈Icc 0 frameCap)
    (hA : (447/800:ℝ)≤A) (hB : B≤283/200) :
    (charge+247/5000)*s≤primaryGain (-s) A B := by
  have hc := cosine_pos hs
  have ht := transport_trig hs
  have hAprod := mul_nonneg (sub_nonneg.mpr hA) ht.2.2.1
  have hBprod := mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr (Real.cos_le_one s))
  have he : primaryGain (-s) A B*Real.cos s=
      lowL*((A+1/2)*Real.sin s+(1/2-B)*(1-Real.cos s)) := by
    rw [primaryGain,edgeWidth_negative_formula hs]
    simp only [Real.sin_neg,Real.cos_neg]
    field_simp [hc.ne']
    ring
  have hJ : lowL*commonJ s≤primaryGain (-s) A B := by
    refine le_of_mul_le_mul_right ?_ hc
    have hJc : lowL*commonJ s*Real.cos s=lowL*((847/800)*Real.sin s-a*(1-Real.cos s)) := by
      rw [commonJ]
      field_simp [hc.ne']
    rw [he,hJc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num [lowL])
    simp only [a]
    linarith
  have hl := mul_le_mul_of_nonneg_left (commonJ_lower hs) (by norm_num [lowL] : 0≤lowL)
  simp only [charge,lowL] at hl hJ ⊢
  linarith

theorem td_arc_charge {s : ℝ} (hs : s∈Icc 0 frameCap) :
    (charge+37/350)*s≤lowC*(Real.sin s+Real.cos s-1) := by
  let f : ℝ→ℝ := fun z => lowC*(Real.sin z+Real.cos z-1)-(charge+37/350)*z
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) f := by
    apply concave_of_deriv2
      (f':=fun z => lowC*(Real.cos z-Real.sin z)-(charge+37/350))
      (f'':=fun z => -lowC*(Real.sin z+Real.cos z))
    · intro z _
      have hh := ((((Real.hasDerivAt_sin z).fun_add (Real.hasDerivAt_cos z)).sub_const 1
        ).const_mul lowC).fun_sub ((hasDerivAt_id z).const_mul (charge+37/350))
      refine (show HasDerivAt f _ z from hh).congr_deriv ?_
      ring
    · intro z _
      exact ((((Real.hasDerivAt_cos z).fun_sub (Real.hasDerivAt_sin z)).const_mul lowC
        ).sub_const (charge+37/350)).congr_deriv (by ring)
    · intro z hz
      have ht := transport_trig hz
      dsimp [lowC]
      linarith [ht.1,ht.2.2.1]
  have hright : 0≤f frameCap := by
    have ht := GlobalGA.Secondary.cap_trig
    simp only [Arithmetic.sin7,frameCap] at ht
    simp only [f,lowC,charge,frameCap]
    norm_num at ht ⊢
    linarith [ht.1,ht.2.2.1]
  have hleft : f 0=0 := by norm_num [f]
  have hmin := hconc.min_le_of_mem_Icc (by norm_num [frameCap]) (by norm_num [frameCap]) hs
  have hh : 0 ≤ min (f 0) (f frameCap) := le_min (by rw [hleft]) hright
  have := hh.trans hmin
  simp only [f] at this
  linarith

theorem tdGain_lower {s : ℝ} {T : SignedPoint} (hs : s∈Icc 0 frameCap)
    (hT : T.Sorted) (hcore : T.AvoidsCore) :
    (charge+37/350)*s≤tdGain (-s) T := by
  have ht := transport_trig hs
  have hphi : 0≤Real.sin s+Real.cos s-1 := by
    have hh := one_le_abs_cos_add_abs_sin s
    rw [abs_of_pos (cosine_pos hs),abs_of_nonneg ht.2.2.1] at hh
    linarith
  have hprimary := SignedPoint.primary_gt_half hT hcore
  have hY := (abs_le.mp hT.2).1
  have hYprod := mul_le_mul_of_nonpos_right hY
    (show Real.cos s-1≤0 by linarith [ht.2.1])
  have hAprod := mul_nonneg (show 0≤T.a-1/2 by linarith) hphi
  have hh := td_arc_charge hs
  rw [tdGain,edgeWidth_negative_formula hs]
  simp only [Real.sin_neg,Real.cos_neg]
  dsimp [lowC] at *
  nlinarith

theorem eGain_lower {s A : ℝ} (hs : s∈Icc 0 frameCap) (hA : A≤283/200) :
    g s≤eGain (-s) A := by
  have hc := cosine_pos hs
  have hprod := mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr (Real.cos_le_one s))
  refine le_of_mul_le_mul_right ?_ hc
  have h1 : g s*Real.cos s=K*Real.sin s-a*(1-Real.cos s) := by
    rw [g]
    field_simp [hc.ne']
  have h2 : eGain (-s) A*Real.cos s=K*Real.sin s+(1/2-A)*(1-Real.cos s) := by
    rw [eGain,edgeWidth_negative_formula hs]
    simp only [Real.cos_neg,Real.sin_neg]
    field_simp [hc.ne']
    ring
  rw [h1,h2]
  simp only [a]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeFlatE
end
end
end

section
/-!
## Exact simultaneous negative A, T, and flat-core-E force collection

The five independent flags retain GA3, AB2, TD2, DE3, and EH1. Only
the comparison expression erases their arguments. Each E primary has
its own actual secant multiplier, and their signed E terms cancel.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeFlatE
open Candidate Secondary
open NegativePrimary (erase erase_positive_le erase_negative_le erase_abs_bound erased_pair_budgets)

def owners (hg ga ab td de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    2,if td then 2 else 0,if de then 3 else 2,if eh then 1 else 0]

def weights (ga ab de eh : Bool) (C : SignedCycle) : Vertex→ℝ :=
  ![lowK,if ga then lowL/Real.cos (delta C.theta G) else lowL,
    if ab then lowL/Real.cos (delta C.theta A) else lowL,lowC,lowC,
    if de then 1/Real.cos (delta C.theta D) else 1,
    if eh then 1/Real.cos (delta C.theta E) else 1]

def stress (hg ga ab td de eh : Bool) (C : SignedCycle) : ℝ :=
  ∑i,weights ga ab de eh C i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab td de eh i))

def dIncrement (z d : ℝ) (P : SignedPoint) : ℝ :=
  lowC*edgeWidth z+edgeWidth d-(dF z d*P.a+dG z d*P.y)+charge*(z+d)-
    (1+lowC)*(1-GlobalGA.Secondary.diagonal)

def reference (hg ga ab td de eh : Bool) (C : SignedCycle) : ℝ :=
  lowBaseline+
    pairIncrement lowK lowL (erase hg (delta C.theta H))
      (erase ga (delta C.theta G)) (C.point G).reflect+
    pairIncrement lowK 1 (erase (!hg) (delta C.theta H))
      (erase eh (delta C.theta E)) (C.point H)+
    pairIncrement lowL lowC (erase ab (delta C.theta A))
      (delta C.theta B) (C.point B).reflect+
    dIncrement (erase td (delta C.theta T)) (erase de (delta C.theta D)) (C.point D).reflect

def gains (ga ab td de eh : Bool) (C : SignedCycle) : ℝ :=
  (if ga then primaryGain (delta C.theta G) (C.point A).a (C.point G).a+
    charge*delta C.theta G else 0)+
  (if ab then primaryGain (delta C.theta A) (C.point A).a (-(C.point B).y)+
    charge*delta C.theta A else 0)+
  (if td then tdGain (delta C.theta T) (C.point T)+charge*delta C.theta T else 0)+
  (if de then eGain (delta C.theta D) (C.point D).a+charge*delta C.theta D else 0)+
  (if eh then eGain (delta C.theta E) (C.point H).a+charge*delta C.theta E else 0)

theorem weights_nonneg (ga ab de eh : Bool) (C : SignedCycle)
    (hsmall : ∀i,|delta C.theta i|≤frameCap) : ∀i,0≤weights ga ab de eh C i := by
  have hG := NegativePrimary.cos_pos (hsmall G)
  have hA := NegativePrimary.cos_pos (hsmall A)
  have hD := NegativePrimary.cos_pos (hsmall D)
  have hE := NegativePrimary.cos_pos (hsmall E)
  intro i
  cases ga <;> cases ab <;> cases de <;> cases eh <;> fin_cases i <;>
    simp [weights,lowK,lowL,lowC] <;> positivity

theorem stress_nonpos {hg ga ab td de eh : Bool} {C : SignedCycle}
    (hsmall : ∀i,|delta C.theta i|≤frameCap)
    (hf : ∀i,C.Feasible i (owners hg ga ab td de eh i)) :
    stress hg ga ab td de eh C≤0 := by
  apply Finset.sum_nonpos
  intro i _
  have hi := hf i
  change 0≤C.edge i (owners hg ga ab td de eh i)-edgeWidth (delta C.theta i) at hi
  exact mul_nonpos_of_nonneg_of_nonpos (weights_nonneg ga ab de eh C hsmall i) (by linarith)

/-! Edge-by-edge form of the collection.  Each original separator term
equals its own slots of the comparison expression, its own gain, and a
flag-free remainder; the remainders cancel around the cycle. -/

private def r43_aslot (p x : ℝ) (P : SignedPoint) : ℝ :=
  p*(edgeWidth x-1)-p*Real.sin x*P.a-p*Real.cos x*P.y+charge*x

private def r43_bslot (q x : ℝ) (P : SignedPoint) : ℝ :=
  q*(edgeWidth x-1)-q*Real.cos x*P.a-q*Real.sin x*P.y+charge*x

private def r43_zslot (x : ℝ) (P : SignedPoint) : ℝ :=
  lowC*edgeWidth x-lowC*Real.sin x*P.a-lowC*Real.cos x*P.y+charge*x

private def r43_dslot (x : ℝ) (P : SignedPoint) : ℝ :=
  edgeWidth x-Real.cos x*P.a-Real.sin x*P.y+charge*x

private theorem r43_pair_split (p q a b : ℝ) (P : SignedPoint) :
    pairIncrement p q a b P=r43_aslot p a P+r43_bslot q b P+fullSupport q p := by
  simp only [pairIncrement,pairF,pairG,r43_aslot,r43_bslot]
  ring

private theorem r43_d_split (z d : ℝ) (P : SignedPoint) :
    dIncrement z d P=r43_zslot z P+r43_dslot d P-(1+lowC)*(1-GlobalGA.Secondary.diagonal) := by
  simp only [dIncrement,dF,dG,r43_zslot,r43_dslot]
  ring

private theorem r43_delta_sum (C : SignedCycle) :
    delta C.theta 0+delta C.theta 1+delta C.theta 2+delta C.theta 3+
      delta C.theta 4+delta C.theta 5+delta C.theta 6=0 := by
  simp only [delta,next]
  norm_num

private theorem r43_edge_H (hg ga ab td de eh : Bool) (C : SignedCycle) :
    weights ga ab de eh C 0*(edgeWidth (delta C.theta 0)-C.edge 0 (owners hg ga ab td de eh 0))=
      r43_aslot lowK (erase hg (delta C.theta 0)) (C.point 1).reflect+
      r43_aslot lowK (erase (!hg) (delta C.theta 0)) (C.point 0)+lowK-charge*delta C.theta 0 := by
  cases hg <;>
    simp [weights,owners,SignedCycle.edge,word,next,zeroProjection,r43_aslot,
      SignedPoint.reflect] <;> ring

private theorem r43_edge_G (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hG : Real.cos (delta C.theta 1)≠0) :
    weights ga ab de eh C 1*(edgeWidth (delta C.theta 1)-C.edge 1 (owners hg ga ab td de eh 1))=
      r43_bslot lowL (erase ga (delta C.theta 1)) (C.point 1).reflect+
      (if ga then primaryGain (delta C.theta 1) (C.point 2).a (C.point 1).a+
        charge*delta C.theta 1 else 0)+lowL+lowL*(C.point 2).y-charge*delta C.theta 1 := by
  cases ga
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_bslot,
      SignedPoint.reflect]
    ring
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_bslot,
      SignedPoint.reflect,primaryGain,G,A]
    field_simp
    ring

private theorem r43_edge_A (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hA : Real.cos (delta C.theta 2)≠0) :
    weights ga ab de eh C 2*(edgeWidth (delta C.theta 2)-C.edge 2 (owners hg ga ab td de eh 2))=
      r43_aslot lowL (erase ab (delta C.theta 2)) (C.point 3).reflect+
      (if ab then primaryGain (delta C.theta 2) (C.point 2).a (-(C.point 3).y)+
        charge*delta C.theta 2 else 0)+lowL-lowL*(C.point 2).y-charge*delta C.theta 2 := by
  cases ab
  · simp [weights,owners,SignedCycle.edge,word,next,zeroProjection,r43_aslot,
      SignedPoint.reflect]
    ring
  · simp [weights,owners,SignedCycle.edge,word,next,zeroProjection,r43_aslot,
      SignedPoint.reflect,primaryGain,G,A]
    field_simp
    ring

private theorem r43_edge_B (hg ga ab td de eh : Bool) (C : SignedCycle) :
    weights ga ab de eh C 3*(edgeWidth (delta C.theta 3)-C.edge 3 (owners hg ga ab td de eh 3))=
      r43_bslot lowC (delta C.theta 3) (C.point 3).reflect+lowC+lowC*(C.point 4).y-
        charge*delta C.theta 3 := by
  simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_bslot,
    SignedPoint.reflect]
  ring

private theorem r43_edge_T (hg ga ab td de eh : Bool) (C : SignedCycle) :
    weights ga ab de eh C 4*(edgeWidth (delta C.theta 4)-C.edge 4 (owners hg ga ab td de eh 4))=
      r43_zslot (erase td (delta C.theta 4)) (C.point 5).reflect+
      (if td then tdGain (delta C.theta 4) (C.point 4)+charge*delta C.theta 4 else 0)-
        lowC*(C.point 4).y-charge*delta C.theta 4 := by
  cases td <;>
    simp [weights,owners,SignedCycle.edge,word,next,zeroProjection,r43_zslot,
      SignedPoint.reflect,tdGain] <;> ring

private theorem r43_edge_D (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hflat : (C.point 6).a=7/12) (hD : Real.cos (delta C.theta 5)≠0) :
    weights ga ab de eh C 5*(edgeWidth (delta C.theta 5)-C.edge 5 (owners hg ga ab td de eh 5))=
      r43_dslot (erase de (delta C.theta 5)) (C.point 5).reflect+
      (if de then eGain (delta C.theta 5) (C.point 5).a+charge*delta C.theta 5 else 0)+
        (C.point 6).y-charge*delta C.theta 5 := by
  cases de
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_dslot,
      SignedPoint.reflect]
    ring
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_dslot,
      SignedPoint.reflect,eGain,hflat,D]
    field_simp
    ring

private theorem r43_edge_E (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hflat : (C.point 6).a=7/12) (hE : Real.cos (delta C.theta 6)≠0) :
    weights ga ab de eh C 6*(edgeWidth (delta C.theta 6)-C.edge 6 (owners hg ga ab td de eh 6))=
      r43_bslot 1 (erase eh (delta C.theta 6)) (C.point 0)+
      (if eh then eGain (delta C.theta 6) (C.point 0).a+charge*delta C.theta 6 else 0)+
        1-(C.point 6).y-charge*delta C.theta 6 := by
  cases eh
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_bslot]
    ring
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_bslot,eGain,hflat,E]
    field_simp
    ring

theorem decomposition (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hflat : (C.point E).a=7/12)
    (hG : Real.cos (delta C.theta G)≠0) (hA : Real.cos (delta C.theta A)≠0)
    (hD : Real.cos (delta C.theta D)≠0) (hE : Real.cos (delta C.theta E)≠0) :
    stress hg ga ab td de eh C=reference hg ga ab td de eh C+gains ga ab td de eh C := by
  simp only [G,A,D,E] at hflat hG hA hD hE
  have hH' := r43_edge_H hg ga ab td de eh C
  have hG' := r43_edge_G hg ga ab td de eh C hG
  have hA' := r43_edge_A hg ga ab td de eh C hA
  have hB' := r43_edge_B hg ga ab td de eh C
  have hT' := r43_edge_T hg ga ab td de eh C
  have hD' := r43_edge_D hg ga ab td de eh C hflat hD
  have hE' := r43_edge_E hg ga ab td de eh C hflat hE
  have hs := r43_delta_sum C
  simp only [stress,Fin.sum_univ_seven,reference,gains,r43_pair_split,r43_d_split,lowBaseline,
    H,G,A,B,T,D,E]
  linear_combination hH'+hG'+hA'+hB'+hT'+hD'+hE'-charge*hs

theorem reference_reserve {q : ℝ} {C : SignedCycle} (hg ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) : baseline<reference hg ga ab td de eh C := by
  have hn : negativeVariation C.theta≤frameCap := by rwa [←variations_equal]
  have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) hg ga
  have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) (!hg) eh
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab false
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) td de
  simp only [NegativePrimary.erase_false] at hbb
  have hG := actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hc G) hq hgb.1 hgb.2
  have hH := actual_fixed_pair_nonneg 1 hHy (hc H) hq hhb.1 hhb.2
  have hB := actual_fixed_pair_nonneg 2 (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hc B) hq hbb.1 hbb.2
  have hde := pair_error_bounds hdb.1 hdb.2
  have hD := actual_D_lower (P:=(C.point D).reflect)
    (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  simp only [coefficientP,coefficientQ,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] at hG hH hB
  have hL := low_baseline_reserve
  dsimp only [reference,dIncrement,baseline]
  have hsum := add_nonneg (add_nonneg (add_nonneg hG hH) hB) (sub_nonneg.mpr hD)
  exact lt_of_lt_of_le hL (le_of_le_of_eq (le_add_of_nonneg_right hsum) (by ring))

end SquaresInCircles.Eight.GlobalGA.NegativeFlatE
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeFlatE
open Candidate Secondary

def magnitude (primary : Bool) (d : ℝ) : ℝ := if primary then -d else 0

theorem magnitude_nonneg (p : Bool) {d : ℝ} (hd : p=true → d≤0) : 0≤ magnitude p d := by
  cases hp : p
  · simp [magnitude]
  · simpa [magnitude,hp] using neg_nonneg.mpr (hd hp)

theorem magnitude_le_negativePart (p : Bool) (d : ℝ) : magnitude p d≤negativePart d := by
  cases p
  · exact negativePart_nonneg d
  · exact le_max_left _ _

theorem primary_charged_nonneg {d A B : ℝ} (hd : d≤0) (hsmall : |d|≤frameCap)
    (hA : (447/800:ℝ)≤A) (hB : B≤283/200) :
    0≤primaryGain d A B+charge*d := by
  have hs : -d∈Icc 0 frameCap := ⟨neg_nonneg.mpr hd,(neg_le_abs d).trans hsmall⟩
  have hh := primaryGain_lower hs hA hB
  simp only [neg_neg,charge] at hh ⊢
  linarith

theorem td_charged_nonneg {d : ℝ} {T : SignedPoint} (hd : d≤0) (hsmall : |d|≤frameCap)
    (hT : T.Sorted) (hcore : T.AvoidsCore) : 0≤tdGain d T+charge*d := by
  have hs : -d∈Icc 0 frameCap := ⟨neg_nonneg.mpr hd,(neg_le_abs d).trans hsmall⟩
  have hh := tdGain_lower hs hT hcore
  simp only [neg_neg,charge] at hh ⊢
  linarith

theorem e_charged_lower (p : Bool) {d A : ℝ} (hd : p=true → d≤0)
    (hsmall : |d|≤frameCap) (hA : A≤283/200) :
    g (magnitude p d)-charge*magnitude p d≤ if p then eGain d A+charge*d else 0 := by
  cases hp : p
  · simp [magnitude]
  · have hs : -d∈Icc 0 frameCap := ⟨neg_nonneg.mpr (hd hp),(neg_le_abs d).trans hsmall⟩
    have hh := eGain_lower hs hA
    simp only [neg_neg] at hh
    simpa [magnitude,sub_eq_add_neg,mul_neg] using add_le_add_right hh (charge*d)

theorem gains_reserve {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hq : q≤qCap)
    (hvar : positiveVariation C.theta≤frameCap)
    (hga : ga=true → delta C.theta G≤0) (hab : ab=true → delta C.theta A≤0)
    (htd : td=true → delta C.theta T≤0) (hde : de=true → delta C.theta D≤0)
    (heh : eh=true → delta C.theta E≤0) : -baseline<gains ga ab td de eh C := by
  have hn : negativeVariation C.theta≤frameCap := by rwa [←variations_equal]
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hA := SignedPoint.coordinate_bounds (hs A) (hcore A) (hc A) hq
  have hG := SignedPoint.coordinate_bounds (hs G) (hcore G) (hc G) hq
  have hB := SignedPoint.coordinate_bounds (hs B) (hcore B) (hc B) hq
  have hD := SignedPoint.coordinate_bounds (hs D) (hcore D) (hc D) hq
  have hH := SignedPoint.coordinate_bounds (hs H) (hcore H) (hc H) hq
  have hBy : -(C.point B).y≤283/200 := by linarith [neg_le_abs (C.point B).y,hB.2.2]
  have hgainG : 0≤ if ga then primaryGain (delta C.theta G) (C.point A).a (C.point G).a+
      charge*delta C.theta G else 0 := by
    cases hp : ga
    · simp
    · exact primary_charged_nonneg (hga hp) (hsmall G) hA.1.le hG.2.1.le
  have hgainA : 0≤ if ab then primaryGain (delta C.theta A) (C.point A).a (-(C.point B).y)+
      charge*delta C.theta A else 0 := by
    cases hp : ab
    · simp
    · exact primary_charged_nonneg (hab hp) (hsmall A) hA.1.le hBy
  have hgainT : 0≤ if td then tdGain (delta C.theta T) (C.point T)+charge*delta C.theta T else 0 := by
    cases hp : td
    · simp
    · exact td_charged_nonneg (htd hp) (hsmall T) (hs T) (hcore T)
  have hgainD := e_charged_lower de hde (hsmall D) hD.2.1.le
  have hgainH := e_charged_lower eh heh (hsmall E) hH.2.1.le
  have hnD := magnitude_nonneg de hde
  have hnH := magnitude_nonneg eh heh
  have hsum : magnitude de (delta C.theta D)+magnitude eh (delta C.theta E)≤frameCap := by
    have hh := (original_pair_budgets (i:=D) (j:=E) hvar hn (by norm_num [D,E])).2
    exact (add_le_add (magnitude_le_negativePart de _) (magnitude_le_negativePart eh _)).trans hh
  have hcombine := gain_pair hnD hnH hsum
  have hfinal := baseline_gain_positive ⟨add_nonneg hnD hnH,hsum⟩
  dsimp [gains]
  linarith

theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12) (_hEy : (C.point E).y∈Icc (-(1/2:ℝ)) 0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2)) (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (hDE : C.Feasible D (if de then 3 else 2)) (hEH : C.Feasible E (if eh then 1 else 0))
    (hga : ga=true → delta C.theta G≤0) (hab : ab=true → delta C.theta A≤0)
    (htd : td=true → delta C.theta T≤0) (hde : de=true → delta C.theta D≤0)
    (heh : eh=true → delta C.theta E≤0) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rwa [←variations_equal]
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab td de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hupper := stress_nonpos hsmall hf
  have hbase := reference_reserve hg ga ab td de eh hs hc hq hHy hGy hBy hDy hvar
  have hgain := gains_reserve ga ab td de eh hs hc hcore hq hvar hga hab htd hde heh
  have hid := decomposition hg ga ab td de eh C hflat
    (NegativePrimary.cos_pos (hsmall G)).ne' (NegativePrimary.cos_pos (hsmall A)).ne'
    (NegativePrimary.cos_pos (hsmall D)).ne' (NegativePrimary.cos_pos (hsmall E)).ne'
  rw [hid] at hupper
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeFlatE
end
end
end
