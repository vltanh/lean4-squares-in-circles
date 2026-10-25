module

public import SquaresInCircles.Eight.Owners.GA.Positive.ATD0DVelocity
public import SquaresInCircles.Eight.Owners.GA.Sorted.Support

/-!
# Eight squares: the fixed positive-A stress at the two original D errors

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
  norm_num [dStress,dF,dG,clippedSupport,diagonalSupport,edgeWidth,pairWidth,lowC] <;> ring

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
  norm_num [dPositiveDiagonal,diagonalSupport,dF,dG,edgeWidth,pairWidth] <;> ring

theorem dPositiveFull_eq {z : ℝ} (hz : z∈Icc 0 frameCap) :
    dPositiveFull z=lowC*edgeWidth z+edgeWidth 0-
      fullSupport (dF z 0) (dG z 0)+charge*(z+0) := by
  rw [edgeWidth_positive_formula hz]
  unfold fullSupport
  rw [d_force_norm]
  norm_num [dPositiveFull,dF,dG,edgeWidth,pairWidth] <;> ring

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
