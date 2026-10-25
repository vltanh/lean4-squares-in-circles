module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: direct contraction at a positive middle error

For the original AB owner 0, a positive AB frame difference contracts B directly to A's frame
whenever A is at or above T (`actual_B_contraction`). The proof uses the norm of B's own corner,
with no lift to a common comparison circle (`direct_norm_contraction`). The parameter lower bound
is `2/5`, so a T sign error of one tenth is allowed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddlePositiveContraction

def comparisonX (X Y γ d : ℝ) : ℝ :=
  X*Real.cos d-Y*Real.sin d+(1+Real.tan γ)*(1-Real.cos d)
def comparisonY (X Y d : ℝ) : ℝ :=
  X*Real.sin d+Y*Real.cos d+1-Real.cos d-Real.sin d
def primaryCorner (D Y γ : ℝ) : ℝ := 1+D/Real.cos γ+Y*Real.tan γ

/-- A whole-domain norm inequality for the two comparison coordinates.
The affine norm difference has negative coefficients in both original
corner coordinates, so the dummy corner `(1/2,1/2)` is its maximum. -/
theorem comparison_norm_strict {X Y γ d : ℝ}
    (hX : 1/2 ≤ X) (hY : 1/2 ≤ Y)
    (hγ : 0 ≤ γ) (hd : 0 < d) (hspan : γ+d ≤ 7/10) :
    (comparisonX X Y γ d)^2+(comparisonY X Y d)^2 < X^2+Y^2 := by
  have hdm : d ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le,by linarith only [hγ,hspan]⟩
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hγ,by linarith only [hd,hspan]⟩
  have hum : γ+d ∈ Icc 0 (7/10 : ℝ) := ⟨by linarith only [hγ,hd],hspan⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hdm
  obtain ⟨hcg,hcg1,hsg0,hsg,hsgc⟩ := transport_trig hγm
  have hsu := (transport_trig hum).2.2.2.1
  have hc0 : 0 < Real.cos d := by linarith only [hc]
  have hcg0 : 0 < Real.cos γ := by linarith only [hcg]
  have hspos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd
    (by linarith only [hdm.2,Real.pi_gt_three])
  let c := Real.cos d
  let s := Real.sin d
  let v := 1-c
  let a := 1+Real.tan γ
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq d
  have ht0 : 0 ≤ Real.tan γ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg hsg0 hcg0.le
  have htu : Real.tan γ < 17/20 := by
    rw [Real.tan_eq_sin_div_cos,div_lt_iff₀ hcg0]
    linarith only [hsg,hcg]
  have ha0 : 0 < a := by dsimp [a]; linarith only [ht0]
  have hau : a < 37/20 := by dsimp [a]; linarith only [htu]
  have hclt : c < 1 := by
    by_contra! hn
    have hp := mul_pos hspos hspos
    have hcs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hn 2
    linarith only [hp,hcs,hunit]
  have hv : 0 < v := by dsimp [v]; linarith only [hclt]
  have hsum : 1 < c+s := by
    by_contra! hn
    have hcs := pow_le_pow_left₀ (by dsimp [c,s]; positivity : 0 ≤ c+s) hn 2
    have hp := mul_pos hc0 hspos
    linarith only [hcs,hp,hunit]
  have hvs : v < s := by dsimp [v]; linarith only [hsum]
  have hAx : Real.tan γ*c+s-1 < 0 := by
    have hid : (Real.tan γ*c+s-1)*Real.cos γ=Real.sin (γ+d)-Real.cos γ := by
      dsimp [c,s]
      rw [Real.tan_eq_sin_div_cos,Real.sin_add]
      field_simp [hcg0.ne']
    by_contra! hn
    have hp := mul_nonneg hn hcg0.le
    rw [hid] at hp
    linarith only [hp,hsu,hcg]
  let Bx := a*c*v+s*(v-s)
  let By := -a*s*v+c*(v-s)
  have hBxid : Bx=v*(Real.tan γ*c+s-1) := by
    dsimp [Bx,a,v]
    linear_combination -hunit
  have hBx : Bx < 0 := by rw [hBxid]; exact mul_neg_of_pos_of_neg hv hAx
  have hBy : By < 0 := by
    have hfirst : -a*s*v < 0 := mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by linarith only [ha0] : -a < 0) hspos) hv
    have hsecond : c*(v-s) < 0 := mul_neg_of_pos_of_neg hc0 (by linarith only [hvs])
    dsimp [By]
    linarith only [hfirst,hsecond]
  let xd := (c-s)/2+a*v
  let yd := 1-(c+s)/2
  have hratio : (27/10 : ℝ)*v < s := by
    have hh : (27/10 : ℝ)*s < 1+c := by dsimp [c,s]; linarith only [hs,hc]
    have hp := mul_lt_mul_of_pos_right hh hv
    apply (mul_lt_mul_iff_left₀ hspos).mp
    dsimp [v] at hp ⊢
    linarith only [hp,hunit]
  have hxd : 0 < xd ∧ xd < 1/2 := by
    have hav := mul_lt_mul_of_pos_right hau hv
    have hav0 := mul_pos ha0 hv
    dsimp [xd,v]
    dsimp [v] at hav hratio hav0
    constructor <;> linarith only [hav,hav0,hratio,hsc]
  have hyd : 0 < yd ∧ yd < 1/2 := by
    dsimp [yd,c,s]
    constructor <;> linarith only [hc1,hs,hsum]
  have hxd2 := pow_lt_pow_left₀ hxd.2 hxd.1.le (by decide : (2:ℕ) ≠ 0)
  have hyd2 := pow_lt_pow_left₀ hyd.2 hyd.1.le (by decide : (2:ℕ) ≠ 0)
  have hdummy : xd^2+yd^2 < 1/2 := by linarith only [hxd2,hyd2]
  have hcoeffX := mul_nonpos_of_nonpos_of_nonneg hBx.le (sub_nonneg.mpr hX)
  have hcoeffY := mul_nonpos_of_nonpos_of_nonneg hBy.le (sub_nonneg.mpr hY)
  have hid : (comparisonX X Y γ d)^2+(comparisonY X Y d)^2-X^2-Y^2=
      xd^2+yd^2-1/2+2*Bx*(X-1/2)+2*By*(Y-1/2) := by
    dsimp [comparisonX,comparisonY,xd,yd,Bx,By,a,v,c,s]
    linear_combination (X^2+Y^2-1/2)*(Real.sin_sq_add_cos_sq d)
  linarith only [hid,hdummy,hcoeffX,hcoeffY]

/-- The original weak AB and BT contacts put the exact new B below the two comparison
coordinates. Its circle is strictly smaller. -/
theorem direct_norm_contraction {D Y0 X Y γ d : ℝ}
    (hD : 2/5 ≤ D) (hY0 : 0 < Y0) (hX : 1/2 ≤ X) (hY : 1/2 ≤ Y)
    (hγ : 0 ≤ γ) (hd : 0 < d) (hspan : γ+d ≤ 7/10)
    (hAB : Y0 ≤ comparisonY X Y d)
    (hBT : D ≤ (X-1)*Real.cos (γ+d)-Y*Real.sin (γ+d)) :
    7/5 ≤ primaryCorner D Y0 γ ∧
      (primaryCorner D Y0 γ)^2+Y0^2 < X^2+Y^2 := by
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hγ,by linarith⟩
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hγm
  have hc0 : 0 < Real.cos γ := by linarith
  have ht0 : 0 ≤ Real.tan γ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg hs0 hc0.le
  have hD0 : 0 ≤ D := by linarith
  have hDdiv : D ≤ D/Real.cos γ := by
    rw [le_div_iff₀ hc0]
    have hp := mul_nonneg hD0 (sub_nonneg.mpr (Real.cos_le_one γ))
    nlinarith
  have hprimary : 7/5 ≤ primaryCorner D Y0 γ := by
    have hp := mul_nonneg hY0.le ht0
    dsimp [primaryCorner]
    linarith
  have hid : (comparisonX X Y γ d-primaryCorner D Y0 γ)*Real.cos γ=
      ((X-1)*Real.cos (γ+d)-Y*Real.sin (γ+d)-D)+
        Real.sin γ*(comparisonY X Y d-Y0) := by
    dsimp [comparisonX,comparisonY,primaryCorner]
    rw [Real.cos_add,Real.sin_add,Real.tan_eq_sin_div_cos]
    field_simp [hc0.ne']
    ring
  have hcompareX : primaryCorner D Y0 γ ≤ comparisonX X Y γ d := by
    have hp := mul_nonneg hs0 (sub_nonneg.mpr hAB)
    apply (mul_le_mul_iff_right₀ hc0).mp
    linarith
  have hX2 := pow_le_pow_left₀ (by linarith : 0 ≤ primaryCorner D Y0 γ) hcompareX 2
  have hY2 := pow_le_pow_left₀ hY0.le hAB 2
  exact ⟨hprimary,by linarith [comparison_norm_strict hX hY hγ hd hspan]⟩

theorem primaryCorner_contact {D Y γ : ℝ} (hc : Real.cos γ ≠ 0) :
    (primaryCorner D Y γ-1)*Real.cos γ-Y*Real.sin γ=D := by
  dsimp [primaryCorner]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hc]
  ring

structure BContraction (A B T : SignedPoint) (γ : ℝ) where
  point : SignedPoint
  sorted : point.Sorted
  avoids : point.AvoidsCore
  normal : point.y < 0
  circle_lt : point.circle < B.circle
  AB_exact : A.y-point.y=1
  AB_zero : zeroFeasible A point 0 0
  AB_two : zeroFeasible A point 0 2
  BT_exact : quarterProjection point T (-γ) 2=edgeWidth (-γ)

/-- The direct norm contraction at the original signed points. T may have the small wrong
sign; A and B keep their normal signs. -/
theorem actual_B_contraction {A B T : SignedPoint} {γ d : ℝ}
    (hsA : A.Sorted) (hcA : A.AvoidsCore) (hqA : A.circle ≤ qCap)
    (hsB : B.Sorted) (hqB : B.circle ≤ qCap)
    (_hyA : 0 ≤ A.y) (hyB : B.y ≤ 0) (hyT : -(1/10 : ℝ) ≤ T.y)
    (hγ : 0 ≤ γ) (hd : 0 < d) (hspan : γ+d ≤ 7/10)
    (hAB : zeroFeasible A B d 0)
    (hBT : quarterFeasible B T (-(γ+d)) 2) : Nonempty (BContraction A B T γ) := by
  let D := T.y+1/2
  let Y0 := 3/2-A.y
  let X := B.a+1/2
  let Y := -B.y+1/2
  let X0 := primaryCorner D Y0 γ
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hγ,by linarith only [hd,hspan]⟩
  have hdm : d ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le,by linarith only [hγ,hspan]⟩
  have hum : γ+d ∈ Icc 0 (7/10 : ℝ) := ⟨by linarith only [hγ,hd],hspan⟩
  have hD : 2/5 ≤ D := by dsimp [D]; linarith only [hyT]
  have hAy : A.y < 9/10 := by
    have hh := (SignedPoint.coordinate_bounds hsA hcA hqA le_rfl).2.2
    linarith only [hh,le_abs_self A.y]
  have hY0 : 3/5 < Y0 := by dsimp [Y0]; linarith only [hAy]
  have hX : 1/2 ≤ X := by dsimp [X]; linarith only [hsB.1]
  have hY : 1/2 ≤ Y := by dsimp [Y]; linarith only [hyB]
  have hAB' : Y0 ≤ comparisonY X Y d := by
    have hh : edgeWidth d ≤ A.y+B.a*Real.sin d-B.y*Real.cos d := hAB
    rw [edgeWidth_positive_formula hdm] at hh
    dsimp [Y0,comparisonY,X,Y]
    linarith only [hh]
  have hBT' : D ≤ (X-1)*Real.cos (γ+d)-Y*Real.sin (γ+d) := by
    have hh : edgeWidth (-(γ+d)) ≤
        B.a*Real.cos (-(γ+d))-B.y*Real.sin (-(γ+d))-T.y := hBT
    rw [edgeWidth_neg,edgeWidth_positive_formula hum,Real.cos_neg,Real.sin_neg] at hh
    dsimp [D,X,Y]
    linarith only [hh]
  obtain ⟨hX0,hdrop⟩ := direct_norm_contraction hD (by linarith only [hY0] : 0 < Y0)
    hX hY hγ hd hspan hAB' hBT'
  change 7/5 ≤ X0 at hX0
  change X0^2+Y0^2 < X^2+Y^2 at hdrop
  have hsource : X^2+Y^2=B.circle := by
    simp [X,Y,SignedPoint.circle,abs_of_nonpos hyB]
  have hsorted : Y0 < X0 := by
    by_contra! hn
    have hXs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7/5) hX0 2
    have hYs := pow_le_pow_left₀ (by linarith only [hX0] : 0 ≤ X0) hn 2
    have hq := hqB
    rw [← hsource] at hq
    dsimp [qCap] at hq
    linarith only [hXs,hYs,hq,hdrop]
  let B' : SignedPoint := ⟨X0-1/2,-(Y0-1/2)⟩
  have hnormal : B'.y < 0 := by dsimp [B']; linarith only [hY0]
  have hcircle : B'.circle=X0^2+Y0^2 := by
    dsimp [SignedPoint.circle]
    rw [abs_of_neg hnormal]
    dsimp [B']
    ring
  have hABexact : A.y-B'.y=1 := by dsimp [B',Y0]; ring
  refine ⟨{
    point := B'
    sorted := ⟨by dsimp [B']; linarith only [hX0],?_⟩
    avoids := ?_
    normal := hnormal
    circle_lt := by rw [hcircle,← hsource]; exact hdrop
    AB_exact := hABexact
    AB_zero := by simp [zeroFeasible,zeroProjection,hABexact]
    AB_two := by simp [zeroFeasible,zeroProjection,hABexact]
    BT_exact := ?_
  }⟩
  · rw [abs_of_neg hnormal]
    dsimp [B']
    linarith only [hsorted]
  · have ha : (9/10 : ℝ) ≤ B'.a := by dsimp [B']; linarith only [hX0]
    dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith only [ha] : 0 ≤ B'.a-1/2)]
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2/5)
      (show 2/5 ≤ B'.a-1/2 by linarith only [ha]) 2
    linarith only [hs,sq_nonneg (max (|B'.y|-1/2) 0)]
  · have hc : Real.cos γ ≠ 0 := ne_of_gt (by
      linarith only [(transport_trig_coarse hγm).1] : 0 < Real.cos γ)
    have hh := primaryCorner_contact (D := D) (Y := Y0) hc
    change (X0-1)*Real.cos γ-Y0*Real.sin γ=T.y+1/2 at hh
    change (X0-1/2)*Real.cos (-γ)-(-(Y0-1/2))*Real.sin (-γ)-T.y=edgeWidth (-γ)
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg,edgeWidth_positive_formula hγm]
    linear_combination hh

end SquaresInCircles.Eight.MiddlePositiveContraction
