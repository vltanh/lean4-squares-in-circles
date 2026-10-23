module

public import SquaresInCircles.Eight.TableFree.TrigonometricReserves

/-!
# Direct contraction at a positive middle error

Uncompiled draft.  For original AB owner 0, a positive AB frame difference
contracts B directly to A's frame whenever A is at or above T.  The proof
uses the actual B corner norm, not a lift to a common comparison circle.
The parameter lower bound is `2/5`, so a T sign error of one tenth is
allowed.  This is Section 3 of the direct AB-alignment proof with the
enlarged range from the small-wrong-sign extension.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.MiddlePositiveContraction

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
  have hdm : d ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le,by linarith⟩
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hγ,by linarith⟩
  have hum : γ+d ∈ Icc 0 (7/10 : ℝ) := ⟨by linarith,hspan⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hdm
  obtain ⟨hcg,hcg1,hsg0,hsg,hsgc⟩ := transport_trig hγm
  have hsu := (transport_trig hum).2.2.2.1
  have hc0 : 0 < Real.cos d := by linarith
  have hcg0 : 0 < Real.cos γ := by linarith
  have hspos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd
    (by linarith [hdm.2,Real.pi_gt_three])
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
    linarith
  have ha0 : 0 < a := by dsimp [a]; linarith
  have hau : a < 37/20 := by dsimp [a]; linarith
  have hclt : c < 1 := by
    by_contra! hn
    have hp := mul_pos hspos hspos
    have hcs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hn 2
    nlinarith
  have hv : 0 < v := by dsimp [v]; linarith
  have hsum : 1 < c+s := by
    by_contra! hn
    have hcs := pow_le_pow_left₀ (by dsimp [c,s]; positivity : 0 ≤ c+s) hn 2
    have hp := mul_pos hc0 hspos
    nlinarith
  have hvs : v < s := by dsimp [v]; linarith
  have hAx : Real.tan γ*c+s-1 < 0 := by
    have hid : (Real.tan γ*c+s-1)*Real.cos γ=Real.sin (γ+d)-Real.cos γ := by
      dsimp [c,s]
      rw [Real.tan_eq_sin_div_cos,Real.sin_add]
      field_simp [hcg0.ne']
      ring
    by_contra! hn
    have hp := mul_nonneg hn hcg0.le
    rw [hid] at hp
    linarith
  let Bx := a*c*v+s*(v-s)
  let By := -a*s*v+c*(v-s)
  have hBxid : Bx=v*(Real.tan γ*c+s-1) := by
    dsimp [Bx,a,v]
    linear_combination -hunit
  have hBx : Bx < 0 := by rw [hBxid]; exact mul_neg_of_pos_of_neg hv hAx
  have hBy : By < 0 := by
    have hfirst : -a*s*v < 0 := mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by linarith : -a < 0) hspos) hv
    have hsecond : c*(v-s) < 0 := mul_neg_of_pos_of_neg hc0 (by linarith)
    dsimp [By]
    linarith
  let xd := (c-s)/2+a*v
  let yd := 1-(c+s)/2
  have hratio : (27/10 : ℝ)*v < s := by
    have hh : (27/10 : ℝ)*s < 1+c := by dsimp [c,s]; linarith
    have hp := mul_lt_mul_of_pos_right hh hv
    apply (mul_lt_mul_iff_left₀ hspos).mp
    dsimp [v] at hp ⊢
    nlinarith [hunit]
  have hxd : 0 < xd ∧ xd < 1/2 := by
    have hav := mul_lt_mul_of_pos_right hau hv
    have hav0 := mul_pos ha0 hv
    dsimp [xd,v]
    dsimp [v] at hav hratio hav0
    constructor <;> nlinarith
  have hyd : 0 < yd ∧ yd < 1/2 := by
    dsimp [yd,c,s]
    constructor <;> linarith
  have hxd2 := pow_lt_pow_left₀ hxd.1.le hxd.2 (by decide : (2:ℕ) ≠ 0)
  have hyd2 := pow_lt_pow_left₀ hyd.1.le hyd.2 (by decide : (2:ℕ) ≠ 0)
  have hdummy : xd^2+yd^2 < 1/2 := by nlinarith
  have hcoeffX := mul_nonpos_of_nonpos_of_nonneg hBx.le (sub_nonneg.mpr hX)
  have hcoeffY := mul_nonpos_of_nonpos_of_nonneg hBy.le (sub_nonneg.mpr hY)
  have hid : (comparisonX X Y γ d)^2+(comparisonY X Y d)^2-X^2-Y^2=
      xd^2+yd^2-1/2+2*Bx*(X-1/2)+2*By*(Y-1/2) := by
    dsimp [comparisonX,comparisonY,xd,yd,Bx,By,a,v,c,s]
    linear_combination (X^2+Y^2-1/2)*(Real.sin_sq_add_cos_sq d)
  nlinarith

/-- The original weak AB and BT contacts put the exact replacement below
the two comparison coordinates.  Its actual circle is strictly smaller. -/
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

/-- Original signed points invoke the direct norm contraction.  T may
have the small wrong sign; A and B retain their normal signs. -/
theorem actual_B_contraction {A B T : SignedPoint} {γ d : ℝ}
    (hsA : A.Sorted) (hcA : A.AvoidsCore) (hqA : A.circle ≤ qCap)
    (hsB : B.Sorted) (hqB : B.circle ≤ qCap)
    (hyA : 0 ≤ A.y) (hyB : B.y ≤ 0) (hyT : -(1/10 : ℝ) ≤ T.y)
    (hγ : 0 ≤ γ) (hd : 0 < d) (hspan : γ+d ≤ 7/10)
    (hAB : zeroFeasible A B d 0)
    (hBT : quarterFeasible B T (-(γ+d)) 2) : Nonempty (BContraction A B T γ) := by
  let D := T.y+1/2
  let Y0 := 3/2-A.y
  let X := B.a+1/2
  let Y := -B.y+1/2
  let X0 := primaryCorner D Y0 γ
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hγ,by linarith⟩
  have hdm : d ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le,by linarith⟩
  have hum : γ+d ∈ Icc 0 (7/10 : ℝ) := ⟨by linarith,hspan⟩
  have hD : 2/5 ≤ D := by dsimp [D]; linarith
  have hAy : A.y < 9/10 := by
    have hh := (SignedPoint.coordinate_bounds hsA hcA hqA le_rfl).2.2
    linarith [le_abs_self A.y]
  have hY0 : 3/5 < Y0 := by dsimp [Y0]; linarith
  have hX : 1/2 ≤ X := by dsimp [X]; linarith [hsB.1]
  have hY : 1/2 ≤ Y := by dsimp [Y]; linarith
  have hAB' : Y0 ≤ comparisonY X Y d := by
    have hh := hAB
    simp only [zeroFeasible,zeroProjection,Matrix.cons_val_zero] at hh
    rw [edgeWidth_positive_formula hdm] at hh
    dsimp [Y0,comparisonY,X,Y]
    nlinarith
  have hBT' : D ≤ (X-1)*Real.cos (γ+d)-Y*Real.sin (γ+d) := by
    have hh := hBT
    simp [quarterFeasible,quarterProjection] at hh
    rw [edgeWidth_positive_formula hum] at hh
    dsimp [D,X,Y]
    nlinarith
  obtain ⟨hX0,hdrop⟩ := direct_norm_contraction hD (by linarith : 0 < Y0)
    hX hY hγ hd hspan hAB' hBT'
  change 7/5 ≤ X0 at hX0
  change X0^2+Y0^2 < X^2+Y^2 at hdrop
  have hsource : X^2+Y^2=B.circle := by
    simp [X,Y,SignedPoint.circle,abs_of_nonpos hyB]
  have hsorted : Y0 < X0 := by
    by_contra! hn
    have hXs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7/5) hX0 2
    have hYs := pow_le_pow_left₀ (by linarith : 0 ≤ X0) hn 2
    have hq := hqB
    rw [← hsource] at hq
    dsimp [qCap] at hq
    nlinarith
  let B' : SignedPoint := ⟨X0-1/2,-(Y0-1/2)⟩
  have hnormal : B'.y < 0 := by dsimp [B']; linarith
  have hcircle : B'.circle=X0^2+Y0^2 := by
    dsimp [SignedPoint.circle]
    rw [abs_of_neg hnormal]
    dsimp [B']
    ring
  have hABexact : A.y-B'.y=1 := by dsimp [B',Y0]; ring
  refine ⟨{
    point := B'
    sorted := ⟨by dsimp [B']; linarith,?_⟩
    avoids := ?_
    normal := hnormal
    circle_lt := by rw [hcircle,← hsource]; exact hdrop
    AB_exact := hABexact
    AB_zero := by simpa [zeroFeasible,zeroProjection,hABexact]
    AB_two := by simpa [zeroFeasible,zeroProjection,hABexact]
    BT_exact := ?_
  }⟩
  · rw [abs_of_neg hnormal]
    dsimp [B']
    linarith
  · have ha : (9/10 : ℝ) ≤ B'.a := by dsimp [B']; linarith
    dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ B'.a-1/2)]
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2/5)
      (show 2/5 ≤ B'.a-1/2 by linarith) 2
    nlinarith [sq_nonneg (max (|B'.y|-1/2) 0)]
  · have hc : Real.cos γ ≠ 0 := ne_of_gt (by
      linarith [(transport_trig_coarse hγm).1] : 0 < Real.cos γ)
    have hh := primaryCorner_contact (D := D) (Y := Y0) hc
    change (X0-1)*Real.cos γ-Y0*Real.sin γ=D at hh
    change B'.a*Real.cos (-γ)-B'.y*Real.sin (-γ)-T.y=edgeWidth (-γ)
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg,edgeWidth_positive_formula hγm]
    dsimp [B',D] at *
    nlinarith

end SquaresInCircles.Eight.TableFree.MiddlePositiveContraction
