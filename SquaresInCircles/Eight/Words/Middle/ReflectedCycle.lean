module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.NecessaryCycle
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: the exact AB2 dual of the direct middle contractions

Reflection is used only for the local triple
`(B.reflect, A.reflect, G.reflect)`.  The resulting hard cycle changes A
alone and leaves the actual E data and E sign intact.  A nonzero AB2
error is aligned when G is at or above both middle frames, with strict
loss on A's original circle.
-/

section
/-!
## Direct contraction at a positive middle error

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
end
end
end

section
/-!
## Direct contraction at a negative middle error

If the original AB owner is 0 and T is at or below B's frame, a negative AB error contracts B
directly to A's frame (`actual_B_contraction`). The comparison uses B's original sorted corner and
its original circle (`direct_norm_contraction`). The lower transverse bound is `2/5`, allowing a
T sign error of one tenth.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddleNegativeContraction
open MiddlePositiveContraction

def comparisonX (X Y γ d : ℝ) : ℝ :=
  X*Real.cos d+Y*Real.sin d+(1-Real.cos d)+
    Real.tan γ*((1-Real.cos d)-Real.sin d)
def comparisonY (X Y d : ℝ) : ℝ :=
  -X*Real.sin d+Y*Real.cos d+(1-Real.cos d)

/-- The endpoint comparison at `γ = d`.  Its affine norm difference
decreases as either sorted corner coordinate increases.  Its value at
the dummy corner `(1/2,1/2)` is strictly negative. -/
theorem reference_norm_strict {X Y d : ℝ}
    (hXY : Y ≤ X) (hY : 1/2 ≤ Y) (hd : 0 < d) (hdu : d ≤ 7/10) :
    (X*Real.cos d+Y*Real.sin d-
      (1-Real.cos d)*(Real.cos d/(1+Real.sin d)))^2+
      (-X*Real.sin d+Y*Real.cos d+(1-Real.cos d))^2 < X^2+Y^2 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig (show d ∈ Icc 0 (7/10 : ℝ) from
    ⟨hd.le,hdu⟩)
  have hc0 : 0 < Real.cos d := by linarith
  have hspos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd
    (by linarith [Real.pi_gt_three])
  let c := Real.cos d
  let s := Real.sin d
  let v := 1-c
  let r := c/(1+s)
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq d
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
  have hsp : 0 < 1+s := by dsimp [s]; linarith
  have hr : r < 1 := by
    dsimp [r]
    rw [div_lt_iff₀ hsp]
    dsimp [c,s]
    linarith
  have hrid : r*(1+s)=c := by
    dsimp [r]
    field_simp [hsp.ne']
  have hrc : r*c=1-s := by
    have hp : (r*c-(1-s))*(1+s)=0 := by
      linear_combination c*hrid+hunit
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hsp.ne')
  have hrr : r^2*(1+s)=1-s := by
    linear_combination r*hrid+hrc
  have hnorm : (X*c+Y*s-v*r)^2+(-X*s+Y*c+v)^2-X^2-Y^2=
      2*v*(-X+r*Y)+v^2*(1+r^2) := by
    linear_combination (X^2+Y^2)*hunit-2*v*X*hrc-2*v*Y*hrid
  have hbase : -X+r*Y ≤ (r-1)/2 := by
    have hp := mul_nonpos_of_nonpos_of_nonneg
      (show r-1 ≤ 0 by linarith) (sub_nonneg.mpr hY)
    nlinarith
  have hcoeff := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 2*v)
  have hdummy : v*(r-1)+v^2*(1+r^2)=v*(v-s)/(1+s) := by
    apply (eq_div_iff hsp.ne').2
    dsimp [v]
    linear_combination (1-c)*hrid+(1-c)^2*hrr
  have hnegative : v*(v-s)/(1+s) < 0 := div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hv (sub_neg.mpr hvs)) hsp
  change (X*c+Y*s-v*r)^2+(-X*s+Y*c+v)^2 < X^2+Y^2
  linarith

/-- For `γ ≥ d`, increasing the target angle only decreases the first
comparison coordinate.  Nonnegativity is supplied by the weak
contact comparison in `direct_norm_contraction`. -/
theorem comparison_norm_strict {X Y γ d : ℝ}
    (hXY : Y ≤ X) (hY : 1/2 ≤ Y) (hd : 0 < d)
    (hdγ : d ≤ γ) (hγu : γ ≤ 7/10)
    (hpositive : 0 ≤ comparisonX X Y γ d) :
    (comparisonX X Y γ d)^2+(comparisonY X Y d)^2 < X^2+Y^2 := by
  have hdm : d ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le,hdγ.trans hγu⟩
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le.trans hdγ,hγu⟩
  have hzm : γ-d ∈ Icc 0 (7/10 : ℝ) := ⟨sub_nonneg.mpr hdγ,by linarith⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hdm
  have hc0 : 0 < Real.cos d := by linarith
  have hcg0 : 0 < Real.cos γ := by linarith [(transport_trig_coarse hγm).1]
  have hspos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd
    (by linarith [hdm.2,Real.pi_gt_three])
  let c := Real.cos d
  let s := Real.sin d
  let v := 1-c
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq d
  have hsp : 0 < 1+s := by dsimp [s]; linarith
  have hsum : 1 < c+s := by
    by_contra! hn
    have hcs := pow_le_pow_left₀ (by dsimp [c,s]; positivity : 0 ≤ c+s) hn 2
    have hp := mul_pos hc0 hspos
    nlinarith
  have hvs : v < s := by dsimp [v]; linarith
  have htan : s/c ≤ Real.tan γ := by
    rw [Real.tan_eq_sin_div_cos,div_le_div_iff₀ hc0 hcg0]
    have hh := (transport_trig_coarse hzm).2.1
    rw [Real.sin_sub] at hh
    dsimp [c,s]
    nlinarith
  have hshift : v+(s/c)*(v-s)= -v*(c/(1+s)) := by
    have hc' : c ≠ 0 := hc0.ne'
    have hs' : 1+s ≠ 0 := hsp.ne'
    dsimp only [v]
    field_simp
    linear_combination -(c+s)*hunit
  have hcompare : comparisonX X Y γ d ≤ X*c+Y*s-v*(c/(1+s)) := by
    have hp := mul_le_mul_of_nonpos_right htan (show v-s ≤ 0 by linarith)
    change X*c+Y*s+v+Real.tan γ*(v-s) ≤ X*c+Y*s-v*(c/(1+s))
    linarith
  have hX2 := pow_le_pow_left₀ hpositive hcompare 2
  have href := reference_norm_strict hXY hY hd (hdγ.trans hγu)
  change (X*c+Y*s-v*(c/(1+s)))^2+(-X*s+Y*c+v)^2 < X^2+Y^2 at href
  change (comparisonX X Y γ d)^2+(-X*s+Y*c+v)^2 < X^2+Y^2
  linarith

/-- The two original weak witnesses bound the exact aligned B by the comparison corner. The
strict decrease uses the original norm. -/
theorem direct_norm_contraction {D Y0 X Y γ d : ℝ}
    (hD : 2/5 ≤ D) (hY0 : 0 < Y0) (hXY : Y ≤ X) (hY : 1/2 ≤ Y)
    (hd : 0 < d) (hdγ : d ≤ γ) (hγu : γ ≤ 7/10)
    (hAB : Y0 ≤ comparisonY X Y d)
    (hBT : D ≤ (X-1)*Real.cos (γ-d)-Y*Real.sin (γ-d)) :
    7/5 ≤ primaryCorner D Y0 γ ∧
      (primaryCorner D Y0 γ)^2+Y0^2 < X^2+Y^2 := by
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le.trans hdγ,hγu⟩
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
      ((X-1)*Real.cos (γ-d)-Y*Real.sin (γ-d)-D)+
        Real.sin γ*(comparisonY X Y d-Y0) := by
    dsimp [comparisonX,comparisonY,primaryCorner]
    rw [Real.cos_sub,Real.sin_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc0.ne']
    ring
  have hcompareX : primaryCorner D Y0 γ ≤ comparisonX X Y γ d := by
    have hp := mul_nonneg hs0 (sub_nonneg.mpr hAB)
    apply (mul_le_mul_iff_right₀ hc0).mp
    linarith
  have hX2 := pow_le_pow_left₀ (by linarith : 0 ≤ primaryCorner D Y0 γ) hcompareX 2
  have hY2 := pow_le_pow_left₀ hY0.le hAB 2
  have hcomparison := comparison_norm_strict hXY hY hd hdγ hγu
    (show 0 ≤ comparisonX X Y γ d by linarith)
  exact ⟨hprimary,by linarith⟩

/-- A negative original AB0 error with B at or above T has an aligned B with a smaller original
circle and exact AB and BT contacts. -/
theorem actual_B_contraction {A B T : SignedPoint} {γ d : ℝ}
    (hsA : A.Sorted) (hcA : A.AvoidsCore) (hqA : A.circle ≤ qCap)
    (hsB : B.Sorted) (hqB : B.circle ≤ qCap)
    (_hyA : 0 ≤ A.y) (hyB : B.y ≤ 0) (hyT : -(1/10 : ℝ) ≤ T.y)
    (hd : 0 < d) (hdγ : d ≤ γ) (hγu : γ ≤ 7/10)
    (hAB : zeroFeasible A B (-d) 0)
    (hBT : quarterFeasible B T (-(γ-d)) 2) : Nonempty (BContraction A B T γ) := by
  let D := T.y+1/2
  let Y0 := 3/2-A.y
  let X := B.a+1/2
  let Y := -B.y+1/2
  let X0 := primaryCorner D Y0 γ
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le.trans hdγ,hγu⟩
  have hdm : d ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le,hdγ.trans hγu⟩
  have hzm : γ-d ∈ Icc 0 (7/10 : ℝ) := ⟨sub_nonneg.mpr hdγ,by linarith only [hd,hγu]⟩
  have hD : 2/5 ≤ D := by dsimp [D]; linarith only [hyT]
  have hAy : A.y < 9/10 := by
    have hh := (SignedPoint.coordinate_bounds hsA hcA hqA le_rfl).2.2
    linarith only [hh,le_abs_self A.y]
  have hY0 : 3/5 < Y0 := by dsimp [Y0]; linarith only [hAy]
  have hXY : Y ≤ X := by
    have hh := hsB.2
    rw [abs_of_nonpos hyB] at hh
    dsimp [X,Y]
    linarith only [hh]
  have hY : 1/2 ≤ Y := by dsimp [Y]; linarith only [hyB]
  have hAB' : Y0 ≤ comparisonY X Y d := by
    have hh : edgeWidth (-d) ≤ A.y+B.a*Real.sin (-d)-B.y*Real.cos (-d) := hAB
    rw [edgeWidth_neg,edgeWidth_positive_formula hdm,Real.sin_neg,Real.cos_neg] at hh
    dsimp [Y0,comparisonY,X,Y]
    linarith only [hh]
  have hBT' : D ≤ (X-1)*Real.cos (γ-d)-Y*Real.sin (γ-d) := by
    have hh : edgeWidth (-(γ-d)) ≤
        B.a*Real.cos (-(γ-d))-B.y*Real.sin (-(γ-d))-T.y := hBT
    rw [edgeWidth_neg,edgeWidth_positive_formula hzm,Real.cos_neg,Real.sin_neg] at hh
    dsimp [D,X,Y]
    linarith only [hh]
  obtain ⟨hX0,hdrop⟩ := direct_norm_contraction hD (by linarith only [hY0] : 0 < Y0)
    hXY hY hd hdγ hγu hAB' hBT'
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

end SquaresInCircles.Eight.MiddleNegativeContraction
end
end
end

section
/-!
## A positive-AB-error reduction of a hard necessary cycle

The original positive AB0 error is removed by the B contraction (`replaceB`,
`HardInput.positive_middle_contraction`). Only B's center and frame change. Its new frame is the
original A frame, so the real frame interval cannot expand. The strict circle loss is at the
anchor B and keeps every earlier B loss (`HardInput.align_positive_AB0`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate MiddlePositiveContraction
namespace SignedCycle

def replaceB (C : SignedCycle) (P : SignedPoint) : SignedCycle :=
  replacePoint C B P (C.theta A)

theorem replaceB_unchanged (C : SignedCycle) (P : SignedPoint)
    (i : Vertex) (hi : i ≠ B) :
    (replaceB C P).point i=C.point i ∧ (replaceB C P).theta i=C.theta i := by
  simp [replaceB,replacePoint,hi]

theorem replaceB_spread {C : SignedCycle} (h : C.Spread) (P : SignedPoint) :
    (replaceB C P).Spread := by
  intro i j
  by_cases hi : i=B <;> by_cases hj : j=B
  · subst i; subst j
    simpa [replaceB,replacePoint] using h A A
  · subst i
    simpa [replaceB,replacePoint,hj] using h A j
  · subst j
    simpa [replaceB,replacePoint,hi] using h i A
  · simpa [replaceB,replacePoint,hi,hj] using h i j

theorem replaceB_AB (C : SignedCycle) (P : SignedPoint) (j : Fin 4) :
    (replaceB C P).Feasible A j ↔ zeroFeasible (C.point A) P 0 j := by
  simp [replaceB,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,A,B,
    zeroFeasible,sub_nonneg]

theorem replaceB_BT (C : SignedCycle) (P : SignedPoint) (j : Fin 4) :
    (replaceB C P).Feasible B j ↔
      quarterFeasible P (C.point T) (C.theta T-C.theta A) j := by
  simp [replaceB,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,A,B,T,
    quarterFeasible,sub_nonneg]

def Witnesses.replaceB {C : SignedCycle} (w : C.Witnesses)
    (O : BContraction (C.point A) (C.point B) (C.point T) (C.theta A-C.theta T)) :
    (SignedCycle.replaceB C O.point).Witnesses where
  owner i := if i=B then 2 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · exact (replacePoint_other_feasible (v := B) (by decide : H ≠ B)
        (by decide : next H ≠ B)).2 (w.feasible H)
    · exact (replacePoint_other_feasible (v := B) (by decide : G ≠ B)
        (by decide : next G ≠ B)).2 (w.feasible G)
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      show (SignedCycle.replaceB C O.point).Feasible A (w.owner A)
      rcases hj with hj | hj
      · rw [hj]; exact (replaceB_AB C O.point _).2 O.AB_zero
      · rw [hj]; exact (replaceB_AB C O.point _).2 O.AB_two
    · apply (replaceB_BT C O.point 2).2
      unfold quarterFeasible
      have hh := O.BT_exact.symm.le
      simpa only [neg_sub] using hh
    · exact (replacePoint_other_feasible (v := B) (by decide : T ≠ B)
        (by decide : next T ≠ B)).2 (w.feasible T)
    · exact (replacePoint_other_feasible (v := B) (by decide : D ≠ B)
        (by decide : next D ≠ B)).2 (w.feasible D)
    · exact (replacePoint_other_feasible (v := B) (by decide : E ≠ B)
        (by decide : next E ≠ B)).2 (w.feasible E)
  allowed := by
    intro i
    by_cases hi : i=B
    · subst i; norm_num [normalOwners,B]
    · simpa [hi] using w.allowed i

def HardInput.fromPositiveMiddle {q : ℝ} (I : HardInput q)
    (O : BContraction (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta A-I.cycle.theta T)) : HardInput q where
  cycle := SignedCycle.replaceB I.cycle O.point
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=B
      · subst i; simpa [replaceB,replacePoint] using O.sorted
      · simpa [replaceB,replacePoint,hi] using I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=B
      · subst i
        have hh := O.circle_lt.le.trans (I.necessary.contained B)
        simpa [replaceB,replacePoint,SignedPoint.Contained] using hh
      · simpa [replaceB,replacePoint,hi] using I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=B
      · subst i; simpa [replaceB,replacePoint] using O.avoids
      · simpa [replaceB,replacePoint,hi] using I.necessary.core i
    spread := replaceB_spread I.necessary.spread O.point }
  anchors_normal := by
    constructor
    · simpa [replaceB,replacePoint,H,B] using I.anchors_normal.H_nonneg
    · simpa [replaceB,replacePoint,A,B] using I.anchors_normal.A_nonneg
    · simpa [replaceB,replacePoint] using O.normal.le
    · simpa [replaceB,replacePoint,D,B] using I.anchors_normal.D_nonpos
  E_nonpos := by simpa [replaceB,replacePoint,E,B] using I.E_nonpos
  witnesses := I.witnesses.replaceB O
  GA_hard := (replacePoint_other_feasible (v := B) (by decide : G ≠ B)
    (by decide : next G ≠ B)).2 I.GA_hard
  BT_hard := by
    apply (replaceB_BT I.cycle O.point 2).2
    unfold quarterFeasible
    simpa only [neg_sub] using O.BT_exact.symm.le
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.replaceB,H,B] using hh
      simpa [replaceB,replacePoint,G,B] using I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.replaceB,T,B] using hh
      simpa [replaceB,replacePoint,T,B] using I.zero_signs.TD_canceling hj }
  E_radial := by simpa [replaceB,replacePoint,H,D,E,B] using I.E_radial

theorem HardInput.positive_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta A < I.cycle.theta B)
    (hγ : I.cycle.theta T ≤ I.cycle.theta A)
    (hAB : I.cycle.Feasible A 0) :
    Nonempty (BContraction (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta A-I.cycle.theta T)) := by
  have hspan : (I.cycle.theta A-I.cycle.theta T)+
      (I.cycle.theta B-I.cycle.theta A) ≤ 7/10 := by
    have hh := I.necessary.spread B T
    have ha := le_abs_self (I.cycle.theta B-I.cycle.theta T)
    dsimp [frameCap] at hh
    linarith
  have hAB' : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-((I.cycle.theta A-I.cycle.theta T)+(I.cycle.theta B-I.cycle.theta A))) 2 := by
    rw [show -((I.cycle.theta A-I.cycle.theta T)+
      (I.cycle.theta B-I.cycle.theta A))=I.cycle.theta T-I.cycle.theta B by ring]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  exact actual_B_contraction (I.necessary.sorted A) (I.necessary.core A)
    ((I.necessary.contained A).trans hq) (I.necessary.sorted B)
    ((I.necessary.contained B).trans hq) I.anchors_normal.A_nonneg
    I.anchors_normal.B_nonpos hyT (sub_nonneg.mpr hγ) (sub_pos.mpr hd)
    hspan hAB' hBT'

/-- A nonzero original AB0 error in this frame sector has a hard descendant with the original A
frame and a strict B-anchor circle loss. -/
theorem HardInput.align_positive_AB0 {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta A < I.cycle.theta B)
    (hγ : I.cycle.theta T ≤ I.cycle.theta A)
    (hAB : I.cycle.Feasible A 0) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta B=I.cycle.theta A ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.positive_middle_contraction hq hyT hd hγ hAB
  refine ⟨I.fromPositiveMiddle O,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [HardInput.fromPositiveMiddle,replaceB,replacePoint,A,B]
  · simp [HardInput.fromPositiveMiddle,replaceB,replacePoint]
  · simpa [HardInput.fromPositiveMiddle,replaceB,replacePoint,A,B] using O.AB_exact
  · simpa [HardInput.fromPositiveMiddle,replaceB,replacePoint] using O.circle_lt
  · intro i hi
    by_cases hb : i=B
    · subst i
      simpa [HardInput.fromPositiveMiddle,replaceB,replacePoint] using O.circle_lt.le
    · exact (congrArg SignedPoint.circle (replaceB_unchanged I.cycle O.point i hb).1).le
  · refine ⟨B,by simp [anchorVertices],?_⟩
    simpa [HardInput.fromPositiveMiddle,replaceB,replacePoint] using O.circle_lt
  · exact replaceB_unchanged I.cycle O.point

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate MiddlePositiveContraction

namespace MiddleReflectedContraction

structure AContraction (G A B : SignedPoint) (γ : ℝ) where
  point : SignedPoint
  sorted : point.Sorted
  avoids : point.AvoidsCore
  normal : 0 < point.y
  circle_lt : point.circle < A.circle
  AB_exact : point.y-B.y=1
  AB_zero : zeroFeasible point B 0 0
  AB_two : zeroFeasible point B 0 2
  GA_exact : quarterProjection G point (-γ) 0=edgeWidth (-γ)

/-- Local physical owner reflection preserves the source anchor circle. -/
def reflectB {G A B : SignedPoint} {γ : ℝ}
    (O : BContraction B.reflect A.reflect G.reflect γ) : AContraction G A B γ where
  point := O.point.reflect
  sorted := by simpa using O.sorted
  avoids := by simpa using O.avoids
  normal := by simpa [SignedPoint.reflect] using neg_pos.mpr O.normal
  circle_lt := by simpa using O.circle_lt
  AB_exact := by
    have hh := O.AB_exact
    dsimp [SignedPoint.reflect] at hh ⊢
    linarith
  AB_zero := by
    have hh := (zeroFeasible_reflect O.point.reflect B 0 0).1
      (by simpa [reflectedOwner] using O.AB_two)
    exact hh
  AB_two := by
    have hh := (zeroFeasible_reflect O.point.reflect B 0 2).1
      (by simpa [reflectedOwner] using O.AB_zero)
    exact hh
  GA_exact := by
    have hp := quarterProjection_reflect G O.point.reflect (-γ) 0
    have he : quarterProjection O.point G.reflect (-γ) 2=
        quarterProjection G O.point.reflect (-γ) 0 := by
      simpa [reflectedOwner] using hp
    exact he.symm.trans O.BT_exact

end MiddleReflectedContraction

open MiddleReflectedContraction
namespace SignedCycle

def replaceA (C : SignedCycle) (P : SignedPoint) : SignedCycle :=
  replacePoint C A P (C.theta B)

theorem replaceA_unchanged (C : SignedCycle) (P : SignedPoint)
    (i : Vertex) (hi : i ≠ A) :
    (replaceA C P).point i=C.point i ∧ (replaceA C P).theta i=C.theta i := by
  simp [replaceA,replacePoint,hi]

theorem replaceA_spread {C : SignedCycle} (h : C.Spread) (P : SignedPoint) :
    (replaceA C P).Spread := by
  intro i j
  by_cases hi : i=A <;> by_cases hj : j=A
  · subst i; subst j
    simpa [replaceA,replacePoint] using h B B
  · subst i
    simpa [replaceA,replacePoint,hj] using h B j
  · subst j
    simpa [replaceA,replacePoint,hi] using h i B
  · simpa [replaceA,replacePoint,hi,hj] using h i j

theorem replaceA_GA (C : SignedCycle) (P : SignedPoint) (j : Fin 4) :
    (replaceA C P).Feasible G j ↔
      quarterFeasible (C.point G) P (C.theta B-C.theta G) j := by
  simp [replaceA,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,G,A,B,
    quarterFeasible,sub_nonneg]

theorem replaceA_AB (C : SignedCycle) (P : SignedPoint) (j : Fin 4) :
    (replaceA C P).Feasible A j ↔ zeroFeasible P (C.point B) 0 j := by
  simp [replaceA,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,A,B,
    zeroFeasible,sub_nonneg]

def Witnesses.replaceA {C : SignedCycle} (w : C.Witnesses)
    (O : AContraction (C.point G) (C.point A) (C.point B) (C.theta G-C.theta B)) :
    (SignedCycle.replaceA C O.point).Witnesses where
  owner i := if i=G then 0 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · exact (replacePoint_other_feasible (v := A) (by decide : H ≠ A)
        (by decide : next H ≠ A)).2 (w.feasible H)
    · apply (replaceA_GA C O.point 0).2
      unfold quarterFeasible
      simpa only [neg_sub] using O.GA_exact.symm.le
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj
      · have hAG : A ≠ G := by decide
        exact (replaceA_AB C O.point _).2 (by
          show zeroFeasible O.point (C.point B) 0 (if A = G then 0 else w.owner A)
          simp only [hAG,↓reduceIte,hj]
          exact O.AB_zero)
      · have hAG : A ≠ G := by decide
        exact (replaceA_AB C O.point _).2 (by
          show zeroFeasible O.point (C.point B) 0 (if A = G then 0 else w.owner A)
          simp only [hAG,↓reduceIte,hj]
          exact O.AB_two)
    · exact (replacePoint_other_feasible (v := A) (by decide : B ≠ A)
        (by decide : next B ≠ A)).2 (w.feasible B)
    · exact (replacePoint_other_feasible (v := A) (by decide : T ≠ A)
        (by decide : next T ≠ A)).2 (w.feasible T)
    · exact (replacePoint_other_feasible (v := A) (by decide : D ≠ A)
        (by decide : next D ≠ A)).2 (w.feasible D)
    · exact (replacePoint_other_feasible (v := A) (by decide : E ≠ A)
        (by decide : next E ≠ A)).2 (w.feasible E)
  allowed := by
    intro i
    by_cases hi : i=G
    · subst i; norm_num [normalOwners,G]
    · simpa [hi] using w.allowed i

def HardInput.fromReflectedMiddle {q : ℝ} (I : HardInput q)
    (O : AContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta G-I.cycle.theta B)) : HardInput q where
  cycle := SignedCycle.replaceA I.cycle O.point
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=A
      · subst i; simpa [replaceA,replacePoint] using O.sorted
      · simpa [replaceA,replacePoint,hi] using I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=A
      · subst i
        have hh := O.circle_lt.le.trans (I.necessary.contained A)
        simpa [replaceA,replacePoint,SignedPoint.Contained] using hh
      · simpa [replaceA,replacePoint,hi] using I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=A
      · subst i; simpa [replaceA,replacePoint] using O.avoids
      · simpa [replaceA,replacePoint,hi] using I.necessary.core i
    spread := replaceA_spread I.necessary.spread O.point }
  anchors_normal := by
    constructor
    · simpa [replaceA,replacePoint,H,A] using I.anchors_normal.H_nonneg
    · simpa [replaceA,replacePoint] using O.normal.le
    · simpa [replaceA,replacePoint,B,A] using I.anchors_normal.B_nonpos
    · simpa [replaceA,replacePoint,D,A] using I.anchors_normal.D_nonpos
  E_nonpos := by simpa [replaceA,replacePoint,E,A] using I.E_nonpos
  witnesses := I.witnesses.replaceA O
  GA_hard := by
    apply (replaceA_GA I.cycle O.point 0).2
    unfold quarterFeasible
    simpa only [neg_sub] using O.GA_exact.symm.le
  BT_hard := (replacePoint_other_feasible (v := A) (by decide : B ≠ A)
    (by decide : next B ≠ A)).2 I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.replaceA,H,G] using hh
      simpa [replaceA,replacePoint,G,A] using I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.replaceA,T,G] using hh
      simpa [replaceA,replacePoint,T,A] using I.zero_signs.TD_canceling hj }
  E_radial := by simpa [replaceA,replacePoint,H,D,E,A] using I.E_radial

/-- The two actual AB0 contraction formulas reflected at the original
local triple.  Both AB2 error signs are covered in this frame sector. -/
theorem HardInput.reflected_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hG : max (I.cycle.theta A) (I.cycle.theta B) ≤ I.cycle.theta G)
    (hne : I.cycle.theta A ≠ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 2) :
    Nonempty (AContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta G-I.cycle.theta B)) := by
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hABraw : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) 2 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hABref : zeroFeasible (I.cycle.point B).reflect (I.cycle.point A).reflect
      (I.cycle.theta B-I.cycle.theta A) 0 := by
    simpa [reflectedOwner] using (zeroFeasible_reflect _ _ _ 2).2 hABraw
  have hBTref : quarterFeasible (I.cycle.point A).reflect (I.cycle.point G).reflect
      (I.cycle.theta A-I.cycle.theta G) 2 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ _ 0).2 hGA
  have hs1 : (I.cycle.point B).reflect.Sorted := by simpa using I.necessary.sorted B
  have hc1 : (I.cycle.point B).reflect.AvoidsCore := by simpa using I.necessary.core B
  have hq1 : (I.cycle.point B).reflect.circle ≤ qCap := by
    simpa using (I.necessary.contained B).trans hq
  have hs2 : (I.cycle.point A).reflect.Sorted := by simpa using I.necessary.sorted A
  have hq2 : (I.cycle.point A).reflect.circle ≤ qCap := by
    simpa using (I.necessary.contained A).trans hq
  have hy1 : 0 ≤ (I.cycle.point B).reflect.y := by
    simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos
  have hy2 : (I.cycle.point A).reflect.y ≤ 0 := by
    simpa [SignedPoint.reflect] using neg_nonpos.mpr I.anchors_normal.A_nonneg
  have hy3 : -(1/10 : ℝ) ≤ (I.cycle.point G).reflect.y := by
    dsimp [SignedPoint.reflect]
    linarith
  have hAG := (le_max_left (I.cycle.theta A) (I.cycle.theta B)).trans hG
  have hBG := (le_max_right (I.cycle.theta A) (I.cycle.theta B)).trans hG
  rcases lt_or_gt_of_ne hne with hpos | hneg
  · have hspan : (I.cycle.theta G-I.cycle.theta B)+
        (I.cycle.theta B-I.cycle.theta A) ≤ 7/10 := by
      have hh := I.necessary.spread G A
      have ha := le_abs_self (I.cycle.theta G-I.cycle.theta A)
      dsimp [frameCap] at hh
      linarith
    have hBT' : quarterFeasible (I.cycle.point A).reflect (I.cycle.point G).reflect
        (-((I.cycle.theta G-I.cycle.theta B)+(I.cycle.theta B-I.cycle.theta A))) 2 := by
      rw [show -((I.cycle.theta G-I.cycle.theta B)+
        (I.cycle.theta B-I.cycle.theta A))=I.cycle.theta A-I.cycle.theta G by ring]
      exact hBTref
    obtain ⟨O⟩ := MiddlePositiveContraction.actual_B_contraction
      hs1 hc1 hq1 hs2 hq2 hy1 hy2 hy3 (sub_nonneg.mpr hBG)
      (sub_pos.mpr hpos) hspan hABref hBT'
    exact ⟨reflectB O⟩
  · have hγu : I.cycle.theta G-I.cycle.theta B ≤ 7/10 := by
      have hh := I.necessary.spread G B
      have ha := le_abs_self (I.cycle.theta G-I.cycle.theta B)
      dsimp [frameCap] at hh
      linarith
    have hAB' : zeroFeasible (I.cycle.point B).reflect (I.cycle.point A).reflect
        (-(I.cycle.theta A-I.cycle.theta B)) 0 := by
      simpa only [neg_sub] using hABref
    have hBT' : quarterFeasible (I.cycle.point A).reflect (I.cycle.point G).reflect
        (-((I.cycle.theta G-I.cycle.theta B)-(I.cycle.theta A-I.cycle.theta B))) 2 := by
      rw [show -((I.cycle.theta G-I.cycle.theta B)-
        (I.cycle.theta A-I.cycle.theta B))=I.cycle.theta A-I.cycle.theta G by ring]
      exact hBTref
    obtain ⟨O⟩ := MiddleNegativeContraction.actual_B_contraction
      hs1 hc1 hq1 hs2 hq2 hy1 hy2 hy3 (sub_pos.mpr hneg)
      (show I.cycle.theta A-I.cycle.theta B ≤ I.cycle.theta G-I.cycle.theta B by linarith)
      hγu hAB' hBT'
    exact ⟨reflectB O⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end
