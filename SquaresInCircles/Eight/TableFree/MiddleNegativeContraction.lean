module

public import SquaresInCircles.Eight.TableFree.MiddlePositiveContraction

/-!
# Direct contraction at a negative middle error

Uncompiled draft.  If the original AB owner is 0 and T is at or below
B's frame, a negative AB error contracts B directly to A's frame.  The
comparison uses B's original sorted corner and its original circle.  The
lower transverse bound is `2/5`, allowing a T sign error of one tenth.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.MiddleNegativeContraction
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
comparison coordinate.  Nonnegativity is supplied by the actual weak
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
    dsimp [v]
    field_simp [hc0.ne',hsp.ne']
    linear_combination -(1+s)*hunit
  have hcompare : comparisonX X Y γ d ≤ X*c+Y*s-v*(c/(1+s)) := by
    have hp := mul_le_mul_of_nonpos_right htan (show v-s ≤ 0 by linarith)
    change X*c+Y*s+v+Real.tan γ*(v-s) ≤ X*c+Y*s-v*(c/(1+s))
    linarith
  have hX2 := pow_le_pow_left₀ hpositive hcompare 2
  have href := reference_norm_strict hXY hY hd (hdγ.trans hγu)
  change (X*c+Y*s-v*(c/(1+s)))^2+(-X*s+Y*c+v)^2 < X^2+Y^2 at href
  change (comparisonX X Y γ d)^2+(-X*s+Y*c+v)^2 < X^2+Y^2
  linarith

/-- The two original weak witnesses bound the exact aligned replacement
by the comparison corner.  The strict decrease uses the original norm. -/
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

/-- A negative original AB0 error with B at or above T has an explicit
aligned B with smaller original circle and exact AB and BT contacts. -/
theorem actual_B_contraction {A B T : SignedPoint} {γ d : ℝ}
    (hsA : A.Sorted) (hcA : A.AvoidsCore) (hqA : A.circle ≤ qCap)
    (hsB : B.Sorted) (hqB : B.circle ≤ qCap)
    (hyA : 0 ≤ A.y) (hyB : B.y ≤ 0) (hyT : -(1/10 : ℝ) ≤ T.y)
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
  have hzm : γ-d ∈ Icc 0 (7/10 : ℝ) := ⟨sub_nonneg.mpr hdγ,by linarith⟩
  have hD : 2/5 ≤ D := by dsimp [D]; linarith
  have hAy : A.y < 9/10 := by
    have hh := (SignedPoint.coordinate_bounds hsA hcA hqA le_rfl).2.2
    linarith [le_abs_self A.y]
  have hY0 : 3/5 < Y0 := by dsimp [Y0]; linarith
  have hXY : Y ≤ X := by
    have hh := hsB.2
    rw [abs_of_nonpos hyB] at hh
    dsimp [X,Y]
    linarith
  have hY : 1/2 ≤ Y := by dsimp [Y]; linarith
  have hAB' : Y0 ≤ comparisonY X Y d := by
    have hh := hAB
    simp [zeroFeasible,zeroProjection] at hh
    rw [edgeWidth_positive_formula hdm] at hh
    dsimp [Y0,comparisonY,X,Y]
    nlinarith
  have hBT' : D ≤ (X-1)*Real.cos (γ-d)-Y*Real.sin (γ-d) := by
    have hh := hBT
    simp [quarterFeasible,quarterProjection] at hh
    rw [edgeWidth_positive_formula hzm] at hh
    dsimp [D,X,Y]
    nlinarith
  obtain ⟨hX0,hdrop⟩ := direct_norm_contraction hD (by linarith : 0 < Y0)
    hXY hY hd hdγ hγu hAB' hBT'
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

end SquaresInCircles.Eight.TableFree.MiddleNegativeContraction
