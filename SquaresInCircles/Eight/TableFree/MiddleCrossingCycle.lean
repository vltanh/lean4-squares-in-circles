module

public import SquaresInCircles.Eight.TableFree.MiddleNegativeCycle

/-!
# Direct AB0 contraction across the T frame

Uncompiled draft.  When `θB < θT ≤ θA`, the exact negative-hard-quarter
width gives a second comparison shift.  It is largest at `θT = θB`,
where it equals the already proved strict reference contraction.  Thus
the actual B point can jump directly to A's frame with strict loss on
its original circle; no minimizer or implicit continuation is needed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate MiddlePositiveContraction

namespace MiddleCrossingContraction

def comparisonX (X Y γ d : ℝ) : ℝ :=
  X*Real.cos d+Y*Real.sin d+(1-Real.cos d)-Real.sin d+
    Real.tan γ*(1-Real.sin d)

theorem comparison_norm_strict {X Y γ d : ℝ}
    (hXY : Y ≤ X) (hY : 1/2 ≤ Y) (hd : 0 < d)
    (hγ : 0 ≤ γ) (hγd : γ ≤ d) (hdu : d ≤ 7/10)
    (hpositive : 0 ≤ comparisonX X Y γ d) :
    (comparisonX X Y γ d)^2+(MiddleNegativeContraction.comparisonY X Y d)^2 <
      X^2+Y^2 := by
  have hdm : d ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le,hdu⟩
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hγ,hγd.trans hdu⟩
  have hzm : d-γ ∈ Icc 0 (7/10 : ℝ) := ⟨sub_nonneg.mpr hγd,by linarith⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hdm
  have hc0 : 0 < Real.cos d := by linarith
  have hcg0 : 0 < Real.cos γ := by linarith [(transport_trig_coarse hγm).1]
  let c := Real.cos d
  let s := Real.sin d
  let v := 1-c
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq d
  have hsp : 0 < 1+s := by dsimp [s]; linarith
  have htan : Real.tan γ ≤ s/c := by
    rw [Real.tan_eq_sin_div_cos,div_le_div_iff₀ hcg0 hc0]
    have hh := (transport_trig_coarse hzm).2.1
    rw [Real.sin_sub] at hh
    dsimp [c,s]
    nlinarith
  have hshift : v-s+(s/c)*(1-s)= -v*(c/(1+s)) := by
    dsimp [v]
    field_simp [hc0.ne',hsp.ne']
    linear_combination -(c+s)*hunit
  have hcompare : comparisonX X Y γ d ≤ X*c+Y*s-v*(c/(1+s)) := by
    have hp := mul_le_mul_of_nonneg_right htan (show 0 ≤ 1-s by dsimp [s]; linarith)
    change X*c+Y*s+v-s+Real.tan γ*(1-s) ≤ X*c+Y*s-v*(c/(1+s))
    linarith
  have hX2 := pow_le_pow_left₀ hpositive hcompare 2
  have href := MiddleNegativeContraction.reference_norm_strict hXY hY hd hdu
  change (X*c+Y*s-v*(c/(1+s)))^2+(-X*s+Y*c+v)^2 < X^2+Y^2 at href
  change (comparisonX X Y γ d)^2+(-X*s+Y*c+v)^2 < X^2+Y^2
  linarith

/-- The sign of the original BT angle determines the extra width term.
Keeping that term yields a strict direct comparison even across T. -/
theorem direct_norm_contraction {D Y0 X Y γ d : ℝ}
    (hD : 2/5 ≤ D) (hY0 : 0 < Y0) (hXY : Y ≤ X) (hY : 1/2 ≤ Y)
    (hd : 0 < d) (hγ : 0 ≤ γ) (hγd : γ ≤ d) (hdu : d ≤ 7/10)
    (hAB : Y0 ≤ MiddleNegativeContraction.comparisonY X Y d)
    (hBT : D ≤ (X-1)*Real.cos (d-γ)+(Y-1)*Real.sin (d-γ)) :
    7/5 ≤ primaryCorner D Y0 γ ∧
      (primaryCorner D Y0 γ)^2+Y0^2 < X^2+Y^2 := by
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hγ,hγd.trans hdu⟩
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
      ((X-1)*Real.cos (d-γ)+(Y-1)*Real.sin (d-γ)-D)+
        Real.sin γ*(MiddleNegativeContraction.comparisonY X Y d-Y0) := by
    dsimp [comparisonX,MiddleNegativeContraction.comparisonY,primaryCorner]
    rw [Real.cos_sub,Real.sin_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc0.ne']
    ring
  have hcompareX : primaryCorner D Y0 γ ≤ comparisonX X Y γ d := by
    have hp := mul_nonneg hs0 (sub_nonneg.mpr hAB)
    apply (mul_le_mul_iff_right₀ hc0).mp
    linarith
  have hX2 := pow_le_pow_left₀ (by linarith : 0 ≤ primaryCorner D Y0 γ) hcompareX 2
  have hY2 := pow_le_pow_left₀ hY0.le hAB 2
  have hcomparison := comparison_norm_strict hXY hY hd hγ hγd hdu
    (show 0 ≤ comparisonX X Y γ d by linarith)
  exact ⟨hprimary,by linarith⟩

theorem actual_B_contraction {A B T : SignedPoint} {γ d : ℝ}
    (hsA : A.Sorted) (hcA : A.AvoidsCore) (hqA : A.circle ≤ qCap)
    (hsB : B.Sorted) (hqB : B.circle ≤ qCap)
    (hyA : 0 ≤ A.y) (hyB : B.y ≤ 0) (hyT : -(1/10 : ℝ) ≤ T.y)
    (hd : 0 < d) (hγ : 0 ≤ γ) (hγd : γ ≤ d) (hdu : d ≤ 7/10)
    (hAB : zeroFeasible A B (-d) 0)
    (hBT : quarterFeasible B T (d-γ) 2) : Nonempty (BContraction A B T γ) := by
  let D := T.y+1/2
  let Y0 := 3/2-A.y
  let X := B.a+1/2
  let Y := -B.y+1/2
  let X0 := primaryCorner D Y0 γ
  have hγm : γ ∈ Icc 0 (7/10 : ℝ) := ⟨hγ,hγd.trans hdu⟩
  have hdm : d ∈ Icc 0 (7/10 : ℝ) := ⟨hd.le,hdu⟩
  have hzm : d-γ ∈ Icc 0 (7/10 : ℝ) := ⟨sub_nonneg.mpr hγd,by linarith⟩
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
  have hAB' : Y0 ≤ MiddleNegativeContraction.comparisonY X Y d := by
    have hh := hAB
    simp [zeroFeasible,zeroProjection] at hh
    rw [edgeWidth_positive_formula hdm] at hh
    dsimp [Y0,MiddleNegativeContraction.comparisonY,X,Y]
    nlinarith
  have hBT' : D ≤ (X-1)*Real.cos (d-γ)+(Y-1)*Real.sin (d-γ) := by
    have hh := hBT
    simp [quarterFeasible,quarterProjection] at hh
    rw [edgeWidth_positive_formula hzm] at hh
    dsimp [D,X,Y]
    nlinarith
  obtain ⟨hX0,hdrop⟩ := direct_norm_contraction hD (by linarith : 0 < Y0)
    hXY hY hd hγ hγd hdu hAB' hBT'
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

end MiddleCrossingContraction

namespace SignedCycle

theorem HardInput.crossing_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hBA : I.cycle.theta B ≤ I.cycle.theta T)
    (hTA : I.cycle.theta T ≤ I.cycle.theta A)
    (hAB : I.cycle.Feasible A 0) :
    Nonempty (BContraction (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta A-I.cycle.theta T)) := by
  have hdu : I.cycle.theta A-I.cycle.theta B ≤ 7/10 := by
    have hh := I.necessary.spread A B
    have ha := le_abs_self (I.cycle.theta A-I.cycle.theta B)
    dsimp [frameCap] at hh
    linarith
  have hAB' : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (-(I.cycle.theta A-I.cycle.theta B)) 0 := by
    rw [neg_sub]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      ((I.cycle.theta A-I.cycle.theta B)-(I.cycle.theta A-I.cycle.theta T)) 2 := by
    rw [show (I.cycle.theta A-I.cycle.theta B)-
      (I.cycle.theta A-I.cycle.theta T)=I.cycle.theta T-I.cycle.theta B by ring]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  exact MiddleCrossingContraction.actual_B_contraction
    (I.necessary.sorted A) (I.necessary.core A)
    ((I.necessary.contained A).trans hq) (I.necessary.sorted B)
    ((I.necessary.contained B).trans hq) I.anchors_normal.A_nonneg
    I.anchors_normal.B_nonpos hyT (sub_pos.mpr hd) (sub_nonneg.mpr hTA)
    (show I.cycle.theta A-I.cycle.theta T ≤ I.cycle.theta A-I.cycle.theta B by linarith)
    hdu hAB' hBT'

/-- The actual A frame being above T now suffices for either nonzero
original AB0 error.  There is no restriction on B's side of T. -/
theorem HardInput.middle_AB0_contraction_above_T {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hTA : I.cycle.theta T ≤ I.cycle.theta A)
    (hne : I.cycle.theta A ≠ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 0) :
    Nonempty (BContraction (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta A-I.cycle.theta T)) := by
  rcases lt_or_gt_of_ne hne with hpos | hneg
  · exact I.positive_middle_contraction hq hyT hpos hTA hAB
  · rcases le_total (I.cycle.theta T) (I.cycle.theta B) with hTB | hBT
    · exact I.negative_middle_contraction hq hyT hneg hTB hAB
    · exact I.crossing_middle_contraction hq hyT hneg hBT hTA hAB

theorem HardInput.align_nonzero_AB0_A_above_T {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hTA : I.cycle.theta T ≤ I.cycle.theta A)
    (hne : I.cycle.theta A ≠ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 0) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta B=I.cycle.theta A ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.middle_AB0_contraction_above_T hq hyT hTA hne hAB
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
end SquaresInCircles.Eight.TableFree
