module

public import SquaresInCircles.Eight.Owners.Positive.ScalarData
public import SquaresInCircles.Eight.Owners.Positive.SplitComparison

/-!
# Eight squares: the seven trigonometric scalars are positive

Sine is replaced by a lower bound and cosine by an upper bound. The perturbation bound of the
Euclidean norm pays for the only varying norm row, and the radicand of `V` moves in the favorable
direction (`row_error`, `rowSum_error`, `demand_error`). The total error is at most `24/10¹⁵`,
below the allowance `10⁻¹²` of the polynomials, so the seven scalars are positive
(`value_positive`, `seven_scalar_bounds`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.PositiveScalarTransfer
open PositiveScalarPolynomials (ScalarCase)
open PositiveScalarData HighOrderTaylor ScalarRadicalTransfer

theorem tilted_error (c : ScalarCase) {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    |tilted c d (Real.sin d) (Real.cos d)-tilted c d (S15 d) (C16 d)|≤2*remainder := by
  rcases frame_remainders hd with ⟨hs0,hs1,hc0,hc1⟩
  rcases parameter_bounds c hd with ⟨hL,hL1,hcw,hη0,hη1⟩
  have he0 := mul_nonneg hη0 hs0
  have he1 := mul_le_mul hη1 hs1.le hs0 (by norm_num : (0:ℝ)≤19/50)
  apply abs_le.mpr
  dsimp [tilted,K]
  constructor <;> nlinarith

theorem row_error (c : ScalarCase) (i : Fin 5) {d : ℝ}
    (hd : d∈Set.Icc 0 frameCap) :
    (rowData c d (Real.sin d) (Real.cos d) i).2*
        Real.sqrt (rowData c d (Real.sin d) (Real.cos d) i).1≤
      (rowData c d (S15 d) (C16 d) i).2*
        Real.sqrt (rowData c d (S15 d) (C16 d) i).1+2*remainder := by
  have he := tilted_error c hd
  have hN1 := norm_coordinate_perturbation 1
    (tilted c d (Real.sin d) (Real.cos d)) (tilted c d (S15 d) (C16 d))
  have hNL := norm_coordinate_perturbation (ell c d)
    (tilted c d (Real.sin d) (Real.cos d)) (tilted c d (S15 d) (C16 d))
  rw [one_pow] at hN1
  rcases parameter_bounds c hd with ⟨hL,hL1,hcw,hη0,hη1⟩
  rcases frame_remainders hd with ⟨hs0,hs1,hc0,hc1⟩
  have hV : Real.sqrt (K^2+(ell c d)^2-2*K*ell c d*Real.sin d)≤
      Real.sqrt (K^2+(ell c d)^2-2*K*ell c d*S15 d) := by
    apply Real.sqrt_le_sqrt
    have h := mul_nonneg (mul_nonneg (show 0≤K by norm_num [K]) hL.le) hs0
    nlinarith
  have hroot : Real.sqrt (1+(eta c d)^2)≤2 := by
    have hη2 := pow_le_pow_left₀ hη0 hη1 2
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hprimary : K*Real.sin d*Real.sqrt (1+(eta c d)^2)≤
      K*S15 d*Real.sqrt (1+(eta c d)^2)+2*remainder := by
    have h := mul_le_mul hs1.le hroot (Real.sqrt_nonneg _) (by norm_num [remainder])
    have hK : K=863/1000 := rfl
    rw [hK]
    nlinarith
  have hrem : 0≤2*remainder := by norm_num [remainder]
  cases c <;> fin_cases i <;>
    simp only [rowData,PositiveScalarPolynomials.isP,PositiveScalarPolynomials.isV,
      Bool.false_eq_true,↓reduceIte,Fin.isValue,Fin.reduceFinMk,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.head_cons,Matrix.tail_cons,one_mul,zero_mul] <;>
    first
    | exact le_add_of_nonneg_right hrem
    | linarith only [hNL,he]
    | linarith only [hN1,he]
    | exact hprimary
    | linarith only [hV,hrem]

theorem rowSum_error (c : ScalarCase) {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    rowSum c d (Real.sin d) (Real.cos d)≤taylorSum c d+10*remainder := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => row_error c i hd)
  rw [Finset.sum_add_distrib] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  unfold taylorSum rowSum
  push_cast at h
  linarith

theorem demand_error (c : ScalarCase) {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    taylorDemand c d-4*remainder≤
      demandData c d (Real.sin d) (Real.cos d)
        (Real.sin (frameCap-d)) (Real.cos (frameCap-d)) := by
  have he : frameCap-d∈Set.Icc 0 frameCap := ⟨by linarith [hd.2],by linarith [hd.1]⟩
  rcases frame_remainders hd with ⟨hs0,hs1,hc0,hc1⟩
  rcases frame_remainders he with ⟨hes0,hes1,hec0,hec1⟩
  rcases parameter_bounds c hd with ⟨hL,hL1,hcw,hη0,hη1⟩
  have hpositive := mul_nonneg
    (show 0≤1+2*eta c d by linarith) hs0
  have hj : jData (S15 (frameCap-d)) (C16 (frameCap-d))-2*remainder≤
      jData (Real.sin (frameCap-d)) (Real.cos (frameCap-d)) := by
    dsimp [jData]
    linarith
  have hrem : 0≤remainder := by norm_num [remainder]
  cases c <;> dsimp [taylorDemand,demandData,K] at * <;> nlinarith

theorem taylorSum_nonneg (c : ScalarCase) {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    0≤taylorSum c d := by
  rw [← polynomial_radicalSum]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg ((taylor_rows_nonneg c hd).2 i) (Real.sqrt_nonneg _)

theorem value_positive (c : ScalarCase) {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    0<value c d := by
  have hcert := taylor_scalar_reserve c hd
  have hdem := demand_error c hd
  have hsum := rowSum_error c hd
  have hsn := taylorSum_nonneg c hd
  have hR0 := Real.sqrt_nonneg qCap
  have hR2 : Real.sqrt qCap≤2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num [qCap])
  have hsR := mul_le_mul_of_nonneg_left hsum hR0
  have hsU := mul_le_mul_of_nonneg_right sqrt_qCap_le_radiusUpper hsn
  have herr := mul_le_mul_of_nonneg_right hR2
    (show 0≤10*remainder by norm_num [remainder])
  have hmargin : (24:ℝ)*remainder<(PositiveScalarPolynomials.epsilon:ℝ) := by
    norm_num [remainder,PositiveScalarPolynomials.epsilon]
  unfold value
  linarith

def V (l d : ℝ) : ℝ :=
  K*(Real.cos d-1)-Real.sqrt qCap*
    (Real.sqrt (K^2+l^2-2*K*l*Real.sin d)-Real.sqrt (K^2+l^2))

def J (d : ℝ) : ℝ := -Real.sin d/12-(13/12 : ℝ)*(1-Real.cos d)

def BN (d : ℝ) : ℝ :=
  PositivePrimaryBaselines.secondaryBaseline (Real.sqrt qCap) K
    (PositiveStressCoefficients.lN d) (PositiveStressCoefficients.cN d) (19/50) d

theorem scalar_formulas (d : ℝ) :
    value .PV d=PositiveSplitComparison.familyPBaseline d+V (PositiveStressCoefficients.lP d) d ∧
    value .PL d=PositiveSplitComparison.familyPBaseline d+(103/100 : ℝ)*d ∧
    value .PE d=PositiveSplitComparison.familyPBaseline d+J (frameCap-d)+
      PositiveStressCoefficients.lP d-87/1250 ∧
    value .NV d=BN d+V (PositiveStressCoefficients.lN d) d ∧
    value .NL d=BN d+PositiveStressCoefficients.lambdaN d*d ∧
    value .NE d=BN d+J (frameCap-d)+PositiveStressCoefficients.lN d-87/1250 ∧
    value .NET d=BN d+J (frameCap-d)+PositiveStressCoefficients.lambdaN d*frameCap := by
  repeat' constructor <;>
    simp [value,demandData,rowSum,rowData,Fin.sum_univ_succ,
      PositiveScalarPolynomials.isP,PositiveScalarPolynomials.isV,
      ell,cw,eta,lambda,tilted,jData,V,J,BN,K,
      PositiveSplitComparison.familyPBaseline,PositivePrimaryBaselines.tdBaseline,
      PositivePrimaryBaselines.secondaryBaseline,PositivePrimaryBaselines.zeroNorms,
      PositivePrimaryBaselines.primaryCoefficient,PositiveAngularEnvelope.pairNorm_zero,
      SecondaryEStress.tiltedWeight,PositiveStressCoefficients.k] <;> ring

theorem seven_scalar_bounds {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    0<PositiveSplitComparison.familyPBaseline d+V (PositiveStressCoefficients.lP d) d ∧
    0<PositiveSplitComparison.familyPBaseline d+(103/100 : ℝ)*d ∧
    0<PositiveSplitComparison.familyPBaseline d+J (frameCap-d)+
      PositiveStressCoefficients.lP d-87/1250 ∧
    0<BN d+V (PositiveStressCoefficients.lN d) d ∧
    0<BN d+PositiveStressCoefficients.lambdaN d*d ∧
    0<BN d+J (frameCap-d)+PositiveStressCoefficients.lN d-87/1250 ∧
    0<BN d+J (frameCap-d)+PositiveStressCoefficients.lambdaN d*frameCap := by
  rcases scalar_formulas d with ⟨hPV,hPL,hPE,hNV,hNL,hNE,hNET⟩
  exact ⟨hPV ▸ value_positive .PV hd,hPL ▸ value_positive .PL hd,
    hPE ▸ value_positive .PE hd,hNV ▸ value_positive .NV hd,
    hNL ▸ value_positive .NL hd,hNE ▸ value_positive .NE hd,
    hNET ▸ value_positive .NET hd⟩

end SquaresInCircles.Eight.PositiveScalarTransfer
