module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Positive.SplitComparison
public import SquaresInCircles.Eight.Owners.Positive.StressCoefficients
public import SquaresInCircles.Eight.Owners.ScalarRadicalTransfer

/-!
# Eight squares: the seven trigonometric scalars are positive

Sine is replaced by a lower bound and cosine by an upper bound. The perturbation bound of the
Euclidean norm pays for the only varying norm row, and the radicand of `V` moves in the favorable
direction (`row_error`, `rowSum_error`, `demand_error`). The total error is at most `24/10¹⁵`,
below the allowance `10⁻¹²` of the polynomials, so the seven scalars are positive
(`value_positive`, `seven_scalar_bounds`).
-/

section
/-!
## Exact and Taylor scalar data, with the radical rows identified

The seven expressions are written with their
original sine and cosine inputs. Substituting the two Taylor polynomials
gives exactly the rational polynomial builders, including the cancellation
of the AB radical in each V row.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.PositiveScalarData
open Polynomial
open PositiveScalarPolynomials (ScalarCase)

def K : ℝ := 863/1000
def ell (c : ScalarCase) (d : ℝ) : ℝ :=
  if PositiveScalarPolynomials.isP c then PositiveStressCoefficients.lP d
  else PositiveStressCoefficients.lN d
def cw (c : ScalarCase) (d : ℝ) : ℝ :=
  if PositiveScalarPolynomials.isP c then K else PositiveStressCoefficients.cN d
def eta (c : ScalarCase) (d : ℝ) : ℝ :=
  if PositiveScalarPolynomials.isP c then PositiveStressCoefficients.etaP d else 19/50
def lambda (c : ScalarCase) (d : ℝ) : ℝ :=
  if PositiveScalarPolynomials.isP c then 103/100 else PositiveStressCoefficients.lambdaN d
def tilted (c : ScalarCase) (d s co : ℝ) : ℝ := K*(co+eta c d*s)

/-- A row stores its radicand and its nonnegative weight. The support mass
is needed only in the polynomial majorant, not in the exact scalar. -/
def rowData (c : ScalarCase) (d s co : ℝ) : Fin 5 → ℝ × ℝ :=
  let L := ell c d
  let Cw := cw c d
  let η := eta c d
  let n := tilted c d s co
  if PositiveScalarPolynomials.isP c then
    if PositiveScalarPolynomials.isV c then
      ![(1+K^2,2),(L^2+n^2,1),(1+η^2,K*s),(K^2+L^2-2*K*L*s,1),(0,0)]
    else ![(1+K^2,2),(K^2+L^2,1),(L^2+n^2,1),(1+η^2,K*s),(0,0)]
  else if PositiveScalarPolynomials.isV c then
    ![(1+n^2,1),(L^2+Cw^2,1),(1+Cw^2,1),(1+η^2,K*s),(K^2+L^2-2*K*L*s,1)]
  else ![(1+n^2,1),(K^2+L^2,1),(L^2+Cw^2,1),(1+Cw^2,1),(1+η^2,K*s)]

def rowSum (c : ScalarCase) (d s co : ℝ) : ℝ :=
  ∑ i : Fin 5,(rowData c d s co i).2*Real.sqrt (rowData c d s co i).1

def jData (s co : ℝ) : ℝ := -s/12-(13/12 : ℝ)*(1-co)

def demandData (c : ScalarCase) (d s co se ce : ℝ) : ℝ :=
  3+2*ell c d+3*cw c d+K*(1+2*co+(1+2*eta c d)*s)+
    match c with
    | .PV | .NV => K*(co-1)
    | .PL | .NL => lambda c d*d
    | .PE | .NE => jData se ce+ell c d-87/1250
    | .NET => jData se ce+lambda c d*frameCap

def value (c : ScalarCase) (d : ℝ) : ℝ :=
  demandData c d (Real.sin d) (Real.cos d)
    (Real.sin (frameCap-d)) (Real.cos (frameCap-d))-
    Real.sqrt qCap*rowSum c d (Real.sin d) (Real.cos d)

def taylorDemand (c : ScalarCase) (d : ℝ) : ℝ :=
  demandData c d (HighOrderTaylor.S15 d) (HighOrderTaylor.C16 d)
    (HighOrderTaylor.S15 (frameCap-d)) (HighOrderTaylor.C16 (frameCap-d))
def taylorSum (c : ScalarCase) (d : ℝ) : ℝ :=
  rowSum c d (HighOrderTaylor.S15 d) (HighOrderTaylor.C16 d)

theorem parameter_bounds (c : ScalarCase) {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    0<ell c d ∧ ell c d≤1 ∧ 0≤cw c d ∧ 0≤eta c d ∧ eta c d≤19/50 := by
  rcases PositiveStressCoefficients.coefficient_bounds hd with
    ⟨hLP0,hLP1,hLN0,hLN1,hc0,-,hη0,hη1,-,-⟩
  have hk : PositiveStressCoefficients.k=863/1000 := rfl
  rw [hk] at hLP1 hLN1 hc0
  have hP : 0<PositiveStressCoefficients.lP d ∧ PositiveStressCoefficients.lP d≤1 ∧ 0≤K ∧
      0≤PositiveStressCoefficients.etaP d ∧ PositiveStressCoefficients.etaP d≤19/50 :=
    ⟨by linarith,by linarith,by norm_num [K],by linarith,by linarith⟩
  have hN : 0<PositiveStressCoefficients.lN d ∧ PositiveStressCoefficients.lN d≤1 ∧
      0≤PositiveStressCoefficients.cN d ∧ 0≤(19/50:ℝ) ∧ (19/50:ℝ)≤19/50 :=
    ⟨by linarith,by linarith,by linarith,by norm_num,le_rfl⟩
  cases c <;> simp only [ell,cw,eta,PositiveScalarPolynomials.isP,Bool.false_eq_true,
    ↓reduceIte] <;> first | exact hP | exact hN

theorem polynomial_parameters (c : ScalarCase) (d : ℝ) :
    aeval d (PositiveScalarPolynomials.l c)=ell c d ∧
    aeval d (PositiveScalarPolynomials.cWeight c)=cw c d ∧
    aeval d (PositiveScalarPolynomials.eta c)=eta c d ∧
    aeval d (PositiveScalarPolynomials.lambda c)=lambda c d := by
  cases c <;>
    simp [PositiveScalarPolynomials.l,PositiveScalarPolynomials.cWeight,
      PositiveScalarPolynomials.eta,PositiveScalarPolynomials.lambda,
      PositiveScalarPolynomials.isP,PositiveScalarPolynomials.k,ell,cw,eta,lambda,K,
      PositiveStressCoefficients.lP,PositiveStressCoefficients.lN,
      PositiveStressCoefficients.cN,PositiveStressCoefficients.etaP,
      PositiveStressCoefficients.lambdaN]

theorem polynomial_rows (c : ScalarCase) (i : Fin 5) (d : ℝ) :
    (aeval d (PositiveScalarPolynomials.rows c i).v,
      aeval d (PositiveScalarPolynomials.rows c i).w)=
      rowData c d (HighOrderTaylor.S15 d) (HighOrderTaylor.C16 d) i := by
  rcases polynomial_parameters c d with ⟨hl,hc,hη,-⟩
  cases c <;> fin_cases i <;>
    simp only [PositiveScalarPolynomials.rows,PositiveScalarPolynomials.isP,
      PositiveScalarPolynomials.isV,Bool.false_eq_true,↓reduceIte,Fin.isValue,Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,
      Matrix.tail_cons,rowData] <;>
    dsimp only [PositiveScalarPolynomials.constantRow,PositiveScalarPolynomials.klRow,
      PositiveScalarPolynomials.tiltedRow,PositiveScalarPolynomials.primaryRow,
      PositiveScalarPolynomials.HRow,PositiveScalarPolynomials.BRow,
      PositiveScalarPolynomials.DRow,PositiveScalarPolynomials.VRow,
      PositiveScalarPolynomials.dummy,PositiveScalarPolynomials.n] <;>
    simp only [map_add,map_sub,map_mul,map_pow,map_one,map_zero,map_ofNat,aeval_C,
      eq_ratCast,hl,hc,hη,PositiveScalarPolynomials.sine_eval,
      PositiveScalarPolynomials.cosine_eval,tilted,Prod.mk.injEq] <;>
    norm_num [PositiveScalarPolynomials.k,K]

theorem polynomial_demand (c : ScalarCase) (d : ℝ) :
    aeval d (PositiveScalarPolynomials.demand c)=taylorDemand c d := by
  rcases polynomial_parameters c d with ⟨hl,hc,hη,hlam⟩
  cases c <;>
    simp [PositiveScalarPolynomials.demand,PositiveScalarPolynomials.jCharge,
      PositiveScalarPolynomials.sine_eval,PositiveScalarPolynomials.cosine_eval,
      PositiveScalarPolynomials.k,PositiveScalarPolynomials.h,Polynomial.aeval_comp,map_ofNat,
      hl,hc,hη,hlam,taylorDemand,demandData,jData,K,frameCap] <;> ring

theorem polynomial_radicalSum (c : ScalarCase) (d : ℝ) :
    ScalarRadicalTransfer.radicalSum c d=taylorSum c d := by
  unfold ScalarRadicalTransfer.radicalSum taylorSum rowSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← polynomial_rows c i d]

theorem taylor_rows_nonneg (c : ScalarCase) {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    (∀ i : Fin 5,0≤aeval d (PositiveScalarPolynomials.rows c i).v) ∧
      (∀ i : Fin 5,0≤aeval d (PositiveScalarPolynomials.rows c i).w) := by
  have hS := HighOrderTaylor.S15_nonneg hd
  have hSup := (HighOrderTaylor.S15_le_sin hd.1).trans_lt (transport_trig hd).2.2.2.1
  have hL := (parameter_bounds c hd).1
  have hK : 0<K := by norm_num [K]
  have hV : 0≤K^2+(ell c d)^2-2*K*ell c d*HighOrderTaylor.S15 d := by
    have h := mul_nonneg (mul_nonneg hK.le hL.le)
      (show 0≤1-HighOrderTaylor.S15 d by linarith)
    nlinarith [sq_nonneg (K-ell c d)]
  constructor <;> intro i
  · rw [show aeval d (PositiveScalarPolynomials.rows c i).v=
        (rowData c d (HighOrderTaylor.S15 d) (HighOrderTaylor.C16 d) i).1 from
        congrArg Prod.fst (polynomial_rows c i d)]
    cases c <;> fin_cases i <;>
      simp [rowData,PositiveScalarPolynomials.isP,PositiveScalarPolynomials.isV] at * <;>
      first | exact hV | positivity
  · rw [show aeval d (PositiveScalarPolynomials.rows c i).w=
        (rowData c d (HighOrderTaylor.S15 d) (HighOrderTaylor.C16 d) i).2 from
        congrArg Prod.snd (polynomial_rows c i d)]
    cases c <;> fin_cases i <;> simp [rowData,PositiveScalarPolynomials.isP,
      PositiveScalarPolynomials.isV,K] <;> positivity

theorem taylor_scalar_reserve (c : ScalarCase) {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    (PositiveScalarPolynomials.epsilon:ℝ)<
      taylorDemand c d-(PositiveScalarPolynomials.radiusUpper:ℝ)*taylorSum c d := by
  have hn := taylor_rows_nonneg c hd
  have h := ScalarRadicalTransfer.radical_model_positive hd hn.1 hn.2
  simpa only [polynomial_demand,polynomial_radicalSum] using h

end SquaresInCircles.Eight.PositiveScalarData
end
end
end

section
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
end
end
end
