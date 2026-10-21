module

public import SquaresInCircles.Eight.TableFree.ScalarRadicalTransfer
public import SquaresInCircles.Eight.TableFree.PositiveSplitComparison

/-!
# Exact and Taylor scalar data, with the radical rows identified

Uncompiled source draft. The seven expressions are written with their
original sine and cosine inputs. Substituting the two Taylor polynomials
gives exactly the rational polynomial builders, including the cancellation
of the AB radical in each V row.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.PositiveScalarData
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
    ⟨hLP0,hLP1,hLN0,hLN1,hc0,hc1,hη0,hη1,hr0,hr1⟩
  norm_num [PositiveStressCoefficients.k] at hLP1 hLN1 hc0
  cases c <;> simp only [ell,cw,eta,PositiveScalarPolynomials.isP,Bool.false_eq_true,
    if_false,if_true] <;> dsimp [K] <;> (repeat' constructor) <;> linarith

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
      PositiveStressCoefficients.lambdaN] <;> ring

theorem polynomial_rows (c : ScalarCase) (i : Fin 5) (d : ℝ) :
    (aeval d (PositiveScalarPolynomials.rows c i).v,
      aeval d (PositiveScalarPolynomials.rows c i).w)=
      rowData c d (HighOrderTaylor.S15 d) (HighOrderTaylor.C16 d) i := by
  rcases polynomial_parameters c d with ⟨hl,hc,hη,hλ⟩
  cases c <;> fin_cases i <;> apply Prod.ext <;>
    simp [PositiveScalarPolynomials.rows,PositiveScalarPolynomials.isP,
      PositiveScalarPolynomials.isV,PositiveScalarPolynomials.constantRow,
      PositiveScalarPolynomials.klRow,PositiveScalarPolynomials.tiltedRow,
      PositiveScalarPolynomials.primaryRow,PositiveScalarPolynomials.HRow,
      PositiveScalarPolynomials.BRow,PositiveScalarPolynomials.DRow,
      PositiveScalarPolynomials.VRow,PositiveScalarPolynomials.dummy,
      PositiveScalarPolynomials.n,PositiveScalarPolynomials.sine_eval,
      PositiveScalarPolynomials.cosine_eval,PositiveScalarPolynomials.k,
      hl,hc,hη,rowData,tilted,K] <;> ring

theorem polynomial_demand (c : ScalarCase) (d : ℝ) :
    aeval d (PositiveScalarPolynomials.demand c)=taylorDemand c d := by
  rcases polynomial_parameters c d with ⟨hl,hc,hη,hλ⟩
  cases c <;>
    simp [PositiveScalarPolynomials.demand,PositiveScalarPolynomials.jCharge,
      PositiveScalarPolynomials.sine_eval,PositiveScalarPolynomials.cosine_eval,
      PositiveScalarPolynomials.k,PositiveScalarPolynomials.h,Polynomial.aeval_comp,
      hl,hc,hη,hλ,taylorDemand,demandData,jData,K,frameCap] <;> ring

theorem polynomial_radicalSum (c : ScalarCase) (d : ℝ) :
    ScalarRadicalTransfer.radicalSum c d=taylorSum c d := by
  apply Finset.sum_congr rfl
  intro i _
  have h := polynomial_rows c i d
  have hv := congrArg Prod.fst h
  have hw := congrArg Prod.snd h
  simp only [hv,hw]

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

end SquaresInCircles.Eight.TableFree.PositiveScalarData
