module

public import SquaresInCircles.Eight.TableFree.ExceptionalNegativeTPolynomials

/-!
# Real inputs for the exceptional negative-T certificates

Uncompiled source. Both the total primary angle and its remaining
ordinary angle have independent sine/cosine inputs. The coefficient
families and the removed secant angle remain exact throughout the
Taylor substitution.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalNegativeTScalarData
open Polynomial HighOrderTaylor ExceptionalNegativeTScalarModel

def taylorOutside (s : Case) (t : ℝ) : ℝ :=
  outside s t (S15 t) (C16 t) (S15 (angle s.row t)) (C16 (angle s.row t))
def taylorSum (s : Case) (t : ℝ) : ℝ :=
  rowSum s t (S15 t) (C16 t) (S15 (angle s.row t))

theorem coordinates_bounds (s : Case) {t sn cs : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band s.row))
    (hs : sn∈Set.Icc 0 1) (hc : cs∈Set.Icc 0 (1001/1000)) (i : Fin 4) :
    0≤first s t sn cs i ∧ first s t sn cs i≤2 ∧
      0≤second s t sn cs i ∧ second s t sn cs i≤2 := by
  rcases ExceptionalEScalarData.coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc0,hc1,he,he1⟩
  have hp0 := add_nonneg hc.1 (mul_nonneg he hs.1)
  have hp1 := mul_le_mul_of_nonneg_left hs.2 he
  have hkp0 := mul_nonneg hk.le hp0
  have hkp1 := mul_le_mul_of_nonneg_right hk1 hp0
  fin_cases i <;> cases h : s.atG <;> simp [first,second,h] <;>
    repeat' constructor <;> first | assumption | nlinarith [hc.2]

theorem nu_bounds {r : Row} {t : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band r)) (i : Fin 3) :
    nu r t i∈Set.Icc 0 2 := by
  rcases ExceptionalEScalarData.coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  fin_cases i <;> simp [nu] <;> constructor <;> linarith

theorem weight_bounds (s : Case) {t sn : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band s.row)) (hs : sn∈Set.Icc 0 1) (i : Fin 5) :
    weight s t sn i∈Set.Icc 0 2 := by
  have hk := (ExceptionalECoefficients.ranges ht).1
  have hp0 := mul_nonneg (show 0≤ExceptionalECoefficients.k (band s.row) t by linarith [hk.1]) hs.1
  have hp1 := mul_le_mul hk.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤1)
  dsimp [weight]
  split_ifs <;> constructor <;> linarith [hs.1,hs.2]

theorem square_nonneg (s : Case) {t sn cs sd : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band s.row))
    (hs : sn∈Set.Icc 0 1) (hc : cs∈Set.Icc 0 (1001/1000))
    (hd : sd∈Set.Icc 0 1) (i : Fin 5) : 0≤square s t sn cs sd i := by
  dsimp [square]
  split_ifs with hi
  · let j : Fin 4 := ⟨i.val,hi⟩
    have hb := coordinates_bounds s ht hs hc j
    have hp := mul_nonneg (mul_nonneg hb.1 hb.2.2.1) (sub_nonneg.mpr hd.2)
    dsimp [squared]
    split_ifs
    · nlinarith [sq_nonneg (first s t sn cs j-second s t sn cs j)]
    · positivity
  · positivity

theorem polynomial_parameters (s : Case) (t : ℝ) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.k s)=ExceptionalECoefficients.k (band s.row) t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.ell s)=ExceptionalECoefficients.ell (band s.row) t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.c s)=ExceptionalECoefficients.c (band s.row) t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.eta s)=ExceptionalECoefficients.eta (band s.row) t := by
  rcases s with ⟨r,face⟩
  cases r <;> simp [ExceptionalNegativeTPolynomials.k,ExceptionalNegativeTPolynomials.ell,
    ExceptionalNegativeTPolynomials.c,ExceptionalNegativeTPolynomials.eta,
    ExceptionalNegativeTPolynomials.parameter,origin,band,
    ExceptionalECoefficients.k,ExceptionalECoefficients.ell,ExceptionalECoefficients.c,
    ExceptionalECoefficients.eta] <;> (repeat' constructor) <;> ring

theorem polynomial_removed (s : Case) (t : ℝ) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.removed s)=removed s.row t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.angle s)=angle s.row t := by
  simp [ExceptionalNegativeTPolynomials.removed,ExceptionalNegativeTPolynomials.angle,
    ExceptionalNegativeTPolynomials.parameter,removed,angle,apply_ite]

theorem polynomial_trig (s : Case) (t : ℝ) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.sine s)=S15 t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.cosine s)=C16 t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.shortSine s)=S15 (angle s.row t) ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.shortCosine s)=C16 (angle s.row t) := by
  have hp : aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.parameter s)=t := by
    simp [ExceptionalNegativeTPolynomials.parameter]
  simp [ExceptionalNegativeTPolynomials.sine,ExceptionalNegativeTPolynomials.cosine,
    ExceptionalNegativeTPolynomials.shortSine,ExceptionalNegativeTPolynomials.shortCosine,
    Polynomial.aeval_comp,hp,(polynomial_removed s t).2,
    PositiveScalarPolynomials.sine_eval,PositiveScalarPolynomials.cosine_eval]

theorem polynomial_coordinates (s : Case) (t : ℝ) (i : Fin 4) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.first s i)=first s t (S15 t) (C16 t) i ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.second s i)=second s t (S15 t) (C16 t) i := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  rcases polynomial_trig s t with ⟨hs,hco,hd,hcd⟩
  fin_cases i <;> simp [ExceptionalNegativeTPolynomials.first,ExceptionalNegativeTPolynomials.second,
    ExceptionalNegativeTPolynomials.p,first,second,hk,hl,hc,he,hs,hco,apply_ite]

theorem polynomial_nu (s : Case) (t : ℝ) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.nu s)=nu s.row t (index s.row) := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  generalize hj : index s.row=j
  fin_cases j <;> simp [ExceptionalNegativeTPolynomials.nu,nu,hj,hl,hc]

theorem polynomial_rows (s : Case) (t : ℝ) (i : Fin 5) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.rowSquare s i)=
      square s t (S15 t) (C16 t) (S15 (angle s.row t)) i ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.rowWeight s i)=weight s t (S15 t) i := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  rcases polynomial_trig s t with ⟨hs,hco,hd,hcd⟩
  have hv (j : Fin 4) := polynomial_coordinates s t j
  constructor <;> fin_cases i <;>
    simp [ExceptionalNegativeTPolynomials.rowSquare,ExceptionalNegativeTPolynomials.rowWeight,
      ExceptionalNegativeTPolynomials.squaredNorm,square,weight,squared,
      (hv 0).1,(hv 0).2,(hv 1).1,(hv 1).2,(hv 2).1,(hv 2).2,(hv 3).1,(hv 3).2,
      hk,hl,hc,he,hs,hco,hd,apply_ite]

theorem polynomial_outside (s : Case) (t : ℝ) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.outside s)=taylorOutside s t := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  rcases polynomial_trig s t with ⟨hs,hco,hd,hcd⟩
  have hn := polynomial_nu s t
  have hr := (polynomial_removed s t).1
  simp [ExceptionalNegativeTPolynomials.outside,ExceptionalNegativeTPolynomials.correction,
    ExceptionalNegativeTPolynomials.slope,taylorOutside,outside,correction,slope,g,
    hk,hl,hc,he,hs,hco,hd,hcd,hn,hr,apply_ite]

end SquaresInCircles.Eight.TableFree.ExceptionalNegativeTScalarData
