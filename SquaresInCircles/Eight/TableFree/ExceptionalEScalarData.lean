module

public import SquaresInCircles.Eight.TableFree.ExceptionalEPolynomials
public import SquaresInCircles.Eight.TableFree.SoleScalarTaylor

/-!
# Real scalar model of the exceptional endpoint polynomials

Uncompiled source. The common negative H coefficient is 1.06; the
other three coefficients are the actual l,c,c. Only the B alternative
is needed in either low interval. The radius appears solely in the
support term, so the final transfer retains the original common radius.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalEScalarData
open Polynomial ExceptionalECoefficients HighOrderTaylor
open ExceptionalEPolynomials (ScalarCase band negativeIndex)

def firstData (b : Band) (t sn cs : ℝ) : Fin 4 → ℝ := ![cs+eta b t*sn,k b t,ell b t,1]
def secondData (b : Band) (t : ℝ) : Fin 4 → ℝ := ![k b t,ell b t,c b t,c b t]
def nuData (b : Band) (t : ℝ) : Fin 4 → ℝ := ![53/50,ell b t,c b t,c b t]

def outsideData (s : ScalarCase) (t sn cs : ℝ) : ℝ :=
  3*k (band s) t+2*ell (band s) t+3*c (band s) t+1+2*cs+
    (1+2*eta (band s) t)*sn+nuData (band s) t (negativeIndex s)*(cs-1)

def squaredData (s : ScalarCase) (t sn cs : ℝ) (i : Fin 4) : ℝ :=
  (firstData (band s) t sn cs i)^2+(secondData (band s) t i)^2-
    (if i=negativeIndex s then 2*firstData (band s) t sn cs i*secondData (band s) t i*sn else 0)

def squareData (s : ScalarCase) (t sn cs : ℝ) (i : Fin 5) : ℝ :=
  if hi : i.val<4 then squaredData s t sn cs ⟨i.val,hi⟩ else 1+(eta (band s) t)^2

def weightData (sn : ℝ) (i : Fin 5) : ℝ := if i.val<4 then 1 else sn
def rowSum (s : ScalarCase) (t sn cs : ℝ) : ℝ :=
  ∑i : Fin 5,weightData sn i*Real.sqrt (squareData s t sn cs i)
def valueAt (s : ScalarCase) (R t : ℝ) : ℝ :=
  outsideData s t (Real.sin t) (Real.cos t)-R*rowSum s t (Real.sin t) (Real.cos t)
def taylorOutside (s : ScalarCase) (t : ℝ) : ℝ := outsideData s t (S15 t) (C16 t)
def taylorSum (s : ScalarCase) (t : ℝ) : ℝ := rowSum s t (S15 t) (C16 t)

def charge (R : ℝ) (b : Band) (t : ℝ) (i : Fin 4) : ℝ :=
  SingleAngleConcavity.Vnu R (firstData b t (Real.sin t) (Real.cos t) i)
    (secondData b t i) (nuData b t i) t

theorem coefficient_bounds {b : Band} {t : ℝ} (ht : t∈domain b) :
    0<k b t ∧ k b t≤1 ∧ 0<ell b t ∧ ell b t<1 ∧
      0<c b t ∧ c b t<6/5 ∧ 0≤eta b t ∧ eta b t≤7/20 := by
  rcases ranges ht with ⟨hk,hl,hl1,hc,hc1,he⟩
  exact ⟨by linarith [hk.1],hk.2,hl,hl1,hc,by linarith,by linarith [he.1],by linarith [he.2]⟩

theorem nu_bounds {b : Band} {t : ℝ} (ht : t∈domain b) (i : Fin 4) :
    nuData b t i∈Set.Icc 0 2 := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  fin_cases i <;> simp [nuData] <;> constructor <;> linarith

theorem coordinates_bounds {b : Band} {t sn cs : ℝ}
    (ht : t∈domain b) (hs : sn∈Set.Icc 0 1) (hco : cs∈Set.Icc 0 (1001/1000)) (i : Fin 4) :
    0≤firstData b t sn cs i ∧ firstData b t sn cs i≤2 ∧
      0≤secondData b t i ∧ secondData b t i≤2 := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  have hp0 := add_nonneg hco.1 (mul_nonneg he hs.1)
  have hp1 := mul_le_mul_of_nonneg_left hs.2 he
  fin_cases i <;> simp [firstData,secondData] <;> repeat' constructor <;>
    first | assumption | nlinarith [hco.2]

theorem weight_bounds {sn : ℝ} (hs : sn∈Set.Icc 0 1) (i : Fin 5) :
    0≤weightData sn i ∧ weightData sn i≤2 := by
  dsimp [weightData]
  split_ifs <;> constructor <;> linarith [hs.1,hs.2]

theorem square_nonneg (s : ScalarCase) {t sn cs : ℝ}
    (ht : t∈domain (band s)) (hs : sn∈Set.Icc 0 1)
    (hco : cs∈Set.Icc 0 (1001/1000)) (i : Fin 5) : 0≤squareData s t sn cs i := by
  dsimp [squareData]
  split_ifs with hi
  · let j : Fin 4 := ⟨i.val,hi⟩
    have hb := coordinates_bounds ht hs hco j
    have hp := mul_nonneg (mul_nonneg hb.1 hb.2.2.1) (sub_nonneg.mpr hs.2)
    dsimp [squaredData]
    split_ifs
    · nlinarith [sq_nonneg (firstData (band s) t sn cs j-secondData (band s) t j)]
    · positivity
  · positivity

theorem polynomial_parameters (s : ScalarCase) (t : ℝ) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.k s)=k (band s) t ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.ell s)=ell (band s) t ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.c s)=c (band s) t ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.eta s)=eta (band s) t := by
  cases s <;> simp [ExceptionalEPolynomials.k,ExceptionalEPolynomials.ell,
    ExceptionalEPolynomials.c,ExceptionalEPolynomials.eta,ExceptionalEPolynomials.parameter,
    ExceptionalEPolynomials.origin,band,k,ell,c,eta] <;> (repeat' constructor) <;> ring

theorem polynomial_trig (s : ScalarCase) (t : ℝ) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.sine s)=S15 t ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.cosine s)=C16 t := by
  have hp : aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.parameter s)=t := by
    simp [ExceptionalEPolynomials.parameter]
  simp [ExceptionalEPolynomials.sine,ExceptionalEPolynomials.cosine,Polynomial.aeval_comp,hp,
    PositiveScalarPolynomials.sine_eval,PositiveScalarPolynomials.cosine_eval]

theorem polynomial_coordinates (s : ScalarCase) (t : ℝ) (i : Fin 4) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.first s i)=
      firstData (band s) t (S15 t) (C16 t) i ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.second s i)=
      secondData (band s) t i := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  rcases polynomial_trig s t with ⟨hs,hco⟩
  fin_cases i <;> simp [ExceptionalEPolynomials.first,ExceptionalEPolynomials.second,
    ExceptionalEPolynomials.p,firstData,secondData,hk,hl,hc,he,hs,hco]

theorem polynomial_nu (s : ScalarCase) (t : ℝ) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.nu s)=
      nuData (band s) t (negativeIndex s) := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  generalize hj : negativeIndex s=j
  fin_cases j <;> simp [ExceptionalEPolynomials.nu,nuData,hj,hl,hc]

theorem polynomial_rows (s : ScalarCase) (t : ℝ) (i : Fin 5) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.rowSquare s i)=
      squareData s t (S15 t) (C16 t) i ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.rowWeight s i)=
      weightData (S15 t) i := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  rcases polynomial_trig s t with ⟨hs,hco⟩
  have hv (j : Fin 4) := polynomial_coordinates s t j
  constructor <;> fin_cases i <;>
    simp [ExceptionalEPolynomials.rowSquare,ExceptionalEPolynomials.rowWeight,
      ExceptionalEPolynomials.squaredNorm,squareData,weightData,squaredData,
      (hv 0).1,(hv 0).2,(hv 1).1,(hv 1).2,(hv 2).1,(hv 2).2,(hv 3).1,(hv 3).2,
      hk,hl,hc,he,hs,hco,apply_ite]

theorem polynomial_outside (s : ScalarCase) (t : ℝ) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.outside s)=
      taylorOutside s t := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  rcases polynomial_trig s t with ⟨hs,hco⟩
  have hn := polynomial_nu s t
  simp [ExceptionalEPolynomials.outside,taylorOutside,outsideData,hk,hl,hc,he,hs,hco,hn]

theorem value_eq_endpoint_charge (s : ScalarCase) (R t : ℝ) :
    valueAt s R t=ExceptionalContactSupport.atE R (k (band s) t) (ell (band s) t)
      (c (band s) t) (eta (band s) t) t+charge R (band s) t (negativeIndex s) := by
  cases s <;> first
    | (simp [valueAt,outsideData,rowSum,squareData,squaredData,weightData,firstData,secondData,
        nuData,band,negativeIndex,charge,SingleAngleConcavity.Vnu,ExceptionalContactSupport.atE,
        ExceptionalContactSupport.contactScalar,ExceptionalContactStress.tilt,
        PositiveAngularEnvelope.pairNorm,Real.sin_neg,Fin.sum_univ_succ]; ring)
    | (rename_i i; fin_cases i <;>
        simp [valueAt,outsideData,rowSum,squareData,squaredData,weightData,firstData,secondData,
          nuData,band,negativeIndex,charge,SingleAngleConcavity.Vnu,ExceptionalContactSupport.atE,
          ExceptionalContactSupport.contactScalar,ExceptionalContactStress.tilt,
          PositiveAngularEnvelope.pairNorm,Real.sin_neg,Fin.sum_univ_succ] <;> ring)

end SquaresInCircles.Eight.TableFree.ExceptionalEScalarData
