module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3Coefficients

/-!
# Actual sine/cosine inputs in the five-mass BT3 numerator

Uncompiled scalar-transfer data. The fifth mass is the harmless
unit mass with zero weight on the diagonal-D rows. The broad input
rectangle contains both the actual trigonometric values and the two
alternating Taylor polynomials on the whole frame interval.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Analytic
open Candidate Secondary Polynomial Certificate (Row Endpoint)
open BoundedRadicalPerturbation HighOrderTaylor

def fData (eta s t : ℝ) : ℝ := t+eta*s
def TData (eta s t : ℝ) : ℝ := 1+2*t+(1+2*eta)*s
def vData (r : Row) (e : Endpoint) (k c eta s t : ℝ) : Fin 5→ℝ :=
  ![1+k^2,(fData eta s t)^2+c^2,
    if e=.V then 1+k^2-2*k*s else 1+k^2*t^2,
    1+eta^2,if Certificate.diagonalD r then 0 else 1+c^2]
def alphaData (r : Row) (e : Endpoint) (k c eta s t : ℝ) : Fin 5→ℝ :=
  ![(91+60*k)/109,(20*fData eta s t+21*c)/29,
    if e=.V then (36*(k-s)+77*t)/85 else (91+60*k*t)/109,
    (40+13*eta)/42,if Certificate.diagonalD r then 1 else (21+20*c)/29]
def weightData (r : Row) (e : Endpoint) (c eta s t : ℝ) : Fin 5→ℝ :=
  ![if e=.V then fData eta s t else fData eta s t*t,
    if e=.V then 1 else t,fData eta s t,
    if e=.V then c*s else c*s*t,
    if Certificate.diagonalD r then 0 else if e=.V then fData eta s t else fData eta s t*t]
def AData (r : Row) (e : Endpoint) (k c eta s t : ℝ) : ℝ :=
  (if e=.V then fData eta s t*(2*k+5+t)+c*TData eta s t
   else (fData eta s t*(2*k+5)+c*TData eta s t)*t+fData eta s t*(1+(13/12)*s))-
    if Certificate.diagonalD r then
      (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)*fData eta s t*(if e=.V then 1 else t) else 0
def numeratorData (r : Row) (e : Endpoint) (k c eta s t : ℝ) : ℝ :=
  2*AData r e k c eta s t*(∏i,alphaData r e k c eta s t i)-(Certificate.Rplus:ℝ)*
    ∑i,weightData r e c eta s t i*(vData r e k c eta s t i+(alphaData r e k c eta s t i)^2)*
      ∏j∈Finset.univ.erase i,alphaData r e k c eta s t j

theorem polynomial_identity (r : Row) (e : Endpoint) (z : ℝ) :
    aeval z (Certificate.numerator r e)=
      numeratorData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (S15 z) (C16 z) := by
  simp only [Certificate.numerator,numeratorData,map_sub,map_mul,map_sum,map_prod,
    map_pow,aeval_C,map_ofNat]
  congr 2
  all_goals
    simp [Certificate.A,Certificate.alpha,Certificate.v,Certificate.weight,Certificate.f,
      Certificate.Tstar,Certificate.S,Certificate.Cstar,PositiveScalarPolynomials.sine_eval,
      PositiveScalarPolynomials.cosine_eval,AData,alphaData,vData,weightData,fData,TData,
      Explicit.k,Explicit.c,Explicit.eta]

abbrev epsilon : ℝ := 1/100000000000000000

theorem input_errors {z : ℝ} (hz : z∈Icc 0 frameCap) :
    |Real.sin z-S15 z|≤epsilon ∧ |Real.cos z-C16 z|≤epsilon := by
  have hslo := S15_le_sin hz.1
  have hshi := sin_le_S17 hz.1
  have hclo := C18_le_cos hz.1
  have hchi := cos_le_C16 hz.1
  have hp17 := pow_le_pow_left₀ hz.1 hz.2 17
  have hp18 := pow_le_pow_left₀ hz.1 hz.2 18
  have he17 : frameCap^17/355687428096000<epsilon := by norm_num [frameCap,epsilon]
  have he18 : frameCap^18/6402373705728000<epsilon := by norm_num [frameCap,epsilon]
  dsimp [S17] at hshi
  dsimp [C18] at hclo
  constructor
  · rw [abs_of_nonneg (sub_nonneg.mpr hslo)]
    nlinarith
  · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hchi)]
    nlinarith

theorem factor_bounds {eta s t : ℝ} (he : eta∈Icc (0:ℝ) (9/20))
    (hs : s∈Icc (0:ℝ) (129/200)) (ht : t∈Icc (191/250:ℝ) (1001/1000)) :
    fData eta s t∈Icc (191/250:ℝ) (13/10) ∧ TData eta s t∈Icc (0:ℝ) (9/2) := by
  have hep := mul_le_mul he.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤9/20)
  have he0 := mul_nonneg he.1 hs.1
  dsimp [fData,TData]
  constructor <;> constructor <;> nlinarith [ht.1,ht.2,hs.1,hs.2]

theorem data_bounds (r : Row) (e : Endpoint) {k c eta s t : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hc : c∈Icc (7/10:ℝ) (7/5))
    (he : eta∈Icc (0:ℝ) (9/20))
    (hs : s∈Icc (0:ℝ) (129/200)) (ht : t∈Icc (191/250:ℝ) (1001/1000)) :
    (∀i,alphaData r e k c eta s t i∈Icc (1/2:ℝ) 3) ∧
      (∀i,|vData r e k c eta s t i|≤4) ∧
      (∀i,weightData r e c eta s t i∈Icc (0:ℝ) 2) ∧ |AData r e k c eta s t|≤20 := by
  have hfac := factor_bounds he hs ht
  have hf0 : 0≤fData eta s t := by linarith [hfac.1.1]
  have hc0 : 0≤c := by linarith [hc.1]
  have hk0 : 0≤k := by linarith [hk.1]
  have ht0 : 0≤t := by linarith [ht.1]
  have hk2 := pow_le_pow_left₀ hk0 hk.2 2
  have hc2 := pow_le_pow_left₀ hc0 hc.2 2
  have he2 := pow_le_pow_left₀ he.1 he.2 2
  have hf2 := pow_le_pow_left₀ hf0 hfac.1.2 2
  have ht2 := pow_le_pow_left₀ ht0 ht.2 2
  have hkt := mul_le_mul hk.2 ht.2 ht0 (by norm_num : (0:ℝ)≤751/1000)
  have hktt := mul_le_mul hk2 ht2 (sq_nonneg t) (by norm_num : (0:ℝ)≤(751/1000)^2)
  have hks := mul_le_mul hk.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤751/1000)
  have hft := mul_le_mul hfac.1.2 ht.2 ht0 (by norm_num : (0:ℝ)≤13/10)
  have hcs := mul_le_mul hc.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤7/5)
  have hcst := mul_le_mul hcs ht.2 ht0 (by norm_num : (0:ℝ)≤(7/5)*(129/200))
  have hfkt := mul_le_mul_of_nonneg_left (show 2*k+5+t≤8 by linarith [hk.2,ht.2]) hf0
  have hfk := mul_le_mul_of_nonneg_left (show 2*k+5≤7 by linarith [hk.2]) hf0
  have hcT := mul_le_mul hc.2 hfac.2.2 hfac.2.1 (by norm_num : (0:ℝ)≤7/5)
  have hb : 0≤fData eta s t*(2*k+5)+c*TData eta s t ∧
      fData eta s t*(2*k+5)+c*TData eta s t≤77/5 := by
    constructor
    · positivity
    · nlinarith [hfac.1.2]
  have hbt := mul_le_mul hb.2 ht.2 ht0 (by norm_num : (0:ℝ)≤77/5)
  have hlast := mul_le_mul_of_nonneg_left
    (show 1+(13/12)*s≤17/10 by linarith [hs.2]) hf0
  have hd : 0≤(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c) ∧
      (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)≤7/2 := by
    constructor
    · norm_num [Certificate.Rplus,Certificate.dPlus]; positivity
    · norm_num [Certificate.Rplus,Certificate.dPlus]; nlinarith [hc.2]
  have hdf := mul_le_mul hd.2 hfac.1.2 hf0 (by norm_num : (0:ℝ)≤7/2)
  have hdft := mul_le_mul hdf ht.2 ht0 (by norm_num : (0:ℝ)≤(7/2)*(13/10))
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [alphaData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
      constructor <;> nlinarith [hk.1,hk.2,hc.1,hc.2,he.1,he.2,hs.1,hs.2,ht.1,ht.2,
        hfac.1.1,hfac.1.2]
  · intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [vData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
      apply abs_le.mpr <;> constructor <;>
      nlinarith [sq_nonneg k,sq_nonneg c,sq_nonneg eta,sq_nonneg (fData eta s t),mul_nonneg hk0 hs.1]
  · intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [weightData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
      constructor <;> first | positivity | nlinarith [hfac.1.2,ht.2]
  · have hdiag0 := mul_nonneg hd.1 hf0
    have hdiagT0 := mul_nonneg hdiag0 ht0
    have hV0 : 0≤fData eta s t*(2*k+5+t)+c*TData eta s t := by positivity
    have hF0 : 0≤(fData eta s t*(2*k+5)+c*TData eta s t)*t+
        fData eta s t*(1+(13/12)*s) := by positivity
    cases r <;> cases e <;>
      simp only [AData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,mul_one,sub_zero] <;>
      apply abs_le.mpr <;> constructor <;> nlinarith [hfac.1.2]

theorem add_error {a a' b b' A B : ℝ} (ha : |a-a'|≤A) (hb : |b-b'|≤B) :
    |(a+b)-(a'+b')|≤A+B := by
  rw [show (a+b)-(a'+b')=(a-a')+(b-b') by ring]
  exact (abs_add _ _).trans (add_le_add ha hb)

theorem subtract_error {a a' b b' A B : ℝ} (ha : |a-a'|≤A) (hb : |b-b'|≤B) :
    |(a-b)-(a'-b')|≤A+B := by
  rw [show (a-b)-(a'-b')=(a-a')-(b-b') by ring]
  exact (sub_abs_bound _ _).trans (add_le_add ha hb)

theorem factor_errors {eta s t s' t' ε : ℝ} (he : eta∈Icc (0:ℝ) (9/20))
    (hε : 0≤ε) (hS : |s-s'|≤ε) (hT : |t-t'|≤ε) :
    |fData eta s t-fData eta s' t'|≤2*ε ∧
      |TData eta s t-TData eta s' t'|≤4*ε := by
  have hf := linear_difference (a:=1) (b:=eta) (A:=1) (B:=1)
    (by norm_num) (by rw [abs_of_nonneg he.1]; linarith [he.2]) hT hS
  have hJ := linear_difference (a:=2) (b:=1+2*eta) (A:=2) (B:=2)
    (by norm_num) (by rw [abs_of_nonneg (by linarith [he.1])]; linarith [he.2]) hT hS
  refine ⟨by simpa [fData] using hf,?_⟩
  have hid : TData eta s t-TData eta s' t'=(2*t+(1+2*eta)*s)-(2*t'+(1+2*eta)*s') := by
    dsimp [TData]; ring
  rw [hid]
  exact hJ

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Analytic
