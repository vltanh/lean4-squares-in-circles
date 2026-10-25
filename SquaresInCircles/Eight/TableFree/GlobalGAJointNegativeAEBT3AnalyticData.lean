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
open Candidate Secondary Polynomial
open Certificate (Row Endpoint)
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

private theorem r66_fin5 {P : Fin 5 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) : ∀ i,P i := by
  intro i
  fin_cases i
  exacts [h0,h1,h2,h3,h4]

theorem polynomial_identity (r : Row) (e : Endpoint) (z : ℝ) :
    aeval z (Certificate.numerator r e)=
      numeratorData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (S15 z) (C16 z) := by
  have hS : aeval z Certificate.S=S15 z := PositiveScalarPolynomials.sine_eval z
  have hC : aeval z Certificate.Cstar=C16 z := PositiveScalarPolynomials.cosine_eval z
  have hf : aeval z (Certificate.f r)=fData (Explicit.eta r z) (S15 z) (C16 z) := by
    simp only [Certificate.f,fData,map_add,map_mul,hS,hC,Explicit.eta]
  have hT : aeval z (Certificate.Tstar r)=TData (Explicit.eta r z) (S15 z) (C16 z) := by
    simp only [Certificate.Tstar,TData,map_add,map_mul,map_one,hS,hC,Explicit.eta,aeval_C]
    norm_num
  have hα : ∀ i,aeval z (Certificate.alpha r e i)=
      alphaData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (S15 z) (C16 z) i := by
    apply r66_fin5 <;>
      simp only [Certificate.alpha,alphaData,Matrix.cons_val,apply_ite (aeval z)] <;>
      simp [hf,hS,hC,Explicit.k,Explicit.c,Explicit.eta] <;> ring
  have hv : ∀ i,aeval z (Certificate.v r e i)=
      vData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (S15 z) (C16 z) i := by
    apply r66_fin5 <;>
      simp only [Certificate.v,vData,Matrix.cons_val,apply_ite (aeval z)] <;>
      simp [hf,hS,hC,Explicit.k,Explicit.c,Explicit.eta] <;> ring
  have hw : ∀ i,aeval z (Certificate.weight r e i)=
      weightData r e (Explicit.c r z) (Explicit.eta r z) (S15 z) (C16 z) i := by
    apply r66_fin5 <;>
      simp only [Certificate.weight,weightData,Matrix.cons_val,apply_ite (aeval z)] <;>
      simp [hf,hS,hC,Explicit.k,Explicit.c,Explicit.eta]
  have hA : aeval z (Certificate.A r e)=
      AData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (S15 z) (C16 z) := by
    cases r <;> cases e <;>
      simp [Certificate.A,AData,Certificate.diagonalD,hf,hT,hS,hC,Explicit.k,Explicit.c,
        Explicit.eta,map_ofNat] <;> ring
  simp only [Certificate.numerator,numeratorData,map_sub,map_mul,map_sum,map_prod,map_pow,
    map_add,hα,hv,hw,hA,aeval_C]
  norm_num

abbrev epsilon : ℝ := 1/100000000000000000

theorem input_errors {z : ℝ} (hz : z∈Icc 0 frameCap) :
    |Real.sin z-S15 z|≤epsilon ∧ |Real.cos z-C16 z|≤epsilon := by
  have hslo := S15_le_sin hz.1
  have hshi := sin_le_S17 hz.1
  have hclo := C18_le_cos hz.1
  have hchi := cos_le_C16 hz.1
  have hp17 := pow_le_pow_left₀ hz.1 hz.2 17
  have hp18 := pow_le_pow_left₀ hz.1 hz.2 18
  have he17 : (7/10:ℝ)^17/355687428096000<1/100000000000000000 := by norm_num
  have he18 : (7/10:ℝ)^18/6402373705728000<1/100000000000000000 := by norm_num
  simp only [frameCap] at hp17 hp18
  dsimp only [S17] at hshi
  dsimp only [C18] at hclo
  show _≤1/100000000000000000 ∧ _≤1/100000000000000000
  constructor
  · rw [abs_of_nonneg (sub_nonneg.mpr hslo)]
    linarith
  · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hchi)]
    linarith

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
  have hkt0 := mul_nonneg hk0 ht0
  have hktt := mul_le_mul hk2 ht2 (sq_nonneg t) (by norm_num : (0:ℝ)≤(751/1000)^2)
  have hks := mul_le_mul hk.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤751/1000)
  have hks0 := mul_nonneg hk0 hs.1
  have hft := mul_le_mul hfac.1.2 ht.2 ht0 (by norm_num : (0:ℝ)≤13/10)
  have hft0 := mul_nonneg hf0 ht0
  have hcs := mul_le_mul hc.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤7/5)
  have hcs0 := mul_nonneg hc0 hs.1
  have hcst := mul_le_mul hcs ht.2 ht0 (by norm_num : (0:ℝ)≤(7/5)*(129/200))
  have hcst0 := mul_nonneg hcs0 ht0
  have hfkt := mul_le_mul_of_nonneg_left (show 2*k+5+t≤8 by linarith [hk.2,ht.2]) hf0
  have hfkt0 := mul_nonneg hf0 (show 0≤2*k+5+t by linarith)
  have hfk := mul_le_mul_of_nonneg_left (show 2*k+5≤7 by linarith [hk.2]) hf0
  have hfk0 := mul_nonneg hf0 (show 0≤2*k+5 by linarith)
  have hcT := mul_le_mul hc.2 hfac.2.2 hfac.2.1 (by norm_num : (0:ℝ)≤7/5)
  have hcT0 := mul_nonneg hc0 hfac.2.1
  have hb : 0≤fData eta s t*(2*k+5)+c*TData eta s t ∧
      fData eta s t*(2*k+5)+c*TData eta s t≤77/5 := by
    constructor
    · linarith
    · linarith [hfac.1.2]
  have hbt := mul_le_mul hb.2 ht.2 ht0 (by norm_num : (0:ℝ)≤77/5)
  have hbt0 := mul_nonneg hb.1 ht0
  have hlast := mul_le_mul_of_nonneg_left
    (show 1+(13/12)*s≤17/10 by linarith [hs.2]) hf0
  have hlast0 := mul_nonneg hf0 (show 0≤1+(13/12)*s by linarith [hs.1])
  have hd : 0≤(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c) ∧
      (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)≤7/2 := by
    constructor
    · norm_num [Certificate.Rplus,Certificate.dPlus]; linarith
    · norm_num [Certificate.Rplus,Certificate.dPlus]; linarith [hc.2]
  have hdf := mul_le_mul hd.2 hfac.1.2 hf0 (by norm_num : (0:ℝ)≤7/2)
  have hdf0 := mul_nonneg hd.1 hf0
  have hdft := mul_le_mul hdf ht.2 ht0 (by norm_num : (0:ℝ)≤(7/2)*(13/10))
  have hdft0 := mul_nonneg hdf0 ht0
  have hs0 := hs.1
  have hfu := hfac.1.2
  have hfl := hfac.1.1
  have ab (x : ℝ) (h1 : -4≤x) (h2 : x≤4) : |x|≤4 := abs_le.mpr ⟨h1,h2⟩
  refine ⟨?_,?_,?_,?_⟩
  · apply r66_fin5
    · simp only [alphaData,Matrix.cons_val]
      exact ⟨by linarith only [hk.1],by linarith only [hk.2]⟩
    · simp only [alphaData,Matrix.cons_val]
      exact ⟨by linarith only [hfl,hc.1],by linarith only [hfu,hc.2]⟩
    · simp only [alphaData,Matrix.cons_val]
      split_ifs
      · exact ⟨by linarith only [hk.1,hs.2,ht.1],by linarith only [hk.2,hs0,ht.2]⟩
      · exact ⟨by linarith only [hkt0],by linarith only [hkt]⟩
    · simp only [alphaData,Matrix.cons_val]
      exact ⟨by linarith only [he.1],by linarith only [he.2]⟩
    · simp only [alphaData,Matrix.cons_val]
      split_ifs
      · norm_num
      · exact ⟨by linarith only [hc.1],by linarith only [hc.2]⟩
  · apply r66_fin5
    · simp only [vData,Matrix.cons_val]
      exact ab _ (by linarith only [sq_nonneg k]) (by linarith only [hk2])
    · simp only [vData,Matrix.cons_val]
      exact ab _ (by linarith only [sq_nonneg c,sq_nonneg (fData eta s t)])
        (by linarith only [hc2,hf2])
    · simp only [vData,Matrix.cons_val]
      split_ifs
      · exact ab _ (by linarith only [sq_nonneg k,hks]) (by linarith only [hk2,hks0])
      · exact ab _ (by linarith only [sq_nonneg (k*t),hktt])
          (by nlinarith only [hktt])
    · simp only [vData,Matrix.cons_val]
      exact ab _ (by linarith only [sq_nonneg eta]) (by linarith only [he2])
    · simp only [vData,Matrix.cons_val]
      split_ifs
      · norm_num
      · exact ab _ (by linarith only [sq_nonneg c]) (by linarith only [hc2])
  · apply r66_fin5
    · simp only [weightData,Matrix.cons_val]
      split_ifs
      · exact ⟨hf0,by linarith only [hfu]⟩
      · exact ⟨hft0,by linarith only [hft]⟩
    · simp only [weightData,Matrix.cons_val]
      split_ifs
      · norm_num
      · exact ⟨ht0,by linarith only [ht.2]⟩
    · simp only [weightData,Matrix.cons_val]
      exact ⟨hf0,by linarith only [hfu]⟩
    · simp only [weightData,Matrix.cons_val]
      split_ifs
      · exact ⟨hcs0,by linarith only [hcs]⟩
      · exact ⟨hcst0,by linarith only [hcst]⟩
    · simp only [weightData,Matrix.cons_val]
      split_ifs
      · norm_num
      · exact ⟨hf0,by linarith only [hfu]⟩
      · exact ⟨hft0,by linarith only [hft]⟩
  · simp only [AData]
    generalize (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)=Q at *
    split_ifs <;>
      exact abs_le.mpr ⟨by linarith only [hfkt0,hcT0,hdf,hdft,hbt0,hlast0],
        by linarith only [hfkt,hcT,hdf0,hfu,hbt,hlast,hdft0]⟩

theorem add_error {a a' b b' A B : ℝ} (ha : |a-a'|≤A) (hb : |b-b'|≤B) :
    |(a+b)-(a'+b')|≤A+B := by
  rw [show (a+b)-(a'+b')=(a-a')+(b-b') by ring]
  exact (abs_add_le _ _).trans (add_le_add ha hb)

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
  have hfid : fData eta s t-fData eta s' t'=(1*t+eta*s)-(1*t'+eta*s') := by
    dsimp [fData]; ring
  have hTid : TData eta s t-TData eta s' t'=(2*t+(1+2*eta)*s)-(2*t'+(1+2*eta)*s') := by
    dsimp [TData]; ring
  rw [hfid,hTid]
  constructor <;> linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Analytic
