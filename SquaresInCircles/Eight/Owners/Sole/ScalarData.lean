module

public import SquaresInCircles.Eight.Owners.Sole.ScalarPolynomials

/-!
# Eight squares: exact data for the twenty-four sole-E endpoint scalars

The radius and the axis bound remain explicit
parameters of the outside term. The rational polynomial model is obtained
by substituting the displayed Taylor polynomials, not by changing an
original geometric state. This file contains identities and coefficient
bounds; the strict trigonometric inequalities are proved separately.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleScalarData
open Polynomial SoleECoefficients HighOrderTaylor
open SoleScalarPolynomials (ScalarCase band atG isDE negativeIndex)

def nData (b : Band) (t sn cs : ℝ) : ℝ := k b t*(cs+g b t*sn)
def pData (b : Band) (t sn cs : ℝ) : ℝ :=
  if b=.high then 1 else cs+eta b t*sn
def rData (sn cs : ℝ) : ℝ := cs+(7/10)*sn

def firstData (s : ScalarCase) (t sn cs : ℝ) : Fin 4 → ℝ :=
  let b := band s
  if atG s then ![1,k b t,ell b t,1]
  else if isDE s then ![rData sn cs,k b t,ell b t,1]
  else ![1,k b t,ell b t,pData b t sn cs]

def secondData (s : ScalarCase) (t sn cs : ℝ) : Fin 4 → ℝ :=
  let b := band s
  ![if atG s then nData b t sn cs else k b t,ell b t,c b t,c b t]

def nuData (s : ScalarCase) (t sn cs : ℝ) : ℝ :=
  let b := band s
  if s=.highDEH then 53/50
  else ![if atG s then nData b t sn cs else if isDE s then rData sn cs else k b t,
    ell b t,c b t,c b t] (negativeIndex s)

def outsideData (s : ScalarCase) (R M t sn cs sh : ℝ) : ℝ :=
  let b := band s
  (if atG s then
      3+2*ell b t+3*c b t+k b t*(1+2*cs+(1+2*g b t)*sn)
    else if isDE s then
      3*k b t+2*ell b t+3*c b t+1+cs/2+(1/2-M)*sn+(3/2)*rData sn cs
    else if b=.high then
      3+sn-2*R*sh+3*k b t+2*ell b t+3*c b t
    else
      3*k b t+2*ell b t+3*c b t+1+2*cs+(1+2*eta b t)*sn)+
    nuData s t sn cs*(cs-1)

def squaredData (s : ScalarCase) (t sn cs : ℝ) (i : Fin 4) : ℝ :=
  (firstData s t sn cs i)^2+(secondData s t sn cs i)^2-
    (if i=negativeIndex s then
      2*firstData s t sn cs i*secondData s t sn cs i*sn else 0)

def squareData (s : ScalarCase) (t sn cs : ℝ) (i : Fin 5) : ℝ :=
  if hi : i.val<4 then squaredData s t sn cs ⟨i.val,hi⟩
  else if atG s then 1+(g (band s) t)^2
  else if isDE s=true ∨ band s=.high then 1 else 1+(eta (band s) t)^2

def weightData (s : ScalarCase) (t sn : ℝ) (i : Fin 5) : ℝ :=
  if i.val<4 then 1 else if atG s then k (band s) t*sn
  else if isDE s=true ∨ band s=.high then 0 else sn

def rowSum (s : ScalarCase) (t sn cs : ℝ) : ℝ :=
  ∑i : Fin 5,weightData s t sn i*Real.sqrt (squareData s t sn cs i)

def valueAt (s : ScalarCase) (R M t : ℝ) : ℝ :=
  outsideData s R M t (Real.sin t) (Real.cos t) (Real.sin (t/2))-
    R*rowSum s t (Real.sin t) (Real.cos t)

def value (s : ScalarCase) (t : ℝ) : ℝ :=
  valueAt s (Real.sqrt qTrial) (axisCoordinate qTrial) t

def taylorOutside (s : ScalarCase) (t : ℝ) : ℝ :=
  outsideData s (SoleScalarPolynomials.radiusUpper:ℝ)
    (SoleScalarPolynomials.axisUpper:ℝ) t (S15 t) (C16 t) (S15 (t/2))

def taylorSum (s : ScalarCase) (t : ℝ) : ℝ := rowSum s t (S15 t) (C16 t)

theorem coefficient_bounds {b : Band} {t : ℝ} (ht : t∈domain b) :
    0<k b t ∧ k b t<11/10 ∧ 0<ell b t ∧ ell b t<1 ∧
    0<c b t ∧ c b t≤6/5 ∧ 0≤g b t ∧ g b t≤7/20 ∧
    0≤eta b t ∧ eta b t≤7/20 := by
  have hp := positive ht
  cases b
  · rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
    simp only [SoleECoefficients.g]
    exact ⟨hp.1,by linarith,hp.2.1,by linarith,hp.2.2.1,by linarith,
      by norm_num,by norm_num,hp.2.2.2.2,by linarith⟩
  · rcases middle_bounds ht with ⟨hk0,hk1,hc0,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
    simp only [SoleECoefficients.g]
    exact ⟨hp.1,by linarith,hp.2.1,by linarith,hp.2.2.1,by linarith,
      by norm_num,by norm_num,hp.2.2.2.2,by linarith⟩
  · rcases high_bounds ht with ⟨hk0,hk1,hc,hl0,hl1,hlk,hcl,hg0,hg1⟩
    exact ⟨hp.1,by linarith,hp.2.1,by linarith,hp.2.2.1,by rw [hc]; norm_num,
      hp.2.2.2.1,by linarith,by norm_num [SoleECoefficients.eta],
      by norm_num [SoleECoefficients.eta]⟩

theorem polynomial_parameters (b : Band) (t : ℝ) :
    aeval (t-(SoleScalarPolynomials.origin b:ℝ)) (SoleScalarPolynomials.k b)=k b t ∧
    aeval (t-(SoleScalarPolynomials.origin b:ℝ)) (SoleScalarPolynomials.ell b)=ell b t ∧
    aeval (t-(SoleScalarPolynomials.origin b:ℝ)) (SoleScalarPolynomials.c b)=c b t ∧
    aeval (t-(SoleScalarPolynomials.origin b:ℝ)) (SoleScalarPolynomials.g b)=g b t ∧
    aeval (t-(SoleScalarPolynomials.origin b:ℝ)) (SoleScalarPolynomials.eta b)=eta b t := by
  cases b <;>
    simp [SoleScalarPolynomials.origin,SoleScalarPolynomials.parameter,
      SoleScalarPolynomials.k,SoleScalarPolynomials.ell,SoleScalarPolynomials.c,
      SoleScalarPolynomials.g,SoleScalarPolynomials.eta,SoleECoefficients.k,
      SoleECoefficients.ell,SoleECoefficients.c,SoleECoefficients.g,SoleECoefficients.eta]

theorem polynomial_trig (b : Band) (t : ℝ) :
    aeval (t-(SoleScalarPolynomials.origin b:ℝ)) (SoleScalarPolynomials.sine b)=S15 t ∧
    aeval (t-(SoleScalarPolynomials.origin b:ℝ)) (SoleScalarPolynomials.cosine b)=C16 t ∧
    aeval (t-(SoleScalarPolynomials.origin b:ℝ)) (SoleScalarPolynomials.halfSine b)=S15 (t/2) := by
  have hp : aeval (t-(SoleScalarPolynomials.origin b:ℝ))
      (SoleScalarPolynomials.parameter b)=t := by
    simp [SoleScalarPolynomials.parameter]
  simp [SoleScalarPolynomials.sine,SoleScalarPolynomials.cosine,
    SoleScalarPolynomials.halfSine,Polynomial.aeval_comp,hp,
    PositiveScalarPolynomials.sine_eval,PositiveScalarPolynomials.cosine_eval,
    div_eq_mul_inv,mul_comm]

theorem polynomial_coordinates (s : ScalarCase) (i : Fin 4) (t : ℝ) :
    aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.first s i)=
      firstData s t (S15 t) (C16 t) i ∧
    aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.second s i)=
      secondData s t (S15 t) (C16 t) i := by
  rcases polynomial_parameters (band s) t with ⟨hk,hl,hc,hg,he⟩
  rcases polynomial_trig (band s) t with ⟨hs,hco,hh⟩
  have hn : aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.n (band s))=
      nData (band s) t (S15 t) (C16 t) := by
    simp [SoleScalarPolynomials.n,nData,hk,hg,hs,hco]
  have hp : aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.p (band s))=
      pData (band s) t (S15 t) (C16 t) := by
    simp only [SoleScalarPolynomials.p,pData]
    split_ifs <;> simp [he,hs,hco]
  have hr : aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.r (band s))=
      rData (S15 t) (C16 t) := by
    simp [SoleScalarPolynomials.r,rData,hs,hco]
  simp only [SoleScalarPolynomials.first,SoleScalarPolynomials.second,firstData,secondData]
  split_ifs <;> fin_cases i <;> simp [hk,hl,hc,hn,hp,hr]

theorem polynomial_nu (s : ScalarCase) (t : ℝ) :
    aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.nu s)=
      nuData s t (S15 t) (C16 t) := by
  rcases polynomial_parameters (band s) t with ⟨hk,hl,hc,hg,he⟩
  rcases polynomial_trig (band s) t with ⟨hs,hco,hh⟩
  have hn : aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.n (band s))=
      nData (band s) t (S15 t) (C16 t) := by
    simp [SoleScalarPolynomials.n,nData,hk,hg,hs,hco]
  have hr : aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.r (band s))=
      rData (S15 t) (C16 t) := by
    simp [SoleScalarPolynomials.r,rData,hs,hco]
  simp only [SoleScalarPolynomials.nu,nuData]
  split_ifs
  · simp
  all_goals
    generalize negativeIndex s=j
    fin_cases j <;> simp [hk,hl,hc,hn,hr]

theorem polynomial_rows (s : ScalarCase) (i : Fin 5) (t : ℝ) :
    aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.rowSquare s i)=
      squareData s t (S15 t) (C16 t) i ∧
    aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.rowWeight s i)=
      weightData s t (S15 t) i := by
  rcases polynomial_parameters (band s) t with ⟨hk,hl,hc,hg,he⟩
  rcases polynomial_trig (band s) t with ⟨hs,hco,hh⟩
  have hv (j : Fin 4) := polynomial_coordinates s j t
  constructor
  · simp only [SoleScalarPolynomials.rowSquare,squareData]
    split_ifs with h1 h2 h3
    · simp only [SoleScalarPolynomials.squaredNorm,squaredData]
      split_ifs <;> simp [(hv _).1,(hv _).2,hs,map_ofNat]
    · simp [hg]
    · simp
    · simp [he]
  · simp only [SoleScalarPolynomials.rowWeight,weightData]
    split_ifs <;> simp [hk,hs]

theorem polynomial_outside (s : ScalarCase) (t : ℝ) :
    aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.outside s)=
      taylorOutside s t := by
  rcases polynomial_parameters (band s) t with ⟨hk,hl,hc,hg,he⟩
  rcases polynomial_trig (band s) t with ⟨hs,hco,hh⟩
  have hn := polynomial_nu s t
  have hr : aeval (t-(SoleScalarPolynomials.origin (band s):ℝ)) (SoleScalarPolynomials.r (band s))=
      rData (S15 t) (C16 t) := by
    simp [SoleScalarPolynomials.r,rData,hs,hco]
  simp only [SoleScalarPolynomials.outside,taylorOutside,outsideData]
  split_ifs <;> simp [hk,hl,hc,hg,he,hs,hco,hh,hn,hr,map_ofNat]
  ring

theorem weight_bounds (s : ScalarCase) {t sn : ℝ} (ht : t∈domain (band s))
    (hs : sn∈Set.Icc 0 1) (i : Fin 5) : 0≤weightData s t sn i ∧ weightData s t sn i≤2 := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,hg,hg1,he,he1⟩
  have hp := mul_nonneg hk.le hs.1
  have hu := mul_le_mul_of_nonneg_left hs.2 hk.le
  dsimp [weightData]
  split_ifs <;> constructor <;> nlinarith [hs.1,hs.2]

theorem coordinates_bounds (s : ScalarCase) {t sn cs : ℝ}
    (ht : t∈domain (band s)) (hs : sn∈Set.Icc 0 1)
    (hc : cs∈Set.Icc 0 (1001/1000)) (i : Fin 4) :
    0≤firstData s t sn cs i ∧ firstData s t sn cs i≤2 ∧
    0≤ secondData s t sn cs i ∧ secondData s t sn cs i≤2 := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc0,hc1,hg,hg1,he,he1⟩
  have hgs := mul_nonneg hg hs.1
  have hgu := mul_le_mul_of_nonneg_left hs.2 hg
  have hes := mul_nonneg he hs.1
  have heu := mul_le_mul_of_nonneg_left hs.2 he
  have hn0 : 0≤nData (band s) t sn cs := by
    exact mul_nonneg hk.le (add_nonneg hc.1 hgs)
  have hn1 : nData (band s) t sn cs≤2 := by
    have hh := mul_le_mul_of_nonneg_left
      (show cs+g (band s) t*sn≤1351/1000 by linarith [hc.2]) hk.le
    dsimp [nData]
    nlinarith
  have hp0 : 0≤pData (band s) t sn cs := by
    unfold pData; split_ifs
    · norm_num
    · exact add_nonneg hc.1 hes
  have hp1 : pData (band s) t sn cs≤2 := by
    unfold pData; split_ifs
    · norm_num
    · linarith [hc.2]
  have hr0 : 0≤rData sn cs := add_nonneg hc.1 (mul_nonneg (by norm_num) hs.1)
  have hr1 : rData sn cs≤2 := by dsimp [rData]; linarith [hs.2,hc.2]
  simp only [firstData,secondData]
  split_ifs <;> fin_cases i <;> refine ⟨?_,?_,?_,?_⟩ <;> (try simp) <;>
    linarith only [hk,hk1,hl,hl1,hc0,hc1,hn0,hn1,hp0,hp1,hr0,hr1]

theorem square_nonneg (s : ScalarCase) {t sn cs : ℝ}
    (ht : t∈domain (band s)) (hs : sn∈Set.Icc 0 1)
    (hc : cs∈Set.Icc 0 (1001/1000)) (i : Fin 5) :
    0≤ squareData s t sn cs i := by
  dsimp only [squareData]
  split_ifs with hi hg he
  · have hb := coordinates_bounds s ht hs hc ⟨i.val,hi⟩
    have hp := mul_nonneg (mul_nonneg hb.1 hb.2.2.1) (sub_nonneg.mpr hs.2)
    dsimp only [squaredData]
    split_ifs
    · nlinarith [sq_nonneg (firstData s t sn cs ⟨i.val,hi⟩-secondData s t sn cs ⟨i.val,hi⟩)]
    · rw [sub_zero]
      positivity
  · positivity
  · norm_num
  · positivity

end SquaresInCircles.Eight.SoleScalarData
