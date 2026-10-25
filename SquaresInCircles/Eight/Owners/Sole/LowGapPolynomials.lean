module

public import SquaresInCircles.Eight.Owners.BoundedRadicalPerturbation
public import SquaresInCircles.Eight.Owners.Sole.ScalarPolynomials

/-!
# Eight squares: a polynomial gap on the whole interval for the low sole-E family

Two squarings of positive sides turn the gap of the low sole-EH family into the polynomials
`demand`, `firstSquare` and `certificate` (`certificate_eval`). The radius parameter is the lower
endpoint `qLow`, so the comparison applies at the common radius of the cycle. The three identities
and the coefficient bounds cover the whole interval `[0, 1/5]` (`reserves`).
-/

section
/-!
## Exact data for the twenty-four sole-E endpoint scalars

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
end
end
end

section
/-!
## Whole-interval Taylor error for the sole-E scalars

All comparisons use the same parameter t in the
same coefficient family. Four anchor rows and one optional tilt row
are handled uniformly; the absent fifth row has weight zero. Each
weighted radical loses at most 500 times the Taylor remainder, and
the outside term loses at most 100 times that remainder.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleScalarTaylor
open SoleECoefficients SoleScalarData HighOrderTaylor BoundedRadicalPerturbation
open SoleScalarPolynomials (ScalarCase band atG isDE negativeIndex)

theorem input_bounds {t : ℝ} (ht : t∈Set.Icc 0 frameCap) :
    Real.sin t∈Set.Icc 0 1 ∧ Real.cos t∈Set.Icc 0 (1001/1000) ∧
    S15 t∈Set.Icc 0 1 ∧ C16 t∈Set.Icc 0 (1001/1000) := by
  rcases frame_remainders ht with ⟨hs0,hs1,hc0,hc1⟩
  have hc := (transport_trig ht).1
  have hs := (transport_trig ht).2.2.1
  have hcu := Real.cos_le_one t
  have hsu := Real.sin_le_one t
  have he : remainder≤1/1000 := by norm_num [remainder]
  exact ⟨⟨hs,hsu⟩,⟨by linarith,by linarith⟩,
    ⟨S15_nonneg ht,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem input_errors {t : ℝ} (ht : t∈Set.Icc 0 frameCap) :
    |Real.sin t-S15 t|≤remainder ∧ |Real.cos t-C16 t|≤remainder ∧
    |Real.sin (t/2)-S15 (t/2)|≤remainder := by
  rcases frame_remainders ht with ⟨hs0,hs1,hc0,hc1⟩
  have h1 := ht.1
  have h2 := ht.2
  norm_num [frameCap] at h2
  have hh : t/2∈Set.Icc 0 frameCap :=
    ⟨by linarith,by norm_num [frameCap]; linarith⟩
  rcases frame_remainders hh with ⟨hh0,hh1,_,_⟩
  refine ⟨?_,?_,?_⟩
  · rw [abs_of_nonneg hs0]; exact hs1.le
  · rw [abs_sub_comm,abs_of_nonneg hc0]; exact hc1.le
  · rw [abs_of_nonneg hh0]; exact hh1.le

theorem tilted_bounds {K v sn cs : ℝ}
    (hK : K∈Set.Icc 0 (11/10)) (hv : v∈Set.Icc 0 (7/10))
    (hs : sn∈Set.Icc 0 1) (hc : cs∈Set.Icc 0 (1001/1000)) :
    K*(cs+v*sn)∈Set.Icc 0 2 := by
  have hvs := mul_nonneg hv.1 hs.1
  have hvu := mul_le_mul_of_nonneg_left hs.2 hv.1
  have hinner : cs+v*sn≤1701/1000 := by linarith [hc.2,hv.2]
  have hh := mul_le_mul_of_nonneg_left hinner hK.1
  exact ⟨mul_nonneg hK.1 (add_nonneg hc.1 hvs),by nlinarith [hK.2]⟩

theorem tilted_error {K v t : ℝ} (ht : t∈Set.Icc 0 frameCap)
    (hK : K∈Set.Icc 0 (11/10)) (hv : v∈Set.Icc 0 (7/10)) :
    |K*(Real.cos t+v*Real.sin t)-K*(C16 t+v*S15 t)|≤2*remainder := by
  have he := input_errors ht
  have hKv0 := mul_nonneg hK.1 hv.1
  have hKv1 : K*v≤77/100 := by
    linarith [mul_le_mul hK.2 hv.2 hv.1 (by norm_num : (0:ℝ)≤11/10)]
  have hh := linear_difference
    (show |K|≤11/10 by rw [abs_of_nonneg hK.1]; exact hK.2)
    (show |K*v|≤77/100 by rw [abs_of_nonneg hKv0]; exact hKv1) he.2.1 he.1
  have hid : K*(Real.cos t+v*Real.sin t)-K*(C16 t+v*S15 t)=
      (K*Real.cos t+(K*v)*Real.sin t)-(K*C16 t+(K*v)*S15 t) := by ring
  rw [hid]
  linarith [show 0≤remainder by norm_num [remainder]]

theorem coordinate_errors (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s))
    (i : Fin 4) :
    |firstData s t (Real.sin t) (Real.cos t) i-firstData s t (S15 t) (C16 t) i|≤
        3*remainder ∧
    |secondData s t (Real.sin t) (Real.cos t) i-secondData s t (S15 t) (C16 t) i|≤
        3*remainder := by
  have hd := angle ht
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,hg,hg1,he,he1⟩
  have hn := tilted_error hd ⟨hk.le,hk1.le⟩ ⟨hg,by linarith⟩
  have hr := tilted_error hd (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10))
    (by norm_num : (7/10:ℝ)∈Set.Icc 0 (7/10))
  have hp := tilted_error hd (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10))
    ⟨he,by linarith⟩
  change |nData (band s) t (Real.sin t) (Real.cos t)-
    nData (band s) t (S15 t) (C16 t)|≤2*remainder at hn
  simp only [one_mul] at hr hp
  have hpn : |pData (band s) t (Real.sin t) (Real.cos t)-
      pData (band s) t (S15 t) (C16 t)|≤2*remainder := by
    dsimp only [pData]
    split_ifs
    · norm_num [remainder]
    · exact hp
  change |rData (Real.sin t) (Real.cos t)-rData (S15 t) (C16 t)|≤2*remainder at hr
  have hr0 : 0≤remainder := by norm_num [remainder]
  simp only [firstData,secondData]
  split_ifs <;> fin_cases i <;> refine ⟨?_,?_⟩ <;> (try simp) <;> linarith

theorem nu_bounds (s : ScalarCase) {t sn cs : ℝ}
    (ht : t∈domain (band s)) (hs : sn∈Set.Icc 0 1)
    (hco : cs∈Set.Icc 0 (1001/1000)) :
    nuData s t sn cs∈Set.Icc 0 2 := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,hg,hg1,he,he1⟩
  have hn := tilted_bounds ⟨hk.le,hk1.le⟩ (show g (band s) t∈Set.Icc 0 (7/10)
    from ⟨hg,by linarith⟩) hs hco
  have hr := tilted_bounds (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10))
    (by norm_num : (7/10:ℝ)∈Set.Icc 0 (7/10)) hs hco
  change nData (band s) t sn cs∈Set.Icc 0 2 at hn
  simp only [one_mul] at hr
  change rData sn cs∈Set.Icc 0 2 at hr
  generalize hj : negativeIndex s=j
  fin_cases j <;> simp [nuData,hj] <;> split_ifs <;>
    constructor <;> linarith [hn.1,hn.2,hr.1,hr.2]

theorem nu_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    |nuData s t (Real.sin t) (Real.cos t)-nuData s t (S15 t) (C16 t)|≤3*remainder := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,hg,hg1,he,he1⟩
  have hn := tilted_error (angle ht) ⟨hk.le,hk1.le⟩ ⟨hg,by linarith⟩
  have hr := tilted_error (angle ht) (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10))
    (by norm_num : (7/10:ℝ)∈Set.Icc 0 (7/10))
  change |nData (band s) t (Real.sin t) (Real.cos t)-
    nData (band s) t (S15 t) (C16 t)|≤2*remainder at hn
  simp only [one_mul] at hr
  change |rData (Real.sin t) (Real.cos t)-rData (S15 t) (C16 t)|≤2*remainder at hr
  have hr0 : 0≤remainder := by norm_num [remainder]
  simp only [nuData]
  split_ifs
  · simp only [sub_self,abs_zero]; linarith
  all_goals
    generalize negativeIndex s=j
    fin_cases j <;> (try simp) <;> linarith

theorem weight_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s))
    (i : Fin 5) :
    |weightData s t (Real.sin t) i-weightData s t (S15 t) i|≤3*remainder := by
  have hs := (input_errors (angle ht)).1
  have hk := (coefficient_bounds ht).1
  have hku := (coefficient_bounds ht).2.1
  have hh := constant_product_difference
    (show |k (band s) t|≤11/10 by rw [abs_of_nonneg hk.le]; exact hku.le) hs
  have hr0 : 0≤remainder := by norm_num [remainder]
  dsimp only [weightData]
  split_ifs <;> (try simp only [sub_self,abs_zero]) <;> linarith

theorem square_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s))
    (i : Fin 5) :
    |squareData s t (Real.sin t) (Real.cos t) i-squareData s t (S15 t) (C16 t) i|≤
      100*remainder := by
  rcases input_bounds (angle ht) with ⟨hs,hc,hs',hc'⟩
  have he := input_errors (angle ht)
  have he0 : 0≤remainder := by norm_num [remainder]
  dsimp only [squareData]
  split_ifs with hi hg haux
  · have hb := coordinates_bounds s ht hs hc ⟨i.val,hi⟩
    have hb' := coordinates_bounds s ht hs' hc' ⟨i.val,hi⟩
    have hd := coordinate_errors s ht ⟨i.val,hi⟩
    have ha : |firstData s t (Real.sin t) (Real.cos t) ⟨i.val,hi⟩|≤2 := by
      rw [abs_of_nonneg hb.1]; exact hb.2.1
    have ha' : |firstData s t (S15 t) (C16 t) ⟨i.val,hi⟩|≤2 := by
      rw [abs_of_nonneg hb'.1]; exact hb'.2.1
    have hbb : |secondData s t (Real.sin t) (Real.cos t) ⟨i.val,hi⟩|≤2 := by
      rw [abs_of_nonneg hb.2.2.1]; exact hb.2.2.2
    have hbb' : |secondData s t (S15 t) (C16 t) ⟨i.val,hi⟩|≤2 := by
      rw [abs_of_nonneg hb'.2.2.1]; exact hb'.2.2.2
    unfold squaredData
    split_ifs
    · exact negative_pair_difference he0 ha ha' hbb hbb'
        (by rw [abs_of_nonneg hs'.1]; exact hs'.2) hd.1 hd.2 he.1
    · simpa only [sub_zero] using positive_pair_difference he0 ha ha' hbb hbb' hd.1 hd.2
  · norm_num [remainder]
  · norm_num [remainder]
  · norm_num [remainder]

theorem row_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s))
    (i : Fin 5) :
    |weightData s t (Real.sin t) i*Real.sqrt (squareData s t (Real.sin t) (Real.cos t) i)-
      weightData s t (S15 t) i*Real.sqrt (squareData s t (S15 t) (C16 t) i)|≤
        500*remainder := by
  rcases input_bounds (angle ht) with ⟨hs,hc,hs',hc'⟩
  have hp := SoleScalarPolynomials.square_bounds s i (SoleScalarPolynomials.local_parameter ht)
  rw [(polynomial_rows s i t).1] at hp
  exact weighted_root_difference (square_nonneg s ht hs hc i) hp.1.le hp.2.le
    (by norm_num [remainder]) (by norm_num [remainder])
    (weight_bounds s ht hs i) (weight_bounds s ht hs' i)
    (square_error s ht i) (weight_error s ht i)

theorem rowSum_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    rowSum s t (Real.sin t) (Real.cos t)≤taylorSum s t+2500*remainder := by
  have hh (i : Fin 5) :
      weightData s t (Real.sin t) i*Real.sqrt (squareData s t (Real.sin t) (Real.cos t) i)≤
        weightData s t (S15 t) i*Real.sqrt (squareData s t (S15 t) (C16 t) i)+500*remainder := by
    have hi := (le_abs_self _).trans (row_error s ht i)
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul] at hsum
  simp only [rowSum,taylorSum]
  push_cast at hsum
  linarith

end SquaresInCircles.Eight.SoleScalarTaylor
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SoleLowGapPolynomials
open Polynomial WholeIntervalPolynomial HighOrderTaylor SoleECoefficients

def sinCap : ℚ := PositiveScalarPolynomials.sine.eval (7/10)
def cosLower : ℚ[X] :=
  PositiveScalarPolynomials.cosine-C (1/20922789888000)*X^16
def cosCap : ℚ := cosLower.eval (7/10)
def sinUpper : ℚ[X] :=
  PositiveScalarPolynomials.sine+C (1/1307674368000)*X^15
def l : ℚ[X] := SoleScalarPolynomials.ell .low
def c : ℚ[X] := SoleScalarPolynomials.c .low
def q : ℚ := 19577/5000
def normSquare : ℚ[X] := l^2+c^2-2*l*c*C sinCap
def squareGap : ℚ[X] := 2*l*c*(C sinCap-sinUpper)
def demand : ℚ[X] := C (43/100)+c*(PositiveScalarPolynomials.cosine-C cosCap)
def firstSquare : ℚ[X] := C q*squareGap-demand^2
def certificate : ℚ[X] := firstSquare^2-4*C q*demand^2*normSquare


/-! ### Kernel certificates

The polynomials are mirrored by scaled integer coefficient lists
(`PolynomialCertificates`); the identities and reserves are integer
computations checked by the kernel. -/

section Certificates
open WholeIntervalPolynomial.Certificate

/-- A rational lower reserve from an integer comparison. -/
private theorem lt_of_int {r : ℚ} {n d s m : ℕ} {Z : ℤ} (hr : r=(n:ℚ)/d) (hd : 0<d)
    (hs : 0<s) (h : (n:ℤ)*(s*2^m)<2*d*Z) : r<(Z:ℚ)/(s*2^m/2) := by
  have hd' : (0:ℚ)<d := by exact_mod_cast hd
  have hs' : (0:ℚ)<(s:ℚ)*2^m/2 := by positivity
  rw [hr,div_lt_div_iff₀ hd' hs']
  have h' := (Int.cast_lt (R := ℚ)).mpr h
  push_cast at h'
  linarith

private theorem sinCap_val :
    sinCap=1562944261619609101762963/2426112000000000000000000 := by
  simp only [sinCap,PositiveScalarPolynomials.sine,eval_add,eval_sub,eval_mul,eval_pow,
    eval_C,eval_X]
  norm_num

private theorem cosCap_val :
    cosCap=136076805969657256004599/177914880000000000000000 := by
  simp only [cosCap,cosLower,PositiveScalarPolynomials.cosine,eval_add,eval_sub,eval_mul,
    eval_pow,eval_C,eval_X,eval_one]
  norm_num

private def sineS : Scaled :=
  ((((((Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))).sub
    ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))).add
    ((Scaled.const (1/362880)).mul (Scaled.var.pow 9))).sub
    ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11))).add
    ((Scaled.const (1/6227020800)).mul (Scaled.var.pow 13))).sub
    ((Scaled.const (1/1307674368000)).mul (Scaled.var.pow 15))

private theorem rep_sine : sineS.Rep PositiveScalarPolynomials.sine :=
  ((((((Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 9))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 13))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 15))

private def cosineS : Scaled :=
  (((((((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))).sub
    ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
    ((Scaled.const (1/40320)).mul (Scaled.var.pow 8))).sub
    ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10))).add
    ((Scaled.const (1/479001600)).mul (Scaled.var.pow 12))).sub
    ((Scaled.const (1/87178291200)).mul (Scaled.var.pow 14)) |>.add
    ((Scaled.const (1/20922789888000)).mul (Scaled.var.pow 16))

private theorem rep_cosine : cosineS.Rep PositiveScalarPolynomials.cosine :=
  ((((((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 12))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 14))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 16)))

private def sinUpperS : Scaled :=
  sineS.add ((Scaled.const (1/1307674368000)).mul (Scaled.var.pow 15))

private theorem rep_sinUpper : sinUpperS.Rep sinUpper :=
  rep_sine.add ((Scaled.rep_const _).mul (Scaled.rep_var.pow 15))

private def lS : Scaled :=
  ((Scaled.const (50521/100000)).add ((Scaled.const (823/1000)).mul Scaled.var)).add
    ((Scaled.const (7/10)).mul (Scaled.var.pow 2))

private theorem rep_l : lS.Rep l :=
  ((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))

private def cS : Scaled :=
  (((Scaled.const (17253/20000)).add ((Scaled.const (11/20)).mul Scaled.var)).add
    ((Scaled.const (3/10)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (3/10)).mul Scaled.var)

private theorem rep_c : cS.Rep c :=
  (((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul Scaled.rep_var)

private def sinCapS : Scaled := Scaled.const (1562944261619609101762963/2426112000000000000000000)

private theorem rep_sinCap : sinCapS.Rep (C sinCap) := by
  rw [sinCap_val]; exact Scaled.rep_const _

private def cosCapS : Scaled := Scaled.const (136076805969657256004599/177914880000000000000000)

private theorem rep_cosCap : cosCapS.Rep (C cosCap) := by
  rw [cosCap_val]; exact Scaled.rep_const _

private def normSquareS : Scaled :=
  ((lS.pow 2).add (cS.pow 2)).sub ((((Scaled.ofNat 2).mul lS).mul cS).mul sinCapS)

private theorem rep_normSquare : normSquareS.Rep normSquare :=
  ((rep_l.pow 2).add (rep_c.pow 2)).sub ((((Scaled.rep_ofNat 2).mul rep_l).mul rep_c).mul rep_sinCap)

private def squareGapS : Scaled := (((Scaled.ofNat 2).mul lS).mul cS).mul (sinCapS.sub sinUpperS)

private theorem rep_squareGap : squareGapS.Rep squareGap :=
  (((Scaled.rep_ofNat 2).mul rep_l).mul rep_c).mul (rep_sinCap.sub rep_sinUpper)

private def demandS : Scaled := (Scaled.const (43/100)).add (cS.mul (cosineS.sub cosCapS))

private theorem rep_demand : demandS.Rep demand :=
  (Scaled.rep_const _).add (rep_c.mul (rep_cosine.sub rep_cosCap))

private def firstSquareS : Scaled := ((Scaled.const (19577/5000)).mul squareGapS).sub (demandS.pow 2)

private theorem rep_firstSquare : firstSquareS.Rep firstSquare :=
  ((Scaled.rep_const _).mul rep_squareGap).sub (rep_demand.pow 2)

private def certificateS : Scaled :=
  (firstSquareS.pow 2).sub ((((Scaled.ofNat 4).mul (Scaled.const (19577/5000))).mul
    (demandS.pow 2)).mul normSquareS)

private theorem rep_certificate : certificateS.Rep certificate :=
  (rep_firstSquare.pow 2).sub ((((Scaled.rep_ofNat 4).mul (Scaled.rep_const _)).mul
    (rep_demand.pow 2)).mul rep_normSquare)

/-- The centered polynomials on `[0,1/5]`: `(0+1/5)/2 = (1/5-0)/2 = 1/10`. -/
private theorem rep_centered {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) :
    (a.center 1 10 1 1).Rep (centered 0 (1/5) p) :=
  ha.centered 1 10 1 1 (by norm_num) (by norm_num) (by norm_num)

end Certificates

theorem firstSquare_identity : centered 0 (1/5) firstSquare=
    expansion 36 (centered 0 (1/5) firstSquare) := by
  exact (rep_centered rep_firstSquare).eq_expansion (by decide +kernel) (by decide +kernel)

theorem certificate_identity : centered 0 (1/5) certificate=
    expansion 72 (centered 0 (1/5) certificate) := by
  exact (rep_centered rep_certificate).eq_expansion (by decide +kernel) (by decide +kernel)

theorem firstSquare_reserve : (17/10 : ℚ)<lowerOn 36 0 (1/5) firstSquare := by
  rw [Certificate.lowerOn_eq_of_rep (rep_centered rep_firstSquare) (by decide +kernel)
    (by decide +kernel)]
  exact lt_of_int (n := 17) (d := 10) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem certificate_reserve : (4/25 : ℚ)<lowerOn 72 0 (1/5) certificate := by
  rw [Certificate.lowerOn_eq_of_rep (rep_centered rep_certificate) (by decide +kernel)
    (by decide +kernel)]
  exact lt_of_int (n := 4) (d := 25) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem reserves {t : ℝ} (ht : t∈domain .low) :
    63/100<aeval t demand ∧ 17/10<aeval t firstSquare ∧
      4/25<aeval t certificate := by
  have ht' : t∈Set.Icc ((0:ℚ):ℝ) ((1/5:ℚ):ℝ) := by
    simpa [domain] using ht
  -- `demand - 63/100` has positive Bernstein coefficients of degree `18` on `[0, 1/5]`.
  have h1 : (63/100:ℝ)<aeval t demand := by
    have h0 : (0:ℝ)≤t := by simpa using ht'.1
    have h5 : 0≤1/5-t := sub_nonneg.2 (by simpa using ht'.2)
    have hb (i j : ℕ) : 0≤t^i*(1/5-t)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h5 j)
    simp only [demand,c,SoleScalarPolynomials.c,SoleScalarPolynomials.k,
      PositiveScalarPolynomials.cosine,cosCap_val,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,
      aeval_X,eq_ratCast]
    push_cast
    linarith [hb 18 0,hb 17 1,hb 16 2,hb 15 3,hb 14 4,hb 13 5,hb 12 6,hb 11 7,hb 10 8,hb 9 9,
      hb 8 10,hb 7 11,hb 6 12,hb 5 13,hb 4 14,hb 3 15,hb 2 16,hb 1 17,hb 0 18]
  have h2 := positive_on_interval (by norm_num) firstSquare_identity firstSquare_reserve ht'
  have h3 := positive_on_interval (by norm_num) certificate_identity certificate_reserve ht'
  push_cast at h2 h3
  exact ⟨h1,h2,h3⟩

theorem sinCap_eq : (sinCap:ℝ)=S15 frameCap := by
  norm_num [sinCap,PositiveScalarPolynomials.sine,S15,S13,S11,
    Arithmetic.sin9,Arithmetic.sin7,frameCap]

theorem cosCap_eq : (cosCap:ℝ)=C14 frameCap := by
  norm_num [cosCap,cosLower,PositiveScalarPolynomials.cosine,C14,C12,
    Arithmetic.cos10,Arithmetic.cos8,frameCap]

theorem sinUpper_eval (t : ℝ) : aeval t sinUpper=S13 t := by
  simp only [sinUpper,map_add,map_mul,aeval_C,map_pow,aeval_X,eq_ratCast,
    PositiveScalarPolynomials.sine_eval]
  dsimp only [S15]
  push_cast
  ring

theorem coefficients_eval (t : ℝ) :
    aeval t l=ell .low t ∧ aeval t c=SoleECoefficients.c .low t := by
  have hh := SoleScalarData.polynomial_parameters .low t
  simp only [SoleScalarPolynomials.origin,Rat.cast_zero,sub_zero] at hh
  exact ⟨hh.2.1,hh.2.2.1⟩

theorem normSquare_eval (t : ℝ) : aeval t normSquare=
    (ell .low t)^2+(SoleECoefficients.c .low t)^2-
      2*ell .low t*SoleECoefficients.c .low t*S15 frameCap := by
  simp only [normSquare,map_sub,map_add,map_mul,map_pow,map_ofNat,aeval_C,eq_ratCast,
    (coefficients_eval t).1,(coefficients_eval t).2,sinCap_eq]

theorem squareGap_eval (t : ℝ) : aeval t squareGap=
    2*ell .low t*SoleECoefficients.c .low t*(S15 frameCap-S13 t) := by
  simp only [squareGap,map_sub,map_mul,map_ofNat,aeval_C,eq_ratCast,
    (coefficients_eval t).1,(coefficients_eval t).2,sinCap_eq,sinUpper_eval]

theorem demand_eval (t : ℝ) : aeval t demand=
    43/100+SoleECoefficients.c .low t*(C16 t-C14 frameCap) := by
  simp only [demand,map_add,map_mul,map_sub,aeval_C,eq_ratCast,
    (coefficients_eval t).2,PositiveScalarPolynomials.cosine_eval,cosCap_eq]
  push_cast
  ring

theorem firstSquare_eval (t : ℝ) : aeval t firstSquare=
    qLow*aeval t squareGap-(aeval t demand)^2 := by
  simp [firstSquare,q,qLow]

theorem certificate_eval (t : ℝ) : aeval t certificate=
    (aeval t firstSquare)^2-4*qLow*(aeval t demand)^2*aeval t normSquare := by
  simp only [certificate,map_sub,map_mul,map_pow,map_ofNat,aeval_C,eq_ratCast,q,qLow]
  push_cast
  ring

end SquaresInCircles.Eight.SoleLowGapPolynomials
end
end
end
