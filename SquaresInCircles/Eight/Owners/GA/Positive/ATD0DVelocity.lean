module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.GA.HybridConcentration
public import SquaresInCircles.Eight.Owners.GA.ChargedPairs
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveASupport

/-!
# Eight squares: the charged D velocity for the positive-A low-angle stress

An identity with positive coefficients proves the cancellation bound on its whole signed interval
(`dVelocity_sine_lower`); both D angles stay in the bound.
-/

section
/-!
## The fixed low-angle positive-A stress

These are the four fixed coefficients in that proof.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.PositiveATD0

abbrev lowK : ℝ := 39/50
abbrev lowL : ℝ := 63/50
abbrev lowC : ℝ := 9/5
abbrev charge : ℝ := 103/100

end SquaresInCircles.Eight.GlobalGA.PositiveATD0
end
end
end

section
/-!
## The three charged low-angle circle blocks

Separate concavity reduces the two signed errors to the four intrinsic corners
(`charged_pair_minorant`). The radicals are enclosed by rational bounds (`fixed_norm_zero`,
`fixed_norm_positive`, `fixed_norm_negative`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveATD0
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity ActualOrdinaryBlocks

def chargedMixed (p q P N : ℝ) : ℝ :=
  mixedBlock R p q P N+charge*(P-N)

def chargedPair (p q a b : ℝ) : ℝ :=
  p*psi a+q*psi b-R*(pairNorm p q (a+b)-pairNorm p q 0)+charge*(a+b)

@[simp] theorem chargedMixed_zero (p q : ℝ) : chargedMixed p q 0 0=0 := by
  simp [chargedMixed,mixedBlock]

theorem chargedMixed_concave_P {p q N : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hN : N∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => chargedMixed p q P N) := by
  apply concave_of_deriv2
    (f' := fun P => mixedPDerivative R p q P N+charge)
    (f'' := fun P => curvature R p q (P-N)-p*PositiveAngularEnvelope.phi P)
  · intro P hP
    have h := (mixedP_hasDerivAt (R := R) hp (hp.trans_le hpq) hP hN).fun_add
      (((hasDerivAt_id P).sub_const N).const_mul charge)
    convert h using 1
    · funext x
      simp only [chargedMixed,id]
    · ring
  · intro P hP
    exact (mixedPDerivative_hasDerivAt hp (hp.trans_le hpq) hP hN).add_const charge
  · intro P hP
    exact (mixedP_second_lt (Real.sqrt_nonneg _) (by rw [radius_sq])
      hp hpq hqp hP hN).le.trans (by nlinarith)

theorem chargedMixed_concave_N {p q P : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hP : P∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (chargedMixed p q P) := by
  apply concave_of_deriv2
    (f' := fun N => mixedNDerivative R p q P N-charge)
    (f'' := fun N => curvature R p q (P-N)-q*Real.cos N)
  · intro N hN
    have h := (mixedN_hasDerivAt (R := R) hp (hp.trans_le hpq) hP hN).fun_add
      (((hasDerivAt_const N P).sub (hasDerivAt_id N)).const_mul charge)
    convert h using 1
    · funext x
      simp only [chargedMixed,id,Pi.sub_apply]
    · ring
  · intro N hN
    exact (mixedNDerivative_hasDerivAt hp (hp.trans_le hpq) hP hN).sub_const charge
  · intro N hN
    exact (mixedN_second_lt (Real.sqrt_nonneg _) (by rw [radius_sq])
      hp hpq hqp hP hN).le.trans (by nlinarith [hp.trans_le hpq])

theorem charged_pair_minorant {p q a b : ℝ} (hp : 0≤p) (hpq : p≤q)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    chargedMixed p q (positivePart a+positivePart b) (negativePart a+negativePart b)≤
      chargedPair p q a b := by
  let B : Block := ⟨p,q,a,b⟩
  have hm := B.minorant R
    (by simpa [B,Block.p,min_eq_left hpq] using hp) hP hN
  have he : positivePart a+positivePart b-(negativePart a+negativePart b)=a+b := by
    linarith [positive_sub_negative a,positive_sub_negative b]
  simp only [B,Block.p,Block.q,Block.P,Block.N,Block.increment,
    min_eq_left hpq,max_eq_right hpq] at hm
  dsimp [chargedMixed,chargedPair]
  rw [he]
  linarith

/-- The zero corner is exact; the other three corners have a strict reserve. -/
theorem charged_rectangle_nonneg {p q P N : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap)
    (h10 : 0≤chargedMixed p q frameCap 0)
    (h01 : 0≤chargedMixed p q 0 frameCap)
    (h11 : 0≤chargedMixed p q frameCap frameCap) :
    0≤chargedMixed p q P N := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have h0 := (chargedMixed_concave_N hp hpq hqp hz).min_le_of_mem_Icc hz hh hN
  have h1 := (chargedMixed_concave_N hp hpq hqp hh).min_le_of_mem_Icc hz hh hN
  have h2 := (chargedMixed_concave_P hp hpq hqp hN).min_le_of_mem_Icc hz hh hP
  have h00 : 0≤chargedMixed p q 0 0 := by simp
  exact (le_min ((le_min h00 h01).trans h0) ((le_min h10 h11).trans h1)).trans h2

def coefficientP : Fin 3→ℝ := ![lowK,lowK,lowL]
def coefficientQ : Fin 3→ℝ := ![lowL,1,lowC]
def normZeroLower : Fin 3→ℝ := ![1481890/1000000,1268227/1000000,2197180/1000000]
def normZeroUpper : Fin 3→ℝ := ![1481891/1000000,1268228/1000000,2197181/1000000]
def normPositiveUpper : Fin 3→ℝ := ![1860719/1000000,1616596/1000000,2783842/1000000]
def normNegativeUpper : Fin 3→ℝ := ![964223/1000000,776802/1000000,1380373/1000000]

theorem coefficient_ranges (i : Fin 3) :
    0<coefficientP i ∧ coefficientP i≤coefficientQ i ∧ coefficientQ i≤2*coefficientP i := by
  fin_cases i <;> norm_num [coefficientP,coefficientQ,lowK,lowL,lowC]

theorem fixed_norm_zero (i : Fin 3) :
    normZeroLower i<pairNorm (coefficientP i) (coefficientQ i) 0 ∧
      pairNorm (coefficientP i) (coefficientQ i) 0<normZeroUpper i := by
  rw [pairNorm_zero]
  fin_cases i <;>
    exact ⟨(Real.lt_sqrt (by norm_num [normZeroLower])).mpr
        (by norm_num [coefficientP,coefficientQ,normZeroLower,lowK,lowL,lowC]),
      (Real.sqrt_lt' (by norm_num [normZeroUpper])).mpr
        (by norm_num [coefficientP,coefficientQ,normZeroUpper,lowK,lowL,lowC])⟩

theorem fixed_norm_positive (i : Fin 3) :
    pairNorm (coefficientP i) (coefficientQ i) frameCap<normPositiveUpper i := by
  have ht := cap_trig.2.1
  norm_num [Arithmetic.sin9,Arithmetic.sin7,frameCap] at ht
  unfold pairNorm
  fin_cases i <;>
    refine (Real.sqrt_lt' (by norm_num [normPositiveUpper])).mpr ?_ <;>
    norm_num [coefficientP,coefficientQ,normPositiveUpper,lowK,lowL,lowC,frameCap] <;>
    linarith

theorem fixed_norm_negative (i : Fin 3) :
    pairNorm (coefficientP i) (coefficientQ i) (-frameCap)<normNegativeUpper i := by
  have hh := coefficient_ranges i
  have hs := pairNorm_sq hh.1 (hh.1.trans_le hh.2.1)
    (t:= -frameCap) (by norm_num [frameCap])
  have hp := pairNorm_pos hh.1 (hh.1.trans_le hh.2.1)
    (t:= -frameCap) (by norm_num [frameCap])
  have ht := cap_trig.1
  fin_cases i <;>
    norm_num [coefficientP,coefficientQ,normNegativeUpper,lowK,lowL,lowC,
      pairEnergy,pairProduct,Real.sin_neg,Arithmetic.sin7,frameCap] at hs hp ht ⊢ <;> nlinarith

theorem fixed_corners (i : Fin 3) :
    (3/40:ℝ)<chargedMixed (coefficientP i) (coefficientQ i) frameCap 0 ∧
    (7/1000:ℝ)<chargedMixed (coefficientP i) (coefficientQ i) 0 frameCap ∧
    (11/500:ℝ)<chargedMixed (coefficientP i) (coefficientQ i) frameCap frameCap := by
  have hn0 := radius_norm_lower
    (show 0<normZeroLower i by fin_cases i <;> norm_num [normZeroLower]) (fixed_norm_zero i).1
  have hnp := radius_norm_upper
    (show 0<normPositiveUpper i by fin_cases i <;> norm_num [normPositiveUpper]) (fixed_norm_positive i)
  have hnn := radius_norm_upper
    (show 0<normNegativeUpper i by fin_cases i <;> norm_num [normNegativeUpper]) (fixed_norm_negative i)
  have hs := cap_trig.1
  have hc := cap_trig.2.2.1
  fin_cases i <;>
    norm_num [coefficientP,coefficientQ,normZeroLower,normPositiveUpper,normNegativeUpper,
      Arithmetic.sin7,frameCap,lowK,lowL,lowC] at hn0 hnp hnn hs hc ⊢ <;>
    refine ⟨?_,?_,?_⟩ <;>
    norm_num [chargedMixed,mixedBlock,PositiveAngularEnvelope.phi,charge,coefficientP,coefficientQ,
      lowK,lowL,lowC,frameCap] <;> linarith

theorem fixed_pair_nonneg (i : Fin 3) {a b : ℝ}
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    0≤chargedPair (coefficientP i) (coefficientQ i) a b := by
  have hr := coefficient_ranges i
  have hc := fixed_corners i
  have hh := charged_rectangle_nonneg hr.1 hr.2.1 hr.2.2
    ⟨add_nonneg (positivePart_nonneg _) (positivePart_nonneg _),hP⟩
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hN⟩
    (by linarith [hc.1]) (by linarith [hc.2.1]) (by linarith [hc.2.2])
  exact hh.trans (charged_pair_minorant hr.1.le hr.2.1 hP hN)

def pairIncrement (p q a b : ℝ) (P : SignedPoint) : ℝ :=
  p*(edgeWidth a-1)+q*(edgeWidth b-1)-
    (pairF p q a b*P.a+pairG p q a b*P.y)+
    fullSupport q p+charge*(a+b)

theorem actual_pair_lower {r p q a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (ha : |a|≤frameCap) (hb : |b|≤frameCap) :
    chargedPair p q a b≤pairIncrement p q a b P := by
  have hh := Secondary.actual_pair_lower hy hc hr ha hb (p:=p) (q:=q)
  dsimp [Secondary.chargedPair,Secondary.pairIncrement,chargedPair,pairIncrement] at *
  linarith

theorem actual_fixed_pair_nonneg (i : Fin 3) {r a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    0≤pairIncrement (coefficientP i) (coefficientQ i) a b P := by
  have he := pair_error_bounds hP hN
  exact (fixed_pair_nonneg i hP hN).trans (actual_pair_lower hy hc hr he.1 he.2.1)

def lowBaseline : ℝ := lowK+2*lowL+2*lowC+2-
  fullSupport 1 lowK-fullSupport lowL lowK-fullSupport lowC lowL-(1+lowC)*GlobalGA.Secondary.diagonal

theorem low_baseline_reserve : (13/400:ℝ)<lowBaseline := by
  have hG := radius_norm_upper (by norm_num : (0:ℝ)<1481891/1000000) (fixed_norm_zero 0).2
  have hH := radius_norm_upper (by norm_num : (0:ℝ)<1268228/1000000) (fixed_norm_zero 1).2
  have hB := radius_norm_upper (by norm_num : (0:ℝ)<2197181/1000000) (fixed_norm_zero 2).2
  have hd := diagonal_bounds.2
  rw [lowBaseline,fullSupport_pair lowK 1,fullSupport_pair lowK lowL,fullSupport_pair lowL lowC]
  norm_num [coefficientP,coefficientQ,normZeroUpper,lowK,lowL,lowC] at hG hH hB ⊢
  linarith

theorem low_A_charge_lower {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    -a^2/4-(183/200)*a≤TwoPositive.ASupport.charge a := by
  rw [TwoPositive.ASupport.charge_low ha.2]
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=a)
  have hsin := Real.sin_le ha.1
  have hm := mul_le_mul_of_nonneg_left hsin
    (show 0≤axial-1/2 by linarith [axial_bounds.1])
  have hax := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2]) ha.1
  dsimp [TwoPositive.ASupport.axialCharge]
  nlinarith

/-- The final one-variable reserve is the right-endpoint value `49/15000`. -/
theorem low_scalar_positive {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    (49/15000:ℝ)<lowBaseline+charge*a+lowL*TwoPositive.ASupport.charge a := by
  have hj := mul_le_mul_of_nonneg_left (low_A_charge_lower ha)
    (show 0≤lowL by norm_num [lowL])
  have ha2 := pow_le_pow_left₀ ha.1 ha.2 2
  have hbase := low_baseline_reserve
  dsimp [lowL,charge] at *
  nlinarith [ha.2]

end SquaresInCircles.Eight.GlobalGA.PositiveATD0
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveATD0
open Secondary PositiveAngularEnvelope PairNormCalculus

def dVelocity (s : ℝ) : ℝ := R*normD1 1 lowC s
def dCancellation (s : ℝ) : ℝ := dVelocity s-Real.sin (frameCap-s)
def dCancellationD (s : ℝ) : ℝ :=
  R*normD2 1 lowC s+Real.cos (frameCap-s)
def dCancellationDD (s : ℝ) : ℝ :=
  R*normD3 1 lowC s+Real.sin (frameCap-s)

theorem dNorm_sq {s : ℝ} (hs : |s|≤frameCap) :
    (pairNorm 1 lowC s)^2=106/25+(18/5)*Real.sin s := by
  rw [pairNorm_sq (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC]) hs]
  simp only [pairEnergy,pairProduct,lowC]
  ring

theorem dNorm_zero_upper : pairNorm 1 lowC 0<(103/50:ℝ) := by
  have h := dNorm_sq (s:=0) (by norm_num [frameCap])
  rw [Real.sin_zero,mul_zero,add_zero] at h
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h]; norm_num)

theorem dNorm_cap_upper : pairNorm 1 lowC frameCap<(1281/500:ℝ) := by
  have h := dNorm_sq (s:=frameCap) (by norm_num [frameCap])
  have ht := (transport_trig (x:=frameCap) (by norm_num [frameCap])).2.2.2.1
  nlinarith [Real.sqrt_nonneg ((1:ℝ)^2+lowC^2+2*1*lowC*Real.sin frameCap)]

theorem dVelocity_zero_lower : charge+Real.sin frameCap<dVelocity 0 := by
  have hN := pairNorm_pos (p:=1) (q:=lowC) (t:=0)
    (by norm_num) (by norm_num [lowC]) (by norm_num [frameCap])
  have hs := (transport_trig (x:=frameCap) (by norm_num [frameCap])).2.2.2.1
  have hm := mul_le_mul
    (show charge+Real.sin frameCap≤charge+6443/10000 by linarith)
    dNorm_zero_upper.le hN.le (by norm_num [charge])
  have he : dVelocity 0=lowC*R/pairNorm 1 lowC 0 := by
    dsimp only [dVelocity,normD1,pairProduct]
    rw [Real.cos_zero]
    ring
  rw [he,lt_div_iff₀ hN]
  dsimp only [charge,lowC] at hm ⊢
  linarith [radius_bounds.1]

theorem dVelocity_cap_lower : charge<dVelocity frameCap := by
  have hN := pairNorm_pos (p:=1) (q:=lowC) (t:=frameCap)
    (by norm_num) (by norm_num [lowC]) (by norm_num [frameCap])
  obtain ⟨hc,_,_,_,_⟩ := transport_trig (x:=frameCap) (by norm_num [frameCap])
  have hm := mul_le_mul radius_bounds.1.le hc.le
    (by norm_num : (0:ℝ)≤7648/10000) (Real.sqrt_nonneg qCap)
  have hn := mul_lt_mul_of_pos_left dNorm_cap_upper (by norm_num : (0:ℝ)<charge)
  have he : dVelocity frameCap=lowC*R*Real.cos frameCap/pairNorm 1 lowC frameCap := by
    dsimp [dVelocity,normD1,pairProduct]
    ring
  rw [he,lt_div_iff₀ hN]
  dsimp only [charge,lowC] at hn ⊢
  linarith

/-- Squaring of positive quantities on the whole negative half, with the signed sine kept in the
norm identity. -/
theorem dVelocity_negative_lower {s : ℝ} (hs : s∈Icc (-frameCap) 0) :
    dVelocity 0≤dVelocity s := by
  have hsi : |s|≤frameCap := abs_le.mpr
    ⟨hs.1,hs.2.trans (by norm_num [frameCap])⟩
  have hN := pairNorm_pos (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC]) hsi
  have hN0 := pairNorm_pos (p:=1) (q:=lowC) (t:=0)
    (by norm_num) (by norm_num [lowC]) (by norm_num [frameCap])
  have hsq := dNorm_sq hsi
  have hsq0 := dNorm_sq (s:=0) (by norm_num [frameCap])
  rw [Real.sin_zero,mul_zero,add_zero] at hsq0
  have hn : -s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have ht := transport_trig hn
  have hsin : -(6443/10000:ℝ)<Real.sin s ∧ Real.sin s≤0 := by
    have he := Real.sin_neg s
    constructor <;> linarith [ht.2.2.1,ht.2.2.2.1]
  have hp : 0≤ -Real.sin s*((106/25)*Real.sin s+18/5) :=
    mul_nonneg (by linarith [hsin.2]) (by linarith [hsin.1])
  have hc := transport_cos_pos hsi
  have hcomp : pairNorm 1 lowC s≤pairNorm 1 lowC 0*Real.cos s := by
    have he : (pairNorm 1 lowC 0*Real.cos s)^2-(pairNorm 1 lowC s)^2=
        -Real.sin s*((106/25)*Real.sin s+18/5) := by
      rw [mul_pow,hsq0,hsq]
      linear_combination (106/25)*Real.sin_sq_add_cos_sq s
    exact le_of_pow_le_pow_left₀ two_ne_zero (mul_pos hN0 hc).le (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hcomp
    (show 0≤lowC*R by positivity)
  have he (x : ℝ) : dVelocity x=lowC*R*Real.cos x/pairNorm 1 lowC x := by
    dsimp [dVelocity,normD1,pairProduct]
    ring
  rw [he 0,he s,Real.cos_zero,mul_one,div_le_div_iff₀ hN0 hN]
  linarith

/-- The strict reserve of the second derivative on `[0, frameCap]`, from a positive polynomial. -/
theorem dVelocity_curvature_reserve {s : ℝ} (hs : s∈Icc 0 frameCap) :
    frameCap-s< -R*normD3 1 lowC s := by
  have hsi : |s|≤frameCap := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hN := pairNorm_pos (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC]) hsi
  have hsq := dNorm_sq hsi
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hsin := Real.sin_ge_sub_cube hs.1
  have hsinup := Real.sin_le hs.1
  obtain ⟨hc,_,hsin0,_,_⟩ := transport_trig hs
  have hs2 : s^2≤(7/10:ℝ)^2 :=
    pow_le_pow_left₀ hs.1 (by simpa [frameCap] using hs.2) 2
  have hs3 : s^3≤(7/10:ℝ)^3 :=
    pow_le_pow_left₀ hs.1 (by simpa [frameCap] using hs.2) 3
  have hC0 : 0≤1-s^2/2 := by linarith
  have hP0 : 0≤5161/625+(954/125)*s-(159/125)*s^3 := by linarith [hs.1]
  have hP : 5161/625+(954/125)*s-(159/125)*s^3≤
      5161/625+(954/125)*Real.sin s+(81/25)*(Real.sin s)^2 := by
    linarith [sq_nonneg (Real.sin s)]
  have hCP := mul_le_mul hcos hP hP0 (by linarith : 0≤Real.cos s)
  have hR : (1773/500:ℝ)≤lowC*R := by
    dsimp [lowC]
    linarith [radius_bounds.1]
  have hRmul := mul_le_mul_of_nonneg_right hR
    (mul_nonneg (by linarith : 0≤Real.cos s)
      (show 0≤5161/625+(954/125)*Real.sin s+(81/25)*(Real.sin s)^2 by positivity))
  have hCPmul := mul_le_mul_of_nonneg_left hCP (by norm_num : (0:ℝ)≤1773/500)
  have hnum : (1773/500)*(1-s^2/2)*(5161/625+(954/125)*s-(159/125)*s^3)≤
      lowC*R*Real.cos s*(5161/625+(954/125)*Real.sin s+(81/25)*(Real.sin s)^2) := by
    calc (1773/500)*(1-s^2/2)*(5161/625+(954/125)*s-(159/125)*s^3)
        =(1773/500)*((1-s^2/2)*(5161/625+(954/125)*s-(159/125)*s^3)) := by ring
      _ ≤ _ := hCPmul
      _ ≤ _ := hRmul
      _ = _ := by ring
  have hNu : pairNorm 1 lowC s<103/50+(7/8)*s :=
    lt_of_pow_lt_pow_left₀ 2 (by linarith [hs.1])
      (by rw [hsq]; linarith [sq_nonneg s,hs.1])
  have hrad : 106/25+(18/5)*Real.sin s≤106/25+(18/5)*s := by linarith
  have hrad0 : 0≤106/25+(18/5)*Real.sin s := by positivity
  have hp2 := pow_le_pow_left₀ hrad0 hrad 2
  have hpow := mul_le_mul hNu.le hp2 (sq_nonneg _)
    (show 0≤103/50+(7/8)*s by linarith [hs.1])
  have hN5 : (pairNorm 1 lowC s)^5=
      pairNorm 1 lowC s*(106/25+(18/5)*Real.sin s)^2 := by
    rw [show (pairNorm 1 lowC s)^5=pairNorm 1 lowC s*((pairNorm 1 lowC s)^2)^2 by ring,hsq]
  have hden : (pairNorm 1 lowC s)^5≤(103/50+(7/8)*s)*(106/25+(18/5)*s)^2 := by
    rw [hN5]
    exact hpow
  have hdenmul := mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hs.2)
  have hid : (1773/500)*(1-s^2/2)*(5161/625+(954/125)*s-(159/125)*s^3)-
      (103/50+(7/8)*s)*(106/25+(18/5)*s)^2*(frameCap-s)=
      1049297/312500+(566517/62500)*s+(16619147/625000)*s^2+
      (1714347/62500)*s^3+(567/50)*s^4+(281907/125000)*s^5 := by
    dsimp [frameCap]
    ring
  have hp : 0<(1773/500)*(1-s^2/2)*(5161/625+(954/125)*s-(159/125)*s^3)-
      (103/50+(7/8)*s)*(106/25+(18/5)*s)^2*(frameCap-s) := by
    rw [hid]
    have h3 := pow_nonneg hs.1 3
    have h4 := pow_nonneg hs.1 4
    have h5 := pow_nonneg hs.1 5
    linarith [hs.1,sq_nonneg s]
  have he : -R*normD3 1 lowC s=
      (lowC*R*Real.cos s*(5161/625+(954/125)*Real.sin s+(81/25)*(Real.sin s)^2))/
        (pairNorm 1 lowC s)^5 := by
    simp only [normD3,pairEnergy,pairProduct,lowC]
    ring
  rw [he,lt_div_iff₀ (pow_pos hN 5)]
  dsimp only [frameCap] at hdenmul hp ⊢
  linarith

theorem dCancellation_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt dCancellation (dCancellationD s) s := by
  have hn := (normD1_hasDerivAt (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC])
    (by rw [abs_of_nonneg hs.1]; exact hs.2)).const_mul R
  have ht := (Real.hasDerivAt_sin (frameCap-s)).comp s
    ((hasDerivAt_const s frameCap).sub (hasDerivAt_id s))
  refine (hn.sub ht).congr_deriv ?_
  rw [dCancellationD]
  ring

theorem dCancellationD_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt dCancellationD (dCancellationDD s) s := by
  have hn := (normD2_hasDerivAt (p:=1) (q:=lowC) (by norm_num) (by norm_num [lowC])
    (by rw [abs_of_nonneg hs.1]; exact hs.2)).const_mul R
  have ht := (Real.hasDerivAt_cos (frameCap-s)).comp s
    ((hasDerivAt_const s frameCap).sub (hasDerivAt_id s))
  refine (hn.add ht).congr_deriv ?_
  rw [dCancellationDD]
  ring

theorem dCancellation_concave : ConcaveOn ℝ (Icc 0 frameCap) dCancellation := by
  apply concave_of_deriv2
    (fun s hs => dCancellation_hasDerivAt hs)
    (fun s hs => dCancellationD_hasDerivAt hs)
  intro s hs
  have h := dVelocity_curvature_reserve hs
  have ht := Real.sin_le (sub_nonneg.mpr hs.2)
  dsimp [dCancellationDD]
  linarith

theorem dCancellation_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    charge<dCancellation s := by
  apply concave_gt_of_endpoints dCancellation_concave hs
  · dsimp [dCancellation]
    simp only [sub_zero]
    linarith [dVelocity_zero_lower]
  · simpa [dCancellation] using dVelocity_cap_lower

/-- The signed cancellation: `s + w` is the other D angle and is bounded by the same
`frameCap`. -/
theorem dVelocity_sine_lower {s w : ℝ}
    (hs : s∈Icc (-frameCap) frameCap) (hw : w∈Icc 0 frameCap)
    (hsw : s+w≤frameCap) : charge<dVelocity s-Real.sin w := by
  by_cases hs0 : s≤0
  · have hv := dVelocity_negative_lower ⟨hs.1,hs0⟩
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hw.1,Real.pi_pos])
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hw.2
    linarith [dVelocity_zero_lower]
  · have hs0' : 0≤ s := (lt_of_not_ge hs0).le
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hw.1,Real.pi_pos])
      (by dsimp [frameCap] at hs; linarith [hs0',Real.pi_gt_three])
      (show w≤frameCap-s by linarith)
    have hh := dCancellation_lower ⟨hs0',hs.2⟩
    dsimp [dCancellation] at hh
    linarith

end SquaresInCircles.Eight.GlobalGA.PositiveATD0
end
end
end
