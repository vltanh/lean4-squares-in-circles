module

public import SquaresInCircles.Eight.Owners.BT.ReturnScalar
public import SquaresInCircles.Eight.Owners.BT.CoreDE3Support
public import SquaresInCircles.Eight.Owners.BT.CoreDE3Polynomial
public import SquaresInCircles.Eight.Owners.BT.OneNegativeAligned
public import SquaresInCircles.Eight.Owners.BT.ErrorComparisons

/-!
# Eight squares: excluding every original BT0 owner

Every DE owner, radial kind and signed error is dispatched.  Both
zero-edge owners, both signs of B and all original weak axis ties
remain available.  Fixed-ray expansion preserves the supplied BT0
witness, so the contradiction belongs to the source radius.
-/

section
/-!
## The polynomials of the saturated-prefix monotonicity

For each saturated placement, the numerator of the derivative, with the prefix circle kept, is
the polynomial `H last`, of degree `13` or `14` in the prefix total. Each is positive on the whole
prefix interval `[0, 7/10]`, where its Bernstein coefficients of degree `14` are positive
(`positive`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3.SaturatedPolynomial

open Polynomial PowerTailBounds FrameCircleArc

def a (last : Bool) : ℚ := if last then 269343/250000 else 49/50
def other (last : Bool) : ℚ := if last then 49/50 else 269343/250000
def rho (last : Bool) : ℚ := if last then 574543/500000 else 616589/500000
def U : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5
def tangent (last : Bool) : ℚ[X] :=
  C ((3/5)/rho last)+C ((2/5)*(other last)^2/(rho last)^3)*X
def P (last : Bool) : ℚ[X] :=
  if last then C (3083/2500)-C (833/2500)*X-C (3167/10000)*X^2
  else C (11491/10000)-C (1541/5000)*X-C (2931/10000)*X^2
def numerator (last : Bool) : ℚ[X] :=
  C (a last)*PrefixPolynomial.c*TailPolynomial.C6+
    C ((2/5)*a last)*TailPolynomial.S7-C (2/5)*PrefixPolynomial.c
def energy (last : Bool) : ℚ[X] :=
  C ((a last)^2)+PrefixPolynomial.c^2-
    C (2*a last)*PrefixPolynomial.c*TailPolynomial.S7
def denominator (last : Bool) : ℚ[X] := energy last+(P last)^2
def affinePart (last : Bool) : ℚ[X] :=
  (if last then C (-3/5)+C (2/5)*TailPolynomial.C6-PrefixPolynomial.c*U
    else C (-1/5)-C (49/50)*U)-C ((1979/1000)*(2/5))*tangent last
def H (last : Bool) : ℚ[X] := affinePart last*denominator last+
  C (2*(989/500))*numerator last*P last

/-- `H last` has positive Bernstein coefficients of degree `14` on `[0, 7/10]`: it is a positive
combination of the products `p^i (7/10 - p)^(14-i)`, which `linarith` finds. -/
theorem positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<aeval p (H last) := by
  have h0 := hp.1
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤p^i*(7/10-p)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  cases last <;>
    simp only [H,affinePart,denominator,energy,numerator,P,tangent,U,a,other,rho,
      PrefixPolynomial.c,TailPolynomial.S7,TailPolynomial.C6,Bool.false_eq_true,↓reduceIte,
      map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast] <;>
    push_cast <;>
    linarith [hb 14 0,hb 13 1,hb 12 2,hb 11 3,hb 10 4,hb 9 5,hb 8 6,hb 7 7,hb 6 8,hb 5 9,
      hb 4 10,hb 3 11,hb 2 12,hb 1 13,hb 0 14]

theorem a_bounds (last : Bool) : (49/50:ℝ)≤(a last:ℝ) ∧ 0<(a last:ℝ) := by
  cases last <;> norm_num [a]

theorem rho_reserve (last : Bool) :
    (0:ℝ)<(rho last:ℝ) ∧ (rho last:ℝ)^2<(other last:ℝ)^2+9/25 := by
  cases last <;> norm_num [rho,other]

theorem envelope_positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/4:ℝ)<aeval p (P last) := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  dsimp [frameCap] at hp h2
  cases last <;> norm_num [P] <;> nlinarith [hp.1,hp.2]

theorem sine_polynomial_nonnegative {p : ℝ} (hp : p∈Icc 0 frameCap) :
    0≤aeval p TailPolynomial.S7 := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  have h6 := pow_le_pow_left₀ hp.1 hp.2 6
  have h4 := pow_nonneg hp.1 4
  have hfactor : 0≤1-p^2/6+p^4/120-p^6/5040 := by
    dsimp [frameCap] at h2 h6
    nlinarith only [h2,h6,h4]
  have hm := mul_nonneg hp.1 hfactor
  rw [TailPolynomial.S7_eval]
  dsimp [Arithmetic.sin7]
  nlinarith only [hm]

theorem cosine_polynomial_lower {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/4:ℝ)<aeval p TailPolynomial.C6 := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  have h6 := pow_le_pow_left₀ hp.1 hp.2 6
  have h4 := pow_nonneg hp.1 4
  rw [TailPolynomial.C6_eval]
  dsimp [frameCap] at h2 h6
  nlinarith only [h2,h6,h4]

theorem numerator_positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    0<aeval p (numerator last) := by
  have ha := a_bounds last
  have hc := weight_pos hp
  have hfirst := mul_lt_mul_of_pos_left (cosine_polynomial_lower hp)
    (mul_pos ha.2 hc)
  have hs := mul_nonneg (show 0≤(2/5:ℝ)*(a last:ℝ) from mul_nonneg (by norm_num) ha.2.le)
    (sine_polynomial_nonnegative hp)
  have hgap : 0<(3/4)*(a last:ℝ)-2/5 := by linarith [ha.1]
  have hpositive := mul_pos hc hgap
  simp only [numerator,map_sub,map_add,map_mul,aeval_C,eq_ratCast,PrefixPolynomial.c_eval]
  push_cast
  nlinarith only [hfirst,hs,hpositive]

end SquaresInCircles.Eight.GlobalBT.CoreDE3.SaturatedPolynomial
end
end
end

section
/-!
## Tangent majorants of the saturated norm ratios

A factored difference of squares proves the tangent bound of the concave ratio `c / N`
(`circle_ratio_tangent`). Replacing only its positive root denominators by smaller rational roots
gives the two polynomial tangents `SaturatedPolynomial.tangent` (`saturated_tangent_upper`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open Polynomial FrameCircleArc

theorem circle_ratio_tangent {b c t N N0 : ℝ}
    (hc : 0≤c) (ht : 0≤t) (hN : 0<N) (hN0 : 0<N0)
    (hs : N^2=b^2+c^2) (hs0 : N0^2=b^2+t^2) :
    c/N≤t/N0+(b^2/N0^3)*(c-t) := by
  have hfactor : ((b^2*c+t^3)*N)^2-(c*N0^3)^2=
      b^2*(c-t)^2*(b^2*c*(c+2*t)+t^3*(2*c+t)) := by
    calc
      ((b^2*c+t^3)*N)^2-(c*N0^3)^2=
          (b^2*c+t^3)^2*N^2-c^2*(N0^2)^3 := by ring
      _ = b^2*(c-t)^2*(b^2*c*(c+2*t)+t^3*(2*c+t)) := by rw [hs,hs0]; ring
  have hfactor_nonneg : 0≤b^2*(c-t)^2*(b^2*c*(c+2*t)+t^3*(2*c+t)) := by positivity
  have hright : 0≤(b^2*c+t^3)*N := by positivity
  have hcross : c*N0^3≤(b^2*c+t^3)*N := by
    nlinarith only [hfactor,hfactor_nonneg,hright]
  have hquot : c/N≤(b^2*c+t^3)/N0^3 :=
    (div_le_div_iff₀ hN (pow_pos hN0 3)).2 hcross
  have hid : (b^2*c+t^3)/N0^3=t/N0+(b^2/N0^3)*(c-t) := by
    field_simp [hN0.ne']
    linear_combination -t*hs0
  rw [hid] at hquot
  exact hquot

theorem saturated_tangent_upper (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    weight p/tailNorm (SaturatedPolynomial.other last:ℝ) (weight p) 0≤
      aeval p (SaturatedPolynomial.tangent last) := by
  let b : ℝ := (SaturatedPolynomial.other last:ℝ)
  let rho : ℝ := (SaturatedPolynomial.rho last:ℝ)
  let N0 := tailNorm b (3/5) 0
  let N := tailNorm b (weight p) 0
  have hb : 0<b := by cases last <;> norm_num [b,SaturatedPolynomial.other]
  have hc := weight_pos hp
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hN : 0<N := tailNorm_pos hb hc hzero
  have hN0 : 0<N0 := tailNorm_pos hb (by norm_num) hzero
  have hsq : N^2=b^2+(weight p)^2 := by
    simpa [N] using tailNorm_sq hb hc hzero
  have hsq0 : N0^2=b^2+(3/5)^2 := by
    simpa [N0] using tailNorm_sq hb (by norm_num : (0:ℝ)<3/5) hzero
  have hreserve := SaturatedPolynomial.rho_reserve last
  have hrho : 0<rho := hreserve.1
  have hroot : rho≤N0 := by
    have hh : rho^2<b^2+(3/5)^2 := by
      rw [show ((3:ℝ)/5)^2=9/25 by norm_num]
      exact hreserve.2
    nlinarith only [hh,hsq0,hN0,hrho]
  have hfirst := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤3/5) hrho hroot
  have hsecond := div_le_div_of_nonneg_left (sq_nonneg b) (pow_pos hrho 3)
    (pow_le_pow_left₀ hrho.le hroot 3)
  have hproduct := mul_le_mul_of_nonneg_right hsecond
    (show 0≤weight p-3/5 by linarith [(weight_bounds hp).1])
  have htangent := circle_ratio_tangent hc.le (by norm_num : (0:ℝ)≤3/5)
    hN hN0 hsq hsq0
  have hpoly : aeval p (SaturatedPolynomial.tangent last)=
      (3/5)/rho+(b^2/rho^3)*(weight p-3/5) := by
    simp only [SaturatedPolynomial.tangent,map_add,map_mul,aeval_C,aeval_X,eq_ratCast]
    push_cast
    dsimp [rho,b,weight,slope]
    ring
  rw [hpoly]
  change weight p/N≤_
  linarith only [hfirst,hproduct,htangent]

end SquaresInCircles.Eight.GlobalBT.CoreDE3
end
end
end

section
/-!
## Transferring the two saturated derivative certificates

The actual varying-circle numerator lies above its polynomial, its
norm square lies below the explicit energy polynomial, and the exact
other-circle ratio lies below its tangent.  The signed radius choices
then transfer each complete polynomial certificate to the derivative.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open Polynomial FrameCircleArc

theorem radius_lower : (989/500:ℝ)<R := by
  have hs := R_sq
  have hp := R_pos
  norm_num [Q0] at hs
  nlinarith

theorem norm_ratio_lower {N X P b B : ℝ}
    (hN : 0<N) (_hP : 0<P) (hB : 0<B) (hX : N^2≤X) (hb : B≤b) :
    0<X+P^2 ∧ 2*B*P/(X+P^2)≤b/N := by
  have hD : 0<X+P^2 := by nlinarith [sq_pos_of_pos hN,sq_nonneg P]
  have hs : 2*P*N≤X+P^2 := by nlinarith [sq_nonneg (N-P)]
  have hfirst := mul_le_mul_of_nonneg_left hs hB.le
  have hlast := mul_le_mul_of_nonneg_right hb hD.le
  refine ⟨hD,(div_le_div_iff₀ hD hN).2 ?_⟩
  nlinarith only [hfirst,hlast]

theorem polynomial_ratio_lower (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    0<aeval p (SaturatedPolynomial.denominator last) ∧
      2*aeval p (SaturatedPolynomial.numerator last)*aeval p (SaturatedPolynomial.P last)/
        aeval p (SaturatedPolynomial.denominator last)≤
          prefixRatio (SaturatedPolynomial.a last:ℝ) p := by
  let a : ℝ := (SaturatedPolynomial.a last:ℝ)
  have ha : 0<a := (SaturatedPolynomial.a_bounds last).2
  have hc := weight_pos hp
  have hN := tailNorm_pos ha hc hp
  have hP : 0<aeval p (SaturatedPolynomial.P last) := by
    linarith [SaturatedPolynomial.envelope_positive last hp]
  have hB := SaturatedPolynomial.numerator_positive last hp
  have hsin := sin7_lower hp.1
  have hcos := cos_lower_six hp.1
  have hsinProduct := mul_le_mul_of_nonneg_left hsin (show 0 ≤ slope*a by
    dsimp [slope]; positivity)
  have hcosProduct := mul_le_mul_of_nonneg_left hcos (mul_nonneg ha.le hc.le)
  have hb : aeval p (SaturatedPolynomial.numerator last)≤
      a*weight p*Real.cos p+slope*a*Real.sin p-slope*weight p := by
    simp only [SaturatedPolynomial.numerator,map_sub,map_add,map_mul,aeval_C,eq_ratCast,
      PrefixPolynomial.c_eval,TailPolynomial.C6_eval,TailPolynomial.S7_eval]
    push_cast
    dsimp [a,slope] at hsinProduct hcosProduct ⊢
    nlinarith only [hsinProduct,hcosProduct]
  have hsq := tailNorm_sq ha hc hp
  have hsinEnergy := mul_le_mul_of_nonneg_left hsin (show 0≤2*a*weight p by positivity)
  have hX : (tailNorm a (weight p) p)^2≤aeval p (SaturatedPolynomial.energy last) := by
    rw [hsq]
    simp only [SaturatedPolynomial.energy,map_sub,map_add,map_mul,map_pow,aeval_C,eq_ratCast,
      PrefixPolynomial.c_eval,TailPolynomial.S7_eval]
    push_cast
    dsimp [a] at hsinEnergy ⊢
    nlinarith only [hsinEnergy]
  have hh := norm_ratio_lower hN hP hB hX hb
  simpa [SaturatedPolynomial.denominator,prefixRatio,a] using hh

def rawDerivative (last : Bool) (p : ℝ) : ℝ :=
  (if last then -3/5+slope*Real.cos p-weight p*Real.sin p else -1/5-kappa*Real.sin p)+
    R*(prefixRatio (SaturatedPolynomial.a last:ℝ) p-
      slope*weight p/tailNorm (SaturatedPolynomial.other last:ℝ) (weight p) 0)

theorem polynomial_affine_lower (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    aeval p (SaturatedPolynomial.affinePart last)+
      (1979/1000)*slope*aeval p (SaturatedPolynomial.tangent last)≤
        (if last then -3/5+slope*Real.cos p-weight p*Real.sin p
          else -1/5-kappa*Real.sin p) := by
  have hsin : Real.sin p≤aeval p SaturatedPolynomial.U := by
    have h := sin_upper_five hp.1
    simp only [SaturatedPolynomial.U,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X,
      eq_ratCast]
    push_cast
    linarith
  have hcos := cos_lower_six hp.1
  have hsinW := mul_le_mul_of_nonneg_left hsin (weight_pos hp).le
  have hsinK := mul_le_mul_of_nonneg_left hsin (show 0≤kappa by norm_num [kappa])
  cases last <;>
    simp only [SaturatedPolynomial.affinePart,Bool.false_eq_true,↓reduceIte,
      map_sub,map_add,map_mul,aeval_C,eq_ratCast,
      PrefixPolynomial.c_eval,TailPolynomial.C6_eval] <;>
    norm_num [slope,kappa] at hsinK ⊢ <;> nlinarith only [hcos,hsinW,hsinK]

theorem rawDerivative_positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    0<rawDerivative last p := by
  let B : ℝ := aeval p (SaturatedPolynomial.numerator last)
  let P : ℝ := aeval p (SaturatedPolynomial.P last)
  let D : ℝ := aeval p (SaturatedPolynomial.denominator last)
  let L : ℝ := aeval p (SaturatedPolynomial.affinePart last)
  let T : ℝ := aeval p (SaturatedPolynomial.tangent last)
  let q : ℝ := 2*B*P/D
  have hB : 0<B := SaturatedPolynomial.numerator_positive last hp
  have hP : 0<P := by dsimp [P]; linarith [SaturatedPolynomial.envelope_positive last hp]
  have hrat := polynomial_ratio_lower last hp
  have hD : 0<D := hrat.1
  have hq : 0≤q := by dsimp [q]; positivity
  have hratio : q≤prefixRatio (SaturatedPolynomial.a last:ℝ) p := hrat.2
  have hRratio := mul_le_mul radius_lower.le hratio hq R_pos.le
  have hb : 0<(SaturatedPolynomial.other last:ℝ) := by
    cases last <;> norm_num [SaturatedPolynomial.other]
  have hnorm := tailNorm_pos hb (weight_pos hp)
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  have htangent := saturated_tangent_upper last hp
  have hpenalty := mul_le_mul radius_upper.le htangent
    (div_nonneg (weight_pos hp).le hnorm.le) (by norm_num : (0:ℝ)≤1979/1000)
  have hpenalty' := mul_le_mul_of_nonneg_left hpenalty (show 0 ≤ slope by norm_num [slope])
  have hpoly : 0<L*D+2*(989/500)*B*P := by
    simpa [SaturatedPolynomial.H,L,D,B,P] using SaturatedPolynomial.positive last hp
  have hmodel : 0<L+(989/500)*q := by
    have hid : (L+(989/500)*q)*D=L*D+2*(989/500)*B*P := by
      dsimp [q]
      field_simp [hD.ne']
    have hh : 0<(L+(989/500)*q)*D := by rw [hid]; exact hpoly
    exact (mul_pos_iff_of_pos_right hD).1 hh
  have hbase := polynomial_affine_lower last hp
  dsimp [L,T] at hmodel
  dsimp [rawDerivative]
  have e1 : R*(slope*weight p/tailNorm (SaturatedPolynomial.other last:ℝ) (weight p) 0)=
      slope*(R*(weight p/tailNorm (SaturatedPolynomial.other last:ℝ) (weight p) 0)) := by
    ring
  linarith only [hmodel,hbase,hRratio,hpenalty',e1]

theorem firstD_at_m_positive {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<firstD p m := by
  simpa [rawDerivative,firstD,SaturatedPolynomial.a,SaturatedPolynomial.other,kappa,m] using
    rawDerivative_positive false hp

theorem lastD_at_m_positive {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<lastD p m := by
  simpa [rawDerivative,lastD,SaturatedPolynomial.a,SaturatedPolynomial.other,kappa,m] using
    rawDerivative_positive true hp

end SquaresInCircles.Eight.GlobalBT.CoreDE3
end
end
end

section
/-!
## The core-E negative-DE3 tail exceeds the path threshold

Both saturated prefix placements `first` and `last` increase from their aligned value
(`first_monotone`, `last_monotone`) and exceed `pathThreshold` (`endpoints_strict`). With the
polynomial for small DE errors, this bounds the tail for both owners of TD and every allocation of
the negative errors (`tail_strict`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open FrameCircleArc

theorem firstD_positive {p e : ℝ} (hp : p∈Icc 0 frameCap)
    (he : e∈Icc m (141/100:ℝ)) : 0<firstD p e := by
  have hm : 0 < m := by norm_num [m]
  have hepos := hm.trans_le he.1
  have hc := weight_pos hp
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hNm := tailNorm_pos hm hc hzero
  have hNe := tailNorm_pos hepos hc hzero
  have hsm := tailNorm_sq hm hc hzero
  have hse := tailNorm_sq hepos hc hzero
  have hpow := pow_le_pow_left₀ hm.le he.1 2
  have hnorm : tailNorm m (weight p) 0≤tailNorm e (weight p) 0 := by
    simp only [Real.sin_zero,mul_zero,sub_zero] at hsm hse
    nlinarith only [hsm,hse,hpow,hNm,hNe]
  have hratio := div_le_div_of_nonneg_left hc.le hNm hnorm
  have hprod := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ R*slope by exact mul_nonneg R_pos.le (by norm_num [slope]))
  have hbase := firstD_at_m_positive hp
  dsimp [firstD] at hbase ⊢
  have e1 : ∀ N : ℝ, R*(slope*weight p/N)=R*slope*(weight p/N) := fun N => by ring
  linarith only [hbase,hprod,e1 (tailNorm e (weight p) 0),e1 (tailNorm m (weight p) 0)]

theorem lastD_positive {p e : ℝ} (hp : p∈Icc 0 frameCap)
    (he : e∈Icc m (141/100:ℝ)) : 0<lastD p e := by
  have hratio := prefixRatio_monotone hp
    (show m∈Icc m (141/100:ℝ) by norm_num [m]) he he.1
  have hm := mul_le_mul_of_nonneg_left hratio R_pos.le
  have hbase := lastD_at_m_positive hp
  dsimp [lastD] at hbase ⊢
  nlinarith only [hbase,hm]

theorem first_monotone (t : ℝ) {e : ℝ} (he : e∈Icc m (141/100:ℝ)) :
    MonotoneOn (fun p => first p t e) (Icc 0 frameCap) := by
  have hepos : 0<e := by dsimp [m] at he; linarith [he.1]
  apply monoOn_of_hasDeriv_nonneg
  · exact fun p hp => (first_deriv (t := t) hp hepos).continuousAt.continuousWithinAt
  · exact fun p hp => first_deriv (t := t) (Ioo_subset_Icc_self hp) hepos
  · exact fun p hp => (firstD_positive (Ioo_subset_Icc_self hp) he).le

theorem last_monotone (t : ℝ) {e : ℝ} (he : e∈Icc m (141/100:ℝ)) :
    MonotoneOn (fun p => last p t e) (Icc 0 frameCap) := by
  have hepos : 0<e := by dsimp [m] at he; linarith [he.1]
  apply monoOn_of_hasDeriv_nonneg
  · exact fun p hp => (last_deriv (t := t) hp hepos).continuousAt.continuousWithinAt
  · exact fun p hp => last_deriv (t := t) (Ioo_subset_Icc_self hp) hepos
  · exact fun p hp => (lastD_positive (Ioo_subset_Icc_self hp) he).le

theorem first_zero_le {p t e : ℝ} (hp : p∈Icc 0 frameCap)
    (he : e∈Icc m (141/100:ℝ)) : first 0 t e≤first p t e :=
  first_monotone t he (by norm_num [frameCap]) hp hp.1

theorem last_zero_le {p t e : ℝ} (hp : p∈Icc 0 frameCap)
    (he : e∈Icc m (141/100:ℝ)) : last 0 t e≤last p t e :=
  last_monotone t he (by norm_num [frameCap]) hp hp.1

theorem endpoints_strict {p t : ℝ} (hp : p∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) :
    pathThreshold<first p t (endpointWeight t) ∧ pathThreshold<last p t (endpointWeight t) := by
  by_cases hsmall : t≤1/5
  · rw [endpointWeight,ite_eq_left hsmall]
    exact small_endpoints hp ⟨ht.1,hsmall⟩
  · have hsat : t∈Icc (1/5:ℝ) frameCap := ⟨by linarith,ht.2⟩
    have he := saturated_weight_bounds ht
    have hbase := saturated_base hsat
    have hfirst := first_zero_le (t := t) hp ⟨he.1,he.2.le⟩
    have hlast := last_zero_le (t := t) hp ⟨he.1,he.2.le⟩
    rw [first_zero] at hfirst
    rw [last_zero] at hlast
    rw [endpointWeight,ite_eq_right hsmall]
    exact ⟨hbase.trans_le hfirst,hbase.trans_le hlast⟩

/-- For both owners of TD and all nonnegative errors `r`, `s`, `t` with `r + s + t ≤ frameCap`, the
tail exceeds `pathThreshold`. -/
theorem tail_strict (second : Bool) {r s t : ℝ}
    (hr : 0≤r) (hs : 0≤ s) (ht : 0≤t) (hcap : r+s+t≤frameCap) :
    pathThreshold<tail second (endpointWeight t) (weight (r+s)) r s t := by
  have hp : r+s∈Icc 0 frameCap := ⟨add_nonneg hr hs,by linarith⟩
  have htdom : t∈Icc 0 frameCap := ⟨ht,by linarith⟩
  have he : 0<endpointWeight t := by
    have hh := (endpointWeight_bounds htdom).1
    dsimp [kappa] at hh
    linarith
  have hends := endpoints_strict hp htdom
  exact (lt_min hends.1 hends.2).trans_le (concentrated_lower second hr hs hp.2 he)

end SquaresInCircles.Eight.GlobalBT.CoreDE3
end
end
end

section
/-!
## The core-E negative-DE3 path

The weak AB, BT0, TD and DE3 inequalities, with their positive weights, make the path charge
exceed `pathThreshold` when E is on the core (`path`). Only the positive prefix errors are removed
inside the dual; the negative DE3 error and the core marker stay in it. On a boundary cycle at
`Q0` with `C.tangent E ≤ 0`, owner `0` on BT, owner `3` on DE, E on the core and
`delta F.theta D ≤ 0` are therefore incompatible (`ceiling_false`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open Candidate FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem path (a b t d e : State) (ab td : Bool) {v x w u : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0) (hcore : e.branch.type=0)
    (hv : |v|≤frameCap) (hx : |x|≤frameCap) (hw : |w|≤frameCap)
    (hu : u∈Icc 0 frameCap)
    (hcap : max (-x) 0+max (-w) 0+u≤frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v (leftOwner ab))
    (hBT : GlobalOuterAnchor.width x≤projection true b t x 0)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width (-u)≤projection true d e (-u) 3) :
    pathThreshold<Real.pi+v+x+w-u+kappa*a.b+ZeroPrimary.unsigned e := by
  let p := max (-x) 0+max (-w) 0
  have hp : p∈Icc 0 frameCap :=
    ⟨by dsimp [p]; positivity,by dsimp [p]; linarith [hu.1]⟩
  have hc := weight_pos hp
  have hcu := (weight_bounds hp).2.2
  have heWeight : 0≤endpointWeight u :=
    (show 0≤kappa by norm_num [kappa]).trans (endpointWeight_bounds hu).1
  have hABdual := (AB_delete a b ab hv).trans
    (zeroDual_le_error a b ab (ABweight_positive hv).le hAB)
  have hBTdual := (retain_BT0 b t (lambda := kappa) hx (by norm_num [kappa]) le_rfl).trans
    (quarterDual_le_error b t 0 (lambda := kappa) (by norm_num [kappa]) hBT)
  have hTDdual := (retain_zero t d td hw hc.le hcu).trans
    (zeroDual_le_error t d td hc.le hTD)
  have hDEdual := quarterDual_le_error d e 3 heWeight hDE
  have hscalar := tail_strict td (le_max_right (-x) 0) (le_max_right (-w) 0) hu.1 hcap
  have hsupport := support b t d e td (c := weight p) ht hd he hcore
    (negative_part_range hx) (negative_part_range hw) hu
  have hstrict := hscalar.trans_le hsupport
  have hay := transverse_of_nonneg a ha
  rw [hay] at hABdual
  dsimp [reduced] at hstrict
  dsimp [retainedNegative,p] at hBTdual hTDdual hstrict
  linarith

theorem ceiling_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 0).Feasible (C.square B) (C.square T))
    (hDE : (forwardAxis 3).Feasible (C.square D) (C.square E))
    (hcore : C.kind E≠.outer) (hnegative : delta F.theta D≤0) : False := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hA := GlobalZeroLow.frame_BT_low_A_positive F hq 0 (Or.inl rfl) hBT
  have hT : 0<C.tangent T := by
    rcases GlobalQuarterSign.of_frame F hq B (by norm_num [word,B]) 0
      (by simpa [B,T,next] using hBT) with ⟨_,hh⟩ | ⟨hh,_⟩
    · simpa [B,T,next] using hh
    · rcases hh with hh | hh <;> norm_num at hh
  have hD := (GlobalQuarterSign.frame_DE F hq hE).1
  have hex (i : Vertex) :
      ∃ k : Fin 4,(forwardAxis k).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨k,hk⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨k,hk ▸ C.feasible i⟩
  choose owner hf using hex
  have hABowner : owner Candidate.A=0 ∨ owner Candidate.A=2 := by
    rcases GlobalZeroSign.of_frame F hq Candidate.A (by norm_num [word,Candidate.A])
      (owner Candidate.A) (hf Candidate.A) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hTDowner : owner T=0 ∨ owner T=2 := by
    rcases GlobalZeroSign.of_frame F hq T (by norm_num [word,T]) (owner T) (hf T) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  obtain ⟨ab,hab⟩ : ∃ab : Bool,leftOwner ab=owner Candidate.A := by
    rcases hABowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  obtain ⟨td,htd⟩ : ∃td : Bool,leftOwner td=owner T := by
    rcases hTDowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hABstate : (stateOf C Candidate.A).Feasible (stateOf C B) (leftOwner ab)
      (0+delta F.theta Candidate.A) := by
    simpa [Candidate.phi,word,Candidate.A,B,next,hab] using
      GlobalAllHigh.frame_state_feasible F Candidate.A (owner Candidate.A) (hf Candidate.A)
  have hBTstate : (stateOf C B).Feasible (stateOf C T) 0
      (Real.pi/2+delta F.theta B) := by
    simpa [Candidate.phi,word,B,T,next] using GlobalAllHigh.frame_state_feasible F B 0
      (by simpa [B,T,next] using hBT)
  have hTDstate : (stateOf C T).Feasible (stateOf C D) (leftOwner td)
      (0+delta F.theta T) := by
    simpa [Candidate.phi,word,T,D,next,htd] using
      GlobalAllHigh.frame_state_feasible F T (owner T) (hf T)
  have hDEstate : (stateOf C D).Feasible (stateOf C E) 3
      (Real.pi/2+delta F.theta D) := by
    simpa [Candidate.phi,word,D,E,next] using GlobalAllHigh.frame_state_feasible F D 3
      (by simpa [D,E,next] using hDE)
  have hey : transverse (stateOf C E)≤0 := by
    rw [GlobalAllHigh.state_transverse_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (C.a_pos E).le hE
  have hcoreState : (stateOf C E).branch.type=0 := (branchOf_core_iff C E).2 hcore
  have hu : -delta F.theta D∈Icc 0 frameCap :=
    ⟨by linarith,(neg_le_abs (delta F.theta D)).trans (hdelta D)⟩
  have hcap : max (-delta F.theta B) 0+max (-delta F.theta T) 0+
      (-delta F.theta D)≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    rw [max_eq_left (show 0≤-delta F.theta D by linarith)] at hh
    exact hh
  have hpath := path (stateOf C Candidate.A) (stateOf C B) (stateOf C T) (stateOf C D)
    (stateOf C E) ab td (GlobalAllHigh.state_positive_of_tangent C Candidate.A hA).le
    (GlobalAllHigh.state_positive_of_tangent C T hT).le
    (GlobalAllHigh.state_negative_of_tangent C D hD).le hey hcoreState
    (hdelta Candidate.A) (hdelta B) (hdelta T) hu hcap
    ((projection_feasible false _ _ _ (hdelta Candidate.A)).1 hABstate)
    ((projection_feasible true _ _ _ (hdelta B)).1 hBTstate)
    ((projection_feasible false _ _ _ (hdelta T)).1 hTDstate)
    (by simpa only [neg_neg] using (projection_feasible true _ _ _ (hdelta D)).1 hDEstate)
  have hreturn := frame_tail_cap F hE hA.le
  dsimp [tailCharge] at hreturn
  linarith

end SquaresInCircles.Eight.GlobalBT.CoreDE3
end
end
end

section
/-!
## Pointwise positive-BT1 removal on the original states

The global quarter-owner theorem already makes the actual T outer.
Its original primary is therefore at least the diagonal coordinate,
which pays the primary loss directly.  The B increment uses its
unchanged signed circle.  No maximizing point is introduced.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OnePositive

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem B_increment (b : State) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0≤kappa*Real.sin x*(R-(Real.cos x+Real.sin x)/2-
      (Real.cos x*b.a-Real.sin x*transverse b)) := by
  have tr := transport_trig hx
  have hs := state_support b (Real.cos x) (Real.sin x)
  have hunit : (Real.cos x)^2+(Real.sin x)^2=1 := by
    linarith [Real.sin_sq_add_cos_sq x]
  rw [hunit,Real.sqrt_one,mul_one] at hs
  have hy := mul_nonneg tr.2.2.1
    (show 0≤b.b+transverse b by linarith [(transverse_bounds b).1])
  have hinner : 0≤R-(Real.cos x+Real.sin x)/2-
      (Real.cos x*b.a-Real.sin x*transverse b) := by
    change Real.cos x*b.a+Real.sin x*b.b≤R-(Real.cos x+Real.sin x)/2 at hs
    linarith only [hs,hy]
  exact mul_nonneg (mul_nonneg (by norm_num [kappa]) tr.2.2.1) hinner

theorem difference_identity (b t : State) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    quarterDual b t 1 x (kappa*Real.cos x)-quarterDual b t 0 0 kappa=
      gain x+kappa*Real.sin x*(R-(Real.cos x+Real.sin x)/2-
        (Real.cos x*b.a-Real.sin x*transverse b))+
          kappa*(1-Real.cos x)*(t.a-c0) := by
  have hw0 : GlobalOuterAnchor.width 0=1 := by norm_num [GlobalOuterAnchor.width]
  have hp1 : projection true b t x 1=t.a+b.a*Real.sin x+transverse b*Real.cos x := by
    simp [projection]
  have hp0 : projection true b t 0 0=transverse b+t.a := by simp [projection]
  simp only [quarterDual]
  rw [width_positive hx,hw0,hp1,hp0]
  unfold gain
  linear_combination kappa*(1/2-transverse b)*(Real.sin_sq_add_cos_sq x)

theorem delete (b t : State) (hT : c0≤t.a) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    quarterDual b t 0 0 kappa≤quarterDual b t 1 x (kappa*Real.cos x) := by
  have hB := B_increment b hx
  have hTgain := mul_nonneg
    (mul_nonneg (by norm_num [kappa] : 0≤kappa)
      (sub_nonneg.mpr (Real.cos_le_one x))) (sub_nonneg.mpr hT)
  have hG := gain_nonnegative hx
  have hid := difference_identity b t hx
  linarith

theorem delete_outer (b t : State) (hT : t.branch.type≠0) {x : ℝ}
    (hx : x∈Icc 0 frameCap) :
    quarterDual b t 0 0 kappa≤quarterDual b t 1 x (kappa*Real.cos x) := by
  have ht := state_outer_chart t hT
  have ha := (A_bounds ht.2).1
  rw [← ht.1] at ha
  exact delete b t ha hx

theorem actual_aligned_charge (b t : State) (hT : t.branch.type≠0) {x : ℝ}
    (hx : x∈Icc 0 frameCap) (hBT : GlobalOuterAnchor.width x≤projection true b t x 1) :
    quarterDual b t 0 0 kappa≤x := by
  have hl : 0≤kappa*Real.cos x :=
    mul_nonneg (by norm_num [kappa]) (by linarith [(transport_trig hx).1])
  exact (delete_outer b t hT hx).trans (quarterDual_le_error b t 1 hl hBT)

end SquaresInCircles.Eight.GlobalBT.OnePositive
end
end
end

section
/-!
## The two tails after a positive BT1 error

An outer T pays the pointwise BT comparison, which deletes a nonnegative BT1 error. The two tail
scalars then apply with BT error zero, the ordinary one (`ordinary_path`) and the core-E
negative-DE3 one (`core_path`), for every owner of AB and TD; so a boundary cycle at `Q0` with
`C.tangent E ≤ 0` has no weak BT1 witness at nonnegative error (`ceiling_false`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OnePositive

open Candidate FramePair FrameCircleArc GlobalOuterAnchor

theorem ordinary_path (a b t d e : State) (ab td : Bool) (jD : Fin 4)
    {v x w y : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0) (hT : t.branch.type≠0)
    (hv : |v|≤frameCap) (hx : x∈Icc 0 frameCap) (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-w) 0+max (-y) 0≤frameCap)
    (hjD : jD=2 ∨ jD=3) (hordinary : jD=2 ∨ 0≤y ∨ e.branch.type≠0)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v (leftOwner ab))
    (hBT : GlobalOuterAnchor.width x≤projection true b t x 1)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width y≤projection true d e y jD) :
    pathThreshold<Real.pi+v+x+w+y+kappa*a.b+ZeroPrimary.unsigned e := by
  let i := tailChart e.branch.type
  let z := max (-w) 0+max (-y) 0
  let c := strengthenedWeight i z
  have hz : z∈Icc 0 frameCap := ⟨by dsimp [z]; positivity,hcap⟩
  have hcBounds := strengthened_bounds i hz
  have hc : 0≤c := by dsimp [c]; linarith [hcBounds.1]
  have hcu : c≤kappa := hcBounds.2.1
  have heBounds := tailChart_weight_bounds i
  have hABdual := (AB_delete a b ab hv).trans
    (zeroDual_le_error a b ab (ABweight_positive hv).le hAB)
  have hBTdual := actual_aligned_charge b t hT hx hBT
  have hTDdual := (retain_zero t d td hw hc hcu).trans
    (zeroDual_le_error t d td hc hTD)
  have hDEdual := (retain_DE d e jD hd he hjD hy heBounds.1.le heBounds.2 hordinary).trans
    (quarterDual_le_error d e jD heBounds.1.le hDE)
  have hstrict := reduced_de2_strict b t d e td ht hd he
    (r := 0) (by norm_num) (le_max_right (-w) 0) (le_max_right (-y) 0)
    (by simpa only [zero_add] using hcap)
  rw [transverse_of_nonneg a ha] at hABdual
  dsimp [reducedDE2Tail] at hstrict
  simp only [zero_add,neg_zero] at hstrict
  dsimp [retainedNegative,c,z,i] at hTDdual hDEdual
  linarith

theorem core_path (a b t d e : State) (ab td : Bool) {v x w u : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0)
    (hT : t.branch.type≠0) (hcore : e.branch.type=0)
    (hv : |v|≤frameCap) (hx : x∈Icc 0 frameCap) (hw : |w|≤frameCap)
    (hu : u∈Icc 0 frameCap) (hcap : max (-w) 0+u≤frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v (leftOwner ab))
    (hBT : GlobalOuterAnchor.width x≤projection true b t x 1)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width (-u)≤projection true d e (-u) 3) :
    pathThreshold<Real.pi+v+x+w-u+kappa*a.b+ZeroPrimary.unsigned e := by
  have hs : max (-w) 0∈Icc 0 frameCap := negative_part_range hw
  have hc := CoreDE3.weight_pos hs
  have hcu := (CoreDE3.weight_bounds hs).2.2
  have heWeight : 0≤CoreDE3.endpointWeight u :=
    (show 0≤kappa by norm_num [kappa]).trans (CoreDE3.endpointWeight_bounds hu).1
  have hABdual := (AB_delete a b ab hv).trans
    (zeroDual_le_error a b ab (ABweight_positive hv).le hAB)
  have hBTdual := actual_aligned_charge b t hT hx hBT
  have hTDdual := (retain_zero t d td hw hc.le hcu).trans
    (zeroDual_le_error t d td hc.le hTD)
  have hDEdual := quarterDual_le_error d e 3 heWeight hDE
  have hscalar := CoreDE3.tail_strict td (r := 0) (by norm_num) hs.1 hu.1
    (by simpa only [zero_add] using hcap)
  have hsupport := CoreDE3.support b t d e td (c := CoreDE3.weight (max (-w) 0)) (r := 0)
    ht hd he hcore (by norm_num [frameCap]) hs hu
  simp only [zero_add] at hscalar
  have hstrict := hscalar.trans_le hsupport
  rw [transverse_of_nonneg a ha] at hABdual
  dsimp [CoreDE3.reduced] at hstrict
  simp only [neg_zero] at hstrict
  dsimp [retainedNegative] at hTDdual
  linarith

theorem ceiling_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hpositive : 0≤delta F.theta B) : False := by
  obtain ⟨L⟩ := lowSource F hE 1 (Or.inr rfl) hBT
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hx : delta F.theta B∈Icc 0 frameCap :=
    ⟨hpositive,(le_abs_self (delta F.theta B)).trans (hdelta B)⟩
  have hcap : max (-delta F.theta T) 0+max (-delta F.theta D) 0≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    rw [max_eq_right (show -delta F.theta B≤0 by linarith),zero_add] at hh
    exact hh
  have hpath : pathThreshold<tailCharge C F.theta := by
    by_cases ho : L.DE=2 ∨ 0≤delta F.theta D ∨ (stateOf C E).branch.type≠0
    · exact ordinary_path (stateOf C A) (stateOf C B) (stateOf C T) (stateOf C D)
        (stateOf C E) L.AB L.TD L.DE L.A_positive L.T_positive L.D_negative L.E_negative
        L.T_outer (hdelta A) hx (hdelta T) (hdelta D) hcap L.DE_owner ho
        L.AB_projection L.BT_projection L.TD_projection L.DE_projection
    · have hnotTwo : L.DE≠2 := fun h => ho (Or.inl h)
      have hnegative : delta F.theta D<0 := by
        exact lt_of_not_ge (fun h => ho (Or.inr (Or.inl h)))
      have hcore : (stateOf C E).branch.type=0 := by
        by_contra hn
        exact ho (Or.inr (Or.inr hn))
      have hDE3 := L.DE_owner.resolve_left hnotTwo
      have hu : -delta F.theta D∈Icc 0 frameCap :=
        ⟨by linarith,(neg_le_abs (delta F.theta D)).trans (hdelta D)⟩
      have hcap' : max (-delta F.theta T) 0+(-delta F.theta D)≤frameCap := by
        simpa only [max_eq_left (show 0≤-delta F.theta D by linarith)] using hcap
      have hh := core_path (stateOf C A) (stateOf C B) (stateOf C T) (stateOf C D)
        (stateOf C E) L.AB L.TD L.A_positive L.T_positive L.D_negative L.E_negative
        L.T_outer hcore (hdelta A) hx (hdelta T) hu hcap'
        L.AB_projection L.BT_projection L.TD_projection
        (by simpa only [neg_neg,hDE3] using L.DE_projection)
      simpa only [tailCharge,sub_neg_eq_add] using hh
  exact (not_lt_of_ge (frame_tail_cap F hE L.A_tangent.le).le) hpath

end SquaresInCircles.Eight.GlobalBT.OnePositive
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open Candidate FramePair

theorem ceiling_BT0_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 0).Feasible (C.square B) (C.square T)) : False := by
  obtain ⟨j,hj⟩ := F.forward_complete D (C.selected D) (C.feasible D)
  have hDE : (forwardAxis j).Feasible (C.square D) (C.square E) := hj ▸ C.feasible D
  by_cases htwo : j=2
  · exact ceiling_BT0_ordinary_false F hE hBT j hDE (Or.inl htwo)
  by_cases hpositive : 0≤delta F.theta D
  · exact ceiling_BT0_ordinary_false F hE hBT j hDE (Or.inr (Or.inl hpositive))
  by_cases houter : C.kind E=.outer
  · exact ceiling_BT0_ordinary_false F hE hBT j hDE (Or.inr (Or.inr houter))
  have howner := (GlobalQuarterSign.frame_DE F (by norm_num [Q0]) hE).2 j hDE
  have hthree : j=3 := howner.resolve_left htwo
  have hDE3 : (forwardAxis 3).Feasible (C.square D) (C.square E) := by
    simpa only [hthree] using hDE
  exact CoreDE3.ceiling_false F hE hBT hDE3 houter (le_of_lt (lt_of_not_ge hpositive))

/-- This complete original-axis exclusion has only the intrinsic
nonpositive-E chart condition.  Every tail branch is proved above. -/
theorem frame_BT0_false {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hBT : (forwardAxis 0).Feasible (C.square B) (C.square T)) : False := by
  let K := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C K := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame K := FramePhysicalTransport.candidatePushforward F hR le_rfl
  apply ceiling_BT0_false F'
  · simpa only [hR.same_tangents] using hE
  · simpa [B,T,next] using hR.preserves_all_axes B (forwardAxis 0)
      (by simpa [B,T,next] using hBT)

end SquaresInCircles.Eight.GlobalBT
end
end
end
