module

public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTCoefficients
public import SquaresInCircles.Eight.TableFree.SolePositiveTGrowth
public import SquaresInCircles.Eight.TableFree.SolePositiveTSameBlock
public import SquaresInCircles.Eight.TableFree.ExceptionalSmallGap
public import SquaresInCircles.Eight.TableFree.WholeIntervalBernstein
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Ordinary-angle growth for the positive-T contact families

Uncompiled source. These are the low fixed-ratio chord, middle balanced
and one-angle slopes, and high .71-ratio quartic in section 5 of the
outside-strip proof. The actual negative coefficient is retained until
its scalar comparison. All derivative transfers use the original R.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTGrowth
open Polynomial WholeIntervalPolynomial
open WholeIntervalPolynomial.Certificate (Scaled lowerOn_eq_of_rep)

def lowerRadius : ℚ := 19787/10000

def ratioPolynomial : ℚ[X] :=
  C (lowerRadius^2)*X^2*C ((478/625)^2)-
    (X+C (6443/10000))^2*(1+X^2-C (3221/2500)*X)

private def r54Ratio : Scaled :=
  Scaled.sub
    ((((Scaled.const (19787/10000)).pow 2).mul (Scaled.var.pow 2)).mul
      ((Scaled.const (478/625)).pow 2))
    (((Scaled.var.add (Scaled.const (6443/10000))).pow 2).mul
      (((Scaled.ofNat 1).add (Scaled.var.pow 2)).sub ((Scaled.const (3221/2500)).mul Scaled.var)))

private theorem r54Ratio_rep : r54Ratio.Rep ratioPolynomial := by
  have h := (((((Scaled.rep_const (19787/10000)).pow 2).mul (Scaled.rep_var.pow 2)).mul
      ((Scaled.rep_const (478/625)).pow 2))).sub
    (((Scaled.rep_var.add (Scaled.rep_const (6443/10000))).pow 2).mul
      ((Scaled.rep_one.add (Scaled.rep_var.pow 2)).sub
        ((Scaled.rep_const (3221/2500)).mul Scaled.rep_var)))
  have e : ratioPolynomial=C (19787/10000)^2*X^2*C (478/625)^2-
      (X+C (6443/10000))^2*(1+X^2-C (3221/2500)*X) := by
    simp only [ratioPolynomial,lowerRadius,map_pow]
  rw [e]
  exact h

theorem ratio_identity :
    centered (71/100) 1 ratioPolynomial=
      expansion 4 (centered (71/100) 1 ratioPolynomial) :=
  (r54Ratio_rep.centered 1 200 171 29 (by norm_num) (by norm_num) (by norm_num)).eq_expansion
    (by decide +kernel) (by decide +kernel)

theorem ratio_reserve : (13/250:ℚ)<lowerOn 4 (71/100) 1 ratioPolynomial := by
  rw [lowerOn_eq_of_rep (r54Ratio_rep.centered 1 200 171 29 (by norm_num) (by norm_num)
    (by norm_num)) (by decide +kernel) (by decide +kernel)]
  decide +kernel

open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryAngleConcentration OrdinaryNegativeSlope OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison SingleAngleConcavity

theorem radius_le {R : ℝ} (hR : 0≤R) (hQ : qLow≤R^2) :
    (lowerRadius:ℝ)≤R := by
  have h := SoleAngleGrowth.radius_lower hR hQ
  have e : ((lowerRadius:ℚ):ℝ)=19787/10000 := by norm_num [lowerRadius]
  linarith

theorem ratio_square {r : ℝ} (hr : r∈Icc (71/100:ℝ) 1) :
    (13/250:ℝ)<(lowerRadius:ℝ)^2*r^2*(478/625)^2-
      (r+6443/10000)^2*(1+r^2-2*r*(3221/5000)) := by
  have h := positive_on_interval (by norm_num : (71/100:ℚ)<1)
    ratio_identity ratio_reserve (x := r) (by simpa using hr)
  norm_num [ratioPolynomial,lowerRadius] at h ⊢
  nlinarith

theorem normalized_high_slope {R r : ℝ}
    (hR : 0≤R) (hQ : qLow≤R^2) (hr : r∈Icc (71/100:ℝ) 1) :
    r< -Real.sin frameCap+R*r*Real.cos frameCap/root r (Real.sin frameCap) := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hs := transport_trig hh
  have hN := root_pos r (sin_mem hh)
  have hN2 := root_sq r (sin_mem hh)
  have hr0 : 0<r := by linarith [hr.1]
  have hS : Real.sin frameCap≤6443/10000 := hs.2.2.2.1.le
  have hC : (478/625:ℝ)≤Real.cos frameCap := by linarith [hs.1]
  have hD : (root r (Real.sin frameCap))^2≤
      1+r^2-2*r*(3221/5000) := by
    nlinarith [mul_le_mul_of_nonneg_left cap_sin_lower.le hr0.le]
  have hDmul := mul_le_mul_of_nonneg_left hD (sq_nonneg (r+6443/10000))
  have hpoly := ratio_square hr
  have hcross0 : (r+6443/10000)*root r (Real.sin frameCap)<
      (lowerRadius:ℝ)*r*(478/625) := by
    have hp : 0≤(lowerRadius:ℝ)*r*(478/625) := by
      exact mul_nonneg (mul_nonneg (by norm_num [lowerRadius]) hr0.le) (by norm_num)
    nlinarith
  have hleft := mul_le_mul_of_nonneg_right
    (by linarith : r+Real.sin frameCap≤r+6443/10000) hN.le
  have hright := mul_le_mul
    (mul_le_mul_of_nonneg_right (radius_le hR hQ) hr0.le) hC
    (by norm_num : (0:ℝ)≤478/625) (mul_nonneg hR hr0.le)
  have hcross : (r+Real.sin frameCap)*root r (Real.sin frameCap)<
      R*r*Real.cos frameCap := hleft.trans_lt (hcross0.trans_le hright)
  linarith [(lt_div_iff₀ hN).2 hcross]

theorem Vd_gt_smaller {R p q t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (71/100)*q≤p)
    (ht : t∈Icc 0 frameCap) : p<Vd R p q t := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (71/100:ℝ) 1 :=
    ⟨(le_div_iff₀ hq).2 hratio,(div_le_one hq).2 hpq⟩
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hbase := mul_lt_mul_of_pos_left (normalized_high_slope hR hQL hr) hq
  have hcancel : q*(p/q)=p := by field_simp [hq.ne']
  rw [hcancel,← Vd_normalized hq] at hbase
  exact hbase.trans_le ((Vd_antitone hR hQU hp hpq (by linarith)) ht hh ht.2)

theorem VnuDeriv_antitone {R p q nu : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hnu : p≤nu) :
    AntitoneOn (VnuDeriv R p q nu) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro x hx
    exact (VnuDeriv_hasDerivAt hp (hp.trans_le hpq) hx).continuousAt.continuousWithinAt
  · intro x hx
    exact VnuDeriv_hasDerivAt hp (hp.trans_le hpq) (Ioo_subset_Icc_self hx)
  · intro x hx
    linarith [Vnu_second_lt hR hQU hp hpq hqp hnu (Ioo_subset_Icc_self hx)]

theorem VnuDeriv_ge_Vd {R p q nu t : ℝ} (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) : Vd R p q t≤VnuDeriv R p q nu t := by
  have h := mul_le_mul_of_nonneg_right hnu (transport_trig ht).2.2.1
  dsimp [Vd,mixedNDerivative,VnuDeriv]
  simp only [zero_sub]
  linarith

theorem high_growth {R p q nu t u : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (71/100)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    p*(u-t)≤Vnu R p q nu u-Vnu R p q nu t := by
  apply derivative_reserve
    (fun x hx => (Vnu_hasDerivAt hp (hp.trans_le hpq) hx).continuousAt.continuousWithinAt)
    (fun x hx => Vnu_hasDerivAt hp (hp.trans_le hpq) (Ioo_subset_Icc_self hx))
    (fun x hx => ?_) ht hu htu
  exact (Vd_gt_smaller hR hQL hQU hp hpq hratio (Ioo_subset_Icc_self hx)).le.trans
    (VnuDeriv_ge_Vd hnu (Ioo_subset_Icc_self hx))

theorem low_growth {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (117/200)*q≤p)
    (hq : 431/500≤q) (hnu : nu≤q) (ht : t∈Icc 0 (9/50:ℝ)) :
    (431/500)*(7/10)*(frameCap-t)≤Vnu R p q nu frameCap-Vnu R p q nu t := by
  have hq0 := hp.trans_le hpq
  have hbase := ExceptionalSmallGap.fixed_gap hR hQL hQU ht
  have hlen : 0≤frameCap-t := by dsimp [frameCap]; linarith [ht.2]
  have hpositive : 0≤V R (117/200) 1 frameCap-V R (117/200) 1 t := by
    dsimp [ExceptionalSmallGap.ratio] at hbase
    simp only [frameCap] at hbase hlen ⊢
    linarith
  have hscale := mul_le_mul_of_nonneg_right hq hpositive
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  have htransfer := derivative_reserve
    (f:=fun s => Vnu R p q nu s-q*V R (117/200) 1 s)
    (df:=fun s => VnuDeriv R p q nu s-q*Vd R (117/200) 1 s) (k:=0)
    (fun s hs => ((Vnu_hasDerivAt hp hq0 hs).sub
      ((V_hasDerivAt (by norm_num) (by norm_num) hs).const_mul q)).continuousAt.continuousWithinAt)
    (fun s hs => (Vnu_hasDerivAt hp hq0 (Ioo_subset_Icc_self hs)).sub
      ((V_hasDerivAt (by norm_num) (by norm_num) (Ioo_subset_Icc_self hs)).const_mul q))
    (fun s hs => sub_nonneg.mpr
      ((ExceptionalSmallGap.derivative_ratio hR hq0 hpq hratio (Ioo_subset_Icc_self hs)).trans
        (VnuDeriv_ge_Vd hnu (Ioo_subset_Icc_self hs))))
    ht' (by norm_num [frameCap]) ht'.2
  dsimp [ExceptionalSmallGap.ratio] at hbase
  nlinarith

def balancedPolynomial : ℚ[X] :=
  C (lowerRadius^2*(2/3)^2)*(1-X^2)-
    (X+C (337/500))^2*(C (1+(2/3)^2)-C (4/3)*X)
private theorem r54_balanced_explicit : balancedPolynomial=
    C (81295223/75000000)+C (-754543/562500)*X+C (-312125369/225000000)*X^2+C (4/3)*X^3 := by
  apply Polynomial.funext
  intro r
  simp only [balancedPolynomial,lowerRadius,eval_sub,eval_mul,eval_C,eval_pow,eval_add,eval_X,
    eval_one]
  ring
private theorem r54_balanced_coeff (j : ℕ) : balancedPolynomial.coeff j=
    if j=0 then 81295223/75000000 else if j=1 then -754543/562500 else
      if j=2 then -312125369/225000000 else if j=3 then 4/3 else 0 := by
  rw [r54_balanced_explicit]
  simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_C,coeff_X]
  rcases j with _ | _ | _ | _ | j <;> simp
theorem balanced_identity : balancedPolynomial=
    WholeIntervalBernstein.expansion 3 (6443/10000) balancedPolynomial := by
  apply Polynomial.funext
  intro r
  simp only [WholeIntervalBernstein.expansion,WholeIntervalBernstein.coefficient,
    WholeIntervalBernstein.basis,r54_balanced_coeff,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Fin.val_zero,Fin.val_succ,zero_add,Finset.sum_range_succ,Finset.sum_range_zero,add_zero]
  rw [r54_balanced_explicit]
  simp only [eval_add,eval_mul,eval_C,eval_pow,eval_X,eval_sub]
  norm_num [Nat.choose]
  ring
theorem balanced_partition :
    (∑i : Fin 4,WholeIntervalBernstein.basis 3 (6443/10000) i)=1 := by
  apply Polynomial.funext
  intro r
  simp only [WholeIntervalBernstein.basis,Fin.sum_univ_four,eval_add,eval_mul,eval_C,eval_pow,
    eval_X,eval_sub,eval_one,Fin.val_zero,Fin.val_one,Fin.val_two,Fin.isValue]
  norm_num [Nat.choose]
  ring
theorem balanced_reserve (i : Fin 4) :
    (1/100000:ℚ)≤WholeIntervalBernstein.coefficient 3 (6443/10000) balancedPolynomial i := by
  fin_cases i <;>
    simp only [WholeIntervalBernstein.coefficient,r54_balanced_coeff,Finset.sum_range_succ,
      Finset.sum_range_zero] <;>
    norm_num [Nat.choose]

theorem balanced_normalized {s : ℝ} (hs : s∈Icc 0 frameCap) :
    (337/500:ℝ)< -Real.sin s+(lowerRadius:ℝ)*(2/3)*Real.cos s/
      root (2/3) (Real.sin s) := by
  have hsin : Real.sin s∈Icc (0:ℝ) (6443/10000) :=
    ⟨(transport_trig hs).2.2.1,(transport_trig hs).2.2.2.1.le⟩
  have hpoly := WholeIntervalBernstein.lower_on_interval (by norm_num)
    balanced_identity balanced_partition balanced_reserve (x := Real.sin s) (by simpa using hsin)
  have hN := root_pos (2/3) (sin_mem hs)
  have hN2 := root_sq (2/3) (sin_mem hs)
  have hcos : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hcross : (337/500+Real.sin s)*root (2/3) (Real.sin s)<
      (lowerRadius:ℝ)*(2/3)*Real.cos s := by
    norm_num [balancedPolynomial,lowerRadius] at hpoly
    have hright : 0<(lowerRadius:ℝ)*(2/3)*Real.cos s := by
      exact mul_pos (by norm_num [lowerRadius]) hcos
    have hB2 : ((337/500+Real.sin s)*root (2/3) (Real.sin s))^2=
        (Real.sin s+337/500)^2*(13/9-4/3*Real.sin s) := by
      rw [mul_pow,hN2]
      ring
    have hA2 : ((lowerRadius:ℝ)*(2/3)*Real.cos s)^2=
        391525369/225000000*(1-Real.sin s^2) := by
      rw [mul_pow,Real.cos_sq']
      norm_num [lowerRadius]
    nlinarith [hA2,hB2,hpoly,hright]
  linarith [(lt_div_iff₀ hN).2 hcross]

theorem balanced_growth {R p q nu t u : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : 0<p) (hpq : p≤q) (hratio : (2/3)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    (337/500)*q*(u-t)≤Vnu R p q nu u-Vnu R p q nu t := by
  have hq := hp.trans_le hpq
  have hbase := derivative_reserve
    (f:=V (lowerRadius:ℝ) (2/3) 1) (df:=Vd (lowerRadius:ℝ) (2/3) 1)
    (k:=337/500)
    (fun x hx => (V_hasDerivAt (by norm_num) (by norm_num) hx).continuousAt.continuousWithinAt)
    (fun x hx => V_hasDerivAt (by norm_num) (by norm_num) (Ioo_subset_Icc_self hx))
    (fun x hx => by
      rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
      simpa only [div_one,one_mul] using (balanced_normalized (Ioo_subset_Icc_self hx)).le)
    ht hu htu
  have hscale := mul_le_mul_of_nonneg_left hbase hq.le
  have htransfer := SolePositiveTGrowth.normalized_growth (radius_le hR hQL) hp hpq
    (by norm_num : (0:ℝ)<2/3) hratio hnu ht hu htu
  have e : ((SolePositiveTGrowth.lowerRadius:ℚ):ℝ)=(lowerRadius:ℝ) := by
    norm_num [SolePositiveTGrowth.lowerRadius,lowerRadius]
  rw [e] at htransfer
  nlinarith

theorem middle_A_endpoint {R p q : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : 159/250≤p) (hq : 0<q) (hr : p/q∈Icc (31/50:ℝ) (203/250)) :
    (4/5:ℝ)<VnuDeriv R p q p frameCap := by
  let r : ℝ := p/q
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := root_pos r (sin_mem hh)
  have hN2 := root_sq r (sin_mem hh)
  have hr0 : 0≤r := by dsimp [r]; linarith [hr.1]
  have hproduct := mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  have hsin := mul_le_mul_of_nonneg_left cap_sin_lower.le hr0
  have hNupper : root r (Real.sin frameCap)≤393/500 := by
    have hsq : (root r (Real.sin frameCap))^2≤(393/500)^2 := by
      dsimp only [r] at hN2 hsin hr0 ⊢
      nlinarith [hproduct,hr.2]
    nlinarith [hN]
  have hc : (478/625:ℝ)≤Real.cos frameCap := by linarith [(transport_trig hh).1]
  have hs := (transport_trig hh).2.2.2.1.le
  have hnum : (lowerRadius:ℝ)*(478/625)≤R*Real.cos frameCap :=
    mul_le_mul (radius_le hR hQL) hc (by norm_num) hR
  let k : ℝ := (lowerRadius:ℝ)*(478/625)/(393/500)
  have hk0 : 0≤k := by norm_num [k,lowerRadius]
  have hprod := mul_le_mul_of_nonneg_left hNupper hk0
  have hfraction : k≤R*Real.cos frameCap/root r (Real.sin frameCap) := by
    apply (le_div_iff₀ hN).2
    dsimp [k] at hprod ⊢
    nlinarith
  have hbracket : k-6443/10000≤
      -Real.sin frameCap+R*Real.cos frameCap/root r (Real.sin frameCap) := by linarith
  have hpositive : 0≤k-6443/10000 := by norm_num [k,lowerRadius]
  have hmul := mul_le_mul hp hbracket hpositive (by linarith : 0≤p)
  have hreserve : (4/5:ℝ)<(159/250)*(k-6443/10000) := by norm_num [k,lowerRadius]
  have he : VnuDeriv R p q p frameCap=
      p*(-Real.sin frameCap+R*Real.cos frameCap/root r (Real.sin frameCap)) := by
    dsimp [VnuDeriv,normD1,pairProduct,r]
    rw [Real.cos_neg,negativeNorm_normalized hq]
    field_simp [hq.ne']
  rw [he]
  exact hreserve.trans_le hmul

theorem middle_A_growth {R p q t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 159/250≤p) (hpq : p≤q) (hr : p/q∈Icc (31/50:ℝ) (203/250))
    (ht : t∈Icc 0 frameCap) :
    (4/5)*(frameCap-t)≤Vnu R p q p frameCap-Vnu R p q p t := by
  have hp0 : 0<p := by linarith
  have hq := hp0.trans_le hpq
  have hqp : q≤2*p := by
    have hh := (le_div_iff₀ hq).1 hr.1
    nlinarith
  have hanti := VnuDeriv_antitone hR hQU hp0 hpq hqp (le_refl p)
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  apply derivative_reserve
    (fun x hx => (Vnu_hasDerivAt hp0 hq hx).continuousAt.continuousWithinAt)
    (fun x hx => Vnu_hasDerivAt hp0 hq (Ioo_subset_Icc_self hx))
    (fun x hx => ?_) ht hh ht.2
  exact (middle_A_endpoint hR hQL hp hq hr).le.trans
    (hanti (Ioo_subset_Icc_self hx) hh hx.2.le)

theorem low_same_block {R p q t : ℝ} (hq : 0≤q)
    (hr : (117/200+1/5*t)*q≤p) (ht : t∈Icc 0 (9/50:ℝ)) :
    V R p q t≤OrdinaryAngleConcentration.M R p q t := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := (transport_trig hh).1
  have hs := (transport_trig hh).2.2.2.1
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  apply SolePositiveTSameBlock.from_bracket hq hr ht'
  apply SolePositiveTSameBlock.half_angle_bracket ht' (by linarith [ht.2])
  have hm := mul_le_mul_of_nonneg_right hc.le
    (show 0≤frameCap-t by linarith [ht'.2])
  dsimp [frameCap] at *
  nlinarith [sq_nonneg t,ht.1,ht.2]

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTGrowth

