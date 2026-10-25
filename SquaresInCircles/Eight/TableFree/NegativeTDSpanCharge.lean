module

public import SquaresInCircles.Eight.TableFree.TD0Span
public import SquaresInCircles.Eight.TableFree.PowerTailBounds
public import SquaresInCircles.Eight.TableFree.NegativeTEntry
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# The actual negative-TD charge dominates the middle norm

Uncompiled source. A positive-square comparison replaces the third-
derivative calculation by one factored rational polynomial on [0,.3].
Its exact coefficient identities and positive reserves are specified for
kernel reduction, which has not been executed. The original T coordinate
bounds are derived from BT2, TD2 and true-core avoidance.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.NegativeTDSpanCharge
open Polynomial SpanNormBounds TD0Span

def J (z : ℝ) : ℝ := (13/12)*Real.sin z-(2/5)*(1-Real.cos z)

def S5 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5
def S7 : ℚ[X] := S5-C (1/5040)*X^7
def lowerA : ℚ[X] := C (13/12)*S7+C (3/5)*(C (1/2)*X^2-C (1/24)*X^4)
def upperA : ℚ[X] := C (13/12)*S5+C (3/10)*X^2
def numerator : ℚ[X] :=
  C (2*(1978787/1000000)*(596343/500000))*lowerA-
    C (2*(9789/2500)*(13/20))*S5-upperA^2
def quotient : ℚ[X] := ∑ i : Fin 10,C (numerator.coeff (i.val+1))*X^i.val

/-! ### Kernel certificate

`numerator` is represented by a scaled integer coefficient list
(`WholeIntervalPolynomial.Certificate`) built to mirror its definition;
`quotient` is its `divX`, and the reserves are integer inequalities checked by
the kernel. -/

open WholeIntervalPolynomial.Certificate in
private theorem r60_repC (n : ℤ) (d : ℕ) {q : ℚ} (hd : d≠0) (h : q=n/d) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [h]
  field_simp

open WholeIntervalPolynomial.Certificate in
private def r60_S5S : Scaled :=
  (Scaled.var.sub ((⟨[1],6⟩ : Scaled).mul (Scaled.var.pow 3))).add
    ((⟨[1],120⟩ : Scaled).mul (Scaled.var.pow 5))

open WholeIntervalPolynomial.Certificate in
private theorem r60_rep_S5 : r60_S5S.Rep S5 :=
  (Scaled.rep_var.sub ((r60_repC 1 6 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 3))).add
    ((r60_repC 1 120 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 5))

open WholeIntervalPolynomial.Certificate in
private def r60_numS : Scaled :=
  (((⟨[1180035775941],250000000000⟩ : Scaled).mul
      (((⟨[13],12⟩ : Scaled).mul (r60_S5S.sub ((⟨[1],5040⟩ : Scaled).mul (Scaled.var.pow 7)))).add
        ((⟨[3],5⟩ : Scaled).mul (((⟨[1],2⟩ : Scaled).mul (Scaled.var.pow 2)).sub
          ((⟨[1],24⟩ : Scaled).mul (Scaled.var.pow 4)))))).sub
    ((⟨[127257],25000⟩ : Scaled).mul r60_S5S)).sub
    ((((⟨[13],12⟩ : Scaled).mul r60_S5S).add ((⟨[3],10⟩ : Scaled).mul (Scaled.var.pow 2))).pow 2)

open WholeIntervalPolynomial.Certificate in
private theorem r60_rep_num : r60_numS.Rep numerator :=
  (((r60_repC 1180035775941 250000000000 (by norm_num) (by norm_num)).mul
      (((r60_repC 13 12 (by norm_num) (by norm_num)).mul (r60_rep_S5.sub
        ((r60_repC 1 5040 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 7)))).add
        ((r60_repC 3 5 (by norm_num) (by norm_num)).mul (((r60_repC 1 2 (by norm_num)
          (by norm_num)).mul (Scaled.rep_var.pow 2)).sub ((r60_repC 1 24 (by norm_num)
          (by norm_num)).mul (Scaled.rep_var.pow 4)))))).sub
    ((r60_repC 127257 25000 (by norm_num) (by norm_num)).mul r60_rep_S5)).sub
    ((((r60_repC 13 12 (by norm_num) (by norm_num)).mul r60_rep_S5).add
      ((r60_repC 3 10 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))).pow 2)

/-- The integer facts about the numerator list, computed once by the kernel. -/
private theorem r60_facts :
    r60_numS.s≠0 ∧ r60_numS.l.length≤11 ∧ r60_numS.l.getD 0 0=0 ∧
      (r60_numS.s:ℤ)<50*r60_numS.l.tail.getD 0 0 ∧
      0<r60_numS.l.tail.getD 1 0*((10:ℕ):ℤ)^8-∑ j : Fin 8,|r60_numS.l.tail.getD (j.val+2) 0| *
        ((3:ℕ):ℤ)^(j.val+1)*((10:ℕ):ℤ)^(8-1-j.val) := by
  decide +kernel

private theorem r60_quotient_eq : quotient=numerator.divX := by
  have hdeg : numerator.natDegree≤10 :=
    (r60_rep_num.natDegree_le r60_facts.1).trans (by have := r60_facts.2.1; omega)
  ext n
  rw [coeff_divX,quotient,finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Fin.sum_univ_eq_sum_range (fun i => if n=i then numerator.coeff (i+1) else 0) 10,
    Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt]
    simp only [Finset.mem_range,not_lt] at h
    omega

open WholeIntervalPolynomial.Certificate in
private theorem r60_coeff_sub_norm {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (j0 k n a m : ℕ) (hm : 0 < m) :
    p.coeff j0-PowerTailBounds.norm p k n ((a:ℚ)/m)=
      ((c.l.getD j0 0*(m:ℤ)^n-∑ j : Fin n,|c.l.getD (j.val+k) 0| *(a:ℤ)^(j.val+1)*
        (m:ℤ)^(n-1-j.val) : ℤ):ℚ)/((c.s*m^n:ℕ):ℚ) := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hm' : (0:ℚ) < m := by exact_mod_cast hm
  unfold PowerTailBounds.norm
  simp only [hc.coeff hs]
  push_cast
  rw [sub_div,Finset.sum_div]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj := j.isLt
    have hpow : (m:ℚ)^n=m^(n-1-j.val)*m^(j.val+1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [abs_div,abs_of_pos hs',hpow,div_pow]
    field_simp

open WholeIntervalPolynomial.Certificate in
theorem polynomial_identities :
    X*quotient=numerator ∧
      quotient=C (quotient.coeff 0)+C (quotient.coeff 1)*X+
        PowerTailBounds.tail quotient 2 8 := by
  have h0 : numerator.coeff 0=0 := by
    rw [r60_rep_num.coeff r60_facts.1,r60_facts.2.2.1]
    simp
  refine ⟨?_,?_⟩
  · have h := divX_mul_X_add numerator
    rw [h0,map_zero,add_zero] at h
    rw [r60_quotient_eq,mul_comm]
    exact h
  · have hdeg : quotient.natDegree<2+8 := by
      have h := r60_rep_num.divX.natDegree_le r60_facts.1
      have hl := r60_facts.2.1
      rw [r60_quotient_eq]
      simp only [Scaled.divX,List.length_tail] at h
      omega
    conv_lhs => rw [quotient.as_sum_range_C_mul_X_pow' hdeg]
    rw [Finset.sum_range_add,PowerTailBounds.tail,
      Fin.sum_univ_eq_sum_range (fun j => C (quotient.coeff (j+2))*X^(j+2)) 8]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]

open WholeIntervalPolynomial.Certificate in
theorem coefficient_reserves :
    (1/50:ℚ)<quotient.coeff 0 ∧
      0<quotient.coeff 1-PowerTailBounds.norm quotient 2 8 (3/10) := by
  obtain ⟨hs,-,-,h1,h2⟩ := r60_facts
  have hq := r60_rep_num.divX
  rw [← r60_quotient_eq] at hq
  refine ⟨?_,?_⟩
  · rw [hq.coeff hs]
    have hs' : (0:ℚ)<r60_numS.s := by exact_mod_cast Nat.pos_of_ne_zero hs
    simp only [Scaled.divX]
    rw [lt_div_iff₀ hs']
    have h1' : ((r60_numS.s:ℤ):ℚ)<((50*r60_numS.l.tail.getD 0 0 : ℤ):ℚ) := Int.cast_lt.mpr h1
    push_cast at h1'
    linarith
  · rw [show (3/10:ℚ)=((3:ℕ):ℚ)/((10:ℕ):ℚ) by norm_num,
      r60_coeff_sub_norm hq hs 1 2 8 3 10 (by norm_num)]
    apply div_pos _ (by exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero hs (by norm_num)))
    exact Int.cast_pos.mpr h2

theorem polynomial_positive {z : ℝ} (hz : z∈Ioc 0 (3/10:ℝ)) :
    0<aeval z numerator := by
  have hlo := PowerTailBounds.linear_lower polynomial_identities.2
    (show (0:ℚ)≤3/10 by norm_num)
    (show |z|≤((3/10:ℚ):ℝ) by rw [abs_of_pos hz.1]; push_cast; exact hz.2)
  rw [abs_of_pos hz.1] at hlo
  have hzero : (1/50:ℝ)<(quotient.coeff 0:ℝ) := by
    have h := coefficient_reserves.1
    have h' : ((1/50:ℚ):ℝ)<(quotient.coeff 0:ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hlinear : 0<(quotient.coeff 1:ℝ)-(PowerTailBounds.norm quotient 2 8 (3/10):ℝ) := by
    have h := coefficient_reserves.2
    rw [← Rat.cast_sub]
    exact_mod_cast h
  have hq : 0<aeval z quotient := by nlinarith [hz.1]
  have he := congrArg (fun p : ℚ[X] => aeval z p) polynomial_identities.1
  simp only [map_mul,aeval_X] at he
  rw [← he]
  exact mul_pos hz.1 hq

theorem lowerA_nonneg {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) :
    0≤aeval z lowerA := by
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz6 := pow_le_pow_left₀ hz.1 hz.2 6
  have hp : 0≤(13/12)*(1-z^2/6+z^4/120-z^6/5040)+
      (3/5)*z*(1/2-z^2/24) := by
    have hm := mul_nonneg hz.1 (show 0≤1/2-z^2/24 by nlinarith)
    nlinarith [pow_nonneg hz.1 4]
  have he : aeval z lowerA=z*((13/12)*(1-z^2/6+z^4/120-z^6/5040)+
      (3/5)*z*(1/2-z^2/24)) := by simp [lowerA,S7,S5]; ring
  rw [he]
  exact mul_nonneg hz.1 hp

/-- A strictly positive original trigonometric charge at every nonzero
angle in the single complete short interval. -/
theorem charge_strict {z : ℝ} (hz : z∈Ioc 0 (3/10:ℝ)) :
    V TD0Span.lambda z<J z := by
  obtain ⟨a,ha⟩ : ∃ a : ℝ,a=(13/12)*Real.sin z+(3/5)*(1-Real.cos z) := ⟨_,rfl⟩
  have hzi : z∈Icc 0 frameCap := ⟨hz.1.le,by simp only [frameCap]; linarith [hz.2]⟩
  have hsi := (transport_trig hzi).2.2.1
  have hcos1 := Real.cos_le_one z
  have ha0 : 0≤a := by rw [ha]; nlinarith
  have hlow : aeval z lowerA≤a := by
    have hs := sin_lower_seven hz.1.le
    have hc := cos_upper_four hz.1.le
    have he : aeval z lowerA=(13/12)*(z-z^3/6+z^5/120-z^7/5040)+
        (3/5)*(z^2/2-z^4/24) := by simp [lowerA,S7,S5]; ring
    rw [he,ha]
    linarith
  have hupp : a≤aeval z upperA := by
    have hs := sin_upper_five hz.1.le
    have hc := Real.one_sub_sq_div_two_le_cos (x := z)
    have he : aeval z upperA=(13/12)*(z-z^3/6+z^5/120)+(3/10)*z^2 := by
      simp [upperA,S5]; ring
    rw [he,ha]
    linarith
  have halow0 := lowerA_nonneg ⟨hz.1.le,hz.2⟩
  have hs5 : Real.sin z≤aeval z S5 := by
    have he : aeval z S5=z-z^3/6+z^5/120 := by simp [S5]; ring
    rw [he]
    exact sin_upper_five hz.1.le
  have hN0 := fixed_norm_bounds.1
  have hR0 : 0<R := by linarith [radius_bounds.1]
  have hcoeff : (2*(1978787/1000000)*(596343/500000):ℝ)≤
      2*R*N TD0Span.lambda 0 := by
    have hmul := mul_le_mul radius_bounds.1.le hN0.le (by norm_num) hR0.le
    simp only [TD0Span.lambda]
    linarith
  have hmain := mul_le_mul hcoeff hlow halow0 (by positivity : 0≤2*R*N TD0Span.lambda 0)
  have hsin := mul_le_mul_of_nonneg_left hs5
    (show 0≤2*qCap*TD0Span.lambda by norm_num [qCap,TD0Span.lambda])
  have hasq := pow_le_pow_left₀ ha0 hupp 2
  have hp := polynomial_positive hz
  have hpos : 0<2*R*N TD0Span.lambda 0*a-
      2*qCap*TD0Span.lambda*Real.sin z-a^2 := by
    simp only [numerator,map_sub,map_mul,map_pow,aeval_C,eq_ratCast] at hp
    push_cast at hp
    simp only [qCap,TD0Span.lambda] at hsin ⊢
    linarith
  have hzabs : |-z|≤frameCap := by rw [abs_neg,abs_of_pos hz.1]; exact hzi.2
  have hNsq := N_sq (show (0:ℝ)<TD0Span.lambda by norm_num [TD0Span.lambda]) hzabs
  have hN0sq := N_sq (show (0:ℝ)<TD0Span.lambda by norm_num [TD0Span.lambda])
    (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hn2 : (R*N TD0Span.lambda (-z))^2=
      qCap*(1+TD0Span.lambda^2-2*TD0Span.lambda*Real.sin z) := by
    rw [mul_pow,hR2,hNsq,Real.sin_neg]
    ring
  have hn02 : (R*N TD0Span.lambda 0)^2=qCap*(1+TD0Span.lambda^2) := by
    rw [mul_pow,hR2,hN0sq,Real.sin_zero]
    ring
  have hnonneg : 0≤R*N TD0Span.lambda (-z) := mul_nonneg hR0.le (Real.sqrt_nonneg _)
  have hgain : R*N TD0Span.lambda 0-a<R*N TD0Span.lambda (-z) := by
    by_contra! hbad
    have hsquare := pow_le_pow_left₀ hnonneg hbad 2
    have hexp : (R*N TD0Span.lambda 0-a)^2=
        (R*N TD0Span.lambda 0)^2-2*R*N TD0Span.lambda 0*a+a^2 := by ring
    linarith
  have hV : V TD0Span.lambda z=(Real.cos z-1)-
      (R*N TD0Span.lambda (-z)-R*N TD0Span.lambda 0) := by
    simp only [SpanNormBounds.V,OrdinaryAngleConcavity.V,SpanNormBounds.N]
    ring
  rw [hV,J]
  linarith

theorem charge_lower {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) :
    V TD0Span.lambda z≤J z := by
  rcases eq_or_lt_of_le hz.1 with hz0 | hz0
  · simp [← hz0,J,SpanNormBounds.V,OrdinaryAngleConcavity.V]
  · exact (charge_strict ⟨hz0,hz.2⟩).le

/-- The short interval and true-core primary bound follow from actual
BT2/TD2. The point need not lie on a radial boundary. -/
theorem actual_negative_cuts {q z v : ℝ} {B T D : SignedPoint}
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBc : B.Contained q) (hDc : D.Contained q)
    (hTc : T.AvoidsCore) (hDc0 : D.AvoidsCore) (hq : q≤qCap)
    (hyD : D.y≤0) (hz : z∈Ioc 0 frameCap)
    (hBT : quarterFeasible B T v 2) (hTD : zeroFeasible T D (-z) 2) :
    1/10<T.y ∧ T.y<83/200 ∧ 7/12≤T.a ∧ z<3/10 := by
  obtain ⟨hy,hyu,hsum,hyD'⟩ := NegativeTEntry.negative_TD_signs
    hBs hTs hDs hBc hDc hDc0 hq hyD hz hBT hTD
  have hDu := (SignedPoint.coordinate_bounds hDs hDc0 hDc hq).2.2
  rw [abs_of_nonpos hyD] at hDu
  have hyl : 1/10<T.y := by linarith
  have haHalf := SignedPoint.primary_gt_half hTs hTc
  have hcore := hTc
  simp only [SignedPoint.AvoidsCore,SignedPoint.coreDistance,abs_of_pos hy,
    max_eq_left (by linarith : 0≤T.a-1/2),max_eq_right (by linarith : T.y-1/2≤0)] at hcore
  have ha : 7/12≤T.a := by nlinarith
  have hzi : z∈Icc 0 frameCap := ⟨hz.1.le,hz.2⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hzi
  have h1 := mul_le_mul_of_nonneg_right ha hs0
  have h2 := mul_lt_mul_of_pos_right hyu (show 0<Real.cos z by linarith)
  have hh : edgeWidth (-z)≤T.a*Real.sin (-z)+T.y*Real.cos (-z)-D.y := hTD
  rw [edgeWidth_negative_formula hzi,Real.sin_neg,Real.cos_neg] at hh
  have hmargin : (17/200)*Real.cos z+(13/12)*Real.sin z<2/5 := by linarith
  have hshort : z<3/10 := by
    by_contra! hbad
    have hm := NegativeTEntry.TD_short_harmonic_mono.monotoneOn
      (⟨by norm_num,by norm_num [frameCap]⟩ : (3/10:ℝ)∈Icc 0 frameCap) hzi hbad
    have hc3 := cos_lower_six (show (0:ℝ)≤3/10 by norm_num)
    have hs3 := sin_lower_seven (show (0:ℝ)≤3/10 by norm_num)
    norm_num at hc3 hs3 hm
    linarith
  exact ⟨hyl,hyu,ha,hshort⟩

end SquaresInCircles.Eight.TableFree.NegativeTDSpanCharge
