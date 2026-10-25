module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowNegative
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# The low G-pair constants before E-angle reduction

Uncompiled transcription of the complete scalar companion, (25)--(27),
and the angle companion, (33)--(34). The lower curvature certificate is
the single degree-sixteen polynomial in x = 1/6 - theta. Its positive
higher coefficients and its completed quadratic are kept explicitly.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowG
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryCurvatureBounds OrdinaryNegativeSlope

namespace Certificate
open Polynomial

def k : ℚ[X] := C (1677/2500)-C (3/20)*X+C 4*X^2
def l : ℚ[X] := C (10073/10000)+C (17/10)*X+C (11/5)*X^2
def reserve : ℚ[X] := C (4*(9789/2500))*k^4*l^4-(k^2+l^2)^3

/-! ### Kernel certificate

`reserve` is represented by a scaled integer coefficient list
(`WholeIntervalPolynomial.Certificate`) built to mirror its definition. -/

open WholeIntervalPolynomial.Certificate in
private theorem r74_repC (n : ℤ) (d : ℕ) {q : ℚ} (hd : d≠0) (h : q=n/d) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [h]
  field_simp

open WholeIntervalPolynomial.Certificate in
private def r74_kS : Scaled :=
  ((⟨[1677],2500⟩ : Scaled).sub ((⟨[3],20⟩ : Scaled).mul Scaled.var)).add
    ((⟨[4],1⟩ : Scaled).mul (Scaled.var.pow 2))

open WholeIntervalPolynomial.Certificate in
private theorem r74_rep_k : r74_kS.Rep k :=
  ((r74_repC 1677 2500 (by norm_num) (by norm_num)).sub
    ((r74_repC 3 20 (by norm_num) (by norm_num)).mul Scaled.rep_var)).add
    ((r74_repC 4 1 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))

open WholeIntervalPolynomial.Certificate in
private def r74_lS : Scaled :=
  ((⟨[10073],10000⟩ : Scaled).add ((⟨[17],10⟩ : Scaled).mul Scaled.var)).add
    ((⟨[11],5⟩ : Scaled).mul (Scaled.var.pow 2))

open WholeIntervalPolynomial.Certificate in
private theorem r74_rep_l : r74_lS.Rep l :=
  ((r74_repC 10073 10000 (by norm_num) (by norm_num)).add
    ((r74_repC 17 10 (by norm_num) (by norm_num)).mul Scaled.rep_var)).add
    ((r74_repC 11 5 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))

open WholeIntervalPolynomial.Certificate in
private def r74_resS : Scaled :=
  (((⟨[9789],625⟩ : Scaled).mul (r74_kS.pow 4)).mul (r74_lS.pow 4)).sub
    (((r74_kS.pow 2).add (r74_lS.pow 2)).pow 3)

open WholeIntervalPolynomial.Certificate in
private theorem r74_rep_res : r74_resS.Rep reserve :=
  (((r74_repC 9789 625 (by norm_num) (by norm_num)).mul (r74_rep_k.pow 4)).mul
    (r74_rep_l.pow 4)).sub (((r74_rep_k.pow 2).add (r74_rep_l.pow 2)).pow 3)

/-- All integer facts about the list of `reserve`, checked in one kernel run. -/
private theorem r74_facts :
    r74_resS.s≠0 ∧ r74_resS.l.length-1<3+14 ∧
    123*(r74_resS.s:ℤ)<r74_resS.l.getD 0 0*1000 ∧
    -813*(r74_resS.s:ℤ)<r74_resS.l.getD 1 0*500 ∧
    1599*(r74_resS.s:ℤ)<r74_resS.l.getD 2 0*100 ∧
    ∀ j : Fin 14,177*(r74_resS.s:ℤ)<r74_resS.l.getD (j.val+3) 0*1 := by
  decide +kernel

/-- A polynomial of degree below `k+n` is its first `k` monomials plus its tail. -/
private theorem r74_split {p : ℚ[X]} (k n : ℕ) (hp : p.natDegree<k+n) :
    p=(∑ i ∈ Finset.range k,C (p.coeff i)*X^i)+PowerTailBounds.tail p k n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' hp]
  rw [Finset.sum_range_add,PowerTailBounds.tail,
    Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+k))*X^(j+k)) n]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_comm k j]

/-- A rational number below an integer fraction, from an integer inequality. -/
private theorem r74_lt_frac {r : ℚ} {a N : ℤ} {b D : ℕ} (hr : r=a/b) (hb : 0<b) (hD : 0<D)
    (h : a*D<N*b) : r<(N:ℚ)/(D:ℚ) := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  rw [hr,div_lt_div_iff₀ hb' hD']
  exact_mod_cast h

theorem coefficient_certificate :
    reserve=C (reserve.coeff 0)+C (reserve.coeff 1)*X+
      C (reserve.coeff 2)*X^2+PowerTailBounds.tail reserve 3 14 ∧
    (123/1000:ℚ)<reserve.coeff 0 ∧
    -(813/500:ℚ)<reserve.coeff 1 ∧ (1599/100:ℚ)<reserve.coeff 2 ∧
    (∀j : Fin 14,(177:ℚ)<reserve.coeff (j.val+3)) := by
  obtain ⟨hs,hlen,h0,h1,h2,ht⟩ := r74_facts
  have hD := Nat.pos_of_ne_zero hs
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := r74_split 3 14 (lt_of_le_of_lt (r74_rep_res.natDegree_le hs) hlen)
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,
      pow_one] at h
    exact h
  · rw [r74_rep_res.coeff hs 0]
    exact r74_lt_frac (a:=123) (b:=1000) (by norm_num) (by norm_num) hD h0
  · rw [r74_rep_res.coeff hs 1]
    exact r74_lt_frac (a:=-813) (b:=500) (by norm_num) (by norm_num) hD h1
  · rw [r74_rep_res.coeff hs 2]
    exact r74_lt_frac (a:=1599) (b:=100) (by norm_num) (by norm_num) hD h2
  · intro j
    rw [r74_rep_res.coeff hs]
    exact r74_lt_frac (a:=177) (b:=1) (by norm_num) (by norm_num) hD (ht j)

theorem polynomial_positive {x : ℝ} (hx : 0≤x) : 0<aeval x reserve := by
  have htail : 0≤aeval x (PowerTailBounds.tail reserve 3 14) := by
    simp only [PowerTailBounds.tail,map_sum,map_mul,map_pow,aeval_C,aeval_X]
    apply Finset.sum_nonneg
    intro j _
    have hc : (0:ℝ)<(reserve.coeff (j.val+3):ℝ) := by
      have hh := (coefficient_certificate.2.2.2.2 j)
      have hh' : (177:ℝ)<(reserve.coeff (j.val+3):ℝ) := by exact_mod_cast hh
      linarith
    exact mul_nonneg hc.le (pow_nonneg hx _)
  have h0 : (123/1000:ℝ)<(reserve.coeff 0:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr coefficient_certificate.2.1
    push_cast at hh
    exact hh
  have h1 : -(813/500:ℝ)<(reserve.coeff 1:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr coefficient_certificate.2.2.1
    push_cast at hh
    exact hh
  have h2 : (1599/100:ℝ)<(reserve.coeff 2:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr coefficient_certificate.2.2.2.1
    push_cast at hh
    exact hh
  have hm1 := mul_le_mul_of_nonneg_right h1.le hx
  have hm2 := mul_le_mul_of_nonneg_right h2.le (sq_nonneg x)
  have hi := congrArg (fun p : ℚ[X] => aeval x p) coefficient_certificate.1
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hi
  nlinarith [sq_nonneg (x-271/5330),h0,hm1,hm2,htail,hi]

theorem original_positive {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<4*qCap*(Explicit.k .low θ)^4*(Explicit.l .low θ)^4-
      ((Explicit.k .low θ)^2+(Explicit.l .low θ)^2)^3 := by
  have hh := polynomial_positive (x:=1/6-θ) (by linarith [hθ.2])
  have hk : aeval (1/6-θ) k=Explicit.k .low θ := by
    simp [k,Explicit.k,Explicit.L]
    ring
  have hl : aeval (1/6-θ) l=Explicit.l .low θ := by
    simp [l,Explicit.l,Explicit.L]
    ring
  simp only [reserve,map_sub,map_mul,map_pow,map_add,aeval_C,eq_ratCast,hk,hl] at hh
  have hq : ((4:ℚ):ℝ)*((9789/2500:ℚ):ℝ)=4*qCap := by norm_num [qCap]
  rw [hq] at hh
  exact hh

end Certificate

/-- Increasing either positive coefficient increases the zero-angle norm
slope. This is a scalar comparison, not a source-witness replacement. -/
theorem zero_slope_rectangle {p q P Q : ℝ}
    (hp : 0<p) (hq : 0<q) (hpP : p≤P) (hqQ : q≤Q) :
    NegativeAPositiveTD.Curvature.slopeZero p q≤NegativeAPositiveTD.Curvature.slopeZero P Q := by
  have hP := hp.trans_le hpP
  have hQ := hq.trans_le hqQ
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos hp hq ht
  have hN := pairNorm_pos hP hQ ht
  have hn2 := pairNorm_sq hp hq ht
  have hN2 := pairNorm_sq hP hQ ht
  simp only [pairEnergy,Real.sin_zero,mul_zero,add_zero] at hn2 hN2
  have hp2 := pow_le_pow_left₀ hp.le hpP 2
  have hq2 := pow_le_pow_left₀ hq.le hqQ 2
  have h₁ := mul_le_mul_of_nonneg_left hq2 (mul_nonneg (sq_nonneg p) (sq_nonneg P))
  have h₂ := mul_le_mul_of_nonneg_left hp2 (mul_nonneg (sq_nonneg q) (sq_nonneg Q))
  have hsq : (p*q*pairNorm P Q 0)^2≤(P*Q*pairNorm p q 0)^2 := by
    simp only [mul_pow]
    rw [hn2,hN2]
    nlinarith only [h₁,h₂]
  have hcross : p*q*pairNorm P Q 0≤P*Q*pairNorm p q 0 := by
    nlinarith [mul_pos (mul_pos hp hq) hN,mul_pos (mul_pos hP hQ) hn]
  have hdiv := (div_le_div_iff₀ hn hN).2 hcross
  have hh := mul_le_mul_of_nonneg_left hdiv (Real.sqrt_nonneg qCap)
  simp only [NegativeAPositiveTD.Curvature.slopeZero,pairProduct]
  rw [mul_div_assoc R (p*q),mul_div_assoc R (P*Q)]
  exact hh

theorem zero_slope_upper {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    NegativeAPositiveTD.Curvature.slopeZero (Explicit.k .low θ) (Explicit.l .low θ)<131/100 := by
  have hr := Explicit.low_ranges hθ
  have hh := zero_slope_rectangle (by linarith [hr.1] : 0<Explicit.k .low θ)
    (by linarith [hr.2.2.1] : 0<Explicit.l .low θ) hr.2.1.le hr.2.2.2.1.le
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos (p:=(757/1000:ℝ)) (q:=(1352/1000:ℝ)) (by norm_num) (by norm_num) ht
  have hn2 := pairNorm_sq (p:=(757/1000:ℝ)) (q:=(1352/1000:ℝ)) (by norm_num) (by norm_num) ht
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have he : NegativeAPositiveTD.Curvature.slopeZero (757/1000) (1352/1000)<131/100 := by
    unfold NegativeAPositiveTD.Curvature.slopeZero
    apply quotient_lt_of_square hn (by norm_num)
    rw [mul_pow,hR2,hn2]
    norm_num [pairProduct,pairEnergy,qCap]
  exact hh.trans_lt he

theorem curvature_lower {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (1/2:ℝ)<curvatureZero R (Explicit.k .low θ) (Explicit.l .low θ) := by
  have hr := Explicit.low_ranges hθ
  have hk : 0<Explicit.k .low θ := by linarith [hr.1]
  have hl : 0<Explicit.l .low θ := by linarith [hr.2.2.1]
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos hk hl ht
  have hn2 := pairNorm_sq hk hl ht
  simp only [pairEnergy,Real.sin_zero,mul_zero,add_zero] at hn2
  have hpoly := Certificate.original_positive hθ
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hnum : 0<2*R*(Explicit.k .low θ*Explicit.l .low θ)^2 := by
    have hR : 0<R := by linarith [NegativeAPositiveTD.Curvature.radius_bounds.1]
    positivity
  have hsquare : ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3)^2<
      (2*R*(Explicit.k .low θ*Explicit.l .low θ)^2)^2 := by
    rw [show ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3)^2=
      ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^2)^3 by ring,hn2,
      show (2*R*(Explicit.k .low θ*Explicit.l .low θ)^2)^2=
        4*R^2*(Explicit.k .low θ)^4*(Explicit.l .low θ)^4 by ring,hR2]
    generalize qCap = Q at hpoly ⊢
    linarith only [hpoly]
  have hcross : (pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3<
      2*R*(Explicit.k .low θ*Explicit.l .low θ)^2 :=
    lt_of_pow_lt_pow_left₀ 2 hnum.le hsquare
  unfold curvatureZero
  apply (lt_div_iff₀ (pow_pos hn 3)).2
  dsimp [pairProduct]
  generalize R = R0 at hcross ⊢
  linarith only [hcross]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowG
