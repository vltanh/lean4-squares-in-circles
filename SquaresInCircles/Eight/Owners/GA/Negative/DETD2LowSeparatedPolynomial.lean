module

public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowSeparatedSlope

/-!
# Eight squares: the two polynomial reserves in the low separated-block argument

The degree-fourteen polynomial retains
its centered quadratic on the whole short interval. The interior-D
quartic has positive Bernstein coefficients on `[0.27, 0.645]`. No sample points
or interval mesh enter either bound.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope

namespace Certificate
open PositiveTD.Certificate (S5 C4)

def AP : ℚ[X] := C (13753/50000)-C (13607/12500)*X-C (1/6)*X^2+C (1/6)*X^3
def BP : ℚ[X] := C (32033/25000)-C (2729/4000)*X-C (5/24)*X^2+C (5/24)*X^3
def shortPolynomial : ℚ[X] := C (13/12)-C (2/5)*S5.comp (C (7/10)-X)-
  (C4.comp (C (7/10)-X))^2*(BP+C (500/389)*AP^2)
def shortTranslated : ℚ[X] := DirectedPowerBounds.shift (3/25) shortPolynomial

/-! ### Kernel certificates

Each polynomial is represented by a scaled integer coefficient list
(`WholeIntervalPolynomial.Certificate`) built to mirror its definition. -/

open WholeIntervalPolynomial.Certificate in
private theorem r75_repC (n : ℤ) (d : ℕ) {q : ℚ} (hd : d≠0) (h : q=n/d) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [h]
  field_simp

private theorem r75_shift_eq (a : ℚ) (p : ℚ[X]) :
    DirectedPowerBounds.shift a p=WholeIntervalPolynomial.centered (a-1) (a+1) p := by
  rw [DirectedPowerBounds.shift,WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,
    show (a-1+(a+1))/2=a by ring,show (a+1-(a-1))/2=1 by ring,map_one,one_mul]

/-- A polynomial of degree below `k+n` is its first `k` monomials plus its tail. -/
private theorem r75_split {p : ℚ[X]} (k n : ℕ) (hp : p.natDegree<k+n) :
    p=(∑ i ∈ Finset.range k,C (p.coeff i)*X^i)+PowerTailBounds.tail p k n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' hp]
  rw [Finset.sum_range_add,PowerTailBounds.tail,
    Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+k))*X^(j+k)) n]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_comm k j]

open WholeIntervalPolynomial.Certificate in
private theorem r75_coeff_sub_norm {c : Scaled} {p : ℚ[X]}
    (hc : c.Rep p) (hs : c.s≠0) (j0 k n a m : ℕ) (hm : 0 < m) {r : ℚ} (hr : r*m=a) :
    p.coeff j0-PowerTailBounds.norm p k n r=
      ((c.l.getD j0 0*(m:ℤ)^n-
        ∑ j : Fin n,|c.l.getD (j.val+k) 0| *(a:ℤ)^(j.val+1)*(m:ℤ)^(n-1-j.val) : ℤ):ℚ)/
        ((c.s*m^n:ℕ):ℚ) := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hm' : (0:ℚ) < m := by exact_mod_cast hm
  have hr' : r=a/m := by field_simp; linarith
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
    rw [abs_div,abs_of_pos hs',hr',hpow,div_pow]
    field_simp

/-- A rational number below an integer fraction, from an integer inequality. -/
private theorem r75_lt_frac {r : ℚ} {a N : ℤ} {b D : ℕ} (hr : r=a/b) (hb : 0<b) (hD : 0<D)
    (h : a*D<N*b) : r<(N:ℚ)/(D:ℚ) := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  rw [hr,div_lt_div_iff₀ hb' hD']
  exact_mod_cast h

/-- The absolute value of an integer fraction below a rational number. -/
private theorem r75_abs_lt {r : ℚ} {N a : ℤ} {D b : ℕ} (hr : r=a/b) (hD : 0<D) (hb : 0<b)
    (h : |N| *b<a*D) : |(N:ℚ)/(D:ℚ)|<r := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  rw [hr,abs_div,abs_of_pos hD',div_lt_div_iff₀ hD' hb']
  have h' : ((|N| *b:ℤ):ℚ)<((a*D:ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  exact h'

open WholeIntervalPolynomial.Certificate in
private def r75_YS : Scaled := (⟨[7],10⟩ : Scaled).sub Scaled.var

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_Y : r75_YS.Rep (C (7/10)-X) :=
  (r75_repC 7 10 (by norm_num) (by norm_num)).sub Scaled.rep_var

open WholeIntervalPolynomial.Certificate in
private def r75_S5cS : Scaled :=
  (r75_YS.sub ((⟨[1],6⟩ : Scaled).mul (r75_YS.pow 3))).add ((⟨[1],120⟩ : Scaled).mul (r75_YS.pow 5))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_S5c : r75_S5cS.Rep (S5.comp (C (7/10)-X)) := by
  have e : S5.comp (C (7/10)-X)=(C (7/10)-X)-C (1/6)*(C (7/10)-X)^3+
      C (1/120)*(C (7/10)-X)^5 := by
    simp only [S5,add_comp,sub_comp,mul_comp,C_comp,X_comp,X_pow_comp]
  rw [e]
  exact (r75_rep_Y.sub ((r75_repC 1 6 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 3))).add
    ((r75_repC 1 120 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 5))

open WholeIntervalPolynomial.Certificate in
private def r75_C4cS : Scaled :=
  ((Scaled.ofNat 1).sub ((⟨[1],2⟩ : Scaled).mul (r75_YS.pow 2))).add
    ((⟨[1],24⟩ : Scaled).mul (r75_YS.pow 4))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_C4c : r75_C4cS.Rep (C4.comp (C (7/10)-X)) := by
  have e : C4.comp (C (7/10)-X)=1-C (1/2)*(C (7/10)-X)^2+C (1/24)*(C (7/10)-X)^4 := by
    simp only [C4,add_comp,sub_comp,mul_comp,C_comp,X_pow_comp,one_comp]
  rw [e]
  exact (Scaled.rep_one.sub ((r75_repC 1 2 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 2))).add
    ((r75_repC 1 24 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 4))

open WholeIntervalPolynomial.Certificate in
private def r75_APS : Scaled :=
  (((⟨[13753],50000⟩ : Scaled).sub ((⟨[13607],12500⟩ : Scaled).mul Scaled.var)).sub
    ((⟨[1],6⟩ : Scaled).mul (Scaled.var.pow 2))).add ((⟨[1],6⟩ : Scaled).mul (Scaled.var.pow 3))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_AP : r75_APS.Rep AP :=
  (((r75_repC 13753 50000 (by norm_num) (by norm_num)).sub
    ((r75_repC 13607 12500 (by norm_num) (by norm_num)).mul Scaled.rep_var)).sub
    ((r75_repC 1 6 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))).add
    ((r75_repC 1 6 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 3))

open WholeIntervalPolynomial.Certificate in
private def r75_BPS : Scaled :=
  (((⟨[32033],25000⟩ : Scaled).sub ((⟨[2729],4000⟩ : Scaled).mul Scaled.var)).sub
    ((⟨[5],24⟩ : Scaled).mul (Scaled.var.pow 2))).add ((⟨[5],24⟩ : Scaled).mul (Scaled.var.pow 3))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_BP : r75_BPS.Rep BP :=
  (((r75_repC 32033 25000 (by norm_num) (by norm_num)).sub
    ((r75_repC 2729 4000 (by norm_num) (by norm_num)).mul Scaled.rep_var)).sub
    ((r75_repC 5 24 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))).add
    ((r75_repC 5 24 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 3))

open WholeIntervalPolynomial.Certificate in
private def r75_shortS : Scaled :=
  ((⟨[13],12⟩ : Scaled).sub ((⟨[2],5⟩ : Scaled).mul r75_S5cS)).sub
    ((r75_C4cS.pow 2).mul (r75_BPS.add ((⟨[500],389⟩ : Scaled).mul (r75_APS.pow 2))))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_short : r75_shortS.Rep shortPolynomial :=
  ((r75_repC 13 12 (by norm_num) (by norm_num)).sub
    ((r75_repC 2 5 (by norm_num) (by norm_num)).mul r75_rep_S5c)).sub
    ((r75_rep_C4c.pow 2).mul (r75_rep_BP.add
      ((r75_repC 500 389 (by norm_num) (by norm_num)).mul (r75_rep_AP.pow 2))))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_shortT : (r75_shortS.center 1 25 3 25).Rep shortTranslated := by
  rw [shortTranslated,r75_shift_eq]
  exact r75_rep_short.centered 1 25 3 25 (by norm_num) (by norm_num) (by norm_num)

theorem short_certificate :
    shortTranslated=C (shortTranslated.coeff 0)+C (shortTranslated.coeff 1)*X+
      C (shortTranslated.coeff 2)*X^2+PowerTailBounds.tail shortTranslated 3 12 ∧
    (21067/2500000:ℚ)<shortTranslated.coeff 0 ∧
    |shortTranslated.coeff 1|<(77231/10000000:ℚ) ∧
    (6217/10000:ℚ)<shortTranslated.coeff 2 ∧
    (4307/20000:ℚ)<shortTranslated.coeff 2-
      PowerTailBounds.norm shortTranslated 3 12 (6/25) := by
  have hs : (r75_shortS.center 1 25 3 25).s≠0 := by decide +kernel
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := r75_split 3 12 (lt_of_le_of_lt (r75_rep_shortT.natDegree_le hs) (by decide +kernel))
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,
      pow_one] at h
    exact h
  · rw [r75_rep_shortT.coeff hs 0]
    exact r75_lt_frac (a:=21067) (b:=2500000) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · rw [r75_rep_shortT.coeff hs 1]
    exact r75_abs_lt (a:=77231) (b:=10000000) (by norm_num) (by decide +kernel) (by norm_num)
      (by decide +kernel)
  · rw [r75_rep_shortT.coeff hs 2]
    exact r75_lt_frac (a:=6217) (b:=10000) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · rw [r75_coeff_sub_norm r75_rep_shortT hs 2 3 12 6 25 (by norm_num) (by norm_num)]
    exact r75_lt_frac (a:=4307) (b:=20000) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)

theorem short_positive {d : ℝ} (hd : d∈Icc (0:ℝ) (9/25)) :
    (167/20000:ℝ)<aeval d shortPolynomial := by
  obtain ⟨x,hxd⟩ : ∃ x : ℝ,x=d-3/25 := ⟨_,rfl⟩
  have hx : |x|≤((6/25:ℚ):ℝ) := by
    rw [abs_le,hxd]
    push_cast
    exact ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have ht := PowerTailBounds.quadratic_lower short_certificate.1 (by norm_num) hx
  have h0 : (21067/2500000:ℝ)<(shortTranslated.coeff 0:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr short_certificate.2.1
    push_cast at hh
    exact hh
  have h1 : |(shortTranslated.coeff 1:ℝ)|<(77231/10000000:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr short_certificate.2.2.1
    push_cast at hh
    exact hh
  have h2 : (4307/20000:ℝ)<(shortTranslated.coeff 2:ℝ)-
      (PowerTailBounds.norm shortTranslated 3 12 (6/25):ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr short_certificate.2.2.2.2
    push_cast at hh
    exact hh
  have hlin : -(77231/10000000)*|x|≤(shortTranslated.coeff 1:ℝ)*x := by
    have hh := mul_le_mul_of_nonneg_right h1.le (abs_nonneg x)
    rw [←abs_mul] at hh
    have hh' := (abs_le.mp hh).1
    linarith
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg x)
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(21067/2500000:ℝ)) (b:=-(77231/10000000:ℝ)) (x:=|x|)
    (show (0:ℝ)<4307/20000 by norm_num)
  have hreserve : (167/20000:ℝ)<21067/2500000-
      (77231/10000000:ℝ)^2/(4*(4307/20000)) := by norm_num
  have he : aeval x shortTranslated=aeval d shortPolynomial := by
    have hx' : ((3/25:ℚ):ℝ)+x=d := by rw [hxd]; push_cast; ring
    simp only [shortTranslated,DirectedPowerBounds.shift_eval,hx']
  rw [he] at ht
  rw [sq_abs] at hmin
  nlinarith

@[simp] theorem AP_eval (d : ℝ) : aeval d AP=A d := by
  simp [AP,A]
  ring
@[simp] theorem BP_eval (d : ℝ) : aeval d BP=B d := by simp [BP,B]

theorem short_model_reserve {d : ℝ} (hd : d∈Icc (0:ℝ) (9/25)) :
    0<13/12-(2/5)*aeval (frameCap-d) S5-
      (aeval (frameCap-d) C4)^2*model d := by
  have hp := short_positive hd
  have he : aeval d shortPolynomial=13/12-(2/5)*aeval (frameCap-d) S5-
      (aeval (frameCap-d) C4)^2*model d := by
    simp [shortPolynomial,aeval_comp,frameCap,model,AP_eval,BP_eval]
  rw [he] at hp
  linarith

def interiorPolynomial : ℚ[X] := C (1/1200)-C (9/184)*X+C (79057/211600)*X^2-
  C (881/1150)*X^3+C (375/529)*X^4

theorem interior_positive {y : ℝ} (hy : y∈Icc (27/100:ℝ) (129/200)) :
    0<aeval y interiorPolynomial := by
  have h1 : 0≤y-27/100 := sub_nonneg.2 hy.1
  have h2 : 0≤129/200-y := sub_nonneg.2 hy.2
  simp only [interiorPolynomial,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [pow_nonneg h1 4,mul_nonneg (pow_nonneg h1 3) h2,
    mul_nonneg (pow_nonneg h1 2) (pow_nonneg h2 2),mul_nonneg h1 (pow_nonneg h2 3),pow_nonneg h2 4]

end Certificate

def AFirst (d : ℝ) : ℝ := -(13607/12500)-d/3+d^2/2
def lateCubic (d : ℝ) : ℝ := 960319/800000-(41011/100000)*d-d^2/6+d^3/6

theorem A_derivative (d : ℝ) : HasDerivAt A (AFirst d) d := by
  have h := ((((hasDerivAt_id d).const_mul (13607/12500:ℝ)).const_sub (13753/50000:ℝ)).sub
    ((hasDerivAt_pow 2 d).div_const 6)).add ((hasDerivAt_pow 3 d).div_const 6)
  convert h using 1
  · rfl
  · simp only [AFirst,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,show (3:ℕ)-1=2 from rfl,pow_one]
    ring

theorem A_late_upper {d : ℝ} (hd : d∈Icc (9/25:ℝ) frameCap) : A d< -(389/4000:ℝ) := by
  have hm : AntitoneOn A (Icc (9/25:ℝ) frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun d _ => (A_derivative d).continuousAt.continuousWithinAt)
      (fun d _ => A_derivative d)
    intro d hd
    have h1 := hd.1
    have h2 := hd.2
    simp only [frameCap] at h2
    have hd2 := pow_le_pow_left₀ (show 0≤d by linarith) h2.le 2
    simp only [AFirst]
    nlinarith
  have hh := hm (by norm_num [frameCap]) hd hd.1
  have hA : A (9/25)=-(163307/1250000) := by norm_num [A]
  linarith

theorem lateCubic_derivative (d : ℝ) : HasDerivAt lateCubic
    (-(41011/100000)-d/3+d^2/2) d := by
  have h := ((((hasDerivAt_id d).const_mul (41011/100000:ℝ)).const_sub (960319/800000:ℝ)).sub
    ((hasDerivAt_pow 2 d).div_const 6)).add ((hasDerivAt_pow 3 d).div_const 6)
  convert h using 1
  · rfl
  · simp only [Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,show (3:ℕ)-1=2 from rfl,pow_one]
    ring

theorem lateCubic_upper {d : ℝ} (hd : d∈Icc (9/25:ℝ) frameCap) : lateCubic d<1039/1000 := by
  have hm : AntitoneOn lateCubic (Icc (9/25:ℝ) frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun d _ => (lateCubic_derivative d).continuousAt.continuousWithinAt)
      (fun d _ => lateCubic_derivative d)
    intro d hd
    have h1 := hd.1
    have h2 := hd.2
    simp only [frameCap] at h2
    have hd2 := pow_le_pow_left₀ (show 0≤d by linarith) h2.le 2
    nlinarith
  have hh := hm (by norm_num [frameCap]) hd hd.1
  have hL : lateCubic (9/25)=20778703/20000000 := by norm_num [lateCubic]
  linarith

theorem late_slope_upper {p q d : ℝ}
    (hp : 0<p) (hp0 : p≤p0) (hq : q∈Icc 1 qMax)
    (hd : d∈Icc (9/25:ℝ) frameCap) : OrdinaryNegativeSlope.Vd Secondary.R p q d<1039/1000 := by
  have hmodel := quadratic_model hp hp0 hq ⟨by linarith [hd.1],hd.2⟩
  have hA := A_late_upper hd
  have hproduct := mul_nonpos_of_nonpos_of_nonneg
    (show A d+389/4000≤0 by linarith) (sub_nonneg.mpr hq.1)
  have he : B d+A d*(q-q0)-(389/2000)*(q-q0)^2=
      lateCubic d+(A d+389/4000)*(q-1)-(389/2000)*(q-1)^2 := by
    dsimp [A,B,lateCubic,q0]
    ring
  rw [he] at hmodel
  have hh : OrdinaryNegativeSlope.Vd Secondary.R p q d<lateCubic d := by
    nlinarith [sq_nonneg (q-1)]
  exact hh.trans (lateCubic_upper hd)

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
