module

public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.Negative.ContactGeometry
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: compact attainment of the actual negative-DE3 outside endpoint

A compact set contains the actual E radial states with
both original projections feasible. Its least positive-EH angle is attained.
The explicit strict improvement directions exclude every interior minimum
except an actual EH0 stop. Thus no feasible continuation path, first stopping
time, or omitted radial boundary is a hypothesis.
-/

section
/-!
## A whole-interval polynomial for the long EH / DE2 contact

The single polynomial has degree 27 and is positive on the entire interval
[11/50,7/10]. Its coefficients are calculated from its displayed formula;
there are no sampled angles or imported certificate rows. The finite
kernel reductions below are proof scripts and have not been executed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.OutsideDE2Polynomial
open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate

def Rlo : ℚ := 19787/10000
def Rhi : ℚ := 4947/2500
def Zlo : ℚ := 981/500
def Plo : ℚ := 3991/10000
def Phi : ℚ := 3993/10000

def S3 : ℚ[X] := X-C (1/6)*X^3
def S5 : ℚ[X] := S3+C (1/120)*X^5
def C2 : ℚ[X] := 1-C (1/2)*X^2
def C4 : ℚ[X] := C2+C (1/24)*X^4
def Ylo : ℚ[X] := (C Zlo-C4)*S3+C Plo*C2
def Yhi : ℚ[X] := (C Rhi-C2)*S5+C Phi*C4
def Xlo : ℚ[X] := C Zlo*C2-C Phi*S5+S3^2
def Xhi : ℚ[X] := C Rhi*C4-C Plo*S3+S5^2
def Alo : ℚ[X] := 1-C (1/Zlo)*C4
def Llo : ℚ[X] := C (1103/625)-Yhi

def certificate : ℚ[X] :=
  C Rlo*Xlo*Alo*(Llo*Xhi+C Rhi*Ylo*Alo)-C Rhi*Xhi^2*S5

/-- Build a `Scaled` representation of a polynomial written with `+`, `-`, `*`,
powers, `C`, `X` and numerals, following its syntax. -/
local syntax "repT" : tactic
local macro_rules | `(tactic| repT) => `(tactic| first
  | (with_reducible apply Scaled.Rep.add; repT; repT)
  | (with_reducible apply Scaled.Rep.sub; repT; repT)
  | (with_reducible apply Scaled.Rep.mul; repT; repT)
  | (with_reducible apply Scaled.Rep.pow; repT)
  | (with_reducible apply Scaled.Rep.neg; repT)
  | with_reducible exact Scaled.rep_var
  | with_reducible exact Scaled.rep_zero
  | with_reducible exact Scaled.rep_one
  | with_reducible exact Scaled.rep_ofNat _
  | with_reducible exact Scaled.rep_natCast _
  | with_reducible exact Scaled.rep_const _)

private theorem lt_lowerOn_of {c : Scaled} {a b ρ : ℚ} {p : ℚ[X]} {D : ℕ}
    (hc : c.Rep (centered a b p)) (hs : c.s≠0) (hl : c.l.length≤D+1)
    (h : ρ<(lowerZ D (fun j => (chebList c.l).getD j 0):ℚ)/(c.s*2^c.l.length/2)) :
    ρ<lowerOn D a b p := by
  rw [lowerOn_eq_of_rep hc hs hl]
  exact h

/-- Unfold the polynomials of this file. -/
local macro "unfoldAll" : tactic => `(tactic| simp only [certificate,Xlo,Alo,Llo,Xhi,Ylo,
  Yhi,S3,S5,C2,C4])

theorem expansion_identity :
    centered (11/50) (7/10) certificate=
      expansion 27 (centered (11/50) (7/10) certificate) := by
  have hp := (by unfoldAll; repT : Scaled.Rep _ certificate)
  exact (hp.centered 1 50 23 12 (by norm_num) (by norm_num) (by norm_num)).eq_expansion
    (by decide +kernel) (by decide +kernel)

theorem coefficient_reserve :
    (8179/10000 : ℚ)<lowerOn 27 (11/50) (7/10) certificate := by
  have hp := (by unfoldAll; repT : Scaled.Rep _ certificate)
  exact lt_lowerOn_of (hp.centered 1 50 23 12 (by norm_num) (by norm_num) (by norm_num))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

inductive Factor where
  | ylo | yhi | xlo | xhi | alo | llo

def factor : Factor → ℚ[X]
  | .ylo => Ylo
  | .yhi => Yhi
  | .xlo => Xlo
  | .xhi => Xhi
  | .alo => Alo
  | .llo => Llo

theorem certificate_positive {p : ℝ} (hp : p∈Set.Icc (11/50 : ℝ) (7/10)) :
    (8179/10000 : ℝ)<aeval p certificate := by
  have h := positive_on_interval (by norm_num) expansion_identity coefficient_reserve
    (x := p) (by simpa using hp)
  simpa using h

/-- Each factor has positive Bernstein coefficients of its degree on `[11/50, 7/10]`. -/
private theorem ylo_positive {p : ℝ} (hp : p∈Set.Icc (11/50 : ℝ) (7/10)) :
    0<aeval p Ylo := by
  have h0 : 0≤p-11/50 := sub_nonneg.2 hp.1
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤(p-11/50)^i*(7/10-p)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  simp only [Ylo,S3,C2,C4,Zlo,Plo,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    eq_ratCast]
  push_cast
  linarith [hb 7 0,hb 6 1,hb 5 2,hb 4 3,hb 3 4,hb 2 5,hb 1 6,hb 0 7]

private theorem yhi_positive {p : ℝ} (hp : p∈Set.Icc (11/50 : ℝ) (7/10)) :
    0<aeval p Yhi := by
  have h0 : 0≤p-11/50 := sub_nonneg.2 hp.1
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤(p-11/50)^i*(7/10-p)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  simp only [Yhi,S3,S5,C2,C4,Rhi,Phi,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    eq_ratCast]
  push_cast
  linarith [hb 7 0,hb 6 1,hb 5 2,hb 4 3,hb 3 4,hb 2 5,hb 1 6,hb 0 7]

private theorem xlo_positive {p : ℝ} (hp : p∈Set.Icc (11/50 : ℝ) (7/10)) :
    0<aeval p Xlo := by
  have h0 : 0≤p-11/50 := sub_nonneg.2 hp.1
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤(p-11/50)^i*(7/10-p)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  simp only [Xlo,S3,S5,C2,Zlo,Phi,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    eq_ratCast]
  push_cast
  linarith [hb 6 0,hb 5 1,hb 4 2,hb 3 3,hb 2 4,hb 1 5,hb 0 6]

private theorem xhi_positive {p : ℝ} (hp : p∈Set.Icc (11/50 : ℝ) (7/10)) :
    0<aeval p Xhi := by
  have h0 : 0≤p-11/50 := sub_nonneg.2 hp.1
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤(p-11/50)^i*(7/10-p)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  simp only [Xhi,S3,S5,C2,C4,Rhi,Plo,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    eq_ratCast]
  push_cast
  linarith [hb 10 0,hb 9 1,hb 8 2,hb 7 3,hb 6 4,hb 5 5,hb 4 6,hb 3 7,hb 2 8,hb 1 9,hb 0 10]

private theorem alo_positive {p : ℝ} (hp : p∈Set.Icc (11/50 : ℝ) (7/10)) :
    0<aeval p Alo := by
  have h0 : 0≤p-11/50 := sub_nonneg.2 hp.1
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤(p-11/50)^i*(7/10-p)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  simp only [Alo,C2,C4,Zlo,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    eq_ratCast]
  push_cast
  linarith [hb 4 0,hb 3 1,hb 2 2,hb 1 3,hb 0 4]

private theorem llo_positive {p : ℝ} (hp : p∈Set.Icc (11/50 : ℝ) (7/10)) :
    0<aeval p Llo := by
  have h0 : 0≤p-11/50 := sub_nonneg.2 hp.1
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤(p-11/50)^i*(7/10-p)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  simp only [Llo,Yhi,S3,S5,C2,C4,Rhi,Phi,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    eq_ratCast]
  push_cast
  linarith [hb 7 0,hb 6 1,hb 5 2,hb 4 3,hb 3 4,hb 2 5,hb 1 6,hb 0 7]

theorem factor_positive (i : Factor) {p : ℝ}
    (hp : p∈Set.Icc (11/50 : ℝ) (7/10)) : 0<aeval p (factor i) := by
  cases i
  exacts [ylo_positive hp,yhi_positive hp,xlo_positive hp,xhi_positive hp,alo_positive hp,
    llo_positive hp]

theorem factors_positive {p : ℝ} (hp : p∈Set.Icc (11/50 : ℝ) (7/10)) :
    0<aeval p Ylo ∧ 0<aeval p Yhi ∧ 0<aeval p Xlo ∧
      0<aeval p Xhi ∧ 0<aeval p Alo ∧ 0<aeval p Llo := by
  exact ⟨factor_positive .ylo hp,factor_positive .yhi hp,
    factor_positive .xlo hp,factor_positive .xhi hp,
    factor_positive .alo hp,factor_positive .llo hp⟩

@[simp] theorem S3_eval (p : ℝ) : aeval p S3=p-p^3/6 := by simp [S3]; ring
@[simp] theorem S5_eval (p : ℝ) : aeval p S5=p-p^3/6+p^5/120 := by simp [S5]; ring
@[simp] theorem C2_eval (p : ℝ) : aeval p C2=1-p^2/2 := by simp [C2]; ring
@[simp] theorem C4_eval (p : ℝ) : aeval p C4=1-p^2/2+p^4/24 := by simp [C4]; ring

theorem certificate_eval (p : ℝ) : aeval p certificate=
    (Rlo:ℝ)*aeval p Xlo*aeval p Alo*
      (aeval p Llo*aeval p Xhi+(Rhi:ℝ)*aeval p Ylo*aeval p Alo)-
        (Rhi:ℝ)*(aeval p Xhi)^2*aeval p S5 := by
  simp only [certificate,map_sub,map_mul,map_add,map_pow,aeval_C,eq_ratCast]

/-- The cleared-denominator polynomial supplies the strict derivative
reserve, before any geometric comparison is made. -/
theorem derivative_lower_positive {p : ℝ}
    (hp : p∈Set.Icc (11/50 : ℝ) (7/10)) :
    0<aeval p Xlo*aeval p Alo*
      (aeval p Llo/(Rhi:ℝ)+aeval p Ylo*aeval p Alo/aeval p Xhi)-
        aeval p Xhi*aeval p S5/(Rlo:ℝ) := by
  have hx := (factors_positive hp).2.2.2.1
  have hden : 0<(Rlo:ℝ)*(Rhi:ℝ)*aeval p Xhi := by
    have h1 : (0:ℝ)<(Rlo:ℝ) := by norm_num [Rlo]
    have h2 : (0:ℝ)<(Rhi:ℝ) := by norm_num [Rhi]
    positivity
  have he : aeval p Xlo*aeval p Alo*
      (aeval p Llo/(Rhi:ℝ)+aeval p Ylo*aeval p Alo/aeval p Xhi)-
        aeval p Xhi*aeval p S5/(Rlo:ℝ)=
      aeval p certificate/((Rlo:ℝ)*(Rhi:ℝ)*aeval p Xhi) := by
    rw [certificate_eval]
    field_simp [hx.ne',show (Rlo:ℝ)≠0 by norm_num [Rlo],
      show (Rhi:ℝ)≠0 by norm_num [Rhi]]
  rw [he]
  exact div_pos (by linarith [certificate_positive hp]) hden

/-- Algebraic transfer from the explicit Taylor envelopes to the actual
derivative in equation (24). The arguments are the real contact values;
each displayed bound is derived from that contact in the geometric use. -/
theorem derivative_positive {p X Y L Z R beta : ℝ}
    (hp : p∈Set.Icc (11/50 : ℝ) (7/10))
    (hRlo : (Rlo:ℝ)≤R) (hRhi : R≤(Rhi:ℝ))
    (hXlo : aeval p Xlo≤X) (hXhi : X≤aeval p Xhi)
    (hYlo : aeval p Ylo≤Y) (hLlo : aeval p Llo≤L)
    (hZ : 0<Z) (hZR : Z≤R)
    (hbeta : aeval p Xlo*aeval p Alo≤beta)
    (hA : aeval p Alo≤1-Real.cos p/R)
    (hs : 0≤Real.sin p) (hs5 : Real.sin p≤aeval p S5) :
    0<beta*(L/Z+Y/X*(1-Real.cos p/R))-X*Real.sin p/R := by
  obtain ⟨hyl,_,hxl,hxu,ha,hl⟩ := factors_positive hp
  have hX : 0<X := hxl.trans_le hXlo
  have hY : 0≤Y := (hyl.trans_le hYlo).le
  have hL : 0≤L := (hl.trans_le hLlo).le
  have hAr : 0≤1-Real.cos p/R := ha.le.trans hA
  have hfirst : aeval p Llo/(Rhi:ℝ)≤L/Z :=
    div_le_div₀ hL hLlo hZ (hZR.trans hRhi)
  have hratio : aeval p Ylo/aeval p Xhi≤Y/X :=
    div_le_div₀ hY hYlo hX hXhi
  have hsecond : aeval p Ylo*aeval p Alo/aeval p Xhi≤
      Y/X*(1-Real.cos p/R) := by
    calc
      aeval p Ylo*aeval p Alo/aeval p Xhi =
          (aeval p Ylo/aeval p Xhi)*aeval p Alo := by ring
      _ ≤ Y/X*(1-Real.cos p/R) :=
        mul_le_mul hratio hA ha.le (div_nonneg hY hX.le)
  have hmain := mul_le_mul hbeta (add_le_add hfirst hsecond)
    (add_nonneg (div_nonneg hl.le (by norm_num [Rhi]))
      (div_nonneg (mul_nonneg hyl.le ha.le) hxu.le)) (by linarith [mul_pos hxl ha])
  have hlast : X*Real.sin p/R≤aeval p Xhi*aeval p S5/(Rlo:ℝ) :=
    div_le_div₀ (mul_nonneg hxu.le (hs.trans hs5)) (mul_le_mul hXhi hs5 hs hxu.le)
      (by norm_num [Rlo]) hRlo
  linarith [derivative_lower_positive hp]

end SquaresInCircles.Eight.OutsideDE2Polynomial
end
end
end

section
/-!
## Reference contact for the outside DE2 comparison

The reference uses the same original q and the least sorted H primary `leastPrimary`. It is only
a comparison of real scalar functions; no square of the packing is moved to it. The polynomial
envelopes (`bounds`) are derived here from the exact circle and contact formulas; they give the
positive gap derivative `derivative_pos`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OutsideDE2Reference
open Polynomial OutsideDE2Polynomial

def radius (q : ℝ) : ℝ := Real.sqrt q
def leastPrimary (q : ℝ) : ℝ := Real.sqrt (q/2)-1
def u (q p : ℝ) : ℝ := leastPrimary q-Real.sin p
def z (q p : ℝ) : ℝ := Real.sqrt (q-(u q p)^2)
def x (q p : ℝ) : ℝ := z q p*Real.cos p-u q p*Real.sin p
def y (q p : ℝ) : ℝ := z q p*Real.sin p+u q p*Real.cos p
def beta (q p : ℝ) : ℝ := x q p*(1-Real.cos p/z q p)
def ell (q p : ℝ) : ℝ := 1+Real.cos (7/10 : ℝ)-y q p
def root (q p : ℝ) : ℝ := Real.sqrt (q-(ell q p)^2)
def gap (q p : ℝ) : ℝ := root q p-Real.sin (7/10 : ℝ)-
  x q p*(1-Real.cos p/radius q)
def gapDerivative (q p : ℝ) : ℝ := beta q p*
  (ell q p/root q p+y q p/x q p*(1-Real.cos p/radius q))-
    x q p*Real.sin p/radius q

theorem constant_bounds {q : ℝ} (hq : qLow≤q∧q≤qCap) :
    (Rlo:ℝ)<radius q ∧ radius q<(Rhi:ℝ) ∧
      (Plo:ℝ)<leastPrimary q ∧ leastPrimary q<(Phi:ℝ) := by
  have hq0 : 0≤q := by dsimp [qLow] at hq; linarith
  have hr := Real.sq_sqrt hq0
  have hp := Real.sq_sqrt (show 0≤q/2 by linarith)
  have hr0 := Real.sqrt_nonneg q
  have hp0 := Real.sqrt_nonneg (q/2)
  dsimp [radius,leastPrimary,Rlo,Rhi,Plo,Phi,qLow,qCap] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem taylor_bounds {p : ℝ} (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    0≤aeval p S3 ∧ aeval p S3≤Real.sin p ∧ Real.sin p≤aeval p S5 ∧
      0<aeval p C2 ∧ aeval p C2≤Real.cos p ∧ Real.cos p≤aeval p C4 ∧
        aeval p C4≤1 ∧ 0≤Real.sin p ∧ Real.sin p<129/200 := by
  have hp0 : 0≤p := by linarith [hp.1]
  have hp2 := pow_le_pow_left₀ hp0 hp.2 2
  have hp3 := pow_le_pow_left₀ hp0 hp.2 3
  obtain ⟨hc,hc1,hs,hsu,hsc⟩ := transport_trig ⟨hp0,hp.2⟩
  have hmul := mul_nonneg (sq_nonneg p) (show 0≤12-p^2 by nlinarith)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,hs,by linarith⟩
  · rw [S3_eval]; nlinarith [hp.1]
  · rw [S3_eval]; exact Real.sin_ge_sub_cube hp0
  · rw [S5_eval]; exact sin_upper_five hp0
  · rw [C2_eval]; nlinarith
  · rw [C2_eval]; exact Real.one_sub_sq_div_two_le_cos
  · rw [C4_eval]; exact cos_upper_four hp0
  · rw [C4_eval]; nlinarith

theorem z_bounds {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    (Zlo:ℝ)<z q p ∧ z q p≤radius q ∧ 0<q-(u q p)^2 := by
  obtain ⟨-,-,hpl,hpu⟩ := constant_bounds hq
  obtain ⟨-,hs3s,-,-,-,-,-,-,hshi⟩ := taylor_bounds hp
  have hp3 := pow_le_pow_left₀ (show 0≤p by linarith [hp.1]) hp.2 3
  have eP : (Plo:ℝ)=3991/10000 := by norm_num [Plo]
  have eQ : (Phi:ℝ)=3993/10000 := by norm_num [Phi]
  have eZ : (Zlo:ℝ)=981/500 := by norm_num [Zlo]
  rw [S3_eval] at hs3s
  have hu : -(123/500 : ℝ)<u q p ∧ u q p<123/500 := by
    unfold u
    constructor
    · linarith only [hpl,eP,hshi]
    · linarith only [hpu,eQ,hs3s,hp3,hp.1]
  have hu2 : (u q p)^2<(123/500 : ℝ)^2 := sq_lt_sq' hu.1 hu.2
  have hzrad : (Zlo:ℝ)^2<q-(u q p)^2 := by
    have hq1 : (19577/5000:ℝ)≤q := hq.1
    rw [eZ]
    linarith only [hq1,hu2]
  have hz0 : 0<q-(u q p)^2 := lt_of_le_of_lt (sq_nonneg _) hzrad
  refine ⟨(Real.lt_sqrt (by rw [eZ]; norm_num)).mpr hzrad,?_,hz0⟩
  exact Real.sqrt_le_sqrt (by linarith only [sq_nonneg (u q p)])

/-- Bounds used in the polynomial transfer, proved from the reference solution at the
original q. -/
structure Bounds (q p : ℝ) : Prop where
  radius_lower : (Rlo:ℝ)<radius q
  radius_upper : radius q<(Rhi:ℝ)
  z_lower : (Zlo:ℝ)<z q p
  z_upper : z q p≤radius q
  x_lower : aeval p Xlo≤x q p
  x_upper : x q p≤aeval p Xhi
  y_lower : aeval p Ylo≤y q p
  y_upper : y q p≤aeval p Yhi
  beta_lower : aeval p Xlo*aeval p Alo≤beta q p
  radius_factor : aeval p Alo≤1-Real.cos p/radius q
  ell_lower : aeval p Llo≤ell q p
  sine_lower : 0≤Real.sin p
  sine_upper : Real.sin p≤aeval p S5

theorem bounds {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) : Bounds q p := by
  obtain ⟨hrl,hru,hpl,hpu⟩ := constant_bounds hq
  obtain ⟨hzl,hzr,-⟩ := z_bounds hq hp
  obtain ⟨hs3,hs3s,hss5,hc2,hc2c,hcc4,-,hs,-⟩ := taylor_bounds hp
  obtain ⟨-,-,hxl,-,ha,-⟩ := factors_positive hp
  have eR : (Rhi:ℝ)=4947/2500 := by norm_num [Rhi]
  have eZ : (Zlo:ℝ)=981/500 := by norm_num [Zlo]
  have eP : (Plo:ℝ)=3991/10000 := by norm_num [Plo]
  have eQ : (Phi:ℝ)=3993/10000 := by norm_num [Phi]
  have hc : 0≤Real.cos p := hc2.le.trans hc2c
  have hc4 : 0≤aeval p C4 := hc.trans hcc4
  have hP0 : 0≤leastPrimary q := by linarith only [hpl,eP]
  have hc1 := Real.cos_le_one p
  have hz0 : 0<z q p := by linarith only [hzl,eZ]
  have hXl : aeval p Xlo≤x q p := by
    have h1 := mul_le_mul hzl.le hc2c hc2.le hz0.le
    have h2 := mul_le_mul hpu.le hss5 hs (by linarith only [eQ])
    have h3 := pow_le_pow_left₀ hs3 hs3s 2
    simp only [Xlo,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast]
    dsimp only [x,u]
    linarith only [h1,h2,h3]
  have hXu : x q p≤aeval p Xhi := by
    have h1 := mul_le_mul (hzr.trans hru.le) hcc4 hc (by linarith only [eR])
    have h2 := mul_le_mul hpl.le hs3s hs3 hP0
    have h3 := pow_le_pow_left₀ hs hss5 2
    simp only [Xhi,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast]
    dsimp only [x,u]
    linarith only [h1,h2,h3]
  have hYl : aeval p Ylo≤y q p := by
    have h1 := mul_le_mul (sub_le_sub hzl.le hcc4) hs3s hs3
      (by linarith only [hzl,eZ,hc1] : 0≤z q p-Real.cos p)
    have h2 := mul_le_mul hpl.le hc2c hc2.le hP0
    simp only [Ylo,map_add,map_sub,map_mul,aeval_C,eq_ratCast]
    dsimp only [y,u]
    linarith only [h1,h2]
  have hYu : y q p≤aeval p Yhi := by
    have h1 := mul_le_mul (sub_le_sub (hzr.trans hru.le) hc2c) hss5 hs
      (by linarith only [eR,hc2c,hc1])
    have h2 := mul_le_mul hpu.le hcc4 hc (by linarith only [eQ])
    simp only [Yhi,map_add,map_sub,map_mul,aeval_C,eq_ratCast]
    dsimp only [y,u]
    linarith only [h1,h2]
  have hfac : aeval p Alo≤1-Real.cos p/z q p := by
    have hh := div_le_div₀ hc4 hcc4 (by rw [eZ]; norm_num) hzl.le
    simp only [Alo,map_sub,map_mul,map_one,aeval_C,eq_ratCast,Rat.cast_div,Rat.cast_one]
    rw [eZ] at hh ⊢
    linarith only [hh]
  have hfacR : aeval p Alo≤1-Real.cos p/radius q := by
    have hh := div_le_div₀ hc le_rfl hz0 hzr
    linarith only [hh,hfac]
  have hb : aeval p Xlo*aeval p Alo≤beta q p :=
    mul_le_mul hXl hfac ha.le (hxl.le.trans hXl)
  have he : aeval p Llo≤ell q p := by
    have hh := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
    have hcos : (478/625 : ℝ)<Real.cos (7/10 : ℝ) := by norm_num at hh ⊢; linarith
    simp only [Llo,map_sub,aeval_C,eq_ratCast]
    dsimp only [ell]
    push_cast
    linarith only [hYu,hcos]
  exact ⟨hrl,hru,hzl,hzr,hXl,hXu,hYl,hYu,hb,hfacR,he,hs,hss5⟩

/-- `Ylo - 1/2` has positive Bernstein coefficients of degree seven on `[11/50, 7/10]`. -/
theorem y_gt_half {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) : 1/2<y q p := by
  have h0 : 0≤p-11/50 := sub_nonneg.2 hp.1
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤(p-11/50)^i*(7/10-p)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  have hh : 1/2<aeval p Ylo := by
    simp only [Ylo,S3,C2,C4,Zlo,Plo,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
      eq_ratCast]
    push_cast
    linarith [hb 7 0,hb 6 1,hb 5 2,hb 4 3,hb 3 4,hb 2 5,hb 1 6,hb 0 7]
  linarith [(bounds hq hp).y_lower]

theorem root_bounds {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    0<ell q p ∧ ell q p<3/2 ∧ 0<root q p ∧ root q p≤radius q := by
  have hb := bounds hq hp
  have hy := y_gt_half hq hp
  have hl : 0<ell q p := (factors_positive hp).2.2.2.2.2.trans_le hb.ell_lower
  have hlu : ell q p<3/2 := by dsimp [ell]; linarith [Real.cos_le_one (7/10 : ℝ)]
  have hr : 0<q-(ell q p)^2 := by
    have hq0 := hq.1
    dsimp [qLow] at hq0
    nlinarith
  exact ⟨hl,hlu,Real.sqrt_pos.mpr hr,
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (ell q p)])⟩

theorem derivative_pos {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) : 0<gapDerivative q p := by
  have hb := bounds hq hp
  have hr := root_bounds hq hp
  exact OutsideDE2Polynomial.derivative_positive hp hb.radius_lower.le hb.radius_upper.le
    hb.x_lower hb.x_upper hb.y_lower hb.ell_lower hr.2.2.1 hr.2.2.2
    hb.beta_lower hb.radius_factor hb.sine_lower hb.sine_upper

theorem contact_circle {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    (x q p)^2+(y q p)^2=q ∧
      y q p*Real.cos p-(x q p-1)*Real.sin p=leastPrimary q := by
  have hz : (z q p)^2=q-(u q p)^2 := Real.sq_sqrt (z_bounds hq hp).2.2.le
  have hu := Real.sin_sq_add_cos_sq p
  have hid (Z U s c : ℝ) : (Z*c-U*s)^2+(Z*s+U*c)^2=(Z^2+U^2)*(s^2+c^2) := by ring
  have hi2 (Z U s c : ℝ) : (Z*s+U*c)*c-(Z*c-U*s-1)*s=U*(s^2+c^2)+s := by ring
  constructor
  · rw [x,y,hid,hu]
    linarith
  · rw [x,y,hi2,hu]
    simp [u]

end SquaresInCircles.Eight.OutsideDE2Reference
end
end
end

section
/-!
## The actual E radial arcs used by the outside transport

Feasible EH1 below a primary smaller than one forces a
true-core E onto its flat arc. The other radial kind is E's own actual outer
q-circle. All arc coordinates, derivatives, sorting and circle values below
are proved from these original radial kinds.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace OutsideE

inductive ArcKind where
  | flatCore
  | outerCircle

def ArcKind.primary (kind : ArcKind) (q b : ℝ) : ℝ :=
  match kind with
  | .flatCore => 7/12
  | .outerCircle => Real.sqrt (q-(b+1/2)^2)-1/2

def ArcKind.point (kind : ArcKind) (q b : ℝ) : SignedPoint :=
  ⟨kind.primary q b,-b⟩

def ArcKind.slope (kind : ArcKind) (q b : ℝ) : ℝ :=
  match kind with
  | .flatCore => 0
  | .outerCircle => (b+1/2)/Real.sqrt (q-(b+1/2)^2)

structure ArcSource (q : ℝ) (E : SignedPoint) (kind : ArcKind) : Prop where
  sorted : E.Sorted
  nonpos : E.y≤0
  flat : kind=.flatCore → E.a=7/12 ∧ -E.y<9/40
  outer : kind=.outerCircle → E.Outer q

theorem core_eh1_flat {H E : SignedPoint} {p : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.Core)
    (hHa : H.a<1) (hp : p∈Icc 0 (7/10 : ℝ))
    (hf : quarterFeasible E H p 1) : E.a=7/12 ∧ -E.y<9/40 := by
  have hEa := SignedPoint.core_primary_le hEs hEc
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hp
  have hw := edgeWidth_positive_formula hp
  have hfeas : (1+Real.cos p+Real.sin p)/2≤
      H.a+E.a*Real.sin p+E.y*Real.cos p := by
    simpa [quarterFeasible,quarterProjection,hw] using hf
  have hmul := mul_le_mul_of_nonneg_right hEa hs0
  have hb : -E.y<9/40 := by
    by_contra! hbad
    have hlo := mul_lt_mul_of_pos_left hc (show (0:ℝ)<29/40 by norm_num)
    have hcmp := mul_le_mul_of_nonneg_right
      (show (29/40 : ℝ)≤ -E.y+1/2 by linarith) (by linarith : 0≤Real.cos p)
    nlinarith
  have habs : |E.y|≤1/2 := by rw [abs_of_nonpos hEy]; linarith
  exact ⟨(SignedPoint.flat_core_iff hEs habs).1 hEc,hb⟩

theorem arcSource_of_boundary {q p : ℝ} {H E : SignedPoint}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hHa : H.a<1) (hp : p∈Icc 0 (7/10 : ℝ))
    (hf : quarterFeasible E H p 1) : ∃ kind, ArcSource q E kind := by
  rcases hEr with ho | hc
  · exact ⟨.outerCircle,⟨hEs,hEy,(by intro h; cases h),fun _ => ho⟩⟩
  · exact ⟨.flatCore,⟨hEs,hEy,fun _ => core_eh1_flat hEs hEy hc hHa hp hf,
      (by intro h; cases h)⟩⟩

theorem ArcKind.continuous_primary (kind : ArcKind) (q : ℝ) :
    Continuous (kind.primary q) := by
  cases kind
  · exact continuous_const
  · show Continuous (fun b : ℝ => Real.sqrt (q-(b+1/2)^2)-1/2)
    fun_prop

theorem ArcSource.initial {q : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) : kind.point q (-E.y)=E := by
  have ha : kind.primary q (-E.y)=E.a := by
    cases kind with
    | flatCore => exact (I.flat rfl).1.symm
    | outerCircle =>
      have ho := I.outer rfl
      have heq : q-(-E.y+1/2)^2=(E.a+1/2)^2 := by
        simp only [SignedPoint.Outer,SignedPoint.circle,abs_of_nonpos I.nonpos] at ho
        linarith
      dsimp [ArcKind.primary]
      rw [heq,Real.sqrt_sq_eq_abs,abs_of_pos (by linarith [I.sorted.1] : 0<E.a+1/2)]
      ring
  unfold ArcKind.point
  rw [ha,neg_neg]

theorem ArcSource.geometry {q b : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    (kind.point q b).Sorted ∧ (kind.point q b).Contained q ∧
      (kind.point q b).AvoidsCore ∧ (kind.point q b).Boundary q ∧
      (kind.point q b).circle≤E.circle ∧
      1/2<kind.primary q b ∧ b≤kind.primary q b := by
  cases kind with
  | flatCore =>
    obtain ⟨hEa,hEb⟩ := I.flat rfl
    have hbsmall : |-b|≤1/2 := by rw [abs_neg,abs_of_nonneg hb.1]; linarith [hb.2]
    have hs := SignedPoint.flat_sorted hbsmall
    have hc := SignedPoint.flat_contained hq hbsmall
    have hcore := SignedPoint.flat_on_core hbsmall
    have hloss : (SignedPoint.flat (-b)).circle≤E.circle := by
      have hbsq := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hb.1])
        (show b+1/2≤ -E.y+1/2 by linarith [hb.2]) 2
      simpa [SignedPoint.circle,SignedPoint.flat,hEa,abs_of_nonpos I.nonpos,
        abs_neg,abs_of_nonneg hb.1] using add_le_add_left hbsq ((13/12 : ℝ)^2)
    exact ⟨hs,hc,hcore.ge,Or.inr hcore,hloss,by norm_num [ArcKind.primary],by
      dsimp [ArcKind.primary]; linarith [hb.2]⟩
  | outerCircle =>
    have hediag := SignedPoint.contained_minor_le_diagonal I.sorted (I.outer rfl).le
    have hbdiag : |-b|≤diagonalCoordinate q := by
      rw [abs_neg,abs_of_nonneg hb.1]
      exact hb.2.trans (by simpa [abs_of_nonpos I.nonpos] using hediag)
    have heq : ArcKind.outerCircle.point q b=SignedPoint.outerAt q (-b) := by
      simp [ArcKind.point,ArcKind.primary,SignedPoint.outerAt,
        abs_neg,abs_of_nonneg hb.1]
    obtain ⟨hs,ho,hcore⟩ := SignedPoint.outerAt_spec hq hbdiag
    rw [heq]
    have hprim : 1/2<(SignedPoint.outerAt q (-b)).a :=
      SignedPoint.primary_gt_half hs hcore
    have hsort : b≤(SignedPoint.outerAt q (-b)).a := by
      simpa [SignedPoint.outerAt,abs_neg,abs_of_nonneg hb.1] using hs.2
    exact ⟨hs,ho.le,hcore,Or.inl ho,ho.trans (I.outer rfl).symm |>.le,
      by simpa [SignedPoint.outerAt,ArcKind.primary,abs_neg,abs_of_nonneg hb.1] using hprim,
      by simpa [SignedPoint.outerAt,ArcKind.primary,abs_neg,abs_of_nonneg hb.1] using hsort⟩

theorem ArcSource.derivative {q b : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (kind.primary q) (-kind.slope q b) b ∧
      0≤kind.slope q b ∧ kind.slope q b≤1 := by
  cases kind with
  | flatCore =>
    refine ⟨?_,by show (0:ℝ) ≤ 0; exact le_rfl,by show (0:ℝ) ≤ 1; norm_num⟩
    show HasDerivAt (fun _ : ℝ => (7/12:ℝ)) (-0) b
    rw [neg_zero]
    exact hasDerivAt_const b _
  | outerCircle =>
    have hgeom := I.geometry hq hb
    have hroot : 0<Real.sqrt (q-(b+1/2)^2) := by
      have hh := hgeom.2.2.2.2.2.1
      dsimp [ArcKind.primary] at hh
      linarith
    have hrad : 0<q-(b+1/2)^2 := Real.sqrt_pos.mp hroot
    have hd := ((hasDerivAt_const b q).fun_sub
      (((hasDerivAt_id' b).add_const (1/2)).fun_pow 2)).sqrt hrad.ne'
    refine ⟨?_,?_,?_⟩
    · convert hd.sub_const (1/2) using 1
      · rfl
      · show -((b+1/2)/Real.sqrt (q-(b+1/2)^2))=_
        field_simp
        push_cast
        ring
    · exact div_nonneg (by linarith [hb.1]) hroot.le
    · apply (div_le_one hroot).2
      have hh := hgeom.2.2.2.2.2.2
      dsimp [ArcKind.primary] at hh
      linarith

theorem ArcSource.radial_identity {q b : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    (kind=.flatCore ∧ kind.slope q b=0 ∧ b≤1/2) ∨
      b-kind.slope q b*kind.primary q b= -(1-kind.slope q b)/2 := by
  cases kind with
  | flatCore =>
    exact Or.inl ⟨rfl,rfl,by linarith [(I.flat rfl).2,hb.2]⟩
  | outerCircle =>
    right
    have hg := I.geometry hq hb
    have hr : 0<Real.sqrt (q-(b+1/2)^2) := by
      have hh := hg.2.2.2.2.2.1
      dsimp [ArcKind.primary] at hh
      linarith
    dsimp only [ArcKind.slope,ArcKind.primary]
    generalize Real.sqrt (q-(b+1/2)^2)=r at hr ⊢
    field_simp
    ring

def ehSlack (kind : ArcKind) (q : ℝ) (H : SignedPoint) (p b : ℝ) : ℝ :=
  H.a-1/2+(kind.primary q b-1/2)*Real.sin p-(b+1/2)*Real.cos p

def de3Slack (kind : ArcKind) (q α : ℝ) (D : SignedPoint) (p b : ℝ) : ℝ :=
  D.a-1/2-(kind.primary q b+1/2)*Real.sin (p-α)+(b-1/2)*Real.cos (p-α)

def de2Slack (D : SignedPoint) (α p b : ℝ) : ℝ :=
  (D.a-1/2)*Real.cos (p-α)+(D.y-1/2)*Real.sin (p-α)+b-1/2

theorem ehSlack_actual (kind : ArcKind) (q : ℝ) (H : SignedPoint) {p : ℝ} (b : ℝ)
    (hp : p∈Icc 0 (7/10 : ℝ)) :
    ehSlack kind q H p b=quarterProjection (kind.point q b) H p 1-edgeWidth p := by
  rw [edgeWidth_positive_formula hp]
  simp [ehSlack,quarterProjection,ArcKind.point]
  ring

theorem de3Slack_actual (kind : ArcKind) (q α : ℝ) (D : SignedPoint) {p : ℝ} (b : ℝ)
    (hn : p-α∈Icc 0 (7/10 : ℝ)) :
    de3Slack kind q α D p b=
      quarterProjection D (kind.point q b) (-(p-α)) 3-edgeWidth (-(p-α)) := by
  rw [edgeWidth_negative_formula hn]
  simp only [de3Slack,quarterProjection,ArcKind.point,Matrix.cons_val,Real.sin_neg,
    Real.cos_neg]
  ring

theorem de2Slack_actual (kind : ArcKind) (q α : ℝ) (D : SignedPoint) {p : ℝ} (b : ℝ)
    (hn : p-α∈Icc 0 (7/10 : ℝ)) :
    de2Slack D α p b=
      quarterProjection D (kind.point q b) (-(p-α)) 2-edgeWidth (-(p-α)) := by
  rw [edgeWidth_negative_formula hn]
  simp only [de2Slack,quarterProjection,ArcKind.point,Matrix.cons_val,Real.sin_neg,
    Real.cos_neg]
  ring

end OutsideE
end SquaresInCircles.Eight
end
end
end

section
/-!
## Strict simultaneous improvement directions for negative DE3 and positive EH1

The angular and radial rates are those of the original
physical projections. A small amount beyond the exact EH1-contact speed
makes both margins strictly improve, on either actual radial kind. These
directions supply compact endpoint attainment without an assumed path.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace OutsideE

def contactSpeed (a b v p : ℝ) : ℝ :=
  ((a-1/2)*Real.cos p+(b+1/2)*Real.sin p)/(Real.cos p+v*Real.sin p)

theorem contactSpeed_positive {a b v p : ℝ}
    (ha : 1/2<a) (hb : 0≤b) (hv : 0≤v)
    (hp : p∈Icc 0 (7/10 : ℝ)) :
    0<Real.cos p+v*Real.sin p ∧ 0<contactSpeed a b v p := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hp
  have hcpos : 0<Real.cos p := by linarith
  have hden : 0<Real.cos p+v*Real.sin p :=
    add_pos_of_pos_of_nonneg hcpos (mul_nonneg hv hs0)
  refine ⟨hden,div_pos ?_ hden⟩
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr ha) hcpos) (mul_nonneg (by linarith) hs0)

/-- The DE3 improvement is uniform in both angle orders. In particular,
no sign of the original H/D span occurs in this calculation. -/
theorem de3_contact_rate_positive {a b v p n : ℝ}
    (hb : 0≤b) (hv : 0≤v ∧ v≤1)
    (hp : p∈Icc 0 (7/10 : ℝ)) (hn : n∈Icc 0 (7/10 : ℝ))
    (hr : (v=0 ∧ b≤1/2) ∨ b-v*a= -(1-v)/2) :
    0<(a+1/2-contactSpeed a b v p)*Real.cos n+
      (b-1/2-v*contactSpeed a b v p)*Real.sin n := by
  obtain ⟨hcp,hcp1,hsp0,hsp,hspcp⟩ := transport_trig hp
  obtain ⟨hcn,hcn1,hsn0,hsn,hsncn⟩ := transport_trig hn
  have hcp0 : 0<Real.cos p := by linarith
  have hcn0 : 0<Real.cos n := by linarith
  let den := Real.cos p+v*Real.sin p
  have hden : 0<den := add_pos_of_pos_of_nonneg hcp0 (mul_nonneg hv.1 hsp0)
  let W := (a+1/2-contactSpeed a b v p)*Real.cos n+
    (b-1/2-v*contactSpeed a b v p)*Real.sin n
  have hid : W*den=
      Real.cos n*Real.cos p-(1-v)/2*
        (Real.sin n*Real.cos p+Real.cos n*Real.sin p)+
      (b-v*a)*(Real.sin n*Real.cos p-Real.cos n*Real.sin p)-
      v*Real.sin n*Real.sin p := by
    have hβ₀ : contactSpeed a b v p*(Real.cos p+v*Real.sin p)=
        (a-1/2)*Real.cos p+(b+1/2)*Real.sin p := by
      unfold contactSpeed; exact div_mul_cancel₀ _ hden.ne'
    simp only [W,den]
    linear_combination (-(Real.cos n+v*Real.sin n))*hβ₀
  have hscaled : 0<W*den := by
    rcases hr with ⟨hvzero,hbhalf⟩ | hr
    · have heq : W*den=(1/2-b)*Real.cos p*(Real.cos n-Real.sin n)+
          (1/2+b)*Real.cos n*(Real.cos p-Real.sin p) := by
        rw [hid,hvzero]
        ring
      rw [heq]
      apply add_pos_of_nonneg_of_pos
      · exact mul_nonneg (mul_nonneg (by linarith) hcp0.le)
          (sub_nonneg.mpr hsncn.le)
      · exact mul_pos (mul_pos (by linarith) hcn0) (sub_pos.mpr hspcp)
    · have heq : W*den=Real.cos p*(Real.cos n-Real.sin n)+
          v*Real.sin n*(Real.cos p-Real.sin p) := by
        rw [hid,hr]
        ring
      rw [heq]
      exact add_pos_of_pos_of_nonneg (mul_pos hcp0 (sub_pos.mpr hsncn))
        (mul_nonneg (mul_nonneg hv.1 hsn0) (sub_nonneg.mpr hspcp.le))
  exact (mul_pos_iff_of_pos_right hden).1 hscaled

theorem ArcSource.de3_improving_speed {q b p n : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y))
    (hp : p∈Icc 0 (7/10 : ℝ)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    ∃ β, 0<β ∧
      0<β*(Real.cos p+kind.slope q b*Real.sin p)-
        ((kind.primary q b-1/2)*Real.cos p+(b+1/2)*Real.sin p) ∧
      0<(kind.primary q b+1/2-β)*Real.cos n+
        (b-1/2-kind.slope q b*β)*Real.sin n := by
  let a := kind.primary q b
  let v := kind.slope q b
  let β₀ := contactSpeed a b v p
  let c := Real.cos n+v*Real.sin n
  let W := (a+1/2-β₀)*Real.cos n+(b-1/2-v*β₀)*Real.sin n
  have hg := I.geometry hq hb
  have hd := I.derivative hq hb
  have hrad := I.radial_identity hq hb
  have hdenβ := contactSpeed_positive hg.2.2.2.2.2.1 hb.1 hd.2.1 hp
  have hW : 0<W := by
    apply de3_contact_rate_positive hb.1 hd.2 hp hn
    rcases hrad with ⟨hk,hv,hb⟩ | hr
    · exact Or.inl ⟨hv,hb⟩
    · exact Or.inr hr
  have hc : 0<c := by
    obtain ⟨hnc,hnc1,hns,hns1,hsc⟩ := transport_trig hn
    exact add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg hd.2.1 hns)
  let η := W/(2*c)
  have hη : 0<η := div_pos hW (mul_pos (by norm_num) hc)
  have hηc : η*c=W/2 := by
    dsimp [η]
    field_simp [hc.ne']
  refine ⟨β₀+η,add_pos hdenβ.2 hη,?_,?_⟩
  · have heq : (β₀+η)*(Real.cos p+v*Real.sin p)-
        ((a-1/2)*Real.cos p+(b+1/2)*Real.sin p)=
        η*(Real.cos p+v*Real.sin p) := by
      have hβ₀ : contactSpeed a b v p*(Real.cos p+v*Real.sin p)=
          (a-1/2)*Real.cos p+(b+1/2)*Real.sin p := by
        unfold contactSpeed; exact div_mul_cancel₀ _ hdenβ.1.ne'
      simp only [β₀]
      linear_combination hβ₀
    rw [heq]
    exact mul_pos hη hdenβ.1
  · have heq : (a+1/2-(β₀+η))*Real.cos n+
        (b-1/2-v*(β₀+η))*Real.sin n=W-η*c := by
      dsimp [W,c]
      ring
    rw [heq,hηc]
    linarith

theorem de3_fixed_tangent_rate_positive {a b n : ℝ}
    (ha : 1/2<a) (hb : 0≤b) (hn : n∈Icc 0 (7/10 : ℝ)) :
    0<(a+1/2)*Real.cos n+(b-1/2)*Real.sin n := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hn
  have haC := mul_pos (show 0<a by linarith) (show 0<Real.cos n by linarith)
  have hbS := mul_nonneg hb hs0
  nlinarith

theorem ArcSource.eh_direction_derivative {q b p β : ℝ} {E H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind)
    (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => ehSlack kind q H (p-τ) (b-β*τ))
      (β*(Real.cos p+kind.slope q b*Real.sin p)-
        ((kind.primary q b-1/2)*Real.cos p+(b+1/2)*Real.sin p)) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul β).const_sub b
  have hpder : HasDerivAt (fun τ : ℝ => p-τ) (-1) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub p
  have ha0 : HasDerivAt (kind.primary q) (-kind.slope q b) (b-β*0) := by
    simpa using (I.derivative hq hb).1
  have hader := ha0.comp 0 hbder
  have hsder := (Real.hasDerivAt_sin (p-0)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos (p-0)).comp 0 hpder
  convert ((hasDerivAt_const (0:ℝ) (H.a-1/2)).fun_add
    ((hader.sub_const (1/2)).fun_mul hsder)).fun_sub
      ((hbder.add_const (1/2)).fun_mul hcder) using 1
  · funext τ
    simp only [ehSlack,Function.comp_apply]
  · simp only [Function.comp_apply,sub_zero,mul_zero]
    ring

theorem ArcSource.de3_direction_derivative {q α b p β : ℝ} {E D : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind)
    (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => de3Slack kind q α D (p-τ) (b-β*τ))
      ((kind.primary q b+1/2-β)*Real.cos (p-α)+
        (b-1/2-kind.slope q b*β)*Real.sin (p-α)) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul β).const_sub b
  have hpder : HasDerivAt (fun τ : ℝ => (p-τ)-α) (-1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_sub p).sub_const α
  have ha0 : HasDerivAt (kind.primary q) (-kind.slope q b) (b-β*0) := by
    simpa using (I.derivative hq hb).1
  have hader := ha0.comp 0 hbder
  have hsder := (Real.hasDerivAt_sin ((p-0)-α)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos ((p-0)-α)).comp 0 hpder
  convert ((hasDerivAt_const (0:ℝ) (D.a-1/2)).fun_sub
    ((hader.add_const (1/2)).fun_mul hsder)).fun_add
      ((hbder.sub_const (1/2)).fun_mul hcder) using 1
  · funext τ
    simp only [de3Slack,Function.comp_apply]
  · simp only [Function.comp_apply,sub_zero,mul_zero]
    ring

theorem de2_direction_derivative (D : SignedPoint) (α b p β : ℝ) :
    HasDerivAt (fun τ => de2Slack D α (p-τ) (b-β*τ))
      ((D.a-1/2)*Real.sin (p-α)+(1/2-D.y)*Real.cos (p-α)-β) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul β).const_sub b
  have hpder : HasDerivAt (fun τ : ℝ => (p-τ)-α) (-1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_sub p).sub_const α
  have hsder := (Real.hasDerivAt_sin ((p-0)-α)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos ((p-0)-α)).comp 0 hpder
  convert ((((hcder.const_mul (D.a-1/2)).add
    (hsder.const_mul (D.y-1/2))).add hbder).sub_const (1/2)) using 1 <;>
    simp [de2Slack]
  ring

end OutsideE
end SquaresInCircles.Eight
end
end
end

section
/-!
## The actual zero-tangent endpoints of the outside-E transport

A flat-core EH1 contact supplies the actual EH0 axis
using H's original outer circle. An outer-E contact at long EH error is
incompatible with the high sorted H tangent. These discharge the radial
boundary of compact endpoint attainment.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace OutsideE

theorem flat_zero_contact_eh0 {q p : ℝ} {H : SignedPoint}
    (hq : qLow≤q) (_hHs : H.Sorted) (hHy : 0≤H.y) (hHo : H.Outer q)
    (hp : p∈Ioc 0 (7/10 : ℝ))
    (hcontact : ehSlack .flatCore q H p 0=0) :
    quarterFeasible (ArcKind.flatCore.point q 0) H p 0 := by
  let X := H.a+1/2
  let Y := H.y+1/2
  let Z := 1+(1/12 : ℝ)*Real.cos p+(1/2 : ℝ)*Real.sin p
  have ht := transport_trig ⟨hp.1.le,hp.2⟩
  have hs0 : 0≤Real.sin p := ht.2.2.1
  have hc0 : 0<Real.cos p := by linarith [ht.1]
  have hspos : 0<Real.sin p := Real.sin_pos_of_pos_of_lt_pi hp.1
    (by linarith [hp.2,Real.pi_gt_three])
  have hX : X=1+Real.cos p/2-Real.sin p/12 := by
    dsimp [ehSlack,ArcKind.primary] at hcontact
    dsimp [X]
    linarith
  have hlinear : (7/6 : ℝ)*Real.cos p+(5/6 : ℝ)*Real.sin p<3/2 := by
    have hrot : ((7/6 : ℝ)*Real.cos p+(5/6 : ℝ)*Real.sin p)^2+
        ((7/6 : ℝ)*Real.sin p-(5/6 : ℝ)*Real.cos p)^2=74/36 := by
      nlinarith [Real.sin_sq_add_cos_sq p]
    nlinarith [sq_nonneg ((7/6 : ℝ)*Real.sin p-(5/6 : ℝ)*Real.cos p)]
  have hnorm : X^2+Z^2<541/144 := by
    rw [hX]
    dsimp [Z]
    nlinarith [Real.sin_sq_add_cos_sq p]
  have hHcircle : X^2+Y^2=q := by
    simpa [X,Y,SignedPoint.Outer,SignedPoint.circle,abs_of_nonneg hHy] using hHo
  have hYZ : Z<Y := by
    have hY : 0<Y := by dsimp [Y]; linarith
    have hZ : 0<Z := by dsimp [Z]; positivity
    dsimp [qLow] at hq
    nlinarith
  have hid : quarterProjection (ArcKind.flatCore.point q 0) H p 0-edgeWidth p=
      Real.sin p*(Y-Z) := by
    rw [edgeWidth_positive_formula ⟨hp.1.le,hp.2⟩]
    have hHa : H.a=1/2+Real.cos p/2-Real.sin p/12 := by dsimp [X] at hX; linarith
    simp only [quarterProjection,ArcKind.point,Y,Z,Matrix.cons_val_zero]
    rw [hHa]
    linear_combination (1/2 : ℝ)*Real.sin_sq_add_cos_sq p
  apply sub_nonneg.mp
  rw [hid]
  exact (mul_pos hspos (sub_pos.mpr hYZ)).le

theorem outer_zero_long_contact_false {q p : ℝ} {H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHy : 211/250<H.y)
    (hp : p∈Icc (11/50 : ℝ) (7/10 : ℝ))
    (hcontact : ehSlack .outerCircle q H p 0=0) : False := by
  have hha : 211/250<H.a := hHy.trans_le ((le_abs_self _).trans hHs.2)
  have hroot := (uniform_circle_reserves hqL hqU).2.2.1
  have ha : 7/5<ArcKind.outerCircle.primary q 0 := by
    have h14 : (0+1/2 : ℝ)^2=1/4 := by norm_num
    simp only [ArcKind.primary,h14]
    linarith
  have hp0 : 0≤p := by linarith [hp.1]
  have hsin : 1/5<Real.sin p := by
    have hpoly := Real.sin_ge_sub_cube hp0
    have hp2 : p^2≤(7/10 : ℝ)^2 := by nlinarith [hp.2]
    have hp3 : p^3≤(7/10 : ℝ)^2*p := by
      have hh := mul_nonneg hp0 (sub_nonneg.mpr hp2)
      nlinarith
    nlinarith [hp.1]
  have hs0 : 0≤Real.sin p := by linarith
  have hmul := mul_lt_mul_of_pos_right
    (show (9/10 : ℝ)<ArcKind.outerCircle.primary q 0-1/2 by linarith)
    (show 0<Real.sin p by linarith)
  dsimp [ehSlack] at hcontact
  nlinarith [Real.cos_le_one p]

/-- The only zero-tangent first contact supplies the advertised EH0 stop.
No core, circle, or tangent-floor alternative is left implicit. -/
theorem ArcSource.zero_contact_eh0 {q p : ℝ} {E H : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHy : 211/250<H.y) (hHo : H.Outer q)
    (hp : p∈Icc (11/50 : ℝ) (7/10 : ℝ))
    (hcontact : ehSlack kind q H p 0=0) :
    quarterFeasible (kind.point q 0) H p 0 := by
  cases kind with
  | flatCore =>
    exact flat_zero_contact_eh0 hqL hHs (by linarith) hHo
      ⟨by linarith [hp.1],hp.2⟩ hcontact
  | outerCircle =>
    exact (outer_zero_long_contact_false hqL hqU hHs hHy hp hcontact).elim

end OutsideE
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace OutsideE

theorem eventually_nonneg_of_value_or_rate {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hf : 0≤f 0) (h : 0<f 0 ∨ 0<d) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ), 0≤f τ := by
  rcases h with hp | hr
  · exact ((hd.continuousAt.tendsto.eventually (eventually_gt_nhds hp)).mono
      (fun _ hh => hh.le)).filter_mono nhdsWithin_le_nhds
  · exact (NegativeContact.eventually_right_gt hd hr).mono
      (fun _ hh => hf.trans hh.le)

/-- The small real movement is selected only after strict derivative or
strict source-margin certificates have been supplied for both functions. -/
theorem feasible_shift_left {f g : ℝ → ℝ → ℝ} {l u b₀ p b β df dg : ℝ}
    (hp : p∈Ioc l u) (hb : b∈Icc 0 b₀) (hβ : 0≤β)
    (hfloor : β=0 ∨ 0<b)
    (hdf : HasDerivAt (fun τ => f (p-τ) (b-β*τ)) df 0)
    (hdg : HasDerivAt (fun τ => g (p-τ) (b-β*τ)) dg 0)
    (hf : 0≤f p b) (hg : 0≤g p b)
    (hfstrict : 0<f p b ∨ 0<df) (hgstrict : 0<g p b ∨ 0<dg) :
    ∃ z : ℝ×ℝ, z.1∈Icc l u ∧ z.2∈Icc 0 b₀ ∧
      0≤f z.1 z.2 ∧ 0≤g z.1 z.2 ∧ z.1<p := by
  have hfe := eventually_nonneg_of_value_or_rate hdf
    (by simpa using hf) (by simpa using hfstrict)
  have hge := eventually_nonneg_of_value_or_rate hdg
    (by simpa using hg) (by simpa using hgstrict)
  have hangle : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ<p-l :=
    (eventually_lt_nhds (sub_pos.mpr hp.1)).filter_mono nhdsWithin_le_nhds
  have hradial : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0≤b-β*τ := by
    rcases hfloor with hzero | hbpos
    · exact Filter.Eventually.of_forall (by intro τ; simpa [hzero] using hb.1)
    · have hc : ContinuousAt (fun τ : ℝ => b-β*τ) 0 := by fun_prop
      have hval : 0<(fun τ : ℝ => b-β*τ) 0 := by simpa using hbpos
      exact ((hc.tendsto.eventually (eventually_gt_nhds hval)).mono
        (fun _ hh => hh.le)).filter_mono nhdsWithin_le_nhds
  obtain ⟨τ,hτ,hangle,hradial,hfe,hge⟩ :=
    ((eventually_mem_nhdsWithin (s := Ioi (0:ℝ)) (a := 0)).and
      (hangle.and (hradial.and (hfe.and hge)))).exists
  have hτ0 : (0:ℝ)<τ := hτ
  refine ⟨⟨p-τ,b-β*τ⟩,⟨show l≤p-τ by linarith,show p-τ≤u by linarith [hp.2]⟩,
    ⟨hradial,?_⟩,hfe,hge,show p-τ<p by linarith⟩
  have hprod := mul_nonneg hβ hτ0.le
  linarith [hb.2]

structure DE3Endpoint (q : ℝ) (D E H : SignedPoint) (n p : ℝ) where
  point : SignedPoint
  movement : ℝ
  movement_nonneg : 0≤ movement
  movement_le_n : movement≤n
  error_positive : 0<p-movement
  sorted : point.Sorted
  contained : point.Contained q
  core : point.AvoidsCore
  radial : point.Boundary q
  nonpos : point.y≤0
  tangent_nonincrease : |point.y|≤|E.y|
  circle_nonincrease : point.circle≤E.circle
  DE3 : quarterFeasible D point (-(n-movement)) 3
  EH1 : quarterFeasible point H (p-movement) 1
  terminal : quarterFeasible point H (p-movement) 0 ∨
    p-movement≤11/50 ∨ (n-movement=0 ∧ 11/50<p-movement)

theorem de3_endpoint {q n p : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHy : 211/250<H.y) (hHa : H.a<1) (hHo : H.Outer q)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hn : n∈Ioc 0 (7/10 : ℝ)) (hp : p∈Ioc (11/50 : ℝ) (7/10 : ℝ))
    (hDE : quarterFeasible D E (-n) 3) (hEH : quarterFeasible E H p 1) :
    Nonempty (DE3Endpoint q D E H n p) := by
  obtain ⟨kind,I⟩ := arcSource_of_boundary hEs hEy hEr hHa
    ⟨by linarith [hp.1],hp.2⟩ hEH
  let α := p-n
  let l := max (11/50 : ℝ) α
  let f := ehSlack kind q H
  let g := de3Slack kind q α D
  have hlp : l<p := max_lt_iff.mpr ⟨hp.1,by dsimp [α]; linarith [hn.1]⟩
  have hlshort : 11/50≤l := le_max_left _ _
  have hlα : α≤l := le_max_right _ _
  have hparams {x : ℝ} (hx : x∈Icc l p) :
      x∈Icc (11/50 : ℝ) (7/10 : ℝ) ∧ x-α∈Icc 0 (7/10 : ℝ) := by
    constructor
    · exact ⟨hlshort.trans hx.1,hx.2.trans hp.2⟩
    · constructor
      · linarith [hx.1]
      · dsimp [α]; linarith [hx.2,hn.2]
  have hprim := kind.continuous_primary q
  have hcf : Continuous (fun z : ℝ×ℝ => f z.1 z.2) := by
    dsimp [f,ehSlack]
    fun_prop
  have hcg : Continuous (fun z : ℝ×ℝ => g z.1 z.2) := by
    dsimp [g,de3Slack]
    fun_prop
  let S : Set (ℝ×ℝ) :=
    ((Icc l p ×ˢ Icc 0 (-E.y)) ∩ {z | 0≤f z.1 z.2}) ∩ {z | 0≤g z.1 z.2}
  have hcompact : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hcf)).inter_right
      (isClosed_le continuous_const hcg)
  have hstart : (p,-E.y)∈S := by
    refine ⟨⟨⟨⟨hlp.le,le_rfl⟩,⟨neg_nonneg.mpr hEy,le_rfl⟩⟩,?_⟩,?_⟩
    · dsimp [f]
      rw [ehSlack_actual kind q H (-E.y) ⟨by linarith [hp.1],hp.2⟩,I.initial]
      exact sub_nonneg.mpr hEH
    · dsimp [g]
      rw [de3Slack_actual kind q α D (-E.y)
        (by dsimp [α]; simpa using ⟨hn.1.le,hn.2⟩),I.initial]
      simpa [α] using sub_nonneg.mpr hDE
  obtain ⟨z,hz,hmin⟩ := hcompact.exists_isMinOn ⟨(p,-E.y),hstart⟩
    continuous_fst.continuousOn
  let m := z.1
  let b := z.2
  have hm : m∈Icc l p := hz.1.1.1
  have hb : b∈Icc 0 (-E.y) := hz.1.1.2
  have hf : 0≤f m b := hz.1.2
  have hg : 0≤g m b := hz.2
  have hangles := hparams hm
  have hstop : quarterFeasible (kind.point q b) H m 0 ∨ m=l := by
    by_cases hEH0 : quarterFeasible (kind.point q b) H m 0
    · exact Or.inl hEH0
    right
    apply le_antisymm _ hm.1
    by_contra! hlm
    have hpm : m∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hangles.1.1],hangles.1.2⟩
    have hnear : ∃ z' : ℝ×ℝ, z'.1∈Icc l p ∧ z'.2∈Icc 0 (-E.y) ∧
        0≤f z'.1 z'.2 ∧ 0≤g z'.1 z'.2 ∧ z'.1<m := by
      by_cases hbzero : b=0
      · have hfpos : 0<f m b := by
          apply lt_of_le_of_ne hf
          intro heq
          have hcontact : ehSlack kind q H m 0=0 := by
            simpa [f,hbzero] using heq.symm
          exact hEH0 (by simpa [hbzero] using
            I.zero_contact_eh0 hqL hqU hHs hHy hHo hangles.1 hcontact)
        have hgpos := de3_fixed_tangent_rate_positive
          (I.geometry hqL hb).2.2.2.2.2.1 hb.1 hangles.2
        exact feasible_shift_left ⟨hlm,hm.2⟩ hb (le_rfl : (0:ℝ)≤0) (Or.inl rfl)
          (I.eh_direction_derivative (H := H) (p := m) (β := 0) hqL hb)
          (I.de3_direction_derivative (D := D) (α := α) (p := m) (β := 0) hqL hb)
          hf hg (Or.inl hfpos) (Or.inr (by simpa using hgpos))
      · have hbpos : 0<b := lt_of_le_of_ne hb.1 (Ne.symm hbzero)
        obtain ⟨β,hβ,hfpos,hgpos⟩ := I.de3_improving_speed hqL hb hpm hangles.2
        exact feasible_shift_left ⟨hlm,hm.2⟩ hb hβ.le (Or.inr hbpos)
          (I.eh_direction_derivative (H := H) (p := m) (β := β) hqL hb)
          (I.de3_direction_derivative (D := D) (α := α) (p := m) (β := β) hqL hb)
          hf hg (Or.inr hfpos) (Or.inr hgpos)
    obtain ⟨z',hz'p,hz'b,hz'f,hz'g,hz'lt⟩ := hnear
    have hz'S : z'∈S := ⟨⟨⟨hz'p,hz'b⟩,hz'f⟩,hz'g⟩
    have hh : m≤z'.1 := hmin hz'S
    linarith
  have hgeometry := I.geometry hqL hb
  have hEHfinal : quarterFeasible (kind.point q b) H m 1 := by
    have hh := hf
    dsimp [f] at hh
    rw [ehSlack_actual kind q H b ⟨by linarith [hangles.1.1],hangles.1.2⟩] at hh
    exact sub_nonneg.mp hh
  have hDEfinal : quarterFeasible D (kind.point q b) (-(n-(p-m))) 3 := by
    have hh := hg
    dsimp [g] at hh
    rw [de3Slack_actual kind q α D b hangles.2] at hh
    have heq : m-α=n-(p-m) := by dsimp [α]; ring
    rw [quarterFeasible,← heq]; exact sub_nonneg.mp hh
  have hterminal : quarterFeasible (kind.point q b) H m 0 ∨
      m≤11/50 ∨ (n-(p-m)=0 ∧ 11/50<m) := by
    rcases hstop with hstop | hstop
    · exact Or.inl hstop
    · by_cases hmshort : m≤11/50
      · exact Or.inr (Or.inl hmshort)
      · have hmα : m=α := by
          have hlEq : l=α := by
            apply max_eq_right
            by_contra! hα
            have hlEq : l=11/50 := max_eq_left hα.le
            linarith
          exact hstop.trans hlEq
        exact Or.inr (Or.inr ⟨by dsimp [α] at hmα; linarith,lt_of_not_ge hmshort⟩)
  exact ⟨{
    point := kind.point q b
    movement := p-m
    movement_nonneg := sub_nonneg.mpr hm.2
    movement_le_n := by dsimp [α] at hlα; linarith [hm.1]
    error_positive := by linarith [hangles.1.1]
    sorted := hgeometry.1
    contained := hgeometry.2.1
    core := hgeometry.2.2.1
    radial := hgeometry.2.2.2.1
    nonpos := by dsimp [ArcKind.point]; linarith [hb.1]
    tangent_nonincrease := by
      simp only [ArcKind.point,abs_neg,abs_of_nonneg hb.1,abs_of_nonpos hEy]
      exact hb.2
    circle_nonincrease := hgeometry.2.2.2.2.1
    DE3 := hDEfinal
    EH1 := by simpa using hEHfinal
    terminal := by simpa using hterminal }⟩

end OutsideE
end SquaresInCircles.Eight
end
end
end
