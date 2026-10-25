module

public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: A whole-interval polynomial for the long EH / DE2 contact

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
