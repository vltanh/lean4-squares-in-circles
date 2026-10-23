module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDCertificates

/-!
# From the negative-TD2 polynomials to the original three norms

Uncompiled transcription of equations (28)--(36). Both primary charges
are bounded on their own actual intervals. The original three pair
coefficients are unchanged. S11 bounds a subtracted sine and S9 bounds
an added sine, exactly as prescribed in the hand proof.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Analytic
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open TensorWholeIntervalPolynomial TwoVariablePolynomial
open Certificate (Kind)

def value (f : Kind) (t e : ℝ) : ℝ := match f with
  | .negative i => negativeScalar i t e
  | .equal => equalScalar t e
  | .positive i => positiveScalar i t e
  | .diagonal => DScalar t e

def nonradicalBase (t e : ℝ) : ℝ :=
  2*k e+3*l e+(5/2)*c+5/2-(1+c)*diagonal+primaryCost t e

def nonradical (f : Kind) (t e : ℝ) : ℝ := match f with
  | .negative i => nonradicalBase t e+q e i.castSucc*(Real.cos t-1)
  | .equal => nonradicalBase t e+speed*t
  | .positive i => nonradicalBase t e+speed*frameCap+
      p e i.castSucc*(Real.cos (frameCap-t)+Real.sin (frameCap-t)-1)
  | .diagonal => nonradicalBase t e+speed*frameCap-aD*(frameCap-t)

def normAngle (f : Kind) (j : Fin 3) (t : ℝ) : ℝ := match f with
  | .negative i => if i=j then -t else 0
  | .positive i => if i=j then frameCap-t else 0
  | _ => 0

def norm (f : Kind) (j : Fin 3) (t e : ℝ) : ℝ :=
  pairNorm (p e j.castSucc) (q e j.castSucc) (normAngle f j t)

theorem value_identity (f : Kind) (t e : ℝ) :
    value f t e=nonradical f t e-R*(norm f 0 t e+norm f 1 t e+norm f 2 t e) := by
  cases f with
  | negative i =>
    fin_cases i <;>
      simp only [value,negativeScalar,base_norms,nonradical,nonradicalBase,
        norm,normAngle,p,q,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Fin.reduceFinMk,ite_true,ite_false,V] <;> ring
  | equal =>
    simp only [value,equalScalar,base_norms,nonradical,nonradicalBase,norm,normAngle,
      p,q,Matrix.cons_val_zero,Matrix.cons_val_succ]
    ring
  | positive i =>
    fin_cases i <;>
      simp only [value,positiveScalar,base_norms,nonradical,nonradicalBase,
        norm,normAngle,p,q,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Fin.reduceFinMk,ite_true,ite_false,U,phi] <;> ring
  | diagonal =>
    simp only [value,DScalar,base_norms,nonradical,nonradicalBase,norm,normAngle,
      p,q,Matrix.cons_val_zero,Matrix.cons_val_succ]
    ring

theorem diagonal_upper : diagonal≤(Certificate.cbar:ℝ) := by
  have hs := diagonal_circle
  have hp := diagonal_bounds.1
  norm_num [qCap,Certificate.cbar] at hs ⊢
  nlinarith

theorem J_lower {u : Bivar} {t E : ℝ}
    (hu : evaluate t E u∈Icc 0 frameCap) :
    evaluate t E (Certificate.J u)≤TwoPositive.ASupport.charge (evaluate t E u) := by
  have hh := Charges.rectangle_E_charge hu
  simpa only [Certificate.J,map_sub,map_add,map_mul,map_pow,evaluate_scalar,evaluate_lift,
    Charges.polynomialJ,Certificate.abar,NonnegativeTotals.Certificate.abar,
    Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat] using hh

theorem base_lower {t E : ℝ} (hd : Certificate.Domain t E) :
    evaluate t E Certificate.A0≤nonradicalBase ((Certificate.L:ℝ)+t) E := by
  have hdom := Certificate.domain_angles hd
  have hang := domain_angles hdom
  have hl : 0≤l E := by linarith [(ranges hang.2.1).2.2.1]
  have hA := J_lower (u:=Certificate.a) (by simpa using hang.2.2.1)
  have hE := J_lower (u:=Certificate.e) (by simpa using hang.2.1)
  have hAl := mul_le_mul_of_nonneg_left hA hl
  have hdiag := mul_le_mul_of_nonneg_left diagonal_upper (show (0:ℝ)≤1+c by norm_num [c])
  simp only [Certificate.A0,map_add,map_sub,map_mul,evaluate_scalar,
    Certificate.evaluate_k,Certificate.evaluate_l] at ⊢
  push_cast
  simp only [Certificate.evaluate_a,Certificate.evaluate_e] at hAl hE
  dsimp [nonradicalBase,primaryCost,Certificate.c,c] at *
  linarith

theorem nonradical_lower (f : Kind) {t E : ℝ} (hd : Certificate.Domain t E) :
    evaluate t E (Certificate.A f)≤nonradical f ((Certificate.L:ℝ)+t) E := by
  have hdom := Certificate.domain_angles hd
  have hang := domain_angles hdom
  have ht := PositiveTD.Certificate.taylor_bounds hang.1
  have hb := PositiveTD.Certificate.taylor_bounds
    (show frameCap-((Certificate.L:ℝ)+t)∈Icc 0 frameCap from
      ⟨hang.2.2.2.1,hang.2.2.2.2.trans (by norm_num [span,frameCap])⟩)
  have hbase := base_lower hd
  cases f with
  | negative i =>
    have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
      ((coefficients hang.2.1 i.castSucc).1.trans_le (coefficients hang.2.1 i.castSucc).2.1).le
    simp only [Certificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,
      Certificate.evaluate_q,Certificate.evaluate_delta]
    dsimp [nonradical]
    linarith
  | equal =>
    simp only [Certificate.A,map_add,map_mul,evaluate_scalar,Certificate.evaluate_delta]
    dsimp [nonradical,speed,gamma,c,Certificate.gamma,Certificate.c]
    norm_num
    linarith
  | positive i =>
    have hp := mul_le_mul_of_nonneg_left
      (show aeval (frameCap-((Certificate.L:ℝ)+t)) PositiveTD.Certificate.C10+
          aeval (frameCap-((Certificate.L:ℝ)+t)) PositiveTD.Certificate.S11-1≤
        Real.cos (frameCap-((Certificate.L:ℝ)+t))+Real.sin (frameCap-((Certificate.L:ℝ)+t))-1 by
          linarith [hb.2.2.2.2.1,hb.2.1]) (coefficients hang.2.1 i.castSucc).1.le
    simp only [Certificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,
      Certificate.evaluate_p,Certificate.evaluate_b,evaluate_scalar]
    dsimp [nonradical,speed,gamma,c,Certificate.gamma,Certificate.c,Certificate.h,frameCap] at *
    norm_num
    linarith
  | diagonal =>
    have hp := mul_le_mul_of_nonneg_right (sub_le_sub_right diagonal_upper (1/2)) hang.2.2.2.1
    simp only [Certificate.A,map_add,map_sub,map_mul,evaluate_scalar,Certificate.evaluate_b]
    dsimp [nonradical,speed,gamma,c,aD,Certificate.gamma,Certificate.c,Certificate.h,frameCap] at *
    push_cast
    linarith

theorem norm_square_upper (f : Kind) (j : Fin 3) {t E : ℝ} (hd : Certificate.Domain t E) :
    (norm f j ((Certificate.L:ℝ)+t) E)^2≤evaluate t E (Certificate.P f j) := by
  have hdom := Certificate.domain_angles hd
  have hang := domain_angles hdom
  have hp := (coefficients hang.2.1 j.castSucc).1
  have hq := hp.trans_le (coefficients hang.2.1 j.castSucc).2.1
  have hb : frameCap-((Certificate.L:ℝ)+t)∈Icc 0 frameCap :=
    ⟨hang.2.2.2.1,hang.2.2.2.2.trans (by norm_num [span,frameCap])⟩
  have hzero : (pairNorm (p E j.castSucc) (q E j.castSucc) 0)^2=
      (p E j.castSucc)^2+(q E j.castSucc)^2 := NonnegativeTotals.Analytic.norm_zero_square _ _
  cases f with
  | negative i =>
    by_cases hi : i=j
    · have hh := NonnegativeTotals.Analytic.norm_negative_polynomial hp hq hang.1
      simpa [norm,normAngle,Certificate.P,Certificate.P0,hi] using hh
    · simp [norm,normAngle,Certificate.P,Certificate.P0,hi,hzero]
  | positive i =>
    by_cases hi : i=j
    · have hs := pairNorm_sq hp hq
        (show |frameCap-((Certificate.L:ℝ)+t)|≤frameCap by rw [abs_of_nonneg hb.1]; exact hb.2)
      have hsin := mul_le_mul_of_nonneg_left (PositiveTD.Certificate.taylor_bounds hb).2.2.1
        (show 0≤2*p E j.castSucc*q E j.castSucc by positivity)
      simp only [norm,normAngle,if_pos hi,Certificate.P,Certificate.P0,map_add,map_mul,map_pow,
        evaluate_scalar,evaluate_lift,Certificate.evaluate_p,Certificate.evaluate_q,Certificate.evaluate_b]
      dsimp [Certificate.h,frameCap,pairEnergy,pairProduct] at *
      norm_num
      nlinarith only [hs,hsin]
    · simp [norm,normAngle,Certificate.P,Certificate.P0,hi,hzero]
  | equal => simp [norm,normAngle,Certificate.P,Certificate.P0,hzero]
  | diagonal => simp [norm,normAngle,Certificate.P,Certificate.P0,hzero]

theorem polynomial_transfer (f : Kind) {t E : ℝ} (hd : Certificate.Domain t E)
    (hnum : 0<evaluate t E (Certificate.numerator f)) :
    0<value f ((Certificate.L:ℝ)+t) E := by
  have hm (j : Fin 3) : 0<evaluate t E (Certificate.mass f j) := by
    linarith [Certificate.mass_positive f j hd]
  have hn (j : Fin 3) : 0≤norm f j ((Certificate.L:ℝ)+t) E := Real.sqrt_nonneg _
  have hh := PositiveTD.Certificate.three_norm_transfer
    (hm 0) (hm 1) (hm 2) (hn 0) (hn 1) (hn 2)
    (norm_square_upper f 0 hd) (norm_square_upper f 1 hd) (norm_square_upper f 2 hd)
    (nonradical_lower f hd)
    (by simpa only [Certificate.numerator,map_sub,map_add,map_mul,map_pow,evaluate_scalar,
      Certificate.Rbar,PositiveTD.Certificate.Rbar,Rat.cast_div,Rat.cast_ofNat] using hnum)
  rwa [value_identity]

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Analytic
