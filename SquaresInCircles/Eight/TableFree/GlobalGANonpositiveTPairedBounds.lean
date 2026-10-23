module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTPairedCertificates
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDScalars

/-!
# Actual paired-T scalar functions and radical transfer

Uncompiled Sections 7--9 of the nonpositive T-total note.  The paired
gain is c*kappa*(phi(s)-1), with its own short cap M.  The three
full-circle norms and both actual nonnegative A/E support charges
are retained when the exact polynomial numerators are applied.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open TensorWholeIntervalPolynomial TwoVariablePolynomial

abbrev L : ℝ := 1/6
abbrev M : ℝ := 41/100
abbrev kappa : ℝ := 847/800
abbrev c := NonnegativeTotals.NegativeTD.c
abbrev k := NonnegativeTotals.NegativeTD.k
abbrev l := NonnegativeTotals.NegativeTD.l
abbrev p := NonnegativeTotals.NegativeTD.p
abbrev q := NonnegativeTotals.NegativeTD.q
abbrev base := NonnegativeTotals.NegativeTD.base
abbrev primaryCost := NonnegativeTotals.NegativeTD.primaryCost
abbrev aD := NonnegativeTotals.NegativeTD.aD
abbrev coefficients := NonnegativeTotals.NegativeTD.coefficients
abbrev ranges := NonnegativeTotals.NegativeTD.ranges
def gain (s : ℝ) : ℝ := c*kappa*(phi s-1)
def negativeScalar (i : Fin 3) (t E : ℝ) : ℝ :=
  base E+primaryCost t E+gain M+V R (p E i.castSucc) (q E i.castSucc) (t-M)
def equalScalar (t E : ℝ) : ℝ := base E+primaryCost t E+gain t
def positiveScalar (i : Fin 3) (t E : ℝ) : ℝ :=
  base E+primaryCost t E+gain M+U R (p E i.castSucc) (q E i.castSucc) (M-t)
def DScalar (t E : ℝ) : ℝ := base E+primaryCost t E+gain M-aD*(M-t)
def Domain (f : Certificate.Kind) (t E : ℝ) : Prop :=
  t∈Icc (Certificate.origin f:ℝ) ((Certificate.origin f:ℝ)+(Certificate.length f:ℝ)) ∧ E∈Icc 0 t

namespace Analytic
open Certificate (Kind)

def value (f : Kind) (t E : ℝ) : ℝ := match f with
  | .negative i => negativeScalar i t E
  | .equal => equalScalar t E
  | .positive i => positiveScalar i t E
  | .diagonal => DScalar t E
abbrev nonradicalBase := NonnegativeTotals.NegativeTD.Analytic.nonradicalBase
def nonradical (f : Kind) (t E : ℝ) : ℝ := match f with
  | .negative i => nonradicalBase t E+gain M+q E i.castSucc*(Real.cos (t-M)-1)
  | .equal => nonradicalBase t E+gain t
  | .positive i => nonradicalBase t E+gain M+
      p E i.castSucc*(Real.cos (M-t)+Real.sin (M-t)-1)
  | .diagonal => nonradicalBase t E+gain M-aD*(M-t)
def angle (f : Kind) (t : ℝ) : ℝ := match f with
  | .negative _ => t-M
  | .positive _ => M-t
  | .diagonal => M-t
  | .equal => 0
def normAngle (f : Kind) (j : Fin 3) (t : ℝ) : ℝ := match f with
  | .negative i => if i=j then -(t-M) else 0
  | .positive i => if i=j then M-t else 0
  | _ => 0
def norm (f : Kind) (j : Fin 3) (t E : ℝ) : ℝ :=
  pairNorm (p E j.castSucc) (q E j.castSucc) (normAngle f j t)

theorem domain_of_native {f : Kind} {x E : ℝ} (hd : Certificate.Domain f x E) :
    Domain f ((Certificate.origin f:ℝ)+x) E := by
  exact ⟨⟨by linarith [hd.1.1],by linarith [hd.1.2]⟩,hd.2⟩
theorem native_of_domain {f : Kind} {t E : ℝ} (hd : Domain f t E) :
    Certificate.Domain f (t-(Certificate.origin f:ℝ)) E := by
  refine ⟨⟨by linarith [hd.1.1],by linarith [hd.1.2]⟩,?_⟩
  simpa only [add_sub_cancel] using hd.2
theorem domain_angles {f : Kind} {t E : ℝ} (hd : Domain f t E) :
    NonnegativeTotals.NegativeTD.Domain t E ∧ angle f t∈Icc 0 frameCap := by
  refine ⟨⟨?_,hd.2⟩,?_⟩
  · cases f <;> dsimp [Domain,Certificate.origin,Certificate.length,Certificate.L,
      Certificate.M,Certificate.h,NonnegativeTotals.NegativeTD.L,frameCap] at * <;>
      constructor <;> linarith [hd.1.1,hd.1.2]
  · cases f <;> dsimp [Domain,angle,M,Certificate.origin,Certificate.length,
      Certificate.L,Certificate.M,Certificate.h,frameCap] at * <;>
      constructor <;> linarith [hd.1.1,hd.1.2]

theorem value_identity (f : Kind) (t E : ℝ) :
    value f t E=nonradical f t E-R*(norm f 0 t E+norm f 1 t E+norm f 2 t E) := by
  cases f with
  | negative i =>
    fin_cases i <;> simp only [value,negativeScalar,NonnegativeTotals.NegativeTD.base_norms,
      nonradical,nonradicalBase,NonnegativeTotals.NegativeTD.Analytic.nonradicalBase,
      norm,normAngle,p,q,NonnegativeTotals.NegativeTD.p,NonnegativeTotals.NegativeTD.q,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceFinMk,ite_true,ite_false,V] <;> ring
  | positive i =>
    fin_cases i <;> simp only [value,positiveScalar,NonnegativeTotals.NegativeTD.base_norms,
      nonradical,nonradicalBase,NonnegativeTotals.NegativeTD.Analytic.nonradicalBase,
      norm,normAngle,p,q,NonnegativeTotals.NegativeTD.p,NonnegativeTotals.NegativeTD.q,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceFinMk,ite_true,ite_false,U,phi] <;> ring
  | equal =>
    simp only [value,equalScalar,NonnegativeTotals.NegativeTD.base_norms,
      nonradical,nonradicalBase,NonnegativeTotals.NegativeTD.Analytic.nonradicalBase,norm,normAngle,
      p,q,NonnegativeTotals.NegativeTD.p,NonnegativeTotals.NegativeTD.q,
      Matrix.cons_val_zero,Matrix.cons_val_succ]
    ring
  | diagonal =>
    simp only [value,DScalar,NonnegativeTotals.NegativeTD.base_norms,
      nonradical,nonradicalBase,NonnegativeTotals.NegativeTD.Analytic.nonradicalBase,norm,normAngle,
      p,q,NonnegativeTotals.NegativeTD.p,NonnegativeTotals.NegativeTD.q,
      Matrix.cons_val_zero,Matrix.cons_val_succ]
    ring

theorem base_lower (f : Kind) {x E : ℝ} (hd : Certificate.Domain f x E) :
    evaluate x E (Certificate.A0 f)≤nonradicalBase ((Certificate.origin f:ℝ)+x) E := by
  have hang := NonnegativeTotals.NegativeTD.domain_angles (domain_angles (domain_of_native hd)).1
  have hl : 0≤l E := by linarith [(ranges hang.2.1).2.2.1]
  have hA := NonnegativeTotals.NegativeTD.Analytic.J_lower
    (u:=Certificate.delta f-Certificate.e) (by simpa using hang.2.2.1)
  have hE := NonnegativeTotals.NegativeTD.Analytic.J_lower
    (u:=Certificate.e) (by simpa using hang.2.1)
  have hAl := mul_le_mul_of_nonneg_left hA hl
  have hdiag := mul_le_mul_of_nonneg_left NonnegativeTotals.NegativeTD.Analytic.diagonal_upper
    (show (0:ℝ)≤1+c by norm_num [c,NonnegativeTotals.NegativeTD.c])
  simp only [Certificate.A0,map_add,map_sub,map_mul,evaluate_scalar,
    Certificate.evaluate_k,Certificate.evaluate_l] at ⊢
  push_cast
  simp only [map_sub,Certificate.evaluate_delta,Certificate.evaluate_e] at hAl hE
  dsimp [nonradicalBase,NonnegativeTotals.NegativeTD.Analytic.nonradicalBase,
    primaryCost,NonnegativeTotals.NegativeTD.primaryCost,Certificate.c,c,NonnegativeTotals.NegativeTD.c] at *
  linarith

theorem gain_lower {u : Bivar} {x E : ℝ} (hu : evaluate x E u∈Icc 0 frameCap) :
    evaluate x E (Certificate.gain u)≤gain (evaluate x E u) := by
  have hb := PositiveTD.Certificate.taylor_bounds hu
  have hh := mul_le_mul_of_nonneg_left
    (show aeval (evaluate x E u) PositiveTD.Certificate.C10+
        aeval (evaluate x E u) PositiveTD.Certificate.S11-1≤
      Real.cos (evaluate x E u)+Real.sin (evaluate x E u)-1 by
        linarith [hb.2.2.2.2.1,hb.2.1])
    (show 0≤c*kappa by norm_num [c,NonnegativeTotals.NegativeTD.c,kappa])
  simpa [Certificate.gain,gain,phi,Certificate.c,Certificate.kappa,c,
    NonnegativeTotals.NegativeTD.c,kappa] using hh

theorem nonradical_lower (f : Kind) {x E : ℝ} (hd : Certificate.Domain f x E) :
    evaluate x E (Certificate.A f)≤nonradical f ((Certificate.origin f:ℝ)+x) E := by
  have hdom := domain_angles (domain_of_native hd)
  have hang := NonnegativeTotals.NegativeTD.domain_angles hdom.1
  have hb := PositiveTD.Certificate.taylor_bounds hdom.2
  have hbase := base_lower f hd
  have hM := gain_lower (x:=x) (E:=E) (u:=scalar Certificate.M)
    (by norm_num [Certificate.M,frameCap])
  have ht := gain_lower (u:=Certificate.delta f) (by simpa using hang.1)
  cases f with
  | equal => simpa [Certificate.A,nonradical] using add_le_add hbase ht
  | negative i =>
    have hq := (coefficients hang.2.1 i.castSucc).1.trans_le (coefficients hang.2.1 i.castSucc).2.1
    have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right hb.2.2.2.2.1 1) hq.le
    simp only [Certificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,
      evaluate_scalar,Certificate.evaluate_q,Certificate.evaluate_delta]
    dsimp [nonradical,angle,Certificate.M,M] at *
    push_cast at *
    linarith
  | positive i =>
    have hp := mul_le_mul_of_nonneg_left
      (show aeval (angle (.positive i) ((Certificate.origin (.positive i):ℝ)+x)) PositiveTD.Certificate.C10+
          aeval (angle (.positive i) ((Certificate.origin (.positive i):ℝ)+x)) PositiveTD.Certificate.S11-1≤
        Real.cos (angle (.positive i) ((Certificate.origin (.positive i):ℝ)+x))+
          Real.sin (angle (.positive i) ((Certificate.origin (.positive i):ℝ)+x))-1 by
            linarith [hb.2.2.2.2.1,hb.2.1]) (coefficients hang.2.1 i.castSucc).1.le
    simp only [Certificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,
      evaluate_scalar,Certificate.evaluate_p,Certificate.evaluate_delta]
    dsimp [nonradical,angle,Certificate.M,M] at *
    push_cast at *
    linarith
  | diagonal =>
    have hp := mul_le_mul_of_nonneg_right
      (sub_le_sub_right NonnegativeTotals.NegativeTD.Analytic.diagonal_upper (1/2)) hdom.2.1
    simp only [Certificate.A,map_add,map_sub,map_mul,evaluate_scalar,Certificate.evaluate_delta]
    dsimp [nonradical,angle,aD,NonnegativeTotals.NegativeTD.aD,Certificate.M,M] at *
    push_cast at *
    linarith

theorem norm_square_upper (f : Kind) (j : Fin 3) {x E : ℝ} (hd : Certificate.Domain f x E) :
    (norm f j ((Certificate.origin f:ℝ)+x) E)^2≤evaluate x E (Certificate.P f j) := by
  have hdom := domain_angles (domain_of_native hd)
  have hang := NonnegativeTotals.NegativeTD.domain_angles hdom.1
  have hp := (coefficients hang.2.1 j.castSucc).1
  have hq := hp.trans_le (coefficients hang.2.1 j.castSucc).2.1
  have hzero : (pairNorm (p E j.castSucc) (q E j.castSucc) 0)^2=
      (p E j.castSucc)^2+(q E j.castSucc)^2 := NonnegativeTotals.Analytic.norm_zero_square _ _
  cases f with
  | negative i =>
    by_cases hi : i=j
    · have hh := NonnegativeTotals.Analytic.norm_negative_polynomial hp hq hdom.2
      simpa [norm,normAngle,Certificate.P,Certificate.P0,Certificate.M,M,angle,hi] using hh
    · simp [norm,normAngle,Certificate.P,Certificate.P0,hi,hzero]
  | positive i =>
    by_cases hi : i=j
    · have hs := pairNorm_sq hp hq
        (show |angle (.positive i) ((Certificate.origin (.positive i):ℝ)+x)|≤frameCap by
          rw [abs_of_nonneg hdom.2.1]; exact hdom.2.2)
      have hsin := mul_le_mul_of_nonneg_left (PositiveTD.Certificate.taylor_bounds hdom.2).2.2.1
        (show 0≤2*p E j.castSucc*q E j.castSucc by positivity)
      simp only [norm,normAngle,if_pos hi,Certificate.P,Certificate.P0,map_add,map_mul,map_pow,
        map_sub,evaluate_scalar,evaluate_lift,Certificate.evaluate_p,Certificate.evaluate_q,Certificate.evaluate_delta]
      dsimp [Certificate.M,M,angle,pairEnergy,pairProduct] at *
      push_cast
      nlinarith only [hs,hsin]
    · simp [norm,normAngle,Certificate.P,Certificate.P0,hi,hzero]
  | equal => simp [norm,normAngle,Certificate.P,Certificate.P0,hzero]
  | diagonal => simp [norm,normAngle,Certificate.P,Certificate.P0,hzero]

theorem polynomial_transfer (f : Kind) {x E : ℝ} (hd : Certificate.Domain f x E)
    (hnum : 0<evaluate x E (Certificate.numerator f)) :
    0<value f ((Certificate.origin f:ℝ)+x) E := by
  have hm (j : Fin 3) : 0<evaluate x E (Certificate.mass f j) := by
    linarith [Certificate.mass_positive f j hd]
  have hn (j : Fin 3) : 0≤norm f j ((Certificate.origin f:ℝ)+x) E := Real.sqrt_nonneg _
  have hh := PositiveTD.Certificate.three_norm_transfer
    (hm 0) (hm 1) (hm 2) (hn 0) (hn 1) (hn 2)
    (norm_square_upper f 0 hd) (norm_square_upper f 1 hd) (norm_square_upper f 2 hd)
    (nonradical_lower f hd)
    (by simpa only [Certificate.numerator,map_sub,map_add,map_mul,map_pow,evaluate_scalar,
      Certificate.Rbar,NonnegativeTotals.NegativeTD.Certificate.Rbar,PositiveTD.Certificate.Rbar,
      Rat.cast_div,Rat.cast_ofNat] using hnum)
  rwa [value_identity]

end Analytic
end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired
