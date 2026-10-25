module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDCertificates
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNorms

/-!
# Eight squares: from the negative-TD2 polynomials to the three norms

Both primary charges are bounded on their own intervals. The three pair coefficients are
unchanged. `S11` bounds a subtracted sine and `S9` an added sine (`norm_square_upper`,
`polynomial_transfer`).
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD.Analytic
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open TensorWholeIntervalPolynomial TwoVariablePolynomial
open NegativeTD.Certificate (Kind)

def value (f : Kind) (t e : ℝ) : ℝ := match f with
  | .negative i => negativeScalar i t e
  | .equal => equalScalar t e
  | .positive i => positiveScalar i t e
  | .diagonal => DScalar t e

def nonradicalBase (t e : ℝ) : ℝ :=
  2*k e+3*l e+(5/2)*c+5/2-(1+c)*Secondary.diagonal+primaryCost t e

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
        norm,normAngle,p,q,V,Fin.isValue,Fin.reduceFinMk,Fin.zero_eta,Fin.mk_one,Fin.reduceCastSucc,Matrix.cons_val,Fin.reduceEq,↓reduceIte] <;> ring
  | equal =>
    simp only [value,equalScalar,base_norms,nonradical,nonradicalBase,norm,normAngle,p,q,
      Fin.isValue,Fin.reduceCastSucc,Matrix.cons_val]
    ring
  | positive i =>
    fin_cases i <;>
      simp only [value,positiveScalar,base_norms,nonradical,nonradicalBase,
        norm,normAngle,p,q,U,PositiveAngularEnvelope.phi,Fin.isValue,Fin.reduceFinMk,Fin.zero_eta,Fin.mk_one,Fin.reduceCastSucc,
        Matrix.cons_val,Fin.reduceEq,↓reduceIte] <;> ring
  | diagonal =>
    simp only [value,DScalar,base_norms,nonradical,nonradicalBase,norm,normAngle,p,q,
      Fin.isValue,Fin.reduceCastSucc,Matrix.cons_val]
    ring

theorem diagonal_upper : Secondary.diagonal≤(Certificate.cbar:ℝ) := by
  have hs := diagonal_circle
  have hp := diagonal_bounds.1
  norm_num [qCap,Certificate.cbar] at hs ⊢
  nlinarith

theorem J_lower {u : Bivar} {t E : ℝ}
    (hu : evaluate t E u∈Icc 0 frameCap) :
    evaluate t E (Certificate.J u)≤TwoPositive.ASupport.charge (evaluate t E u) := by
  have hh := Charges.rectangle_E_charge hu
  simp only [Charges.polynomialJ,NonnegativeTotals.Certificate.abar] at hh
  simp only [Certificate.J,map_sub,map_add,map_mul,map_pow,map_one,evaluate_scalar,
    evaluate_lift,Certificate.abar]
  push_cast at hh ⊢
  linarith

theorem base_lower {t E : ℝ} (hd : Certificate.Domain t E) :
    evaluate t E Certificate.A0≤nonradicalBase ((Certificate.L:ℝ)+t) E := by
  have hdom := Certificate.domain_angles hd
  have hang := domain_angles hdom
  have hl : 0≤l E := by linarith [(ranges hang.2.1).2.2.1]
  have hA := J_lower (t:=t) (E:=E) (u:=Certificate.a)
    (by rw [Certificate.evaluate_a]; exact hang.2.2.1)
  have hE := J_lower (t:=t) (E:=E) (u:=Certificate.e)
    (by rw [Certificate.evaluate_e]; exact hang.2.1)
  rw [Certificate.evaluate_a] at hA
  rw [Certificate.evaluate_e] at hE
  have hAl := mul_le_mul_of_nonneg_left hA hl
  have hdiag := mul_le_mul_of_nonneg_left diagonal_upper (show (0:ℝ)≤1+c by norm_num [c])
  simp only [Certificate.A0,map_add,map_mul,evaluate_scalar,
    Certificate.evaluate_k,Certificate.evaluate_l]
  simp only [nonradicalBase,primaryCost]
  push_cast at hAl hdiag ⊢
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
  have hh : ((Certificate.h:ℚ):ℝ)=frameCap := by norm_num [Certificate.h,frameCap]
  have hs : ((Certificate.gamma*Certificate.c*Certificate.h:ℚ):ℝ)=speed*frameCap := by
    norm_num [Certificate.gamma,Certificate.c,Certificate.h,speed,gamma,c,frameCap]
  cases f with
  | negative i =>
    have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
      ((coefficients hang.2.1 i.castSucc).1.trans_le (coefficients hang.2.1 i.castSucc).2.1).le
    simp only [Certificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,
      Certificate.evaluate_q,Certificate.evaluate_delta]
    dsimp only [nonradical]
    linarith
  | equal =>
    have hs' : ((Certificate.gamma*Certificate.c:ℚ):ℝ)=speed := by
      norm_num [Certificate.gamma,Certificate.c,speed,gamma,c]
    simp only [Certificate.A,map_add,map_mul,evaluate_scalar,Certificate.evaluate_delta]
    rw [hs']
    dsimp only [nonradical]
    linarith
  | positive i =>
    have hp := mul_le_mul_of_nonneg_left
      (show aeval (frameCap-((Certificate.L:ℝ)+t)) PositiveTD.Certificate.C10+
          aeval (frameCap-((Certificate.L:ℝ)+t)) PositiveTD.Certificate.S11-1≤
        Real.cos (frameCap-((Certificate.L:ℝ)+t))+Real.sin (frameCap-((Certificate.L:ℝ)+t))-1 by
          linarith [hb.2.2.2.2.1,hb.2.1]) (coefficients hang.2.1 i.castSucc).1.le
    simp only [Certificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,
      Certificate.evaluate_p,Certificate.evaluate_b,evaluate_scalar]
    rw [hh,hs]
    dsimp only [nonradical]
    linarith
  | diagonal =>
    have hp := mul_le_mul_of_nonneg_right (sub_le_sub_right diagonal_upper (1/2)) hang.2.2.2.1
    have hc2 : ((Certificate.cbar-1/2:ℚ):ℝ)=(Certificate.cbar:ℝ)-1/2 := by push_cast; ring
    simp only [Certificate.A,map_add,map_sub,map_mul,evaluate_scalar,Certificate.evaluate_b]
    rw [hh,hs,hc2]
    dsimp only [nonradical,aD]
    generalize (Certificate.L:ℝ)+t=T at hp hbase ⊢
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
  have hP0 : evaluate t E (Certificate.P0 j)=(p E j.castSucc)^2+(q E j.castSucc)^2 := by
    simp only [Certificate.P0,map_add,map_pow,Certificate.evaluate_p,Certificate.evaluate_q]
  have hh : ((Certificate.h:ℚ):ℝ)=frameCap := by norm_num [Certificate.h,frameCap]
  cases f with
  | negative i =>
    by_cases hi : i=j
    · have hh := NonnegativeTotals.Analytic.norm_negative_polynomial hp hq hang.1
      simpa [norm,normAngle,Certificate.P,Certificate.P0,hi] using hh
    · simp only [norm,normAngle,Certificate.P,hi,↓reduceIte,sub_zero,hP0,hzero,le_refl]
  | positive i =>
    by_cases hi : i=j
    · subst hi
      have hs := pairNorm_sq hp hq
        (show |frameCap-((Certificate.L:ℝ)+t)|≤frameCap by rw [abs_of_nonneg hb.1]; exact hb.2)
      have hsin := mul_le_mul_of_nonneg_left (PositiveTD.Certificate.taylor_bounds hb).2.2.1
        (show 0≤2*p E i.castSucc*q E i.castSucc by positivity)
      simp only [norm,normAngle,Certificate.P,↓reduceIte,map_add,map_mul,
        evaluate_scalar,evaluate_lift,Certificate.evaluate_p,Certificate.evaluate_q,
        Certificate.evaluate_b,hP0,hh]
      rw [hs]
      simp only [pairEnergy,pairProduct,Rat.cast_ofNat]
      linarith
    · simp only [norm,normAngle,Certificate.P,hi,↓reduceIte,add_zero,hP0,hzero,le_refl]
  | equal => simp only [norm,normAngle,Certificate.P,hP0,hzero,le_refl]
  | diagonal => simp only [norm,normAngle,Certificate.P,hP0,hzero,le_refl]

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
    (by
      have hR : ((Certificate.Rbar:ℚ):ℝ)=((PositiveTD.Certificate.Rbar:ℚ):ℝ) := by
        norm_num [Certificate.Rbar,PositiveTD.Certificate.Rbar]
      simp only [Certificate.numerator,map_sub,map_add,map_mul,map_pow,evaluate_scalar,
        Rat.cast_ofNat] at hnum
      rw [hR] at hnum
      exact hnum)
  rwa [value_identity]

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD.Analytic
