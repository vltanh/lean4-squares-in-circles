module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsPolynomial
public import SquaresInCircles.Eight.TableFree.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates
public import SquaresInCircles.Eight.TableFree.BivariateCertificates

/-!
# Whole-domain coefficient bounds for the two A/E weight families

Uncompiled transcription of Section 4. The triangle's affine secondary
coordinate is reduced to its two original edges. The two q-star bounds
retain the specified center 1/5, radius 1/3, and completed-square tail.
The rectangle's largest coefficient uses the single polynomial (31).
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Coefficients
open TensorWholeIntervalPolynomial TwoVariablePolynomial

abbrev d : ℚ := 8/15

def edge (far : Bool) (p : Bivar) : ℚ[X] :=
  restrict p X (if far then C d-X else 0)
def difference : Fin 4→Bivar :=
  ![Certificate.l .triangle-Certificate.k .triangle,
    Certificate.c .triangle-Certificate.k .triangle,
    Certificate.c .triangle-scalar (9/10)*Certificate.l .triangle,
    scalar (11/10)*Certificate.l .triangle-Certificate.c .triangle]
def differenceReserve : Fin 4→ℚ := ![3/200,7/1000,2/25,39/500]

def lowerM : Bivar := Certificate.c .triangle*
  (lift (Certificate.theta .triangle) PositiveTD.Certificate.C10+
    scalar (293/1000)*lift (Certificate.theta .triangle) PositiveTD.Certificate.S11)
def lowerGap (far : Bool) : ℚ[X] := edge far (lowerM-Certificate.k .triangle)
def upperGap (far : Bool) : ℚ[X] :=
  edge far (Certificate.qStar .triangle-Certificate.M .triangle .atT)
def centeredGap (far : Bool) : ℚ[X] := (upperGap far).comp (C (1/5)+X)
def gapCoefficient (far : Bool) (j : ℕ) : ℚ := (centeredGap far).coeff j
def gapTail (far : Bool) : ℚ :=
  ∑j : Fin 13,|gapCoefficient far (j.val+3)| *(1/3)^(j.val+1)
def gapCurvature (far : Bool) : ℚ := gapCoefficient far 2-gapTail far
def gapReserve : Bool→ℚ | false => 239/50000 | true => 1/625

def rectangleMaximum : ℚ[X] :=
  (C (11913/10000)-C (1/4)*X)*
    (PositiveTD.Certificate.C12+C (293/1000)*PositiveTD.Certificate.S9)

/-! ### Kernel certificates

The univariate polynomials below are restrictions of explicit bivariate
polynomials; they are represented by scaled integer coefficient lists
(`WholeIntervalPolynomial.Certificate`), mirroring their definitions. -/

private theorem r79_restrict_lift (u : Bivar) (q : ℚ[X]) (f g : ℚ[X]) :
    TwoVariablePolynomial.restrict (lift u q) f g=q.comp (TwoVariablePolynomial.restrict u f g) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add,TwoVariablePolynomial.restrict,eval₂_add,add_comp] at hp hq ⊢
      rw [hp,hq]
  | monomial n a =>
      simp [TwoVariablePolynomial.restrict,lift,← C_mul_X_pow_eq_monomial,eval₂_pow]

private theorem r79_restrict_add (p q : Bivar) (f g : ℚ[X]) :
    TwoVariablePolynomial.restrict (p+q) f g=
      TwoVariablePolynomial.restrict p f g+TwoVariablePolynomial.restrict q f g :=
  eval₂_add _ _

private theorem r79_restrict_sub (p q : Bivar) (f g : ℚ[X]) :
    TwoVariablePolynomial.restrict (p-q) f g=
      TwoVariablePolynomial.restrict p f g-TwoVariablePolynomial.restrict q f g :=
  eval₂_sub _

private theorem r79_restrict_mul (p q : Bivar) (f g : ℚ[X]) :
    TwoVariablePolynomial.restrict (p*q) f g=
      TwoVariablePolynomial.restrict p f g*TwoVariablePolynomial.restrict q f g :=
  eval₂_mul _ _

private theorem r79_restrict_X (f g : ℚ[X]) : TwoVariablePolynomial.restrict X f g=f :=
  eval₂_X _ _

private theorem r79_restrict_scalar (r : ℚ) (f g : ℚ[X]) :
    TwoVariablePolynomial.restrict (scalar r) f g=C r := by
  simp [TwoVariablePolynomial.restrict,scalar]

open WholeIntervalPolynomial.Certificate in
private def r79_C10of (v : Scaled) : Scaled :=
  (((((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (v.pow 2))).add
    ((Scaled.const (1/24)).mul (v.pow 4))).sub
    ((Scaled.const (1/720)).mul (v.pow 6))).add
    ((Scaled.const (1/40320)).mul (v.pow 8))).sub
    ((Scaled.const (1/3628800)).mul (v.pow 10))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_C10of {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r79_C10of v).Rep (PositiveTD.Certificate.C10.comp q) := by
  have e : PositiveTD.Certificate.C10.comp q=1-C (1/2)*q^2+C (1/24)*q^4-C (1/720)*q^6+
      C (1/40320)*q^8-C (1/3628800)*q^10 := by
    simp only [PositiveTD.Certificate.C10,PositiveTD.Certificate.C4,sub_comp,add_comp,
      mul_comp,C_comp,X_comp,pow_comp,one_comp]
  rw [e]
  exact ((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (hv.pow 2))).add
    ((Scaled.rep_const _).mul (hv.pow 4))).sub
    ((Scaled.rep_const _).mul (hv.pow 6))).add
    ((Scaled.rep_const _).mul (hv.pow 8))).sub
    ((Scaled.rep_const _).mul (hv.pow 10))

open WholeIntervalPolynomial.Certificate in
private def r79_C12of (v : Scaled) : Scaled :=
  (r79_C10of v).add ((Scaled.const (1/479001600)).mul (v.pow 12))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_C12of {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r79_C12of v).Rep (PositiveTD.Certificate.C12.comp q) := by
  have e : PositiveTD.Certificate.C12.comp q=PositiveTD.Certificate.C10.comp q+
      C (1/479001600)*q^12 := by
    simp only [PositiveTD.Certificate.C12,add_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact (r79_rep_C10of hv).add ((Scaled.rep_const _).mul (hv.pow 12))

open WholeIntervalPolynomial.Certificate in
private def r79_S9of (v : Scaled) : Scaled :=
  (((v.sub ((Scaled.const (1/6)).mul (v.pow 3))).add
    ((Scaled.const (1/120)).mul (v.pow 5))).sub
    ((Scaled.const (1/5040)).mul (v.pow 7))).add
    ((Scaled.const (1/362880)).mul (v.pow 9))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_S9of {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r79_S9of v).Rep (PositiveTD.Certificate.S9.comp q) := by
  have e : PositiveTD.Certificate.S9.comp q=q-C (1/6)*q^3+C (1/120)*q^5-C (1/5040)*q^7+
      C (1/362880)*q^9 := by
    simp only [PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,sub_comp,add_comp,
      mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact (((hv.sub ((Scaled.rep_const _).mul (hv.pow 3))).add
    ((Scaled.rep_const _).mul (hv.pow 5))).sub
    ((Scaled.rep_const _).mul (hv.pow 7))).add
    ((Scaled.rep_const _).mul (hv.pow 9))

open WholeIntervalPolynomial.Certificate in
private def r79_S11of (v : Scaled) : Scaled :=
  (r79_S9of v).sub ((Scaled.const (1/39916800)).mul (v.pow 11))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_S11of {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r79_S11of v).Rep (PositiveTD.Certificate.S11.comp q) := by
  have e : PositiveTD.Certificate.S11.comp q=PositiveTD.Certificate.S9.comp q-
      C (1/39916800)*q^11 := by
    simp only [PositiveTD.Certificate.S11,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact (r79_rep_S9of hv).sub ((Scaled.rep_const _).mul (hv.pow 11))

open WholeIntervalPolynomial.Certificate in
/-- The coefficient list of the derivative. -/
private def r79_derivL : List ℤ → List ℤ
  | [] => []
  | [_] => []
  | _ :: b :: l => WholeIntervalPolynomial.Certificate.add (b :: l) (0 :: r79_derivL (b :: l))

open WholeIntervalPolynomial.Certificate in
private theorem r79_toPoly_derivL : ∀ l : List ℤ,toPoly (r79_derivL l)=derivative (toPoly l)
  | [] => by simp [r79_derivL,toPoly]
  | [a] => by simp [r79_derivL,toPoly]
  | a :: b :: l => by
    rw [r79_derivL,toPoly_add]
    have ih := r79_toPoly_derivL (b :: l)
    simp only [toPoly] at ih ⊢
    rw [ih]
    simp only [Int.cast_zero,map_zero,zero_add,derivative_add,derivative_C,derivative_mul,
      derivative_X,one_mul]

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_derivative {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (⟨r79_derivL c.l,c.s⟩ : Scaled).Rep (derivative p) := by
  unfold Scaled.Rep at *
  rw [r79_toPoly_derivL,hc,derivative_C_mul]

/-- Horner evaluation of an integer list at `num/den`, scaled by `den^(length-1)`. -/
private def r79_hornerZ (num : ℤ) (den : ℕ) : List ℤ → ℤ × ℕ
  | [] => (0,0)
  | [a] => (a,0)
  | a :: l => let r := r79_hornerZ num den l; (a*(den:ℤ)^(r.2+1)+num*r.1,r.2+1)

open WholeIntervalPolynomial.Certificate in
private theorem r79_eval_toPoly (num : ℤ) (den : ℕ) (hden : den≠0) : ∀ l : List ℤ,
    (toPoly l).eval ((num:ℚ)/den)=((r79_hornerZ num den l).1:ℚ)/(den:ℚ)^(r79_hornerZ num den l).2
  | [] => by simp [toPoly,r79_hornerZ]
  | [a] => by simp [toPoly,r79_hornerZ]
  | a :: b :: l => by
    have ih := r79_eval_toPoly num den hden (b :: l)
    have hd : (den:ℚ)≠0 := by exact_mod_cast hden
    rw [toPoly,eval_add,eval_mul,eval_C,eval_X,ih]
    simp only [r79_hornerZ]
    push_cast
    field_simp
    ring

open WholeIntervalPolynomial.Certificate in
private theorem r79_eval_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (num : ℤ) (den : ℕ) (hden : den≠0) :
    p.eval ((num:ℚ)/den)=((r79_hornerZ num den c.l).1:ℚ)/
      ((den^(r79_hornerZ num den c.l).2*c.s:ℕ):ℚ) := by
  have hs' : (c.s:ℚ)≠0 := by exact_mod_cast hs
  have he := congrArg (eval ((num:ℚ)/den)) hc
  rw [r79_eval_toPoly num den hden,eval_mul,eval_C] at he
  push_cast
  rw [div_mul_eq_div_div,he]
  field_simp

private theorem r79_lt_div {a A : ℤ} {b B : ℕ} (hb : 0<b) (hB : 0<B) (h : a*B<A*b) :
    (a:ℚ)/b<(A:ℚ)/B := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hB)]
  exact_mod_cast h

open WholeIntervalPolynomial.Certificate in
private def r79_lS : Scaled :=
  (((Scaled.ofNat 1).add ((Scaled.const (7/400)).mul Scaled.var)).sub
    ((Scaled.const (2733/2500)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (639/500)).mul (Scaled.var.pow 3))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_l : r79_lS.Rep (edge false (Certificate.l .triangle)) := by
  have e : edge false (Certificate.l .triangle)=1+C (7/400)*X-C (2733/2500)*X^2+
      C (639/500)*X^3 := by
    simp [edge,TwoVariablePolynomial.restrict,Certificate.l,scalar]
  rw [e]
  exact ((Scaled.rep_one.add ((Scaled.rep_const _).mul Scaled.rep_var)).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))

theorem l_lower_certificate :
    WholeIntervalPolynomial.centered 0 d (edge false (Certificate.l .triangle))=
      WholeIntervalPolynomial.expansion 3
        (WholeIntervalPolynomial.centered 0 d (edge false (Certificate.l .triangle))) ∧
    (22/25:ℚ)<WholeIntervalPolynomial.lowerOn 3 0 d (edge false (Certificate.l .triangle)) := by
  have hc := r79_rep_l.centered (a:=0) (b:=d) 4 15 1 1 (by norm_num) (by norm_num [d])
    (by norm_num [d])
  refine ⟨hc.eq_expansion (by decide +kernel) (by decide +kernel),?_⟩
  rw [WholeIntervalPolynomial.Certificate.lowerOn_eq_of_rep hc (by decide +kernel)
    (by decide +kernel)]
  decide +kernel

open WholeIntervalPolynomial.Certificate in
private def r79_cS (g : Scaled) : Scaled :=
  (((((Scaled.const (10163/10000)).sub ((Scaled.const (209/10000)).mul Scaled.var)).sub
    ((Scaled.const (5743/5000)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (14069/10000)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/4)).mul g))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_c {g : Scaled} {q : ℚ[X]} (hg : g.Rep q) :
    (r79_cS g).Rep (TwoVariablePolynomial.restrict (Certificate.c .triangle) X q) := by
  have e : TwoVariablePolynomial.restrict (Certificate.c .triangle) X q=
      C (10163/10000)-C (209/10000)*X-C (5743/5000)*X^2+C (14069/10000)*X^3+C (1/4)*q := by
    simp [TwoVariablePolynomial.restrict,Certificate.c,scalar]
  rw [e]
  exact ((((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul hg)

open WholeIntervalPolynomial.Certificate in
private def r79_kS (g : Scaled) : Scaled :=
  (((((Scaled.const (1673/2500)).add ((Scaled.const (2609/5000)).mul Scaled.var)).sub
    ((Scaled.const (1489/2500)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (527/1250)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (7/25)).mul g))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_k {g : Scaled} {q : ℚ[X]} (hg : g.Rep q) :
    (r79_kS g).Rep (TwoVariablePolynomial.restrict (Certificate.k .triangle) X q) := by
  have e : TwoVariablePolynomial.restrict (Certificate.k .triangle) X q=
      C (1673/2500)+C (2609/5000)*X-C (1489/2500)*X^2+C (527/1250)*X^3+C (7/25)*q := by
    simp [TwoVariablePolynomial.restrict,Certificate.k,scalar]
  rw [e]
  exact ((((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul hg)

open WholeIntervalPolynomial.Certificate in
private def r79_thetaS : Scaled := (Scaled.const (1/6)).add Scaled.var

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_theta (q : ℚ[X]) :
    r79_thetaS.Rep (TwoVariablePolynomial.restrict (Certificate.theta .triangle) X q) := by
  have e : TwoVariablePolynomial.restrict (Certificate.theta .triangle) X q=C (1/6)+X := by
    simp [TwoVariablePolynomial.restrict,Certificate.theta,scalar]
  rw [e]
  exact (Scaled.rep_const _).add Scaled.rep_var

open WholeIntervalPolynomial.Certificate in
private def r79_gS : Bool → Scaled
  | false => ⟨[],1⟩
  | true => (Scaled.const d).sub Scaled.var

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_g (far : Bool) :
    (r79_gS far).Rep (if far then C d-X else 0) := by
  cases far
  · exact Scaled.rep_zero
  · exact (Scaled.rep_const _).sub Scaled.rep_var

open WholeIntervalPolynomial.Certificate in
private def r79_lowerGapS (far : Bool) : Scaled :=
  ((r79_cS (r79_gS far)).mul ((r79_C10of r79_thetaS).add
    ((Scaled.const (293/1000)).mul (r79_S11of r79_thetaS)))).sub (r79_kS (r79_gS far))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_lowerGap (far : Bool) : (r79_lowerGapS far).Rep (lowerGap far) := by
  have e : lowerGap far=TwoVariablePolynomial.restrict (Certificate.c .triangle) X
        (if far then C d-X else 0)*
      (PositiveTD.Certificate.C10.comp (TwoVariablePolynomial.restrict
          (Certificate.theta .triangle) X (if far then C d-X else 0))+
        C (293/1000)*PositiveTD.Certificate.S11.comp (TwoVariablePolynomial.restrict
          (Certificate.theta .triangle) X (if far then C d-X else 0)))-
      TwoVariablePolynomial.restrict (Certificate.k .triangle) X (if far then C d-X else 0) := by
    simp only [lowerGap,edge,lowerM,r79_restrict_sub,r79_restrict_mul,r79_restrict_add,
      r79_restrict_lift,r79_restrict_scalar]
  rw [e]
  exact ((r79_rep_c (r79_rep_g far)).mul ((r79_rep_C10of (r79_rep_theta _)).add
    ((Scaled.rep_const _).mul (r79_rep_S11of (r79_rep_theta _))))).sub (r79_rep_k (r79_rep_g far))

theorem c_lower_certificate :
    WholeIntervalPolynomial.centered 0 d (edge false (Certificate.c .triangle))=
      WholeIntervalPolynomial.expansion 3
        (WholeIntervalPolynomial.centered 0 d (edge false (Certificate.c .triangle))) ∧
    (439/500:ℚ)<WholeIntervalPolynomial.lowerOn 3 0 d (edge false (Certificate.c .triangle)) := by
  have hc := (r79_rep_c (r79_rep_g false)).centered (a:=0) (b:=d) 4 15 1 1 (by norm_num)
    (by norm_num [d]) (by norm_num [d])
  have he : edge false (Certificate.c .triangle)=
      TwoVariablePolynomial.restrict (Certificate.c .triangle) X (if false then C d-X else 0) := by
    simp [edge]
  rw [he]
  refine ⟨hc.eq_expansion (by decide +kernel) (by decide +kernel),?_⟩
  rw [WholeIntervalPolynomial.Certificate.lowerOn_eq_of_rep hc (by decide +kernel)
    (by decide +kernel)]
  decide +kernel

/-! ### The four differences, as exact bivariate models -/

section Differences
open PackedModels BivariateCertificate

/-- Seven rows and columns of 128-bit digits. -/
private def r79_cfg : Config := ⟨0, 3, 128⟩

/-- `a₀ ± a₁ x - a₂ x² + a₃ x³ + e y`, the shape of `k`, `l` and `c`. -/
private def r79_cubicM (a0 : XM) (neg1 : Bool) (a1 a2 a3 e : ℤ × ℕ) : XM :=
  XM.add r79_cfg (XM.add r79_cfg (XM.sub r79_cfg ((if neg1 then XM.sub r79_cfg else XM.add r79_cfg) a0
    (XM.mul r79_cfg (XM.ofInt r79_cfg a1.1 a1.2) (XM.varX r79_cfg)))
    (XM.mul r79_cfg (XM.ofInt r79_cfg a2.1 a2.2) (XM.pow r79_cfg (XM.varX r79_cfg) 2)))
    (XM.mul r79_cfg (XM.ofInt r79_cfg a3.1 a3.2) (XM.pow r79_cfg (XM.varX r79_cfg) 3)))
    (XM.mul r79_cfg (XM.ofInt r79_cfg e.1 e.2) (XM.varY r79_cfg))

private theorem r79_rep_cubicM {a0 : XM} {p0 : Bivar} (h0 : a0.Rep r79_cfg p0) (neg1 : Bool)
    {r1 r2 r3 r4 : ℚ} {a1 a2 a3 e : ℤ × ℕ} (h1 : r1=a1.1/a1.2) (h2 : r2=a2.1/a2.2)
    (h3 : r3=a3.1/a3.2) (h4 : r4=e.1/e.2) :
    (r79_cubicM a0 neg1 a1 a2 a3 e).Rep r79_cfg
      ((if neg1 then p0-scalar r1*X else p0+scalar r1*X)-scalar r2*X^2+
        scalar r3*X^3+scalar r4*C X) := by
  unfold r79_cubicM
  refine XM.rep_add (XM.rep_add (XM.rep_sub ?_ (XM.rep_mul (XM.rep_lit r79_cfg h2)
    (XM.rep_pow (XM.rep_X r79_cfg) 2))) (XM.rep_mul (XM.rep_lit r79_cfg h3)
    (XM.rep_pow (XM.rep_X r79_cfg) 3))) (XM.rep_mul (XM.rep_lit r79_cfg h4) (XM.rep_Y r79_cfg))
  cases neg1
  · exact XM.rep_add h0 (XM.rep_mul (XM.rep_lit r79_cfg h1) (XM.rep_X r79_cfg))
  · exact XM.rep_sub h0 (XM.rep_mul (XM.rep_lit r79_cfg h1) (XM.rep_X r79_cfg))

private def r79_kM : XM :=
  r79_cubicM (XM.ofInt r79_cfg 1673 2500) false (2609,5000) (1489,2500) (527,1250) (7,25)
private def r79_lM : XM :=
  r79_cubicM (XM.ofInt r79_cfg 1 1) false (7,400) (2733,2500) (639,500) (1,4)
private def r79_cM : XM :=
  r79_cubicM (XM.ofInt r79_cfg 10163 10000) true (209,10000) (5743,5000) (14069,10000) (1,4)

private theorem r79_rep_kM : r79_kM.Rep r79_cfg (Certificate.k .triangle) :=
  r79_rep_cubicM (XM.rep_lit r79_cfg (by norm_num)) false (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
private theorem r79_rep_lM : r79_lM.Rep r79_cfg (Certificate.l .triangle) :=
  r79_rep_cubicM (XM.rep_one r79_cfg) false (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem r79_rep_cM : r79_cM.Rep r79_cfg (Certificate.c .triangle) :=
  r79_rep_cubicM (XM.rep_lit r79_cfg (by norm_num)) true (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The differences, mirroring `difference`. -/
private def r79_differenceM : Fin 4 → XM :=
  ![XM.sub r79_cfg r79_lM r79_kM, XM.sub r79_cfg r79_cM r79_kM,
    XM.sub r79_cfg r79_cM (XM.mul r79_cfg (XM.ofInt r79_cfg 9 10) r79_lM),
    XM.sub r79_cfg (XM.mul r79_cfg (XM.ofInt r79_cfg 11 10) r79_lM) r79_cM]

private theorem r79_rep_differenceM (i : Fin 4) :
    (r79_differenceM i).Rep r79_cfg (difference i) := by
  fin_cases i
  · exact XM.rep_sub r79_rep_lM r79_rep_kM
  · exact XM.rep_sub r79_rep_cM r79_rep_kM
  · exact XM.rep_sub r79_rep_cM (XM.rep_mul (XM.rep_lit r79_cfg (by norm_num)) r79_rep_lM)
  · exact XM.rep_sub (XM.rep_mul (XM.rep_lit r79_cfg (by norm_num)) r79_rep_lM) r79_rep_cM

/-- The reserves `3/200, 7/1000, 2/25, 39/500`, as numerators and denominators. -/
private def r79_reserveN : Fin 4 → ℤ := ![3,7,2,39]
private def r79_reserveD : Fin 4 → ℕ := ![200,1000,25,500]

private theorem r79_check (i : Fin 4) :
    XM.lowerCheck r79_cfg (XM.triangleM r79_cfg (r79_differenceM i) 8 15) 3 (r79_reserveN i)
      (r79_reserveD i)=true := by
  revert i; decide +kernel

theorem difference_certificate (i : Fin 4) :
    Certificate.transform .triangle (difference i)=
      expansion 3 (Certificate.transform .triangle (difference i)) ∧
    differenceReserve i<Certificate.lowerOn .triangle 3 (difference i) :=
  XM.lower_certificate (XM.rep_triangleM (r79_rep_differenceM i) (by norm_num)) (r79_check i)
    (by fin_cases i <;> norm_num [differenceReserve,r79_reserveN,r79_reserveD])

end Differences

theorem lowerGap_certificate (far : Bool) :
    WholeIntervalPolynomial.centered 0 d (lowerGap far).derivative=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered 0 d (lowerGap far).derivative) ∧
    WholeIntervalPolynomial.upperOn 14 0 d (lowerGap far).derivative< -(37/100:ℚ) ∧
    (21/2500:ℚ)<(lowerGap far).eval d := by
  have hr := r79_rep_lowerGap far
  have hc := (r79_rep_derivative hr).centered (a:=0) (b:=d) 4 15 1 1 (by norm_num)
    (by norm_num [d]) (by norm_num [d])
  have hd : d=((8:ℤ):ℚ)/((15:ℕ):ℚ) := by norm_num [d]
  have h21 : (21/2500:ℚ)=((21:ℤ):ℚ)/((2500:ℕ):ℚ) := by norm_num
  refine ⟨?_,?_,?_⟩
  · cases far
    · exact hc.eq_expansion (by decide +kernel) (by decide +kernel)
    · exact hc.eq_expansion (by decide +kernel) (by decide +kernel)
  · cases far
    · rw [WholeIntervalPolynomial.Certificate.upperOn_eq_of_rep hc (by decide +kernel)
        (by decide +kernel)]
      decide +kernel
    · rw [WholeIntervalPolynomial.Certificate.upperOn_eq_of_rep hc (by decide +kernel)
        (by decide +kernel)]
      decide +kernel
  · rw [hd,r79_eval_rep hr (by cases far <;> decide +kernel) 8 15 (by norm_num),h21]
    cases far
    · exact r79_lt_div (by norm_num) (by decide +kernel) (by decide +kernel)
    · exact r79_lt_div (by norm_num) (by decide +kernel) (by decide +kernel)

open WholeIntervalPolynomial.Certificate in
private def r79_lgS (g : Scaled) : Scaled :=
  (((((Scaled.ofNat 1).add ((Scaled.const (7/400)).mul Scaled.var)).sub
    ((Scaled.const (2733/2500)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (639/500)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/4)).mul g))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_lg {g : Scaled} {q : ℚ[X]} (hg : g.Rep q) :
    (r79_lgS g).Rep (TwoVariablePolynomial.restrict (Certificate.l .triangle) X q) := by
  have e : TwoVariablePolynomial.restrict (Certificate.l .triangle) X q=
      1+C (7/400)*X-C (2733/2500)*X^2+C (639/500)*X^3+C (1/4)*q := by
    simp [TwoVariablePolynomial.restrict,Certificate.l,scalar]
  rw [e]
  exact (((Scaled.rep_one.add ((Scaled.rep_const _).mul Scaled.rep_var)).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul hg)

open WholeIntervalPolynomial.Certificate in
private def r79_upperGapS (far : Bool) : Scaled :=
  ((r79_lgS (r79_gS far)).add ((Scaled.const (3/20)).mul
    ((Scaled.const (8/15)).sub Scaled.var))).sub
  ((r79_cS (r79_gS far)).mul ((r79_C12of r79_thetaS).add
    ((Scaled.const (293/1000)).mul (r79_S9of r79_thetaS))))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_upperGap (far : Bool) : (r79_upperGapS far).Rep (upperGap far) := by
  have e : upperGap far=(TwoVariablePolynomial.restrict (Certificate.l .triangle) X
        (if far then C d-X else 0)+C (3/20)*(C (8/15)-X))-
      TwoVariablePolynomial.restrict (Certificate.c .triangle) X (if far then C d-X else 0)*
      (PositiveTD.Certificate.C12.comp (TwoVariablePolynomial.restrict
          (Certificate.theta .triangle) X (if far then C d-X else 0))+
        C (293/1000)*PositiveTD.Certificate.S9.comp (TwoVariablePolynomial.restrict
          (Certificate.theta .triangle) X (if far then C d-X else 0))) := by
    simp only [upperGap,edge,Certificate.qStar,Certificate.M,r79_restrict_sub,r79_restrict_mul,
      r79_restrict_add,r79_restrict_lift,r79_restrict_scalar,r79_restrict_X]
  rw [e]
  exact ((r79_rep_lg (r79_rep_g far)).add ((Scaled.rep_const _).mul
    ((Scaled.rep_const _).sub Scaled.rep_var))).sub
    ((r79_rep_c (r79_rep_g far)).mul ((r79_rep_C12of (r79_rep_theta _)).add
      ((Scaled.rep_const _).mul (r79_rep_S9of (r79_rep_theta _)))))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_centeredGap (far : Bool) :
    ((r79_upperGapS far).center 1 5 1 5).Rep (centeredGap far) := by
  have e : centeredGap far=WholeIntervalPolynomial.centered (-4/5) (6/5) (upperGap far) := by
    rw [centeredGap,WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine]
    congr 1
    norm_num
  rw [e]
  exact (r79_rep_upperGap far).centered 1 5 1 5 (by norm_num) (by norm_num) (by norm_num)

private theorem r79_curv_eq (l : List ℤ) (s : ℕ) (hs : s≠0) :
    (l.getD 2 0:ℚ)/s-∑ j : Fin 13,|(l.getD (j.val+3) 0:ℚ)/s| * (1/3)^(j.val+1)=
      ((l.getD 2 0*3^13-∑ j : Fin 13,|l.getD (j.val+3) 0| * 3^(12-j.val):ℤ):ℚ)/((s:ℚ)*3^13) := by
  have hs' : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  rw [eq_div_iff (by positivity)]
  push_cast
  rw [sub_mul,Finset.sum_mul]
  congr 1
  · field_simp
    norm_num
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : j.val≤12 := by omega
    rw [abs_div,abs_of_pos hs']
    have h3 : (3:ℚ)^13=3^(j.val+1)*3^(12-j.val) := by rw [← pow_add]; congr 1; omega
    rw [h3]
    field_simp
    rw [one_div,inv_pow,mul_assoc,inv_mul_cancel₀ (by positivity),mul_one]

private theorem r79_reserve {rn L0 L1 K : ℤ} {rd s : ℕ} (hrd : 0<rd) (hs : 0<s) (hK : 0<K)
    (h : rn*(4*K*s)<(4*K*L0-3^13*L1^2)*rd) :
    (rn:ℚ)/rd<(L0:ℚ)/s-((L1:ℚ)/s)^2/(4*((K:ℚ)/((s:ℚ)*3^13))) := by
  have hs' : (0:ℚ)<s := by exact_mod_cast hs
  have hK' : (0:ℚ)<K := by exact_mod_cast hK
  have key : (L0:ℚ)/s-((L1:ℚ)/s)^2/(4*((K:ℚ)/((s:ℚ)*3^13)))=
      ((4*K*L0-3^13*L1^2:ℤ):ℚ)/((4*K*s:ℤ):ℚ) := by
    push_cast
    field_simp
    ring
  rw [key,div_lt_div_iff₀ (by exact_mod_cast hrd) (by push_cast; positivity)]
  exact_mod_cast h

theorem upperGap_certificate (far : Bool) :
    centeredGap far=C (gapCoefficient far 0)+C (gapCoefficient far 1)*X+
      C (gapCoefficient far 2)*X^2+
        ∑j : Fin 13,C (gapCoefficient far (j.val+3))*X^(j.val+3) ∧
    0<gapCurvature far ∧
    gapReserve far<gapCoefficient far 0-(gapCoefficient far 1)^2/(4*gapCurvature far) := by
  have hrep := r79_rep_centeredGap far
  have hs : ((r79_upperGapS far).center 1 5 1 5).s≠0 := by cases far <;> decide +kernel
  have hcoef (j : ℕ) := hrep.coeff hs j
  have hcurv : gapCurvature far=
      ((((r79_upperGapS far).center 1 5 1 5).l.getD 2 0*3^13-∑ j : Fin 13,
        |((r79_upperGapS far).center 1 5 1 5).l.getD (j.val+3) 0| * 3^(12-j.val):ℤ):ℚ)/
        ((((r79_upperGapS far).center 1 5 1 5).s:ℚ)*3^13) := by
    simp only [gapCurvature,gapTail,gapCoefficient,hcoef]
    exact r79_curv_eq _ _ hs
  refine ⟨?_,?_,?_⟩
  · have hdeg : (centeredGap far).natDegree<16 :=
      lt_of_le_of_lt (hrep.natDegree_le hs) (by cases far <;> decide +kernel)
    rw [Fin.sum_univ_eq_sum_range (fun j => C (gapCoefficient far (j+3))*X^(j+3)) 13]
    conv_lhs => rw [(centeredGap far).as_sum_range_C_mul_X_pow' hdeg]
    rw [Finset.sum_range_succ',Finset.sum_range_succ',Finset.sum_range_succ']
    simp only [gapCoefficient,add_assoc,Nat.reduceAdd,zero_add,pow_zero,mul_one,pow_one]
    ring
  · rw [hcurv]
    apply div_pos _ (by positivity)
    exact_mod_cast (show (0:ℤ)<_ by cases far <;> decide +kernel)
  · rw [hcurv,gapCoefficient,gapCoefficient,hcoef 0,hcoef 1]
    cases far
    · rw [show gapReserve false=((239:ℤ):ℚ)/((50000:ℕ):ℚ) by norm_num [gapReserve]]
      exact r79_reserve (by norm_num) (Nat.pos_of_ne_zero hs) (by decide +kernel)
        (by decide +kernel)
    · rw [show gapReserve true=((1:ℤ):ℚ)/((625:ℕ):ℚ) by norm_num [gapReserve]]
      exact r79_reserve (by norm_num) (Nat.pos_of_ne_zero hs) (by decide +kernel)
        (by decide +kernel)

open WholeIntervalPolynomial.Certificate in
private def r79_rectMaxS : Scaled :=
  ((Scaled.const (11913/10000)).sub ((Scaled.const (1/4)).mul Scaled.var)).mul
    ((r79_C12of Scaled.var).add ((Scaled.const (293/1000)).mul (r79_S9of Scaled.var)))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_rectMax : r79_rectMaxS.Rep rectangleMaximum := by
  have e : rectangleMaximum=(C (11913/10000)-C (1/4)*X)*
      (PositiveTD.Certificate.C12.comp X+C (293/1000)*PositiveTD.Certificate.S9.comp X) := by
    simp only [rectangleMaximum,comp_X]
  rw [e]
  exact ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).mul
    ((r79_rep_C12of Scaled.rep_var).add ((Scaled.rep_const _).mul (r79_rep_S9of Scaled.rep_var)))

theorem rectangle_maximum_certificate :
    WholeIntervalPolynomial.centered 0 (1/6) rectangleMaximum=
      WholeIntervalPolynomial.expansion 13
        (WholeIntervalPolynomial.centered 0 (1/6) rectangleMaximum) ∧
    WholeIntervalPolynomial.upperOn 13 0 (1/6) rectangleMaximum<(299/250:ℚ) := by
  have hc := r79_rep_rectMax.centered (a:=0) (b:=1/6) 1 12 1 1 (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨hc.eq_expansion (by decide +kernel) (by decide +kernel),?_⟩
  rw [WholeIntervalPolynomial.Certificate.upperOn_eq_of_rep hc (by decide +kernel)
    (by decide +kernel)]
  decide +kernel

theorem difference_lower (i : Fin 4) {x y : ℝ}
    (hd : Explicit.Domain .triangle x y) :
    (differenceReserve i:ℝ)<evaluate x y (difference i) :=
  Certificate.positive_on_domain (difference_certificate i).1 (difference_certificate i).2 hd

theorem lowerGap_lower (far : Bool) {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    (21/2500:ℝ)<aeval x (lowerGap far) := by
  have hc := lowerGap_certificate far
  have hm : AntitoneOn (fun x : ℝ => aeval x (lowerGap far)) (Icc (0:ℝ) (8/15)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt (lowerGap far) x).continuousAt.continuousWithinAt)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt (lowerGap far) x)
    intro x hx
    have hx' : x∈Icc ((0:ℚ):ℝ) ((d:ℚ):ℝ) := by
      simp only [d]; push_cast; exact Ioo_subset_Icc_self hx
    have hh := (WholeIntervalPolynomial.interval_bounds (by norm_num : (0:ℚ)<d)
      hc.1 hx').2
    have hbound : (WholeIntervalPolynomial.upperOn 14 0 d (lowerGap far).derivative:ℝ)<
        -(37/100:ℝ) := by
      rw [show -(37/100:ℝ)=((-(37/100):ℚ):ℝ) by norm_num]
      exact Rat.cast_lt.mpr hc.2.1
    linarith
  have hh := hm hx (show (8/15:ℝ)∈Icc 0 (8/15) by norm_num) hx.2
  have he : (21/2500:ℝ)<aeval (8/15:ℝ) (lowerGap far) := by
    have hcast : (21/2500:ℝ)<(((lowerGap far).eval d:ℚ):ℝ) := by
      rw [show (21/2500:ℝ)=((21/2500:ℚ):ℝ) by norm_num]
      exact Rat.cast_lt.mpr hc.2.2
    have h8 : ((d:ℚ):ℝ)=8/15 := by norm_num [d]
    rwa [←Certificate.eval_rat,h8] at hcast
  exact he.trans_le hh

theorem upperGap_tail (far : Bool) {u : ℝ} (hu : |u|≤1/3) (j : Fin 13) :
    -(|(gapCoefficient far (j.val+3):ℝ)| *(1/3)^(j.val+1))*u^2≤
      (gapCoefficient far (j.val+3):ℝ)*u^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg u) hu (j.val+1)
  have hh := mul_le_mul_of_nonneg_left hp (abs_nonneg (gapCoefficient far (j.val+3):ℝ))
  have hbound : |(gapCoefficient far (j.val+3):ℝ)*u^(j.val+1)|≤
      |(gapCoefficient far (j.val+3):ℝ)| * (1/3)^(j.val+1) := by
    rw [abs_mul,abs_pow]; exact hh
  have hscaled := mul_le_mul_of_nonneg_right (abs_le.mp hbound).1 (sq_nonneg u)
  rw [show u^(j.val+3)=u^(j.val+1)*u^2 by rw [←pow_add]]
  linarith

theorem upperGap_lower (far : Bool) {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    (gapReserve far:ℝ)<aeval x (upperGap far) := by
  set u : ℝ := x-1/5 with hu_def
  have hu : |u|≤1/3 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => upperGap_tail far hu j)
  have he : (∑j : Fin 13,-(|(gapCoefficient far (j.val+3):ℝ)| * (1/3)^(j.val+1))*u^2)=
      -(gapTail far:ℝ)*u^2 := by
    simp [gapTail,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [he] at hsum
  have hid := congrArg (fun p : ℚ[X] => aeval u p) (upperGap_certificate far).1
  simp only [map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hid
  have hlower : (gapCoefficient far 0:ℝ)+(gapCoefficient far 1:ℝ)*u+
      (gapCurvature far:ℝ)*u^2≤aeval u (centeredGap far) := by
    dsimp only [gapCurvature]
    push_cast
    rw [hid]
    linarith
  have hκ : (0:ℝ)<(gapCurvature far:ℝ) := by exact_mod_cast (upperGap_certificate far).2.1
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(gapCoefficient far 0:ℝ)) (b:=(gapCoefficient far 1:ℝ)) (x:=u) hκ
  have hreserve : (gapReserve far:ℝ)<(gapCoefficient far 0:ℝ)-
      (gapCoefficient far 1:ℝ)^2/(4*(gapCurvature far:ℝ)) := by
    exact_mod_cast (upperGap_certificate far).2.2
  have hvalue : aeval u (centeredGap far)=aeval x (upperGap far) := by
    simp [centeredGap,aeval_comp,u]
  rw [hvalue] at hlower
  linarith

theorem rectangle_maximum_upper {x : ℝ} (hx : x∈Icc 0 (1/6:ℝ)) :
    aeval x rectangleMaximum<(299/250:ℝ) := by
  have hx' : x∈Icc ((0:ℚ):ℝ) (((1/6):ℚ):ℝ) := by push_cast; exact hx
  have hh := (WholeIntervalPolynomial.interval_bounds (by norm_num : (0:ℚ)<1/6)
    rectangle_maximum_certificate.1 hx').2
  have hc : (WholeIntervalPolynomial.upperOn 13 0 (1/6) rectangleMaximum:ℝ)<299/250 := by
    rw [show (299/250:ℝ)=((299/250:ℚ):ℝ) by norm_num]
    exact Rat.cast_lt.mpr rectangle_maximum_certificate.2
  exact hh.trans_lt hc

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Coefficients
