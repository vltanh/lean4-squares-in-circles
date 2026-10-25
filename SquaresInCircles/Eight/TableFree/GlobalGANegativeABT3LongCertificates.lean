module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3LongData
public import SquaresInCircles.Eight.TableFree.CertificateRestrictions
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongECertificates

/-!
# Literal whole-domain certificates for the twelve BT3 longer-E endpoints

Uncompiled exact rational coefficient inequalities from Section 12.
The TE base is the already proved positive-BT triangle base.  The
RE second derivative and its three intrinsic edges cover its entire
trapezoid, and RC uses its exact polynomial quotient in y.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LongE.Certificate
open NegativeA.LongE (Region)
open TensorWholeIntervalPolynomial TwoVariablePolynomial

def massReserve : Region → ℚ
  | .TE => 7/10 | .TC => 107/100 | .RE => 11/10 | .RC => 103/100
def TEbase (i : Fin 3) : ℚ[X] := TwoVariablePolynomial.baseY (numerator .TE i)
def TEquotient (i : Fin 3) : Bivar := divY (numerator .TE i)
def TEfar (i : Fin 3) : ℚ[X] := restrict (TEquotient i) X (C (8/15)-X)
def TEderivativeReserve : Fin 3 → ℚ := ![-7/10,-11/20,-1/2]
def TEfarReserve : Fin 3 → ℚ := ![11/1000,83/1000,123/1000]
def TCreserve : Fin 3 → ℚ := ![13/1000,4/125,53/200]
def REcurvatureReserve : Fin 3 → ℚ := ![-67/10,-36/5,-111/10]
def REboundary (i j : Fin 3) : ℚ[X] :=
  match j.val with
  | 0 => restrict (numerator .RE i) 0 X
  | 1 => restrict (numerator .RE i) (C (1/6)) X
  | _ => restrict (numerator .RE i) X (C (19/50)-X)
def RElength (j : Fin 3) : ℚ := ![19/50,16/75,1/6] j
def REreserve (i j : Fin 3) : ℚ :=
  ![![135/100000,1489/100000,2681/100000],
    ![134/100000,1489/100000,2681/100000],
    ![2979/10000,1489/100000,2680/100000]] i j
def RCbase (i : Fin 3) : ℚ[X] := TwoVariablePolynomial.baseY (numerator .RC i)
def RCquotient (i : Fin 3) : Bivar := divY (numerator .RC i)
def RCquotientReserve : Fin 3 → ℚ := ![427/500,148/125,3443/1000]

open CertificateRestrictions

/-- Proves all integer facts of a certificate by one kernel computation: the conjuncts of `P`
are left open and fixed by the goals they close. -/
private theorem h_all {P R : Prop} (hP : P) (h : P → R) : R := h hP

/-- Uses representations of the four masses of a numerator, each built once. -/
private theorem h_withMasses (φ : Bivar →+* ℚ[X]) (p0 p1 p2 p3 : Bivar)
    {a0 a1 a2 a3 : WholeIntervalPolynomial.Certificate.Scaled} {G : Prop}
    (h0 : RepOn φ a0 p0) (h1 : RepOn φ a1 p1) (h2 : RepOn φ a2 p2) (h3 : RepOn φ a3 p3)
    (h : RepOn φ a0 p0 → RepOn φ a1 p1 → RepOn φ a2 p2 → RepOn φ a3 p3 → G) : G :=
  h h0 h1 h2 h3

/-- Unfolds the parts of a numerator into ring expressions in `X`, `C X`, scalars, `lift` and
`cubicMass`; the substitution `pull` is pushed down to `X`, `C X`, scalars and `lift`. -/
macro "h_longe_unfold" : tactic => `(tactic| simp only [
    NegativeABT3.LongE.Certificate.A,NegativeABT3.LongE.Certificate.qB,
    NegativeABT3.LongE.Certificate.baseNorm,NegativeABT3.LongE.Certificate.P,
    NegativeABT3.LongE.Certificate.rho,NegativeABT3.LongE.Certificate.z,
    NegativeABT3.LongE.Certificate.e,NegativeABT3.LongE.Certificate.s,
    NegativeABT3.LongE.Certificate.delta,NegativeABT3.LongE.Certificate.k,
    NegativeABT3.LongE.Certificate.l,NegativeABT3.LongE.Certificate.m,
    NegativeABT3.LongE.Certificate.gain,NegativeABT3.LongE.Certificate.jE,
    NegativeABT3.LongE.Certificate.rotation,NegativeABT3.LongE.Certificate.ABase,
    NegativeA.LongE.Certificate.ABase,NegativeA.LongE.Certificate.M,
    NegativeA.LongE.Certificate.jE,NegativeA.LongE.Certificate.gain,
    NegativeA.LongE.Certificate.delta,NegativeA.LongE.Certificate.s,NegativeA.LongE.Certificate.z,
    NegativeA.LongE.Certificate.e,NegativeA.LongE.Certificate.k,NegativeA.LongE.Certificate.l,
    NegativeA.LongE.Certificate.c,NegativeA.LongE.Certificate.pull,
    NegativeA.LongE.Certificate.baseY,NonnegativeTotals.Certificate.theta,
    NonnegativeTotals.Certificate.e,NonnegativeTotals.Certificate.k,
    NonnegativeTotals.Certificate.l,NonnegativeTotals.Certificate.c,
    NonnegativeTotals.Certificate.J,NegativeA.LongE.Explicit.baseRegion,Matrix.cons_val,
    Fin.isValue,↓reduceIte,Fin.val_two,reduceCtorEq,false_and,and_true,true_and,Fin.val_zero,
    Fin.val_one,Nat.reduceEqDiff,Fin.reduceEq,and_false,Fin.coe_ofNat_eq_mod,Nat.reduceMod,
    false_or,or_false,true_or,or_true,eq_self_iff_true,substitute_X_CX,substitute_X,substitute_CX,
    substitute_scalar,substitute_lift,map_add,map_sub,map_mul,map_pow,map_one,map_neg])

/-- Two polynomials are equal when their scaled lists agree. -/
private theorem h_eq_of_rep {p q : ℚ[X]} {a b : WholeIntervalPolynomial.Certificate.Scaled}
    (ha : a.Rep p) (hb : b.Rep q)
    (h : a.s≠0 ∧ b.s≠0 ∧ WholeIntervalPolynomial.Certificate.smul (b.s:ℤ) a.l=
      WholeIntervalPolynomial.Certificate.smul (a.s:ℤ) b.l) : p=q := by
  obtain ⟨hs,hs',hl⟩ := h
  have e := congrArg WholeIntervalPolynomial.Certificate.toPoly hl
  simp only [WholeIntervalPolynomial.Certificate.toPoly_smul] at e
  unfold WholeIntervalPolynomial.Certificate.Scaled.Rep at ha hb
  rw [ha,hb] at e
  have hne : C ((a.s:ℚ)*b.s)≠0 := by
    rw [Ne,C_eq_zero]; exact mul_ne_zero (by exact_mod_cast hs) (by exact_mod_cast hs')
  apply mul_left_cancel₀ hne
  push_cast at e
  rw [map_mul]
  linear_combination e

/-- Unfolds the parts of a positive-BT3 numerator into ring expressions in `X`, `C X`, scalars,
`lift` and `cubicMass`. -/
macro "h_bt3_unfold" : tactic => `(tactic| simp only [
    PositiveBT3.LargeCertificate.A,PositiveBT3.LargeCertificate.P,
    PositiveBT3.LargeCertificate.baseNorm,PositiveBT3.LargeCertificate.rotation,
    PositiveBT3.LargeCertificate.qB,PositiveBT3.LargeCertificate.rho,
    PositiveBT3.LargeCertificate.theta,PositiveBT3.LargeCertificate.e,
    PositiveBT3.LargeCertificate.delta,PositiveBT3.LargeCertificate.k,
    PositiveBT3.LargeCertificate.l,PositiveBT3.LargeCertificate.m,PositiveBT3.LargeCertificate.jE,
    NonnegativeTotals.Certificate.ABase,NonnegativeTotals.Certificate.jE,
    NonnegativeTotals.Certificate.J,NonnegativeTotals.Certificate.k,
    NonnegativeTotals.Certificate.l,NonnegativeTotals.Certificate.c,
    NonnegativeTotals.Certificate.theta,NonnegativeTotals.Certificate.e,
    NonnegativeTotals.Certificate.delta,NonnegativeTotals.Certificate.qStar,Matrix.cons_val,
    Fin.isValue,↓reduceIte,Fin.val_two,reduceCtorEq,false_and,and_true,true_and,Fin.val_zero,
    Fin.val_one,Nat.reduceEqDiff,Fin.reduceEq,and_false,Fin.coe_ofNat_eq_mod,Nat.reduceMod,
    false_or,or_false,true_or,or_true,eq_self_iff_true])

/-! ### Exact models of the numerators

The bivariate certificates are checked on exact packed models (`BivariateCertificates`), as in
`GlobalGANegativeALongECertificates`, whose mirrors of the shared definitions are used here; the
definitions specific to `GlobalGANegativeABT3LongData` have their own mirrors below. -/

section Models
open PackedModels BivariateCertificate
open NegativeA.LongE.Certificate (h_kM h_lM h_cM h_MM h_deltaM h_ABaseM h_rep_kM h_rep_lM
  h_rep_cM h_rep_MM h_rep_deltaM h_rep_ABaseM)

/-- Mirror of `qB r`. -/
def h_qBM (cfg : Config) : Region → XM
  | .TE => XM.add cfg (h_lM cfg .TE)
      (XM.mul cfg (XM.ofInt cfg 3 20) (XM.sub cfg (XM.ofInt cfg 8 15) (XM.varX cfg)))
  | .TC => XM.add cfg (h_lM cfg .TC)
      (XM.mul cfg (XM.ofInt cfg 3 20) (XM.sub cfg (XM.ofInt cfg 8 15) (XM.varX cfg)))
  | .RE => h_cM cfg .RE
  | .RC => h_cM cfg .RC

theorem h_rep_qBM (cfg : Config) (r : Region) : (h_qBM cfg r).Rep cfg (qB r) := by
  cases r
  · exact XM.rep_add (h_rep_lM cfg _) (XM.rep_mul (XM.rep_lit cfg (by norm_num))
      (XM.rep_sub (XM.rep_lit cfg (by norm_num)) (XM.rep_X cfg)))
  · exact XM.rep_add (h_rep_lM cfg _) (XM.rep_mul (XM.rep_lit cfg (by norm_num))
      (XM.rep_sub (XM.rep_lit cfg (by norm_num)) (XM.rep_X cfg)))
  · exact h_rep_cM cfg _
  · exact h_rep_cM cfg _

/-- Mirror of `A r i`, reduced. -/
def h_AM (cfg : Config) (r : Region) (i : Fin 3) : XM :=
  XM.reduce cfg <| XM.add cfg (h_ABaseM cfg r)
    (XM.mul cfg (![XM.ofInt cfg 1 1,h_lM cfg r,h_qBM cfg r] i)
      (XM.sub cfg (XM.liftM cfg (h_deltaM cfg r) XM.C10L) (XM.ofInt cfg 1 1)))

theorem h_rep_AM (cfg : Config) (r : Region) (i : Fin 3) : (h_AM cfg r i).Rep cfg (A r i) := by
  have h1 : (![XM.ofInt cfg 1 1,h_lM cfg r,h_qBM cfg r] i).Rep cfg (![1,l r,qB r] i) := by
    fin_cases i
    · exact XM.rep_one cfg
    · exact h_rep_lM cfg r
    · exact h_rep_qBM cfg r
  exact XM.rep_reduce <| XM.rep_add (h_rep_ABaseM cfg r)
    (XM.rep_mul h1 (XM.rep_sub (XM.rep_liftC10 (h_rep_deltaM cfg r)) (XM.rep_one cfg)))

/-- Mirror of `baseNorm r`. -/
def h_baseNormM (cfg : Config) (r : Region) : Fin 4 → XM :=
  ![XM.add cfg (XM.ofInt cfg 1 1) (XM.pow cfg (h_kM cfg r) 2),
    XM.add cfg (XM.pow cfg (h_kM cfg r) 2) (XM.pow cfg (h_lM cfg r) 2),
    XM.add cfg (XM.pow cfg (h_lM cfg r) 2) (XM.pow cfg (h_cM cfg r) 2),
    XM.add cfg (XM.ofInt cfg 1 1) (XM.pow cfg (h_MM cfg r) 2)]

/-- Mirror of `P r i j`, reduced. -/
def h_PM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce cfg <| XM.sub cfg (h_baseNormM cfg r j)
    (if j.val=i.val then XM.mul cfg (XM.mul cfg (XM.ofInt cfg 2 1)
        (![h_kM cfg r,XM.mul cfg (h_kM cfg r) (h_lM cfg r),XM.mul cfg (h_lM cfg r) (h_cM cfg r),
          XM.ofInt cfg 0 1] j)) (XM.liftM cfg (h_deltaM cfg r) XM.S11L)
      else XM.ofInt cfg 0 1)

theorem h_rep_PM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) :
    (h_PM cfg r i j).Rep cfg (P r i j) := by
  have hb : (h_baseNormM cfg r j).Rep cfg (baseNorm r j) := by
    fin_cases j
    · exact XM.rep_add (XM.rep_one cfg) (XM.rep_pow (h_rep_kM cfg r) 2)
    · exact XM.rep_add (XM.rep_pow (h_rep_kM cfg r) 2) (XM.rep_pow (h_rep_lM cfg r) 2)
    · exact XM.rep_add (XM.rep_pow (h_rep_lM cfg r) 2) (XM.rep_pow (h_rep_cM cfg r) 2)
    · exact XM.rep_add (XM.rep_one cfg) (XM.rep_pow (h_rep_MM cfg r) 2)
  have hf : (![h_kM cfg r,XM.mul cfg (h_kM cfg r) (h_lM cfg r),XM.mul cfg (h_lM cfg r) (h_cM cfg r),
      XM.ofInt cfg 0 1] j).Rep cfg (![k r,k r*l r,l r*m r,0] j) := by
    fin_cases j
    · exact h_rep_kM cfg r
    · exact XM.rep_mul (h_rep_kM cfg r) (h_rep_lM cfg r)
    · exact XM.rep_mul (h_rep_lM cfg r) (h_rep_cM cfg r)
    · exact XM.rep_zero cfg
  unfold h_PM P
  apply XM.rep_reduce
  split_ifs
  · exact XM.rep_sub hb (XM.rep_mul (XM.rep_mul (XM.rep_lit cfg (by norm_num)) hf)
      (XM.rep_liftS11 (h_rep_deltaM cfg r)))
  · exact XM.rep_sub hb (XM.rep_zero cfg)

/-- `rho r i j` as a numerator and a denominator. -/
def h_rhoP (r : Region) (i : Fin 3) (j : Fin 4) : ℤ × ℕ :=
  match r with
  | .TE | .RE =>
    if j.val=i.val then
      if j=2 then (1302177104,1000000000) else (1107155480,1000000000)
    else ![(1203257512,1000000000),(1203257512,1000000000),(1425785990,1000000000),
      (1451171531,1000000000)] j
  | .TC | .RC =>
    if j.val=i.val then
      ![(1159403846,1000000000),(1232394077,1000000000),(1424873143,1000000000),(0,1)] j
    else ![(1265525725,1000000000),(1341857056,1000000000),(1560132267,1000000000),
      (1523913613,1000000000)] j

theorem h_rho_eq (r : Region) (i : Fin 3) (j : Fin 4) :
    rho r i j=((h_rhoP r i j).1:ℚ)/((h_rhoP r i j).2:ℚ) := by
  cases r <;> fin_cases i <;> fin_cases j <;> norm_num [rho,h_rhoP]

/-- Mirror of the opposite cubic corrections of `mass` on the two triangle G curves. -/
def h_corrM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  if (r=.TE∨r=.TC) ∧ i=1 then
    if j=1 then XM.mul cfg (XM.neg (XM.ofInt cfg 1 4)) (XM.pow cfg (XM.varX cfg) 3)
    else if j=3 then XM.mul cfg (XM.ofInt cfg 1 4) (XM.pow cfg (XM.varX cfg) 3)
    else XM.ofInt cfg 0 1
  else XM.ofInt cfg 0 1

/-- Mirror of `mass r i j`, reduced. -/
def h_massM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce cfg (XM.add cfg (XM.reduce cfg (XM.cubicMassM cfg (h_rhoP r i j).1 (h_rhoP r i j).2
    (h_PM cfg r i j))) (h_corrM cfg r i j))

theorem h_rep_massM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) :
    (h_massM cfg r i j).Rep cfg (mass r i j) :=
  XM.rep_reduce (XM.rep_add
    (XM.rep_reduce (XM.rep_cubicMassM (h_rep_PM cfg r i j) (h_rho_eq r i j)))
    (XM.rep_ite (XM.rep_ite (XM.rep_mul (XM.rep_neg (XM.rep_lit cfg (by norm_num)))
      (XM.rep_pow (XM.rep_X cfg) 3)) (XM.rep_ite (XM.rep_mul (XM.rep_lit cfg (by norm_num))
      (XM.rep_pow (XM.rep_X cfg) 3)) (XM.rep_zero cfg))) (XM.rep_zero cfg)))

/-- Mirror of `numerator r i`, reduced. -/
def h_numM (cfg : Config) (r : Region) (i : Fin 3) : XM :=
  let w := h_massM cfg r i
  XM.reduce cfg <| XM.sub cfg
    (XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.ofInt cfg 2 1)
      (h_AM cfg r i)) (w 0)) (w 1)) (w 2)) (w 3))
    (XM.mul cfg (XM.ofInt cfg 494696877 250000000) (XM.add cfg (XM.add cfg (XM.add cfg
      (XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.add cfg (h_PM cfg r i 0) (XM.pow cfg (w 0) 2)) (w 1))
        (w 2)) (w 3))
      (XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.add cfg (h_PM cfg r i 1) (XM.pow cfg (w 1) 2)) (w 0))
        (w 2)) (w 3)))
      (XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.add cfg (h_PM cfg r i 2) (XM.pow cfg (w 2) 2)) (w 0))
        (w 1)) (w 3)))
      (XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.add cfg (h_PM cfg r i 3) (XM.pow cfg (w 3) 2)) (w 0))
        (w 1)) (w 2))))

theorem h_rep_numM (cfg : Config) (r : Region) (i : Fin 3) :
    (h_numM cfg r i).Rep cfg (numerator r i) := by
  have hw (j : Fin 4) := h_rep_massM cfg r i j
  have hP (j : Fin 4) := h_rep_PM cfg r i j
  exact XM.rep_reduce <| XM.rep_sub (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_mul
      (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (h_rep_AM cfg r i)) (hw 0)) (hw 1)) (hw 2)) (hw 3))
    (XM.rep_mul (XM.rep_lit cfg (by norm_num [NonnegativeTotals.Certificate.Rbar]))
      (XM.rep_add (XM.rep_add (XM.rep_add
      (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 0) (XM.rep_pow (hw 0) 2)) (hw 1))
        (hw 2)) (hw 3))
      (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 1) (XM.rep_pow (hw 1) 2)) (hw 0))
        (hw 2)) (hw 3)))
      (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 2) (XM.rep_pow (hw 2) 2)) (hw 0))
        (hw 1)) (hw 3)))
      (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 3) (XM.rep_pow (hw 3) 2)) (hw 0))
        (hw 1)) (hw 2))))

end Models

section Checks
open PackedModels BivariateCertificate
open NegativeA.LongE.Certificate (h_transformM h_cfgMass h_cfgT h_cfgR)


/-! Each check is one kernel evaluation of the exact model; `Elab.async false` runs the checks
one at a time, which bounds the memory of the file by that of the largest check. -/

/-- The reserves as numerators and denominators. -/
def h_massResP : Region → ℤ × ℕ
  | .TE => (7,10) | .TC => (107,100) | .RE => (11,10) | .RC => (103,100)
def h_TEdR : Fin 3 → ℤ × ℕ := ![(-7,10),(-11,20),(-1,2)]
def h_TCR : Fin 3 → ℤ × ℕ := ![(13,1000),(4,125),(53,200)]
def h_REcR : Fin 3 → ℤ × ℕ := ![(-67,10),(-36,5),(-111,10)]
def h_RCqR : Fin 3 → ℤ × ℕ := ![(427,500),(148,125),(3443,1000)]

set_option Elab.async false in
private theorem h_massCheck_TE : ∀ i : Fin 3, ∀ j : Fin 4,
    XM.lowerCheck h_cfgMass (XM.reduce h_cfgMass (h_transformM h_cfgMass .TE
      (h_massM h_cfgMass .TE i j))) 3 7 10=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_massCheck_TC : ∀ i : Fin 3, ∀ j : Fin 4,
    XM.lowerCheck h_cfgMass (XM.reduce h_cfgMass (h_transformM h_cfgMass .TC
      (h_massM h_cfgMass .TC i j))) 3 107 100=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_massCheck_RE : ∀ i : Fin 3, ∀ j : Fin 4,
    XM.lowerCheck h_cfgMass (XM.reduce h_cfgMass (h_transformM h_cfgMass .RE
      (h_massM h_cfgMass .RE i j))) 3 11 10=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_massCheck_RC : ∀ i : Fin 3, ∀ j : Fin 4,
    XM.lowerCheck h_cfgMass (XM.reduce h_cfgMass (h_transformM h_cfgMass .RC
      (h_massM h_cfgMass .RC i j))) 3 103 100=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TEderivCheck_0 :
    XM.upperCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TE (XM.reduce h_cfgT
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 0)))))) 39 (-7) 10=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TEderivCheck_1 :
    XM.upperCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TE (XM.reduce h_cfgT
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 1)))))) 39 (-11) 20=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TEderivCheck_2 :
    XM.upperCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TE (XM.reduce h_cfgT
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 2)))))) 39 (-1) 2=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TCCheck_0 :
    XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (XM.reduce h_cfgT
      (h_numM h_cfgT .TC 0)))) 39 (13) 1000=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TCCheck_1 :
    XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (XM.reduce h_cfgT
      (h_numM h_cfgT .TC 1)))) 39 (4) 125=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TCCheck_2 :
    XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (XM.reduce h_cfgT
      (h_numM h_cfgT .TC 2)))) 39 (53) 200=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_REcurvCheck_0 :
    XM.upperCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RE (XM.reduce h_cfgR
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 0)))))) 35 (-67) 10=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_REcurvCheck_1 :
    XM.upperCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RE (XM.reduce h_cfgR
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 1)))))) 35 (-36) 5=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_REcurvCheck_2 :
    XM.upperCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RE (XM.reduce h_cfgR
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 2)))))) 35 (-111) 10=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_RCquotCheck_0 :
    XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC (XM.reduce h_cfgR
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 0))))) 35 (427) 500=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_RCquotCheck_1 :
    XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC (XM.reduce h_cfgR
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 1))))) 35 (148) 125=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_RCquotCheck_2 :
    XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC (XM.reduce h_cfgR
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 2))))) 35 (3443) 1000=true := by
  decide +kernel

end Checks

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem mass_certificate (r : Region) (i : Fin 3) (j : Fin 4) :
    transform r (mass r i j)=expansion 3 (transform r (mass r i j)) ∧
    massReserve r<lowerOn r 3 (mass r i j) := by
  open PackedModels BivariateCertificate in
  open NegativeA.LongE.Certificate (h_transformM h_rep_transformM h_cfgMass h_cfgT h_cfgR) in
  have h : XM.lowerCheck h_cfgMass (XM.reduce h_cfgMass (h_transformM h_cfgMass r
      (h_massM h_cfgMass r i j))) 3 (h_massResP r).1 (h_massResP r).2=true := by
    cases r
    · exact h_massCheck_TE i j
    · exact h_massCheck_TC i j
    · exact h_massCheck_RE i j
    · exact h_massCheck_RC i j
  exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM (h_rep_massM h_cfgMass r i j) r)) h
    (by cases r <;> norm_num [massReserve,h_massResP])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_TEbase_identity_0 :
    TEbase 0=PositiveBT3.LargeCertificate.triangleBase 0 := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply h_eq_of_rep ?ha ?hb hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      simp only [TEbase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .TE 0)
      apply h_withMasses (yZero) (mass .TE 0 0) (mass .TE 0 1) (mass .TE 0 2) (mass .TE 0 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_yZero
        all_goals assumption
    case hb =>
      simp only [PositiveBT3.LargeCertificate.triangleBase,baseY_eq_yZero]
      change RepOn yZero _ (PositiveBT3.LargeCertificate.numerator .triangle 0)
      apply h_withMasses (yZero) (PositiveBT3.LargeCertificate.mass .triangle 0 0)
        (PositiveBT3.LargeCertificate.mass .triangle 0 1)
        (PositiveBT3.LargeCertificate.mass .triangle 0 2)
        (PositiveBT3.LargeCertificate.mass .triangle 0 3)
      case h0 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.1
      case h1 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.2.2.1
      case h2 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      case h3 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [PositiveBT3.LargeCertificate.numerator]
        h_bt3_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_TEbase_identity_1 :
    TEbase 1=PositiveBT3.LargeCertificate.triangleBase 1 := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply h_eq_of_rep ?ha ?hb hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      simp only [TEbase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .TE 1)
      apply h_withMasses (yZero) (mass .TE 1 0) (mass .TE 1 1) (mass .TE 1 2) (mass .TE 1 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_yZero
        all_goals assumption
    case hb =>
      simp only [PositiveBT3.LargeCertificate.triangleBase,baseY_eq_yZero]
      change RepOn yZero _ (PositiveBT3.LargeCertificate.numerator .triangle 1)
      apply h_withMasses (yZero) (PositiveBT3.LargeCertificate.mass .triangle 1 0)
        (PositiveBT3.LargeCertificate.mass .triangle 1 1)
        (PositiveBT3.LargeCertificate.mass .triangle 1 2)
        (PositiveBT3.LargeCertificate.mass .triangle 1 3)
      case h0 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.1
      case h1 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.2.2.1
      case h2 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      case h3 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [PositiveBT3.LargeCertificate.numerator]
        h_bt3_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_TEbase_identity_2 :
    TEbase 2=PositiveBT3.LargeCertificate.triangleBase 2 := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply h_eq_of_rep ?ha ?hb hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      simp only [TEbase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .TE 2)
      apply h_withMasses (yZero) (mass .TE 2 0) (mass .TE 2 1) (mass .TE 2 2) (mass .TE 2 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_yZero
        all_goals assumption
    case hb =>
      simp only [PositiveBT3.LargeCertificate.triangleBase,baseY_eq_yZero]
      change RepOn yZero _ (PositiveBT3.LargeCertificate.numerator .triangle 2)
      apply h_withMasses (yZero) (PositiveBT3.LargeCertificate.mass .triangle 2 0)
        (PositiveBT3.LargeCertificate.mass .triangle 2 1)
        (PositiveBT3.LargeCertificate.mass .triangle 2 2)
        (PositiveBT3.LargeCertificate.mass .triangle 2 3)
      case h0 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.1
      case h1 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.2.2.1
      case h2 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      case h3 =>
        simp only [PositiveBT3.LargeCertificate.mass]; h_bt3_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [PositiveBT3.LargeCertificate.numerator]
        h_bt3_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem TEbase_identity (i : Fin 3) :
    TEbase i=PositiveBT3.LargeCertificate.triangleBase i := by
  fin_cases i
  · exact h_TEbase_identity_0
  · exact h_TEbase_identity_1
  · exact h_TEbase_identity_2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem TEderivative_certificate (i : Fin 3) :
    transform .TE (derivativeY (TEquotient i))=
      expansion 39 (transform .TE (derivativeY (TEquotient i))) ∧
    upperOn .TE 39 (derivativeY (TEquotient i))<TEderivativeReserve i := by
  open PackedModels BivariateCertificate in
  open NegativeA.LongE.Certificate (h_transformM h_rep_transformM h_cfgMass h_cfgT h_cfgR) in
  have h : XM.upperCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TE (XM.reduce h_cfgT
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE i))))))
      39 (h_TEdR i).1 (h_TEdR i).2=true := by
    fin_cases i
    · exact h_TEderivCheck_0
    · exact h_TEderivCheck_1
    · exact h_TEderivCheck_2
  have hq := XM.rep_derivYM (XM.rep_divYM (h_rep_numM h_cfgT .TE i))
  exact XM.upper_certificate (XM.rep_reduce (h_rep_transformM (XM.rep_reduce hq) .TE)) h
    (by fin_cases i <;> norm_num [TEderivativeReserve,h_TEdR])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_TEfar_0 :
    WholeIntervalPolynomial.centered 0 (8/15) (TEfar 0)=
      WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 (8/15) (TEfar 0)) ∧
    (11/1000:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 (8/15) (TEfar 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (8/15) 4 15 (by norm_num) (by norm_num) 39 (11/1000:ℚ) 11 1000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      unfold TEfar TEquotient
      apply far_rep (8/15) 4 15 (by norm_num) (by norm_num) ?hΨ ?hB hall.2.2.2.2.2.2.2.2.2.2.2.2.1
      case hΨ =>
        have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        have hV : ((Scaled.const (8/15)).sub Scaled.var).Rep (C (8/15)-X : ℚ[X]) :=
          (Scaled.rep_const (8/15)).sub Scaled.rep_var
        apply h_withMasses (onCurve X (C (8/15)-X)) (mass .TE 0 0) (mass .TE 0 1) (mass .TE 0 2)
          (mass .TE 0 3)
        case h0 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NegativeABT3.LongE.Certificate.numerator]
          h_longe_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .TE 0 0) (mass .TE 0 1) (mass .TE 0 2) (mass .TE 0 3)
        case h0 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NegativeABT3.LongE.Certificate.numerator]
          h_longe_unfold
          build_rep_yZero
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_TEfar_1 :
    WholeIntervalPolynomial.centered 0 (8/15) (TEfar 1)=
      WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 (8/15) (TEfar 1)) ∧
    (83/1000:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 (8/15) (TEfar 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (8/15) 4 15 (by norm_num) (by norm_num) 39 (83/1000:ℚ) 83 1000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      unfold TEfar TEquotient
      apply far_rep (8/15) 4 15 (by norm_num) (by norm_num) ?hΨ ?hB hall.2.2.2.2.2.2.2.2.2.2.2.2.1
      case hΨ =>
        have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        have hV : ((Scaled.const (8/15)).sub Scaled.var).Rep (C (8/15)-X : ℚ[X]) :=
          (Scaled.rep_const (8/15)).sub Scaled.rep_var
        apply h_withMasses (onCurve X (C (8/15)-X)) (mass .TE 1 0) (mass .TE 1 1) (mass .TE 1 2)
          (mass .TE 1 3)
        case h0 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NegativeABT3.LongE.Certificate.numerator]
          h_longe_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .TE 1 0) (mass .TE 1 1) (mass .TE 1 2) (mass .TE 1 3)
        case h0 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NegativeABT3.LongE.Certificate.numerator]
          h_longe_unfold
          build_rep_yZero
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_TEfar_2 :
    WholeIntervalPolynomial.centered 0 (8/15) (TEfar 2)=
      WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 (8/15) (TEfar 2)) ∧
    (123/1000:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 (8/15) (TEfar 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (8/15) 4 15 (by norm_num) (by norm_num) 39 (123/1000:ℚ) 123 1000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      unfold TEfar TEquotient
      apply far_rep (8/15) 4 15 (by norm_num) (by norm_num) ?hΨ ?hB hall.2.2.2.2.2.2.2.2.2.2.2.2.1
      case hΨ =>
        have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        have hV : ((Scaled.const (8/15)).sub Scaled.var).Rep (C (8/15)-X : ℚ[X]) :=
          (Scaled.rep_const (8/15)).sub Scaled.rep_var
        apply h_withMasses (onCurve X (C (8/15)-X)) (mass .TE 2 0) (mass .TE 2 1) (mass .TE 2 2)
          (mass .TE 2 3)
        case h0 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NegativeABT3.LongE.Certificate.numerator]
          h_longe_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .TE 2 0) (mass .TE 2 1) (mass .TE 2 2) (mass .TE 2 3)
        case h0 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NegativeABT3.LongE.Certificate.numerator]
          h_longe_unfold
          build_rep_yZero
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem TEfar_certificate (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 (8/15) (TEfar i)=
      WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 (8/15) (TEfar i)) ∧
    TEfarReserve i<WholeIntervalPolynomial.lowerOn 39 0 (8/15) (TEfar i) := by
  fin_cases i
  · exact h_TEfar_0
  · exact h_TEfar_1
  · exact h_TEfar_2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem TC_certificate (i : Fin 3) :
    transform .TC (numerator .TC i)=expansion 39 (transform .TC (numerator .TC i)) ∧
    TCreserve i<lowerOn .TC 39 (numerator .TC i) := by
  open PackedModels BivariateCertificate in
  open NegativeA.LongE.Certificate (h_transformM h_rep_transformM h_cfgMass h_cfgT h_cfgR) in
  have h : XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (XM.reduce h_cfgT
      (h_numM h_cfgT .TC i))))
      39 (h_TCR i).1 (h_TCR i).2=true := by
    fin_cases i
    · exact h_TCCheck_0
    · exact h_TCCheck_1
    · exact h_TCCheck_2
  have hq := h_rep_numM h_cfgT .TC i
  exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM (XM.rep_reduce hq) .TC)) h
    (by fin_cases i <;> norm_num [TCreserve,h_TCR])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem REcurvature_certificate (i : Fin 3) :
    transform .RE (numerator .RE i).derivative.derivative=
      expansion 35 (transform .RE (numerator .RE i).derivative.derivative) ∧
    upperOn .RE 35 (numerator .RE i).derivative.derivative<REcurvatureReserve i := by
  open PackedModels BivariateCertificate in
  open NegativeA.LongE.Certificate (h_transformM h_rep_transformM h_cfgMass h_cfgT h_cfgR) in
  have h : XM.upperCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RE (XM.reduce h_cfgR
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE i))))))
      35 (h_REcR i).1 (h_REcR i).2=true := by
    fin_cases i
    · exact h_REcurvCheck_0
    · exact h_REcurvCheck_1
    · exact h_REcurvCheck_2
  have hq := XM.rep_derivXM (XM.rep_derivXM (h_rep_numM h_cfgR .RE i))
  exact XM.upper_certificate (XM.rep_reduce (h_rep_transformM (XM.rep_reduce hq) .RE)) h
    (by fin_cases i <;> norm_num [REcurvatureReserve,h_REcR])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_REboundary_0_0 :
    WholeIntervalPolynomial.centered 0 (19/50) (REboundary 0 0)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (19/50) (REboundary 0 0)) ∧
    (135/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (19/50) (REboundary 0 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (19/50) 19 100 (by norm_num) (by norm_num) 35 (135/100000:ℚ) 135 100000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      rw [show REboundary 0 0=xZero (numerator .RE 0) from baseX_eq_xZero _]
      change RepOn xZero _ _
      apply h_withMasses (xZero) (mass .RE 0 0) (mass .RE 0 1) (mass .RE 0 2) (mass .RE 0 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_REboundary_0_1 :
    WholeIntervalPolynomial.centered 0 (16/75) (REboundary 0 1)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (16/75) (REboundary 0 1)) ∧
    (1489/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (16/75) (REboundary 0 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (16/75) 8 75 (by norm_num) (by norm_num) 35 (1489/100000:ℚ) 1489 100000
      (by norm_num) (by norm_num) hall.2.2.2.2
    case ha =>
      rw [show REboundary 0 1=onCurve (C (1/6)) X (numerator .RE 0) from rfl]
      have hU : (Scaled.const (1/6)).Rep (C (1/6) : ℚ[X]) := Scaled.rep_const (1/6)
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve (C (1/6)) X) (mass .RE 0 0) (mass .RE 0 1) (mass .RE 0 2)
        (mass .RE 0 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_curve
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_REboundary_0_2 :
    WholeIntervalPolynomial.centered 0 (1/6) (REboundary 0 2)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (1/6) (REboundary 0 2)) ∧
    (2681/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (REboundary 0 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (2681/100000:ℚ) 2681 100000
      (by norm_num) (by norm_num) hall.2.2.2.2
    case ha =>
      rw [show REboundary 0 2=onCurve X (C (19/50)-X) (numerator .RE 0) from rfl]
      have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      have hV : ((Scaled.const (19/50)).sub Scaled.var).Rep (C (19/50)-X : ℚ[X]) :=
        (Scaled.rep_const (19/50)).sub Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve X (C (19/50)-X)) (mass .RE 0 0) (mass .RE 0 1) (mass .RE 0 2)
        (mass .RE 0 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_curve
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_REboundary_1_0 :
    WholeIntervalPolynomial.centered 0 (19/50) (REboundary 1 0)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (19/50) (REboundary 1 0)) ∧
    (134/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (19/50) (REboundary 1 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (19/50) 19 100 (by norm_num) (by norm_num) 35 (134/100000:ℚ) 134 100000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      rw [show REboundary 1 0=xZero (numerator .RE 1) from baseX_eq_xZero _]
      change RepOn xZero _ _
      apply h_withMasses (xZero) (mass .RE 1 0) (mass .RE 1 1) (mass .RE 1 2) (mass .RE 1 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_REboundary_1_1 :
    WholeIntervalPolynomial.centered 0 (16/75) (REboundary 1 1)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (16/75) (REboundary 1 1)) ∧
    (1489/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (16/75) (REboundary 1 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (16/75) 8 75 (by norm_num) (by norm_num) 35 (1489/100000:ℚ) 1489 100000
      (by norm_num) (by norm_num) hall.2.2.2.2
    case ha =>
      rw [show REboundary 1 1=onCurve (C (1/6)) X (numerator .RE 1) from rfl]
      have hU : (Scaled.const (1/6)).Rep (C (1/6) : ℚ[X]) := Scaled.rep_const (1/6)
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve (C (1/6)) X) (mass .RE 1 0) (mass .RE 1 1) (mass .RE 1 2)
        (mass .RE 1 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_curve
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_REboundary_1_2 :
    WholeIntervalPolynomial.centered 0 (1/6) (REboundary 1 2)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (1/6) (REboundary 1 2)) ∧
    (2681/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (REboundary 1 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (2681/100000:ℚ) 2681 100000
      (by norm_num) (by norm_num) hall.2.2.2.2
    case ha =>
      rw [show REboundary 1 2=onCurve X (C (19/50)-X) (numerator .RE 1) from rfl]
      have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      have hV : ((Scaled.const (19/50)).sub Scaled.var).Rep (C (19/50)-X : ℚ[X]) :=
        (Scaled.rep_const (19/50)).sub Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve X (C (19/50)-X)) (mass .RE 1 0) (mass .RE 1 1) (mass .RE 1 2)
        (mass .RE 1 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_curve
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_REboundary_2_0 :
    WholeIntervalPolynomial.centered 0 (19/50) (REboundary 2 0)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (19/50) (REboundary 2 0)) ∧
    (2979/10000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (19/50) (REboundary 2 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (19/50) 19 100 (by norm_num) (by norm_num) 35 (2979/10000:ℚ) 2979 10000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      rw [show REboundary 2 0=xZero (numerator .RE 2) from baseX_eq_xZero _]
      change RepOn xZero _ _
      apply h_withMasses (xZero) (mass .RE 2 0) (mass .RE 2 1) (mass .RE 2 2) (mass .RE 2 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_REboundary_2_1 :
    WholeIntervalPolynomial.centered 0 (16/75) (REboundary 2 1)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (16/75) (REboundary 2 1)) ∧
    (1489/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (16/75) (REboundary 2 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (16/75) 8 75 (by norm_num) (by norm_num) 35 (1489/100000:ℚ) 1489 100000
      (by norm_num) (by norm_num) hall.2.2.2.2
    case ha =>
      rw [show REboundary 2 1=onCurve (C (1/6)) X (numerator .RE 2) from rfl]
      have hU : (Scaled.const (1/6)).Rep (C (1/6) : ℚ[X]) := Scaled.rep_const (1/6)
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve (C (1/6)) X) (mass .RE 2 0) (mass .RE 2 1) (mass .RE 2 2)
        (mass .RE 2 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_curve
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_REboundary_2_2 :
    WholeIntervalPolynomial.centered 0 (1/6) (REboundary 2 2)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (1/6) (REboundary 2 2)) ∧
    (2680/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (REboundary 2 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (2680/100000:ℚ) 2680 100000
      (by norm_num) (by norm_num) hall.2.2.2.2
    case ha =>
      rw [show REboundary 2 2=onCurve X (C (19/50)-X) (numerator .RE 2) from rfl]
      have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      have hV : ((Scaled.const (19/50)).sub Scaled.var).Rep (C (19/50)-X : ℚ[X]) :=
        (Scaled.rep_const (19/50)).sub Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve X (C (19/50)-X)) (mass .RE 2 0) (mass .RE 2 1) (mass .RE 2 2)
        (mass .RE 2 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_curve
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem REboundary_certificate (i j : Fin 3) :
    WholeIntervalPolynomial.centered 0 (RElength j) (REboundary i j)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (RElength j) (REboundary i j)) ∧
    REreserve i j<WholeIntervalPolynomial.lowerOn 35 0 (RElength j) (REboundary i j) := by
  fin_cases i <;> fin_cases j
  · exact h_REboundary_0_0
  · exact h_REboundary_0_1
  · exact h_REboundary_0_2
  · exact h_REboundary_1_0
  · exact h_REboundary_1_1
  · exact h_REboundary_1_2
  · exact h_REboundary_2_0
  · exact h_REboundary_2_1
  · exact h_REboundary_2_2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem RCquotient_certificate (i : Fin 3) :
    transform .RC (RCquotient i)=expansion 35 (transform .RC (RCquotient i)) ∧
    RCquotientReserve i<lowerOn .RC 35 (RCquotient i) := by
  open PackedModels BivariateCertificate in
  open NegativeA.LongE.Certificate (h_transformM h_rep_transformM h_cfgMass h_cfgT h_cfgR) in
  have h : XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC (XM.reduce h_cfgR
      (XM.divYM h_cfgR (h_numM h_cfgR .RC i)))))
      35 (h_RCqR i).1 (h_RCqR i).2=true := by
    fin_cases i
    · exact h_RCquotCheck_0
    · exact h_RCquotCheck_1
    · exact h_RCquotCheck_2
  have hq := XM.rep_divYM (h_rep_numM h_cfgR .RC i)
  exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM (XM.rep_reduce hq) .RC)) h
    (by fin_cases i <;> norm_num [RCquotientReserve,h_RCqR])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_RCbase_0 :
    WholeIntervalPolynomial.centered 0 (1/6) (RCbase 0)=
      WholeIntervalPolynomial.expansion 35 (WholeIntervalPolynomial.centered 0 (1/6) (RCbase 0)) ∧
    (2209/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (2209/100000:ℚ) 2209 100000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [RCbase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .RC 0)
      apply h_withMasses (yZero) (mass .RC 0 0) (mass .RC 0 1) (mass .RC 0 2) (mass .RC 0 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_RCbase_1 :
    WholeIntervalPolynomial.centered 0 (1/6) (RCbase 1)=
      WholeIntervalPolynomial.expansion 35 (WholeIntervalPolynomial.centered 0 (1/6) (RCbase 1)) ∧
    (2209/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (2209/100000:ℚ) 2209 100000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [RCbase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .RC 1)
      apply h_withMasses (yZero) (mass .RC 1 0) (mass .RC 1 1) (mass .RC 1 2) (mass .RC 1 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_RCbase_2 :
    WholeIntervalPolynomial.centered 0 (1/6) (RCbase 2)=
      WholeIntervalPolynomial.expansion 35 (WholeIntervalPolynomial.centered 0 (1/6) (RCbase 2)) ∧
    (2209/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (2209/100000:ℚ) 2209 100000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [RCbase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .RC 2)
      apply h_withMasses (yZero) (mass .RC 2 0) (mass .RC 2 1) (mass .RC 2 2) (mass .RC 2 3)
      case h0 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeABT3.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeABT3.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem RCbase_certificate (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 (1/6) (RCbase i)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (1/6) (RCbase i)) ∧
    (2209/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase i) := by
  fin_cases i
  · exact h_RCbase_0
  · exact h_RCbase_1
  · exact h_RCbase_2

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LongE.Certificate
