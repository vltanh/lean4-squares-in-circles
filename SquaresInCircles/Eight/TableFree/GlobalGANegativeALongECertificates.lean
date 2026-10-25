module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongEData
public import SquaresInCircles.Eight.TableFree.CertificateRestrictions
public import SquaresInCircles.Eight.TableFree.NonnegativeTotalsMirrors

/-!
# The twelve longer-E numerator certificates

Uncompiled transcription of Section 7. Each arithmetic proposition is
the exact finite coefficient formula of the hand proof, to be reduced by
the standard kernel when this source is eventually elaborated. The TE
base is identified with the earlier pure-T base; the RE trapezoid uses
its three actual boundary curves and its whole-domain second derivative.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

def massReserve : Region → ℚ
  | .TE => 71/100 | .TC => 107/100 | .RE => 11/10 | .RC => 103/100
def TEbase (i : Fin 3) : ℚ[X] := TwoVariablePolynomial.baseY (numerator .TE i)
def TEquotient (i : Fin 3) : Bivar := divY (numerator .TE i)
def TEfar (i : Fin 3) : ℚ[X] := restrict (TEquotient i) X (C (8/15)-X)
def TEderivativeReserve : Fin 3 → ℚ := ![-67/100,-51/100,-11/25]
def TEfarReserve : Fin 3 → ℚ := ![47/1000,13/200,11/500]
def TEcentered : ℚ[X] := (TEfar 0).comp (X+C (4/15))
def TEcoefficient (j : ℕ) : ℚ := TEcentered.coeff j
def TEtail : ℚ := ∑j : Fin 37,|TEcoefficient (j.val+3)| *(4/15)^(j.val+1)
def TEcurvature : ℚ := TEcoefficient 2-TEtail
def TCreserve : Fin 3 → ℚ := ![3/125,43/1000,153/500]
def REcurvatureReserve : Fin 3 → ℚ := ![-7,-7,-11]
def REboundary (i j : Fin 3) : ℚ[X] :=
  match j.val with
  | 0 => restrict (numerator .RE i) 0 X
  | 1 => restrict (numerator .RE i) (C (1/6)) X
  | _ => restrict (numerator .RE i) X (C (19/50)-X)
def RElength (j : Fin 3) : ℚ := ![19/50,16/75,1/6] j
def REreserve (i j : Fin 3) : ℚ :=
  ![![13/10000,37/2500,67/2500],![13/10000,37/2500,67/2500],
    ![1587/5000,37/2500,13/500]] i j
def RCbase (i : Fin 3) : ℚ[X] := TwoVariablePolynomial.baseY (numerator .RC i)
def RCquotient (i : Fin 3) : Bivar := divY (numerator .RC i)
def RCbaseReserve : Fin 3 → ℚ := ![11/500,11/500,21/1000]
def RCquotientReserve : Fin 3 → ℚ := ![9/10,123/100,91/25]

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
    NegativeA.LongE.Certificate.A,NegativeA.LongE.Certificate.ABase,NegativeA.LongE.Certificate.P,
    NegativeA.LongE.Certificate.baseNorm,NegativeA.LongE.Certificate.M,
    NegativeA.LongE.Certificate.qB,NegativeA.LongE.Certificate.jE,
    NegativeA.LongE.Certificate.gain,NegativeA.LongE.Certificate.delta,
    NegativeA.LongE.Certificate.s,NegativeA.LongE.Certificate.z,NegativeA.LongE.Certificate.e,
    NegativeA.LongE.Certificate.k,NegativeA.LongE.Certificate.l,NegativeA.LongE.Certificate.c,
    NegativeA.LongE.Certificate.pull,NegativeA.LongE.Certificate.baseY,
    NegativeA.LongE.Certificate.rho,NonnegativeTotals.Certificate.theta,
    NonnegativeTotals.Certificate.e,NonnegativeTotals.Certificate.k,
    NonnegativeTotals.Certificate.l,NonnegativeTotals.Certificate.c,
    NonnegativeTotals.Certificate.J,NegativeA.LongE.Explicit.baseRegion,Matrix.cons_val,
    Fin.isValue,↓reduceIte,Fin.val_two,reduceCtorEq,false_and,and_true,true_and,Fin.val_zero,
    Fin.val_one,Nat.reduceEqDiff,Fin.reduceEq,and_false,Fin.coe_ofNat_eq_mod,Nat.reduceMod,
    false_or,or_false,true_or,or_true,eq_self_iff_true,substitute_X_CX,substitute_X,substitute_CX,
    substitute_scalar,substitute_lift,map_add,map_sub,map_mul,map_pow,map_one,map_neg])

/-! ### Exact models of the numerators

The bivariate certificates are checked on exact packed models (`BivariateCertificates`): each
definition of `GlobalGANegativeALongEData` has an `XM` mirror, generic in the packing `Config`,
with a representation lemma proved once for all regions and indices. The kernel then evaluates
`lowerCheck` or `upperCheck` on the model of the transformed polynomial. -/

section Models
open PackedModels BivariateCertificate

/-- `baseY r` as `polyF F / q`. -/
def h_pullF : Region → List (ℤ × ℕ × ℕ)
  | .TE | .RE => [(1,0,1)]
  | .TC => [(19,0,0),(50,0,1)]
  | .RC => [(19,0,0),(50,0,1),(-50,1,0)]

/-- The denominator of `h_pullF`. -/
def h_pullQ : Region → ℕ
  | .TE | .RE => 1
  | .TC | .RC => 50

/-- Mirror of `pull r`. -/
def h_pullM (cfg : Config) (r : Region) (m : XM) : XM := XM.substY cfg m (h_pullF r) (h_pullQ r)

theorem h_rep_pullM {cfg : Config} {m : XM} {p : Bivar} (hm : m.Rep cfg p) (r : Region) :
    (h_pullM cfg r m).Rep cfg (pull r p) := by
  have h := XM.rep_substY hm (F := h_pullF r) (by cases r <;> simp [h_pullF]) (h_pullQ r)
  have e : scalar (1/(h_pullQ r:ℚ))*XM.polyF (h_pullF r)=baseY r := by
    apply eq_of_evaluate; intro x y
    cases r <;> simp [h_pullF,h_pullQ,XM.polyF,baseY] <;> ring
  rw [e] at h
  exact h

/-- Mirror of `z r`. -/
def h_zM (cfg : Config) (r : Region) : XM :=
  h_pullM cfg r (NonnegativeTotalsMirrors.thetaM cfg (Explicit.baseRegion r))
/-- Mirror of `e r`. -/
def h_eM (cfg : Config) (r : Region) : XM :=
  h_pullM cfg r (NonnegativeTotalsMirrors.eM cfg (Explicit.baseRegion r))
/-- Mirror of `k r`. -/
def h_kM (cfg : Config) (r : Region) : XM :=
  h_pullM cfg r (NonnegativeTotalsMirrors.kM cfg (Explicit.baseRegion r))
/-- Mirror of `l r`. -/
def h_lM (cfg : Config) (r : Region) : XM :=
  h_pullM cfg r (NonnegativeTotalsMirrors.lM cfg (Explicit.baseRegion r))
/-- Mirror of `c r`. -/
def h_cM (cfg : Config) (r : Region) : XM :=
  h_pullM cfg r (NonnegativeTotalsMirrors.cM cfg (Explicit.baseRegion r))

theorem h_rep_zM (cfg : Config) (r : Region) : (h_zM cfg r).Rep cfg (z r) :=
  h_rep_pullM (NonnegativeTotalsMirrors.rep_thetaM cfg _) r
theorem h_rep_eM (cfg : Config) (r : Region) : (h_eM cfg r).Rep cfg (e r) :=
  h_rep_pullM (NonnegativeTotalsMirrors.rep_eM cfg _) r
theorem h_rep_kM (cfg : Config) (r : Region) : (h_kM cfg r).Rep cfg (k r) :=
  h_rep_pullM (NonnegativeTotalsMirrors.rep_kM cfg _) r
theorem h_rep_lM (cfg : Config) (r : Region) : (h_lM cfg r).Rep cfg (l r) :=
  h_rep_pullM (NonnegativeTotalsMirrors.rep_lM cfg _) r
theorem h_rep_cM (cfg : Config) (r : Region) : (h_cM cfg r).Rep cfg (c r) :=
  h_rep_pullM (NonnegativeTotalsMirrors.rep_cM cfg _) r

/-- Mirror of `s r`. -/
def h_sM (cfg : Config) : Region → XM
  | .TE => XM.varY cfg
  | .TC | .RC => XM.ofInt cfg 19 50
  | .RE => XM.add cfg (XM.varX cfg) (XM.varY cfg)

theorem h_rep_sM (cfg : Config) (r : Region) : (h_sM cfg r).Rep cfg (s r) := by
  cases r
  · exact XM.rep_Y cfg
  · exact XM.rep_lit cfg (by norm_num)
  · exact XM.rep_add (XM.rep_X cfg) (XM.rep_Y cfg)
  · exact XM.rep_lit cfg (by norm_num)

/-- Mirror of `delta r`. -/
def h_deltaM (cfg : Config) (r : Region) : XM :=
  XM.sub cfg (XM.add cfg (h_zM cfg r) (h_eM cfg r)) (h_sM cfg r)

theorem h_rep_deltaM (cfg : Config) (r : Region) : (h_deltaM cfg r).Rep cfg (delta r) :=
  XM.rep_sub (XM.rep_add (h_rep_zM cfg r) (h_rep_eM cfg r)) (h_rep_sM cfg r)

/-- Mirror of `gain`. -/
def h_gainM (cfg : Config) (u : XM) : XM :=
  XM.add cfg (XM.mul cfg (XM.ofInt cfg 13 12) (XM.liftM cfg u XM.S11L))
    (XM.mul cfg (XM.sub cfg (XM.ofInt cfg 82 125) (XM.mul cfg (XM.ofInt cfg 63 100) u))
      (XM.sub cfg (XM.liftM cfg u XM.C10L) (XM.ofInt cfg 1 1)))

theorem h_rep_gainM {cfg : Config} {u : XM} {f : Bivar} (hu : u.Rep cfg f) :
    (h_gainM cfg u).Rep cfg (gain f) :=
  XM.rep_add (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (XM.rep_liftS11 hu))
    (XM.rep_mul (XM.rep_sub (XM.rep_lit cfg (by norm_num))
      (XM.rep_mul (XM.rep_lit cfg (by norm_num)) hu))
      (XM.rep_sub (XM.rep_liftC10 hu) (XM.rep_one cfg)))

/-- Mirror of `jE r`. -/
def h_jEM (cfg : Config) : Region → XM
  | .TE => XM.sub cfg (NonnegativeTotalsMirrors.JM cfg (h_eM cfg .TE))
      (XM.mul cfg (XM.ofInt cfg 1 500) (XM.pow cfg (h_eM cfg .TE) 4))
  | .TC => XM.sub cfg (NonnegativeTotalsMirrors.JM cfg (h_eM cfg .TC))
      (XM.mul cfg (XM.ofInt cfg 1 500) (XM.pow cfg (h_eM cfg .TC) 4))
  | .RE => NonnegativeTotalsMirrors.JM cfg (h_eM cfg .RE)
  | .RC => XM.sub cfg (NonnegativeTotalsMirrors.JM cfg (h_eM cfg .RC))
      (XM.mul cfg (XM.ofInt cfg 29 1000) (XM.pow cfg (h_eM cfg .RC) 4))

theorem h_rep_jEM (cfg : Config) (r : Region) : (h_jEM cfg r).Rep cfg (jE r) := by
  cases r
  · exact XM.rep_sub (NonnegativeTotalsMirrors.rep_JM (h_rep_eM cfg _))
      (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (XM.rep_pow (h_rep_eM cfg _) 4))
  · exact XM.rep_sub (NonnegativeTotalsMirrors.rep_JM (h_rep_eM cfg _))
      (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (XM.rep_pow (h_rep_eM cfg _) 4))
  · exact NonnegativeTotalsMirrors.rep_JM (h_rep_eM cfg _)
  · exact XM.rep_sub (NonnegativeTotalsMirrors.rep_JM (h_rep_eM cfg _))
      (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (XM.rep_pow (h_rep_eM cfg _) 4))

/-- Mirror of `M r`. -/
def h_MM (cfg : Config) (r : Region) : XM :=
  XM.mul cfg (h_cM cfg r) (XM.add cfg (XM.liftM cfg (h_zM cfg r) XM.C12L)
    (XM.mul cfg (XM.ofInt cfg 293 1000) (XM.liftM cfg (h_zM cfg r) XM.S9L)))

theorem h_rep_MM (cfg : Config) (r : Region) : (h_MM cfg r).Rep cfg (M r) :=
  XM.rep_mul (h_rep_cM cfg r) (XM.rep_add (XM.rep_liftC12 (h_rep_zM cfg r))
    (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (XM.rep_liftS9 (h_rep_zM cfg r))))

/-- Mirror of `ABase r`; the constant `(3/2)(293/1000)+1/2-sigmabar` is `-475977291/10⁹`. -/
def h_ABaseM (cfg : Config) (r : Region) : XM :=
  XM.add cfg (XM.add cfg (XM.add cfg (XM.add cfg (XM.add cfg
    (XM.mul cfg (XM.ofInt cfg 2 1) (h_kM cfg r)) (XM.mul cfg (XM.ofInt cfg 3 1) (h_lM cfg r)))
    (XM.ofInt cfg 3 1))
    (XM.mul cfg (h_cM cfg r) (XM.add cfg (XM.add cfg (XM.ofInt cfg 1 1)
      (XM.mul cfg (XM.ofInt cfg 2 1) (XM.liftM cfg (h_zM cfg r) XM.C10L)))
      (XM.mul cfg (XM.ofInt cfg (-475977291) 1000000000)
        (XM.liftM cfg (h_zM cfg r) XM.S9L)))))
    (h_jEM cfg r))
    (XM.mul cfg (h_lM cfg r) (h_gainM cfg (h_sM cfg r)))

theorem h_rep_ABaseM (cfg : Config) (r : Region) : (h_ABaseM cfg r).Rep cfg (ABase r) :=
  XM.rep_add (XM.rep_add (XM.rep_add (XM.rep_add (XM.rep_add
    (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (h_rep_kM cfg r))
    (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (h_rep_lM cfg r)))
    (XM.rep_lit cfg (by norm_num)))
    (XM.rep_mul (h_rep_cM cfg r) (XM.rep_add (XM.rep_add (XM.rep_one cfg)
      (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (XM.rep_liftC10 (h_rep_zM cfg r))))
      (XM.rep_mul (XM.rep_lit cfg (by norm_num [NonnegativeTotals.Certificate.sigmabar]))
        (XM.rep_liftS9 (h_rep_zM cfg r))))))
    (h_rep_jEM cfg r))
    (XM.rep_mul (h_rep_lM cfg r) (h_rep_gainM (h_rep_sM cfg r)))


/-- Mirror of `qB r`. -/
def h_qBM (cfg : Config) : Region → XM
  | .TE => XM.add cfg (h_lM cfg .TE)
      (XM.mul cfg (XM.ofInt cfg 3 20) (XM.sub cfg (XM.ofInt cfg 8 15) (XM.varX cfg)))
  | .TC => XM.add cfg (h_lM cfg .TC)
      (XM.mul cfg (XM.ofInt cfg 3 20) (XM.sub cfg (XM.ofInt cfg 8 15) (XM.varX cfg)))
  | .RE => h_MM cfg .RE
  | .RC => h_MM cfg .RC

theorem h_rep_qBM (cfg : Config) (r : Region) : (h_qBM cfg r).Rep cfg (qB r) := by
  cases r
  · exact XM.rep_add (h_rep_lM cfg _) (XM.rep_mul (XM.rep_lit cfg (by norm_num))
      (XM.rep_sub (XM.rep_lit cfg (by norm_num)) (XM.rep_X cfg)))
  · exact XM.rep_add (h_rep_lM cfg _) (XM.rep_mul (XM.rep_lit cfg (by norm_num))
      (XM.rep_sub (XM.rep_lit cfg (by norm_num)) (XM.rep_X cfg)))
  · exact h_rep_MM cfg _
  · exact h_rep_MM cfg _

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
    XM.add cfg (XM.pow cfg (h_lM cfg r) 2) (XM.pow cfg (h_MM cfg r) 2),
    XM.add cfg (XM.ofInt cfg 1 1) (XM.pow cfg (h_cM cfg r) 2)]

/-- Mirror of `P r i j`, reduced. -/
def h_PM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce cfg <| XM.sub cfg (h_baseNormM cfg r j)
    (if j.val=i.val then XM.mul cfg (XM.mul cfg (XM.ofInt cfg 2 1)
        (![h_kM cfg r,XM.mul cfg (h_kM cfg r) (h_lM cfg r),XM.mul cfg (h_lM cfg r) (h_MM cfg r),
          XM.ofInt cfg 0 1] j)) (XM.liftM cfg (h_deltaM cfg r) XM.S11L)
      else XM.ofInt cfg 0 1)

theorem h_rep_PM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) :
    (h_PM cfg r i j).Rep cfg (P r i j) := by
  have hb : (h_baseNormM cfg r j).Rep cfg (baseNorm r j) := by
    fin_cases j
    · exact XM.rep_add (XM.rep_one cfg) (XM.rep_pow (h_rep_kM cfg r) 2)
    · exact XM.rep_add (XM.rep_pow (h_rep_kM cfg r) 2) (XM.rep_pow (h_rep_lM cfg r) 2)
    · exact XM.rep_add (XM.rep_pow (h_rep_lM cfg r) 2) (XM.rep_pow (h_rep_MM cfg r) 2)
    · exact XM.rep_add (XM.rep_one cfg) (XM.rep_pow (h_rep_cM cfg r) 2)
  have hf : (![h_kM cfg r,XM.mul cfg (h_kM cfg r) (h_lM cfg r),XM.mul cfg (h_lM cfg r) (h_MM cfg r),
      XM.ofInt cfg 0 1] j).Rep cfg (![k r,k r*l r,l r*M r,0] j) := by
    fin_cases j
    · exact h_rep_kM cfg r
    · exact XM.rep_mul (h_rep_kM cfg r) (h_rep_lM cfg r)
    · exact XM.rep_mul (h_rep_lM cfg r) (h_rep_MM cfg r)
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
      if j=2 then (1325511353,1000000000) else (27678887,25000000)
    else ![(150407189,125000000),(150407189,125000000),(1451171531,1000000000),
      (142578599,100000000)] j
  | .TC | .RC =>
    if j.val=i.val then
      ![(579701923,500000000),(1232394077,1000000000),(1450364739,1000000000),(0,1)] j
    else ![(50621029,40000000),(167732132,125000000),(1587872067,1000000000),
      (747493761,500000000)] j

theorem h_rho_eq (r : Region) (i : Fin 3) (j : Fin 4) :
    rho r i j=((h_rhoP r i j).1:ℚ)/((h_rhoP r i j).2:ℚ) := by
  cases r <;> fin_cases i <;> fin_cases j <;> norm_num [rho,h_rhoP]

/-- Mirror of `mass r i j`, reduced. -/
def h_massM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce cfg (XM.cubicMassM cfg (h_rhoP r i j).1 (h_rhoP r i j).2 (h_PM cfg r i j))

theorem h_rep_massM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) :
    (h_massM cfg r i j).Rep cfg (mass r i j) :=
  XM.rep_reduce (XM.rep_cubicMassM (h_rep_PM cfg r i j) (h_rho_eq r i j))

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

/-- Mirror of `transform r`. -/
def h_transformM (cfg : Config) (r : Region) (m : XM) : XM :=
  match r with
  | .TE => XM.triangleM cfg m 8 15
  | .TC => XM.triangleM cfg m 23 150
  | .RE => XM.fanM cfg m 19 50 (-1) 1 1 6
  | .RC => XM.fanM cfg m 23 150 1 1 1 6

theorem h_rep_transformM {cfg : Config} {m : XM} {p : Bivar} (hm : m.Rep cfg p) (r : Region) :
    (h_transformM cfg r m).Rep cfg (transform r p) := by
  cases r
  · exact XM.rep_triangleM hm (by norm_num)
  · exact XM.rep_triangleM hm (by norm_num)
  · exact XM.rep_fanNegM hm (by norm_num) (by norm_num) (by norm_num)
  · exact XM.rep_trapezoidM hm (by norm_num) (by norm_num) (by norm_num)

end Models

section Checks
open PackedModels BivariateCertificate

/-- Packing for the cubic masses: total degree up to `30`, digits of `1100` bits. -/
def h_cfgMass : Config := ⟨0,16,1100⟩
/-- Packing for the triangle numerators: degrees up to `39`, digits of `2500` bits. -/
def h_cfgT : Config := ⟨0,20,2500⟩
/-- Packing for the trapezoid numerators: degrees up to `35`, digits of `2400` bits. -/
def h_cfgR : Config := ⟨0,18,2400⟩

/-! Each check is one kernel evaluation of the exact model; `Elab.async false` runs the checks
one at a time, which bounds the memory of the file by that of the largest check. -/

/-- The reserves as numerators and denominators. -/
def h_massResP : Region → ℤ × ℕ
  | .TE => (71,100) | .TC => (107,100) | .RE => (11,10) | .RC => (103,100)
def h_TEdR : Fin 3 → ℤ × ℕ := ![(-67,100),(-51,100),(-11,25)]
def h_TCR : Fin 3 → ℤ × ℕ := ![(3,125),(43,1000),(153,500)]
def h_REcR : Fin 3 → ℤ × ℕ := ![(-7,1),(-7,1),(-11,1)]
def h_RCqR : Fin 3 → ℤ × ℕ := ![(9,10),(123,100),(91,25)]

set_option Elab.async false in
private theorem h_massCheck_TE : ∀ i : Fin 3, ∀ j : Fin 4,
    XM.lowerCheck h_cfgMass (XM.reduce h_cfgMass (h_transformM h_cfgMass .TE
      (h_massM h_cfgMass .TE i j))) 3 71 100=true := by
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
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 0)))))) 39 (-67) 100=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TEderivCheck_1 :
    XM.upperCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TE (XM.reduce h_cfgT
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 1)))))) 39 (-51) 100=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TEderivCheck_2 :
    XM.upperCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TE (XM.reduce h_cfgT
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 2)))))) 39 (-11) 25=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TCCheck_0 :
    XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (XM.reduce h_cfgT
      (h_numM h_cfgT .TC 0)))) 39 (3) 125=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TCCheck_1 :
    XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (XM.reduce h_cfgT
      (h_numM h_cfgT .TC 1)))) 39 (43) 1000=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_TCCheck_2 :
    XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (XM.reduce h_cfgT
      (h_numM h_cfgT .TC 2)))) 39 (153) 500=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_REcurvCheck_0 :
    XM.upperCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RE (XM.reduce h_cfgR
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 0)))))) 35 (-7) 1=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_REcurvCheck_1 :
    XM.upperCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RE (XM.reduce h_cfgR
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 1)))))) 35 (-7) 1=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_REcurvCheck_2 :
    XM.upperCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RE (XM.reduce h_cfgR
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 2)))))) 35 (-11) 1=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_RCquotCheck_0 :
    XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC (XM.reduce h_cfgR
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 0))))) 35 (9) 10=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_RCquotCheck_1 :
    XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC (XM.reduce h_cfgR
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 1))))) 35 (123) 100=true := by
  decide +kernel

set_option Elab.async false in
private theorem h_RCquotCheck_2 :
    XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC (XM.reduce h_cfgR
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 2))))) 35 (91) 25=true := by
  decide +kernel

end Checks

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem mass_certificate (r : Region) (i : Fin 3) (j : Fin 4) :
    transform r (mass r i j)=expansion 3 (transform r (mass r i j)) ∧
    massReserve r<lowerOn r 3 (mass r i j) := by
  open PackedModels BivariateCertificate in
  have h : XM.lowerCheck h_cfgMass (XM.reduce h_cfgMass (h_transformM h_cfgMass r
      (h_massM h_cfgMass r i j))) 3 (h_massResP r).1 (h_massResP r).2=true := by
    cases r
    · exact h_massCheck_TE i j
    · exact h_massCheck_TC i j
    · exact h_massCheck_RE i j
    · exact h_massCheck_RC i j
  exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM (h_rep_massM h_cfgMass r i j) r)) h
    (by cases r <;> norm_num [massReserve,h_massResP])

/-- `baseY` as a ring homomorphism: evaluate the inner variable at zero. -/
private abbrev r70β : Bivar →+* ℚ[X] := Polynomial.mapRingHom (Polynomial.evalRingHom (0:ℚ))

private theorem r70_baseY (p : Bivar) : TwoVariablePolynomial.baseY p=r70β p := by
  have h : (Polynomial.eval₂RingHom (Polynomial.C : ℚ →+* ℚ[X]) (0:ℚ[X]))=
      Polynomial.C.comp (Polynomial.evalRingHom (0:ℚ)) := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp
  change p.eval₂ (Polynomial.eval₂RingHom Polynomial.C 0) X=p.map _
  rw [h]
  rfl

private theorem r70_scalar (r : ℚ) : r70β (scalar r)=C r := by simp [scalar]
private theorem r70_X : r70β (X:Bivar)=X := by simp
private theorem r70_CX : r70β (C X:Bivar)=0 := by simp

private theorem r70_lift (f : Bivar) (q : ℚ[X]) : r70β (lift f q)=q.comp (r70β f) := by
  change r70β (q.eval₂ ((Polynomial.C).comp Polynomial.C) f)=_
  rw [Polynomial.hom_eval₂]
  have h : r70β.comp ((Polynomial.C).comp Polynomial.C)=(Polynomial.C : ℚ →+* ℚ[X]) :=
    Subsingleton.elim _ _
  rw [h]
  rfl

private theorem r70_constant (p : Bivar) : constant p=(r70β p).coeff 0 := by
  simp [constant,Polynomial.coeff_zero_eq_eval_zero]

private def r70T (q : ℚ[X]) : ℚ[X] := ∑ i : Fin 4,C (q.coeff i.val)*X^i.val

private theorem r70_trunc (p : Bivar) : r70β (truncate3 p)=r70T (r70β p) := by
  simp [truncate3,r70T,Fin.sum_univ_four,scalar,Polynomial.coeff_zero_eq_eval_zero]

private def r70W (q : ℚ[X]) : ℚ[X] := C (1/q.coeff 0)*(r70T q-C (q.coeff 0))
private def r70Φ (rho : ℚ) (q : ℚ[X]) : ℚ[X] :=
  C rho*r70T (1+C (1/2)*r70W q-C (1/8)*(r70W q)^2+C (1/16)*(r70W q)^3)

private theorem r70_mass (rho : ℚ) (p : Bivar) : r70β (cubicMass rho p)=r70Φ rho (r70β p) := by
  simp only [cubicMass,map_mul,r70_scalar,r70_trunc,map_add,map_sub,map_one,map_pow,
    r70_constant,r70Φ,r70W]

private theorem r70_lift_CX : lift (C X : Bivar)=(Polynomial.C : ℚ[X] →+* Bivar) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [lift]
  · simp [lift]

private theorem r70_pull_TE (p : Bivar) : pull .TE p=p := by
  simp only [pull,Certificate.baseY]
  change p.eval₂ (lift (C X)) X=p
  rw [r70_lift_CX,eval₂_C_X]

private theorem r70_gain_zero : r70β (gain (C X))=0 := by
  simp only [gain,map_add,map_mul,map_sub,map_one,r70_lift,r70_scalar,r70_CX,Polynomial.comp_zero]
  simp [PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,
    PositiveTD.Certificate.S5,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4]

/-- Both bases are the inner-variable-zero restrictions of numerators that
agree once the inner variable vanishes: the identity is structural. -/
theorem TEbase_identity (i : Fin 3) :
    TEbase i=NonnegativeTotals.Certificate.triangleBase .atT i := by
  have hk : k .TE=NonnegativeTotals.Certificate.k .triangle := by
    simp [k,r70_pull_TE,Explicit.baseRegion]
  have hl : l .TE=NonnegativeTotals.Certificate.l .triangle := by
    simp [l,r70_pull_TE,Explicit.baseRegion]
  have hc : c .TE=NonnegativeTotals.Certificate.c .triangle := by
    simp [c,r70_pull_TE,Explicit.baseRegion]
  have hz : z .TE=NonnegativeTotals.Certificate.theta .triangle := by
    simp [z,r70_pull_TE,Explicit.baseRegion]
  have he : e .TE=NonnegativeTotals.Certificate.e .triangle := by
    simp [e,r70_pull_TE,Explicit.baseRegion]
  have hs : s .TE=C X := rfl
  have hM : M .TE=NonnegativeTotals.Certificate.M .triangle .atT := by
    simp only [M,NonnegativeTotals.Certificate.M,hc,hz]
  have hqB : qB .TE=NonnegativeTotals.Certificate.qB .triangle .atT := by
    simp only [qB,NonnegativeTotals.Certificate.qB,NonnegativeTotals.Certificate.qStar,hl]
  have hjE : jE .TE=NonnegativeTotals.Certificate.jE .triangle := by
    simp only [jE,NonnegativeTotals.Certificate.jE,he]
  have hbase : baseNorm .TE=NonnegativeTotals.Certificate.baseNorm .triangle .atT := by
    simp only [baseNorm,NonnegativeTotals.Certificate.baseNorm,hk,hl,hM,hc]
  have hABase : ABase .TE=NonnegativeTotals.Certificate.ABase .triangle .atT+l .TE*gain (s .TE) := by
    simp only [ABase,NonnegativeTotals.Certificate.ABase,hk,hl,hc,hz,hjE]
  have hδ : r70β (delta .TE)=r70β (NonnegativeTotals.Certificate.delta .triangle) := by
    simp only [delta,NonnegativeTotals.Certificate.delta,hz,he,hs,NonnegativeTotals.Certificate.e,
      map_add,map_sub,r70_CX,add_zero,sub_zero]
  have hA : r70β (A .TE i)=r70β (NonnegativeTotals.Certificate.A .triangle .atT i) := by
    simp only [A,NonnegativeTotals.Certificate.A,hABase,hl,hqB,map_add,map_mul,map_sub,map_one,
      r70_lift,hδ,hs,r70_gain_zero,mul_zero,add_zero]
  have hP (j : Fin 4) : r70β (P .TE i j)=r70β (NonnegativeTotals.Certificate.P .triangle .atT i j) := by
    simp only [P,NonnegativeTotals.Certificate.P,hbase,hk,hl,hM]
    split_ifs <;> simp only [map_sub,map_mul,r70_lift,hδ,map_zero]
  have hrho (j : Fin 4) : rho .TE i j=NonnegativeTotals.Certificate.rho .atT i j := by
    fin_cases i <;> fin_cases j <;> simp [rho,NonnegativeTotals.Certificate.rho]
  simp only [TEbase,NonnegativeTotals.Certificate.triangleBase,r70_baseY]
  simp only [numerator,NonnegativeTotals.Certificate.numerator,mass,NonnegativeTotals.Certificate.mass,
    map_sub,map_mul,map_add,map_pow,r70_scalar,r70_mass,hA,hP,hrho]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem TEderivative_certificate (i : Fin 3) :
    transform .TE (derivativeY (TEquotient i))=
      expansion 39 (transform .TE (derivativeY (TEquotient i))) ∧
    upperOn .TE 39 (derivativeY (TEquotient i))<TEderivativeReserve i := by
  open PackedModels BivariateCertificate in
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
private theorem h_TEfar_1 :
    WholeIntervalPolynomial.centered 0 (8/15) (TEfar 1)=
      WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 (8/15) (TEfar 1)) ∧
    (13/200:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 (8/15) (TEfar 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (8/15) 4 15 (by norm_num) (by norm_num) 39 (13/200:ℚ) 13 200
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
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NegativeA.LongE.Certificate.numerator]
          h_longe_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .TE 1 0) (mass .TE 1 1) (mass .TE 1 2) (mass .TE 1 3)
        case h0 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NegativeA.LongE.Certificate.numerator]
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
    (11/500:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 (8/15) (TEfar 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (8/15) 4 15 (by norm_num) (by norm_num) 39 (11/500:ℚ) 11 500
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
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NegativeA.LongE.Certificate.numerator]
          h_longe_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .TE 2 0) (mass .TE 2 1) (mass .TE 2 2) (mass .TE 2 3)
        case h0 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NegativeA.LongE.Certificate.numerator]
          h_longe_unfold
          build_rep_yZero
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem TEfar_GB_certificate (i : Fin 3) (hi : i=1∨i=2) :
    WholeIntervalPolynomial.centered 0 (8/15) (TEfar i)=
      WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 (8/15) (TEfar i)) ∧
    TEfarReserve i<WholeIntervalPolynomial.lowerOn 39 0 (8/15) (TEfar i) := by
  rcases hi with rfl|rfl
  · exact h_TEfar_1
  · exact h_TEfar_2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem TEfar_H_certificate :
    TEcentered=C (TEcoefficient 0)+C (TEcoefficient 1)*X+C (TEcoefficient 2)*X^2+
      ∑j : Fin 37,C (TEcoefficient (j.val+3))*X^(j.val+3) ∧
    (133/100:ℚ)<TEcurvature ∧
    (47/1000:ℚ)<TEcoefficient 0-(TEcoefficient 1)^2/(4*TEcurvature) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply quadratic_tail_cert ?ha 37 (4/15) 4 15 (by norm_num) (by norm_num) (133/100) 133 100
      (by norm_num) (by norm_num) (47/1000) 47 1000 (by norm_num) (by norm_num)
        hall.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      rw [show TEcentered=(TEfar 0).comp (C (4/15)+X) by rw [TEcentered,add_comm]]
      apply rep_comp_shift ?hb 1 15 4 15 (4/15) (by norm_num) (by norm_num) (by norm_num)
      case hb =>
        unfold TEfar TEquotient
        apply far_rep (8/15) 4 15 (by norm_num) (by norm_num) ?hΨ ?hB hall.2.2.2.2.2.2.2.2.2.2.2.2.1
        case hΨ =>
          have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
          have hV : ((Scaled.const (8/15)).sub Scaled.var).Rep (C (8/15)-X : ℚ[X]) :=
            (Scaled.rep_const (8/15)).sub Scaled.rep_var
          apply h_withMasses (onCurve X (C (8/15)-X)) (mass .TE 0 0) (mass .TE 0 1) (mass .TE 0 2)
            (mass .TE 0 3)
          case h0 =>
            simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
            exact hall.1
          case h1 =>
            simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
            exact hall.2.1
          case h2 =>
            simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
            exact hall.2.2.1
          case h3 =>
            simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
            exact hall.2.2.2.1
          case h =>
            intro hw0 hw1 hw2 hw3
            simp only [NegativeA.LongE.Certificate.numerator]
            h_longe_unfold
            build_rep_curve
            all_goals assumption
        case hB =>
          apply h_withMasses (yZero) (mass .TE 0 0) (mass .TE 0 1) (mass .TE 0 2) (mass .TE 0 3)
          case h0 =>
            simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
            exact hall.2.2.2.2.1
            exact hall.2.2.2.2.2.1
          case h1 =>
            simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
            exact hall.2.2.2.2.2.2.1
            exact hall.2.2.2.2.2.2.2.1
          case h2 =>
            simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
            exact hall.2.2.2.2.2.2.2.2.1
            exact hall.2.2.2.2.2.2.2.2.2.1
          case h3 =>
            simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
            exact hall.2.2.2.2.2.2.2.2.2.2.1
            exact hall.2.2.2.2.2.2.2.2.2.2.2.1
          case h =>
            intro hw0 hw1 hw2 hw3
            simp only [NegativeA.LongE.Certificate.numerator]
            h_longe_unfold
            build_rep_yZero
            all_goals assumption
  case hP => set_option synthInstance.maxSize 1024 in decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem TC_certificate (i : Fin 3) :
    transform .TC (numerator .TC i)=expansion 39 (transform .TC (numerator .TC i)) ∧
    TCreserve i<lowerOn .TC 39 (numerator .TC i) := by
  open PackedModels BivariateCertificate in
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
    (13/10000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (19/50) (REboundary 0 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (19/50) 19 100 (by norm_num) (by norm_num) 35 (13/10000:ℚ) 13 10000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      rw [show REboundary 0 0=xZero (numerator .RE 0) from baseX_eq_xZero _]
      change RepOn xZero _ _
      apply h_withMasses (xZero) (mass .RE 0 0) (mass .RE 0 1) (mass .RE 0 2) (mass .RE 0 3)
      case h0 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (37/2500:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (16/75) (REboundary 0 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (16/75) 8 75 (by norm_num) (by norm_num) 35 (37/2500:ℚ) 37 2500
      (by norm_num) (by norm_num) hall.2.2.2.2
    case ha =>
      rw [show REboundary 0 1=onCurve (C (1/6)) X (numerator .RE 0) from rfl]
      have hU : (Scaled.const (1/6)).Rep (C (1/6) : ℚ[X]) := Scaled.rep_const (1/6)
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve (C (1/6)) X) (mass .RE 0 0) (mass .RE 0 1) (mass .RE 0 2)
        (mass .RE 0 3)
      case h0 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (67/2500:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (REboundary 0 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (67/2500:ℚ) 67 2500
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
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (13/10000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (19/50) (REboundary 1 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (19/50) 19 100 (by norm_num) (by norm_num) 35 (13/10000:ℚ) 13 10000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      rw [show REboundary 1 0=xZero (numerator .RE 1) from baseX_eq_xZero _]
      change RepOn xZero _ _
      apply h_withMasses (xZero) (mass .RE 1 0) (mass .RE 1 1) (mass .RE 1 2) (mass .RE 1 3)
      case h0 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (37/2500:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (16/75) (REboundary 1 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (16/75) 8 75 (by norm_num) (by norm_num) 35 (37/2500:ℚ) 37 2500
      (by norm_num) (by norm_num) hall.2.2.2.2
    case ha =>
      rw [show REboundary 1 1=onCurve (C (1/6)) X (numerator .RE 1) from rfl]
      have hU : (Scaled.const (1/6)).Rep (C (1/6) : ℚ[X]) := Scaled.rep_const (1/6)
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve (C (1/6)) X) (mass .RE 1 0) (mass .RE 1 1) (mass .RE 1 2)
        (mass .RE 1 3)
      case h0 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (67/2500:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (REboundary 1 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (67/2500:ℚ) 67 2500
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
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (1587/5000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (19/50) (REboundary 2 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (19/50) 19 100 (by norm_num) (by norm_num) 35 (1587/5000:ℚ) 1587 5000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      rw [show REboundary 2 0=xZero (numerator .RE 2) from baseX_eq_xZero _]
      change RepOn xZero _ _
      apply h_withMasses (xZero) (mass .RE 2 0) (mass .RE 2 1) (mass .RE 2 2) (mass .RE 2 3)
      case h0 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (37/2500:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (16/75) (REboundary 2 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (16/75) 8 75 (by norm_num) (by norm_num) 35 (37/2500:ℚ) 37 2500
      (by norm_num) (by norm_num) hall.2.2.2.2
    case ha =>
      rw [show REboundary 2 1=onCurve (C (1/6)) X (numerator .RE 2) from rfl]
      have hU : (Scaled.const (1/6)).Rep (C (1/6) : ℚ[X]) := Scaled.rep_const (1/6)
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve (C (1/6)) X) (mass .RE 2 0) (mass .RE 2 1) (mass .RE 2 2)
        (mass .RE 2 3)
      case h0 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (13/500:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (REboundary 2 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (13/500:ℚ) 13 500
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
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_curve
        exact hall.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (11/500:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (11/500:ℚ) 11 500
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [RCbase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .RC 0)
      apply h_withMasses (yZero) (mass .RC 0 0) (mass .RC 0 1) (mass .RC 0 2) (mass .RC 0 3)
      case h0 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (11/500:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (11/500:ℚ) 11 500
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [RCbase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .RC 1)
      apply h_withMasses (yZero) (mass .RC 1 0) (mass .RC 1 1) (mass .RC 1 2) (mass .RC 1 3)
      case h0 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
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
    (21/1000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (1/6) 1 12 (by norm_num) (by norm_num) 35 (21/1000:ℚ) 21 1000
      (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [RCbase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .RC 2)
      apply h_withMasses (yZero) (mass .RC 2 0) (mass .RC 2 1) (mass .RC 2 2) (mass .RC 2 3)
      case h0 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NegativeA.LongE.Certificate.mass]; h_longe_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NegativeA.LongE.Certificate.numerator]
        h_longe_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem RCbase_certificate (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 (1/6) (RCbase i)=
      WholeIntervalPolynomial.expansion 35 (WholeIntervalPolynomial.centered 0 (1/6) (RCbase i)) ∧
    RCbaseReserve i<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase i) := by
  fin_cases i
  · exact h_RCbase_0
  · exact h_RCbase_1
  · exact h_RCbase_2

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE.Certificate
