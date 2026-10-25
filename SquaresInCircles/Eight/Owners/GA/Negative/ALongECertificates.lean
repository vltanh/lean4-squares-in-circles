module

public import SquaresInCircles.Eight.Owners.GA.Negative.ALongEData
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsCertificates

/-!
# Eight squares: the twelve longer-E numerator certificates

Each numerator has an exact packed model (`BivariateCertificates`). One kernel evaluation per
numerator checks its bivariate bound together with the univariate bounds on its edges, which are
read off the same model. The TE base is identified with the earlier pure-T base; the RE trapezoid
uses its three actual boundary curves and its whole-domain second derivative.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.LongE.Certificate
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

/-- Mirror of `A r i`. -/
def h_AM (cfg : Config) (r : Region) (i : Fin 3) : XM :=
  XM.add cfg (h_ABaseM cfg r)
    (XM.mul cfg (![XM.ofInt cfg 1 1,h_lM cfg r,h_qBM cfg r] i)
      (XM.sub cfg (XM.liftM cfg (h_deltaM cfg r) XM.C10L) (XM.ofInt cfg 1 1)))

theorem h_rep_AM (cfg : Config) (r : Region) (i : Fin 3) : (h_AM cfg r i).Rep cfg (A r i) := by
  have h1 : (![XM.ofInt cfg 1 1,h_lM cfg r,h_qBM cfg r] i).Rep cfg (![1,l r,qB r] i) := by
    fin_cases i
    · exact XM.rep_one cfg
    · exact h_rep_lM cfg r
    · exact h_rep_qBM cfg r
  exact XM.rep_add (h_rep_ABaseM cfg r)
    (XM.rep_mul h1 (XM.rep_sub (XM.rep_liftC10 (h_rep_deltaM cfg r)) (XM.rep_one cfg)))

/-- Mirror of `baseNorm r`. -/
def h_baseNormM (cfg : Config) (r : Region) : Fin 4 → XM :=
  ![XM.add cfg (XM.ofInt cfg 1 1) (XM.pow cfg (h_kM cfg r) 2),
    XM.add cfg (XM.pow cfg (h_kM cfg r) 2) (XM.pow cfg (h_lM cfg r) 2),
    XM.add cfg (XM.pow cfg (h_lM cfg r) 2) (XM.pow cfg (h_MM cfg r) 2),
    XM.add cfg (XM.ofInt cfg 1 1) (XM.pow cfg (h_cM cfg r) 2)]

/-- Mirror of `P r i j`. -/
def h_PM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  XM.sub cfg (h_baseNormM cfg r j)
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

/-- Mirror of `numerator r i`. -/
def h_numM (cfg : Config) (r : Region) (i : Fin 3) : XM :=
  let w := h_massM cfg r i
  XM.sub cfg
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
  exact XM.rep_sub (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_mul
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

/-! ### Edges of exact models

The restriction of the polynomial of a model to `y = 0` or to `x = 0` is read off its digits as a
scaled list (`h_colS`, `h_rowS`), so that the univariate certificates of
`CertificateRestrictions` apply to it; the other edges are first moved onto these lines by
`XM.substX` and `XM.substY`. -/

section Restrictions
open PackedModels BivariateCertificate WholeIntervalPolynomial.Certificate

/-- The digit `k` of the numerator `U - V` of a model, as an integer. -/
private def h_digitZ (c : Config) (m : XM) (k : ℕ) : ℤ :=
  (((m.U >>> (c.w * k)) &&& (2 ^ c.w - 1) : ℕ) : ℤ) -
    (((m.V >>> (c.w * k)) &&& (2 ^ c.w - 1) : ℕ) : ℤ)

private theorem h_digitZ_eq (c : Config) (m : XM) (i j : ℕ) :
    h_digitZ c m (c.S * i + j) =
      (PackedModels.coeffs c m.U i j : ℤ) - PackedModels.coeffs c m.V i j := by
  simp only [h_digitZ, PackedModels.coeffs, PackedModels.digit, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, pow_mul]

private theorem h_digitZ_eq0 (c : Config) (m : XM) (j : ℕ) :
    h_digitZ c m j = (PackedModels.coeffs c m.U 0 j : ℤ) - PackedModels.coeffs c m.V 0 j := by
  simpa using h_digitZ_eq c m 0 j

/-- The restriction to `y = 0` of the polynomial of a model, as a scaled list. -/
private def h_colS (c : Config) (m : XM) : Scaled :=
  ⟨(List.range (m.dx + 1)).map (fun i => h_digitZ c m (c.S * i)), m.s⟩

/-- The restriction to `x = 0` of the polynomial of a model, as a scaled list. -/
private def h_rowS (c : Config) (m : XM) : Scaled :=
  ⟨(List.range (m.dy + 1)).map (fun j => h_digitZ c m j), m.s⟩

private theorem h_getD_range_map (f : ℕ → ℤ) (n k : ℕ) :
    ((List.range n).map f).getD k 0 = if k < n then f k else 0 := by
  by_cases h : k < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

private theorem h_rep_colS {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p)
    (hok : m.ok = true) : (h_colS c m).Rep (yZero p) := by
  obtain ⟨g, v⟩ := hm hok
  have hS := g.dxS
  have hS0 := c.S_pos
  unfold Scaled.Rep
  ext n
  rw [coeff_toPoly, coeff_C_mul, yZero_coeff]
  have hv := congrArg (fun q : Bivar => (q.coeff n).coeff 0) v
  simp only [XM.coeff_scalar_mul] at hv
  rw [XM.coeff_val g] at hv
  simp only [h_colS, h_getD_range_map]
  by_cases h1 : n < m.dx + 1
  · rw [ite_eq_left h1, ← hv, ite_eq_left ⟨by omega, hS0⟩,
      show c.S * n = c.S * n + 0 from rfl, h_digitZ_eq]
    push_cast; rfl
  · rw [ite_eq_right h1]
    by_cases h2 : n < c.S
    · rw [ite_eq_left ⟨h2, hS0⟩] at hv
      have hU : PackedModels.coeffs c m.U n 0 = 0 := by
        by_contra hne
        have := g.suppU n 0 (by rw [cf_poly, ite_eq_left ⟨h2, hS0⟩]; exact hne)
        omega
      have hV : PackedModels.coeffs c m.V n 0 = 0 := by
        by_contra hne
        have := g.suppV n 0 (by rw [cf_poly, ite_eq_left ⟨h2, hS0⟩]; exact hne)
        omega
      rw [← hv, hU, hV]; simp
    · rw [ite_eq_right (fun h => h2 h.1)] at hv
      rw [← hv]; simp

private theorem h_rep_rowS {c : Config} {m : XM} {p : Bivar} (hm : m.Rep c p)
    (hok : m.ok = true) : (h_rowS c m).Rep (xZero p) := by
  obtain ⟨g, v⟩ := hm hok
  have hS := g.dyS
  have hS0 := c.S_pos
  unfold Scaled.Rep
  ext n
  rw [coeff_toPoly, coeff_C_mul, xZero_coeff]
  have hv := congrArg (fun q : Bivar => (q.coeff 0).coeff n) v
  simp only [XM.coeff_scalar_mul] at hv
  rw [XM.coeff_val g] at hv
  simp only [h_rowS, h_getD_range_map]
  by_cases h1 : n < m.dy + 1
  · rw [ite_eq_left h1, ← hv, ite_eq_left ⟨hS0, by omega⟩, h_digitZ_eq0]
    push_cast; rfl
  · rw [ite_eq_right h1]
    by_cases h2 : n < c.S
    · rw [ite_eq_left ⟨hS0, h2⟩] at hv
      have hU : PackedModels.coeffs c m.U 0 n = 0 := by
        by_contra hne
        have := g.suppU 0 n (by rw [cf_poly, ite_eq_left ⟨hS0, h2⟩]; exact hne)
        omega
      have hV : PackedModels.coeffs c m.V 0 n = 0 := by
        by_contra hne
        have := g.suppV 0 n (by rw [cf_poly, ite_eq_left ⟨hS0, h2⟩]; exact hne)
        omega
      rw [← hv, hU, hV]; simp
    · rw [ite_eq_right (fun h => h2 h.2)] at hv
      rw [← hv]; simp

/-- `y = 0` after `y ↦ G` is the curve `(x, G(x, 0))`. -/
private theorem h_yZero_substitute (G N : Bivar) :
    yZero (substitute X G N) = restrict N X (yZero G) := by
  rw [restrict_eq_onCurve]
  have h : yZero.comp (substitute X G) = onCurve X (yZero G) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, substitute, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        hom_lift yZero yZero_C, onCurve]
      rfl
    · simp [substitute, onCurve, yZero_X]
  exact congrArg (fun F : Bivar →+* ℚ[X] => F N) h

/-- `x = 0` after `x ↦ F` is the curve `(F(0, y), y)`. -/
private theorem h_xZero_substitute (F N : Bivar) :
    xZero (substitute F (C X) N) = restrict N (xZero F) X := by
  rw [restrict_eq_onCurve]
  have h : xZero.comp (substitute F (C X)) = onCurve (xZero F) X := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, substitute, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        hom_lift xZero xZero_C, xZero_CX, onCurve]
      simp
    · simp [substitute, onCurve]
  exact congrArg (fun F : Bivar →+* ℚ[X] => F N) h

/-- The curve `(x, v(x))` of a model, through `y ↦ F / q`. -/
private theorem h_rep_substY {c : Config} {m : XM} {N : Bivar} (hm : m.Rep c N)
    {F : List (ℤ × ℕ × ℕ)} (hF : F ≠ []) (q : ℕ) {v : ℚ[X]}
    (hv : yZero (scalar (1 / (q : ℚ)) * XM.polyF F) = v) (hok : (XM.substY c m F q).ok = true) :
    (h_colS c (XM.substY c m F q)).Rep (restrict N X v) := by
  have h := h_rep_colS (XM.rep_substY hm hF q) hok
  rwa [h_yZero_substitute, hv] at h

/-- The curve `(u(y), y)` of a model, through `x ↦ F / q`. -/
private theorem h_rep_substX {c : Config} {m : XM} {N : Bivar} (hm : m.Rep c N)
    {F : List (ℤ × ℕ × ℕ)} (hF : F ≠ []) (q : ℕ) {u : ℚ[X]}
    (hu : xZero (scalar (1 / (q : ℚ)) * XM.polyF F) = u) (hok : (XM.substX c m F q).ok = true) :
    (h_rowS c (XM.substX c m F q)).Rep (restrict N u X) := by
  have h := h_rep_rowS (XM.rep_substX hm hF q) hok
  rwa [h_xZero_substitute, hu] at h

/-- The integer facts of `lower_cert` on `[0, 2 num/den]`, for the reserve `n / dd`. -/
private abbrev h_lowerOK (a : Scaled) (num den D : ℕ) (n : ℤ) (dd : ℕ) : Prop :=
  ((a.center num den 1 1).s≠0 ∧ (a.center num den 1 1).l.length≤D+1) ∧
    n*(((a.center num den 1 1).s*2^(a.center num den 1 1).l.length:ℕ):ℤ)<
      2*dd*lowerZ D (fun j => (chebList (a.center num den 1 1).l).getD j 0)

end Restrictions

section Checks
open PackedModels BivariateCertificate WholeIntervalPolynomial.Certificate

/-- Packing for the cubic masses: total degree up to `30`, digits of `1100` bits. -/
def h_cfgMass : Config := ⟨0,16,1100⟩
/-- Packing for the triangle numerators: degrees up to `39`, digits of `2500` bits. -/
def h_cfgT : Config := ⟨0,20,2500⟩
/-- Packing for the trapezoid numerators: degrees up to `35`, digits of `2400` bits. -/
def h_cfgR : Config := ⟨0,18,2400⟩

/-! Each check is one kernel evaluation of exact models. The bivariate bound of a numerator and
the univariate bounds on its edges share one evaluation, which builds the model of the numerator
once. -/

/-- The reserves as numerators and denominators. -/
def h_massResP : Region → ℤ × ℕ
  | .TE => (71,100) | .TC => (107,100) | .RE => (11,10) | .RC => (103,100)
def h_TEdR : Fin 3 → ℤ × ℕ := ![(-67,100),(-51,100),(-11,25)]
def h_TCR : Fin 3 → ℤ × ℕ := ![(3,125),(43,1000),(153,500)]
def h_REcR : Fin 3 → ℤ × ℕ := ![(-7,1),(-7,1),(-11,1)]
def h_RCqR : Fin 3 → ℤ × ℕ := ![(9,10),(123,100),(91,25)]

/-- The far edge `y = 8/15 - x` of the quotient by `y` of the TE numerator `i`. -/
private def h_TEfarM (i : Fin 3) : XM :=
  XM.substY h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE i)) [(8,0,0),(-15,1,0)] 15
/-- The edge `x = 1/6` of the RE numerator `i`. -/
private def h_REmidM (i : Fin 3) : XM := XM.substX h_cfgR (h_numM h_cfgR .RE i) [(1,0,0)] 6
/-- The edge `y = 19/50 - x` of the RE numerator `i`. -/
private def h_REfarM (i : Fin 3) : XM :=
  XM.substY h_cfgR (h_numM h_cfgR .RE i) [(19,0,0),(-50,1,0)] 50

/-- The integer facts of `quadratic_tail_cert` for the ratio `rn / rd` and the reserves `κn / κd`,
`ρn / ρd`. -/
private abbrev h_quadOK (a : Scaled) (N : ℕ) (rn : ℤ) (rd : ℕ) (κn : ℤ) (κd : ℕ) (ρn : ℤ)
    (ρd : ℕ) : Prop :=
  (a.s≠0 ∧ a.l.length≤N+3) ∧
    0<a.l.getD 2 0*(rd:ℤ)^N-tailZ a.l rn rd N ∧
    κn*((a.s:ℤ)*(rd:ℤ)^N)<κd*(a.l.getD 2 0*(rd:ℤ)^N-tailZ a.l rn rd N) ∧
    ρn*(4*(a.l.getD 2 0*(rd:ℤ)^N-tailZ a.l rn rd N)*a.s)<
      ρd*(4*(a.l.getD 2 0*(rd:ℤ)^N-tailZ a.l rn rd N)*a.l.getD 0 0-a.l.getD 1 0^2*(rd:ℤ)^N)

/-- The checks of the four cubic masses of the numerator `i` of `r`, for the reserve `n / d`. -/
private abbrev h_massOK (cfg : Config) (r : Region) (i : Fin 3) (n : ℤ) (d : ℕ) : Prop :=
  XM.lowerCheck cfg (h_transformM cfg r (h_massM cfg r i 0)) 3 n d=true ∧
  XM.lowerCheck cfg (h_transformM cfg r (h_massM cfg r i 1)) 3 n d=true ∧
  XM.lowerCheck cfg (h_transformM cfg r (h_massM cfg r i 2)) 3 n d=true ∧
  XM.lowerCheck cfg (h_transformM cfg r (h_massM cfg r i 3)) 3 n d=true

set_option Elab.async false in
/-- The TE numerator `0`: its cubic masses, the `y`-derivative of its quotient by `y` on the triangle, and the
quadratic minorant of the far edge of the quotient around `x = 4/15`. -/
private theorem h_TECheck_0 :
    h_massOK h_cfgT .TE 0 71 100 ∧ XM.upperCheck h_cfgT (h_transformM h_cfgT .TE
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 0)))) 39 (-67) 100=true ∧
    (h_TEfarM 0).ok=true ∧
    h_quadOK ((h_colS h_cfgT (h_TEfarM 0)).center 1 15 4 15) 37 4 15 133 100 47 1000 := by
  decide +kernel

set_option Elab.async false in
/-- The TE numerator `1`: its cubic masses, the `y`-derivative of its quotient on the triangle and its far edge. -/
private theorem h_TECheck_1 :
    h_massOK h_cfgT .TE 1 71 100 ∧ XM.upperCheck h_cfgT (h_transformM h_cfgT .TE
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 1)))) 39 (-51) 100=true ∧
    (h_TEfarM 1).ok=true ∧ h_lowerOK (h_colS h_cfgT (h_TEfarM 1)) 4 15 39 13 200 := by
  decide +kernel

set_option Elab.async false in
/-- The TE numerator `2`: its cubic masses, the `y`-derivative of its quotient on the triangle and its far edge. -/
private theorem h_TECheck_2 :
    h_massOK h_cfgT .TE 2 71 100 ∧ XM.upperCheck h_cfgT (h_transformM h_cfgT .TE
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 2)))) 39 (-11) 25=true ∧
    (h_TEfarM 2).ok=true ∧ h_lowerOK (h_colS h_cfgT (h_TEfarM 2)) 4 15 39 11 500 := by
  decide +kernel

set_option Elab.async false in
/-- The TC numerator `0`: its cubic masses and its bound on the triangle. -/
private theorem h_TCCheck_0 :
    h_massOK h_cfgT .TC 0 107 100 ∧ XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (h_numM h_cfgT .TC 0)))
      39 3 125=true := by
  decide +kernel

set_option Elab.async false in
/-- The TC numerator `1`: its cubic masses and its bound on the triangle. -/
private theorem h_TCCheck_1 :
    h_massOK h_cfgT .TC 1 107 100 ∧ XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (h_numM h_cfgT .TC 1)))
      39 43 1000=true := by
  decide +kernel

set_option Elab.async false in
/-- The TC numerator `2`: its cubic masses and its bound on the triangle. -/
private theorem h_TCCheck_2 :
    h_massOK h_cfgT .TC 2 107 100 ∧ XM.lowerCheck h_cfgT (h_transformM h_cfgT .TC (h_numM h_cfgT .TC 2)) 39 153 500=true := by
  decide +kernel

set_option Elab.async false in
/-- The RE numerator `0`: its cubic masses, its second `x`-derivative on the trapezoid and its three
edges. -/
private theorem h_RECheck_0 :
    h_massOK h_cfgR .RE 0 11 10 ∧ XM.upperCheck h_cfgR (h_transformM h_cfgR .RE
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 0)))) 35 (-7) 1=true ∧
    (h_numM h_cfgR .RE 0).ok=true ∧
    h_lowerOK (h_rowS h_cfgR (h_numM h_cfgR .RE 0)) 19 100 35 13 10000 ∧
    (h_REmidM 0).ok=true ∧ h_lowerOK (h_rowS h_cfgR (h_REmidM 0)) 8 75 35 37 2500 ∧
    (h_REfarM 0).ok=true ∧ h_lowerOK (h_colS h_cfgR (h_REfarM 0)) 1 12 35 67 2500 := by
  decide +kernel

set_option Elab.async false in
/-- The RE numerator `1`: its cubic masses, its second `x`-derivative on the trapezoid and its three
edges. -/
private theorem h_RECheck_1 :
    h_massOK h_cfgR .RE 1 11 10 ∧ XM.upperCheck h_cfgR (h_transformM h_cfgR .RE
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 1)))) 35 (-7) 1=true ∧
    (h_numM h_cfgR .RE 1).ok=true ∧
    h_lowerOK (h_rowS h_cfgR (h_numM h_cfgR .RE 1)) 19 100 35 13 10000 ∧
    (h_REmidM 1).ok=true ∧ h_lowerOK (h_rowS h_cfgR (h_REmidM 1)) 8 75 35 37 2500 ∧
    (h_REfarM 1).ok=true ∧ h_lowerOK (h_colS h_cfgR (h_REfarM 1)) 1 12 35 67 2500 := by
  decide +kernel

set_option Elab.async false in
/-- The RE numerator `2`: its cubic masses, its second `x`-derivative on the trapezoid and its three
edges. -/
private theorem h_RECheck_2 :
    h_massOK h_cfgR .RE 2 11 10 ∧ XM.upperCheck h_cfgR (h_transformM h_cfgR .RE
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 2)))) 35 (-11) 1=true ∧
    (h_numM h_cfgR .RE 2).ok=true ∧
    h_lowerOK (h_rowS h_cfgR (h_numM h_cfgR .RE 2)) 19 100 35 1587 5000 ∧
    (h_REmidM 2).ok=true ∧ h_lowerOK (h_rowS h_cfgR (h_REmidM 2)) 8 75 35 37 2500 ∧
    (h_REfarM 2).ok=true ∧ h_lowerOK (h_colS h_cfgR (h_REfarM 2)) 1 12 35 13 500 := by
  decide +kernel

set_option Elab.async false in
/-- The RC numerator `0`: its cubic masses, its quotient by `y` on the trapezoid and its edge
`y = 0`. -/
private theorem h_RCCheck_0 :
    h_massOK h_cfgR .RC 0 103 100 ∧ XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 0)))) 35 9 10=true ∧
    (h_numM h_cfgR .RC 0).ok=true ∧ h_lowerOK (h_colS h_cfgR (h_numM h_cfgR .RC 0)) 1 12 35 11 500 := by
  decide +kernel

set_option Elab.async false in
/-- The RC numerator `1`: its cubic masses, its quotient by `y` on the trapezoid and its edge
`y = 0`. -/
private theorem h_RCCheck_1 :
    h_massOK h_cfgR .RC 1 103 100 ∧ XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 1)))) 35 123 100=true ∧
    (h_numM h_cfgR .RC 1).ok=true ∧ h_lowerOK (h_colS h_cfgR (h_numM h_cfgR .RC 1)) 1 12 35 11 500 := by
  decide +kernel

set_option Elab.async false in
/-- The RC numerator `2`: its cubic masses, its quotient by `y` on the trapezoid and its edge
`y = 0`. -/
private theorem h_RCCheck_2 :
    h_massOK h_cfgR .RC 2 103 100 ∧ XM.lowerCheck h_cfgR (h_transformM h_cfgR .RC (XM.divYM h_cfgR (h_numM h_cfgR .RC 2)))
      35 91 25=true ∧
    (h_numM h_cfgR .RC 2).ok=true ∧ h_lowerOK (h_colS h_cfgR (h_numM h_cfgR .RC 2)) 1 12 35 21 1000 := by
  decide +kernel

/-- The far edge of the TE quotient `i`, read off its model. -/
private theorem h_rep_TEfar (i : Fin 3) (hok : (h_TEfarM i).ok=true) :
    (h_colS h_cfgT (h_TEfarM i)).Rep (TEfar i) :=
  h_rep_substY (XM.rep_divYM (h_rep_numM h_cfgT .TE i)) (by simp) 15
    (by apply Polynomial.funext; intro x; simp [XM.polyF, scalar, yZero_C, yZero_X]; ring) hok

end Checks


/-- The mass certificates of the numerator `i` of `r`, from the checks of its masses. -/
private theorem h_mass_of {cfg : PackedModels.Config} {r : Region} {i : Fin 3} {n : ℤ} {d : ℕ}
    (h : h_massOK cfg r i n d) (hq : massReserve r=n/d) (j : Fin 4) :
    transform r (mass r i j)=expansion 3 (transform r (mass r i j)) ∧
    massReserve r<lowerOn r 3 (mass r i j) := by
  open PackedModels BivariateCertificate in
  have hj : XM.lowerCheck cfg (h_transformM cfg r (h_massM cfg r i j)) 3 n d=true := by
    fin_cases j
    exacts [h.1,h.2.1,h.2.2.1,h.2.2.2]
  exact XM.lower_certificate (h_rep_transformM (h_rep_massM cfg r i j) r) hj hq

theorem mass_certificate (r : Region) (i : Fin 3) (j : Fin 4) :
    transform r (mass r i j)=expansion 3 (transform r (mass r i j)) ∧
    massReserve r<lowerOn r 3 (mass r i j) := by
  cases r <;> fin_cases i
  · exact h_mass_of h_TECheck_0.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_TECheck_1.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_TECheck_2.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_TCCheck_0.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_TCCheck_1.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_TCCheck_2.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_RECheck_0.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_RECheck_1.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_RECheck_2.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_RCCheck_0.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_RCCheck_1.1 (by norm_num [massReserve]) j
  · exact h_mass_of h_RCCheck_2.1 (by norm_num [massReserve]) j

theorem TEderivative_certificate (i : Fin 3) :
    transform .TE (derivativeY (TEquotient i))=
      expansion 39 (transform .TE (derivativeY (TEquotient i))) ∧
    upperOn .TE 39 (derivativeY (TEquotient i))<TEderivativeReserve i := by
  open PackedModels BivariateCertificate in
  have h : XM.upperCheck h_cfgT (h_transformM h_cfgT .TE
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE i)))) 39 (h_TEdR i).1 (h_TEdR i).2=
      true := by
    fin_cases i
    · exact h_TECheck_0.2.1
    · exact h_TECheck_1.2.1
    · exact h_TECheck_2.2.1
  exact XM.upper_certificate
    (h_rep_transformM (XM.rep_derivYM (XM.rep_divYM (h_rep_numM h_cfgT .TE i))) .TE) h
    (by fin_cases i <;> norm_num [TEderivativeReserve,h_TEdR])

theorem TEfar_GB_certificate (i : Fin 3) (hi : i=1∨i=2) :
    WholeIntervalPolynomial.centered 0 (8/15) (TEfar i)=
      WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 (8/15) (TEfar i)) ∧
    TEfarReserve i<WholeIntervalPolynomial.lowerOn 39 0 (8/15) (TEfar i) := by
  rcases hi with rfl|rfl
  · exact lower_cert (h_rep_TEfar 1 h_TECheck_1.2.2.1) (8/15) 4 15 (by norm_num) (by norm_num) 39
      _ 13 200 (by norm_num [TEfarReserve]) (by norm_num) h_TECheck_1.2.2.2
  · exact lower_cert (h_rep_TEfar 2 h_TECheck_2.2.2.1) (8/15) 4 15 (by norm_num) (by norm_num) 39
      _ 11 500 (by norm_num [TEfarReserve]) (by norm_num) h_TECheck_2.2.2.2

theorem TEfar_H_certificate :
    TEcentered=C (TEcoefficient 0)+C (TEcoefficient 1)*X+C (TEcoefficient 2)*X^2+
      ∑j : Fin 37,C (TEcoefficient (j.val+3))*X^(j.val+3) ∧
    (133/100:ℚ)<TEcurvature ∧
    (47/1000:ℚ)<TEcoefficient 0-(TEcoefficient 1)^2/(4*TEcurvature) := by
  have ha := rep_comp_shift (h_rep_TEfar 0 h_TECheck_0.2.2.1) 1 15 4 15 (4/15) (by norm_num)
    (by norm_num) (by norm_num)
  rw [show (TEfar 0).comp (C (4/15)+X)=TEcentered by rw [TEcentered,add_comm]] at ha
  exact quadratic_tail_cert ha 37 (4/15) 4 15 (by norm_num) (by norm_num) (133/100) 133 100
    (by norm_num) (by norm_num) (47/1000) 47 1000 (by norm_num) (by norm_num) h_TECheck_0.2.2.2

theorem TC_certificate (i : Fin 3) :
    transform .TC (numerator .TC i)=expansion 39 (transform .TC (numerator .TC i)) ∧
    TCreserve i<lowerOn .TC 39 (numerator .TC i) := by
  open PackedModels BivariateCertificate in
  fin_cases i
  · exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM (h_rep_numM h_cfgT .TC 0) .TC))
      h_TCCheck_0.2 (by norm_num [TCreserve])
  · exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM (h_rep_numM h_cfgT .TC 1) .TC))
      h_TCCheck_1.2 (by norm_num [TCreserve])
  · exact XM.lower_certificate (h_rep_transformM (h_rep_numM h_cfgT .TC 2) .TC)
      h_TCCheck_2.2 (by norm_num [TCreserve])

theorem REcurvature_certificate (i : Fin 3) :
    transform .RE (numerator .RE i).derivative.derivative=
      expansion 35 (transform .RE (numerator .RE i).derivative.derivative) ∧
    upperOn .RE 35 (numerator .RE i).derivative.derivative<REcurvatureReserve i := by
  open PackedModels BivariateCertificate in
  have h : XM.upperCheck h_cfgR (h_transformM h_cfgR .RE
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE i)))) 35 (h_REcR i).1
      (h_REcR i).2=true := by
    fin_cases i
    · exact h_RECheck_0.2.1
    · exact h_RECheck_1.2.1
    · exact h_RECheck_2.2.1
  exact XM.upper_certificate
    (h_rep_transformM (XM.rep_derivXM (XM.rep_derivXM (h_rep_numM h_cfgR .RE i))) .RE) h
    (by fin_cases i <;> norm_num [REcurvatureReserve,h_REcR])

/-- The three edges of the RE numerator `i`, read off its model. -/
private theorem h_rep_REboundary (i : Fin 3) (h0 : (h_numM h_cfgR .RE i).ok=true)
    (h1 : (h_REmidM i).ok=true) (h2 : (h_REfarM i).ok=true) :
    (h_rowS h_cfgR (h_numM h_cfgR .RE i)).Rep (REboundary i 0) ∧
    (h_rowS h_cfgR (h_REmidM i)).Rep (REboundary i 1) ∧
    (h_colS h_cfgR (h_REfarM i)).Rep (REboundary i 2) := by
  open PackedModels BivariateCertificate in
  refine ⟨?_,h_rep_substX (h_rep_numM h_cfgR .RE i) (by simp) 6
    (by simp [XM.polyF, scalar, xZero_C]) h1,
    h_rep_substY (h_rep_numM h_cfgR .RE i) (by simp) 50
    (by apply Polynomial.funext; intro x; simp [XM.polyF, scalar, yZero_C, yZero_X]; ring) h2⟩
  rw [show REboundary i 0=xZero (numerator .RE i) from baseX_eq_xZero _]
  exact h_rep_rowS (h_rep_numM h_cfgR .RE i) h0

theorem REboundary_certificate (i j : Fin 3) :
    WholeIntervalPolynomial.centered 0 (RElength j) (REboundary i j)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (RElength j) (REboundary i j)) ∧
    REreserve i j<WholeIntervalPolynomial.lowerOn 35 0 (RElength j) (REboundary i j) := by
  fin_cases i
  · obtain ⟨-,-,h0,c0,h1,c1,h2,c2⟩ := h_RECheck_0
    obtain ⟨r0,r1,r2⟩ := h_rep_REboundary 0 h0 h1 h2
    fin_cases j
    · exact lower_cert r0 (19/50) 19 100 (by norm_num) (by norm_num) 35 _ 13 10000
        (by norm_num [REreserve]) (by norm_num) c0
    · exact lower_cert r1 (16/75) 8 75 (by norm_num) (by norm_num) 35 _ 37 2500
        (by norm_num [REreserve]) (by norm_num) c1
    · exact lower_cert r2 (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 67 2500
        (by norm_num [REreserve]) (by norm_num) c2
  · obtain ⟨-,-,h0,c0,h1,c1,h2,c2⟩ := h_RECheck_1
    obtain ⟨r0,r1,r2⟩ := h_rep_REboundary 1 h0 h1 h2
    fin_cases j
    · exact lower_cert r0 (19/50) 19 100 (by norm_num) (by norm_num) 35 _ 13 10000
        (by norm_num [REreserve]) (by norm_num) c0
    · exact lower_cert r1 (16/75) 8 75 (by norm_num) (by norm_num) 35 _ 37 2500
        (by norm_num [REreserve]) (by norm_num) c1
    · exact lower_cert r2 (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 67 2500
        (by norm_num [REreserve]) (by norm_num) c2
  · obtain ⟨-,-,h0,c0,h1,c1,h2,c2⟩ := h_RECheck_2
    obtain ⟨r0,r1,r2⟩ := h_rep_REboundary 2 h0 h1 h2
    fin_cases j
    · exact lower_cert r0 (19/50) 19 100 (by norm_num) (by norm_num) 35 _ 1587 5000
        (by norm_num [REreserve]) (by norm_num) c0
    · exact lower_cert r1 (16/75) 8 75 (by norm_num) (by norm_num) 35 _ 37 2500
        (by norm_num [REreserve]) (by norm_num) c1
    · exact lower_cert r2 (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 13 500
        (by norm_num [REreserve]) (by norm_num) c2

theorem RCquotient_certificate (i : Fin 3) :
    transform .RC (RCquotient i)=expansion 35 (transform .RC (RCquotient i)) ∧
    RCquotientReserve i<lowerOn .RC 35 (RCquotient i) := by
  open PackedModels BivariateCertificate in
  have hq := XM.rep_divYM (h_rep_numM h_cfgR .RC i)
  fin_cases i
  · exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM hq .RC)) h_RCCheck_0.2.1
      (by norm_num [RCquotientReserve])
  · exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM hq .RC)) h_RCCheck_1.2.1
      (by norm_num [RCquotientReserve])
  · exact XM.lower_certificate (h_rep_transformM hq .RC) h_RCCheck_2.2.1
      (by norm_num [RCquotientReserve])

theorem RCbase_certificate (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 (1/6) (RCbase i)=
      WholeIntervalPolynomial.expansion 35 (WholeIntervalPolynomial.centered 0 (1/6) (RCbase i)) ∧
    RCbaseReserve i<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase i) := by
  have hr (i : Fin 3) (h : (h_numM h_cfgR .RC i).ok=true) :
      (h_colS h_cfgR (h_numM h_cfgR .RC i)).Rep (RCbase i) := by
    rw [RCbase,baseY_eq_yZero]; exact h_rep_colS (h_rep_numM h_cfgR .RC i) h
  fin_cases i
  · exact lower_cert (hr 0 h_RCCheck_0.2.2.1) (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 11 500
      (by norm_num [RCbaseReserve]) (by norm_num) h_RCCheck_0.2.2.2
  · exact lower_cert (hr 1 h_RCCheck_1.2.2.1) (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 11 500
      (by norm_num [RCbaseReserve]) (by norm_num) h_RCCheck_1.2.2.2
  · exact lower_cert (hr 2 h_RCCheck_2.2.2.1) (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 21 1000
      (by norm_num [RCbaseReserve]) (by norm_num) h_RCCheck_2.2.2.2

end SquaresInCircles.Eight.GlobalGA.NegativeA.LongE.Certificate
