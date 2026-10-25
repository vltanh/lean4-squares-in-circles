module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LongData
public import SquaresInCircles.Eight.Owners.GA.Negative.ALongECertificates
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeData

/-!
# Eight squares: literal whole-domain certificates for the twelve BT3 longer-E endpoints

The TE base is the already proved positive-BT triangle base.  The
RE second derivative and its three intrinsic edges cover its entire
trapezoid, and RC uses its exact polynomial quotient in y. One kernel evaluation per numerator
checks its bivariate bound together with the univariate bounds on its edges, which are read off
the same exact model.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Certificate
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
    XM.add cfg (XM.pow cfg (h_lM cfg r) 2) (XM.pow cfg (h_cM cfg r) 2),
    XM.add cfg (XM.ofInt cfg 1 1) (XM.pow cfg (h_MM cfg r) 2)]

/-- Mirror of `P r i j`. -/
def h_PM (cfg : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  XM.sub cfg (h_baseNormM cfg r j)
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

end Models

/-- `pull .TE` is the identity. -/
private theorem h_pull_TE (p : Bivar) : NegativeA.LongE.Certificate.pull .TE p=p := by
  have hl : lift (C X : Bivar)=(Polynomial.C : ℚ[X] →+* Bivar) := by
    apply Polynomial.ringHom_ext
    · intro a; simp [lift]
    · simp [lift]
  simp only [NegativeA.LongE.Certificate.pull,NegativeA.LongE.Certificate.baseY]
  change p.eval₂ (lift (C X)) X=p
  rw [hl,eval₂_C_X]

/-- The gain vanishes on `y = 0`. -/
private theorem h_gain_zero : yZero (NegativeA.LongE.Certificate.gain (C X))=0 := by
  simp only [NegativeA.LongE.Certificate.gain,map_add,map_mul,map_sub,map_one,
    hom_lift yZero yZero_C,yZero_CX,Polynomial.comp_zero,scalar,yZero_C]
  simp [PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,
    PositiveTD.Certificate.S5,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4]

/-- Both bases are the restrictions to `y = 0` of numerators that agree once `y` vanishes: the
identity is structural. -/
theorem TEbase_identity (i : Fin 3) :
    TEbase i=PositiveBT3.LargeCertificate.triangleBase i := by
  have hk : NegativeA.LongE.Certificate.k .TE=NonnegativeTotals.Certificate.k .triangle := by
    simp [NegativeA.LongE.Certificate.k,h_pull_TE,NegativeA.LongE.Explicit.baseRegion]
  have hl : NegativeA.LongE.Certificate.l .TE=NonnegativeTotals.Certificate.l .triangle := by
    simp [NegativeA.LongE.Certificate.l,h_pull_TE,NegativeA.LongE.Explicit.baseRegion]
  have hc : NegativeA.LongE.Certificate.c .TE=NonnegativeTotals.Certificate.c .triangle := by
    simp [NegativeA.LongE.Certificate.c,h_pull_TE,NegativeA.LongE.Explicit.baseRegion]
  have hz : NegativeA.LongE.Certificate.z .TE=NonnegativeTotals.Certificate.theta .triangle := by
    simp [NegativeA.LongE.Certificate.z,h_pull_TE,NegativeA.LongE.Explicit.baseRegion]
  have he : NegativeA.LongE.Certificate.e .TE=NonnegativeTotals.Certificate.e .triangle := by
    simp [NegativeA.LongE.Certificate.e,h_pull_TE,NegativeA.LongE.Explicit.baseRegion]
  have hs : NegativeA.LongE.Certificate.s .TE=C X := rfl
  have hM : NegativeA.LongE.Certificate.M .TE=PositiveBT3.LargeCertificate.rotation .triangle := by
    simp only [NegativeA.LongE.Certificate.M,PositiveBT3.LargeCertificate.rotation,hc,hz]
  have hqB : qB .TE=PositiveBT3.LargeCertificate.qB .triangle := by
    simp only [qB,PositiveBT3.LargeCertificate.qB,NonnegativeTotals.Certificate.qStar,hl]
  have hjE : NegativeA.LongE.Certificate.jE .TE=NonnegativeTotals.Certificate.jE .triangle := by
    simp only [NegativeA.LongE.Certificate.jE,NonnegativeTotals.Certificate.jE,he]
  have hbase : baseNorm .TE=PositiveBT3.LargeCertificate.baseNorm .triangle := by
    simp only [baseNorm,PositiveBT3.LargeCertificate.baseNorm,hk,hl,hc,hM]
  have hABase : NegativeA.LongE.Certificate.ABase .TE=
      NonnegativeTotals.Certificate.ABase .triangle .atT+
        NegativeA.LongE.Certificate.l .TE*NegativeA.LongE.Certificate.gain
          (NegativeA.LongE.Certificate.s .TE) := by
    simp only [NegativeA.LongE.Certificate.ABase,NonnegativeTotals.Certificate.ABase,hk,hl,hc,hz,
      hjE]
  have hδ : yZero (NegativeA.LongE.Certificate.delta .TE)=
      yZero (NonnegativeTotals.Certificate.delta .triangle) := by
    simp only [NegativeA.LongE.Certificate.delta,NonnegativeTotals.Certificate.delta,hz,he,hs,
      NonnegativeTotals.Certificate.e,map_add,map_sub,yZero_CX,add_zero,sub_zero]
  have hA : yZero (A .TE i)=yZero (PositiveBT3.LargeCertificate.A .triangle i) := by
    simp only [A,PositiveBT3.LargeCertificate.A,hABase,hl,hqB,map_add,map_mul,map_sub,map_one,
      hom_lift yZero yZero_C,hδ,hs,h_gain_zero,mul_zero,add_zero]
  have hP (j : Fin 4) : yZero (P .TE i j)=yZero (PositiveBT3.LargeCertificate.P .triangle i j) := by
    simp only [P,PositiveBT3.LargeCertificate.P,hbase,hk,hl,hc]
    split_ifs <;> simp only [map_sub,map_mul,hom_lift yZero yZero_C,hδ,map_zero]
  have hrho (j : Fin 4) : rho .TE i j=PositiveBT3.LargeCertificate.rho i j := by
    fin_cases i <;> fin_cases j <;> norm_num [rho,PositiveBT3.LargeCertificate.rho]
  have hmass (j : Fin 4) :
      yZero (mass .TE i j)=yZero (PositiveBT3.LargeCertificate.mass .triangle i j) := by
    simp only [mass,PositiveBT3.LargeCertificate.mass,map_add,
      hom_cubicMass yZero yZero_C yZero_truncate3 constant_eq_yZero,hP,hrho]
    simp
  simp only [TEbase,PositiveBT3.LargeCertificate.triangleBase,baseY_eq_yZero]
  simp only [numerator,PositiveBT3.LargeCertificate.numerator,map_sub,map_mul,map_add,map_pow,hA,
    hP,hmass]

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
open NegativeA.LongE.Certificate (h_transformM h_cfgT h_cfgR)

/-! Each check is one kernel evaluation of exact models. The bivariate bound of a numerator and
the univariate bounds on its edges share one evaluation, which builds the model of the numerator
once. `Elab.async false` runs the checks one at a time, which bounds the memory of the file by
that of the largest check. -/

/-- The reserves as numerators and denominators. -/
def h_massResP : Region → ℤ × ℕ
  | .TE => (7,10) | .TC => (107,100) | .RE => (11,10) | .RC => (103,100)
def h_TEdR : Fin 3 → ℤ × ℕ := ![(-7,10),(-11,20),(-1,2)]
def h_TCR : Fin 3 → ℤ × ℕ := ![(13,1000),(4,125),(53,200)]
def h_REcR : Fin 3 → ℤ × ℕ := ![(-67,10),(-36,5),(-111,10)]
def h_RCqR : Fin 3 → ℤ × ℕ := ![(427,500),(148,125),(3443,1000)]

/-- The far edge `y = 8/15 - x` of the quotient by `y` of the TE numerator `i`. -/
private def h_TEfarM (i : Fin 3) : XM :=
  XM.substY h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE i)) [(8,0,0),(-15,1,0)] 15
/-- The edge `x = 1/6` of the RE numerator `i`. -/
private def h_REmidM (i : Fin 3) : XM := XM.substX h_cfgR (h_numM h_cfgR .RE i) [(1,0,0)] 6
/-- The edge `y = 19/50 - x` of the RE numerator `i`. -/
private def h_REfarM (i : Fin 3) : XM :=
  XM.substY h_cfgR (h_numM h_cfgR .RE i) [(19,0,0),(-50,1,0)] 50

/-- The checks of the four cubic masses of the numerator `i` of `r`, for the reserve `n / d`. -/
private abbrev h_massOK (cfg : Config) (r : Region) (i : Fin 3) (n : ℤ) (d : ℕ) : Prop :=
  XM.lowerCheck cfg (h_transformM cfg r (h_massM cfg r i 0)) 3 n d=true ∧
  XM.lowerCheck cfg (h_transformM cfg r (h_massM cfg r i 1)) 3 n d=true ∧
  XM.lowerCheck cfg (h_transformM cfg r (h_massM cfg r i 2)) 3 n d=true ∧
  XM.lowerCheck cfg (h_transformM cfg r (h_massM cfg r i 3)) 3 n d=true

set_option Elab.async false in
/-- The TE numerator `0`: its cubic masses, the `y`-derivative of its quotient by `y` on the triangle and the far
edge of the quotient. -/
private theorem h_TECheck_0 :
    h_massOK h_cfgT .TE 0 7 10 ∧ XM.upperCheck h_cfgT (h_transformM h_cfgT .TE
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 0)))) 39 (-7) 10=true ∧
    (h_TEfarM 0).ok=true ∧ h_lowerOK (h_colS h_cfgT (h_TEfarM 0)) 4 15 39 11 1000 := by
  decide +kernel

set_option Elab.async false in
/-- The TE numerator `1`: its cubic masses, the `y`-derivative of its quotient on the triangle and its far edge. -/
private theorem h_TECheck_1 :
    h_massOK h_cfgT .TE 1 7 10 ∧ XM.upperCheck h_cfgT (h_transformM h_cfgT .TE
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 1)))) 39 (-11) 20=true ∧
    (h_TEfarM 1).ok=true ∧ h_lowerOK (h_colS h_cfgT (h_TEfarM 1)) 4 15 39 83 1000 := by
  decide +kernel

set_option Elab.async false in
/-- The TE numerator `2`: its cubic masses, the `y`-derivative of its quotient on the triangle and its far edge. -/
private theorem h_TECheck_2 :
    h_massOK h_cfgT .TE 2 7 10 ∧ XM.upperCheck h_cfgT (h_transformM h_cfgT .TE
      (XM.derivYM h_cfgT (XM.divYM h_cfgT (h_numM h_cfgT .TE 2)))) 39 (-1) 2=true ∧
    (h_TEfarM 2).ok=true ∧ h_lowerOK (h_colS h_cfgT (h_TEfarM 2)) 4 15 39 123 1000 := by
  decide +kernel

set_option Elab.async false in
/-- The TC numerator `0`: its cubic masses and its bound on the triangle. -/
private theorem h_TCCheck_0 :
    h_massOK h_cfgT .TC 0 107 100 ∧ XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (h_numM h_cfgT .TC 0)))
      39 13 1000=true := by
  decide +kernel

set_option Elab.async false in
/-- The TC numerator `1`: its cubic masses and its bound on the triangle. -/
private theorem h_TCCheck_1 :
    h_massOK h_cfgT .TC 1 107 100 ∧ XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (h_numM h_cfgT .TC 1)))
      39 4 125=true := by
  decide +kernel

set_option Elab.async false in
/-- The TC numerator `2`: its cubic masses and its bound on the triangle. -/
private theorem h_TCCheck_2 :
    h_massOK h_cfgT .TC 2 107 100 ∧ XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (h_numM h_cfgT .TC 2)))
      39 53 200=true := by
  decide +kernel

set_option Elab.async false in
/-- The RE numerator `0`: its cubic masses, its second `x`-derivative on the trapezoid and its three
edges. -/
private theorem h_RECheck_0 :
    h_massOK h_cfgR .RE 0 11 10 ∧ XM.upperCheck h_cfgR (h_transformM h_cfgR .RE
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 0)))) 35 (-67) 10=true ∧
    (h_numM h_cfgR .RE 0).ok=true ∧
    h_lowerOK (h_rowS h_cfgR (h_numM h_cfgR .RE 0)) 19 100 35 135 100000 ∧
    (h_REmidM 0).ok=true ∧ h_lowerOK (h_rowS h_cfgR (h_REmidM 0)) 8 75 35 1489 100000 ∧
    (h_REfarM 0).ok=true ∧ h_lowerOK (h_colS h_cfgR (h_REfarM 0)) 1 12 35 2681 100000 := by
  decide +kernel

set_option Elab.async false in
/-- The RE numerator `1`: its cubic masses, its second `x`-derivative on the trapezoid and its three
edges. -/
private theorem h_RECheck_1 :
    h_massOK h_cfgR .RE 1 11 10 ∧ XM.upperCheck h_cfgR (h_transformM h_cfgR .RE
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 1)))) 35 (-36) 5=true ∧
    (h_numM h_cfgR .RE 1).ok=true ∧
    h_lowerOK (h_rowS h_cfgR (h_numM h_cfgR .RE 1)) 19 100 35 134 100000 ∧
    (h_REmidM 1).ok=true ∧ h_lowerOK (h_rowS h_cfgR (h_REmidM 1)) 8 75 35 1489 100000 ∧
    (h_REfarM 1).ok=true ∧ h_lowerOK (h_colS h_cfgR (h_REfarM 1)) 1 12 35 2681 100000 := by
  decide +kernel

set_option Elab.async false in
/-- The RE numerator `2`: its cubic masses, its second `x`-derivative on the trapezoid and its three
edges. -/
private theorem h_RECheck_2 :
    h_massOK h_cfgR .RE 2 11 10 ∧ XM.upperCheck h_cfgR (h_transformM h_cfgR .RE
      (XM.derivXM h_cfgR (XM.derivXM h_cfgR (h_numM h_cfgR .RE 2)))) 35 (-111) 10=true ∧
    (h_numM h_cfgR .RE 2).ok=true ∧
    h_lowerOK (h_rowS h_cfgR (h_numM h_cfgR .RE 2)) 19 100 35 2979 10000 ∧
    (h_REmidM 2).ok=true ∧ h_lowerOK (h_rowS h_cfgR (h_REmidM 2)) 8 75 35 1489 100000 ∧
    (h_REfarM 2).ok=true ∧ h_lowerOK (h_colS h_cfgR (h_REfarM 2)) 1 12 35 2680 100000 := by
  decide +kernel

set_option Elab.async false in
/-- The RC numerator `0`: its cubic masses, its quotient by `y` on the trapezoid and its edge
`y = 0`. -/
private theorem h_RCCheck_0 :
    h_massOK h_cfgR .RC 0 103 100 ∧ XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 0)))) 35 427 500=true ∧
    (h_numM h_cfgR .RC 0).ok=true ∧
    h_lowerOK (h_colS h_cfgR (h_numM h_cfgR .RC 0)) 1 12 35 2209 100000 := by
  decide +kernel

set_option Elab.async false in
/-- The RC numerator `1`: its cubic masses, its quotient by `y` on the trapezoid and its edge
`y = 0`. -/
private theorem h_RCCheck_1 :
    h_massOK h_cfgR .RC 1 103 100 ∧ XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 1)))) 35 148 125=true ∧
    (h_numM h_cfgR .RC 1).ok=true ∧
    h_lowerOK (h_colS h_cfgR (h_numM h_cfgR .RC 1)) 1 12 35 2209 100000 := by
  decide +kernel

set_option Elab.async false in
/-- The RC numerator `2`: its cubic masses, its quotient by `y` on the trapezoid and its edge
`y = 0`. -/
private theorem h_RCCheck_2 :
    h_massOK h_cfgR .RC 2 103 100 ∧ XM.lowerCheck h_cfgR (XM.reduce h_cfgR (h_transformM h_cfgR .RC
      (XM.divYM h_cfgR (h_numM h_cfgR .RC 2)))) 35 3443 1000=true ∧
    (h_numM h_cfgR .RC 2).ok=true ∧
    h_lowerOK (h_colS h_cfgR (h_numM h_cfgR .RC 2)) 1 12 35 2209 100000 := by
  decide +kernel

/-- The far edge of the TE quotient `i`, read off its model. -/
private theorem h_rep_TEfar (i : Fin 3) (hok : (h_TEfarM i).ok=true) :
    (h_colS h_cfgT (h_TEfarM i)).Rep (TEfar i) :=
  h_rep_substY (XM.rep_divYM (h_rep_numM h_cfgT .TE i)) (by simp) 15
    (by apply Polynomial.funext; intro x; simp [XM.polyF, scalar, yZero_C, yZero_X]; ring) hok

/-- The three edges of the RE numerator `i`, read off its model. -/
private theorem h_rep_REboundary (i : Fin 3) (h0 : (h_numM h_cfgR .RE i).ok=true)
    (h1 : (h_REmidM i).ok=true) (h2 : (h_REfarM i).ok=true) :
    (h_rowS h_cfgR (h_numM h_cfgR .RE i)).Rep (REboundary i 0) ∧
    (h_rowS h_cfgR (h_REmidM i)).Rep (REboundary i 1) ∧
    (h_colS h_cfgR (h_REfarM i)).Rep (REboundary i 2) := by
  refine ⟨?_,h_rep_substX (h_rep_numM h_cfgR .RE i) (by simp) 6
    (by simp [XM.polyF, scalar, xZero_C]) h1,
    h_rep_substY (h_rep_numM h_cfgR .RE i) (by simp) 50
    (by apply Polynomial.funext; intro x; simp [XM.polyF, scalar, yZero_C, yZero_X]; ring) h2⟩
  rw [show REboundary i 0=xZero (numerator .RE i) from baseX_eq_xZero _]
  exact h_rep_rowS (h_rep_numM h_cfgR .RE i) h0

end Checks

/-- The mass certificates of the numerator `i` of `r`, from the checks of its masses. -/
private theorem h_mass_of {cfg : PackedModels.Config} {r : Region} {i : Fin 3} {n : ℤ} {d : ℕ}
    (h : h_massOK cfg r i n d) (hq : massReserve r=n/d) (j : Fin 4) :
    transform r (mass r i j)=expansion 3 (transform r (mass r i j)) ∧
    massReserve r<lowerOn r 3 (mass r i j) := by
  open PackedModels BivariateCertificate in
  open NegativeA.LongE.Certificate (h_transformM h_rep_transformM) in
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
  open NegativeA.LongE.Certificate (h_transformM h_rep_transformM h_cfgT) in
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

theorem TEfar_certificate (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 (8/15) (TEfar i)=
      WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 (8/15) (TEfar i)) ∧
    TEfarReserve i<WholeIntervalPolynomial.lowerOn 39 0 (8/15) (TEfar i) := by
  fin_cases i
  · exact lower_cert (h_rep_TEfar 0 h_TECheck_0.2.2.1) (8/15) 4 15 (by norm_num) (by norm_num) 39
      _ 11 1000 (by norm_num [TEfarReserve]) (by norm_num) h_TECheck_0.2.2.2
  · exact lower_cert (h_rep_TEfar 1 h_TECheck_1.2.2.1) (8/15) 4 15 (by norm_num) (by norm_num) 39
      _ 83 1000 (by norm_num [TEfarReserve]) (by norm_num) h_TECheck_1.2.2.2
  · exact lower_cert (h_rep_TEfar 2 h_TECheck_2.2.2.1) (8/15) 4 15 (by norm_num) (by norm_num) 39
      _ 123 1000 (by norm_num [TEfarReserve]) (by norm_num) h_TECheck_2.2.2.2

theorem TC_certificate (i : Fin 3) :
    transform .TC (numerator .TC i)=expansion 39 (transform .TC (numerator .TC i)) ∧
    TCreserve i<lowerOn .TC 39 (numerator .TC i) := by
  open PackedModels BivariateCertificate in
  open NegativeA.LongE.Certificate (h_transformM h_rep_transformM h_cfgT) in
  have h : XM.lowerCheck h_cfgT (XM.reduce h_cfgT (h_transformM h_cfgT .TC (h_numM h_cfgT .TC i)))
      39 (h_TCR i).1 (h_TCR i).2=true := by
    fin_cases i
    · exact h_TCCheck_0.2
    · exact h_TCCheck_1.2
    · exact h_TCCheck_2.2
  exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM (h_rep_numM h_cfgT .TC i) .TC)) h
    (by fin_cases i <;> norm_num [TCreserve,h_TCR])

theorem REcurvature_certificate (i : Fin 3) :
    transform .RE (numerator .RE i).derivative.derivative=
      expansion 35 (transform .RE (numerator .RE i).derivative.derivative) ∧
    upperOn .RE 35 (numerator .RE i).derivative.derivative<REcurvatureReserve i := by
  open PackedModels BivariateCertificate in
  open NegativeA.LongE.Certificate (h_transformM h_rep_transformM h_cfgR) in
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

theorem REboundary_certificate (i j : Fin 3) :
    WholeIntervalPolynomial.centered 0 (RElength j) (REboundary i j)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (RElength j) (REboundary i j)) ∧
    REreserve i j<WholeIntervalPolynomial.lowerOn 35 0 (RElength j) (REboundary i j) := by
  fin_cases i
  · obtain ⟨-,-,h0,c0,h1,c1,h2,c2⟩ := h_RECheck_0
    obtain ⟨r0,r1,r2⟩ := h_rep_REboundary 0 h0 h1 h2
    fin_cases j
    · exact lower_cert r0 (19/50) 19 100 (by norm_num) (by norm_num) 35 _ 135 100000
        (by norm_num [REreserve]) (by norm_num) c0
    · exact lower_cert r1 (16/75) 8 75 (by norm_num) (by norm_num) 35 _ 1489 100000
        (by norm_num [REreserve]) (by norm_num) c1
    · exact lower_cert r2 (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 2681 100000
        (by norm_num [REreserve]) (by norm_num) c2
  · obtain ⟨-,-,h0,c0,h1,c1,h2,c2⟩ := h_RECheck_1
    obtain ⟨r0,r1,r2⟩ := h_rep_REboundary 1 h0 h1 h2
    fin_cases j
    · exact lower_cert r0 (19/50) 19 100 (by norm_num) (by norm_num) 35 _ 134 100000
        (by norm_num [REreserve]) (by norm_num) c0
    · exact lower_cert r1 (16/75) 8 75 (by norm_num) (by norm_num) 35 _ 1489 100000
        (by norm_num [REreserve]) (by norm_num) c1
    · exact lower_cert r2 (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 2681 100000
        (by norm_num [REreserve]) (by norm_num) c2
  · obtain ⟨-,-,h0,c0,h1,c1,h2,c2⟩ := h_RECheck_2
    obtain ⟨r0,r1,r2⟩ := h_rep_REboundary 2 h0 h1 h2
    fin_cases j
    · exact lower_cert r0 (19/50) 19 100 (by norm_num) (by norm_num) 35 _ 2979 10000
        (by norm_num [REreserve]) (by norm_num) c0
    · exact lower_cert r1 (16/75) 8 75 (by norm_num) (by norm_num) 35 _ 1489 100000
        (by norm_num [REreserve]) (by norm_num) c1
    · exact lower_cert r2 (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 2680 100000
        (by norm_num [REreserve]) (by norm_num) c2

theorem RCquotient_certificate (i : Fin 3) :
    transform .RC (RCquotient i)=expansion 35 (transform .RC (RCquotient i)) ∧
    RCquotientReserve i<lowerOn .RC 35 (RCquotient i) := by
  open PackedModels BivariateCertificate in
  open NegativeA.LongE.Certificate (h_transformM h_rep_transformM h_cfgR) in
  have hq := XM.rep_divYM (h_rep_numM h_cfgR .RC i)
  fin_cases i
  · exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM hq .RC)) h_RCCheck_0.2.1
      (by norm_num [RCquotientReserve])
  · exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM hq .RC)) h_RCCheck_1.2.1
      (by norm_num [RCquotientReserve])
  · exact XM.lower_certificate (XM.rep_reduce (h_rep_transformM hq .RC)) h_RCCheck_2.2.1
      (by norm_num [RCquotientReserve])

theorem RCbase_certificate (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 (1/6) (RCbase i)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (1/6) (RCbase i)) ∧
    (2209/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase i) := by
  open NegativeA.LongE.Certificate (h_cfgR) in
  have hr (i : Fin 3) (h : (h_numM h_cfgR .RC i).ok=true) :
      (h_colS h_cfgR (h_numM h_cfgR .RC i)).Rep (RCbase i) := by
    rw [RCbase,baseY_eq_yZero]; exact h_rep_colS (h_rep_numM h_cfgR .RC i) h
  fin_cases i
  · exact lower_cert (hr 0 h_RCCheck_0.2.2.1) (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 2209
      100000 (by norm_num) (by norm_num) h_RCCheck_0.2.2.2
  · exact lower_cert (hr 1 h_RCCheck_1.2.2.1) (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 2209
      100000 (by norm_num) (by norm_num) h_RCCheck_1.2.2.2
  · exact lower_cert (hr 2 h_RCCheck_2.2.2.1) (1/6) 1 12 (by norm_num) (by norm_num) 35 _ 2209
      100000 (by norm_num) (by norm_num) h_RCCheck_2.2.2.2

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Certificate
