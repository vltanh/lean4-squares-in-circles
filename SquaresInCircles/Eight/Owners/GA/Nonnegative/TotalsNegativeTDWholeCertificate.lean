module

public import SquaresInCircles.Eight.Arithmetic.BivariateCertificates
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDPolynomialData

/-! # Eight squares: `whole_certificate`: exact `XM` models of the five whole numerators on the trapezoid -/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

open CertificateRestrictions

/-! ### Exact models of the numerators

`XM` mirrors of the definitions of `GlobalGANonnegativeTotalsNegativeTDPolynomialData`, generic
in the packing `Config`, each with its representation lemma. -/

section Mirrors
open PackedModels BivariateCertificate

private def nw_eM (cfg : Config) : XM := XM.varY cfg

private theorem nw_rep_eM (cfg : Config) : (nw_eM cfg).Rep cfg e := XM.rep_Y cfg

private def nw_deltaM (cfg : Config) : XM := XM.add cfg (XM.ofInt cfg 1 6) (XM.varX cfg)

private theorem nw_rep_deltaM (cfg : Config) : (nw_deltaM cfg).Rep cfg delta :=
  XM.rep_add (XM.rep_lit cfg (by norm_num [L])) (XM.rep_X cfg)

private def nw_aM (cfg : Config) : XM := XM.sub cfg (nw_deltaM cfg) (nw_eM cfg)

private theorem nw_rep_aM (cfg : Config) : (nw_aM cfg).Rep cfg a :=
  XM.rep_sub (nw_rep_deltaM cfg) (nw_rep_eM cfg)

private def nw_bM (cfg : Config) : XM := XM.sub cfg (XM.ofInt cfg 7 10) (nw_deltaM cfg)

private theorem nw_rep_bM (cfg : Config) : (nw_bM cfg).Rep cfg b :=
  XM.rep_sub (XM.rep_lit cfg (by norm_num [h])) (nw_rep_deltaM cfg)

private def nw_kM (cfg : Config) : XM :=
  XM.add cfg (XM.ofInt cfg 3 4) (XM.mul cfg (XM.ofInt cfg 7 50) (nw_eM cfg))

private theorem nw_rep_kM (cfg : Config) : (nw_kM cfg).Rep cfg k :=
  XM.rep_add (XM.rep_lit cfg (by norm_num))
    (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (nw_rep_eM cfg))

private def nw_lM (cfg : Config) : XM :=
  XM.add cfg (XM.ofInt cfg 19 20) (XM.mul cfg (XM.ofInt cfg 9 20) (nw_eM cfg))

private theorem nw_rep_lM (cfg : Config) : (nw_lM cfg).Rep cfg l :=
  XM.rep_add (XM.rep_lit cfg (by norm_num))
    (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (nw_rep_eM cfg))

private def nw_pM (cfg : Config) : Fin 3 → XM := ![nw_kM cfg,nw_kM cfg,nw_lM cfg]

private theorem nw_rep_pM (cfg : Config) (j : Fin 3) : (nw_pM cfg j).Rep cfg (p j) :=
  XM.rep_vec3 (nw_rep_kM cfg) (nw_rep_kM cfg) (nw_rep_lM cfg) j

private def nw_qM (cfg : Config) : Fin 3 → XM := ![XM.ofInt cfg 1 1,nw_lM cfg,XM.ofInt cfg 27 20]

private theorem nw_rep_qM (cfg : Config) (j : Fin 3) : (nw_qM cfg j).Rep cfg (q j) :=
  XM.rep_vec3 (XM.rep_one cfg) (nw_rep_lM cfg) (XM.rep_lit cfg (by norm_num [c])) j

/-- `J u`; `1/2-abar` is `-114321959/125000000`. -/
private def nw_JM (cfg : Config) (u : XM) : XM :=
  XM.sub cfg (XM.add cfg (XM.mul cfg (XM.ofInt cfg 1 2) (XM.sub cfg (XM.liftM cfg u XM.C10L)
      (XM.ofInt cfg 1 1)))
    (XM.mul cfg (XM.ofInt cfg (-114321959) 125000000) (XM.liftM cfg u XM.S9L)))
    (XM.mul cfg (XM.ofInt cfg 29 1000) (XM.pow cfg u 4))

private theorem nw_rep_JM {cfg : Config} {u : XM} {f : Bivar} (hu : u.Rep cfg f) :
    (nw_JM cfg u).Rep cfg (J f) :=
  XM.rep_sub (XM.rep_add (XM.rep_mul (XM.rep_lit cfg (by norm_num))
      (XM.rep_sub (XM.rep_liftC10 hu) (XM.rep_one cfg)))
    (XM.rep_mul (XM.rep_lit cfg (by norm_num [abar])) (XM.rep_liftS9 hu)))
    (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (XM.rep_pow hu 4))

/-- `A0`; the constant `(5/2)c+5/2-(1+c)cbar` is `37618469449/10¹⁰`. -/
private def nw_A0M (cfg : Config) : XM :=
  XM.add cfg (XM.add cfg (XM.add cfg (XM.add cfg (XM.mul cfg (XM.ofInt cfg 2 1) (nw_kM cfg))
    (XM.mul cfg (XM.ofInt cfg 3 1) (nw_lM cfg))) (XM.ofInt cfg 37618469449 10000000000))
    (XM.mul cfg (nw_lM cfg) (nw_JM cfg (nw_aM cfg)))) (nw_JM cfg (nw_eM cfg))

private theorem nw_rep_A0M (cfg : Config) : (nw_A0M cfg).Rep cfg A0 :=
  XM.rep_add (XM.rep_add (XM.rep_add (XM.rep_add
    (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (nw_rep_kM cfg))
    (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (nw_rep_lM cfg)))
    (XM.rep_lit cfg (by norm_num [c,cbar])))
    (XM.rep_mul (nw_rep_lM cfg) (nw_rep_JM (nw_rep_aM cfg)))) (nw_rep_JM (nw_rep_eM cfg))

/-- `A f`; `gamma c` is `492669/400000`, `gamma c h` is `3448683/4000000` and `cbar-1/2` is
`199607033/500000000`. -/
private def nw_AM (cfg : Config) : Kind → XM
  | .negative i => XM.add cfg (nw_A0M cfg) (XM.mul cfg (nw_qM cfg i)
      (XM.sub cfg (XM.liftM cfg (nw_deltaM cfg) XM.C10L) (XM.ofInt cfg 1 1)))
  | .equal => XM.add cfg (nw_A0M cfg) (XM.mul cfg (XM.ofInt cfg 492669 400000) (nw_deltaM cfg))
  | .positive i => XM.add cfg (XM.add cfg (nw_A0M cfg) (XM.ofInt cfg 3448683 4000000))
      (XM.mul cfg (nw_pM cfg i) (XM.sub cfg (XM.add cfg (XM.liftM cfg (nw_bM cfg) XM.C10L)
        (XM.liftM cfg (nw_bM cfg) XM.S11L)) (XM.ofInt cfg 1 1)))
  | .diagonal => XM.sub cfg (XM.add cfg (nw_A0M cfg) (XM.ofInt cfg 3448683 4000000))
      (XM.mul cfg (XM.ofInt cfg 199607033 500000000) (nw_bM cfg))

private theorem nw_rep_AM (cfg : Config) (f : Kind) : (nw_AM cfg f).Rep cfg (A f) := by
  cases f with
  | negative i =>
    exact XM.rep_add (nw_rep_A0M cfg) (XM.rep_mul (nw_rep_qM cfg i)
      (XM.rep_sub (XM.rep_liftC10 (nw_rep_deltaM cfg)) (XM.rep_one cfg)))
  | equal =>
    exact XM.rep_add (nw_rep_A0M cfg)
      (XM.rep_mul (XM.rep_lit cfg (by norm_num [gamma,c])) (nw_rep_deltaM cfg))
  | positive i =>
    exact XM.rep_add (XM.rep_add (nw_rep_A0M cfg)
      (XM.rep_lit cfg (by norm_num [gamma,c,h])))
      (XM.rep_mul (nw_rep_pM cfg i) (XM.rep_sub (XM.rep_add (XM.rep_liftC10 (nw_rep_bM cfg))
        (XM.rep_liftS11 (nw_rep_bM cfg))) (XM.rep_one cfg)))
  | diagonal =>
    exact XM.rep_sub (XM.rep_add (nw_rep_A0M cfg)
      (XM.rep_lit cfg (by norm_num [gamma,c,h])))
      (XM.rep_mul (XM.rep_lit cfg (by norm_num [cbar])) (nw_rep_bM cfg))

private def nw_P0M (cfg : Config) (j : Fin 3) : XM :=
  XM.add cfg (XM.pow cfg (nw_pM cfg j) 2) (XM.pow cfg (nw_qM cfg j) 2)

private theorem nw_rep_P0M (cfg : Config) (j : Fin 3) : (nw_P0M cfg j).Rep cfg (P0 j) :=
  XM.rep_add (XM.rep_pow (nw_rep_pM cfg j) 2) (XM.rep_pow (nw_rep_qM cfg j) 2)

/-- `P f j`, reduced. -/
private def nw_PM (cfg : Config) : Kind → Fin 3 → XM
  | .negative i, j => XM.reduce cfg (XM.sub cfg (nw_P0M cfg j) (if i=j then
      XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.ofInt cfg 2 1) (nw_pM cfg j)) (nw_qM cfg j))
        (XM.liftM cfg (nw_deltaM cfg) XM.S11L) else XM.ofInt cfg 0 1))
  | .positive i, j => XM.reduce cfg (XM.add cfg (nw_P0M cfg j) (if i=j then
      XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.ofInt cfg 2 1) (nw_pM cfg j)) (nw_qM cfg j))
        (XM.liftM cfg (nw_bM cfg) XM.S9L) else XM.ofInt cfg 0 1))
  | .equal, j => XM.reduce cfg (nw_P0M cfg j)
  | .diagonal, j => XM.reduce cfg (nw_P0M cfg j)

private theorem nw_rep_PM (cfg : Config) (f : Kind) (j : Fin 3) :
    (nw_PM cfg f j).Rep cfg (P f j) := by
  cases f with
  | negative i =>
    exact XM.rep_reduce (XM.rep_sub (nw_rep_P0M cfg j) (XM.rep_ite
      (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (nw_rep_pM cfg j))
        (nw_rep_qM cfg j)) (XM.rep_liftS11 (nw_rep_deltaM cfg))) (XM.rep_zero cfg)))
  | positive i =>
    exact XM.rep_reduce (XM.rep_add (nw_rep_P0M cfg j) (XM.rep_ite
      (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_lit cfg (by norm_num)) (nw_rep_pM cfg j))
        (nw_rep_qM cfg j)) (XM.rep_liftS9 (nw_rep_bM cfg))) (XM.rep_zero cfg)))
  | equal => exact XM.rep_reduce (nw_rep_P0M cfg j)
  | diagonal => exact XM.rep_reduce (nw_rep_P0M cfg j)

/-- `rho f j` as a numerator and a denominator. -/
private def nw_rhoP : Kind → Fin 3 → ℤ × ℕ
  | .negative i, j => if i=j then
      ![(573074123,500000000),(221684281,200000000),(75820123,50000000)] j
    else ![(5,4),(302592961,250000000),(825378701,500000000)] j
  | .positive i, j => if i=j then
      ![(1524831081,1000000000),(369922233,250000000),(2007252551,1000000000)] j
    else ![(5,4),(302592961,250000000),(825378701,500000000)] j
  | .equal, j => ![(5,4),(302592961,250000000),(825378701,500000000)] j
  | .diagonal, j => ![(5,4),(302592961,250000000),(825378701,500000000)] j

private theorem nw_rho_eq (f : Kind) (j : Fin 3) :
    rho f j=((nw_rhoP f j).1:ℚ)/((nw_rhoP f j).2:ℚ) := by
  rcases f with i | _ | i | _ <;> fin_cases j <;> (try fin_cases i) <;>
    norm_num [rho,nw_rhoP,rhoBase,rhoNegative,rhoPositive]

/-- `mass f j`, reduced. -/
private def nw_massM (cfg : Config) (f : Kind) (j : Fin 3) : XM :=
  XM.reduce cfg (XM.cubicMassRM cfg (nw_rhoP f j).1 (nw_rhoP f j).2 (nw_PM cfg f j))

private theorem nw_rep_massM (cfg : Config) (f : Kind) (j : Fin 3) :
    (nw_massM cfg f j).Rep cfg (mass f j) :=
  XM.rep_reduce (XM.rep_cubicMassRM (nw_rep_PM cfg f j) (nw_rho_eq f j))

/-- `numerator f`, reduced. -/
private def nw_numM (cfg : Config) (f : Kind) : XM :=
  XM.reduce cfg (XM.sub cfg
    (XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.mul cfg (XM.ofInt cfg 2 1) (nw_AM cfg f))
      (nw_massM cfg f 0)) (nw_massM cfg f 1)) (nw_massM cfg f 2))
    (XM.mul cfg (XM.ofInt cfg 494696877 250000000) (XM.add cfg (XM.add cfg
      (XM.mul cfg (XM.mul cfg (XM.add cfg (nw_PM cfg f 0) (XM.pow cfg (nw_massM cfg f 0) 2))
        (nw_massM cfg f 1)) (nw_massM cfg f 2))
      (XM.mul cfg (XM.mul cfg (XM.add cfg (nw_PM cfg f 1) (XM.pow cfg (nw_massM cfg f 1) 2))
        (nw_massM cfg f 0)) (nw_massM cfg f 2)))
      (XM.mul cfg (XM.mul cfg (XM.add cfg (nw_PM cfg f 2) (XM.pow cfg (nw_massM cfg f 2) 2))
        (nw_massM cfg f 0)) (nw_massM cfg f 1)))))

private theorem nw_rep_numM (cfg : Config) (f : Kind) :
    (nw_numM cfg f).Rep cfg (numerator f) := by
  have hw (j : Fin 3) := nw_rep_massM cfg f j
  have hP (j : Fin 3) := nw_rep_PM cfg f j
  exact XM.rep_reduce (XM.rep_sub (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_mul
      (XM.rep_lit cfg (by norm_num)) (nw_rep_AM cfg f)) (hw 0)) (hw 1)) (hw 2))
    (XM.rep_mul (XM.rep_lit cfg (by norm_num [Rbar])) (XM.rep_add (XM.rep_add
      (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 0) (XM.rep_pow (hw 0) 2)) (hw 1)) (hw 2))
      (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 1) (XM.rep_pow (hw 1) 2)) (hw 0)) (hw 2)))
      (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 2) (XM.rep_pow (hw 2) 2)) (hw 0)) (hw 1)))))

/-- `transform (numerator f)`, by `fanM`: `t = d (x+1)/2`, `e = (L+t) (y+1)/2`, reduced. -/
private theorem nw_rep_transformM (cfg : Config) (f : Kind) :
    (XM.reduce cfg (XM.fanM cfg (nw_numM cfg f) 1 6 1 1 8 15)).Rep cfg (transform (numerator f)) :=
  XM.rep_reduce (XM.rep_trapezoidM (nw_rep_numM cfg f) (by norm_num [L]) (by norm_num [d])
    (by norm_num))

end Mirrors

section Checks
open PackedModels BivariateCertificate

/-- Packing of the numerators: boxes of `23 × 23` digits of `830` bits. -/
private def nw_cfg : Config := ⟨0,11,830⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem nw_check_equal :
    XM.lowerCheck nw_cfg (XM.reduce nw_cfg (XM.fanM nw_cfg (nw_numM nw_cfg .equal) 1 6 1 1 8 15))
      20 7 250=true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem nw_check_positive_0 :
    XM.lowerCheck nw_cfg (XM.reduce nw_cfg (XM.fanM nw_cfg (nw_numM nw_cfg (.positive 0))
      1 6 1 1 8 15)) 21 21 40=true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem nw_check_positive_1 :
    XM.lowerCheck nw_cfg (XM.reduce nw_cfg (XM.fanM nw_cfg (nw_numM nw_cfg (.positive 1))
      1 6 1 1 8 15)) 21 5 8=true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem nw_check_positive_2 :
    XM.lowerCheck nw_cfg (XM.reduce nw_cfg (XM.fanM nw_cfg (nw_numM nw_cfg (.positive 2))
      1 6 1 1 8 15)) 21 587 1000=true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem nw_check_diagonal :
    XM.lowerCheck nw_cfg (XM.reduce nw_cfg (XM.fanM nw_cfg (nw_numM nw_cfg .diagonal) 1 6 1 1 8 15))
      20 553 1000=true := by
  decide +kernel

end Checks

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem whole_certificate (f : Kind) (hf : Whole f) :
    transform (numerator f)=expansion (degree f) (transform (numerator f)) ∧
      wholeReserve f<lowerOn (degree f) (numerator f) := by
  open BivariateCertificate in
  rcases f with i | _ | i | _
  · exact hf.elim
  · exact XM.lower_certificate (nw_rep_transformM nw_cfg .equal) nw_check_equal
      (by norm_num [wholeReserve])
  · fin_cases i
    · exact XM.lower_certificate (nw_rep_transformM nw_cfg (.positive 0)) nw_check_positive_0
        (by norm_num [wholeReserve])
    · exact XM.lower_certificate (nw_rep_transformM nw_cfg (.positive 1)) nw_check_positive_1
        (by norm_num [wholeReserve])
    · exact XM.lower_certificate (nw_rep_transformM nw_cfg (.positive 2)) nw_check_positive_2
        (by norm_num [wholeReserve])
  · exact XM.lower_certificate (nw_rep_transformM nw_cfg .diagonal) nw_check_diagonal
      (by norm_num [wholeReserve])

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD.Certificate
