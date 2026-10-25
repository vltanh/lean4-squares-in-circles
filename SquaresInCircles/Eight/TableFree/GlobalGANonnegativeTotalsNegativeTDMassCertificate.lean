module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDPolynomialData
public import SquaresInCircles.Eight.TableFree.BivariateCertificates
public import SquaresInCircles.Eight.TableFree.CertificateRestrictions

/-! # The negative-TD2 mass certificate: exact bivariate checks of the nine cubic masses -/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

open CertificateRestrictions

/-! ### Exact models of the masses

`XM` models of the parts of `mass f j`, generic in the packing. The mass of `f` at `j` is the
base mass `cubicMass (rhoBase j) (P0 j)` unless `f` is `.negative j` or `.positive j`, so nine
masses cover the twenty-four cases. -/

section NMModels
open PackedModels BivariateCertificate

/-- `delta`. -/
private def nm_deltaM (cfg : Config) : XM := XM.add cfg (XM.ofInt cfg 1 6) (XM.varX cfg)

private theorem nm_rep_deltaM (cfg : Config) : (nm_deltaM cfg).Rep cfg delta := by
  unfold nm_deltaM delta
  exact XM.rep_add (XM.rep_lit cfg (by norm_num [L])) (XM.rep_X cfg)

/-- `b`. -/
private def nm_bM (cfg : Config) : XM := XM.sub cfg (XM.ofInt cfg 7 10) (nm_deltaM cfg)

private theorem nm_rep_bM (cfg : Config) : (nm_bM cfg).Rep cfg b := by
  unfold nm_bM b
  exact XM.rep_sub (XM.rep_lit cfg (by norm_num [NegativeTD.Certificate.h])) (nm_rep_deltaM cfg)

/-- `k`. -/
private def nm_kM (cfg : Config) : XM :=
  XM.add cfg (XM.ofInt cfg 3 4) (XM.mul cfg (XM.ofInt cfg 7 50) (XM.varY cfg))

private theorem nm_rep_kM (cfg : Config) : (nm_kM cfg).Rep cfg k := by
  unfold nm_kM k e
  exact XM.rep_add (XM.rep_lit cfg (by norm_num)) (XM.rep_mul (XM.rep_lit cfg (by norm_num))
    (XM.rep_Y cfg))

/-- `l`. -/
private def nm_lM (cfg : Config) : XM :=
  XM.add cfg (XM.ofInt cfg 19 20) (XM.mul cfg (XM.ofInt cfg 9 20) (XM.varY cfg))

private theorem nm_rep_lM (cfg : Config) : (nm_lM cfg).Rep cfg l := by
  unfold nm_lM l e
  exact XM.rep_add (XM.rep_lit cfg (by norm_num)) (XM.rep_mul (XM.rep_lit cfg (by norm_num))
    (XM.rep_Y cfg))

/-- `p j`. -/
private def nm_pM (cfg : Config) (j : Fin 3) : XM := ![nm_kM cfg, nm_kM cfg, nm_lM cfg] j

private theorem nm_rep_pM (cfg : Config) (j : Fin 3) : (nm_pM cfg j).Rep cfg (p j) := by
  unfold nm_pM p
  exact XM.rep_vec3 (nm_rep_kM cfg) (nm_rep_kM cfg) (nm_rep_lM cfg) j

/-- `q j`. -/
private def nm_qM (cfg : Config) (j : Fin 3) : XM :=
  ![XM.ofInt cfg 1 1, nm_lM cfg, XM.ofInt cfg 27 20] j

private theorem nm_rep_qM (cfg : Config) (j : Fin 3) : (nm_qM cfg j).Rep cfg (q j) := by
  unfold nm_qM q
  exact XM.rep_vec3 (XM.rep_one cfg) (nm_rep_lM cfg)
    (XM.rep_lit cfg (by norm_num [NegativeTD.Certificate.c])) j

/-- `P0 j`. -/
private def nm_P0M (cfg : Config) (j : Fin 3) : XM :=
  XM.add cfg (XM.pow cfg (nm_pM cfg j) 2) (XM.pow cfg (nm_qM cfg j) 2)

private theorem nm_rep_P0M (cfg : Config) (j : Fin 3) : (nm_P0M cfg j).Rep cfg (P0 j) := by
  unfold nm_P0M P0
  exact XM.rep_add (XM.rep_pow (nm_rep_pM cfg j) 2) (XM.rep_pow (nm_rep_qM cfg j) 2)

/-- The mass polynomials `P (.negative j) j` and `P (.positive j) j`. -/
private def nm_negP (j : Fin 3) : Bivar :=
  P0 j-TensorWholeIntervalPolynomial.scalar 2*p j*q j*lift delta PositiveTD.Certificate.S11
private def nm_posP (j : Fin 3) : Bivar :=
  P0 j+TensorWholeIntervalPolynomial.scalar 2*p j*q j*lift b PositiveTD.Certificate.S9

/-- `P0 j - 2 p_j q_j S11(delta)` (the mass polynomial of `.negative j` at `j`), reduced. -/
private def nm_PNM (cfg : Config) (j : Fin 3) : XM :=
  XM.reduce cfg (XM.sub cfg (nm_P0M cfg j) (XM.mul cfg (XM.mul cfg (XM.mul cfg
    (XM.ofInt cfg 2 1) (nm_pM cfg j)) (nm_qM cfg j)) (XM.liftM cfg (nm_deltaM cfg) XM.S11L)))

private theorem nm_rep_PNM (cfg : Config) (j : Fin 3) :
    (nm_PNM cfg j).Rep cfg (nm_negP j) :=
  XM.rep_reduce (XM.rep_sub (nm_rep_P0M cfg j) (XM.rep_mul (XM.rep_mul (XM.rep_mul
    (XM.rep_lit cfg (by norm_num)) (nm_rep_pM cfg j)) (nm_rep_qM cfg j))
    (XM.rep_liftS11 (nm_rep_deltaM cfg))))

/-- `P0 j + 2 p_j q_j S9(b)` (the mass polynomial of `.positive j` at `j`), reduced. -/
private def nm_PPM (cfg : Config) (j : Fin 3) : XM :=
  XM.reduce cfg (XM.add cfg (nm_P0M cfg j) (XM.mul cfg (XM.mul cfg (XM.mul cfg
    (XM.ofInt cfg 2 1) (nm_pM cfg j)) (nm_qM cfg j)) (XM.liftM cfg (nm_bM cfg) XM.S9L)))

private theorem nm_rep_PPM (cfg : Config) (j : Fin 3) :
    (nm_PPM cfg j).Rep cfg (nm_posP j) :=
  XM.rep_reduce (XM.rep_add (nm_rep_P0M cfg j) (XM.rep_mul (XM.rep_mul (XM.rep_mul
    (XM.rep_lit cfg (by norm_num)) (nm_rep_pM cfg j)) (nm_rep_qM cfg j))
    (XM.rep_liftS9 (nm_rep_bM cfg))))

/-- `rhoBase`, `rhoNegative`, `rhoPositive` as numerators and denominators. -/
private def nm_rhoB : Fin 3 → ℤ × ℕ := ![(5,4),(302592961,250000000),(825378701,500000000)]
private def nm_rhoN : Fin 3 → ℤ × ℕ :=
  ![(573074123,500000000),(221684281,200000000),(75820123,50000000)]
private def nm_rhoP : Fin 3 → ℤ × ℕ :=
  ![(1524831081,1000000000),(369922233,250000000),(2007252551,1000000000)]

private theorem nm_rhoB_eq (j : Fin 3) : rhoBase j=((nm_rhoB j).1:ℚ)/((nm_rhoB j).2:ℚ) := by
  fin_cases j <;> norm_num [rhoBase,nm_rhoB]
private theorem nm_rhoN_eq (j : Fin 3) : rhoNegative j=((nm_rhoN j).1:ℚ)/((nm_rhoN j).2:ℚ) := by
  fin_cases j <;> norm_num [rhoNegative,nm_rhoN]
private theorem nm_rhoP_eq (j : Fin 3) : rhoPositive j=((nm_rhoP j).1:ℚ)/((nm_rhoP j).2:ℚ) := by
  fin_cases j <;> norm_num [rhoPositive,nm_rhoP]

/-- The base mass `cubicMass (rhoBase j) (P0 j)`, reduced. -/
private def nm_massBM (cfg : Config) (j : Fin 3) : XM :=
  XM.reduce cfg (XM.cubicMassRM cfg (nm_rhoB j).1 (nm_rhoB j).2 (XM.reduce cfg (nm_P0M cfg j)))

private theorem nm_rep_massBM (cfg : Config) (j : Fin 3) :
    (nm_massBM cfg j).Rep cfg (cubicMass (rhoBase j) (P0 j)) :=
  XM.rep_reduce (XM.rep_cubicMassRM (XM.rep_reduce (nm_rep_P0M cfg j)) (nm_rhoB_eq j))

/-- The mass of `.negative j` at `j`, reduced. -/
private def nm_massNM (cfg : Config) (j : Fin 3) : XM :=
  XM.reduce cfg (XM.cubicMassRM cfg (nm_rhoN j).1 (nm_rhoN j).2 (nm_PNM cfg j))

private theorem nm_rep_massNM (cfg : Config) (j : Fin 3) :
    (nm_massNM cfg j).Rep cfg (cubicMass (rhoNegative j) (nm_negP j)) :=
  XM.rep_reduce (XM.rep_cubicMassRM (nm_rep_PNM cfg j) (nm_rhoN_eq j))

/-- The mass of `.positive j` at `j`, reduced. -/
private def nm_massPM (cfg : Config) (j : Fin 3) : XM :=
  XM.reduce cfg (XM.cubicMassRM cfg (nm_rhoP j).1 (nm_rhoP j).2 (nm_PPM cfg j))

private theorem nm_rep_massPM (cfg : Config) (j : Fin 3) :
    (nm_massPM cfg j).Rep cfg (cubicMass (rhoPositive j) (nm_posP j)) :=
  XM.rep_reduce (XM.rep_cubicMassRM (nm_rep_PPM cfg j) (nm_rhoP_eq j))

end NMModels

/-! ### Exact bivariate checks

The masses have total degree `3`, their trapezoid transforms degree `3` in each variable; the
largest intermediate degree is `11` (`S11 (delta)`), so the stride is `13` (`B = 6`). The
largest digit-sum bound met, the final factor `16 ^ 4` included, is below `2 ^ 272`, so digits
of `320` bits suffice (`w = 280` passes, `w = 270` fails). Each check is one kernel computation
on natural numbers, about `60` ms. -/

section NMChecks
open PackedModels BivariateCertificate

/-- The packing of the masses. -/
private def nm_cfg : Config := ⟨0,6,320⟩

private theorem nm_checkB0 : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massBM nm_cfg 0) 1 6 1 1 8 15) 3 18 25=true := by
  decide +kernel
private theorem nm_checkB1 : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massBM nm_cfg 1) 1 6 1 1 8 15) 3 18 25=true := by
  decide +kernel
private theorem nm_checkB2 : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massBM nm_cfg 2) 1 6 1 1 8 15) 3 18 25=true := by
  decide +kernel
private theorem nm_checkN0 : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massNM nm_cfg 0) 1 6 1 1 8 15) 3 18 25=true := by
  decide +kernel
private theorem nm_checkN1 : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massNM nm_cfg 1) 1 6 1 1 8 15) 3 18 25=true := by
  decide +kernel
private theorem nm_checkN2 : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massNM nm_cfg 2) 1 6 1 1 8 15) 3 18 25=true := by
  decide +kernel
private theorem nm_checkP0 : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massPM nm_cfg 0) 1 6 1 1 8 15) 3 18 25=true := by
  decide +kernel
private theorem nm_checkP1 : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massPM nm_cfg 1) 1 6 1 1 8 15) 3 18 25=true := by
  decide +kernel
private theorem nm_checkP2 : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massPM nm_cfg 2) 1 6 1 1 8 15) 3 18 25=true := by
  decide +kernel

private theorem nm_checkB (j : Fin 3) : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massBM nm_cfg j) 1 6 1 1 8 15) 3 18 25=true := by
  fin_cases j
  exacts [nm_checkB0,nm_checkB1,nm_checkB2]
private theorem nm_checkN (j : Fin 3) : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massNM nm_cfg j) 1 6 1 1 8 15) 3 18 25=true := by
  fin_cases j
  exacts [nm_checkN0,nm_checkN1,nm_checkN2]
private theorem nm_checkP (j : Fin 3) : XM.lowerCheck nm_cfg
    (XM.fanM nm_cfg (nm_massPM nm_cfg j) 1 6 1 1 8 15) 3 18 25=true := by
  fin_cases j
  exacts [nm_checkP0,nm_checkP1,nm_checkP2]

/-- A checked model of `pp` gives the certificate of `pp` on the trapezoid. -/
private theorem nm_of_rep {m : XM} {pp : Bivar} (hm : m.Rep nm_cfg pp)
    (hc : XM.lowerCheck nm_cfg (XM.fanM nm_cfg m 1 6 1 1 8 15) 3 18 25=true) :
    transform pp=expansion 3 (transform pp) ∧ (18/25:ℚ)<lowerOn 3 pp :=
  XM.lower_certificate (XM.rep_trapezoidM hm (by norm_num [L]) (by norm_num [d]) (by norm_num)) hc
    (by norm_num)

end NMChecks

theorem mass_certificate (f : Kind) (j : Fin 3) :
    transform (mass f j)=expansion 3 (transform (mass f j)) ∧
      (18/25:ℚ)<lowerOn 3 (mass f j) := by
  have hB : ∀ j : Fin 3, transform (cubicMass (rhoBase j) (P0 j))=
      expansion 3 (transform (cubicMass (rhoBase j) (P0 j))) ∧
      (18/25:ℚ)<lowerOn 3 (cubicMass (rhoBase j) (P0 j)) := fun j =>
    nm_of_rep (nm_rep_massBM nm_cfg j) (nm_checkB j)
  cases f with
  | negative i =>
    by_cases hij : i=j
    · subst hij
      have he : mass (.negative i) i=cubicMass (rhoNegative i) (nm_negP i) := by
        simp only [mass,P,rho,nm_negP,↓reduceIte]
      rw [he]
      exact nm_of_rep (nm_rep_massNM nm_cfg i) (nm_checkN i)
    · have he : mass (.negative i) j=cubicMass (rhoBase j) (P0 j) := by
        simp only [mass,P,rho,hij,↓reduceIte,sub_zero]
      rw [he]
      exact hB j
  | equal => exact hB j
  | positive i =>
    by_cases hij : i=j
    · subst hij
      have he : mass (.positive i) i=cubicMass (rhoPositive i) (nm_posP i) := by
        simp only [mass,P,rho,nm_posP,↓reduceIte]
      rw [he]
      exact nm_of_rep (nm_rep_massPM nm_cfg i) (nm_checkP i)
    · have he : mass (.positive i) j=cubicMass (rhoBase j) (P0 j) := by
        simp only [mass,P,rho,hij,↓reduceIte,add_zero]
      rw [he]
      exact hB j
  | diagonal => exact hB j

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Certificate
