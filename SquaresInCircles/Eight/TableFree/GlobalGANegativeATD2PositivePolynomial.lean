module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2NegativeSlopes
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# The two prescribed positive-angle quartics

Uncompiled transcription of (28)--(29) and (35)--(36) in the negative-A
angle companion. Each positivity statement uses exactly the centered
monomial coefficient norm in the hand proof, on its full stated interval.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.PositivePolynomial
open Polynomial PowerTailBounds DirectedPowerBounds
open WholeIntervalPolynomial.Certificate (Scaled)

def PU : ℚ[X] := (C (3/5)+C (557/1000)*X)^2*
  (1+X^2+C (741/1000)*X)-C ((1839/1000)^2)*X^2
def PA : ℚ[X] := (C (13/12+371/1000)+C (557/1000)*X)^2*
  (1+C (861/1000)*X^2)-C (9789/2500)*(C (371/1000)+X)^2
def centeredU : ℚ[X] := shift (3/4) PU
def centeredA : ℚ[X] := shift (47/50) PA

/-- A polynomial of degree at most four is its constant term plus its degree-one-to-four tail. -/
private lemma r71_eq_tail {p : ℚ[X]} (hp : p.natDegree≤4) :
    p=C (p.coeff 0)+PowerTailBounds.tail p 1 4 := by
  conv_lhs => rw [p.as_sum_range' 5 (by omega)]
  simp only [PowerTailBounds.tail,Fin.sum_univ_four,Finset.sum_range_succ,Finset.sum_range_zero,
    C_mul_X_pow_eq_monomial,Fin.val_zero,Fin.val_one,Fin.val_two]
  simp only [Fin.isValue,zero_add,monomial_zero_left,Nat.reduceAdd,add_assoc]
  rfl

/-- Integer coefficient list of `centeredU = PU (3/4+X)`. -/
private def r71U : Scaled :=
  ((((Scaled.const (3/5)).add ((Scaled.const (557/1000)).mul
      ((Scaled.const (3/4)).add Scaled.var))).pow 2).mul
    (((Scaled.ofNat 1).add (((Scaled.const (3/4)).add Scaled.var).pow 2)).add
      ((Scaled.const (741/1000)).mul ((Scaled.const (3/4)).add Scaled.var)))).sub
  (((Scaled.const (1839/1000)).pow 2).mul (((Scaled.const (3/4)).add Scaled.var).pow 2))

private theorem r71U_rep : r71U.Rep centeredU := by
  have hy := (Scaled.rep_const (3/4)).add Scaled.rep_var
  have h := ((((Scaled.rep_const (3/5)).add ((Scaled.rep_const (557/1000)).mul hy)).pow 2).mul
      ((Scaled.rep_one.add (hy.pow 2)).add ((Scaled.rep_const (741/1000)).mul hy))).sub
    (((Scaled.rep_const (1839/1000)).pow 2).mul (hy.pow 2))
  have e : centeredU=(C (3/5)+C (557/1000)*(C (3/4)+X))^2*
      (1+(C (3/4)+X)^2+C (741/1000)*(C (3/4)+X))-C (1839/1000)^2*(C (3/4)+X)^2 := by
    simp only [centeredU,shift,PU,sub_comp,add_comp,mul_comp,pow_comp,C_comp,X_comp,one_comp,
      map_pow]
  rw [e]
  exact h

/-- Integer coefficient list of `centeredA = PA (47/50+X)`. -/
private def r71A : Scaled :=
  ((((Scaled.const (13/12+371/1000)).add ((Scaled.const (557/1000)).mul
      ((Scaled.const (47/50)).add Scaled.var))).pow 2).mul
    ((Scaled.ofNat 1).add ((Scaled.const (861/1000)).mul
      (((Scaled.const (47/50)).add Scaled.var).pow 2)))).sub
  ((Scaled.const (9789/2500)).mul
    (((Scaled.const (371/1000)).add ((Scaled.const (47/50)).add Scaled.var)).pow 2))

private theorem r71A_rep : r71A.Rep centeredA := by
  have hy := (Scaled.rep_const (47/50)).add Scaled.rep_var
  have h := ((((Scaled.rep_const (13/12+371/1000)).add
      ((Scaled.rep_const (557/1000)).mul hy)).pow 2).mul
      (Scaled.rep_one.add ((Scaled.rep_const (861/1000)).mul (hy.pow 2)))).sub
    ((Scaled.rep_const (9789/2500)).mul (((Scaled.rep_const (371/1000)).add hy).pow 2))
  have e : centeredA=(C (13/12+371/1000)+C (557/1000)*(C (47/50)+X))^2*
      (1+C (861/1000)*(C (47/50)+X)^2)-C (9789/2500)*(C (371/1000)+(C (47/50)+X))^2 := by
    simp only [centeredA,shift,PA,sub_comp,add_comp,mul_comp,pow_comp,C_comp,X_comp,one_comp]
  rw [e]
  exact h

theorem PU_certificate :
    centeredU=C (centeredU.coeff 0)+tail centeredU 1 4 ∧
    centeredU.coeff 0-PowerTailBounds.norm centeredU 1 4 (1/4)=
      (30312841/250000000:ℚ) := by
  have hcl : r71U.l=[119515010515200000000,-143361732019200000000,348924076134400000000,
      749175402086400000000,127077990400000000000] ∧ r71U.s=409600000000000000000 := by
    decide +kernel
  have hs : r71U.s≠0 := by rw [hcl.2]; norm_num
  have hdeg : centeredU.natDegree≤4 := by
    have h := r71U_rep.natDegree_le hs
    rw [hcl.1] at h
    simpa using h
  refine ⟨r71_eq_tail hdeg,?_⟩
  simp only [PowerTailBounds.norm,Fin.sum_univ_four,r71U_rep.coeff hs,hcl.1,hcl.2]
  norm_num

theorem PA_certificate :
    centeredA=C (centeredA.coeff 0)+tail centeredA 1 4 ∧
    centeredA.coeff 0-PowerTailBounds.norm centeredA 1 4 (7/50)=
      (2092249892523197/28125000000000000:ℚ) := by
  have hcl : r71A.l=[55755839881647381250000000000000000,-19161840794565000000000000000000000,
      1253540319000843750000000000000000000,843510001162500000000000000000000000,
      93910918007812500000000000000000000] ∧ r71A.s=351562500000000000000000000000000000 := by
    decide +kernel
  have hs : r71A.s≠0 := by rw [hcl.2]; norm_num
  have hdeg : centeredA.natDegree≤4 := by
    have h := r71A_rep.natDegree_le hs
    rw [hcl.1] at h
    simpa using h
  refine ⟨r71_eq_tail hdeg,?_⟩
  simp only [PowerTailBounds.norm,Fin.sum_univ_four,r71A_rep.coeff hs,hcl.1,hcl.2]
  norm_num

theorem PU_positive {r : ℝ} (hr : r∈Set.Icc (1/2:ℝ) 1) :
    0<(3/5+(557/1000)*r)^2*(1+r^2+(741/1000)*r)-(1839/1000)^2*r^2 := by
  have hx : |r-(3/4:ℝ)|≤((1/4:ℚ):ℝ) := by
    rw [show ((1/4:ℚ):ℝ)=1/4 by norm_num]
    apply abs_le.mpr
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hh := constant_lower PU_certificate.1 hx
  have hreserve : (0:ℝ)<(centeredU.coeff 0:ℝ)-
      (PowerTailBounds.norm centeredU 1 4 (1/4):ℝ) := by
    have he : (0:ℚ)<centeredU.coeff 0-PowerTailBounds.norm centeredU 1 4 (1/4) := by
      rw [PU_certificate.2]
      norm_num
    exact_mod_cast he
  have he : aeval (r-(3/4:ℝ)) centeredU=
      (3/5+(557/1000)*r)^2*(1+r^2+(741/1000)*r)-(1839/1000)^2*r^2 := by
    norm_num [centeredU,shift_eval,PU]
  rw [he] at hh
  exact hreserve.trans_le hh

theorem PA_positive {r : ℝ} (hr : r∈Set.Icc (4/5:ℝ) (27/25:ℝ)) :
    0<(13/12+371/1000+(557/1000)*r)^2*(1+(861/1000)*r^2)-
      qCap*(371/1000+r)^2 := by
  have hx : |r-(47/50:ℝ)|≤((7/50:ℚ):ℝ) := by
    rw [show ((7/50:ℚ):ℝ)=7/50 by norm_num]
    apply abs_le.mpr
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hh := constant_lower PA_certificate.1 hx
  have hreserve : (0:ℝ)<(centeredA.coeff 0:ℝ)-
      (PowerTailBounds.norm centeredA 1 4 (7/50):ℝ) := by
    have he : (0:ℚ)<centeredA.coeff 0-PowerTailBounds.norm centeredA 1 4 (7/50) := by
      rw [PA_certificate.2]
      norm_num
    exact_mod_cast he
  have he : aeval (r-(47/50:ℝ)) centeredA=
      (13/12+371/1000+(557/1000)*r)^2*(1+(861/1000)*r^2)-
        qCap*(371/1000+r)^2 := by
    norm_num [centeredA,shift_eval,PA,qCap]
  rw [he] at hh
  exact hreserve.trans_le hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.PositivePolynomial
