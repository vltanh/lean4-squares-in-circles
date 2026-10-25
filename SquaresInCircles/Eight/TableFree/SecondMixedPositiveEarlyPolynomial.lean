module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial

/-!
# One whole-angle polynomial for the early positive mixed contact

This is the rational lower polynomial for the quadratic reference
envelope in HAND_WRONG_0011011_MIXED_COMPONENTS_WITHOUT_TABLES, §6.1.
The coefficient cages used in its construction are
C ≥ -.204013, A ≥ -.638364, B ≥ 1.347384,
D ≤ -.159078, E ≥ -.153197.

The exact endpoint quotient is positive on the complete interval
[.87,1.3]. Thus the polynomial is bounded below by its right endpoint.
This module proves the polynomial statement only. The fixed-radical
coefficient cages, trigonometric transfer, and original B-coordinate
reduction are separate obligations and are not assumed by an actual
geometric theorem here.

Uncompiled source draft. All coefficient calculations are exact
rational identities and kernel arithmetic; no sampled angle data.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveEarlyPolynomial
open Polynomial WholeIntervalPolynomial

def S13 : ℚ[X] :=
  X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7+
    C (1/362880)*X^9-C (1/39916800)*X^11+C (1/6227020800)*X^13

def C12 : ℚ[X] :=
  1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+
    C (1/40320)*X^8-C (1/3628800)*X^10+C (1/479001600)*X^12

def C14 : ℚ[X] := C12-C (1/87178291200)*X^14

/-- The rational Taylor lower expression, with the required .89765
already subtracted. -/
def lowerPoly : ℚ[X] :=
  X-C (204013/1000000)-C (638364/1000000)*S13+
    C (1347384/1000000)*C14-
    C (159078/1000000)*(C12.comp (C 2*X))-
    C (153197/1000000)*(S13.comp (C 2*X))-C (17953/20000)

/-- Explicit synthetic division at the right endpoint. Its coefficient
formula is determined by lowerPoly, rather than supplied as data. -/
def endpointQuotient : ℚ[X] :=
  -∑ n∈Finset.range 14,C (lowerPoly.coeff (n+1))*
    ∑ i∈Finset.range (n+1),C ((13/10:ℚ)^(n-i))*X^i

/-! Exact rational coefficients of the three polynomials of this module, checked
by polynomial identities, and the Chebyshev coefficients of the centered quotient,
checked by kernel arithmetic. -/

private def lpf (i : ℕ) : ℚ := [(86643/1000000:ℚ),
    (27621/500000:ℚ),
    (-22221/62500:ℚ),
    (93197/300000:ℚ),
    (-49911/1000000:ℚ),
    (-1385167/30000000:ℚ),
    (122689/10000000:ℚ),
    (1012379/252000000:ℚ),
    (-546897/560000000:ℚ),
    (-19768807/90720000000:ℚ),
    (2243729/50400000000:ℚ),
    (2245613/285120000000:ℚ),
    (-1290151/950400000000:ℚ),
    (-313907047/1556755200000000:ℚ),
    (-56141/3632428800000000:ℚ)].getD i 0

private def qf (i : ℕ) : ℚ := [(552251692065402498516482593/8382528000000000000000000000:ℚ),
    (78101484910877115270498661/838252800000000000000000000:ℚ),
    (-16917504814609452671500103/83825280000000000000000000:ℚ),
    (701798250199272871423069/8382528000000000000000000:ℚ),
    (21801376553174836263313/838252800000000000000000:ℚ),
    (-1300202101595781825899/83825280000000000000000:ℚ),
    (-20904471061829371223/8382528000000000000000:ℚ),
    (982407999551586829/838252800000000000000:ℚ),
    (12597601399352833/83825280000000000000:ℚ),
    (-436059712972859/8382528000000000000:ℚ),
    (-4837131207143/838252800000000000:ℚ),
    (135767000989/83825280000000000:ℚ),
    (21975682789/108972864000000000:ℚ),
    (56141/3632428800000000:ℚ)].getD i 0

private def cf (i : ℕ) : ℚ := [(38322676473294228615001780235800297494214921/811550638080000000000000000000000000000000000:ℚ),
    (-6751092865792607966698462516441661826987487/991895224320000000000000000000000000000000000:ℚ),
    (3075231385204253527076206216418929589052463/1487842836480000000000000000000000000000000000:ℚ),
    (534307631343829701081955378602281198945627/4463528509440000000000000000000000000000000000:ℚ),
    (-175098984809146250673052286056176284478947/1785411403776000000000000000000000000000000000:ℚ),
    (-7339214871062615795908869562453075274197/8927057018880000000000000000000000000000000000:ℚ),
    (1218884187780488920629459120942413883839/2231764254720000000000000000000000000000000000:ℚ),
    (17453485211902011327452413427064147521/2231764254720000000000000000000000000000000000:ℚ),
    (-7486092094829125024624894148024544043/8927057018880000000000000000000000000000000000:ℚ),
    (27411209093885927799735437744594849/595137134592000000000000000000000000000000000:ℚ),
    (27539273609250032781514341958458533/4463528509440000000000000000000000000000000000:ℚ),
    (860108086672890415219132540846451/4463528509440000000000000000000000000000000000:ℚ),
    (1598344462397868425342963080933/811550638080000000000000000000000000000000000:ℚ),
    (96465066201332086974327263/2975685672960000000000000000000000000000000000:ℚ)].getD i 0

private def bf (i : ℕ) : ℚ := [(12593688761406814997693436171483488967581634043/261180182495232000000000000000000000000000000000:ℚ),
    (-1364489624957503939284916670274008023724063767/203140141940736000000000000000000000000000000000:ℚ),
    (6000796227498189805988614550285075147500009/6094204258222080000000000000000000000000000000:ℚ),
    (216992443754872663763666677740047700538218751/7313045109866496000000000000000000000000000000000:ℚ),
    (-44451564353225840569928649012991139461466971/3656522554933248000000000000000000000000000000000:ℚ),
    (-369464878660569747851067244472612233809397/7313045109866496000000000000000000000000000000000:ℚ),
    (15554302514507998234631624150169325677751/914130638733312000000000000000000000000000000000:ℚ),
    (21560375588241007630755646341898532711/174120121663488000000000000000000000000000000000:ℚ),
    (-3919105707681543230633345334017308823/609420425822208000000000000000000000000000000000:ℚ),
    (665437971673266251958749707428983099/3656522554933248000000000000000000000000000000000:ℚ),
    (11026258517151839044213000339717571/914130638733312000000000000000000000000000000000:ℚ),
    (1376173691104141034740890465106973/7313045109866496000000000000000000000000000000000:ℚ),
    (1598344462397868425342963080933/1662055706787840000000000000000000000000000000000:ℚ),
    (96465066201332086974327263/12188408516444160000000000000000000000000000000000:ℚ)].getD i 0

private lemma coeff_sum (f : ℕ → ℚ) (N n : ℕ) :
    (∑ i ∈ Finset.range N,C (f i)*X^i).coeff n=if n<N then f n else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

private lemma lowerPoly_eq : lowerPoly=∑ i ∈ Finset.range 15,C (lpf i)*X^i := by
  apply Polynomial.funext
  intro t
  simp only [lowerPoly,S13,C14,C12,Finset.sum_range_succ,Finset.sum_range_zero,
    eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow,eval_comp,eval_one,eval_zero,lpf,
    List.getD_cons_succ,List.getD_cons_zero]
  ring

private lemma lowerPoly_coeff (n : ℕ) : lowerPoly.coeff n=if n<15 then lpf n else 0 := by
  rw [lowerPoly_eq,coeff_sum]

private lemma endpointQuotient_eq : endpointQuotient=∑ i ∈ Finset.range 14,C (qf i)*X^i := by
  apply Polynomial.funext
  intro t
  simp only [endpointQuotient,lowerPoly_coeff,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,↓reduceIte,
    eval_neg,Finset.sum_range_succ,Finset.sum_range_zero,eval_add,eval_mul,eval_C,eval_X,
    eval_pow,eval_zero,lpf,qf,List.getD_cons_succ,List.getD_cons_zero]
  ring

private lemma centered_eq :
    centered (87/100) (13/10) endpointQuotient=∑ i ∈ Finset.range 14,C (cf i)*X^i := by
  apply Polynomial.funext
  intro t
  simp only [centered,affine,endpointQuotient_eq,eval_comp,Finset.sum_range_succ,
    Finset.sum_range_zero,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_zero,qf,cf,
    List.getD_cons_succ,List.getD_cons_zero]
  ring

private lemma coefficient_check :
    ∀ j<14,∑ i ∈ Finset.range 14,cf i*monomialCoefficient i j=bf j := by
  decide +kernel

private lemma coefficient_eq (j : ℕ) (hj : j<14) :
    coefficient 13 (centered (87/100) (13/10) endpointQuotient) j=bf j := by
  rw [centered_eq,coefficient,← coefficient_check j hj]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp [Finset.mem_range.mp hi]

private lemma reserve_check : (1/25:ℚ)<bf 0-∑ j : Fin 13,|bf (j.val+1)| := by
  decide +kernel

private def chebf : ℕ → ℚ → ℚ
  | 0,_ => 1
  | 1,t => t
  | n+2,t => 2*t*chebf (n+1) t-chebf n t

private lemma T_eval (n : ℕ) (t : ℚ) : eval t (Polynomial.Chebyshev.T ℚ (n:ℤ))=chebf n t ∧
    eval t (Polynomial.Chebyshev.T ℚ ((n:ℤ)+1))=chebf (n+1) t := by
  induction n with
  | zero => simp [chebf]
  | succ n ih =>
    refine ⟨by push_cast; exact ih.2,?_⟩
    rw [show ((n+1:ℕ):ℤ)+1=(n:ℤ)+2 by push_cast; ring,Polynomial.Chebyshev.T_add_two]
    simp only [eval_sub,eval_mul,eval_X,ih.1,ih.2,chebf]
    norm_num

theorem factor_identity :
    (C (13/10)-X)*endpointQuotient=
      lowerPoly-C (lowerPoly.eval (13/10)) := by
  apply Polynomial.funext
  intro t
  rw [endpointQuotient_eq,lowerPoly_eq]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,eval_add,eval_sub,eval_mul,eval_C,
    eval_X,eval_pow,eval_zero,qf,lpf,List.getD_cons_succ,List.getD_cons_zero]
  ring

theorem expansion_identity :
    centered (87/100) (13/10) endpointQuotient=
      expansion 13 (centered (87/100) (13/10) endpointQuotient) := by
  conv_rhs => rw [expansion,series,coefficient_eq 0 (by norm_num)]
  rw [Finset.sum_congr rfl (fun (j : Fin 13) _ => by
    rw [coefficient_eq (j.val+1) (by omega)])]
  rw [centered_eq]
  apply Polynomial.funext
  intro t
  simp only [eval_add,eval_finsetSum,eval_mul,eval_C,eval_X,eval_pow,(T_eval _ t).2]
  rw [Fin.sum_univ_eq_sum_range (fun j => bf (j+1)*chebf (j+1) t) 13]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,bf,cf,chebf,List.getD_cons_succ,
    List.getD_cons_zero]
  ring

theorem coefficient_reserve :
    (1/25:ℚ)<lowerOn 13 (87/100) (13/10) endpointQuotient := by
  rw [lowerOn,lower,coefficient_eq 0 (by norm_num),
    Finset.sum_congr rfl (fun (j : Fin 13) _ => by rw [coefficient_eq (j.val+1) (by omega)])]
  exact reserve_check

theorem endpoint_reserve :
    (99/100000:ℚ)<lowerPoly.eval (13/10) := by
  rw [lowerPoly_eq]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,eval_add,eval_mul,eval_C,eval_X,
    eval_pow,eval_zero,lpf,List.getD_cons_succ,List.getD_cons_zero]
  norm_num

theorem quotient_positive {x : ℝ} (hx : x∈Set.Icc (87/100:ℝ) (13/10)) :
    (1/25:ℝ)<aeval x endpointQuotient := by
  have hx' : x∈Set.Icc ((87/100:ℚ):ℝ) ((13/10:ℚ):ℝ) := by push_cast; exact hx
  have h := positive_on_interval (by norm_num) expansion_identity coefficient_reserve hx'
  push_cast at h
  exact h

/-- The complete early angle interval has a strict polynomial reserve
above .00099. No derivative premise or angle subdivision is used. -/
theorem lower {x : ℝ} (hx : x∈Set.Icc (87/100:ℝ) (13/10)) :
    (99/100000:ℝ)<aeval x lowerPoly := by
  have hq := quotient_positive hx
  have hp := mul_nonneg (show 0≤(13/10:ℝ)-x by linarith [hx.2])
    (show 0≤aeval x endpointQuotient by linarith)
  have he := congrArg (fun p : ℚ[X] => aeval x p) factor_identity
  simp only [map_mul,map_sub,aeval_C,aeval_X,eq_ratCast] at he
  have hend : ((99/100000:ℚ):ℝ)<((lowerPoly.eval (13/10):ℚ):ℝ) := Rat.cast_lt.mpr endpoint_reserve
  push_cast at he hend
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveEarlyPolynomial

