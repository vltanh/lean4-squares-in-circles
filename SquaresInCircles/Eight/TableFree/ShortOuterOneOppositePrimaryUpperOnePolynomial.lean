module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperDiagonalData
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# The two whole-branch polynomials for the exceptional primary owner

Uncompiled transcription of Section 4.1, equations (33) and (35), of
`HAND_SHORT_WORD_UPPER_PRIMARY_CONTACTS_WITHOUT_TABLES.md`.
The positive-coordinate branch retains its affine radical lower bound.
Each displayed polynomial has an increasing derivative whose final
value is still negative, so its fixed final value bounds the complete
interval. The split is exactly the sign of the contact coordinate z.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper.OnePolynomial
open CommonQuarter CorePairGeometry Arithmetic

def N (s : ℝ) : ℝ := 2/5+(27563/10000)*s+(2/5)*s^2
def lowerT (s : ℝ) : ℝ := 19379/10000+(51/500)*s
def rootPolynomial : ℚ[X] :=
  C (14359/100000000)+C (4046684/10000000)*X-C (252601/250000)*X^2
def nonnegativePolynomial : ℚ[X] :=
  C (84442089456547/100000000000000)-C (24201302831342/10000000000000)*X+
    C (955780925704/1000000000000)*X^2+C (21490674984/100000000000)*X^3+
      C (36126167/100000000)*X^4+C (3723/200000)*X^5
def negativePolynomial : ℚ[X] :=
  C (12383828123/10000000000)-C (27563/10000)*X+
    C (13013321/10000000)*X^2+C (17667/40000)*X^4

lemma root_identity (s : ℝ) :
    aeval s rootPolynomial=Q0-(2/5-s)^2-(lowerT s)^2 := by
  norm_num [rootPolynomial,lowerT,Q0]
  ring

theorem lowerT_square {s : ℝ} (hs : s∈Icc (0:ℝ) (2/5)) :
    0≤Q0-(2/5-s)^2-(lowerT s)^2 := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (2/5)) (fun x : ℝ => aeval x rootPolynomial) :=
    concave_of_deriv2
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt rootPolynomial x)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt rootPolynomial.derivative x)
      (fun x _ => by norm_num [rootPolynomial])
  have hh : (0:ℝ)<aeval s rootPolynomial := concave_gt_of_endpoints hc hs
    (by norm_num [rootPolynomial]) (by norm_num [rootPolynomial])
  rw [root_identity] at hh
  exact hh.le

lemma nonnegative_identity (s : ℝ) : aeval s nonnegativePolynomial=
    (73/100)*lowerT s*(lowerT s-1+s^2/2)^2-N s := by
  norm_num [nonnegativePolynomial,lowerT,N]
  ring

lemma nonnegative_derivative_increases :
    MonotoneOn (fun s : ℝ => aeval s nonnegativePolynomial.derivative) (Icc (0:ℝ) (2/5)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s _ => (CenteredMonomialBounds.aeval_hasDerivAt nonnegativePolynomial.derivative s).
      continuousAt.continuousWithinAt)
    (fun s _ => CenteredMonomialBounds.aeval_hasDerivAt nonnegativePolynomial.derivative s)
  intro s hs
  have hs0 : 0≤s := hs.1.le
  norm_num [nonnegativePolynomial]
  positivity

lemma nonnegative_derivative_final :
    aeval (2/5:ℝ) nonnegativePolynomial.derivative<-(29/20:ℝ) := by
  norm_num [nonnegativePolynomial]

lemma nonnegative_value_final : (13/250:ℝ)<aeval (2/5:ℝ) nonnegativePolynomial := by
  norm_num [nonnegativePolynomial]

lemma nonnegative_decreases :
    AntitoneOn (fun s : ℝ => aeval s nonnegativePolynomial) (Icc (0:ℝ) (2/5)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun s _ => (CenteredMonomialBounds.aeval_hasDerivAt nonnegativePolynomial s).
      continuousAt.continuousWithinAt)
    (fun s _ => CenteredMonomialBounds.aeval_hasDerivAt nonnegativePolynomial s)
  intro s hs
  have hh := nonnegative_derivative_increases (Ioo_subset_Icc_self hs)
    (by norm_num : (2/5:ℝ)∈Icc (0:ℝ) (2/5)) hs.2.le
  linarith [nonnegative_derivative_final]

theorem nonnegative_polynomial {s : ℝ} (hs : s∈Icc (0:ℝ) (2/5)) :
    0<(73/100)*lowerT s*(lowerT s-1+s^2/2)^2-N s := by
  have hh := nonnegative_decreases hs (by norm_num : (2/5:ℝ)∈Icc (0:ℝ) (2/5)) hs.2
  have hpos : (0:ℝ)<aeval s nonnegativePolynomial := by linarith [nonnegative_value_final]
  simpa only [nonnegative_identity] using hpos

lemma negative_identity (s : ℝ) : aeval s negativePolynomial=
    (9/10)*(1963/1000)*(963/1000+s^2/2)^2-N s := by
  norm_num [negativePolynomial,N]
  ring

lemma negative_derivative_increases :
    MonotoneOn (fun s : ℝ => aeval s negativePolynomial.derivative) (Icc (0:ℝ) (129/200)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s _ => (CenteredMonomialBounds.aeval_hasDerivAt negativePolynomial.derivative s).
      continuousAt.continuousWithinAt)
    (fun s _ => CenteredMonomialBounds.aeval_hasDerivAt negativePolynomial.derivative s)
  intro s hs
  norm_num [negativePolynomial]
  positivity

lemma negative_derivative_final :
    aeval (129/200:ℝ) negativePolynomial.derivative<-(3/5:ℝ) := by
  norm_num [negativePolynomial]

lemma negative_value_final : (39/500:ℝ)<aeval (129/200:ℝ) negativePolynomial := by
  norm_num [negativePolynomial]

lemma negative_decreases :
    AntitoneOn (fun s : ℝ => aeval s negativePolynomial) (Icc (0:ℝ) (129/200)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun s _ => (CenteredMonomialBounds.aeval_hasDerivAt negativePolynomial s).
      continuousAt.continuousWithinAt)
    (fun s _ => CenteredMonomialBounds.aeval_hasDerivAt negativePolynomial s)
  intro s hs
  have hh := negative_derivative_increases (Ioo_subset_Icc_self hs)
    (by norm_num : (129/200:ℝ)∈Icc (0:ℝ) (129/200)) hs.2.le
  linarith [negative_derivative_final]

theorem negative_polynomial {s : ℝ} (hs : s∈Icc (0:ℝ) (129/200)) :
    0<(9/10)*(1963/1000)*(963/1000+s^2/2)^2-N s := by
  have hh := negative_decreases hs (by norm_num : (129/200:ℝ)∈Icc (0:ℝ) (129/200)) hs.2
  have hpos : (0:ℝ)<aeval s negativePolynomial := by linarith [negative_value_final]
  simpa only [negative_identity] using hpos

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper.OnePolynomial
