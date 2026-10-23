module

public import SquaresInCircles.Eight.TableFree.SpanNormBounds
public import SquaresInCircles.Eight.TableFree.PowerTailBounds
public import SquaresInCircles.Eight.TableFree.TensorWholeIntervalPolynomial

/-!
# The whole-square certificate for the two negative primary owners

Uncompiled source draft of sections 3--4 of
HAND_G5_GLOBAL_PRIMARY_ENTRY_BOTH_NEGATIVE_ALIGNED_SHORT_SPAN.md.

The original primary-corner cap has its exact radical constant.  One
degree-fourteen polynomial gives the tangent cap, and one tensor
Chebyshev coefficient norm proves the strict inequality on the entire
closed square `[0,.09]²`.  Every Taylor comparison below keeps the sign
of both factors in the actual sine and cosine terms.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.BothNegativeSpanPolynomial

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def m : ℝ := 3/2-SpanNormBounds.c

def X (z : ℝ) : ℝ :=
  1+(3/2-SpanNormBounds.c)*Real.cos z+(13/12)*Real.sin z

def Y (z : ℝ) : ℝ := Real.sqrt (qCap-(X z)^2)

def C4 (z : ℝ) : ℝ := 1-z^2/2+z^4/24
def C6 (z : ℝ) : ℝ := 1-z^2/2+z^4/24-z^6/720
def S7 (z : ℝ) : ℝ := z-z^3/6+z^5/120-z^7/5040

def XL (z : ℝ) : ℝ := 1+(6007859/10000000)*C6 z+(13/12)*S7 z
def YU (z : ℝ) : ℝ := 581611/500000-(3727/2500)*z-z^2

theorem m_identity : m=2-Real.sqrt (qCap/2) := by
  simp only [m,SpanNormBounds.c,diagonalCoordinate]
  ring

theorem m_bounds : (6007859/10000000:ℝ)<m ∧ m<300393/500000 := by
  have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hn := Real.sqrt_nonneg (qCap/2)
  simp only [m_identity]
  norm_num [qCap] at hs hn ⊢
  constructor <;> nlinarith

theorem X_eq (z : ℝ) : X z=1+m*Real.cos z+(13/12)*Real.sin z := rfl

theorem X_bounds {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) :
    (16007859/10000000:ℝ)<X z ∧ X z<212/125 := by
  have hm := m_bounds
  have hm0 : 0≤m := by linarith
  have hm1 : m≤1 := by linarith
  have hzsq : z^2≤81/10000 := by
    have hh := pow_le_pow_left₀ hz.1 hz.2 2
    norm_num at hh
    exact hh
  have hzsq' : z^2≤(9/100)*z := by
    nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have hz3 : z^3≤z := by
    have hh := mul_nonneg hz.1 (show 0≤1-z^2 by nlinarith)
    nlinarith
  have hslo : z/2≤Real.sin z := by
    have hh := Real.sin_ge_sub_cube hz.1
    nlinarith
  have hclo := Real.one_sub_sq_div_two_le_cos z
  have hmclo := mul_le_mul_of_nonneg_left hclo hm0
  have hmz := mul_le_mul_of_nonneg_right hm1 (sq_nonneg z)
  have hX0 : 1+m≤X z := by
    rw [X_eq]
    nlinarith
  have hz4 : z^4≤(81/10000)*z^2 := by
    have hh := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hzsq)
    nlinarith
  have hchi : Real.cos z≤1-(499/1000)*z^2 := by
    have hh := cos_upper_four hz.1
    nlinarith
  have hmchi := mul_le_mul_of_nonneg_left hchi hm0
  have hweight : 0≤((499/1000)*m-299/1000)*z^2 :=
    mul_nonneg (by linarith [hm.1]) (sq_nonneg z)
  have hshi := Real.sin_le hz.1
  have hXhi : X z≤1+300393/500000+(13/12)*z-(299/1000)*z^2 := by
    rw [X_eq]
    nlinarith [hm.2]
  have hmono : (13/12)*z-(299/1000)*z^2≤
      (13/12)*(9/100)-(299/1000)*(9/100)^2 := by
    have hh : 0≤(9/100-z)*((13/12)-(299/1000)*(9/100+z)) :=
      mul_nonneg (by linarith [hz.2]) (by linarith [hz.2])
    nlinarith
  constructor
  · linarith [hm.1]
  · linarith

theorem Y_sq {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) :
    (Y z)^2=qCap-(X z)^2 := by
  have hX := X_bounds hz
  have hrad : 0≤qCap-(X z)^2 := by
    have hp : 0<(212/125-X z)*(212/125+X z) :=
      mul_pos (by linarith [hX.2]) (by linarith [hX.1])
    norm_num [qCap] at *
    nlinarith
  exact Real.sq_sqrt hrad

theorem Y_lower {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) :
    (509/500:ℝ)<Y z := by
  have hX := X_bounds hz
  have hY := Y_sq hz
  have hn : 0≤Y z := Real.sqrt_nonneg _
  have hp : 0<(212/125-X z)*(212/125+X z) :=
    mul_pos (by linarith [hX.2]) (by linarith [hX.1])
  norm_num [qCap] at hY
  nlinarith

theorem S7_nonneg {z : ℝ} (hz : z∈Icc 0 (21/100:ℝ)) : 0≤S7 z := by
  have hz1 : z≤1 := by linarith [hz.2]
  have hz2 := pow_le_pow_left₀ hz.1 hz1 2
  have hz6 := pow_le_pow_left₀ hz.1 hz1 6
  have hbr : 0≤1-z^2/6+z^4/120-z^6/5040 := by
    norm_num at hz2 hz6
    nlinarith [sq_nonneg (z^2)]
  have he : S7 z=z*(1-z^2/6+z^4/120-z^6/5040) := by
    dsimp [S7]
    ring
  rw [he]
  exact mul_nonneg hz.1 hbr

theorem C6_lower {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) : (99/100:ℝ)<C6 z := by
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz6 := pow_le_pow_left₀ hz.1 hz.2 6
  norm_num at hz2 hz6
  dsimp [C6]
  nlinarith [sq_nonneg (z^2)]

theorem XL_lower {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) : (3/2:ℝ)<XL z := by
  have hc := C6_lower hz
  have hs := S7_nonneg (show z∈Icc 0 (21/100:ℝ) by
    exact ⟨hz.1,by linarith [hz.2]⟩)
  dsimp [XL]
  linarith

theorem XL_le_X {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) : XL z≤X z := by
  have hm := m_bounds
  have hc0 : 0≤Real.cos z := by
    have hc := Real.one_sub_sq_div_two_le_cos z
    have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
    norm_num at hz2
    nlinarith
  have hc : C6 z≤Real.cos z := cos_lower_six hz.1
  have hs : S7 z≤Real.sin z := sin_lower_seven hz.1
  have hmc := mul_le_mul_of_nonneg_right hm.1.le hc0
  have htc := mul_le_mul_of_nonneg_left hc
    (show (0:ℝ)≤6007859/10000000 by norm_num)
  have hts := mul_le_mul_of_nonneg_left hs (show (0:ℝ)≤13/12 by norm_num)
  rw [X_eq]
  dsimp [XL]
  linarith

theorem YU_lower {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) : 1<YU z := by
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  norm_num at hz2
  dsimp [YU]
  nlinarith [hz.2]

def cos6 : ℚ[X] :=
  1-C (1/2)*Polynomial.X^2+C (1/24)*Polynomial.X^4-C (1/720)*Polynomial.X^6

def sin7 : ℚ[X] :=
  Polynomial.X-C (1/6)*Polynomial.X^3+C (1/120)*Polynomial.X^5-
    C (1/5040)*Polynomial.X^7

def XLpoly : ℚ[X] := 1+C (6007859/10000000)*cos6+C (13/12)*sin7

def YUpoly : ℚ[X] := C (581611/500000)-C (3727/2500)*Polynomial.X-Polynomial.X^2

def capPolynomial : ℚ[X] := YUpoly^2+XLpoly^2-C (9789/2500)

theorem XLpoly_eval (z : ℝ) : aeval z XLpoly=XL z := by
  simp [XLpoly,cos6,sin7,XL,C6,S7] <;> ring

theorem YUpoly_eval (z : ℝ) : aeval z YUpoly=YU z := by
  simp [YUpoly,YU]

theorem capPolynomial_eval (z : ℝ) :
    aeval z capPolynomial=(YU z)^2+(XL z)^2-qCap := by
  simp [capPolynomial,XLpoly_eval,YUpoly_eval,qCap]

/-- Only negative higher coefficients enter the one-sided lower bound. -/
def negativeTail : ℚ :=
  ∑ j : Fin 12,min (capPolynomial.coeff (j.val+3)) 0*(9/100)^(j.val+1)

theorem cap_expansion : capPolynomial=
    C (capPolynomial.coeff 0)+C (capPolynomial.coeff 1)*Polynomial.X+
      C (capPolynomial.coeff 2)*Polynomial.X^2+
        PowerTailBounds.tail capPolynomial 3 12 := by
  decide

theorem cap_coefficients :
    capPolynomial.coeff 0=91892281/100000000000000 ∧
    capPolynomial.coeff 1=266837/2500000000 ∧
    (1079/10000:ℚ)<capPolynomial.coeff 2+negativeTail := by
  decide

theorem negative_tail_lower {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) :
    (negativeTail:ℝ)*z^2≤aeval z (PowerTailBounds.tail capPolynomial 3 12) := by
  have hterm (j : Fin 12) :
      min (capPolynomial.coeff (j.val+3):ℝ) 0*(9/100:ℝ)^(j.val+1)*z^2≤
        (capPolynomial.coeff (j.val+3):ℝ)*z^(j.val+3) := by
    by_cases hc : 0≤(capPolynomial.coeff (j.val+3):ℝ)
    · rw [min_eq_right hc]
      simp only [zero_mul]
      exact mul_nonneg hc (pow_nonneg hz.1 _)
    · have hc' := (le_of_not_ge hc)
      rw [min_eq_left hc']
      have hp := pow_le_pow_left₀ hz.1 hz.2 (j.val+1)
      have hm := mul_le_mul_of_nonpos_left hp hc'
      have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg z)
      have he : (capPolynomial.coeff (j.val+3):ℝ)*z^(j.val+3)=
          ((capPolynomial.coeff (j.val+3):ℝ)*z^(j.val+1))*z^2 := by
        rw [show j.val+3=(j.val+1)+2 by omega,pow_add]
        ring
      rw [he]
      exact hm'
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  have hn : (negativeTail:ℝ)=
      ∑ j : Fin 12,min (capPolynomial.coeff (j.val+3):ℝ) 0*
        (9/100:ℝ)^(j.val+1) := by
    simp [negativeTail]
  rw [hn,Finset.sum_mul]
  simpa only [PowerTailBounds.tail,map_sum,map_mul,map_pow,aeval_C,aeval_X] using hs

theorem cap_positive {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) :
    0<aeval z capPolynomial := by
  have ht := negative_tail_lower hz
  have he := congrArg (fun p : ℚ[X] => aeval z p) cap_expansion
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at he
  have h0 : 0<(capPolynomial.coeff 0:ℝ) := by
    rw [cap_coefficients.1]
    norm_num
  have h1 : 0≤(capPolynomial.coeff 1:ℝ)*z := by
    rw [cap_coefficients.2.1]
    positivity
  have h2 : 0≤((capPolynomial.coeff 2:ℝ)+(negativeTail:ℝ))*z^2 := by
    have hh : (1079/10000:ℝ)<(capPolynomial.coeff 2:ℝ)+(negativeTail:ℝ) := by
      exact_mod_cast cap_coefficients.2.2
    exact mul_nonneg (by linarith) (sq_nonneg z)
  nlinarith

theorem Y_lt_YU {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) : Y z<YU z := by
  have hp := cap_positive hz
  rw [capPolynomial_eval] at hp
  have hxl := XL_lower hz
  have hxx := XL_le_X hz
  have hx := X_bounds hz
  have hsq : (XL z)^2≤(X z)^2 := by
    simpa only [pow_two] using
      mul_le_mul hxx hxx (by linarith : 0≤XL z) (by linarith [hx.1] : 0≤X z)
  have hy := Y_sq hz
  have hyn : 0≤Y z := Real.sqrt_nonneg _
  have hyu := YU_lower hz
  nlinarith

theorem domain_bounds {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) :
    (16007859/10000000:ℝ)<X z ∧ X z<212/125 ∧
      (509/500:ℝ)<Y z ∧ Y z<581611/500000 := by
  have hx := X_bounds hz
  have hy := Y_lower hz
  have hyu := Y_lt_YU hz
  have hyu' : YU z≤581611/500000 := by
    dsimp [YU]
    nlinarith [hz.1,sq_nonneg z]
  exact ⟨hx.1,hx.2,hy,hyu.trans_le hyu'⟩

open TensorWholeIntervalPolynomial

def leftVariable : Bivar := scalar (9/200)*(1+Polynomial.X)
def rightVariable : Bivar := scalar (9/200)*(1+Polynomial.C Polynomial.X)
def gapVariable : Bivar := scalar (21/100)-leftVariable-rightVariable

def C4tensor (z : Bivar) : Bivar := 1-scalar (1/2)*z^2+scalar (1/24)*z^4
def C6tensor (z : Bivar) : Bivar :=
  1-scalar (1/2)*z^2+scalar (1/24)*z^4-scalar (1/720)*z^6
def S7tensor (z : Bivar) : Bivar :=
  z-scalar (1/6)*z^3+scalar (1/120)*z^5-scalar (1/5040)*z^7
def XLtensor (z : Bivar) : Bivar :=
  1+scalar (6007859/10000000)*C6tensor z+scalar (13/12)*S7tensor z
def YUtensor (z : Bivar) : Bivar :=
  scalar (581611/500000)-scalar (3727/2500)*z-z^2

/-- Equation (14), already expressed on the complete centered square. -/
def squarePolynomial : Bivar :=
  1-YUtensor leftVariable-
    (YUtensor rightVariable-1)*C4tensor gapVariable+
      XLtensor rightVariable*S7tensor gapVariable

def tensorCoefficient (i j : ℕ) : ℚ :=
  TensorWholeIntervalPolynomial.coefficient 14 squarePolynomial i j

theorem square_expansion :
    squarePolynomial=TensorWholeIntervalPolynomial.expansion 14 squarePolynomial := by
  decide

/-- Exact rational multiplication of the single factored polynomial.
The inequalities are the two coefficient reserves in equation (18). -/
theorem tensor_coefficients :
    (135667/12500000:ℚ)<tensorCoefficient 0 0 ∧
      TensorWholeIntervalPolynomial.norm 14 tensorCoefficient<101827/12500000 := by
  decide

theorem square_reserve :
    (27/10000:ℚ)<TensorWholeIntervalPolynomial.lower 14
      (TensorWholeIntervalPolynomial.coefficient 14 squarePolynomial) := by
  have hh := tensor_coefficients
  change (27/10000:ℚ)<tensorCoefficient 0 0-
    TensorWholeIntervalPolynomial.norm 14 tensorCoefficient
  linarith

theorem leftVariable_eval (x y : ℝ) :
    evaluate x y leftVariable=(9/200)*(1+x) := by
  simp [leftVariable]

theorem rightVariable_eval (x y : ℝ) :
    evaluate x y rightVariable=(9/200)*(1+y) := by
  simp [rightVariable]

theorem gapVariable_eval (x y : ℝ) :
    evaluate x y gapVariable=21/100-(9/200)*(1+x)-(9/200)*(1+y) := by
  simp [gapVariable,leftVariable_eval,rightVariable_eval]

theorem C4tensor_eval (x y : ℝ) (z : Bivar) :
    evaluate x y (C4tensor z)=C4 (evaluate x y z) := by
  simp [C4tensor,C4] <;> ring

theorem C6tensor_eval (x y : ℝ) (z : Bivar) :
    evaluate x y (C6tensor z)=C6 (evaluate x y z) := by
  simp [C6tensor,C6] <;> ring

theorem S7tensor_eval (x y : ℝ) (z : Bivar) :
    evaluate x y (S7tensor z)=S7 (evaluate x y z) := by
  simp [S7tensor,S7] <;> ring

theorem XLtensor_eval (x y : ℝ) (z : Bivar) :
    evaluate x y (XLtensor z)=XL (evaluate x y z) := by
  simp [XLtensor,XL,C6tensor_eval,S7tensor_eval]

theorem YUtensor_eval (x y : ℝ) (z : Bivar) :
    evaluate x y (YUtensor z)=YU (evaluate x y z) := by
  simp [YUtensor,YU]

theorem squarePolynomial_eval (x y : ℝ) :
    evaluate x y squarePolynomial=
      1-YU ((9/200)*(1+x))-
        (YU ((9/200)*(1+y))-1)*C4 (21/100-(9/200)*(1+x)-(9/200)*(1+y))+
          XL ((9/200)*(1+y))*S7 (21/100-(9/200)*(1+x)-(9/200)*(1+y)) := by
  simp [squarePolynomial,YUtensor_eval,C4tensor_eval,XLtensor_eval,S7tensor_eval,
    leftVariable_eval,rightVariable_eval,gapVariable_eval]

theorem square_polynomial_positive {t u : ℝ}
    (ht : t∈Icc 0 (9/100:ℝ)) (hu : u∈Icc 0 (9/100:ℝ)) :
    (27/10000:ℝ)<1-YU t-(YU u-1)*C4 (21/100-t-u)+XL u*S7 (21/100-t-u) := by
  let x : ℝ := (200/9)*t-1
  let y : ℝ := (200/9)*u-1
  have hx : |x|≤1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith [ht.1,ht.2]
  have hy : |y|≤1 := by
    apply abs_le.mpr
    dsimp [y]
    constructor <;> linarith [hu.1,hu.2]
  have hxt : (9/200)*(1+x)=t := by dsimp [x]; ring
  have hyu : (9/200)*(1+y)=u := by dsimp [y]; ring
  have hp := TensorWholeIntervalPolynomial.positive_on_square
    square_expansion square_reserve hx hy
  rw [squarePolynomial_eval,hxt,hyu] at hp
  exact hp

/-- Sign-preserving transfer from the rational whole-square certificate
to the original radical cap, with a strict uniform reserve. -/
theorem square_strict_reserve {t u : ℝ}
    (ht : t∈Icc 0 (9/100:ℝ)) (hu : u∈Icc 0 (9/100:ℝ)) :
    Y t+(Y u-1)*Real.cos (21/100-t-u)-X u*Real.sin (21/100-t-u)-1<
      -(27/10000:ℝ) := by
  let v : ℝ := 21/100-t-u
  have hv : v∈Icc 0 (21/100:ℝ) := by
    dsimp [v]
    exact ⟨by linarith [ht.2,hu.2],by linarith [ht.1,hu.1]⟩
  have hc0 : 0≤Real.cos v := by
    have hh := Real.one_sub_sq_div_two_le_cos v
    have hv2 := pow_le_pow_left₀ hv.1 hv.2 2
    norm_num at hv2
    nlinarith
  have hcos : Real.cos v≤C4 v := cos_upper_four hv.1
  have hsin : S7 v≤Real.sin v := sin_lower_seven hv.1
  have hs0 := S7_nonneg hv
  have hyt := Y_lt_YU ht
  have hyu := Y_lt_YU hu
  have hyu0 : 0≤YU u-1 := by linarith [YU_lower hu]
  have hcos1 := mul_le_mul_of_nonneg_right (sub_le_sub_right hyu.le 1) hc0
  have hcos2 := mul_le_mul_of_nonneg_left hcos hyu0
  have hx0 : 0≤X u := by linarith [(X_bounds hu).1]
  have hsinprod : XL u*S7 v≤X u*Real.sin v :=
    mul_le_mul (XL_le_X hu) hsin hs0 hx0
  have hp := square_polynomial_positive ht hu
  change (27/10000:ℝ)<1-YU t-(YU u-1)*C4 v+XL u*S7 v at hp
  change Y t+(Y u-1)*Real.cos v-X u*Real.sin v-1<-(27/10000:ℝ)
  linarith

theorem square_negative {t u : ℝ}
    (ht : t∈Icc 0 (9/100:ℝ)) (hu : u∈Icc 0 (9/100:ℝ)) :
    Y t+(Y u-1)*Real.cos (21/100-t-u)-X u*Real.sin (21/100-t-u)-1<0 := by
  have hh := square_strict_reserve ht hu
  linarith

end SquaresInCircles.Eight.TableFree.BothNegativeSpanPolynomial
