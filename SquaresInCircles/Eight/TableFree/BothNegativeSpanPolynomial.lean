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

theorem m_bounds : (6007859/10000000:ℝ)< m ∧ m<300393/500000 := by
  have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hn := Real.sqrt_nonneg (qCap/2)
  simp only [m_identity]
  norm_num [qCap] at hs hn ⊢
  constructor <;> nlinarith

theorem X_eq (z : ℝ) : X z=1+m*Real.cos z+(13/12)*Real.sin z := rfl

theorem X_bounds {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) :
    (16007859/10000000:ℝ)<X z ∧ X z<212/125 := by
  have hm := m_bounds
  have hm0 : 0 ≤ m := by linarith
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
  have hclo := Real.one_sub_sq_div_two_le_cos (x := z)
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
    have hc := Real.one_sub_sq_div_two_le_cos (x := z)
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

/-! Exact rational coefficient lists: `r23ev l` is the polynomial with coefficient list `l`;
sums and products of lists are computed by the kernel. -/
private def r23ev : List ℚ → ℚ[X]
  | [] => 0
  | a :: l => C a + Polynomial.X * r23ev l

private def r23add : List ℚ → List ℚ → List ℚ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a+b) :: r23add l m

private def r23smul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (c*a) :: r23smul c l

private def r23mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: l, m => r23add (r23smul a m) (0 :: r23mul l m)

private def r23sub (l m : List ℚ) : List ℚ := r23add l (r23smul (-1) m)

private theorem r23ev_add (l m : List ℚ) : r23ev (r23add l m)=r23ev l+r23ev m := by
  induction l generalizing m with
  | nil => simp [r23add,r23ev]
  | cons a l ih =>
    cases m with
    | nil => simp [r23add,r23ev]
    | cons b m => simp only [r23add,r23ev,ih,map_add]; ring

private theorem r23ev_smul (c : ℚ) (l : List ℚ) : r23ev (r23smul c l)=C c*r23ev l := by
  induction l with
  | nil => simp [r23smul,r23ev]
  | cons a l ih => simp only [r23smul,r23ev,ih,map_mul]; ring

private theorem r23ev_mul (l m : List ℚ) : r23ev (r23mul l m)=r23ev l*r23ev m := by
  induction l with
  | nil => simp [r23mul,r23ev]
  | cons a l ih => simp only [r23mul,r23ev,r23ev_add,r23ev_smul,ih,map_zero]; ring

private theorem r23ev_sub (l m : List ℚ) : r23ev (r23sub l m)=r23ev l-r23ev m := by
  simp only [r23sub,r23ev_add,r23ev_smul,map_neg,map_one]; ring

private theorem r23ev_single (a : ℚ) : r23ev [a]=C a := by simp [r23ev]

private theorem r23ev_X : r23ev [0,1]=Polynomial.X := by simp [r23ev]

private theorem r23_coeff (l : List ℚ) (n : ℕ) : (r23ev l).coeff n=l.getD n 0 := by
  induction l generalizing n with
  | nil => simp [r23ev]
  | cons a l ih =>
    cases n with
    | zero => simp [r23ev]
    | succ n => simp [r23ev,ih]

private theorem r23_natDegree (l : List ℚ) (n : ℕ) (h : l.length≤n+1) :
    (r23ev l).natDegree≤n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [r23_coeff,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)]
  rfl

private def r23cos6L : List ℚ := [1,0,-(1/2),0,1/24,0,-(1/720)]
private def r23sin7L : List ℚ := [0,1,0,-(1/6),0,1/120,0,-(1/5040)]
private def r23XLL : List ℚ :=
  r23add (r23add [1] (r23smul (6007859/10000000) r23cos6L)) (r23smul (13/12) r23sin7L)
private def r23YUL : List ℚ := [581611/500000,-(3727/2500),-1]
private def r23capL : List ℚ :=
  r23sub (r23add (r23mul r23YUL r23YUL) (r23mul r23XLL r23XLL)) [9789/2500]

/-- The exact coefficients of `capPolynomial`, from degree `0` to degree `14`. -/
private def r23capval : List ℚ :=
  [(91892281/100000000000000),
      (266837/2500000000),
      (97129938125071/900000000000000),
      (52580611/30000000),
      (2103776155374929/2700000000000000),
      (28742389/150000000),
      (697606465250071/20250000000000000),
      -(1271959/75000000),
      -(47134492343879473/18144000000000000000),
      (3202188847/3628800000000),
      (6387304704875497/54432000000000000000),
      -(78102167/3024000000000),
      -(3467018234958499/1088640000000000000000),
      (78102167/217728000000000),
      (169/3657830400)]

private theorem r23capL_val : r23capL=r23capval := by decide +kernel

private theorem r23cos6 : cos6=r23ev r23cos6L := by
  simp only [cos6,r23cos6L,r23ev,map_neg,map_zero,map_one]; ring
private theorem r23sin7 : sin7=r23ev r23sin7L := by
  simp only [sin7,r23sin7L,r23ev,map_neg,map_zero,map_one]; ring
private theorem r23YU : YUpoly=r23ev r23YUL := by
  simp only [YUpoly,r23YUL,r23ev,map_neg,map_one]; ring

private theorem r23cap_ev : capPolynomial=r23ev r23capval := by
  rw [← r23capL_val]
  simp only [r23capL,r23XLL,r23ev_add,r23ev_sub,r23ev_mul,r23ev_smul,r23ev_single,map_one,
    ← r23cos6,← r23sin7,← r23YU]
  simp only [capPolynomial,XLpoly]
  ring

/-- Only negative higher coefficients enter the one-sided lower bound. -/
def negativeTail : ℚ :=
  ∑ j : Fin 12,min (capPolynomial.coeff (j.val+3)) 0*(9/100)^(j.val+1)

theorem cap_expansion : capPolynomial=
    C (capPolynomial.coeff 0)+C (capPolynomial.coeff 1)*Polynomial.X+
      C (capPolynomial.coeff 2)*Polynomial.X^2+
        PowerTailBounds.tail capPolynomial 3 12 := by
  have hdeg : capPolynomial.natDegree<15 := by
    rw [r23cap_ev]
    exact Nat.lt_succ_of_le (r23_natDegree _ 14 (by rfl))
  conv_lhs => rw [as_sum_range_C_mul_X_pow' capPolynomial hdeg]
  rw [show (15:ℕ)=3+12 from rfl,Finset.sum_range_add,PowerTailBounds.tail,
    Fin.sum_univ_eq_sum_range (fun j => C (capPolynomial.coeff (j+3))*Polynomial.X^(j+3)) 12]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,mul_one,zero_add]

theorem cap_coefficients :
    capPolynomial.coeff 0=91892281/100000000000000 ∧
    capPolynomial.coeff 1=266837/2500000000 ∧
    (1079/10000:ℚ)<capPolynomial.coeff 2+negativeTail := by
  simp only [negativeTail]
  rw [r23cap_ev]
  simp only [r23_coeff]
  decide +kernel

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
  simpa only [PowerTailBounds.tail,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] using hs

theorem cap_positive {z : ℝ} (hz : z∈Icc 0 (9/100:ℝ)) :
    0<aeval z capPolynomial := by
  have ht := negative_tail_lower hz
  have he := congrArg (fun p : ℚ[X] => aeval z p) cap_expansion
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have h0 : 0<(capPolynomial.coeff 0:ℝ) := by
    rw [cap_coefficients.1]
    norm_num
  have h1 : 0≤(capPolynomial.coeff 1:ℝ)*z := by
    rw [cap_coefficients.2.1]
    exact mul_nonneg (by norm_num) hz.1
  have h2 : 0≤((capPolynomial.coeff 2:ℝ)+(negativeTail:ℝ))*z^2 := by
    have hh : (1079/10000:ℝ)<(capPolynomial.coeff 2:ℝ)+(negativeTail:ℝ) := by
      have h := (Rat.cast_lt (K := ℝ)).mpr cap_coefficients.2.2
      push_cast at h
      exact h
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

/-! Exact coefficient lists of the bivariate polynomials: the outer list is indexed by the
power of the outer variable, each inner list by the power of the inner variable. -/
private def r23evB : List (List ℚ) → Bivar
  | [] => 0
  | l :: L => C (r23ev l) + Polynomial.X * r23evB L

private def r23addB : List (List ℚ) → List (List ℚ) → List (List ℚ)
  | [], M => M
  | l :: L, [] => l :: L
  | l :: L, m :: M => r23add l m :: r23addB L M

private def r23smulB (c : List ℚ) : List (List ℚ) → List (List ℚ)
  | [] => []
  | l :: L => r23mul c l :: r23smulB c L

private def r23mulB : List (List ℚ) → List (List ℚ) → List (List ℚ)
  | [], _ => []
  | l :: L, M => r23addB (r23smulB l M) ([] :: r23mulB L M)

private def r23subB (L M : List (List ℚ)) : List (List ℚ) := r23addB L (r23smulB [-1] M)

private theorem r23evB_add (L M : List (List ℚ)) :
    r23evB (r23addB L M)=r23evB L+r23evB M := by
  induction L generalizing M with
  | nil => simp [r23addB,r23evB]
  | cons l L ih =>
    cases M with
    | nil => simp [r23addB,r23evB]
    | cons m M => simp only [r23addB,r23evB,ih,r23ev_add,map_add]; ring

private theorem r23evB_smul (c : List ℚ) (L : List (List ℚ)) :
    r23evB (r23smulB c L)=C (r23ev c)*r23evB L := by
  induction L with
  | nil => simp [r23smulB,r23evB]
  | cons l L ih => simp only [r23smulB,r23evB,ih,r23ev_mul,map_mul]; ring

private theorem r23evB_mul (L M : List (List ℚ)) :
    r23evB (r23mulB L M)=r23evB L*r23evB M := by
  induction L with
  | nil => simp [r23mulB,r23evB]
  | cons l L ih =>
    simp only [r23mulB,r23evB,r23evB_add,r23evB_smul,ih,r23ev,map_zero]
    ring

private theorem r23evB_sub (L M : List (List ℚ)) :
    r23evB (r23subB L M)=r23evB L-r23evB M := by
  simp only [r23subB,r23evB_add,r23evB_smul,r23ev_single,map_neg,map_one]; ring

private theorem r23evB_single (l : List ℚ) : r23evB [l]=C (r23ev l) := by simp [r23evB]

private theorem r23B_coeff (L : List (List ℚ)) (a : ℕ) :
    (r23evB L).coeff a=r23ev (L.getD a []) := by
  induction L generalizing a with
  | nil => simp [r23evB,r23ev]
  | cons l L ih =>
    cases a with
    | zero => simp [r23evB]
    | succ a => simp [r23evB,ih]

private theorem r23B_natDegree (L : List (List ℚ)) (n : ℕ) (h : L.length≤n+1) :
    (r23evB L).natDegree≤n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [r23B_coeff,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)]
  simp [r23ev]

private theorem r23_zero (l : List ℚ) (h : l.all (fun x => decide (x=0))=true) :
    r23ev l=0 := by
  induction l with
  | nil => simp [r23ev]
  | cons a l ih =>
    simp only [List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at h
    simp [r23ev,h.1,ih h.2]

private theorem r23B_zero (L : List (List ℚ))
    (h : L.all (fun l => l.all (fun x => decide (x=0)))=true) : r23evB L=0 := by
  induction L with
  | nil => simp [r23evB]
  | cons l L ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    simp [r23evB,r23_zero l h.1,ih h.2]

private def r23leftL : List (List ℚ) := [[9/200],[9/200]]
private def r23rightL : List (List ℚ) := [[9/200,9/200]]
private def r23gapL : List (List ℚ) := r23subB (r23subB [[21/100]] r23leftL) r23rightL
private def r23sqB (Z : List (List ℚ)) : List (List ℚ) := r23mulB Z Z
private def r23C4B (Z : List (List ℚ)) : List (List ℚ) :=
  r23addB (r23subB [[1]] (r23smulB [1/2] (r23sqB Z))) (r23smulB [1/24] (r23sqB (r23sqB Z)))
private def r23C6B (Z : List (List ℚ)) : List (List ℚ) :=
  r23subB (r23C4B Z) (r23smulB [1/720] (r23mulB (r23sqB Z) (r23sqB (r23sqB Z))))
private def r23S7B (Z : List (List ℚ)) : List (List ℚ) :=
  r23subB (r23addB (r23subB Z (r23smulB [1/6] (r23mulB Z (r23sqB Z))))
      (r23smulB [1/120] (r23mulB Z (r23sqB (r23sqB Z)))))
    (r23smulB [1/5040] (r23mulB (r23mulB Z (r23sqB Z)) (r23sqB (r23sqB Z))))
private def r23XLB (Z : List (List ℚ)) : List (List ℚ) :=
  r23addB (r23addB [[1]] (r23smulB [6007859/10000000] (r23C6B Z))) (r23smulB [13/12] (r23S7B Z))
private def r23YUB (Z : List (List ℚ)) : List (List ℚ) :=
  r23subB (r23subB [[581611/500000]] (r23smulB [3727/2500] Z)) (r23sqB Z)
private def r23sqL : List (List ℚ) :=
  r23addB (r23subB (r23subB [[1]] (r23YUB r23leftL))
      (r23mulB (r23subB (r23YUB r23rightL) [[1]]) (r23C4B r23gapL)))
    (r23mulB (r23XLB r23rightL) (r23S7B r23gapL))

/-- The exact coefficients of `squarePolynomial`. -/
private def r23SQval : List (List ℚ) :=
  [[(12065750317108906760649766737909541/1225000000000000000000000000000000000),
        (2988336595473418481110453674209301/1400000000000000000000000000000000000),
        (141281393579960155201784320789419/1600000000000000000000000000000000000),
        -(1244027342801258967464945015457609/89600000000000000000000000000000000000),
        -(89266077045194208099509607920631/143360000000000000000000000000000000000),
        -(6658576510213554702675090053337/1146880000000000000000000000000000000000),
        -(648639944606724298421093606313/9175040000000000000000000000000000000000),
        (1300918799210873557291128599643/513802240000000000000000000000000000000000),
        (2206654982514277911144233289/36700160000000000000000000000000000000000),
        -(19511746195324321135048293/73400320000000000000000000000000000000000),
        -(118888171374593826301941/22937600000000000000000000000000000000000),
        (826701509060026618473/52428800000000000000000000000000000000000),
        (46478894339957693913/183500800000000000000000000000000000000000),
        -(163035870469154631/367001600000000000000000000000000000000000),
        -(1223861324751/205520896000000000000000000000000000000)],
      [-(4253731663078381116033734671956123/1400000000000000000000000000000000000),
        -(2182593186704432611509740867077119/1120000000000000000000000000000000000),
        -(3508676868183216496108568570933163/89600000000000000000000000000000000000),
        -(9793197813568230130827865456647/7168000000000000000000000000000000000),
        -(2230775699993530951909373733069/1146880000000000000000000000000000000000),
        (119042519926399244809907639337/917504000000000000000000000000000000000),
        (669570150592707900259908232683/73400320000000000000000000000000000000000),
        (1763849462314487142127018239/7340032000000000000000000000000000000000),
        -(91079984698655154827866371/73400320000000000000000000000000000000000),
        -(47471650990417098310203/1835008000000000000000000000000000000000),
        (34746959738416090176297/367001600000000000000000000000000000000000),
        (55689600241133896167/36700160000000000000000000000000000000000),
        -(1182046470775782417/367001600000000000000000000000000000000000),
        -(1223861324751/29360128000000000000000000000000000000)],
      [(21501077663536614411192485921811357/11200000000000000000000000000000000000),
        -(193477776660607008568128038700219/89600000000000000000000000000000000000),
        -(6523980311045420190940079411469/71680000000000000000000000000000000000),
        (8446856320135774556412707296323/573440000000000000000000000000000000000),
        (4567137855920759031713628976809/9175040000000000000000000000000000000000),
        (1061655738851204054358165650097/73400320000000000000000000000000000000000),
        (2202781826080541960617604787/5242880000000000000000000000000000000000),
        -(184448012857774797891570057/73400320000000000000000000000000000000000),
        -(32444040854863595128743/573440000000000000000000000000000000000),
        (17869006497241462839471/73400320000000000000000000000000000000000),
        (717132143191438512837/183500800000000000000000000000000000000000),
        -(3668525544802447251/367001600000000000000000000000000000000000),
        -(3671583974253/29360128000000000000000000000000000000)],
      [(448614027261558839133764466323643/17920000000000000000000000000000000000),
        (23544249187387168585938974984037/35840000000000000000000000000000000000),
        (7874097290304518778307148174067/573440000000000000000000000000000000000),
        (729400317811468008858846974043/2293760000000000000000000000000000000000),
        (980303809844629697256647844471/73400320000000000000000000000000000000000),
        (2199939146217197159228012169/5242880000000000000000000000000000000000),
        -(30767164573777432742356857/10485760000000000000000000000000000000000),
        -(653731378957599733281933/9175040000000000000000000000000000000000),
        (25733112307006184773641/73400320000000000000000000000000000000000),
        (207140399954133927723/36700160000000000000000000000000000000000),
        -(1263637225759182417/73400320000000000000000000000000000000000),
        -(1223861324751/5872025600000000000000000000000000000)],
      [(2529866485834345665579933975321/143360000000000000000000000000000000000),
        (617984187007714650366342110019/1146880000000000000000000000000000000000),
        -(117702390171685741742379638619/1835008000000000000000000000000000000000),
        (585772674235613129942998712199/73400320000000000000000000000000000000000),
        (1370789994017062092970608957/5242880000000000000000000000000000000000),
        -(22915277374899513677612409/10485760000000000000000000000000000000000),
        -(36980095682004430694427/655360000000000000000000000000000000000),
        (4544369853066633419973/14680064000000000000000000000000000000000),
        (182737057876632751167/36700160000000000000000000000000000000000),
        -(1304432603250882417/73400320000000000000000000000000000000000),
        -(1223861324751/5872025600000000000000000000000000000)],
      [-(14435384541976318294269522205389/5734400000000000000000000000000000000000),
        -(1976875639177192722816067421919/22937600000000000000000000000000000000000),
        (1165609716706148765025424366341/367001600000000000000000000000000000000000),
        (2722451961733308805431949011/26214400000000000000000000000000000000000),
        -(11105931505045875468701679/10485760000000000000000000000000000000000),
        -(185792212101477626960211/6553600000000000000000000000000000000000),
        (8943631483923952219053/52428800000000000000000000000000000000000),
        (497502064493927923833/183500800000000000000000000000000000000000),
        -(4035683942227747251/367001600000000000000000000000000000000000),
        -(3671583974253/29360128000000000000000000000000000000)],
      [-(104688526090078053705419580861/45875200000000000000000000000000000000000),
        (57989492592592319070859072251/73400320000000000000000000000000000000000),
        (669857533905746355315597477/26214400000000000000000000000000000000000),
        -(3342920685615325383137829/10485760000000000000000000000000000000000),
        -(2775681162318315171843/327680000000000000000000000000000000000),
        (2899081427225740829631/52428800000000000000000000000000000000000),
        (4469465451947531373/5242880000000000000000000000000000000000),
        -(1386023358234282417/367001600000000000000000000000000000000000),
        -(1223861324751/29360128000000000000000000000000000000)],
      [(314065578270234161116258742583/2569011200000000000000000000000000000000000),
        (92288706532930736334043551/26214400000000000000000000000000000000000),
        -(3575488226284680146593893/73400320000000000000000000000000000000000),
        -(10901603468876004537003/9175040000000000000000000000000000000000),
        (603363541191768451107/73400320000000000000000000000000000000000),
        (22075552262456517357/183500800000000000000000000000000000000000),
        -(203831247960854631/367001600000000000000000000000000000000000),
        -(1223861324751/205520896000000000000000000000000000000)]]

private theorem r23left_ev : r23evB r23leftL=leftVariable := by
  simp only [r23leftL,leftVariable,scalar,r23evB,r23ev,mul_zero,add_zero]; ring
private theorem r23right_ev : r23evB r23rightL=rightVariable := by
  simp only [r23rightL,rightVariable,scalar,r23evB,r23ev,mul_zero,add_zero,map_add,map_mul]
  ring
private theorem r23gap_ev : r23evB r23gapL=gapVariable := by
  simp only [r23gapL,gapVariable,r23evB_sub,r23left_ev,r23right_ev,r23evB_single,r23ev_single,
    scalar]

private theorem r23C4B_ev (Z : List (List ℚ)) : r23evB (r23C4B Z)=C4tensor (r23evB Z) := by
  simp only [r23C4B,r23sqB,r23evB_add,r23evB_sub,r23evB_smul,r23evB_mul,r23evB_single,
    r23ev_single,map_one]
  simp only [C4tensor,scalar]
  ring
private theorem r23C6B_ev (Z : List (List ℚ)) : r23evB (r23C6B Z)=C6tensor (r23evB Z) := by
  simp only [r23C6B,r23C4B_ev,r23sqB,r23evB_sub,r23evB_smul,r23evB_mul,r23ev_single]
  simp only [C6tensor,C4tensor,scalar]
  ring
private theorem r23S7B_ev (Z : List (List ℚ)) : r23evB (r23S7B Z)=S7tensor (r23evB Z) := by
  simp only [r23S7B,r23sqB,r23evB_add,r23evB_sub,r23evB_smul,r23evB_mul,r23ev_single]
  simp only [S7tensor,scalar]
  ring
private theorem r23XLB_ev (Z : List (List ℚ)) : r23evB (r23XLB Z)=XLtensor (r23evB Z) := by
  simp only [r23XLB,r23C6B_ev,r23S7B_ev,r23evB_add,r23evB_smul,r23evB_single,r23ev_single,
    map_one]
  simp only [XLtensor,scalar]
private theorem r23YUB_ev (Z : List (List ℚ)) : r23evB (r23YUB Z)=YUtensor (r23evB Z) := by
  simp only [r23YUB,r23sqB,r23evB_sub,r23evB_smul,r23evB_mul,r23evB_single,r23ev_single]
  simp only [YUtensor,scalar]
  ring

private theorem r23sqL_ev : r23evB r23sqL=squarePolynomial := by
  simp only [r23sqL,r23evB_add,r23evB_sub,r23evB_mul,r23evB_single,r23ev_single,map_one,
    r23YUB_ev,r23C4B_ev,r23XLB_ev,r23S7B_ev,r23left_ev,r23right_ev,r23gap_ev]
  simp only [squarePolynomial]

private theorem r23sq_check :
    (r23subB r23sqL r23SQval).all (fun l => l.all (fun x => decide (x=0)))=true := by
  decide +kernel

private theorem r23sq_ev : squarePolynomial=r23evB r23SQval := by
  have h := r23B_zero _ r23sq_check
  rw [r23evB_sub,sub_eq_zero,r23sqL_ev] at h
  exact h

/-! The monomials as exact combinations of Chebyshev polynomials, up to degree fourteen. -/
private def r23Tpair : ℕ → List ℚ × List ℚ
  | 0 => ([1],[0,1])
  | n+1 => ((r23Tpair n).2,r23sub (r23mul [0,2] (r23Tpair n).2) (r23Tpair n).1)

private theorem r23T (n : ℕ) :
    Polynomial.Chebyshev.T ℚ n=r23ev (r23Tpair n).1 ∧
      Polynomial.Chebyshev.T ℚ ((n:ℤ)+1)=r23ev (r23Tpair n).2 := by
  induction n with
  | zero =>
    simp [r23Tpair,r23ev,Polynomial.Chebyshev.T_zero,Polynomial.Chebyshev.T_one]
  | succ n ih =>
    constructor
    · simp only [r23Tpair]
      exact_mod_cast ih.2
    · have h2 := Polynomial.Chebyshev.T_add_two ℚ (n:ℤ)
      have e : ((n+1:ℕ):ℤ)+1=(n:ℤ)+2 := by push_cast; ring
      rw [e,h2,ih.2,ih.1]
      simp only [r23Tpair,r23ev_sub,r23ev_mul,r23ev,map_zero,map_ofNat,mul_zero,add_zero,
        zero_add]
      ring

private def r23sumL (f : ℕ → List ℚ) : ℕ → List ℚ
  | 0 => []
  | n+1 => r23add (r23sumL f n) (f n)

private theorem r23ev_sumL (f : ℕ → List ℚ) (n : ℕ) :
    r23ev (r23sumL f n)=∑ i ∈ Finset.range n,r23ev (f i) := by
  induction n with
  | zero => simp [r23sumL,r23ev]
  | succ n ih => rw [r23sumL,r23ev_add,ih,Finset.sum_range_succ]

private def r23Xpow : ℕ → List ℚ
  | 0 => [1]
  | n+1 => 0 :: r23Xpow n

private theorem r23ev_Xpow (n : ℕ) : r23ev (r23Xpow n)=Polynomial.X^n := by
  induction n with
  | zero => simp [r23Xpow,r23ev]
  | succ n ih => simp only [r23Xpow,r23ev,ih,map_zero,zero_add]; ring

private theorem r23mono_check : ∀ a<15,
    (r23sub (r23Xpow a) (r23sumL (fun i => r23smul
      (WholeIntervalPolynomial.monomialCoefficient a i) (r23Tpair i).1) 15)).all
        (fun x => decide (x=0))=true := by
  decide +kernel

private theorem r23mono {a : ℕ} (ha : a<15) :
    (Polynomial.X:ℚ[X])^a=∑ i ∈ Finset.range 15,
      C (WholeIntervalPolynomial.monomialCoefficient a i)*Polynomial.Chebyshev.T ℚ i := by
  have h := r23_zero _ (r23mono_check a ha)
  rw [r23ev_sub,sub_eq_zero,r23ev_Xpow,r23ev_sumL] at h
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [r23ev_smul,(r23T i).1]

private theorem r23monoX {a : ℕ} (ha : a<15) :
    (Polynomial.X:Bivar)^a=∑ i : Fin (14+1),
      scalar (WholeIntervalPolynomial.monomialCoefficient a i)*
        Polynomial.Chebyshev.T (Polynomial ℚ) (i:ℕ) := by
  have h := congrArg (Polynomial.map (C : ℚ →+* ℚ[X])) (r23mono ha)
  simp only [Polynomial.map_pow,Polynomial.map_X,Polynomial.map_sum,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.Chebyshev.map_T] at h
  rw [h,Fin.sum_univ_eq_sum_range (fun i => scalar (WholeIntervalPolynomial.monomialCoefficient a i)*
    Polynomial.Chebyshev.T (Polynomial ℚ) (i:ℕ)) (14+1)]
  rfl

private theorem r23monoY {b : ℕ} (hb : b<15) :
    (C (Polynomial.X^b) : Bivar)=∑ j : Fin (14+1),
      scalar (WholeIntervalPolynomial.monomialCoefficient b j)*
        C (Polynomial.Chebyshev.T ℚ (j:ℕ)) := by
  rw [r23mono hb,map_sum,Fin.sum_univ_eq_sum_range (fun j => scalar
    (WholeIntervalPolynomial.monomialCoefficient b j)*C (Polynomial.Chebyshev.T ℚ (j:ℕ))) (14+1)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [scalar,map_mul]

private theorem r23_series_full (c : ℕ → ℕ → ℚ) :
    TensorWholeIntervalPolynomial.series 14 c=
      ∑ i : Fin (14+1),∑ j : Fin (14+1),
        scalar (c i j)*TensorWholeIntervalPolynomial.basis i j := by
  rw [← Fintype.sum_prod_type' (fun (i j : Fin (14+1)) =>
      scalar (c i j)*TensorWholeIntervalPolynomial.basis i j),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ((0:Fin (14+1)),(0:Fin (14+1))))]
  simp only [TensorWholeIntervalPolynomial.series,TensorWholeIntervalPolynomial.indices]
  congr 1
  simp [TensorWholeIntervalPolynomial.basis]

private theorem r23_swap4 {M : Type*} [AddCommMonoid M]
    (F : Fin (14+1) → Fin (14+1) → Fin (14+1) → Fin (14+1) → M) :
    ∑ a,∑ b,∑ i,∑ j,F a b i j=∑ i,∑ j,∑ a,∑ b,F a b i j := by
  calc ∑ a,∑ b,∑ i,∑ j,F a b i j=∑ a,∑ i,∑ b,∑ j,F a b i j :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _=∑ a,∑ i,∑ j,∑ b,F a b i j :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _=∑ i,∑ a,∑ j,∑ b,F a b i j := Finset.sum_comm
    _=∑ i,∑ j,∑ a,∑ b,F a b i j := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

theorem square_expansion :
    squarePolynomial=TensorWholeIntervalPolynomial.expansion 14 squarePolynomial := by
  have hrows : ∀ l∈r23SQval,l.length≤15 := by decide +kernel
  have hp : squarePolynomial.natDegree<15 := by
    rw [r23sq_ev]
    exact Nat.lt_succ_of_le (r23B_natDegree _ 14 (by decide))
  have hq : ∀ a,(squarePolynomial.coeff a).natDegree<15 := by
    intro a
    rw [r23sq_ev,r23B_coeff]
    apply Nat.lt_succ_of_le
    apply r23_natDegree
    rw [List.getD_eq_getElem?_getD]
    cases h : r23SQval[a]? with
    | none => simp
    | some l => exact hrows l (List.mem_of_getElem? h)
  have hsplit : squarePolynomial=∑ a : Fin (14+1),∑ b : Fin (14+1),∑ i : Fin (14+1),
      ∑ j : Fin (14+1),scalar ((squarePolynomial.coeff a).coeff b*
        WholeIntervalPolynomial.monomialCoefficient a i*
          WholeIntervalPolynomial.monomialCoefficient b j)*
        TensorWholeIntervalPolynomial.basis i j := by
    conv_lhs => rw [as_sum_range_C_mul_X_pow' squarePolynomial hp]
    rw [← Fin.sum_univ_eq_sum_range (fun a => C (squarePolynomial.coeff a)*Polynomial.X^a) (14+1)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    conv_lhs => rw [as_sum_range_C_mul_X_pow' (squarePolynomial.coeff a) (hq a)]
    rw [← Fin.sum_univ_eq_sum_range (fun b => C ((squarePolynomial.coeff a).coeff b)*
      Polynomial.X^b) (14+1),map_sum,Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [map_mul,r23monoY b.2,r23monoX a.2,Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [TensorWholeIntervalPolynomial.basis,scalar,map_mul]
    ring
  rw [TensorWholeIntervalPolynomial.expansion,r23_series_full]
  conv_lhs => rw [hsplit]
  rw [r23_swap4]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [TensorWholeIntervalPolynomial.coefficient,scalar,map_sum,Finset.sum_mul]

/-! The tensor coefficients, computed row by row: first the inner Chebyshev coefficients of every
outer coefficient, then the outer ones. -/
private def r23dotL : List ℚ → (ℕ → ℚ) → ℚ
  | [], _ => 0
  | x :: l, f => x*f 0+r23dotL l (fun k => f (k+1))

private theorem r23dotL_eq (l : List ℚ) (f : ℕ → ℚ) (n : ℕ) (h : l.length≤n) :
    r23dotL l f=∑ b ∈ Finset.range n,l.getD b 0*f b := by
  induction l generalizing f n with
  | nil => simp [r23dotL]
  | cons x l ih =>
    obtain ⟨m,rfl⟩ : ∃ m,n=m+1 := ⟨n-1,by simp at h; omega⟩
    rw [Finset.sum_range_succ',r23dotL,ih (fun k => f (k+1)) m (by simp at h; omega)]
    simp only [List.getD_cons_succ,List.getD_cons_zero]
    ring

private theorem r23getD_range {α : Type*} (f : ℕ → α) {n i : ℕ} (d : α) (h : i<n) :
    ((List.range n).map f).getD i d=f i := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range h]
  rfl

private def r23Qrow (row : List ℚ) : List ℚ :=
  (List.range 15).map (fun j =>
    r23dotL row (fun b => WholeIntervalPolynomial.monomialCoefficient b j))
private def r23Q : List (List ℚ) := r23SQval.map r23Qrow
private def r23Ctab : List (List ℚ) :=
  (List.range 15).map (fun i => (List.range 15).map (fun j =>
    r23dotL (r23Q.map (fun r => r.getD j 0))
      (fun a => WholeIntervalPolynomial.monomialCoefficient a i)))

private theorem r23col (L : List (List ℚ)) (a j : ℕ) :
    (L.map (fun r => r.getD j 0)).getD a 0=(L.getD a []).getD j 0 := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getD_eq_getElem?_getD (l := L)]
  cases L[a]? <;> simp

private theorem r23Q_entry (a j : ℕ) (hj : j<15) :
    (r23Q.getD a []).getD j 0=∑ b ∈ Finset.range 15,
      (r23SQval.getD a []).getD b 0*WholeIntervalPolynomial.monomialCoefficient b j := by
  have hrows : ∀ l∈r23SQval,l.length≤15 := by decide +kernel
  rw [r23Q,List.getD_eq_getElem?_getD (l := List.map r23Qrow r23SQval),List.getElem?_map,
    List.getD_eq_getElem?_getD (l := r23SQval)]
  cases h : r23SQval[a]? with
  | none => simp
  | some row =>
    simp only [Option.map_some,Option.getD_some,r23Qrow]
    rw [r23getD_range _ _ hj,r23dotL_eq _ _ 15 (hrows row (List.mem_of_getElem? h))]

private theorem r23C_entry (i j : ℕ) (hi : i<15) (hj : j<15) :
    TensorWholeIntervalPolynomial.coefficient 14 squarePolynomial i j=
      (r23Ctab.getD i []).getD j 0 := by
  rw [r23Ctab,r23getD_range _ _ hi,r23getD_range _ _ hj,
    r23dotL_eq _ _ 15 (by simp [r23Q,r23SQval])]
  simp only [r23col,r23Q_entry _ _ hj,Finset.sum_mul]
  rw [TensorWholeIntervalPolynomial.coefficient,r23sq_ev]
  simp only [r23B_coeff,r23_coeff]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (14+1),
    (r23SQval.getD a []).getD b 0*WholeIntervalPolynomial.monomialCoefficient a i*
      WholeIntervalPolynomial.monomialCoefficient b j) (14+1)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Fin.sum_univ_eq_sum_range (fun b => (r23SQval.getD a []).getD b 0*
    WholeIntervalPolynomial.monomialCoefficient a i*
      WholeIntervalPolynomial.monomialCoefficient b j) (14+1)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- Exact rational multiplication of the single factored polynomial.
The inequalities are the two coefficient reserves in equation (18). -/
theorem tensor_coefficients :
    (135667/12500000:ℚ)<tensorCoefficient 0 0 ∧
      TensorWholeIntervalPolynomial.norm 14 tensorCoefficient<101827/12500000 := by
  have hn : TensorWholeIntervalPolynomial.norm 14 tensorCoefficient=
      ∑ ij ∈ TensorWholeIntervalPolynomial.indices 14,
        |(r23Ctab.getD ij.1.val []).getD ij.2.val 0| :=
    Finset.sum_congr rfl (fun ij _ => by rw [tensorCoefficient,r23C_entry _ _ ij.1.2 ij.2.2])
  rw [hn,tensorCoefficient,r23C_entry 0 0 (by norm_num) (by norm_num)]
  decide +kernel

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
  have h27 : ((27/10000:ℚ):ℝ)=27/10000 := by norm_num
  rw [h27] at hp
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
    have hh := Real.one_sub_sq_div_two_le_cos (x := v)
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
  change Y t+(Y u-1)*Real.cos v-X u*Real.sin v-1 < -(27/10000:ℝ)
  linarith

theorem square_negative {t u : ℝ}
    (ht : t∈Icc 0 (9/100:ℝ)) (hu : u∈Icc 0 (9/100:ℝ)) :
    Y t+(Y u-1)*Real.cos (21/100-t-u)-X u*Real.sin (21/100-t-u)-1<0 := by
  have hh := square_strict_reserve ht hu
  linarith

end SquaresInCircles.Eight.TableFree.BothNegativeSpanPolynomial
