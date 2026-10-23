module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoLabels
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoInverseBounds

/-!
# Whole-domain polynomials for fixed-target contact concavity

The early-circle half uses two exact polynomials in its shifted primary
coordinate.  Their single expansions have positive remainders throughout
the whole interval.  On the late-circle half, two concave polynomials
give the required rational derivative bounds from their endpoints.
There is no interval mesh or asserted coefficient-table premise.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.ContactPolynomial

open CommonQuarter CorePairGeometry Arithmetic
open Inverse (q N K factorD)

def early : Set ℝ := Icc (17/10) (383/200)
def late : Set ℝ := Icc (1399/1000) (171/100)

def R (u : ℝ) : ℝ :=
  Q0*q u*(q u-1/4)-u*(Q0-u^2)*(3*q u-1/2)

def A (u : ℝ) : ℝ :=
  (Q0-u^2)*(N u)^2*(q u-4/25)-(4/25)*(K u)^2

lemma R_expansion (y : ℝ) :
    R (17/10+y)=1777364861/3906250000+(12376707/1562500)*y+
      y^2*(194367/25000-(66383/2500)*y-6*y^2) := by
  norm_num [R,q,Inverse.q,Q0]
  ring

lemma R_positive {u : ℝ} (hu : u∈early) : 0<R u := by
  let y : ℝ := u-17/10
  have hy : y∈Icc 0 (43/200) := by
    dsimp [early] at hu
    dsimp [y]
    constructor <;> linarith [hu.1,hu.2]
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hbracket : 0<(194367/25000:ℝ)-(66383/2500)*y-6*y^2 := by
    nlinarith [hy.2]
  have hprod := mul_nonneg (sq_nonneg y) hbracket.le
  have he := R_expansion y
  have hh : 17/10+y=u := by dsimp [y]; ring
  rw [hh] at he
  nlinarith [hy.1]

def lower (y : ℝ) : ℝ :=
  347/100+(523/25)*y+y^2*(-2114/25-(40261/100)*y+
    (1295/2)*y^2-(2251/25)*y^3-(5057/100)*y^4)

def remainder (y : ℝ) : ℝ :=
  212203130934677909/61035156250000000000+
    (2285349186678467/488281250000000000)*y+
    (235719982588451/97656250000000000)*y^2+
    (31285343561/3906250000000)*y^3+
    (20299879/3906250000)*y^4+(3947/781250)*y^5+(21/2500)*y^6+8*y^7

lemma A_expansion (y : ℝ) : A (17/10+y)=lower y+remainder y := by
  norm_num [A,lower,remainder,q,N,K,Inverse.q,Inverse.N,Inverse.K,Q0]
  ring

lemma remainder_positive {y : ℝ} (hy : 0≤y) : 0<remainder y := by
  dsimp [remainder]
  positivity

lemma lower_bracket {y : ℝ} (hy : y∈Icc 0 (43/200)) :
    -(143:ℝ)< -2114/25-(40261/100)*y+(1295/2)*y^2-
      (2251/25)*y^3-(5057/100)*y^4 := by
  have hdecrease := mul_nonneg (show 0≤(43/200:ℝ)-y by linarith [hy.2])
    (show 0≤(40261/100:ℝ)-(1295/2)*(y+43/200) by linarith [hy.2])
  have hy3 := pow_le_pow_left₀ hy.1 hy.2 3
  have hy4 := pow_le_pow_left₀ hy.1 hy.2 4
  nlinarith

lemma lower_positive {y : ℝ} (hy : y∈Icc 0 (43/200)) : 1<lower y := by
  have hbracket : 0≤ -2114/25-(40261/100)*y+(1295/2)*y^2-
      (2251/25)*y^3-(5057/100)*y^4+143 := by
    linarith [lower_bracket hy]
  have hb := mul_nonneg (sq_nonneg y) hbracket
  have hquad := mul_nonneg hy.1 (show 0≤(43/200:ℝ)-y by linarith [hy.2])
  dsimp [lower]
  nlinarith [hy.2]

lemma A_positive {u : ℝ} (hu : u∈early) : 1<A u := by
  let y : ℝ := u-17/10
  have hy : y∈Icc 0 (43/200) := by
    dsimp [early] at hu
    dsimp [y]
    constructor <;> linarith [hu.1,hu.2]
  have he := A_expansion y
  have hh : 17/10+y=u := by dsimp [y]; ring
  rw [hh] at he
  linarith [lower_positive hy,remainder_positive hy.1]

lemma N_positive {u : ℝ} (hu : u∈early) : 0<N u := by
  have hp := mul_nonneg (show 0≤u-17/10 from sub_nonneg.mpr hu.1)
    (show 0≤4*Q0-2*(u+17/10) by norm_num [Q0]; linarith [hu.2])
  norm_num [N,Inverse.N,Q0]
  nlinarith

lemma K_positive {u : ℝ} (hu : u∈early) : 0<K u := by
  let y : ℝ := u-17/10
  have hy : 0≤y := by dsimp [y]; linarith [hu.1]
  have he : K u=K (17/10)+(804/125)*y+(153/10)*y^2+3*y^3 := by
    dsimp [y,K,Inverse.K]
    norm_num [Q0]
    ring
  rw [he]
  norm_num [K,Inverse.K,Q0]
  positivity

lemma late_full {u : ℝ} (hu : u∈late) : u∈OppositeTwo.Inverse.interval :=
  ⟨hu.1,by linarith [hu.2]⟩

def lateUpper (u : ℝ) : ℝ := (11/100)*OppositeTwo.Inverse.mass u-K u
def lateUpperD (u : ℝ) : ℝ :=
  -(22/25)*u^3+3*((11/100)*(Q0+1)-3)*u^2+5*Q0
def lateUpperDD (u : ℝ) : ℝ :=
  -(66/25)*u^2+6*((11/100)*(Q0+1)-3)*u

lemma lateUpper_hasDerivAt (u : ℝ) : HasDerivAt lateUpper (lateUpperD u) u := by
  have hK := ((((hasDerivAt_id u).pow 3).const_mul 3).sub
    ((hasDerivAt_id u).const_mul (5*Q0))).add_const (Q0*(Q0+1))
  convert ((OppositeTwo.Inverse.mass_hasDerivAt u).const_mul (11/100)).sub hK using 1 <;>
    dsimp [lateUpper,lateUpperD,OppositeTwo.Inverse.massD,K,Inverse.K] <;> ring

lemma lateUpperD_hasDerivAt (u : ℝ) : HasDerivAt lateUpperD (lateUpperDD u) u := by
  convert (((((hasDerivAt_id u).pow 3).const_mul (-(22/25:ℝ))).add
    (((hasDerivAt_id u).pow 2).const_mul (3*((11/100)*(Q0+1)-3)))).add_const
      (5*Q0)) using 1 <;> dsimp [lateUpperD,lateUpperDD] <;> ring

lemma lateUpper_positive {u : ℝ} (hu : u∈late) : 0<lateUpper u :=
  positive_of_second_nonpos hu
    (fun t _ => lateUpper_hasDerivAt t) (fun t _ => lateUpperD_hasDerivAt t)
    (fun t ht => by
      have hp : 0≤t := by linarith [ht.1]
      norm_num [lateUpperDD,Q0]
      nlinarith [sq_nonneg t])
    (by norm_num [lateUpper,OppositeTwo.Inverse.mass,K,Inverse.K,
      OppositeTwo.Inverse.q,Inverse.q,Q0])
    (by norm_num [lateUpper,OppositeTwo.Inverse.mass,K,Inverse.K,
      OppositeTwo.Inverse.q,Inverse.q,Q0])

lemma late_K0 {u : ℝ} (hu : u∈late) :
    -(1/500:ℝ)<K u/OppositeTwo.Inverse.mass u ∧
      K u/OppositeTwo.Inverse.mass u<11/100 := by
  have hm := OppositeTwo.Inverse.mass_lower (late_full hu)
  refine ⟨(OppositeTwo.Inverse.K0_bounds (late_full hu)).1,?_⟩
  apply (div_lt_iff₀ (by linarith : 0<OppositeTwo.Inverse.mass u)).2
  have hh := lateUpper_positive hu
  dsimp [lateUpper] at hh
  linarith

def derivativeNumerator (u : ℝ) : ℝ := N u+(18/125)*u^2*(q u)^2
def derivativeNumeratorD (u : ℝ) : ℝ :=
  9789/625+(577925689/195312500)*u-(663606/78125)*u^2+(288/125)*u^3
def derivativeNumeratorDD (u : ℝ) : ℝ :=
  577925689/195312500-(1327212/78125)*u+(864/125)*u^2

lemma derivativeNumerator_hasDerivAt (u : ℝ) :
    HasDerivAt derivativeNumerator (derivativeNumeratorD u) u := by
  have hN := ((((hasDerivAt_id u).const_mul (4*Q0)).sub
    (((hasDerivAt_id u).pow 2).const_mul 2)).sub_const (Q0*(Q0+1)))
  have hd := hN.add (((((hasDerivAt_id u).pow 2).mul
    ((Inverse.q_hasDerivAt u).pow 2))).const_mul (18/125))
  convert hd using 1 <;> dsimp [derivativeNumerator,derivativeNumeratorD,N,Inverse.N,
    q,Inverse.q] <;> norm_num [Q0] <;> ring

lemma derivativeNumeratorD_hasDerivAt (u : ℝ) :
    HasDerivAt derivativeNumeratorD (derivativeNumeratorDD u) u := by
  convert (((((hasDerivAt_id u).const_mul (577925689/195312500)).const_add
    (9789/625)).sub (((hasDerivAt_id u).pow 2).const_mul (663606/78125))).add
      (((hasDerivAt_id u).pow 3).const_mul (288/125))) using 1 <;>
    dsimp [derivativeNumeratorD,derivativeNumeratorDD] <;> ring

lemma derivativeNumerator_positive {u : ℝ} (hu : u∈late) :
    0<derivativeNumerator u :=
  positive_of_second_nonpos hu
    (fun t _ => derivativeNumerator_hasDerivAt t)
    (fun t _ => derivativeNumeratorD_hasDerivAt t)
    (fun t ht => by
      have hp := mul_nonneg (show 0≤t by linarith [ht.1])
        (show 0≤171/100-t by linarith [ht.2])
      dsimp [derivativeNumeratorDD]
      nlinarith [ht.1])
    (by norm_num [derivativeNumerator,N,Inverse.N,q,Inverse.q,Q0])
    (by norm_num [derivativeNumerator,N,Inverse.N,q,Inverse.q,Q0])

lemma late_factorD {u : ℝ} (hu : u∈late) : -(18/125:ℝ)<factorD u := by
  have hd := OppositeTwo.Inverse.range_data (late_full hu)
  have hq : 0<q u := by linarith [hd.2]
  apply (lt_div_iff₀ (mul_pos (sq_pos_of_pos hd.1) (sq_pos_of_pos hq))).2
  have hh := derivativeNumerator_positive hu
  dsimp [derivativeNumerator] at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.ContactPolynomial
