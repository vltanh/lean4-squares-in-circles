module

public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveAxialPolynomial
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerData

/-!
# Eight squares: the axial contact bound on its whole half-angle interval

The positive numerator is connected to the circle radical, and then the polynomial inequality is
unsquared with its correct sign. The original angle is kept through the arctangent majorant
(`lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.Axial
open CommonQuarter CorePairGeometry Arithmetic Polynomial

def beforeSquare (r : Bool) (u : ℝ) : ℝ :=
  (AxialPolynomial.L r:ℝ)-2*atanFive (half u)-D r u*axialZ u

lemma L_identity (r : Bool) : (AxialPolynomial.L r:ℝ)=
    157079632679489/100000000000000+c+p r*(1414575672/1000000000)+
      (P r+t r)/2-449/500 := by
  simp [AxialPolynomial.L,p,P,t,c]

lemma beforeSquare_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10))
    (hx : half u≤halfCap) : 0<beforeSquare r u := by
  have ht := positive_trig hu
  have hP : 0<P r := by linarith [(coefficient_bounds r).2.2.2.2.1]
  have htk := mul_nonneg (show 0≤t r by linarith [(coefficient_bounds r).2.2.2.2.2.2.1]) ht.2.2.1
  have hPk := mul_le_mul_of_nonneg_left ht.2.1 hP.le
  have hD : D r u≤P r := by dsimp [D]; linarith
  have hZ : 0≤axialZ u ∧ axialZ u≤3/2 := by
    dsimp [axialZ]
    constructor <;> linarith [ht.1,ht.2.1]
  have hDZ := mul_le_mul_of_nonneg_right hD hZ.1
  have hPZ := mul_le_mul_of_nonneg_left hZ.2 hP.le
  have ha := atanFive_le_self ⟨(half_bounds hu).1,hx⟩
  have hL : (69/50:ℝ)<(AxialPolynomial.L r:ℝ) := by
    cases r <;> norm_num [AxialPolynomial.L,pQ,qQ,PQ,tQ]
  have hPmax := (coefficient_bounds r).2.2.2.2.2.1
  dsimp [beforeSquare,halfCap] at *
  nlinarith only [hDZ,hPZ,ha,hL,hPmax,hx]

lemma numerator_identity (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    aeval (half u) (AxialPolynomial.f r)=beforeSquare r u*(1+(half u)^2)^2 := by
  have htr := half_trig hu
  have hd : 1+(half u)^2≠0 := by positivity
  simp only [AxialPolynomial.f,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  dsimp [beforeSquare,D,axialZ,atanFive,p,P,t]
  rw [htr.1,htr.2]
  push_cast
  field_simp [hd]
  ring

lemma subtracted_identity (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    aeval (half u) ((AxialPolynomial.eNumerator r)^2*AxialPolynomial.radicalNumerator)=
      (E r u*axialT u)^2*(1+(half u)^2)^4 := by
  have htr := half_trig hu
  have hd : 1+(half u)^2≠0 := by positivity
  rw [mul_pow,axialT_sq hu]
  simp only [AxialPolynomial.eNumerator,AxialPolynomial.radicalNumerator,
    AxialPolynomial.denominator,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  dsimp [E,axialZ,P,t,Q0]
  rw [htr.1,htr.2]
  push_cast
  field_simp [hd]
  ring

lemma square_difference (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    aeval (half u) (AxialPolynomial.polynomial r)=
      ((beforeSquare r u)^2-(E r u*axialT u)^2)*(1+(half u)^2)^4 := by
  rw [AxialPolynomial.polynomial,map_sub,map_pow,numerator_identity r hu,subtracted_identity r hu]
  ring

lemma unsquared (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) (hx : half u≤halfCap) :
    E r u*axialT u<beforeSquare r u := by
  have hp := AxialPolynomial.positive r
    (show half u∈Icc 0 (AxialPolynomial.h:ℝ) from ⟨(half_bounds hu).1,by simpa [AxialPolynomial.h,halfCap] using hx⟩)
  rw [square_difference r hu] at hp
  have hsq : 0<(beforeSquare r u)^2-(E r u*axialT u)^2 :=
    (mul_pos_iff_of_pos_right (by positivity : 0<(1+(half u)^2)^4)).mp hp
  have hpos := beforeSquare_positive r hu hx
  have hprod := mul_pos (E_positive r hu) (axialT_positive hu)
  nlinarith

theorem lower (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) (hx : half u≤halfCap) :
    (449/500:ℝ)<axial r u := by
  have hsmall := unsquared r hu hx
  have hangle : u≤2*atanFive (half u) := by
    have hh := arctan_le_five (half_bounds hu).1
    linarith [angle_arctan_half hu]
  have hp : p r<0 := by linarith [(coefficient_bounds r).2.1]
  have hsource := mul_lt_mul_of_neg_left ShortOuterZero.fine_axial_bounds.2 hp
  have hpi : (157079632679489/100000000000000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  dsimp [beforeSquare] at hsmall
  rw [L_identity] at hsmall
  dsimp [axial]
  linarith

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.Axial
