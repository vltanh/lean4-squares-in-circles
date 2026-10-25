module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeData
public import SquaresInCircles.Eight.Words.Wrong.WordCircleSupport

/-!
# Eight squares: the original stationary projection for opposite-sign zero contacts

The source coordinate, the target circle and the contact speed are kept together. Angular
stationarity determines the sum of the two shifted target coordinates (`actual_sum`); the two
coordinates are not treated as independent interval variables.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Stationary
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)

def z (b : ℝ) : ℝ := 1/2-b
def mass (r : Row) (b : ℝ) : ℝ := (z b)^2+1/(l r b)^2
def sumCoordinate (r : Row) (b : ℝ) : ℝ := (Q0+2-mass r b)/2
def G (r : Row) (b : ℝ) : ℝ := z b-p r*ratioD b/(l r b)^3
def angleSecond (r : Row) (B x : ℝ) : ℝ :=
  -p r*ratioD (plus B x)*(plusSpeed B x)^2-l r (plus B x)*(plus B x-1/2)

lemma l_positive (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0<l r b := by
  linarith [(slope_bounds r hb).1]

lemma mass_positive (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0< mass r b := by
  have hl := l_positive r hb
  dsimp [mass]
  positivity

lemma plusAngle_hasDerivAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (plusAngle r B) (angleSecond r B x) x := by
  have hl : HasDerivAt (fun y => l r (plus B y)) (-p r*ratioD (plus B x)*(-plusSpeed B x)) x :=
    (l_hasDerivAt r hd.2.2).comp x (SecondWord.OppositeZero.plus_hasDerivAt B x)
  have h := (hl.fun_mul (SecondWord.OppositeZero.plusSpeed_hasDerivAt B x)).const_sub 1
  have he : plusAngle r B=fun y => 1-l r (plus B y)*plusSpeed B y := rfl
  rw [he]
  convert h using 1
  simp only [angleSecond]
  ring

lemma angleSecond_continuousAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    ContinuousAt (angleSecond r B) x := by
  have hb := (SecondWord.OppositeZero.plus_hasDerivAt B x).continuousAt
  have hv := (SecondWord.OppositeZero.plusSpeed_hasDerivAt B x).continuousAt
  have hD := (ShortOuterOne.SameContact.ratioD_hasDerivAt
    (outer_domain hd.2.2)).continuousAt.comp (x := x) hb
  have hL := (l_hasDerivAt r hd.2.2).continuousAt.comp (x := x) hb
  show ContinuousAt (fun y => -p r*ratioD (plus B y)*(plusSpeed B y)^2-
    l r (plus B y)*(plus B y-1/2)) x
  exact ((continuousAt_const.mul hD).mul (hv.pow 2)).sub
    (hL.mul (hb.sub continuousAt_const))

lemma angular_speed (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle r B x=0) : plusSpeed B x=1/l r (plus B x) := by
  have hl := l_positive r hd.2.2
  dsimp [plusAngle] at hstat
  apply (eq_div_iff hl.ne').2
  nlinarith

lemma actual_mass (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle r B x=0) :
    mass r (plus B x)=Q0+2-2*(U B+W B) := by
  have hn := SecondWord.OppositeZero.plus_norm hd.1 x
  have hs : SecondWord.OppositeZero.plusSpeed B x=1/l r (plus B x) := angular_speed r hd hstat
  rw [hs] at hn
  simp only [mass,z,U,W]
  linear_combination hn

lemma actual_sum (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle r B x=0) : sumCoordinate r (plus B x)=U B+W B := by
  rw [sumCoordinate,actual_mass r hd hstat]
  ring

lemma actual_second (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle r B x=0) :
    angleSecond r B x=l r (plus B x)*G r (plus B x) := by
  have hl := l_positive r hd.2.2
  rw [angleSecond,angular_speed r hd hstat]
  dsimp [G,z]
  field_simp [hl.ne']
  ring

lemma projection_identity {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    U B*(Q0+2-2*(U B+W B))*plusK B x=
      (Q0-(U B+W B))*plusSpeed B x+(W B-U B)*z (plus B x) := by
  have hu := U_positive (outer_domain hB)
  have hc := UW_circle (outer_domain hB)
  have hK : U B*plusK B x=U B*Real.cos x-W B*Real.sin x := by
    change U B*(Real.cos x-(W B/U B)*Real.sin x)=_
    field_simp
  have he : U B*(Q0+2-2*(U B+W B))*plusK B x=(Q0+2-2*(U B+W B))*(U B*plusK B x) := by ring
  rw [he,hK]
  simp only [plusSpeed,SecondWord.OppositeZero.plusSpeed,z,plus,SecondWord.OppositeZero.plus,
    U,W] at hc ⊢
  linear_combination (-(Real.cos x-Real.sin x))*hc

/-- The two original projection equations give the target derivative. -/
lemma actual_target (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusAngle r B x=0) :
    plusTarget r B x=t r-v r*ratio B-
      (Q0-(U B+W B))/(U B*mass r (plus B x))-
      (ratio B-1)*z (plus B x)*l r (plus B x)/mass r (plus B x) := by
  have hl := l_positive r hd.2.2
  have hu := U_positive (outer_domain hd.1)
  have hm := mass_positive r hd.2.2
  have hp := projection_identity hd.1 (x := x)
  rw [←actual_mass r hd hstat,angular_speed r hd hstat] at hp
  have hK : plusK B x=((Q0-(U B+W B))*(1/l r (plus B x))+(W B-U B)*z (plus B x))/
      (U B*mass r (plus B x)) := by
    rw [eq_div_iff (mul_pos hu hm).ne']
    linarith [hp]
  simp only [plusTarget,h]
  rw [hK]
  have hr : ratio B=W B/U B := rfl
  rw [hr]
  field_simp
  ring

lemma original_sum_lower {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    outerAxial+1≤U B+W B := by
  have hs := ShortOuterOne.SameContact.arc_state hB
  have hh := outer_concave_lower hs (by norm_num : (0:ℝ)≤1)
    (one_mul outerAxial).ge
    (show outerAxial≤(1+1)*outerDiagonal by
      linarith [outer_endpoint_bounds.2.1,outer_endpoint_bounds.2.2.1])
  dsimp [U,W]
  linarith

/-- Positive squaring of the target circle and its ordered coordinates. -/
lemma original_U_lower {B S₀ u₀ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hS : U B+W B≤S₀) (hsum : u₀≤U B+W B)
    (hcheck : S₀^2-2*u₀*S₀+2*u₀^2<Q0) : u₀<U B := by
  have hc := UW_circle (outer_domain hB)
  have hs := ShortOuterOne.SameContact.arc_state hB
  have huv : W B≤U B := by dsimp [U,W]; linarith [hs.2.1]
  by_contra! hbad
  have hp := mul_nonneg (sub_nonneg.mpr hbad)
    (sub_nonneg.mpr (huv.trans hbad))
  have hq := mul_nonneg (sub_nonneg.mpr hS)
    (show 0≤S₀+(U B+W B)-2*u₀ by linarith)
  nlinarith

lemma angular_nonnegative_source (r : Row) (hr : r=1 ∨ r=4) {b : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hG : 0≤G r b) : 0<z b := by
  have hp : 0<p r := by rcases hr with rfl | rfl <;> norm_num [p]
  have hD := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hl := l_positive r hb
  have hquot := div_pos (mul_pos hp hD) (pow_pos hl 3)
  dsimp [G] at hG
  linarith

lemma target_lower (r : Row) (hr : r=1 ∨ r=4) {B x : ℝ}
    (hd : PlusDomain B x) (hstat : plusAngle r B x=0)
    (hG : 0≤G r (plus B x)) :
    t r-v r*ratio B-(Q0-(U B+W B))/(U B*mass r (plus B x))≤plusTarget r B x := by
  have hz := angular_nonnegative_source r hr hd.2.2 hG
  have hl := l_positive r hd.2.2
  have hm := mass_positive r hd.2.2
  have hratio := (SecondWord.outer_ratio_bounds hd.1).2.1
  have hprod : (ratio B-1)*z (plus B x)*l r (plus B x)/mass r (plus B x)≤0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hz.le) hl.le) hm.le
  rw [actual_target r hd hstat]
  linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Stationary
