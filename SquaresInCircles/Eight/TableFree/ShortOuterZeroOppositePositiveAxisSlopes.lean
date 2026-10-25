module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositePositiveAxisData

/-!
# The three increasing target-zero boundary rows

Uncompiled transcription of equation (13). The two negative source
coefficients use the written ratio chord, one circle tangent, and one
square completion. The constant-slope row uses its original contact
speed bound. No angular reference grid occurs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis
open CommonQuarter CorePairGeometry Arithmetic

abbrev M : ℝ := 1043/1000
def A (r : Row) : ℝ := q r+(16/25)*(-p r)
def B (r : Row) : ℝ := (23/25)*(-p r)

lemma circle_tangent {z w : ℝ} (hw : 0<w) (hc : w^2+z^2≤M^2) :
    w≤M-z^2/(2*M) := by
  have hM : 0<M := by norm_num [M]
  have hs := sq_nonneg (M-w)
  have h : 0≤2*M^2-z^2-2*M*w := by nlinarith
  have he : M-z^2/(2*M)-w=(2*M^2-z^2-2*M*w)/(2*M) := by
    field_simp
  have hq : 0≤(2*M^2-z^2-2*M*w)/(2*M) := div_nonneg h (by positivity)
  linarith

lemma square_completion {a b z : ℝ} (ha : 0<a) (hb : 0≤b) (hz : 0≤z) :
    (a+b*z)*(M-z^2/(2*M))≤a*M+b^2*M^3/(2*a) := by
  have hM : 0<M := by norm_num [M]
  have he : (a+b*z)*(M-z^2/(2*M))=
      a*M+b^2*M^3/(2*a)-(a*z-b*M^2)^2/(2*a*M)-b*z^3/(2*M) := by
    field_simp [ha.ne',hM.ne']
    ring
  rw [he]
  have hsq : 0≤(a*z-b*M^2)^2/(2*a*M) := by positivity
  have hcube : 0≤b*z^3/(2*M) := by positivity
  linarith

lemma negative_primary_coefficients (r : Row) (hr : r=3 ∨ r=5) :
    0<A r ∧ 0<B r ∧ M*A r<1 ∧ A r*M+(B r)^2*M^3/(2*A r)<1 := by
  rcases hr with rfl | rfl <;> norm_num [A,B,M,p,q]

lemma negative_primary_increasing (r : Row) (hr : r=3 ∨ r=5) {x : ℝ}
    (hd : PlusDomain 0 x) : 0<first r x := by
  let z := b x-1/2
  have hs := speed_circle hd
  have hc := ratio_chord (source_range hd)
  have hcoef := negative_primary_coefficients r hr
  have hp : 0< -p r := by rcases hr with rfl | rfl <;> norm_num [p]
  have hmult := mul_lt_mul_of_pos_left hc hp
  have hL : l r (b x)<A r+B r*z := by
    dsimp [l,A,B,z]
    nlinarith
  have hpositive : 0<A r+B r*z := by linarith [(slope_bounds r hd.2.2).1]
  have hspeed : speed x<M := by dsimp [M]; nlinarith [sq_nonneg (b x-1/2)]
  have hwork : l r (b x)*speed x<1 := by
    by_cases hz : z≤0
    · have hsmall : A r+B r*z≤A r := by
        have hh := mul_nonpos_of_nonneg_of_nonpos hcoef.2.1.le hz
        linarith
      have hp := mul_lt_mul (hL.trans_le hsmall) hspeed.le hs.1 hcoef.1.le
      nlinarith [hcoef.2.2.1]
    · have hz' : 0≤z := le_of_not_ge hz
      have hcircle : (speed x)^2+z^2≤M^2 := by simpa [z,M] using hs.2.le
      have htangent := circle_tangent hs.1 hcircle
      have h1 := mul_lt_mul_of_pos_right hL hs.1
      have h2 := mul_le_mul_of_nonneg_left htangent hpositive.le
      have h3 := square_completion hcoef.1 hcoef.2.1.le hz'
      linarith [hcoef.2.2.2]
  dsimp [first,plusAngle]
  linarith

lemma constant_primary_increasing {x : ℝ} (hd : PlusDomain 0 x) : 0<first 0 x := by
  have hs := speed_circle hd
  have hv : speed x<(1043/1000:ℝ) := by nlinarith [sq_nonneg (b x-1/2)]
  norm_num [first,plusAngle,l,p,q]
  linarith

lemma increasing_rows (r : Row) (hr : r=0 ∨ r=3 ∨ r=5) {x : ℝ}
    (hd : PlusDomain 0 x) : 0<first r x := by
  rcases hr with rfl | rfl | rfl
  · exact constant_primary_increasing hd
  · exact negative_primary_increasing 3 (Or.inl rfl) hd
  · exact negative_primary_increasing 5 (Or.inr rfl) hd

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis
