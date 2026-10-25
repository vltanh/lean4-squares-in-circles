module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeData
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.PositivePrimary

/-!
# Eight squares: the two increasing multiplier envelopes on the negative half

The multiplier is exactly `.9994`. The original source remainder is kept (`source_lower`); the
target is bounded by its axial or diagonal support (`target_lower`). Both resulting scalar
functions `axial` and `diagonal` increase on the whole angle interval (`derivatives_positive`)
and have a positive initial reserve (`initial_values`), which gives `contact_lower`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative.Multiplier
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open WrongWordCircleSupport

abbrev weight : ℝ := 4997/5000
def Rows (r : Row) : Prop := r=2 ∨ r=3
def sourceFloor (r : Row) : ℝ := if r=2 then 0 else (p r+q r-weight)*outerDiagonal

def axial (r : Row) (x : ℝ) : ℝ := -x+c r+sourceFloor r+weight/2+v r*outerAxial+
  (weight/2)*Real.cos x+weight*(1/2+outerAxial)*Real.sin x
def diagonal (r : Row) (x : ℝ) : ℝ := -x+c r+sourceFloor r+weight/2+
  (v r+t r)*outerDiagonal+weight*(1/2-outerDiagonal)*Real.cos x+
    weight*(1/2+outerDiagonal)*Real.sin x

def axialD (x : ℝ) : ℝ := -1-(weight/2)*Real.sin x+
  weight*(1/2+outerAxial)*Real.cos x
def diagonalD (x : ℝ) : ℝ := -1+weight*(outerDiagonal-1/2)*Real.sin x+
  weight*(outerDiagonal+1/2)*Real.cos x

lemma source_lower (r : Row) (hr : Rows r) {a b : ℝ} (hs : OuterState a b) :
    sourceFloor r≤p r*a+(q r-weight)*b := by
  rcases hr with rfl | rfl
  · norm_num [sourceFloor,p,q,weight]
  · have hh := outer_diagonal_lower (X := p 3) (Y := q 3-weight) hs
      (by norm_num [p]) (by norm_num [p,q,weight])
    have he : sourceFloor 3=(p 3+(q 3-weight))*outerDiagonal := by
      simp only [sourceFloor]
      rw [ite_eq_right (by decide)]
      ring
    rw [he]
    exact hh

lemma target_lower (r : Row) (hr : Rows r) {A B x : ℝ}
    (ht : OuterState A B) (hx : x∈Icc 0 (7/10)) :
    min ((v r+weight*Real.sin x)*outerAxial)
      ((v r+t r+weight*(Real.sin x-Real.cos x))*outerDiagonal)≤
        (v r+weight*Real.sin x)*A+(t r-weight*Real.cos x)*B := by
  have tr := positive_trig hx
  by_cases hX : 0≤v r+weight*Real.sin x
  · apply outer_concave_lower ht hX (min_le_left _ _)
    have hh := min_le_right ((v r+weight*Real.sin x)*outerAxial)
      ((v r+t r+weight*(Real.sin x-Real.cos x))*outerDiagonal)
    nlinarith
  · have hder : (t r-weight*Real.cos x)-(v r+weight*Real.sin x)≤0 := by
      rcases hr with rfl | rfl
      · norm_num [v,t,weight]
        linarith [tr.2.2.2.2.2]
      · have hnon : 0≤v 3+weight*Real.sin x := by
          norm_num [v,weight]
          exact tr.2.2.1
        exact (hX hnon).elim
    have hh := outer_diagonal_lower ht (le_of_not_ge hX) hder
    have hm := min_le_right ((v r+weight*Real.sin x)*outerAxial)
      ((v r+t r+weight*(Real.sin x-Real.cos x))*outerDiagonal)
    nlinarith

lemma axial_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (axial r) (axialD x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -y+c r+sourceFloor r+weight/2+v r*outerAxial) (-1) x := by
    simpa using ((((((hasDerivAt_id x).neg).add_const (c r)).add_const (sourceFloor r)).add_const
       (weight/2)).add_const (v r*outerAxial))
  have h2 : HasDerivAt (fun y => (weight/2)*Real.cos y) ((weight/2)*(-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul _
  have h3 : HasDerivAt (fun y => weight*(1/2+outerAxial)*Real.sin y)
      (weight*(1/2+outerAxial)*Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul _
  have h := (h1.fun_add h2).fun_add h3
  have he : axial r=fun y => -y+c r+sourceFloor r+weight/2+v r*outerAxial+
      (weight/2)*Real.cos y+weight*(1/2+outerAxial)*Real.sin y := rfl
  rw [he]
  convert h using 1
  simp only [axialD]
  ring

lemma diagonal_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (diagonal r) (diagonalD x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -y+c r+sourceFloor r+weight/2+(v r+t r)*outerDiagonal)
      (-1) x := by
    simpa using ((((((hasDerivAt_id x).neg).add_const (c r)).add_const (sourceFloor r)).add_const
       (weight/2)).add_const ((v r+t r)*outerDiagonal))
  have h2 : HasDerivAt (fun y => weight*(1/2-outerDiagonal)*Real.cos y)
      (weight*(1/2-outerDiagonal)*(-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul _
  have h3 : HasDerivAt (fun y => weight*(1/2+outerDiagonal)*Real.sin y)
      (weight*(1/2+outerDiagonal)*Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul _
  have h := (h1.fun_add h2).fun_add h3
  have he : diagonal r=fun y => -y+c r+sourceFloor r+weight/2+(v r+t r)*outerDiagonal+
      weight*(1/2-outerDiagonal)*Real.cos y+weight*(1/2+outerDiagonal)*Real.sin y := rfl
  rw [he]
  convert h using 1
  simp only [diagonalD]
  ring

lemma derivatives_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<axialD x ∧ 0<diagonalD x := by
  have tr := positive_trig hx
  have hA := mul_le_mul
    (show (1914/1000:ℝ)≤outerAxial+1/2 by linarith [ShortOuterZero.fine_axial_bounds.1])
    tr.1.le (by norm_num) (by linarith [outer_endpoint_bounds.1])
  have hD := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [ShortMixedZero.fine_diagonal_bounds.1])
    tr.1.le (by norm_num) (by linarith [outer_endpoint_bounds.2.2.1])
  have hsin := mul_nonneg
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1]) tr.2.2.1
  simp only [axialD,diagonalD,weight]
  constructor <;> nlinarith [tr.2.2.2.1]

lemma initial_values (r : Row) (hr : Rows r) :
    (112263/125000:ℝ)<axial r 0 ∧ (112263/125000:ℝ)<diagonal r 0 := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  rcases hr with rfl | rfl <;>
    norm_num [axial,diagonal,sourceFloor,weight,c,p,q,v,t] <;>
    constructor <;> linarith [ha.1,ha.2,hd.1,hd.2]

lemma scalar_lower (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (112263/125000:ℝ)< min (axial r x) (diagonal r x) := by
  have ha : MonotoneOn (axial r) (Icc 0 (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (axial_hasDerivAt r x).continuousAt.continuousWithinAt)
      (fun x _ => axial_hasDerivAt r x)
      (fun x hx => (derivatives_positive (Ioo_subset_Icc_self hx)).1.le)
  have hd : MonotoneOn (diagonal r) (Icc 0 (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (diagonal_hasDerivAt r x).continuousAt.continuousWithinAt)
      (fun x _ => diagonal_hasDerivAt r x)
      (fun x hx => (derivatives_positive (Ioo_subset_Icc_self hx)).2.le)
  exact lt_min ((initial_values r hr).1.trans_le (ha (by norm_num) hx hx.1))
    ((initial_values r hr).2.trans_le (hd (by norm_num) hx hx.1))

lemma original_projection (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (112263/125000:ℝ)< -x+c r+p r*a+q r*b+v r*A+t r*B := by
  have hsource := source_lower r hr hs
  have htarget := target_lower r hr ht hx
  have hsep := mul_le_mul_of_nonneg_left hm (by norm_num [weight] : (0:ℝ)≤weight)
  have hvalue := scalar_lower r hr hx
  have he : min (axial r x) (diagonal r x)=
      -x+c r+sourceFloor r+weight*(1+Real.sin x+Real.cos x)/2+
        min ((v r+weight*Real.sin x)*outerAxial)
          ((v r+t r+weight*(Real.sin x-Real.cos x))*outerDiagonal) := by
    rw [add_min]
    congr 1 <;> dsimp [axial,diagonal] <;> ring
  rw [he] at hvalue
  generalize min ((v r+weight*Real.sin x)*outerAxial)
    ((v r+t r+weight*(Real.sin x-Real.cos x))*outerDiagonal) = m at hvalue htarget
  simp only [weight] at hsource htarget hsep hvalue
  linarith only [hsource,htarget,hsep,hvalue]

theorem contact_lower (r : Row) (hr : Rows r) {B x : ℝ} (hd : MinusDomain B x) :
    (89809/100000:ℝ)< minusCost r B x := by
  have hs := ShortOuterOne.SameContact.arc_state hd.2.2
  have ht := ShortOuterOne.SameContact.arc_state hd.1
  have he : (1+Real.sin x+Real.cos x)/2=
      minus B x-arc B*Real.sin x+B*Real.cos x := by
    dsimp [minus,SecondWord.OppositeZero.minus]
    ring
  have hh := original_projection r hr hs ht hd.2.1 he.le
  dsimp [minusCost,source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval]
  linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative.Multiplier
