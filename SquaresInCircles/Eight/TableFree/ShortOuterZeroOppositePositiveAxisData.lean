module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositePositiveCap
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroPositiveSpeeds

/-!
# The physical positive target-zero contact

Uncompiled transcription of the fourth boundary in Section 3.2. Its
source is the unchanged circle coordinate b(x), its speed is the exact
contact speed, and its derivatives are those of the literal row label.
The ratio chord is proved on the complete source interval [.293,d].
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)

abbrev b (x : ℝ) : ℝ := plus 0 x
abbrev speed (x : ℝ) : ℝ := plusSpeed 0 x
abbrev value (r : Row) (x : ℝ) : ℝ := plusCost r 0 x
abbrev first (r : Row) (x : ℝ) : ℝ := plusAngle r 0 x

def second (r : Row) (x : ℝ) : ℝ :=
  -p r*ratioD (b x)*(speed x)^2-l r (b x)*(b x-1/2)
def third (r : Row) (x : ℝ) : ℝ := speed x*
  (p r*ratioDD (b x)*(speed x)^2+3*p r*ratioD (b x)*(b x-1/2)+l r (b x))

lemma same_source (x : ℝ) : b x=Same.contact 0 x := by
  dsimp [b,plus,SecondWord.OppositeZero.plus,Same.contact,SecondWord.SameZero.b]
  ring
lemma same_speed (x : ℝ) : speed x=Same.speed 0 x := by
  dsimp [speed,plusSpeed,SecondWord.OppositeZero.plusSpeed,Same.speed,SecondWord.SameZero.v]
  ring

lemma before_event {e x : ℝ} (he : Same.Event.IsEvent e) (hd : PlusDomain 0 x) : e≤x := by
  apply Same.Event.before_contact he
  exact ⟨hd.1,hd.2.1,by simpa only [←same_source] using hd.2.2⟩

lemma domain {e x : ℝ} (he : Same.Event.IsEvent e) (hx : x∈Icc e (7/10)) : PlusDomain 0 x := by
  have hxi : x∈Icc 0 (7/10) := ⟨(Same.Event.angle_mem he).1.trans hx.1,hx.2⟩
  have hupper := SecondWord.OppositeZero.plus_angle_antitone outer_zero_mem
    (Same.Event.angle_mem he) hxi hx.1
  have heq : plus 0 e=outerDiagonal := by rw [←same_source] at he; exact he.2
  rw [heq] at hupper
  have hl := SecondWord.SameZero.b_lower outer_zero_mem hxi
  rw [←same_source] at hl
  exact ⟨outer_zero_mem,hxi,⟨by linarith,hupper⟩⟩

lemma source_range {x : ℝ} (hd : PlusDomain 0 x) : b x∈Icc (293/1000:ℝ) outerDiagonal := by
  have hl := SecondWord.SameZero.b_lower hd.1 hd.2.1
  rw [←same_source] at hl
  exact ⟨hl.le,hd.2.2.2⟩

lemma source_hasDerivAt (x : ℝ) : HasDerivAt b (-speed x) x :=
  SecondWord.OppositeZero.plus_hasDerivAt 0 x
lemma speed_hasDerivAt (x : ℝ) : HasDerivAt speed (b x-1/2) x :=
  SecondWord.OppositeZero.plusSpeed_hasDerivAt 0 x

lemma value_hasDerivAt (r : Row) {x : ℝ} (hd : PlusDomain 0 x) :
    HasDerivAt (value r) (first r x) x := plusCost_angle_hasDerivAt r hd

lemma first_hasDerivAt (r : Row) {x : ℝ} (hd : PlusDomain 0 x) :
    HasDerivAt (first r) (second r x) x := by
  convert ((((l_hasDerivAt r hd.2.2).comp x (source_hasDerivAt x)).mul
    (speed_hasDerivAt x)).const_sub 1) using 1 <;>
    dsimp [first,plusAngle,second] <;> ring

lemma second_hasDerivAt (r : Row) {x : ℝ} (hd : PlusDomain 0 x) :
    HasDerivAt (second r) (third r x) x := by
  have hD := (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hd.2.2)).comp x
    (source_hasDerivAt x)
  have hL := (l_hasDerivAt r hd.2.2).comp x (source_hasDerivAt x)
  convert (((hD.const_mul (-p r)).mul ((speed_hasDerivAt x).pow 2)).sub
    (hL.mul ((source_hasDerivAt x).sub_const (1/2)))) using 1 <;>
    dsimp [second,third] <;> ring

lemma ratio_chord {y : ℝ} (hy : y∈Icc (293/1000:ℝ) outerDiagonal) :
    ratio y<(9/50:ℝ)+(23/25)*y := by
  have hdom {z : ℝ} (hz : z∈Icc (293/1000:ℝ) outerDiagonal) : z∈Icc 0 outerDiagonal :=
    ⟨by linarith [hz.1],hz.2⟩
  have hc : ConcaveOn ℝ (Icc (293/1000:ℝ) outerDiagonal)
      (fun z => (9/50:ℝ)+(23/25)*z-ratio z) :=
    concave_of_deriv2
      (fun z hz => (((hasDerivAt_id z).const_mul (23/25)).const_add (9/50)).sub
        (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (hdom hz))))
      (fun z hz => (ShortOuterOne.SameContact.ratioD_hasDerivAt
        (outer_domain (hdom hz))).const_sub (23/25))
      (fun z hz => neg_nonpos.mpr
        (ShortOuterOne.SameContact.ratioDD_pos (outer_domain (hdom hz))).le)
  have hleft : ratio (293/1000)<(9/50:ℝ)+(23/25)*(293/1000) := by
    have hpoint : (293/1000:ℝ)∈Icc 0 outerDiagonal :=
      SecondWord.Asymmetric.rational_outer_mem (by norm_num)
    have hcircle := UW_circle (outer_domain hpoint)
    have hu := U_positive (outer_domain hpoint)
    have hroot : (9/5:ℝ)<U (293/1000) := by
      norm_num [W,Q0] at hcircle
      nlinarith
    change ((293/1000:ℝ)+1/2)/U (293/1000)<_
    apply (div_lt_iff₀ hu).2
    nlinarith
  have hright : ratio outerDiagonal<(9/50:ℝ)+(23/25)*outerDiagonal := by
    rw [SecondWord.ratio_diagonal]
    linarith [SecondWord.fine_outer_endpoint_bounds.2]
  have hh := concave_gt_of_endpoints hc hy (by linarith) (by linarith)
  linarith

lemma speed_circle {x : ℝ} (hd : PlusDomain 0 x) :
    0<speed x ∧ (speed x)^2+(b x-1/2)^2<(1043/1000:ℝ)^2 := by
  have hn := SecondWord.OppositeZero.plus_norm hd.1 x
  have hm := SecondWord.OppositeZero.Reference.mass_references.1
  norm_num at hn
  exact ⟨(SecondWord.OppositeZero.positive_data hd.1 hd.2.1).1,by linarith⟩

lemma early_ratioD {y : ℝ} (hy : y∈Icc 0 (1/2:ℝ)) : ratioD y<(197/250:ℝ) := by
  have hpoint : y∈Icc 0 outerDiagonal :=
    ⟨hy.1,by linarith [hy.2,SecondWord.fine_outer_endpoint_bounds.2]⟩
  have hc := UW_circle (outer_domain hpoint)
  have hu := U_positive (outer_domain hpoint)
  have hW : 0≤W y ∧ W y≤1 := by dsimp [W]; constructor <;> linarith [hy.1,hy.2]
  have huL : (1707/1000:ℝ)<U y := by
    have hW2 := pow_le_pow_left₀ hW.1 hW.2 2
    norm_num [Q0] at hc
    nlinarith
  have hu3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1707/1000) huL.le 3
  change Q0/(U y)^3<197/250
  apply (div_lt_iff₀ (pow_pos hu 3)).2
  norm_num [Q0] at hu3 ⊢
  linarith

lemma nonnegative_primary_third (r : Row) (hr : r=1 ∨ r=2 ∨ r=4) {x : ℝ}
    (hd : PlusDomain 0 x) : 0<third r x := by
  have hspeed := (speed_circle hd).1
  have hl := slope_bounds r hd.2.2
  have hD := ShortOuterOne.SameContact.ratioD_pos (outer_domain hd.2.2)
  have hDD := ShortOuterOne.SameContact.ratioDD_pos (outer_domain hd.2.2)
  have hp : 0≤p r ∧ p r≤51554/100000 := by
    rcases hr with rfl | rfl | rfl <;> norm_num [p]
  have hfirst := mul_nonneg (mul_nonneg hp.1 hDD.le) (sq_nonneg (speed x))
  have hinner : 0<p r*ratioDD (b x)*(speed x)^2+
      3*p r*ratioD (b x)*(b x-1/2)+l r (b x) := by
    by_cases hz : 1/2≤b x
    · have hsecond := mul_nonneg (mul_nonneg (by linarith [hp.1] : 0≤3*p r) hD.le)
        (sub_nonneg.mpr hz)
      linarith [hl.1]
    · have hrD := early_ratioD ⟨hd.2.2.1,le_of_not_ge hz⟩
      have hzL : -(207/1000:ℝ)≤b x-1/2 := by linarith [(source_range hd).1]
      have hprod := mul_le_mul hp.2 hrD.le hD.le (by norm_num)
      have hneg := mul_le_mul_of_nonpos_right hprod (by norm_num : (-207/1000:ℝ)≤0)
      have hactual := mul_le_mul_of_nonneg_left hzL (mul_nonneg hp.1 hD.le)
      nlinarith [hl.1]
  exact mul_pos hspeed hinner

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis
