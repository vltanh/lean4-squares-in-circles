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
  (p r*ratioDD (b x)*(speed x)^2-3*p r*ratioD (b x)*(b x-1/2)+l r (b x))

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
  have heq : b e=outerDiagonal := by rw [same_source]; exact he.2
  rw [show SecondWord.OppositeZero.plus 0 e=outerDiagonal from heq] at hupper
  have hl := SecondWord.SameZero.b_lower outer_zero_mem hxi
  have hl' : (293/1000:ℝ)<b x := by rw [same_source]; exact hl
  exact ⟨outer_zero_mem,hxi,⟨by linarith,hupper⟩⟩

lemma source_range {x : ℝ} (hd : PlusDomain 0 x) : b x∈Icc (293/1000:ℝ) outerDiagonal := by
  have hl := SecondWord.SameZero.b_lower hd.1 hd.2.1
  have hl' : (293/1000:ℝ)<b x := by rw [same_source]; exact hl
  exact ⟨hl'.le,hd.2.2.2⟩

lemma source_hasDerivAt (x : ℝ) : HasDerivAt b (-speed x) x :=
  SecondWord.OppositeZero.plus_hasDerivAt 0 x
lemma speed_hasDerivAt (x : ℝ) : HasDerivAt speed (b x-1/2) x :=
  SecondWord.OppositeZero.plusSpeed_hasDerivAt 0 x

lemma value_hasDerivAt (r : Row) {x : ℝ} (hd : PlusDomain 0 x) :
    HasDerivAt (value r) (first r x) x := plusCost_angle_hasDerivAt r hd

lemma first_hasDerivAt (r : Row) {x : ℝ} (hd : PlusDomain 0 x) :
    HasDerivAt (first r) (second r x) x := by
  have hl : HasDerivAt (fun y => l r (b y)) (-p r*ratioD (b x)*(-speed x)) x :=
    (l_hasDerivAt r hd.2.2).comp x (source_hasDerivAt x)
  have h := (hl.fun_mul (speed_hasDerivAt x)).const_sub 1
  have he : first r=fun y => 1-l r (b y)*speed y := rfl
  rw [he]
  convert h using 1
  simp only [second]
  ring

lemma second_hasDerivAt (r : Row) {x : ℝ} (hd : PlusDomain 0 x) :
    HasDerivAt (second r) (third r x) x := by
  have hD : HasDerivAt (fun y => ratioD (b y)) (ratioDD (b x)*(-speed x)) x :=
    (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hd.2.2)).comp x
      (source_hasDerivAt x)
  have hL : HasDerivAt (fun y => l r (b y)) (-p r*ratioD (b x)*(-speed x)) x :=
    (l_hasDerivAt r hd.2.2).comp x (source_hasDerivAt x)
  have h := ((hD.const_mul (-p r)).fun_mul ((speed_hasDerivAt x).fun_pow 2)).fun_sub
    (hL.fun_mul ((source_hasDerivAt x).sub_const (1/2)))
  have he : second r=fun y => -p r*ratioD (b y)*(speed y)^2-l r (b y)*(b y-1/2) := rfl
  rw [he]
  convert h using 1
  simp only [third,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  ring

lemma ratio_chord {y : ℝ} (hy : y∈Icc (293/1000:ℝ) outerDiagonal) :
    ratio y<(9/50:ℝ)+(23/25)*y := by
  have hdom {z : ℝ} (hz : z∈Icc (293/1000:ℝ) outerDiagonal) : z∈Icc 0 outerDiagonal :=
    ⟨by linarith [hz.1],hz.2⟩
  have hDD {z : ℝ} (hz : z∈Icc (293/1000:ℝ) outerDiagonal) : 0<ratioDD z := by
    have hu := U_positive (outer_domain (hdom hz))
    change 0<3*Q0*(z+1/2)/(U z)^5
    exact div_pos (mul_pos (by norm_num [Q0]) (by linarith [hz.1])) (pow_pos hu 5)
  have hc : ConcaveOn ℝ (Icc (293/1000:ℝ) outerDiagonal)
      (fun z => (9/50:ℝ)+(23/25)*z-ratio z) :=
    concave_of_deriv2 (f' := fun z => 23/25-ratioD z) (f'' := fun z => -ratioDD z)
      (fun z hz => by
        have h := (((hasDerivAt_id' z).const_mul (23/25:ℝ)).const_add (9/50:ℝ)).fun_sub
          (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (hdom hz)))
        convert h using 1
        ring)
      (fun z hz => (ShortOuterOne.SameContact.ratioD_hasDerivAt
        (outer_domain (hdom hz))).const_sub (23/25))
      (fun z hz => neg_nonpos.mpr (hDD hz).le)
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
    linarith [fine_outer_endpoint_bounds.2]
  have hh := concave_gt_of_endpoints (c := 0) (x := y) hc hy
    (by linarith) (by linarith)
  beta_reduce at hh
  linarith

lemma speed_circle {x : ℝ} (hd : PlusDomain 0 x) :
    0<speed x ∧ (speed x)^2+(b x-1/2)^2<(1043/1000:ℝ)^2 := by
  have hn := SecondWord.OppositeZero.plus_norm hd.1 x
  have hm := SecondWord.OppositeZero.Reference.mass_references.1
  norm_num at hn
  exact ⟨(SecondWord.OppositeZero.positive_data hd.1 hd.2.1).1,by linarith⟩

lemma early_ratioD {y : ℝ} (hy : y∈Icc 0 (1/2:ℝ)) : ratioD y<(197/250:ℝ) := by
  have hpoint : y∈Icc 0 outerDiagonal :=
    ⟨hy.1,by linarith [hy.2,fine_outer_endpoint_bounds.2]⟩
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
  have hp : 0≤p r := by rcases hr with rfl | rfl | rfl <;> norm_num [p]
  have hu := U_positive (outer_domain hd.2.2)
  have hc := UW_circle (outer_domain hd.2.2)
  have h0 := UW_circle (outer_domain outer_zero_mem)
  have hn : (b x-1/2)^2+(speed x)^2=Q0-2*(arc 0+0) := SecondWord.OppositeZero.plus_norm hd.1 x
  have hf : 0≤(b x+1/2)*(speed x)^2-(b x-1/2)*(U (b x))^2 := by
    have he : (b x+1/2)*(speed x)^2-(b x-1/2)*(U (b x))^2=(b x-arc 0)^2+1/4 := by
      simp only [U,W] at hc h0 ⊢
      linear_combination (b x+1/2)*hn-(b x-1/2)*hc-h0
    rw [he]
    positivity
  have he : p r*ratioDD (b x)*(speed x)^2-3*p r*ratioD (b x)*(b x-1/2)=
      3*p r*Q0/(U (b x))^5*((b x+1/2)*(speed x)^2-(b x-1/2)*(U (b x))^2) := by
    change p r*(3*Q0*(b x+1/2)/(U (b x))^5)*(speed x)^2-3*p r*(Q0/(U (b x))^3)*(b x-1/2)=_
    field_simp
  have hnn : 0≤p r*ratioDD (b x)*(speed x)^2-3*p r*ratioD (b x)*(b x-1/2) := by
    rw [he]
    exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp) (by norm_num [Q0]))
      (pow_pos hu 5).le) hf
  have hl0 : 0<l r (b x) := by linarith [hl.1]
  simp only [third]
  exact mul_pos hspeed (by linarith)

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis
