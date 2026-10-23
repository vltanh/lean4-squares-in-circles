module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositePositiveZeroBoundary
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroPlusDiagonalBoundary

/-!
# The positive source-diagonal boundary

Uncompiled transcription of the third boundary in Section 3.2. The
explicit rotated-circle branch has increasing support factor. Each
literal target cost is concave between the original aligned endpoint
and the actual target-zero event. Both endpoints retain their exact
original labels and their strict written reserves.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.SourceDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)
open SecondWord.OppositeZero (PlusDiagonal)

abbrev horizontal := PlusDiagonal.horizontal
abbrev vertical := PlusDiagonal.vertical
abbrev height := PlusDiagonal.height
abbrev factor := PlusDiagonal.factor
abbrev factorD := PlusDiagonal.factorD
abbrev Geometry := PlusDiagonal.Domain

def value (r : Row) (x : ℝ) : ℝ := x+c r+(p r+q r)*outerDiagonal+
  v r*(horizontal x-1/2)+t r*(vertical x-1/2)
def first (r : Row) (x : ℝ) : ℝ := 1+(v r*vertical x-t r*horizontal x)*factor x
def second (r : Row) (x : ℝ) : ℝ :=
  -(t r*vertical x+v r*horizontal x)*(factor x)^2+
    (v r*vertical x-t r*horizontal x)*factorD x

lemma target_mem {x : ℝ} (hx : Geometry x) : height x∈Icc 0 outerDiagonal :=
  ⟨hx.2,by linarith [(PlusDiagonal.target_bounds hx).2,SecondWord.fine_outer_endpoint_bounds.2]⟩

lemma coordinates {x : ℝ} (hx : Geometry x) :
    U (height x)=horizontal x ∧ W (height x)=vertical x := by
  have hdata := PlusDiagonal.data hx.1
  have hrad := hdata.2.2.2.2.1
  have hcircle : (horizontal x)^2+(vertical x)^2=Q0 := by
    dsimp [horizontal,vertical,PlusDiagonal.horizontal,PlusDiagonal.vertical]
    linear_combination hrad+
      ((PlusDiagonal.Y x)^2+(PlusDiagonal.Z x)^2)*(Real.sin_sq_add_cos_sq x)
  have hactual := UW_circle (outer_domain (target_mem hx))
  have hU := U_positive (outer_domain (target_mem hx))
  have hW : W (height x)=vertical x := by
    dsimp [W,height,PlusDiagonal.height]
    ring
  rw [hW] at hactual
  exact ⟨by nlinarith [hdata.2.2.2.2.2.1],hW⟩

lemma value_actual (r : Row) {x : ℝ} (hx : Geometry x) :
    value r x=plusCost r (height x) x := by
  have hcoords := coordinates hx
  have hA : arc (height x)=horizontal x-1/2 := by dsimp [U] at hcoords; linarith [hcoords.1]
  rw [plusCost,PlusDiagonal.contact hx]
  simp only [source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
    ShortOuterOne.SameContact.arc_diagonal,mul_zero,add_zero,zero_mul,zero_add,hA]
  dsimp [value,height,PlusDiagonal.height]
  ring

lemma value_hasDerivAt (r : Row) {x : ℝ} (hx : Geometry x) :
    HasDerivAt (value r) (first r x) x := by
  have hU := PlusDiagonal.horizontal_hasDerivAt hx.1
  have hV : HasDerivAt vertical (-horizontal x*factor x) x := by
    convert (PlusDiagonal.height_hasDerivAt hx.1).add_const (1/2) using 1 <;>
      dsimp [vertical,height,PlusDiagonal.height,PlusDiagonal.speed] <;> ring
  convert (((((hasDerivAt_id x).add_const (c r)).add_const ((p r+q r)*outerDiagonal)).
    add ((hU.sub_const (1/2)).const_mul (v r))).add
      ((hV.sub_const (1/2)).const_mul (t r))) using 1 <;>
    dsimp [value,first] <;> ring

lemma first_hasDerivAt (r : Row) {x : ℝ} (hx : Geometry x) :
    HasDerivAt (first r) (second r x) x := by
  have hU := PlusDiagonal.horizontal_hasDerivAt hx.1
  have hV : HasDerivAt vertical (-horizontal x*factor x) x := by
    convert (PlusDiagonal.height_hasDerivAt hx.1).add_const (1/2) using 1 <;>
      dsimp [vertical,height,PlusDiagonal.height,PlusDiagonal.speed] <;> ring
  have hf := PlusDiagonal.factor_hasDerivAt hx.1
  convert ((((hV.const_mul (v r)).sub (hU.const_mul (t r))).mul hf).const_add 1)
    using 1 <;> dsimp [first,second] <;> ring

lemma work_signs (r : Row) {x : ℝ} (hx : Geometry x) :
    0<t r*vertical x+v r*horizontal x ∧ v r*vertical x-t r*horizontal x<0 := by
  have hcoords := coordinates hx
  have ht := ShortOuterOne.SameContact.arc_state (target_mem hx)
  have hU0 : 0<horizontal x := by
    rw [←hcoords.1]
    exact U_positive (outer_domain (target_mem hx))
  have hUu : horizontal x<(383/200:ℝ) := by
    have ha := (outer_bounds ht).2.1
    rw [←hcoords.1]
    dsimp [U]
    linarith [outer_endpoint_bounds.2.1]
  have hV : (1/2:ℝ)≤vertical x := by dsimp [height,PlusDiagonal.height] at hx; linarith [hx.2]
  have hpositive : 0<t r*vertical x+v r*horizontal x := by
    fin_cases r <;> norm_num [v,t] <;> linarith
  have htarget := (slope_bounds r (target_mem hx)).2.2
  have hh := mul_pos htarget hU0
  have he : h r (height x)*horizontal x=t r*horizontal x-v r*vertical x := by
    dsimp [h,ratio]
    change (t r-v r*(W (height x)/U (height x)))*horizontal x=_
    rw [hcoords.1,hcoords.2]
    field_simp [hU0.ne']
    ring
  rw [he] at hh
  exact ⟨hpositive,by linarith⟩

lemma curvature_negative (r : Row) {x : ℝ} (hx : Geometry x) : second r x<0 := by
  have hwork := work_signs r hx
  have hdata := PlusDiagonal.data hx.1
  have hf : 0<factor x := hdata.2.2.2.2.2.2.2.2.1
  have hfd : 0<factorD x := by linarith [hdata.2.2.2.2.2.2.2.2.2.2]
  have hfirst := mul_pos hwork.1 (sq_pos_of_pos hf)
  have hsecond := mul_neg_of_neg_of_pos hwork.2 hfd
  dsimp [second]
  linarith

lemma event_geometry {e : ℝ} (he : Same.Event.IsEvent e) : Geometry e ∧ height e=0 := by
  have hcontact : plus 0 e=outerDiagonal := by
    simpa [plus,SecondWord.OppositeZero.plus,Same.contact,SecondWord.SameZero.b] using he.2
  have hd : PlusDomain 0 e := ⟨outer_zero_mem,Same.Event.angle_mem he,
    by rw [hcontact]; exact Negative.diagonal_mem⟩
  exact PlusDiagonal.original hd hcontact

lemma event_cost (r : Row) {e : ℝ} (he : Same.Event.IsEvent e) :
    (22489/25000:ℝ)<e+c r+(p r+q r)*outerDiagonal+v r*outerAxial := by
  have helo := he.1.1
  have hd := ShortMixedZero.fine_diagonal_bounds
  have ha := ShortOuterZero.fine_axial_bounds
  fin_cases r <;> norm_num [c,p,q,v,Same.Event.lo] at helo ⊢ <;>
    linarith [hd.1,hd.2,ha.1,ha.2]

lemma physical_before {e y : ℝ} (he : Same.Event.IsEvent e) (hy : y∈Icc 0 e) : Geometry y := by
  have hE := event_geometry he
  have hya : y∈Icc 0 (27/250) := ⟨hy.1,hy.2.trans hE.1.1.2⟩
  have hh := PlusDiagonal.height_antitone hya hE.1.1 hy.2
  rw [hE.2] at hh
  exact ⟨hya,hh⟩

lemma before_event {e x : ℝ} (he : Same.Event.IsEvent e) (hx : Geometry x) : x≤e := by
  have hE := event_geometry he
  by_contra! hlarge
  have hm := PlusDiagonal.shifted_height_antitone hE.1.1 hx.1 hlarge.le
  rw [hE.2] at hm
  linarith [hx.2]

/-- The entire positive source-diagonal contact, including both endpoints. -/
theorem lower (r : Row) {x : ℝ} (hx : Geometry x) : (89809/100000:ℝ)<value r x := by
  obtain ⟨e,he⟩ := Same.Event.exists_event
  have hE := event_geometry he
  have hpos : 0≤e := (Same.Event.angle_mem he).1
  have hconc : ConcaveOn ℝ (Icc 0 e) (value r) :=
    concave_of_deriv2 (fun y hy => value_hasDerivAt r (physical_before he hy))
      (fun y hy => first_hasDerivAt r (physical_before he hy))
      (fun y hy => (curvature_negative r (physical_before he hy)).le)
  apply concave_gt_of_endpoints hconc ⟨hx.1.1,before_event he hx⟩
  · have hz := physical_before he (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,hpos⟩)
    rw [value_actual r hz,plusCost,PlusDiagonal.contact hz,PlusDiagonal.height_zero]
    have hh := aligned_original r Negative.diagonal_mem low_mem (by dsimp [low]; ring)
    simpa only [zero_add] using hh
  · rw [value_actual r hE.1,hE.2,plusCost,PlusDiagonal.contact hE.1]
    have hh := event_cost r he
    simp only [source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
      ShortOuterOne.SameContact.arc_diagonal,ShortOuterOne.SameContact.arc_zero,
      mul_zero,add_zero,zero_mul,zero_add]
    linarith

theorem original_lower (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hb : plus B x=outerDiagonal) : (89809/100000:ℝ)<plusCost r B x := by
  obtain ⟨hx,hB⟩ := PlusDiagonal.original hd hb
  have hh := lower r hx
  rwa [value_actual r hx,hB] at hh

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.SourceDiagonal
