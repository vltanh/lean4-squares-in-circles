module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPlusDiagonalBoundary
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeNegativeCurvature
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveZeroGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveAxisSlopes
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameEvent

/-!
# Eight squares: the positive source-diagonal boundary

The
explicit rotated-circle branch has increasing support factor. Each
literal target cost is concave between the original aligned endpoint
and the actual target-zero event. Both endpoints retain their exact
original labels and their strict written reserves.
-/

section
/-!
## The three named positive-axis endpoint checks

The two convex-derivative
rows have negative final first derivative; the remaining row has a
negative final second derivative and positive final first derivative.
Every interval encloses the literal source contact and its exact speed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Axis.References
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (zeroSourceBox aBox)

abbrev sourceBox : Interval (b (7/10)) := by
  rw [same_source]
  exact zeroSourceBox (7/10) (by norm_num)

lemma r89_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
lemma r89_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
lemma r89_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl
lemma r89_mp_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).hi = S.hi := by subst e; rfl

/-- The explicit enclosure behind `zeroSourceBox`. -/
abbrev r89_sourceFormula : Interval (1/2+1/2*Real.cos (7/10)-(outerAxial-1/2)*Real.sin (7/10)) :=
  ((Interval.point (1/2)).add ((Interval.point (1/2)).mul (SecondWord.SameZero.PJ.Reference.cosBox (7/10) (by norm_num)))).sub
    ((aBox.sub (Interval.point (1/2))).mul (SecondWord.SameZero.PJ.Reference.sinBox (7/10) (by norm_num)))

lemma r89_sourceBox_lo : sourceBox.lo=r89_sourceFormula.lo := by
  unfold sourceBox zeroSourceBox
  rw [r89_mpr_lo, r89_mpr_lo, r89_mp_lo]
  · norm_num
  · simp only [Same.contact,SecondWord.SameZero.b,ShortOuterOne.SameContact.arc_zero]
    ring
  · exact same_source _

lemma r89_sourceBox_hi : sourceBox.hi=r89_sourceFormula.hi := by
  unfold sourceBox zeroSourceBox
  rw [r89_mpr_hi, r89_mpr_hi, r89_mp_hi]
  · norm_num
  · simp only [Same.contact,SecondWord.SameZero.b,ShortOuterOne.SameContact.arc_zero]
    ring
  · exact same_source _

lemma r89_radicand_pos : 0<(radicand sourceBox).lo := by
  simp only [radicand,Interval.point,Interval.sub,Interval.add,Interval.square,Interval.mul,
    r89_sourceBox_lo,r89_sourceBox_hi]
  norm_num [aBox,SecondWord.SameZero.PJ.Reference.sinBox,SecondWord.SameZero.PJ.Reference.cosBox,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.mul,Q0,
    HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8]

lemma r89_rootThree_lo_pos {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo)
    (h : 0<X.lo) : 0<(rootThree X s hs hX).lo := by
  have hhi : 0≤X.hi := hX.trans (X.mem.1.trans X.mem.2)
  have key : ∀ (t : ℝ) (ht : 0<t), 0<(rootStep X t ht hX).lo := by
    intro t ht
    show 0<X.lo/((t+X.hi/t)/2)
    positivity
  exact key _ (rootStep_hi_pos _ _ _ hX)

lemma r89_shifted_eq {y : ℝ} : SecondWord.U y=Real.sqrt (Q0-(y+1/2)^2) := by
  dsimp [SecondWord.U,ShortOuterOne.SameContact.arc]
  ring

lemma r89_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo=(rootThree (radicand Y) s hs hr).lo :=
  r89_mpr_lo r89_shifted_eq (congrArg _ r89_shifted_eq) _

def rootBox : Interval (SecondWord.U (b (7/10))) :=
  shifted sourceBox (9/5) (by norm_num) r89_radicand_pos.le

def speedBox : Interval (speed (7/10)) :=
  SecondWord.OppositeZero.Reference.speedBox 0 (7/10) (by norm_num) (by norm_num)

macro "axis_reference_arithmetic" : tactic => `(tactic|
  norm_num [sourceBox,rootBox,speedBox,
    SecondWord.OppositeZero.Reference.speedBox,SecondWord.OppositeZero.Reference.rootAt,
    SecondWord.SameZero.PJ.Reference.zeroSourceBox,SecondWord.SameZero.PJ.Reference.aBox,
    SecondWord.SameZero.PJ.Reference.sinBox,SecondWord.SameZero.PJ.Reference.cosBox,
    rootThree,rootStep,shifted,radicand,labelBox,coordinate,ratioBox,ratioDBox,
    source,c,p,q,v,t,Q0,Interval.of_bounds,Interval.point,Interval.add,Interval.sub,
    Interval.neg,Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8])

lemma root_positive : 0<rootBox.lo := by
  rw [rootBox,r89_shifted_lo]
  exact r89_rootThree_lo_pos _ _ _ _ r89_radicand_pos

/-- Rounded enclosures of the literal source contact, its speed, root and ratio at `.7`. -/
lemma r89_trig :
    (644217687237/1000000000000:ℝ)<Real.sin (7/10) ∧
      Real.sin (7/10)<322108843619/500000000000 ∧
      (191210546821/250000000000:ℝ)<Real.cos (7/10) ∧
      Real.cos (7/10)<152968437457/200000000000 := by
  have hs := HighOrderTaylor.S15_le_sin (show (0:ℝ)≤7/10 by norm_num)
  have hs' := HighOrderTaylor.sin_le_S17 (show (0:ℝ)≤7/10 by norm_num)
  have hc := HighOrderTaylor.C18_le_cos (show (0:ℝ)≤7/10 by norm_num)
  have hc' := HighOrderTaylor.cos_le_C16 (show (0:ℝ)≤7/10 by norm_num)
  norm_num [HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8] at hs hs' hc hc'
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

lemma r89_source_speed :
    (146617634711/500000000000:ℝ)<b (7/10) ∧ b (7/10)<73308817517/250000000000 ∧
      (510807450131/500000000000:ℝ)<speed (7/10) ∧ speed (7/10)<102161490103/100000000000 := by
  obtain ⟨hs1,hs2,hc1,hc2⟩ := r89_trig
  have ha := ShortOuterZero.fine_axial_bounds
  have hb : b (7/10)=1/2+1/2*Real.cos (7/10)-(outerAxial-1/2)*Real.sin (7/10) := by
    show SecondWord.OppositeZero.plus 0 (7/10)=_
    simp only [SecondWord.OppositeZero.plus,ShortOuterOne.SameContact.arc_zero]
    ring
  have hv : speed (7/10)=(outerAxial-1/2)*Real.cos (7/10)+1/2*Real.sin (7/10) := by
    show SecondWord.OppositeZero.plusSpeed 0 (7/10)=_
    simp only [SecondWord.OppositeZero.plusSpeed,ShortOuterOne.SameContact.arc_zero]
    ring
  have hA1 : (1414575671/1000000000-1/2:ℝ)<outerAxial-1/2 := by linarith [ha.1]
  have hA2 : outerAxial-1/2<(176821959/125000000-1/2:ℝ) := by linarith [ha.2]
  have hp1 := mul_lt_mul'' hA1 hs1 (by norm_num) (by norm_num)
  have hp2 := mul_lt_mul'' hA2 hs2 (by linarith) (by linarith)
  have hq1 := mul_lt_mul'' hA1 hc1 (by norm_num) (by norm_num)
  have hq2 := mul_lt_mul'' hA2 hc2 (by linarith) (by linarith)
  rw [hb,hv]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

lemma r89_root_ratio :
    (1812836949733/1000000000000:ℝ)<SecondWord.U (b (7/10)) ∧
      SecondWord.U (b (7/10))<1812836950017/1000000000000 ∧
      (437565700221/1000000000000:ℝ)<ShortOuterOne.SameContact.ratio (b (7/10)) ∧
      ShortOuterOne.SameContact.ratio (b (7/10))<437565700647/1000000000000 := by
  obtain ⟨hb1,hb2,-,-⟩ := r89_source_speed
  have hmem : b (7/10)∈Icc 0 outerAxial :=
    ⟨by linarith,by linarith [outer_endpoint_bounds.1]⟩
  have hc := SecondWord.UW_circle hmem
  have hu := SecondWord.U_positive hmem
  simp only [SecondWord.W,Q0] at hc
  have hsq1 : (b (7/10)+1/2)^2<(73308817517/250000000000+1/2:ℝ)^2 :=
    pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
  have hsq2 : (146617634711/500000000000+1/2:ℝ)^2<(b (7/10)+1/2)^2 :=
    pow_lt_pow_left₀ (by linarith) (by norm_num) two_ne_zero
  have hu1 : (1812836949733/1000000000000:ℝ)<SecondWord.U (b (7/10)) :=
    lt_of_pow_lt_pow_left₀ 2 hu.le (by norm_num at hsq1 ⊢; linarith)
  have hu2 : SecondWord.U (b (7/10))<1812836950017/1000000000000 :=
    lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by norm_num at hsq2 ⊢; linarith)
  have hr : ShortOuterOne.SameContact.ratio (b (7/10))=(b (7/10)+1/2)/SecondWord.U (b (7/10)) :=
    rfl
  rw [hr]
  refine ⟨hu1,hu2,?_,?_⟩
  · rw [lt_div_iff₀ hu]
    nlinarith
  · rw [div_lt_iff₀ hu]
    nlinarith

def slopeBox (r : Row) : Interval (l r (b (7/10))) :=
  (Interval.point (q r)).sub ((Interval.point (p r)).mul
    (ratioBox sourceBox rootBox root_positive))

def firstBox (r : Row) : Interval (first r (7/10)) :=
  (Interval.point 1).sub ((slopeBox r).mul speedBox)

def secondBox (r : Row) : Interval (second r (7/10)) :=
  (((Interval.point (-p r)).mul (ratioDBox rootBox root_positive)).mul speedBox.square).sub ((slopeBox r).mul (sourceBox.sub (Interval.point (1/2))))

lemma r89_first_eq (r : Row) : first r (7/10)=
    1-(q r-p r*ShortOuterOne.SameContact.ratio (b (7/10)))*speed (7/10) := rfl

lemma r89_value_eq (r : Row) : value r (7/10)=
    7/10+c r+p r*(SecondWord.U (b (7/10))-1/2)+q r*b (7/10)+v r*outerAxial := by
  show plusCost r 0 (7/10)=_
  simp only [plusCost,source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
    ShortOuterOne.SameContact.arc_zero,SecondWord.U]
  ring

lemma one_final : first 1 (7/10)< -(9/12500:ℝ) ∧
    (229/250:ℝ)<value 1 (7/10) := by
  obtain ⟨hb1,hb2,hs1,hs2⟩ := r89_source_speed
  obtain ⟨hu1,hu2,hr1,hr2⟩ := r89_root_ratio
  constructor
  · have hl : (97954993165/100000000000:ℝ)<q 1-p 1*ShortOuterOne.SameContact.ratio (b (7/10)) := by
      norm_num [p,q]
      linarith
    have hm := mul_lt_mul'' hl hs1 (by norm_num) (by norm_num)
    rw [r89_first_eq]
    linarith
  · rw [r89_value_eq]
    norm_num [c,p,q,v]
    linarith

lemma two_final : first 2 (7/10)< -(21/1000:ℝ) ∧
    (951/1000:ℝ)<value 2 (7/10) := by
  obtain ⟨hb1,hb2,hs1,hs2⟩ := r89_source_speed
  have ha := ShortOuterZero.fine_axial_bounds
  constructor
  · rw [r89_first_eq]
    norm_num [p,q]
    linarith
  · rw [r89_value_eq]
    norm_num [c,p,q,v]
    linarith [ha.2]

lemma four_final : second 4 (7/10)< -(3/20:ℝ) ∧
    (27/5000:ℝ)<first 4 (7/10) := by
  obtain ⟨hb1,hb2,hs1,hs2⟩ := r89_source_speed
  obtain ⟨hu1,hu2,hr1,hr2⟩ := r89_root_ratio
  have hu0 : 0<SecondWord.U (b (7/10)) := by linarith
  have hl1 : 0<q 4-p 4*ShortOuterOne.SameContact.ratio (b (7/10)) := by
    norm_num [p,q]
    linarith
  have hl2 : q 4-p 4*ShortOuterOne.SameContact.ratio (b (7/10))<(9735073792/10000000000:ℝ) := by
    norm_num [p,q]
    linarith
  constructor
  · have hD : (657/1000:ℝ)<ShortOuterOne.SameContact.ratioD (b (7/10)) := by
      show (657/1000:ℝ)<Q0/(SecondWord.U (b (7/10)))^3
      rw [lt_div_iff₀ (pow_pos hu0 3)]
      have hcube : (SecondWord.U (b (7/10)))^3<(1812836950017/1000000000000:ℝ)^3 :=
        pow_lt_pow_left₀ hu2 hu0.le (by norm_num)
      norm_num [Q0] at hcube ⊢
      linarith
    have hS : (10436/10000:ℝ)<(speed (7/10))^2 := by nlinarith
    have hm1 := mul_lt_mul'' hD hS (by norm_num) (by norm_num)
    have hm2 := mul_lt_mul'' hl2 (show 1/2-b (7/10)<1/2-146617634711/500000000000 by linarith)
      hl1.le (by linarith)
    have he : second 4 (7/10)=-(p 4)*(ShortOuterOne.SameContact.ratioD (b (7/10))*
        (speed (7/10))^2)+(q 4-p 4*ShortOuterOne.SameContact.ratio (b (7/10)))*
          (1/2-b (7/10)) := by
      simp only [second,l]
      ring
    rw [he]
    norm_num [p] at hm1 hm2 ⊢
    linarith
  · have hm := mul_lt_mul'' hl2 hs2 hl1.le (by linarith)
    rw [r89_first_eq]
    linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Axis.References
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.SourceDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)

abbrev horizontal := SecondWord.OppositeZero.PlusDiagonal.horizontal
abbrev vertical := SecondWord.OppositeZero.PlusDiagonal.vertical
abbrev height := SecondWord.OppositeZero.PlusDiagonal.height
abbrev factor := SecondWord.OppositeZero.PlusDiagonal.factor
abbrev factorD := SecondWord.OppositeZero.PlusDiagonal.factorD
abbrev Geometry := SecondWord.OppositeZero.PlusDiagonal.Domain

def value (r : Row) (x : ℝ) : ℝ := x+c r+(p r+q r)*outerDiagonal+
  v r*(horizontal x-1/2)+t r*(vertical x-1/2)
def first (r : Row) (x : ℝ) : ℝ := 1+(v r*vertical x-t r*horizontal x)*factor x
def second (r : Row) (x : ℝ) : ℝ :=
  -(t r*vertical x+v r*horizontal x)*(factor x)^2+
    (v r*vertical x-t r*horizontal x)*factorD x

lemma target_mem {x : ℝ} (hx : Geometry x) : height x∈Icc 0 outerDiagonal :=
  ⟨hx.2,by linarith [(SecondWord.OppositeZero.PlusDiagonal.target_bounds hx).2,
    fine_outer_endpoint_bounds.2]⟩

lemma coordinates {x : ℝ} (hx : Geometry x) :
    U (height x)=horizontal x ∧ W (height x)=vertical x := by
  have hdata := SecondWord.OppositeZero.PlusDiagonal.data hx.1
  have hrad := hdata.2.2.2.2.1
  have hcircle : (horizontal x)^2+(vertical x)^2=Q0 := by
    dsimp [horizontal,vertical,SecondWord.OppositeZero.PlusDiagonal.horizontal,SecondWord.OppositeZero.PlusDiagonal.vertical]
    linear_combination hrad+
      ((SecondWord.OppositeZero.PlusDiagonal.Y x)^2+(SecondWord.OppositeZero.PlusDiagonal.Z x)^2)*(Real.sin_sq_add_cos_sq x)
  have hactual := UW_circle (outer_domain (target_mem hx))
  have hU := U_positive (outer_domain (target_mem hx))
  have hW : W (height x)=vertical x := by
    dsimp [W,height,SecondWord.OppositeZero.PlusDiagonal.height]
    ring
  rw [hW] at hactual
  exact ⟨by nlinarith [hdata.2.2.2.2.2.1],hW⟩

lemma value_actual (r : Row) {x : ℝ} (hx : Geometry x) :
    value r x=plusCost r (height x) x := by
  have hcoords := coordinates hx
  have hA : arc (height x)=horizontal x-1/2 := by dsimp [U] at hcoords; linarith [hcoords.1]
  have hc : plus (height x) x=outerDiagonal := SecondWord.OppositeZero.PlusDiagonal.contact hx
  rw [plusCost,hc]
  simp only [source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
    ShortOuterOne.SameContact.arc_diagonal,add_zero,zero_mul,zero_add,hA]
  dsimp [value,height,SecondWord.OppositeZero.PlusDiagonal.height]
  ring

lemma value_hasDerivAt (r : Row) {x : ℝ} (hx : Geometry x) :
    HasDerivAt (value r) (first r x) x := by
  have hU : HasDerivAt horizontal (vertical x*factor x) x :=
    SecondWord.OppositeZero.PlusDiagonal.horizontal_hasDerivAt hx.1
  have hV : HasDerivAt vertical (-horizontal x*factor x) x := by
    have h := (SecondWord.OppositeZero.PlusDiagonal.height_hasDerivAt hx.1).add_const (1/2)
    have he : vertical=fun y => SecondWord.OppositeZero.PlusDiagonal.height y+1/2 := by
      funext y
      simp only [vertical,SecondWord.OppositeZero.PlusDiagonal.height]
      ring
    rw [he]
    exact h
  have h1 : HasDerivAt (fun y : ℝ => y+c r+(p r+q r)*outerDiagonal) 1 x := by
    simpa using ((hasDerivAt_id x).add_const (c r)).add_const ((p r+q r)*outerDiagonal)
  have h := (h1.fun_add ((hU.sub_const (1/2)).const_mul (v r))).fun_add
    ((hV.sub_const (1/2)).const_mul (t r))
  have he : value r=fun y => y+c r+(p r+q r)*outerDiagonal+
      v r*(horizontal y-1/2)+t r*(vertical y-1/2) := rfl
  rw [he]
  convert h using 1
  simp only [first]
  ring

lemma first_hasDerivAt (r : Row) {x : ℝ} (hx : Geometry x) :
    HasDerivAt (first r) (second r x) x := by
  have hU : HasDerivAt horizontal (vertical x*factor x) x :=
    SecondWord.OppositeZero.PlusDiagonal.horizontal_hasDerivAt hx.1
  have hV : HasDerivAt vertical (-horizontal x*factor x) x := by
    have h := (SecondWord.OppositeZero.PlusDiagonal.height_hasDerivAt hx.1).add_const (1/2)
    have he : vertical=fun y => SecondWord.OppositeZero.PlusDiagonal.height y+1/2 := by
      funext y
      simp only [vertical,SecondWord.OppositeZero.PlusDiagonal.height]
      ring
    rw [he]
    exact h
  have hf : HasDerivAt factor (factorD x) x :=
    SecondWord.OppositeZero.PlusDiagonal.factor_hasDerivAt hx.1
  have h := (((hV.const_mul (v r)).fun_sub (hU.const_mul (t r))).fun_mul hf).const_add 1
  have he : first r=fun y => 1+(v r*vertical y-t r*horizontal y)*factor y := rfl
  rw [he]
  convert h using 1
  simp only [second]
  ring

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
  have hV : (1/2:ℝ)≤vertical x := by
    have h2 : 0≤SecondWord.OppositeZero.PlusDiagonal.height x := hx.2
    simp only [SecondWord.OppositeZero.PlusDiagonal.height] at h2
    linarith
  have hpositive : 0<t r*vertical x+v r*horizontal x := by
    fin_cases r <;> norm_num [v,t] <;> linarith
  have htarget := (slope_bounds r (target_mem hx)).2.2
  have hh := mul_pos htarget hU0
  have he : h r (height x)*horizontal x=t r*horizontal x-v r*vertical x := by
    dsimp [h,ratio]
    change (t r-v r*(W (height x)/U (height x)))*horizontal x=_
    rw [hcoords.1,hcoords.2]
    field_simp [hU0.ne']
  rw [he] at hh
  exact ⟨hpositive,by linarith⟩

lemma curvature_negative (r : Row) {x : ℝ} (hx : Geometry x) : second r x<0 := by
  have hwork := work_signs r hx
  have hdata := SecondWord.OppositeZero.PlusDiagonal.data hx.1
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
    by show plus 0 e∈_; rw [hcontact]; exact Negative.diagonal_mem⟩
  exact SecondWord.OppositeZero.PlusDiagonal.original hd hcontact

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
  have hh := SecondWord.OppositeZero.PlusDiagonal.height_antitone hya hE.1.1 hy.2
  have h0 : SecondWord.OppositeZero.PlusDiagonal.height e=0 := hE.2
  rw [h0] at hh
  exact ⟨hya,hh⟩

lemma before_event {e x : ℝ} (he : Same.Event.IsEvent e) (hx : Geometry x) : x≤e := by
  have hE := event_geometry he
  by_contra! hlarge
  have hm := SecondWord.OppositeZero.PlusDiagonal.shifted_height_antitone hE.1.1 hx.1 hlarge.le
  have h0 : SecondWord.OppositeZero.PlusDiagonal.height e=0 := hE.2
  have h2 : 0≤SecondWord.OppositeZero.PlusDiagonal.height x := hx.2
  simp only [h0] at hm
  linarith

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
    have hc0 : plus (height 0) 0=outerDiagonal := SecondWord.OppositeZero.PlusDiagonal.contact hz
    have hh0 : height 0=1-outerDiagonal := SecondWord.OppositeZero.PlusDiagonal.height_zero
    rw [value_actual r hz,plusCost,hc0,hh0]
    have hh := aligned_original r Negative.diagonal_mem low_mem (by dsimp [low]; ring)
    simpa only [zero_add] using hh
  · have hcE : plus (height e) e=outerDiagonal := SecondWord.OppositeZero.PlusDiagonal.contact hE.1
    rw [value_actual r hE.1,plusCost,hcE,hE.2]
    have hh := event_cost r he
    simp only [source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
      ShortOuterOne.SameContact.arc_diagonal,ShortOuterOne.SameContact.arc_zero,
      mul_zero,add_zero,zero_mul,zero_add]
    linarith

theorem original_lower (r : Row) {B x : ℝ} (hd : PlusDomain B x)
    (hb : plus B x=outerDiagonal) : (89809/100000:ℝ)<plusCost r B x := by
  obtain ⟨hx,hB⟩ := SecondWord.OppositeZero.PlusDiagonal.original hd hb
  have hB' : height x=B := hB
  have hh := lower r hx
  rwa [value_actual r hx,hB'] at hh

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.SourceDiagonal
end
end
end
