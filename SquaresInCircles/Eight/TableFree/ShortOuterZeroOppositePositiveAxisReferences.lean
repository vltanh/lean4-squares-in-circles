module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositePositiveAxisSlopes

/-!
# The three named positive-axis endpoint checks

Uncompiled transcription of Section 3.2. The two convex-derivative
rows have negative final first derivative; the remaining row has a
negative final second derivative and positive final first derivative.
Every interval encloses the literal source contact and its exact speed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis.References
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
lemma r89_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi=(rootThree (radicand Y) s hs hr).hi :=
  r89_mpr_hi r89_shifted_eq (congrArg _ r89_shifted_eq) _

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

def valueBox (r : Row) : Interval (value r (7/10)) := by
  let V := (((Interval.point ((7/10:ℝ)+c r)).add (labelBox (source r) sourceBox rootBox)).add ((Interval.point (v r)).mul aBox))
  convert V using 1
  dsimp [value,plusCost,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval]
  rw [ShortOuterOne.SameContact.arc_zero]
  ring

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

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis.References
