module

public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroLKReference
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJBoundaryReferences

/-!
# Eight squares: the initial favorable zero contact and its speed

The event `IsEvent e`, at which the contact with target coordinate zero reaches the diagonal,
exists (`exists_event`). Its speed lies strictly between `.9628` and `.963` (`speed_corrected`),
and the bound `.9628` gives `.557 * .9628 > .536` (`ratio_slope_reserve`), the reserve for the
ratio slope `-.536`.
-/

section
/-!
## The four favorable same-sign zero contacts of the short word

The four literal tuples retain their original source and target labels.
The contact coordinate is exactly the existing same-sign contact, so its
circle and projection identities are shared without changing its domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open SecondWord (RoleLabel U W outer_domain outer_zero_mem outer_ratio_bounds)

abbrev Row := Fin 4

def c : Row→ℝ := ![-6130/100000,27086/100000,-75097/100000,74349/100000]
def p : Row→ℝ := ![0,-9133/100000,51554/100000,-19335/100000]
def q : Row→ℝ := ![94766/100000,88074/100000,119909/100000,76744/100000]
def P : Row→ℝ := ![0,13422/100000,0,33147/100000]
def t : Row→ℝ := ![99940/100000,103828/100000,71553/100000,113360/100000]

def source (r : Row) : RoleLabel := ⟨c r,p r,q r,0,0⟩
def target (r : Row) : RoleLabel := ⟨0,P r,t r,0,0⟩
abbrev contact := SecondWord.SameZero.b
abbrev speed := SecondWord.SameZero.v
abbrev projection := SecondWord.SameZero.k
abbrev Domain := SecondWord.SameZero.Domain

def l (r : Row) (b : ℝ) : ℝ := q r-p r*ratio b
def alpha (r : Row) (b : ℝ) : ℝ := -p r*ratioD b
def cost (r : Row) (B x : ℝ) : ℝ :=
  x+c r+p r*arc (contact B x)+q r*contact B x-P r*arc B-t r*B
def angleFirst (r : Row) (B x : ℝ) : ℝ := 1-l r (contact B x)*speed B x
def angleSecond (r : Row) (B x : ℝ) : ℝ :=
  alpha r (contact B x)*(speed B x)^2-l r (contact B x)*(contact B x-1/2)
def targetFirst (r : Row) (B x : ℝ) : ℝ :=
  l r (contact B x)*projection B x+P r*ratio B-t r
def targetSecond (r : Row) (B x : ℝ) : ℝ :=
  alpha r (contact B x)*(projection B x)^2+
    (l r (contact B x)*Real.sin x+P r)*ratioD B

def Coupled (r : Row) : Prop := r≠2

lemma coefficient_signs (r : Row) : 0<q r ∧ 0<t r ∧ 0≤P r := by
  fin_cases r <;> norm_num [q,t,P]
lemma coupled_signs (r : Row) (hr : Coupled r) : p r≤0 ∧ 0≤P r := by
  fin_cases r
  · norm_num [p,P]
  · norm_num [p,P]
  · exact (hr rfl).elim
  · norm_num [p,P]

lemma source_derivative (r : Row) (b : ℝ) : (source r).d1 b=l r b := by
  simp [source,RoleLabel.d1,l]
lemma target_derivative (r : Row) (B : ℝ) :
    (target r).d1 B=t r-P r*ratio B := by simp [target,RoleLabel.d1]
lemma cost_value (r : Row) (B x : ℝ) :
    cost r B x=SecondWord.SameZero.value (source r) (target r) B x := by
  simp [cost,SecondWord.SameZero.value,RoleLabel.outer,RoleLabel.eval,source,target]
  ring

lemma l_positive (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0<l r b := by
  have hr := outer_ratio_bounds hb
  fin_cases r <;> norm_num [l,p,q] <;> linarith [hr.1,hr.2.1]
lemma alpha_nonneg (r : Row) (hr : Coupled r) {b : ℝ}
    (hb : b∈Icc 0 outerDiagonal) : 0≤alpha r b :=
  mul_nonneg (neg_nonneg.mpr (coupled_signs r hr).1)
    (ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)).le

lemma l_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (l r) (alpha r b) b := by
  have h := ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul
    (p r)).const_sub (q r)
  exact h.congr_deriv (by simp only [alpha]; ring)
lemma alpha_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (alpha r) (-p r*ratioDD b) b :=
  (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).const_mul (-p r)

lemma l_monotone (r : Row) (hr : Coupled r) :
    MonotoneOn (l r) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hb => (l_hasDerivAt r hb).continuousAt.continuousWithinAt)
    (fun _ hb => l_hasDerivAt r (Ioo_subset_Icc_self hb))
    (fun _ hb => alpha_nonneg r hr (Ioo_subset_Icc_self hb))

lemma cost_angle_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (cost r B) (angleFirst r B x) x := by
  have hh := SecondWord.SameZero.value_angle_hasDerivAt (source r) (target r) hd
  have hfun : cost r B=SecondWord.SameZero.value (source r) (target r) B :=
    funext fun y => cost_value r B y
  rw [hfun]
  convert hh using 1
  simp only [angleFirst,SecondWord.SameZero.angleFirst,source_derivative]

lemma angleFirst_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (angleFirst r B) (angleSecond r B x) x := by
  have h := (((l_hasDerivAt r hd.2.2).comp x (SecondWord.SameZero.b_angle_hasDerivAt B x)).mul
    (SecondWord.SameZero.v_angle_hasDerivAt B x)).const_sub 1
  convert h using 1
  · funext y
    rfl
  · simp only [angleSecond,Function.comp_apply]
    ring

lemma cost_target_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (fun B => cost r B x) (targetFirst r B x) B := by
  have hh := SecondWord.SameZero.value_target_hasDerivAt (source r) (target r) hd
  simp only [←cost_value,SecondWord.SameZero.targetFirst,source_derivative,
    target_derivative] at hh
  exact hh.congr_deriv (by simp only [targetFirst]; ring)

lemma targetFirst_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (fun B => targetFirst r B x) (targetSecond r B x) B := by
  have hk : HasDerivAt (fun B => projection B x) (ratioD B*Real.sin x) B :=
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).mul_const
      (Real.sin x)).const_add (Real.cos x)
  convert (((((l_hasDerivAt r hd.2.2).comp B
    (SecondWord.SameZero.b_target_hasDerivAt hd.1 x)).mul hk).add
      ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).const_mul
        (P r))).sub_const (t r)) using 1 <;> dsimp [targetFirst,targetSecond]
  ring

lemma angle_positive {B x : ℝ} (hd : Domain B x) : 0<x := by
  by_contra! hx
  have hz : x=0 := le_antisymm hx hd.2.1.1
  have hb := hd.2.2.2
  rw [hz] at hb
  norm_num [contact,SecondWord.SameZero.b] at hb
  linarith [hd.1.1,outer_endpoint_bounds.2.2.2]

lemma source_monotone (r : Row) : MonotoneOn (source r).outer (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => ((source r).outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => (source r).outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by rw [source_derivative]; exact (l_positive r (Ioo_subset_Icc_self hb)).le)

/-- The first contact has no larger cost than the original weak contact. -/
lemma original_to_contact (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    Domain B x ∧ cost r B x≤x+c r+p r*a+q r*b-P r*A-t r*B := by
  obtain ⟨hd,hb⟩ := SecondWord.SameZero.original_contact hs ht hx hm
  have hh := source_monotone r hd.2.2 ⟨hs.1,(outer_bounds hs).2.2.2.1⟩ hb
  rw [(source r).outer_actual hs] at hh
  have hA := (ShortOuterOne.SameContact.actual_arc ht).1
  refine ⟨hd,?_⟩
  dsimp [cost]
  rw [hA]
  dsimp [source,RoleLabel.outer,RoleLabel.eval] at hh
  linarith

end SquaresInCircles.Eight.ShortOuterZero.Same
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Event
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (sinBox cosBox dBox dUBox aBox zeroSourceBox)

abbrev lo : ℝ := 134079/1250000
abbrev hi : ℝ := 1072633/10000000

def IsEvent (e : ℝ) : Prop := e∈Ioo lo hi ∧ contact 0 e=outerDiagonal

macro "event_reference_arithmetic" : tactic => `(tactic|
  norm_num [lo,hi,SecondWord.SameZero.PJ.Reference.sinBox,
    SecondWord.SameZero.PJ.Reference.cosBox,SecondWord.SameZero.PJ.Reference.dBox,
    SecondWord.SameZero.PJ.Reference.dUBox,SecondWord.SameZero.PJ.Reference.aBox,
    SecondWord.SameZero.PJ.Reference.zeroSourceBox,HighOrderTaylor.S17,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8,Interval.of_bounds,Interval.point,Interval.add,
    Interval.sub,Interval.neg,Interval.mul,Interval.square,Interval.cube,
    Interval.div,Interval.inv,c,p,q,P,t,Q0])

private lemma r49_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r49_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r49_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl
private lemma r49_mp_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).hi = S.hi := by subst e; rfl

private lemma r49_zeroSourceBox_lo (x : ℝ) (hx : 0≤x) : (zeroSourceBox x hx).lo =
    (((Interval.point (1/2)).add ((Interval.point (1/2)).mul (cosBox x hx))).sub
      ((aBox.sub (Interval.point (1/2))).mul (sinBox x hx))).lo := by
  unfold zeroSourceBox
  rw [r49_mpr_lo, r49_mp_lo]
  · norm_num
  · simp only [SecondWord.SameZero.b,ShortOuterOne.SameContact.arc_zero]
    norm_num
private lemma r49_zeroSourceBox_hi (x : ℝ) (hx : 0≤x) : (zeroSourceBox x hx).hi =
    (((Interval.point (1/2)).add ((Interval.point (1/2)).mul (cosBox x hx))).sub
      ((aBox.sub (Interval.point (1/2))).mul (sinBox x hx))).hi := by
  unfold zeroSourceBox
  rw [r49_mpr_hi, r49_mp_hi]
  · norm_num
  · simp only [SecondWord.SameZero.b,ShortOuterOne.SameContact.arc_zero]
    norm_num

local macro "r49_event_arith" : tactic => `(tactic|
  norm_num [lo,hi,SecondWord.SameZero.PJ.Reference.sinBox,
    SecondWord.SameZero.PJ.Reference.cosBox,SecondWord.SameZero.PJ.Reference.dBox,
    SecondWord.SameZero.PJ.Reference.aBox,HighOrderTaylor.S17,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8,Interval.of_bounds,Interval.point,Interval.add,
    Interval.sub,Interval.neg,Interval.mul,Interval.square,Interval.cube,
    Interval.div,Interval.inv,Q0])

lemma endpoint_signs : outerDiagonal<contact 0 lo ∧ contact 0 hi<outerDiagonal := by
  let L := zeroSourceBox lo (by norm_num [lo])
  let H := zeroSourceBox hi (by norm_num [hi])
  have hL : dBox.hi<L.lo := by dsimp only [L]; rw [r49_zeroSourceBox_lo]; r49_event_arith
  have hH : H.hi<dBox.lo := by dsimp only [H]; rw [r49_zeroSourceBox_hi]; r49_event_arith
  exact ⟨dBox.mem.2.trans_lt (hL.trans_le L.mem.1),
    H.mem.2.trans_lt (hH.trans_le dBox.mem.1)⟩

theorem exists_event : ∃e, IsEvent e := by
  have hc : Continuous (contact 0) := by
    have hb : contact 0=fun t => 1/2+(0+1/2)*Real.cos t-(arc 0-1/2)*Real.sin t := rfl
    rw [hb]
    fun_prop
  obtain ⟨e,he,heq⟩ := intermediate_value_Icc (show lo≤hi by norm_num [lo,hi])
    hc.neg.continuousOn
    (show -outerDiagonal∈Icc (-contact 0 lo) (-contact 0 hi) from
      ⟨by linarith [endpoint_signs.1],by linarith [endpoint_signs.2]⟩)
  simp only [Pi.neg_apply] at heq
  have hcontact : contact 0 e=outerDiagonal := by linarith
  have hl : lo<e := lt_of_le_of_ne he.1 (by
    intro hh
    rw [←hh] at hcontact
    exact (ne_of_lt endpoint_signs.1) hcontact.symm)
  have hu : e<hi := lt_of_le_of_ne he.2 (by
    intro hh
    rw [hh] at hcontact
    exact (ne_of_lt endpoint_signs.2) hcontact)
  exact ⟨e,⟨hl,hu⟩,hcontact⟩

lemma angle_mem {e : ℝ} (he : IsEvent e) : e∈Icc 0 (7/10) := by
  have h1 := he.1.1
  have h2 := he.1.2
  norm_num [lo,hi] at h1 h2
  exact ⟨by linarith,by linarith⟩

def eventSin {e : ℝ} (he : IsEvent e) : Interval (Real.sin e) :=
  Interval.of_bounds ⟨(HighOrderTaylor.S15_le_sin (show 0≤lo by norm_num [lo])).trans
    (sin_mono (by norm_num [lo]) (angle_mem he) he.1.1.le),
    (sin_mono (angle_mem he) (by norm_num [hi]) he.1.2.le).trans
      (HighOrderTaylor.sin_le_S17 (show 0≤hi by norm_num [hi]))⟩
def eventCos {e : ℝ} (he : IsEvent e) : Interval (Real.cos e) :=
  Interval.of_bounds ⟨(HighOrderTaylor.C18_le_cos (show 0≤hi by norm_num [hi])).trans
    (cos_anti (angle_mem he) (by norm_num [hi]) he.1.2.le),
    (cos_anti (by norm_num [lo]) (angle_mem he) he.1.1.le).trans
      (HighOrderTaylor.cos_le_C16 (show 0≤lo by norm_num [lo]))⟩

def eventSpeed {e : ℝ} (he : IsEvent e) : Interval (speed 0 e) := by
  let V := ((aBox.sub (Interval.point (1/2))).mul (eventCos he)).add
    ((Interval.point (1/2)).mul (eventSin he))
  simpa [speed,SecondWord.SameZero.v,ShortOuterOne.SameContact.arc_zero] using V

private lemma r49_eventSpeed_lo {e : ℝ} (he : IsEvent e) : (eventSpeed he).lo =
    (((aBox.sub (Interval.point (1/2))).mul (eventCos he)).add
      ((Interval.point (1/2)).mul (eventSin he))).lo := by
  unfold eventSpeed
  rw [r49_mpr_lo, r49_mp_lo]
  · norm_num
  · simp only [speed,SecondWord.SameZero.v,ShortOuterOne.SameContact.arc_zero]
    norm_num
private lemma r49_eventSpeed_hi {e : ℝ} (he : IsEvent e) : (eventSpeed he).hi =
    (((aBox.sub (Interval.point (1/2))).mul (eventCos he)).add
      ((Interval.point (1/2)).mul (eventSin he))).hi := by
  unfold eventSpeed
  rw [r49_mpr_hi, r49_mp_hi]
  · norm_num
  · simp only [speed,SecondWord.SameZero.v,ShortOuterOne.SameContact.arc_zero]
    norm_num

/-- The speed at the event lies strictly between `.9628` and `.963`. -/
lemma speed_corrected {e : ℝ} (he : IsEvent e) :
    (2407/2500:ℝ)<speed 0 e ∧ speed 0 e<(963/1000:ℝ) := by
  have hl : (2407/2500:ℝ)<(eventSpeed he).lo := by
    rw [r49_eventSpeed_lo]
    dsimp only [eventSin,eventCos]
    r49_event_arith
  have hu : (eventSpeed he).hi<(963/1000:ℝ) := by
    rw [r49_eventSpeed_hi]
    dsimp only [eventSin,eventCos]
    r49_event_arith
  exact ⟨hl.trans_le (eventSpeed he).mem.1,(eventSpeed he).mem.2.trans_lt hu⟩

lemma ratio_slope_reserve : (536/1000:ℝ)<(557/1000)*(2407/2500) := by norm_num

lemma initial_cost (r : Row) (hr : Coupled r) {e : ℝ} (he : IsEvent e) :
    (11226/12500:ℝ)<e+c r+(p r+q r)*outerDiagonal-P r*outerAxial := by
  let E : Interval e := Interval.of_bounds ⟨he.1.1.le,he.1.2.le⟩
  let V := (((E.add (Interval.point (c r))).add
    ((Interval.point (p r+q r)).mul dBox)).sub ((Interval.point (P r)).mul aBox))
  have hv : (11226/12500:ℝ)<V.lo := by
    fin_cases r <;> norm_num [Coupled] at hr <;>
      dsimp [V,E] <;> event_reference_arithmetic
  exact hv.trans_le V.mem.1

lemma speed_global_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (69/100:ℝ)<speed 0 x := by
  have tr := positive_trig hx
  have ha := ShortOuterZero.fine_axial_bounds.1
  have hp := mul_le_mul
    (show (914/1000:ℝ)≤outerAxial-1/2 by linarith) tr.1.le
    (by norm_num) (by linarith : 0≤outerAxial-1/2)
  dsimp [speed,SecondWord.SameZero.v]
  rw [ShortOuterOne.SameContact.arc_zero]
  nlinarith [tr.2.2.1]

lemma zero_decrease {x y : ℝ} (hx : x∈Icc 0 (7/10)) (hy : y∈Icc 0 (7/10))
    (hxy : x≤y) : (69/100)*(y-x)≤contact 0 x-contact 0 y := by
  have hm : AntitoneOn (fun u => contact 0 u+(69/100)*u) (Icc 0 (7/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun u _ => ((SecondWord.SameZero.b_angle_hasDerivAt 0 u).add
        ((hasDerivAt_id u).const_mul (69/100))).continuousAt.continuousWithinAt)
      (fun u _ => (SecondWord.SameZero.b_angle_hasDerivAt 0 u).add
        ((hasDerivAt_id u).const_mul (69/100)))
      (fun u hu => by linarith [speed_global_lower (Ioo_subset_Icc_self hu)])
  have hh := hm hx hy hxy
  linarith

lemma before_contact {e B x : ℝ} (he : IsEvent e) (hd : Domain B x) : e≤x := by
  by_contra! hx
  have hh := zero_decrease hd.2.1 (angle_mem he) hx.le
  rw [he.2] at hh
  have ht := SecondWord.SameZero.b_target_monotone hd.2.1
    SecondWord.outer_zero_mem hd.1 hd.1.1
  linarith [hd.2.2.2]

end SquaresInCircles.Eight.ShortOuterZero.Same.Event
end
end
end
