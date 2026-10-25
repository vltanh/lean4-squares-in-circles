module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameData
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJBoundaryReferences

/-!
# Eight squares: the initial favorable zero contact and its speed

The event `IsEvent e`, at which the contact with target coordinate zero reaches the diagonal,
exists (`exists_event`). Its speed lies strictly between `.9628` and `.963` (`speed_corrected`),
and the bound `.9628` gives `.557 * .9628 > .536` (`ratio_slope_reserve`), the reserve for the
ratio slope `-.536`.
-/

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
