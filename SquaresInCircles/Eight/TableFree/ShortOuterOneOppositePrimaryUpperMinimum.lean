module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperStationary
public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperOneDiagonal
public import SquaresInCircles.Eight.TableFree.ContactMinimumDerivatives

/-!
# The exceptional upper primary owner's early contact minimum

Uncompiled transcription of the compact minimum argument in Section 5.
The complete physical region before the unique stationary-angle event
is compact. Axial, initial-angle and terminal-angle boundaries have
their proved values; the source-axis boundary has a feasible descending
direction. An interior minimum would have a zero target derivative and
a strictly positive angle derivative, which is impossible.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper.Minimum
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)

theorem source_strict_lower {B e x : ℝ} (he : Upper.IsEvent e)
    (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 e) (hxe : x<e) :
    outerDiagonal<contact B x := by
  have hx' := (before_domain he hx).2.1
  have hh := ShortOuterZero.Same.Event.zero_decrease hx' (event_bounds he).2.2 hx.2
  have hh' : (69/100)*(e-x)≤contact 0 x-contact 0 e := by
    simpa [ShortOuterZero.Same.contact] using hh
  rw [he.2] at hh'
  have hmono := (contact_strictMono hx').monotoneOn zero_mem hB hB.1
  have hp : 0<(69/100:ℝ)*(e-x) := mul_pos (by norm_num) (sub_pos.mpr hxe)
  linarith

theorem target_diagonal_infeasible {e x : ℝ} (he : Upper.IsEvent e) (hx : x∈Icc 0 e) :
    outerAxial<contact outerDiagonal x := by
  have hc := early_cos he hx
  have hs := axial_bounds he hx
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hp := mul_lt_mul
    (show (1399/1000:ℝ)<outerDiagonal+1/2 by linarith) hc (by norm_num)
      (by linarith : 0≤outerDiagonal+1/2)
  have hm := mul_le_mul
    (show outerDiagonal-1/2≤(2/5:ℝ) by linarith) hs.2.2.2.2.2.2.2.le
      hs.2.2.2.2.2.2.1 (by norm_num)
  dsimp [contact,SecondWord.SameZero.b]
  rw [SameContact.arc_diagonal]
  linarith [ShortOuterZero.fine_axial_bounds.2]

theorem target_strict {B e x : ℝ} (he : Upper.IsEvent e) (hd : Domain B x) (hx : x≤e) :
    B<outerDiagonal := by
  apply lt_of_le_of_ne hd.1.2
  intro heq
  subst B
  exact (not_lt_of_ge hd.2.2.2) (target_diagonal_infeasible he ⟨hd.2.1.1,hx⟩)

theorem source_axial_first {B e x : ℝ} (he : Upper.IsEvent e) (hd : Domain B x)
    (hx : x≤e) (ha : contact B x=outerAxial) : 0<first 1 B x := by
  have hL : (173/50:ℝ)<sourceD 1 (contact B x) := by
    rw [ha,sourceD,ratio,SameContact.arc_axial]
    norm_num [p,q]
    linarith [ShortOuterZero.fine_axial_bounds.1]
  have hc := early_cos he ⟨hd.2.1.1,hx⟩
  have hk := stateSpeed_lower hd.1 hd.2.1
  have hp := mul_lt_mul hL (hc.trans_le hk) (by norm_num)
    (by linarith : 0≤sourceD 1 (contact B x))
  have hr : 0≤ratio B := (SameContact.ratio_pos (SameContact.outer_domain hd.1)).le
  norm_num [first,P,t]
  nlinarith

theorem minimum_not_source_axial {B e s x : ℝ} (he : Upper.IsEvent e)
    (hs : Stationary.IsEvent s) (hd : Domain B x) (hx : x≤s) (hB : 0<B)
    (ha : contact B x=outerAxial)
    (hmin : ∀D y,Domain D y → y≤s → value 1 B x≤value 1 D y) : False := by
  have hxe : x≤e := by linarith [hs.1.2,(event_bounds he).1]
  have hzero := before_domain he ⟨hd.2.1.1,hxe⟩
  have hdom {D : ℝ} (hD : D∈Icc 0 B) : Domain D x := between_domain hzero hd hD
  have hnecessary := ContactMinimumDerivatives.right_endpoint hB
    (first_target_hasDerivAt 1 hd).continuousAt
    (fun D hD => value_target_hasDerivAt 1 (hdom hD))
    (fun D hD => hmin D x (hdom hD) hx)
  exact (not_lt_of_ge hnecessary) (source_axial_first he hd hxe ha)

theorem interior_not_minimum {B e s x : ℝ} (he : Upper.IsEvent e)
    (hs : Stationary.IsEvent s) (hd : Domain B x)
    (hB : B∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 s)
    (ha : contact B x∈Ioo outerDiagonal outerAxial)
    (hmin : ∀D y,Domain D y → y≤s → value 1 B x≤value 1 D y) : False := by
  let OT : Set ℝ := Ioo 0 outerDiagonal ∩ (fun D => contact D x) ⁻¹' Ioo outerDiagonal outerAxial
  have hCT : Continuous (fun D => contact D x) := by
    dsimp [contact,SecondWord.SameZero.b,arc]
    fun_prop
  have hOT : IsOpen OT := isOpen_Ioo.inter (isOpen_Ioo.preimage hCT)
  have hmemT : B∈OT := ⟨hB,ha⟩
  have hlocalT : IsLocalMin (fun D => value 1 D x) B := by
    filter_upwards [hOT.mem_nhds hmemT] with D hD
    exact hmin D x ⟨Ioo_subset_Icc_self hD.1,hd.2.1,Ioo_subset_Icc_self hD.2⟩ hx.2.le
  have htarget : first 1 B x=0 := hlocalT.hasDerivAt_eq_zero (value_target_hasDerivAt 1 hd)
  let OA : Set ℝ := Ioo 0 s ∩ (contact B) ⁻¹' Ioo outerDiagonal outerAxial
  have hCA : Continuous (contact B) := by dsimp [contact,SecondWord.SameZero.b]; fun_prop
  have hOA : IsOpen OA := isOpen_Ioo.inter (isOpen_Ioo.preimage hCA)
  have hmemA : x∈OA := ⟨hx,ha⟩
  have hlocalA : IsLocalMin (value 1 B) x := by
    filter_upwards [hOA.mem_nhds hmemA] with y hy
    have hy' : y∈Icc 0 (7/10) := ⟨hy.1.1.le,by linarith [hy.1.2,hs.1.2]⟩
    exact hmin B y ⟨hd.1,hy',Ioo_subset_Icc_self hy.2⟩ hy.1.2.le
  have hangle : angleFirst 1 B x=0 := hlocalA.hasDerivAt_eq_zero (value_angle_hasDerivAt 1 hd)
  have hlower := Stationary.stationary_angle_lower he hd
    (show x≤e by linarith [hx.2,hs.1.2,(event_bounds he).1]) htarget
  have hpositive := Stationary.positive_before hs hx.1.le hx.2
  linarith

theorem minimum_lower {B e s x : ℝ} (he : Upper.IsEvent e) (hs : Stationary.IsEvent s)
    (hd : Domain B x) (hx : x≤s)
    (hmin : ∀D y,Domain D y → y≤s → value 1 B x≤value 1 D y) :
    (4489/5000:ℝ)<value 1 B x := by
  have hxe : x<e := by linarith [hx,hs.1.2,(event_bounds he).1]
  have hxearly : x∈Icc 0 e := ⟨hd.2.1.1,hxe.le⟩
  by_cases hfinal : x=s
  · subst x
    exact before_one_after_nine he hd ⟨hs.1.1.le,by linarith [hs.1.2,(event_bounds he).1]⟩
  by_cases hzero : B=0
  · subst B
    exact F_one_lower he hxearly
  have hB : 0<B := lt_of_le_of_ne hd.1.1 (Ne.symm hzero)
  by_cases hinitial : x=0
  · subst x
    have hD := before_domain he (show (0:ℝ)∈Icc 0 e from
      ⟨le_rfl,by linarith [(event_bounds he).1]⟩)
    have hm := endpoint_minimum 1 hD hd hd.1.1
      (by linarith [Reference.initial_H_one] : 0≤first 1 0 0)
    have hf := F_one_lower he (show (0:ℝ)∈Icc 0 e from
      ⟨le_rfl,by linarith [(event_bounds he).1]⟩)
    exact hf.trans_le hm
  by_cases haxis : contact B x=outerAxial
  · exact (minimum_not_source_axial he hs hd hx hB haxis hmin).elim
  have hsource : contact B x∈Ioo outerDiagonal outerAxial :=
    ⟨source_strict_lower he hd.1 hxearly hxe,lt_of_le_of_ne hd.2.2.2 haxis⟩
  have htarget : B∈Ioo 0 outerDiagonal := ⟨hB,target_strict he hd hxe.le⟩
  have hangle : x∈Ioo 0 s :=
    ⟨lt_of_le_of_ne hd.2.1.1 (Ne.symm hinitial),lt_of_le_of_ne hx hfinal⟩
  exact (interior_not_minimum he hs hd htarget hangle hsource hmin).elim

theorem early_contact {B e s x : ℝ} (he : Upper.IsEvent e) (hs : Stationary.IsEvent s)
    (hd : Domain B x) (hx : x≤s) : (4489/5000:ℝ)<value 1 B x := by
  let guard : ℝ×ℝ→ℝ := fun p => outerAxial-contact p.1 p.2
  let objective : ℝ×ℝ→ℝ := fun p => value 1 p.1 p.2
  have hg : Continuous guard := by dsimp [guard,contact,SecondWord.SameZero.b,arc]; fun_prop
  have hf : Continuous objective := by
    dsimp [objective,value,source,target,contact,SecondWord.SameZero.b,arc]
    fun_prop
  obtain ⟨m,hm,hbetter,hmin⟩ := contact_region_minimum hg hf
    (p₀:=(B,x)) ⟨hd.1,⟨hd.2.1.1,hx⟩,sub_nonneg.mpr hd.2.2.2⟩
  have hme : m.2<e := by linarith [hm.2.1.2,hs.1.2,(event_bounds he).1]
  have hmd : Domain m.1 m.2 :=
    ⟨hm.1,⟨hm.2.1.1,by linarith [hm.2.1.2,hs.1.2]⟩,
      (source_strict_lower he hm.1 ⟨hm.2.1.1,hme.le⟩ hme).le,sub_nonneg.mp hm.2.2⟩
  have hlower := minimum_lower he hs hmd hm.2.1.2
    (fun D y hDy hy => hmin (D,y) hDy.1 ⟨hDy.2.1.1,hy⟩ (sub_nonneg.mpr hDy.2.2.2))
  exact hlower.trans_le hbetter

theorem one_contact {B x : ℝ} (hd : Domain B x) : (4489/5000:ℝ)<value 1 B x := by
  obtain ⟨e,he⟩ := Upper.exists_event
  obtain ⟨s,hs⟩ := Stationary.exists_event
  by_cases hafter : e≤x
  · exact OneDiagonal.after_contact he hd hafter
  by_cases hearly : x≤s
  · exact early_contact he hs hd hearly
  · exact before_one_after_nine he hd
      ⟨by linarith [hs.1.1],(lt_of_not_ge hafter).le⟩

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper.Minimum
