module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSamePositive
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoPrimaryBound

/-!
# The complete same-sign source-diagonal primary arc

Uncompiled transcription of Section 3.1 of
`HAND_SHORT_WORD_SAME_SIGN_PRIMARY_COMPLETE_WITHOUT_TABLES.md`.
The circle rotation is the existing exact primary-diagonal geometry.
The cost is concave until the unique simultaneous-diagonal event.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)
open StationaryPrimitives (Interval)
open SecondWord.SameZero.PJ.Reference (sinBox cosBox)

abbrev Z := SecondWord.NegativeTwo.PrimaryDiagonal.Z
abbrev Y := SecondWord.NegativeTwo.PrimaryDiagonal.Y
abbrev horizontal := SecondWord.NegativeTwo.PrimaryDiagonal.horizontal
abbrev vertical := SecondWord.NegativeTwo.PrimaryDiagonal.vertical
abbrev height := SecondWord.NegativeTwo.PrimaryDiagonal.height
abbrev factor := SecondWord.NegativeTwo.PrimaryDiagonal.factor
abbrev factorD := SecondWord.NegativeTwo.PrimaryDiagonal.factorD
abbrev Domain := SecondWord.NegativeTwo.PrimaryDiagonal.Domain

def joinContact (x : ℝ) : ℝ :=
  1/2+(1/2-outerDiagonal)*Real.cos x+(outerDiagonal+1/2)*Real.sin x
def joinSpeed (x : ℝ) : ℝ :=
  (outerDiagonal-1/2)*Real.sin x+(outerDiagonal+1/2)*Real.cos x
def IsEvent (e : ℝ) : Prop := e∈Ioo (2779/5000:ℝ) (5559/10000) ∧ joinContact e=outerDiagonal

lemma joinContact_hasDerivAt (x : ℝ) : HasDerivAt joinContact (joinSpeed x) x := by
  convert (((Real.hasDerivAt_cos x).const_mul (1/2-outerDiagonal)).const_add (1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (outerDiagonal+1/2)) using 1 <;>
    dsimp [joinContact,joinSpeed] <;> ring

lemma joinContact_strictMono : StrictMonoOn joinContact (Icc 0 (7/10)) := by
  apply strict_increase_of_reserve
    (fun x _ => (joinContact_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => joinContact_hasDerivAt x) (show (0:ℝ)<1 by norm_num)
  intro x hx
  have ht := positive_trig (Ioo_subset_Icc_self hx)
  have hs := mul_nonneg (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1]) ht.2.2.1
  have hc := mul_le_mul (show (139/100:ℝ)≤outerDiagonal+1/2 by linarith [outer_endpoint_bounds.2.2.1])
    (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) (by norm_num)
    (show 0≤outerDiagonal+1/2 by linarith [outer_endpoint_bounds.2.2.1])
  dsimp [joinSpeed]
  nlinarith

def joinBox (x : ℝ) (hx : 0≤x) : Interval (joinContact x) := by
  convert (((Interval.point (1/2)).add
    (((Interval.point (1/2)).sub RoleFour.dBox).mul (cosBox x hx))).add
      ((RoleFour.dBox.add (Interval.point (1/2))).mul (sinBox x hx))) using 1 <;>
    dsimp [joinContact] <;> ring

lemma join_endpoints : joinContact (2779/5000)<outerDiagonal ∧
    outerDiagonal<joinContact (5559/10000) := by
  have hl := (joinBox (2779/5000) (by norm_num)).mem
  have hu := (joinBox (5559/10000) (by norm_num)).mem
  have hL : (joinBox (2779/5000) (by norm_num)).hi<RoleFour.dBox.lo := by
    norm_num [joinBox,RoleFour.dBox,SecondWord.SameZero.PJ.Reference.sinBox,
      SecondWord.SameZero.PJ.Reference.cosBox,Interval.of_bounds,Interval.point,Interval.add,
      Interval.sub,Interval.neg,Interval.mul,HighOrderTaylor.S17,HighOrderTaylor.S15,
      HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,
      HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8]
  have hU : RoleFour.dBox.hi<(joinBox (5559/10000) (by norm_num)).lo := by
    norm_num [joinBox,RoleFour.dBox,SecondWord.SameZero.PJ.Reference.sinBox,
      SecondWord.SameZero.PJ.Reference.cosBox,Interval.of_bounds,Interval.point,Interval.add,
      Interval.sub,Interval.neg,Interval.mul,HighOrderTaylor.S17,HighOrderTaylor.S15,
      HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,
      HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8]
  exact ⟨hl.2.trans_lt (hL.trans_le RoleFour.dBox.mem.1),
    RoleFour.dBox.mem.2.trans_lt (hU.trans_le hu.1)⟩

theorem exists_event : ∃e,IsEvent e := by
  have hc : Continuous joinContact := by dsimp [joinContact]; fun_prop
  obtain ⟨e,he,heq⟩ := intermediate_value_Icc
    (show (2779/5000:ℝ)≤5559/10000 by norm_num) hc.continuousOn
    (show outerDiagonal∈Icc (joinContact (2779/5000)) (joinContact (5559/10000)) from
      ⟨join_endpoints.1.le,join_endpoints.2.le⟩)
  have hl : (2779/5000:ℝ)<e := lt_of_le_of_ne he.1 (by
    intro hh
    rw [←hh] at heq
    linarith [join_endpoints.1])
  have hu : e<(5559/10000:ℝ) := lt_of_le_of_ne he.2 (by
    intro hh
    rw [hh] at heq
    linarith [join_endpoints.2])
  exact ⟨e,⟨hl,hu⟩,heq⟩

lemma event_angle {e : ℝ} (he : IsEvent e) : e∈Icc 0 (7/10) :=
  ⟨by linarith [he.1.1],by linarith [he.1.2]⟩

lemma diagonal_state : OuterState outerDiagonal outerDiagonal :=
  ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl,by nlinarith [diagonal_circle]⟩

lemma event_height {e : ℝ} (he : IsEvent e) : height e=outerDiagonal := by
  apply SecondWord.NegativeTwo.PrimaryDiagonal.original_height diagonal_state (event_angle he)
  simpa [SecondWord.NegativeTwo.lowerSource,joinContact] using he.2

lemma event_unique {e f : ℝ} (he : IsEvent e) (hf : IsEvent f) : e=f := by
  rcases lt_trichotomy e f with h | h | h
  · have hh := joinContact_strictMono (event_angle he) (event_angle hf) h
    rw [he.2,hf.2] at hh
    exact False.elim (lt_irrefl _ hh)
  · exact h
  · have hh := joinContact_strictMono (event_angle hf) (event_angle he) h
    rw [he.2,hf.2] at hh
    exact False.elim (lt_irrefl _ hh)

lemma before_event {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) : Domain x := by
  have hx' : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans (event_angle he).2⟩
  have hh := SecondWord.NegativeTwo.PrimaryDiagonal.height_monotone hx' (event_angle he) hx.2
  rw [event_height he] at hh
  exact ⟨hx',hh⟩

lemma bounded_by_event {e x : ℝ} (he : IsEvent e) (hx : Domain x) : x≤e := by
  by_contra! hbad
  have hh := SecondWord.NegativeTwo.PrimaryDiagonal.height_half_monotone
    (event_angle he) hx.1 hbad.le
  rw [event_height he] at hh
  linarith [hx.2]

lemma physical_state {x : ℝ} (hx : Domain x) : OuterState (horizontal x-1/2) (height x) := by
  have hc := SecondWord.NegativeTwo.PrimaryDiagonal.circle hx.1
  have hp := SecondWord.NegativeTwo.PrimaryDiagonal.coordinates_positive hx.1
  have hB := SecondWord.NegativeTwo.PrimaryDiagonal.target_mem hx
  have hV : vertical x≤outerDiagonal+1/2 := by
    change vertical x-1/2≤outerDiagonal at hx.2
    linarith
  have hV2 := pow_le_pow_left₀ hp.2.le hV 2
  have horder : vertical x≤horizontal x := by nlinarith [diagonal_circle]
  refine ⟨hB.1,?_,?_⟩
  · change vertical x-1/2≤horizontal x-1/2
    linarith
  · change (horizontal x-1/2+1/2)^2+(vertical x-1/2+1/2)^2=Q0
    nlinarith only [hc]

lemma actual_arc {x : ℝ} (hx : Domain x) : arc (height x)=horizontal x-1/2 :=
  (SameContact.actual_arc (physical_state hx)).1

def cost (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2-x+c r+(p r-q r)*outerDiagonal-P r*(horizontal x-1/2)+t r*(vertical x-1/2)
def first (r : Row) (x : ℝ) : ℝ := -1+(t r*horizontal x+P r*vertical x)*factor x
def second (r : Row) (x : ℝ) : ℝ :=
  (P r*horizontal x-t r*vertical x)*(factor x)^2+
    (t r*horizontal x+P r*vertical x)*factorD x

lemma cost_hasDerivAt (r : Row) {x : ℝ} (hx : Domain x) :
    HasDerivAt (cost r) (first r x) x := by
  convert (((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c r+(p r-q r)*outerDiagonal)).sub
      (((SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt hx.1).
        sub_const (1/2)).const_mul (P r))).add
          (((SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt hx.1).
            sub_const (1/2)).const_mul (t r))) using 1 <;>
    dsimp [cost,first,SecondWord.NegativeTwo.PrimaryDiagonal.speed] <;> ring

lemma first_hasDerivAt (r : Row) {x : ℝ} (hx : Domain x) :
    HasDerivAt (first r) (second r x) x := by
  convert ((((SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt hx.1).const_mul (t r)).
    add ((SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt hx.1).const_mul (P r))).
      mul (SecondWord.NegativeTwo.PrimaryDiagonal.factor_hasDerivAt hx.1)).const_add (-1)
    using 1 <;> dsimp [first,second,SecondWord.NegativeTwo.PrimaryDiagonal.speed] <;> ring

lemma curvature_negative (r : Row) {x : ℝ} (hx : Domain x) : second r x<0 := by
  have hp := SecondWord.NegativeTwo.PrimaryDiagonal.coordinates_positive hx.1
  have hf := SecondWord.NegativeTwo.PrimaryDiagonal.factor_bounds hx.1
  have hfd := SecondWord.NegativeTwo.PrimaryDiagonal.factorD_negative hx.1
  have hstate := physical_state hx
  have horder : vertical x≤horizontal x := by
    change vertical x-1/2≤horizontal x-1/2 at hstate.2.1
    linarith
  have hP : P r≤0 := (coefficient_bounds r).2.2.2.2.1
  have ht : 0<t r := by fin_cases r <;> norm_num [t]
  have hX : P r*horizontal x-t r*vertical x<0 := by
    have h1 := mul_nonpos_of_nonpos_of_nonneg hP (by linarith [hp.1] : 0≤horizontal x)
    have h2 := mul_pos ht hp.2
    linarith
  have hY : 0<t r*horizontal x+P r*vertical x := by
    have h1 := mul_le_mul_of_nonpos_left horder hP
    have h2 := mul_pos (coefficient_bounds r).2.2.2.2.2.1
      (show 0<horizontal x by linarith [hp.1])
    nlinarith
  have hfirst := mul_neg_of_neg_of_pos hX (pow_pos (by linarith [hf.1] : 0<factor x) 2)
  have hsecond := mul_neg_of_pos_of_neg hY hfd
  dsimp [second]
  linarith

lemma initial_value (r : Row) : cost r 0=aligned r b0 := by
  have h0 : Domain 0 := by
    refine ⟨by norm_num,?_⟩
    rw [SecondWord.NegativeTwo.PrimaryDiagonal.height_zero]
    simpa [b0] using b0_mem.2
  have harc := actual_arc h0
  rw [SecondWord.NegativeTwo.PrimaryDiagonal.height_zero] at harc
  have hV : vertical 0-1/2=b0 := SecondWord.NegativeTwo.PrimaryDiagonal.height_zero
  have he : 1-b0=outerDiagonal := by dsimp [b0]; ring
  dsimp [cost,aligned,source,target]
  rw [he,SameContact.arc_diagonal,hV,←harc]
  dsimp [b0]
  ring

lemma final_value (r : Row) {e : ℝ} (he : IsEvent e) : (361/400:ℝ)<cost r e := by
  have hed := before_event he (show e∈Icc 0 e from ⟨(event_angle he).1,le_rfl⟩)
  have hA := actual_arc hed
  rw [event_height he,SameContact.arc_diagonal] at hA
  have hB : vertical e-1/2=outerDiagonal := event_height he
  have hp := pi_hand_enclosure.1
  have hd := ShortMixedZero.fine_diagonal_bounds
  dsimp [cost]
  rw [←hA,hB]
  fin_cases r <;> norm_num [c,p,q,P,t] <;> linarith [he.1.2]

theorem cost_lower (r : Row) {x : ℝ} (hx : Domain x) : (8981/10000:ℝ)<cost r x := by
  obtain ⟨e,he⟩ := exists_event
  have hdom := fun y hy => before_event he (show y∈Icc 0 e from hy)
  have hc : ConcaveOn ℝ (Icc 0 e) (cost r) := concave_of_deriv2
    (fun y hy => cost_hasDerivAt r (hdom y hy))
    (fun y hy => first_hasDerivAt r (hdom y hy))
    (fun y hy => (curvature_negative r (hdom y hy)).le)
  apply concave_gt_of_endpoints hc ⟨hx.1.1,bounded_by_event he hx⟩
  · rw [initial_value]
    exact aligned_lower r ⟨b0_mem.1,le_rfl⟩
  · linarith [final_value r he]

theorem original_contact (r : Row) {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hc : 1/2+(1/2-B)*Real.cos x+(A+1/2)*Real.sin x=outerDiagonal) :
    (8981/10000:ℝ)<Real.pi/2-x+c r+(p r-q r)*outerDiagonal-P r*A+t r*B := by
  have hh := SecondWord.NegativeTwo.PrimaryDiagonal.original_height ht hx
    (by simpa [SecondWord.NegativeTwo.lowerSource] using hc)
  have hd : Domain x := ⟨hx,by rw [hh]; exact (outer_bounds ht).2.2.2.1⟩
  have hA := actual_arc hd
  rw [hh,(SameContact.actual_arc ht).1] at hA
  have hB : vertical x-1/2=B := hh
  have hb := cost_lower r hd
  dsimp [cost] at hb
  rw [←hA,hB] at hb
  exact hb

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Diagonal
