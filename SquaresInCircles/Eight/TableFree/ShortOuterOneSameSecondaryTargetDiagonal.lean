module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameSecondaryDiagonalBound

/-!
# The earlier secondary target-diagonal arc

Uncompiled transcription of Section 4.1 of
`HAND_SHORT_WORD_SAME_SIGN_SECONDARY_COMPLETE_WITHOUT_TABLES.md`.
The exact third derivative is negative throughout the physical arc.
Its first derivative is concave and initially positive, so the cost
has its minimum at alignment or at the simultaneous-diagonal join.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.TargetDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD ratioDD)
open Diagonal (joinContact joinSpeed)

def cost (r : Row) (x : ℝ) : ℝ := Negative.cost r outerDiagonal x
def first (r : Row) (x : ℝ) : ℝ := -1+slope r (joinContact x)*joinSpeed x
def second (r : Row) (x : ℝ) : ℝ :=
  P r*ratioD (joinContact x)*(joinSpeed x)^2+slope r (joinContact x)*(1/2-joinContact x)
def third (r : Row) (x : ℝ) : ℝ := joinSpeed x*
  (P r*ratioDD (joinContact x)*(joinSpeed x)^2+
    3*P r*ratioD (joinContact x)*(1/2-joinContact x)-slope r (joinContact x))

lemma joinSpeed_hasDerivAt (x : ℝ) : HasDerivAt joinSpeed (1/2-joinContact x) x := by
  convert ((Real.hasDerivAt_sin x).const_mul (outerDiagonal-1/2)).add
    ((Real.hasDerivAt_cos x).const_mul (outerDiagonal+1/2)) using 1 <;>
    dsimp [joinSpeed,joinContact] <;> ring

lemma source_range {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    joinContact x∈Icc b0 outerDiagonal := by
  have hx' : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans (Diagonal.event_angle he).2⟩
  have hm := Diagonal.joinContact_strictMono.monotoneOn
  have hlo := hm (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx' hx.1
  have hhi := hm hx' (Diagonal.event_angle he) hx.2
  rw [he.2] at hhi
  norm_num [joinContact] at hlo
  exact ⟨by dsimp [b0]; linarith,hhi⟩

lemma domain {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    Negative.Domain outerDiagonal x := by
  have hb := source_range he hx
  refine ⟨⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩,
    ⟨hx.1,hx.2.trans (Diagonal.event_angle he).2⟩,?_⟩
  rw [diagonal_contact]
  exact ⟨b0_mem.1.trans hb.1,hb.2⟩

lemma speed_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<joinSpeed x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  simpa [Negative.speed,joinSpeed,SameContact.arc_diagonal] using
    Negative.speed_positive hdiag hx

lemma speed_circle (x : ℝ) :
    (joinSpeed x)^2+(joinContact x-1/2)^2=2*outerDiagonal^2+1/2 := by
  dsimp [joinSpeed,joinContact]
  linear_combination (2*outerDiagonal^2+1/2)*(Real.sin_sq_add_cos_sq x)

lemma speed_reserve {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    Q0/2≤(joinSpeed x)^2 := by
  have hb := source_range he hx
  have hdiag := diagonal_circle
  have hnonneg := mul_nonneg (show 0≤joinContact x-b0 by linarith [hb.1])
    (show 0≤outerDiagonal-joinContact x by linarith [hb.2])
  have hc := speed_circle x
  dsimp [b0] at hnonneg
  nlinarith

lemma cost_hasDerivAt (r : Row) {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (cost r) (first r x) x := by
  have hh := Negative.cost_angle_hasDerivAt r (domain he hx)
  simpa [cost,first,Negative.first,Negative.speed,diagonal_contact,joinSpeed,
    SameContact.arc_diagonal] using hh

lemma first_hasDerivAt (r : Row) {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (first r) (second r x) x := by
  have hb := (domain he hx).2.2
  rw [diagonal_contact] at hb
  convert (((Secondary.slope_hasDerivAt r hb).comp x (Diagonal.joinContact_hasDerivAt x)).
    mul (joinSpeed_hasDerivAt x)).const_add (-1) using 1 <;>
    dsimp [first,second] <;> ring

lemma second_hasDerivAt (r : Row) {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (second r) (third r x) x := by
  have hb := (domain he hx).2.2
  rw [diagonal_contact] at hb
  convert ((((SameContact.ratioD_hasDerivAt (SameContact.outer_domain hb)).comp x
    (Diagonal.joinContact_hasDerivAt x)).const_mul (P r)).mul
      ((joinSpeed_hasDerivAt x).pow 2)).add
        (((Secondary.slope_hasDerivAt r hb).comp x (Diagonal.joinContact_hasDerivAt x)).mul
          ((Diagonal.joinContact_hasDerivAt x).const_sub (1/2))) using 1 <;>
    dsimp [second,third] <;> ring

lemma third_negative (r : Row) {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    third r x<0 := by
  let b := joinContact x
  have hb : b∈Icc 0 outerDiagonal := by
    simpa [b,diagonal_contact] using (domain he hx).2.2
  have hs := speed_positive (domain he hx).2.1
  have hl := (Secondary.slope_bounds r hb).1
  have hP := (coefficient_bounds r).2.2.2.2.1
  have hr := SameContact.ratioD_pos (SameContact.outer_domain hb)
  have hrr := SecondWord.ratioDD_positive hb
  have hsum : P r*ratioDD b*(joinSpeed x)^2+
      3*P r*ratioD b*(1/2-b)≤0 := by
    by_cases hsmall : b≤1/2
    · have hfirst := mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hP hrr.le) (sq_nonneg (joinSpeed x))
      have hsecond := mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (show 3*P r≤0 by linarith) hr.le)
        (show 0≤1/2-b by linarith)
      linarith
    · have hbhalf : 1/2≤b := (le_of_not_ge hsmall).le
      have hu := SecondWord.U_positive (SameContact.outer_domain hb)
      have hc := SecondWord.UW_circle (SameContact.outer_domain hb)
      have hU2 : (SecondWord.U b)^2≤Q0-1 := by
        dsimp [SecondWord.W] at hc
        nlinarith
      have hleft : Q0/2≤(b+1/2)*(joinSpeed x)^2 := by
        have hm := mul_nonneg (show 0≤b-1/2 by linarith) (sq_nonneg (joinSpeed x))
        nlinarith [speed_reserve he hx]
      have hright : (b-1/2)*(SecondWord.U b)^2≤(2/5:ℝ)*(Q0-1) := by
        have hm := mul_le_mul (show b-1/2≤(2/5:ℝ) by
          linarith [hb.2,outer_endpoint_bounds.2.2.2]) hU2 (sq_nonneg _) (by norm_num)
        exact hm
      have hgeom : (b-1/2)*(SecondWord.U b)^2≤(b+1/2)*(joinSpeed x)^2 := by
        norm_num [Q0] at hleft hright ⊢
        linarith
      have hid : ratioDD b*(SecondWord.U b)^2=3*(b+1/2)*ratioD b := by
        rw [SecondWord.ratioDD_formula hb]
        dsimp [SecondWord.W]
        field_simp [hu.ne']
        ring
      have hmul := mul_le_mul_of_nonneg_left hgeom (show 0≤3*ratioD b by positivity)
      have hcomp : 3*ratioD b*(b-1/2)≤ratioDD b*(joinSpeed x)^2 := by
        have hUpos := sq_pos_of_pos hu
        apply (mul_le_mul_right hUpos).mp
        calc
          (3*ratioD b*(b-1/2))*(SecondWord.U b)^2 =
              (3*ratioD b)*((b-1/2)*(SecondWord.U b)^2) := by ring
          _ ≤ (3*ratioD b)*((b+1/2)*(joinSpeed x)^2) := hmul
          _ = (ratioDD b*(joinSpeed x)^2)*(SecondWord.U b)^2 := by
            linear_combination -(joinSpeed x)^2*hid
      have hnegative := mul_nonpos_of_nonpos_of_nonneg hP
        (sub_nonneg.mpr hcomp)
      nlinarith only [hnegative]
  have hinside : P r*ratioDD b*(joinSpeed x)^2+
      3*P r*ratioD b*(1/2-b)-slope r b<0 := by linarith
  exact mul_neg_of_pos_of_neg hs hinside

lemma initial_first (r : Row) (hr : r=1 ∨ r=2) : (17/250:ℝ)<first r 0 := by
  have hrat : ratio b0<(319/1000:ℝ) := by
    simpa [b0,ShortOuterZero.Opposite.low] using ShortOuterZero.Opposite.low_ratio
  have hratioPos := SameContact.ratio_pos (SameContact.outer_domain b0_mem)
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hcontact : joinContact 0=b0 := by norm_num [joinContact,b0]
  have hspeed : joinSpeed 0=outerDiagonal+1/2 := by norm_num [joinSpeed]
  rw [first,hcontact,hspeed]
  have hl : (1527/2000:ℝ)<slope r b0 := by
    rcases hr with rfl | rfl <;> norm_num [slope,t,P] <;> linarith
  have hp := mul_lt_mul_of_pos_left
    (show (1399/1000:ℝ)<outerDiagonal+1/2 by linarith) (show 0<slope r b0 by linarith)
  nlinarith

lemma initial_cost (r : Row) : cost r 0=aligned r b0 := by
  have hcontact : Negative.contact outerDiagonal 0=b0 := by
    norm_num [Negative.contact,SameContact.arc_diagonal,b0]
  dsimp [cost,Negative.cost]
  rw [hcontact,targetCost,SameContact.arc_diagonal]
  have hb : 1-b0=outerDiagonal := by dsimp [b0]; ring
  dsimp [aligned,source]
  rw [hb,SameContact.arc_diagonal]
  ring

lemma join_cost (r : Row) {e : ℝ} (he : Diagonal.IsEvent e) :
    cost r e=SourceDiagonal.cost r e := by
  have hc := SourceDiagonal.event_coordinates he
  dsimp [cost,Negative.cost,SourceDiagonal.cost]
  rw [diagonal_contact,he.2,target,targetCost,SameContact.arc_diagonal,hc.1,hc.2]
  ring

theorem cost_lower (r : Row) (hr : r=1 ∨ r=2) {e x : ℝ}
    (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) : (8981/10000:ℝ)<cost r x := by
  have hc : ConcaveOn ℝ (Icc 0 e) (first r) := concave_of_deriv2
    (fun y hy => first_hasDerivAt r he hy)
    (fun y hy => second_hasDerivAt r he hy)
    (fun y hy => (third_negative r he hy).le)
  have hm := RoleFour.minimum_of_concave_derivative
    (fun y hy => cost_hasDerivAt r he hy) hc (by linarith [initial_first r hr]) hx
  have hl : (8981/10000:ℝ)<cost r 0 := by
    rw [initial_cost]
    exact aligned_lower r ⟨b0_mem.1,le_rfl⟩
  have hu : (8981/10000:ℝ)<cost r e := by
    rw [join_cost r he]
    exact SourceDiagonal.cost_lower r hr he ⟨le_rfl,(Diagonal.event_angle he).2⟩
  exact (lt_min hl hu).trans_le hm

theorem original_contact (r : Row) (hr : r=1 ∨ r=2) {x : ℝ}
    (hd : Negative.Domain outerDiagonal x) : (8981/10000:ℝ)<Negative.cost r outerDiagonal x := by
  obtain ⟨e,he⟩ := Diagonal.exists_event
  have hbefore : x≤e := by
    by_contra! hbad
    have hh := Diagonal.joinContact_strictMono (Diagonal.event_angle he) hd.2.1 hbad
    rw [he.2,←diagonal_contact] at hh
    linarith [hd.2.2.2]
  exact cost_lower r hr he ⟨hd.2.1.1,hbefore⟩

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.TargetDiagonal
