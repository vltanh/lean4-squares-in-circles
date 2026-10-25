module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroReferences

/-!
# Eight squares: the L references of the symmetric whole-angle proof

Each declaration below is one exact rational comparison for the label L or its derivatives at a
fixed reference point. The circle radical is carried by the reference enclosures
(`Reference.valueAt`, `Reference.firstAt`, `Reference.secondAt`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open Reference
open StationaryPrimitives (Interval)

private lemma r82_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r82_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r82_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl
private lemma r82_mp_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).hi = S.hi := by subst e; rfl

private lemma r82_rootAt_lo {b : ℝ} (hb : b∈Icc 0 (9/10)) : (rootAt b hb).lo =
    (OppositeThree.ReferenceAlgebra.rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2)
      (by linarith [hb.2]) (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).lo := by
  unfold rootAt
  rw [r82_mpr_lo, r82_mp_lo]
  all_goals simp [U,ShortOuterOne.SameContact.arc]
private lemma r82_rootAt_hi {b : ℝ} (hb : b∈Icc 0 (9/10)) : (rootAt b hb).hi =
    (OppositeThree.ReferenceAlgebra.rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2)
      (by linarith [hb.2]) (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).hi := by
  unfold rootAt
  rw [r82_mpr_hi, r82_mp_hi]
  all_goals simp [U,ShortOuterOne.SameContact.arc]

private lemma r82_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r82_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (OppositeThree.ReferenceAlgebra.coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r82_mpr_lo r82_coordinate_eq (congrArg _ r82_coordinate_eq) _
private lemma r82_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (OppositeThree.ReferenceAlgebra.coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r82_mpr_hi r82_coordinate_eq (congrArg _ r82_coordinate_eq) _
private lemma r82_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(ShortOuterOne.SameContact.arc y)+H.q*y+H.r*y^2+
      H.s*(ShortOuterOne.SameContact.arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r82_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (OppositeThree.ReferenceAlgebra.labelBox H Y X).lo =
      (((((Interval.point H.c).add ((Interval.point H.p).mul
        (OppositeThree.ReferenceAlgebra.coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((OppositeThree.ReferenceAlgebra.coordinate X).mul Y))).lo :=
  r82_mpr_lo (r82_label_eq H) (congrArg _ (r82_label_eq H)) _

private lemma r82_valueAt_lo (H : RoleLabel) (b : ℝ) (hb : b∈Icc 0 (9/10)) :
    (valueAt H b hb).lo =
      (((((Interval.point H.c).add ((Interval.point H.p).mul
        (OppositeThree.ReferenceAlgebra.coordinate (rootAt b hb)))).add
      ((Interval.point H.q).mul (Interval.point b))).add
        ((Interval.point H.r).mul (Interval.point b).square)).add
        ((Interval.point H.s).mul ((OppositeThree.ReferenceAlgebra.coordinate (rootAt b hb)).mul
          (Interval.point b)))).lo :=
  r82_labelBox_lo H _ _

attribute [local simp ↓] r82_rootAt_lo r82_rootAt_hi r82_coordinate_lo r82_coordinate_hi
  r82_valueAt_lo

private lemma first_lower {b l : ℝ} (hb : b∈Icc 0 (9/10))
    (h : l<(firstAt LLabel b hb).lo) : l<LLabel.d1 b :=
  h.trans_le (firstAt LLabel b hb).mem.1
private lemma first_upper {b u : ℝ} (hb : b∈Icc 0 (9/10))
    (h : (firstAt LLabel b hb).hi<u) : LLabel.d1 b<u :=
  (firstAt LLabel b hb).mem.2.trans_lt h
private lemma second_lower {b l : ℝ} (hb : b∈Icc 0 (9/10))
    (h : l<(secondAt LLabel b hb).lo) : l<LLabel.d2 b :=
  h.trans_le (secondAt LLabel b hb).mem.1
private lemma second_upper {b u : ℝ} (hb : b∈Icc 0 (9/10))
    (h : (secondAt LLabel b hb).hi<u) : LLabel.d2 b<u :=
  (secondAt LLabel b hb).mem.2.trans_lt h

lemma L_tenth_first : LLabel.d1 (1/10)<(51/50:ℝ) :=
  first_upper (by norm_num) (by opposite_reference_arithmetic)

lemma L_85_first : LLabel.d1 (17/20)<(51/50:ℝ) :=
  first_upper (by norm_num) (by opposite_reference_arithmetic)

lemma L_fifth_first : LLabel.d1 (1/5)<(17/20:ℝ) :=
  first_upper (by norm_num) (by opposite_reference_arithmetic)

lemma L_76_first : LLabel.d1 (19/25)<(17/20:ℝ) :=
  first_upper (by norm_num) (by opposite_reference_arithmetic)

lemma L_four_first : (649/1000:ℝ)<LLabel.d1 (2/5) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_six_first : (649/1000:ℝ)<LLabel.d1 (3/5) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_six_first_upper : LLabel.d1 (3/5)<(7/10:ℝ) :=
  first_upper (by norm_num) (by opposite_reference_arithmetic)

lemma L_six_second : (1/2:ℝ)<LLabel.d2 (3/5) :=
  second_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_56_first : (15817/25000:ℝ)<LLabel.d1 (14/25) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_56_second : (29/100:ℝ)<LLabel.d2 (14/25) :=
  second_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_66_first : (6933/10000:ℝ)<LLabel.d1 (33/50) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_66_second : (93/100:ℝ)<LLabel.d2 (33/50) :=
  second_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_67_first : (703/1000:ℝ)<LLabel.d1 (67/100) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_seven_first : (1473/2000:ℝ)<LLabel.d1 (7/10) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_seven_second : (6/5:ℝ)<LLabel.d2 (7/10) :=
  second_lower (by norm_num) (by opposite_reference_arithmetic)

def charge : ℝ := 400/391

lemma L_small_chord_reference :
    LLabel.outer 0+charge*(3/20)<LLabel.outer (3/20) := by
  have h := (valueAt LLabel (3/20) (by norm_num)).mem.1
  have hr : (793/20000:ℝ)+(400/391)*(3/20)<
      (valueAt LLabel (3/20) (by norm_num)).lo := by opposite_reference_arithmetic
  have h0 : LLabel.outer 0=793/20000 := by norm_num [RoleLabel.outer,RoleLabel.eval,LLabel]
  rw [h0]
  dsimp only [charge]
  linarith

lemma support_references :
    -(15957/100000:ℝ)<LLabel.outer (3/5)-charge*(3/5) ∧
    -(7977/50000:ℝ)<LLabel.outer (17/20)-charge*(17/20) ∧
    |LLabel.d1 (17/20)-charge|<(1/200:ℝ) := by
  have h1 := (valueAt LLabel (3/5) (by norm_num)).mem.1
  have h2 := (valueAt LLabel (17/20) (by norm_num)).mem.1
  have h3 := (firstAt LLabel (17/20) (by norm_num)).mem
  have r1 : -(15957/100000:ℝ)+(400/391)*(3/5)<
      (valueAt LLabel (3/5) (by norm_num)).lo := by opposite_reference_arithmetic
  have r2 : -(7977/50000:ℝ)+(400/391)*(17/20)<
      (valueAt LLabel (17/20) (by norm_num)).lo := by opposite_reference_arithmetic
  have r3 : (400/391)-(1/200:ℝ)<(firstAt LLabel (17/20) (by norm_num)).lo := by opposite_reference_arithmetic
  have r4 : (firstAt LLabel (17/20) (by norm_num)).hi<(400/391)+(1/200:ℝ) := by opposite_reference_arithmetic
  dsimp [charge]
  refine ⟨by linarith,by linarith,abs_lt.mpr ⟨?_,?_⟩⟩ <;> linarith [h3.1,h3.2]

end SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric

