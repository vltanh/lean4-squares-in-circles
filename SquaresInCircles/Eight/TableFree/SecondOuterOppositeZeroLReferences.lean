module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroReferences

/-!
# The named L references in the symmetric whole-angle proof

Uncompiled source draft.  Each declaration below is one of the exact
rational comparisons displayed in Section 2 or Section 6.  The actual
circle radical is carried by the proved reference enclosure.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open Reference

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

lemma L_four_second : LLabel.d2 (2/5)<(0:ℝ) :=
  second_upper (by norm_num) (by opposite_reference_arithmetic)

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
  norm_num [RoleLabel.outer,RoleLabel.eval,LLabel,charge]
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
  refine ⟨by linarith,by linarith,abs_lt.mpr ⟨?_,?_⟩⟩ <;> linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Symmetric

