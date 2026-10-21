module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroCycle
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoPrimaryDiagonal
public import SquaresInCircles.Eight.TableFree.SecondOuterMinimumCalculus

/-!
# Original opposite-sign outer zero-quarter contacts

Uncompiled source draft.  These are equations (11) and (23) in the
asymmetric hand proof, shared with equations (9) and (13) of the
symmetric hand proof.  Both angle halves and both label orders retain
the actual outer circle and its original weak separator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def plus (B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x-(arc B-1/2)*Real.sin x
def plusSpeed (B x : ℝ) : ℝ :=
  (arc B-1/2)*Real.cos x-(B-1/2)*Real.sin x
def plusK (B x : ℝ) : ℝ := Real.cos x-ratio B*Real.sin x
def minus (B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x+(arc B+1/2)*Real.sin x
def minusSpeed (B x : ℝ) : ℝ :=
  (arc B+1/2)*Real.cos x+(B-1/2)*Real.sin x
def minusK (B x : ℝ) : ℝ := Real.cos x+ratio B*Real.sin x
def PlusDomain (B x : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ plus B x∈Icc 0 outerDiagonal
def MinusDomain (B x : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ minus B x∈Icc 0 outerDiagonal
def plusCost (F G : RoleLabel) (B x : ℝ) : ℝ := x+F.outer (plus B x)+G.outer B
def minusCost (F G : RoleLabel) (B x : ℝ) : ℝ := -x+F.outer (minus B x)+G.outer B
def plusFirst (F : RoleLabel) (B x : ℝ) : ℝ := 1-F.d1 (plus B x)*plusSpeed B x
def minusFirst (F : RoleLabel) (B x : ℝ) : ℝ := -1+F.d1 (minus B x)*minusSpeed B x
def minusSecond (F : RoleLabel) (B x : ℝ) : ℝ :=
  F.d2 (minus B x)*(minusSpeed B x)^2-F.d1 (minus B x)*(minus B x-1/2)
def minusTarget (F G : RoleLabel) (B x : ℝ) : ℝ :=
  G.d1 B-F.d1 (minus B x)*minusK B x

lemma plus_hasDerivAt (B x : ℝ) : HasDerivAt (plus B) (-plusSpeed B x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).sub
    ((Real.hasDerivAt_sin x).const_mul (arc B-1/2))) using 1 <;> dsimp [plus,plusSpeed] <;> ring
lemma plusSpeed_hasDerivAt (B x : ℝ) :
    HasDerivAt (plusSpeed B) (plus B x-1/2) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (arc B-1/2)).sub
    ((Real.hasDerivAt_sin x).const_mul (B-1/2)) using 1 <;> dsimp [plus,plusSpeed] <;> ring
lemma minus_hasDerivAt (B x : ℝ) : HasDerivAt (minus B) (minusSpeed B x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (arc B+1/2))) using 1 <;> dsimp [minus,minusSpeed] <;> ring
lemma minusSpeed_hasDerivAt (B x : ℝ) :
    HasDerivAt (minusSpeed B) (-(minus B x-1/2)) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (arc B+1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (B-1/2)) using 1 <;> dsimp [minus,minusSpeed] <;> ring
lemma plus_target_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun t => plus t x) (-plusK B x) B := by
  convert (((((hasDerivAt_id B).const_sub (1/2)).mul_const (Real.cos x)).const_add (1/2)).sub
    (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).sub_const (1/2)).mul_const
      (Real.sin x))) using 1 <;> dsimp [plus,plusK] <;> ring
lemma minus_target_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun t => minus t x) (-minusK B x) B := by
  convert (((((hasDerivAt_id B).const_sub (1/2)).mul_const (Real.cos x)).const_add (1/2)).add
    (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const (1/2)).mul_const
      (Real.sin x))) using 1 <;> dsimp [minus,minusK] <;> ring

lemma positive_data {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    0<plusSpeed B x ∧ 0<minusSpeed B x ∧ 0<plusK B x ∧ 0<minusK B x := by
  have ht := positive_trig hx
  have hc : 0<Real.cos x-Real.sin x := by linarith [ht.1,ht.2.2.2.1]
  have hs := ShortOuterOne.SameContact.arc_state hB
  have ha : 0<arc B-1/2 := by linarith [(outer_bounds hs).1,fine_outer_endpoint_bounds.2]
  have hp := mul_pos ha hc
  have hq := mul_nonneg (show 0≤arc B-B from sub_nonneg.mpr hs.2.1) ht.2.2.1
  have hm := mul_pos (show 0<arc B+1/2 by linarith) hc
  have hn := mul_nonneg (show 0≤arc B+B by linarith [hB.1]) ht.2.2.1
  have hr := outer_ratio_bounds hB
  have hks := mul_le_mul_of_nonneg_right hr.2.1 ht.2.2.1
  have hms := mul_nonneg (by linarith [hr.1] : 0≤ratio B) ht.2.2.1
  dsimp [plusSpeed,minusSpeed,plusK,minusK]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

lemma plus_angle_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (plus B) (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos (fun x _ => (plus_hasDerivAt B x).continuousAt.continuousWithinAt)
    (fun x _ => plus_hasDerivAt B x)
    (fun x hx => neg_nonpos.mpr (positive_data hB (Ioo_subset_Icc_self hx)).1.le)
lemma minus_angle_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (minus B) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg (fun x _ => (minus_hasDerivAt B x).continuousAt.continuousWithinAt)
    (fun x _ => minus_hasDerivAt B x)
    (fun x hx => (positive_data hB (Ioo_subset_Icc_self hx)).2.1.le)
lemma plus_target_antitone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    AntitoneOn (fun B => plus B x) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (plus_target_hasDerivAt hB x).continuousAt.continuousWithinAt)
    (fun B hB => plus_target_hasDerivAt (Ioo_subset_Icc_self hB) x)
    (fun B hB => neg_nonpos.mpr (positive_data (Ioo_subset_Icc_self hB) hx).2.2.1.le)
lemma minus_target_antitone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    AntitoneOn (fun B => minus B x) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (minus_target_hasDerivAt hB x).continuousAt.continuousWithinAt)
    (fun B hB => minus_target_hasDerivAt (Ioo_subset_Icc_self hB) x)
    (fun B hB => neg_nonpos.mpr (positive_data (Ioo_subset_Icc_self hB) hx).2.2.2.le)

lemma plus_norm {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    (plus B x-1/2)^2+(plusSpeed B x)^2=Q0-2*(arc B+B) := by
  have hcircle := UW_circle (outer_domain hB)
  dsimp [plus,plusSpeed,U,W] at *
  linear_combination hcircle+((arc B-1/2)^2+(B-1/2)^2)*(Real.sin_sq_add_cos_sq x)
lemma minus_norm {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    (minus B x-1/2)^2+(minusSpeed B x)^2=Q0-2*B := by
  have hcircle := UW_circle (outer_domain hB)
  dsimp [minus,minusSpeed,U,W] at *
  linear_combination hcircle+((arc B+1/2)^2+(B-1/2)^2)*(Real.sin_sq_add_cos_sq x)

lemma minus_aligned_le {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    1-B≤minus B x := by
  have hh := minus_angle_monotone hB (by norm_num) hx hx.1
  simpa [minus] using hh
lemma minus_target_lower {B x : ℝ} (hd : MinusDomain B x) : 1-outerDiagonal≤B := by
  linarith [minus_aligned_le hd.1 hd.2.1,hd.2.2.2]
lemma minus_z_bound {B x : ℝ} (hd : MinusDomain B x) :
    -(2/5:ℝ)<minus B x-1/2 ∧ minus B x-1/2<2/5 := by
  have hh := minus_aligned_le hd.1 hd.2.1
  constructor <;> linarith [hd.1.2,hd.2.2.2,outer_endpoint_bounds.2.2.2]

lemma plusCost_hasDerivAt (F G : RoleLabel) {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (plusCost F G B) (plusFirst F B x) x := by
  convert (((hasDerivAt_id x).add ((F.outer_hasDerivAt (outer_domain hd.2.2)).comp x
    (plus_hasDerivAt B x))).add_const (G.outer B)) using 1 <;> dsimp [plusCost,plusFirst] <;> ring
lemma minusCost_hasDerivAt (F G : RoleLabel) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (minusCost F G B) (minusFirst F B x) x := by
  convert ((((hasDerivAt_id x).neg).add ((F.outer_hasDerivAt (outer_domain hd.2.2)).comp x
    (minus_hasDerivAt B x))).add_const (G.outer B)) using 1 <;> dsimp [minusCost,minusFirst] <;> ring
lemma minusFirst_hasDerivAt (F : RoleLabel) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (minusFirst F B) (minusSecond F B x) x := by
  convert ((((F.d1_hasDerivAt (outer_domain hd.2.2)).comp x (minus_hasDerivAt B x)).mul
    (minusSpeed_hasDerivAt B x)).const_add (-1)) using 1 <;>
      dsimp [minusFirst,minusSecond] <;> ring
lemma minusCost_target_hasDerivAt (F G : RoleLabel) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (fun t => minusCost F G t x) (minusTarget F G B x) B := by
  convert ((((F.outer_hasDerivAt (outer_domain hd.2.2)).comp B
    (minus_target_hasDerivAt hd.1 x)).const_add (-x)).add
      (G.outer_hasDerivAt (outer_domain hd.1))) using 1 <;> dsimp [minusCost,minusTarget] <;> ring

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero
