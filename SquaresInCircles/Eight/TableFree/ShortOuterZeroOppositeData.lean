module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroData
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroAlignedPJ
public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameCycle

/-!
# The six opposite-sign outer zero contacts of the short word

Uncompiled transcription of equations (1)--(2) of
`HAND_SHORT_WORD_OUTER_ZERO_OPPOSITE_WITHOUT_TABLES.md`.
Both angle signs use the literal original source-secondary contact;
reversal restores the original target-secondary owner afterward.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open SecondWord (RoleLabel U W outer_domain outer_zero_mem)

abbrev Row := Fin 6

def c : Row→ℝ := ![-24463/100000,-24463/100000,8753/100000,8753/100000,-45320/100000,-45320/100000]
def p : Row→ℝ := ![0,13422/100000,0,-9133/100000,51554/100000,-19335/100000]
def q : Row→ℝ := ![94766/100000,103828/100000,9994/10000,88074/100000,119909/100000,76744/100000]
def v : Row→ℝ := ![13422/100000,0,-9133/100000,0,-19335/100000,51554/100000]
def t : Row→ℝ := ![103828/100000,94766/100000,88074/100000,9994/10000,76744/100000,119909/100000]

def source (r : Row) : RoleLabel := ⟨0,p r,q r,0,0⟩
def target (r : Row) : RoleLabel := ⟨0,v r,t r,0,0⟩
def l (r : Row) (b : ℝ) : ℝ := q r-p r*ratio b
def h (r : Row) (B : ℝ) : ℝ := t r-v r*ratio B

abbrev plus := SecondWord.OppositeZero.plus
abbrev plusSpeed := SecondWord.OppositeZero.plusSpeed
abbrev plusK := SecondWord.OppositeZero.plusK
abbrev minus := SecondWord.OppositeZero.minus
abbrev minusSpeed := SecondWord.OppositeZero.minusSpeed
abbrev minusK := SecondWord.OppositeZero.minusK
abbrev PlusDomain := SecondWord.OppositeZero.PlusDomain
abbrev MinusDomain := SecondWord.OppositeZero.MinusDomain

def plusCost (r : Row) (B x : ℝ) : ℝ :=
  x+c r+(source r).outer (plus B x)+(target r).outer B
def minusCost (r : Row) (B x : ℝ) : ℝ :=
  -x+c r+(source r).outer (minus B x)+(target r).outer B
def plusAngle (r : Row) (B x : ℝ) : ℝ := 1-l r (plus B x)*plusSpeed B x
def minusAngle (r : Row) (B x : ℝ) : ℝ := -1+l r (minus B x)*minusSpeed B x
def plusTarget (r : Row) (B x : ℝ) : ℝ := h r B-l r (plus B x)*plusK B x
def minusTarget (r : Row) (B x : ℝ) : ℝ := h r B-l r (minus B x)*minusK B x

def plusTargetCurvature (r : Row) (B x : ℝ) : ℝ :=
  -p r*ratioD (plus B x)*(plusK B x)^2+(l r (plus B x)*Real.sin x-v r)*ratioD B
def minusTargetCurvature (r : Row) (B x : ℝ) : ℝ :=
  -p r*ratioD (minus B x)*(minusK B x)^2-(l r (minus B x)*Real.sin x+v r)*ratioD B

def aligned (r : Row) (b : ℝ) : ℝ := c r+(source r).outer b+(target r).outer (1-b)
def alignedFirst (r : Row) (b : ℝ) : ℝ := l r b-h r (1-b)
def alignedSecond (r : Row) (b : ℝ) : ℝ := -p r*ratioD b-v r*ratioD (1-b)
abbrev low : ℝ := 1-outerDiagonal

lemma derivative_source (r : Row) (b : ℝ) : (source r).d1 b=l r b := by
  simp [source,RoleLabel.d1,l]
lemma derivative_target (r : Row) (B : ℝ) : (target r).d1 B=h r B := by
  simp [target,RoleLabel.d1,h]

lemma slope_bounds (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (68355/100000:ℝ)≤l r b ∧ l r b≤6/5 ∧ 0<h r b := by
  have hh := SecondWord.outer_ratio_bounds hb
  fin_cases r <;> norm_num [l,h,p,q,v,t] <;>
    repeat' constructor <;> linarith [hh.1,hh.2.1]

lemma source_monotone (r : Row) : MonotoneOn (source r).outer (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => ((source r).outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => (source r).outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by rw [derivative_source]; linarith [(slope_bounds r (Ioo_subset_Icc_self hb)).1])
lemma target_monotone (r : Row) : MonotoneOn (target r).outer (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => ((target r).outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => (target r).outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by rw [derivative_target]; exact (slope_bounds r (Ioo_subset_Icc_self hb)).2.2.le)

lemma l_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (l r) (-p r*ratioD b) b := by
  convert ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul
    (p r)).const_sub (q r) using 1 <;> dsimp [l] <;> ring
lemma h_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (h r) (-v r*ratioD b) b := by
  convert ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul
    (v r)).const_sub (t r) using 1 <;> dsimp [h] <;> ring

lemma plusCost_angle_hasDerivAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (plusCost r B) (plusAngle r B x) x := by
  have hh := (SecondWord.OppositeZero.plusCost_hasDerivAt (source r) (target r) hd).add_const (c r)
  convert hh using 1 <;> dsimp [plusCost,plusAngle,SecondWord.OppositeZero.plusCost,
    SecondWord.OppositeZero.plusFirst] <;> rw [derivative_source] <;> ring

lemma minusCost_angle_hasDerivAt (r : Row) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (minusCost r B) (minusAngle r B x) x := by
  have hh := (SecondWord.OppositeZero.minusCost_hasDerivAt (source r) (target r) hd).add_const (c r)
  convert hh using 1 <;> dsimp [minusCost,minusAngle,SecondWord.OppositeZero.minusCost,
    SecondWord.OppositeZero.minusFirst] <;> rw [derivative_source] <;> ring

lemma plusCost_target_hasDerivAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (fun B => plusCost r B x) (plusTarget r B x) B := by
  convert (((source r).outer_hasDerivAt (outer_domain hd.2.2)).comp B
    (SecondWord.OppositeZero.plus_target_hasDerivAt hd.1 x)).add
      ((target r).outer_hasDerivAt (outer_domain hd.1)) |>.const_add (x+c r) using 1 <;>
    dsimp [plusCost,plusTarget] <;> rw [derivative_source,derivative_target] <;> ring

lemma minusCost_target_hasDerivAt (r : Row) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (fun B => minusCost r B x) (minusTarget r B x) B := by
  convert (((source r).outer_hasDerivAt (outer_domain hd.2.2)).comp B
    (SecondWord.OppositeZero.minus_target_hasDerivAt hd.1 x)).add
      ((target r).outer_hasDerivAt (outer_domain hd.1)) |>.const_add (-x+c r) using 1 <;>
    dsimp [minusCost,minusTarget] <;> rw [derivative_source,derivative_target] <;> ring

lemma plusTarget_hasDerivAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (fun B => plusTarget r B x) (plusTargetCurvature r B x) B := by
  have hK : HasDerivAt (fun B => plusK B x) (-ratioD B*Real.sin x) B := by
    convert ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).mul_const
      (Real.sin x)).const_sub (Real.cos x) using 1 <;> dsimp [plusK,SecondWord.OppositeZero.plusK] <;> ring
  convert (h_hasDerivAt r hd.1).sub (((l_hasDerivAt r hd.2.2).comp B
    (SecondWord.OppositeZero.plus_target_hasDerivAt hd.1 x)).mul hK) using 1 <;>
    dsimp [plusTarget,plusTargetCurvature] <;> ring

lemma minusTarget_hasDerivAt (r : Row) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (fun B => minusTarget r B x) (minusTargetCurvature r B x) B := by
  have hK : HasDerivAt (fun B => minusK B x) (ratioD B*Real.sin x) B :=
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).mul_const
      (Real.sin x)).const_add (Real.cos x)
  convert (h_hasDerivAt r hd.1).sub (((l_hasDerivAt r hd.2.2).comp B
    (SecondWord.OppositeZero.minus_target_hasDerivAt hd.1 x)).mul hK) using 1 <;>
    dsimp [minusTarget,minusTargetCurvature] <;> ring

lemma aligned_domains {b : ℝ} (hb : b∈Icc low outerDiagonal) :
    b∈Icc 0 outerDiagonal ∧ 1-b∈Icc 0 outerDiagonal := by
  dsimp [low] at hb
  refine ⟨⟨?_,hb.2⟩,⟨?_,?_⟩⟩ <;>
    linarith [hb.1,hb.2,outer_endpoint_bounds.2.2.1,outer_endpoint_bounds.2.2.2]

lemma aligned_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc low outerDiagonal) :
    HasDerivAt (aligned r) (alignedFirst r b) b := by
  convert ((((source r).outer_hasDerivAt (outer_domain (aligned_domains hb).1)).const_add
    (c r)).add (((target r).outer_hasDerivAt (outer_domain (aligned_domains hb).2)).comp b
      ((hasDerivAt_id b).const_sub 1))) using 1 <;>
    dsimp [aligned,alignedFirst] <;> rw [derivative_source,derivative_target] <;> ring

lemma alignedFirst_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc low outerDiagonal) :
    HasDerivAt (alignedFirst r) (alignedSecond r b) b := by
  convert (l_hasDerivAt r (aligned_domains hb).1).sub
    ((h_hasDerivAt r (aligned_domains hb).2).comp b ((hasDerivAt_id b).const_sub 1)) using 1 <;>
    dsimp [alignedFirst,alignedSecond] <;> ring

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite
