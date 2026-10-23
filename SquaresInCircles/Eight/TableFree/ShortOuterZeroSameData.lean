module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroContact
public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJDiagonalGeometry
public import SquaresInCircles.Eight.TableFree.ShortOuterZeroUnfavorable

/-!
# The four favorable same-sign zero contacts of the short word

Uncompiled transcription of Sections 1 and 3 of
`HAND_SHORT_WORD_OUTER_ZERO_SAME_WITHOUT_TABLES.md`.
The four literal tuples retain their original source and target labels.
The contact coordinate is exactly the existing same-sign contact, so its
circle and projection identities are shared without changing its domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Same
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
  fin_cases r <;> norm_num [Coupled,p,P] at hr ⊢

lemma source_derivative (r : Row) (b : ℝ) : (source r).d1 b=l r b := by
  simp [source,RoleLabel.d1,l]
lemma source_second (r : Row) (b : ℝ) : (source r).d2 b=alpha r b := by
  simp [source,RoleLabel.d2,alpha]
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
  convert ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul
    (p r)).const_sub (q r) using 1 <;> dsimp [l,alpha] <;> ring
lemma alpha_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (alpha r) (-p r*ratioDD b) b :=
  (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).const_mul (-p r)

lemma l_monotone (r : Row) (hr : Coupled r) :
    MonotoneOn (l r) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (l_hasDerivAt r hb).continuousAt.continuousWithinAt)
    (fun b hb => l_hasDerivAt r (Ioo_subset_Icc_self hb))
    (fun b hb => alpha_nonneg r hr (Ioo_subset_Icc_self hb))

lemma cost_angle_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (cost r B) (angleFirst r B x) x := by
  have hh := SecondWord.SameZero.value_angle_hasDerivAt (source r) (target r) hd
  simpa only [←cost_value,SecondWord.SameZero.angleFirst,source_derivative] using hh

lemma angleFirst_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (angleFirst r B) (angleSecond r B x) x := by
  convert ((((l_hasDerivAt r hd.2.2).comp x (SecondWord.SameZero.b_angle_hasDerivAt B x)).mul
    (SecondWord.SameZero.v_angle_hasDerivAt B x)).const_sub 1) using 1 <;>
    dsimp [angleFirst,angleSecond] <;> ring

lemma cost_target_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (fun B => cost r B x) (targetFirst r B x) B := by
  have hh := SecondWord.SameZero.value_target_hasDerivAt (source r) (target r) hd
  simpa only [←cost_value,SecondWord.SameZero.targetFirst,source_derivative,
    target_derivative,sub_sub] using hh

lemma targetFirst_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (fun B => targetFirst r B x) (targetSecond r B x) B := by
  have hk : HasDerivAt (fun B => projection B x) (ratioD B*Real.sin x) B :=
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).mul_const
      (Real.sin x)).const_add (Real.cos x)
  convert (((((l_hasDerivAt r hd.2.2).comp B
    (SecondWord.SameZero.b_target_hasDerivAt hd.1 x)).mul hk).add
      ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).const_mul
        (P r))).sub_const (t r)) using 1 <;> dsimp [targetFirst,targetSecond] <;> ring

lemma angle_positive {B x : ℝ} (hd : Domain B x) : 0<x := by
  by_contra! hx
  have hz : x=0 := le_antisymm hx hd.2.1.1
  have hb := hd.2.2.2
  rw [hz] at hb
  norm_num [contact,SecondWord.SameZero.b] at hb
  linarith [hd.1.1,outer_endpoint_bounds.2.2.2]

lemma target_curvature_positive (r : Row) (hr : Coupled r) {B x : ℝ}
    (hd : Domain B x) : 0<targetSecond r B x := by
  have hpos := angle_positive hd
  have hsin : 0<Real.sin x := Real.sin_pos_of_pos_of_lt_pi hpos
    (by linarith [hd.2.1.2,Real.pi_gt_three])
  have hfirst := mul_nonneg (alpha_nonneg r hr hd.2.2) (sq_nonneg (projection B x))
  have hprod := mul_pos (l_positive r hd.2.2) hsin
  have hlast := mul_pos
    (show 0<l r (contact B x)*Real.sin x+P r by linarith [(coefficient_signs r).2.2])
    (ShortOuterOne.SameContact.ratioD_pos (outer_domain hd.1))
  dsimp [targetSecond]
  linarith

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

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Same
