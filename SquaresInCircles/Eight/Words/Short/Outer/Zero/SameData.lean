module

public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroContact

/-!
# Eight squares: the four favorable same-sign zero contacts of the short word

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
    (fun b hb => (l_hasDerivAt r hb).continuousAt.continuousWithinAt)
    (fun b hb => l_hasDerivAt r (Ioo_subset_Icc_self hb))
    (fun b hb => alpha_nonneg r hr (Ioo_subset_Icc_self hb))

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
        (P r))).sub_const (t r)) using 1 <;> dsimp [targetFirst,targetSecond] <;> ring

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
