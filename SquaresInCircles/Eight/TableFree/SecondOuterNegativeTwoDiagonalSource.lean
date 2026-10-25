module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoContactBoundary
public import SquaresInCircles.Eight.TableFree.SecondOuterFixedReference
public import SquaresInCircles.Eight.TableFree.SecondOuterMinimumCalculus

/-!
# The actual diagonal-source contact and its derivative shape

The global target-curvature bound `|T''|<1.335`, together with `T'''>1.6`,
already makes the contact cost's third derivative positive on its
entire physical arc.  No target-sign split or contact curvature rows
are required.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma T_second_abs {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    |TLabel.d2 b|<(267/200:ℝ) := by
  have hz := T_second_monotone outer_zero_mem hb hb.1
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hh := T_second_monotone hb hd hb.2
  have hzero : -(267/200:ℝ)<TLabel.d2 0 := by
    have hr := (outer_ratio_bounds outer_zero_mem).1
    norm_num [RoleLabel.d2,TLabel]
    linarith
  have hdiag : TLabel.d2 outerDiagonal<(267/200:ℝ) := by
    have hD := (outer_ratio_bounds hd).2.2
    have hp := mul_le_mul outer_endpoint_bounds.2.2.2.le hD.2.le hD.1.le (by norm_num)
    norm_num [RoleLabel.d2,TLabel,ratio_diagonal]
    nlinarith
  rw [abs_lt]
  constructor <;> linarith

namespace NegativeTwo.DiagonalSource

def height (x : ℝ) : ℝ := TargetContact.B outerDiagonal x
def speed (x : ℝ) : ℝ := TargetContact.v outerDiagonal x
def cost (x : ℝ) : ℝ := value outerDiagonal (height x) (Real.pi/2-x)
def first (x : ℝ) : ℝ := -1+TLabel.d1 (height x)*speed x
def second (x : ℝ) : ℝ :=
  TLabel.d2 (height x)*(speed x)^2-TLabel.d1 (height x)*(height x-1/2)
def third (x : ℝ) : ℝ := speed x*(TLabel.d3 (height x)*(speed x)^2-
  3*TLabel.d2 (height x)*(height x-1/2)-TLabel.d1 (height x))

def Domain (x : ℝ) : Prop := x∈Icc 0 (7/10) ∧ height x≤outerDiagonal

lemma diagonal_mem : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩

lemma height_zero : height 0=1-outerDiagonal := by
  rw [height,TargetContact.B_zero,ShortOuterOne.SameContact.arc_diagonal]

lemma height_monotone : MonotoneOn height (Icc 0 (7/10)) :=
  TargetContact.B_angle_monotone diagonal_mem

lemma height_hasDerivAt (x : ℝ) : HasDerivAt height (speed x) x :=
  TargetContact.B_angle_hasDerivAt outerDiagonal x

lemma speed_hasDerivAt (x : ℝ) : HasDerivAt speed (1/2-height x) x :=
  TargetContact.v_angle_hasDerivAt outerDiagonal x

lemma domain_data {x : ℝ} (hx : Domain x) :
    height x∈Icc 0 outerDiagonal ∧ 0<speed x ∧ |height x-1/2|<2/5 ∧
      (4889/2500:ℝ)<(speed x)^2 := by
  have hlo := height_monotone (by norm_num) hx.1 hx.1.1
  rw [height_zero] at hlo
  have hheight : height x∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.2],hx.2⟩
  have hv := TargetContact.v_positive diagonal_mem hx.1
  have hz : |height x-1/2|<2/5 := by
    rw [abs_lt]
    constructor <;> linarith [hlo,hx.2,outer_endpoint_bounds.2.2.2]
  have hn : (height x-1/2)^2+(speed x)^2=Q0-2*outerDiagonal := by
    have hh := TargetContact.norm_identity diagonal_mem x
    norm_num [U,ShortOuterOne.SameContact.arc_diagonal,Inverse.q] at hh
    dsimp [height,speed]
    linarith
  have hz2 : (height x-1/2)^2<(4/25:ℝ) := by
    nlinarith [(abs_lt.mp hz).1,(abs_lt.mp hz).2]
  refine ⟨hheight,hv,hz,?_⟩
  norm_num [Q0] at hn
  nlinarith [outer_endpoint_bounds.2.2.2]

lemma domain_before {x t : ℝ} (hx : Domain x) (ht : t∈Icc 0 x) : Domain t := by
  have htcap : t∈Icc 0 (7/10) := ⟨ht.1,ht.2.trans hx.1.2⟩
  exact ⟨htcap,(height_monotone htcap hx.1 ht.2).trans hx.2⟩

lemma cost_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt cost (first x) x := by
  have hT := (TLabel.outer_hasDerivAt (outer_domain (domain_data hx).1)).comp x
    (height_hasDerivAt x)
  have hd := (((hasDerivAt_id' x).const_sub (Real.pi/2)).sub_const
    (P outerDiagonal)).add hT
  exact hd.congr_deriv (by simp only [first])

lemma first_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt first (second x) x := by
  have hT := (TLabel.d1_hasDerivAt (outer_domain (domain_data hx).1)).comp x
    (height_hasDerivAt x)
  have hd := (hT.mul (speed_hasDerivAt x)).const_add (-1)
  exact hd.congr_deriv (by simp only [second,Function.comp_apply]; ring)

lemma second_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt second (third x) x := by
  have hT := (TLabel.d1_hasDerivAt (outer_domain (domain_data hx).1)).comp x
    (height_hasDerivAt x)
  have hTT := (TLabel.d2_hasDerivAt (outer_domain (domain_data hx).1)).comp x
    (height_hasDerivAt x)
  have hs2 : HasDerivAt (fun y => (speed y)^2) (2*speed x*(1/2-height x)) x :=
    ((speed_hasDerivAt x).pow 2).congr_deriv (by norm_num)
  have hd := (hTT.mul hs2).sub (hT.mul ((height_hasDerivAt x).sub_const (1/2)))
  exact hd.congr_deriv (by simp only [third,Function.comp_apply]; ring)

lemma third_positive {x : ℝ} (hx : Domain x) : 0<third x := by
  have hd := domain_data hx
  have hT3 := T_third_lower hd.1
  have hT2 := T_second_abs hd.1
  have hT1 := T_first_upper hd.1
  have hprod := mul_le_mul_of_nonneg_left hd.2.2.2.le
    (show 0≤TLabel.d3 (height x) by linarith)
  have hprod' := mul_lt_mul_of_pos_right hT3 (by norm_num : (0:ℝ)<4889/2500)
  have habs : |TLabel.d2 (height x)*(height x-1/2)|<(267/500:ℝ) := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left hd.2.2.1.le (abs_nonneg (TLabel.d2 (height x)))
    nlinarith
  have hcharge := (le_abs_self (TLabel.d2 (height x)*(height x-1/2))).trans_lt habs
  have hinside : 0<TLabel.d3 (height x)*(speed x)^2-
      3*TLabel.d2 (height x)*(height x-1/2)-TLabel.d1 (height x) := by
    nlinarith
  exact mul_pos hd.2.1 hinside

lemma second_monotone {x : ℝ} (hx : Domain x) : MonotoneOn second (Icc 0 x) :=
  monoOn_of_hasDeriv_nonneg
    (fun t ht => (second_hasDerivAt (domain_before hx ht)).continuousAt.continuousWithinAt)
    (fun t ht => second_hasDerivAt (domain_before hx (Ioo_subset_Icc_self ht)))
    (fun t ht => (third_positive (domain_before hx (Ioo_subset_Icc_self ht))).le)

end NegativeTwo.DiagonalSource
end SquaresInCircles.Eight.TableFree.SecondWord
