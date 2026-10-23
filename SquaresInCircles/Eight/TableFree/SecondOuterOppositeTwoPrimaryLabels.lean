module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoSourceRatio

/-!
# The source label in the original primary coordinate

The primary label is the exact circle transform of the source label.
Its increasing curvature and derivative are proved on the complete
physical primary interval, with one rational reference at height one.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma primary_diagonal_mem : outerDiagonal∈Icc outerDiagonal outerAxial :=
  ⟨le_rfl,ShortOuterOne.SameContact.diagonal_le_axial⟩

lemma M_third_positive {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<PPrimaryLabel.d3 a := by
  have hu := U_positive (primary_domain ha)
  have he := PPrimaryLabel.third_numerator (primary_domain ha)
  have hW : (1399/1000:ℝ)<W a := by dsimp [W]; linarith [ha.1,fine_outer_endpoint_bounds.2]
  norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,Q0] at he
  have hp := pow_pos hu 5
  nlinarith

lemma M_second_monotone :
    MonotoneOn PPrimaryLabel.d2 (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (PPrimaryLabel.d2_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun a ha => PPrimaryLabel.d2_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun a ha => (M_third_positive (Ioo_subset_Icc_self ha)).le)

lemma primary_diagonal_ratioD : (71/50:ℝ)<ratioD outerDiagonal := by
  have hu := U_positive (primary_domain primary_diagonal_mem)
  have hU : U outerDiagonal<7/5 := by
    rw [U,ShortOuterOne.SameContact.arc_diagonal]
    linarith [outer_endpoint_bounds.2.2.2]
  have hc := pow_le_pow_left₀ hu.le hU.le 3
  change (71/50:ℝ)<Q0/(U outerDiagonal)^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0]
  nlinarith

lemma M_second_diagonal : (9/10:ℝ)<PPrimaryLabel.d2 outerDiagonal := by
  have hc : (807/1000:ℝ)<22663/25000-(2211/20000)*outerDiagonal := by
    linarith [outer_endpoint_bounds.2.2.2]
  have hm := mul_lt_mul hc primary_diagonal_ratioD (by norm_num)
    (by linarith : 0<22663/25000-(2211/20000)*outerDiagonal)
  norm_num [RoleLabel.d2,PPrimaryLabel,RoleLabel.primary,PLabel,ratio_diagonal]
  nlinarith

lemma M_second_positive {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<PPrimaryLabel.d2 a := by
  have hh := M_second_monotone primary_diagonal_mem ha ha.1
  linarith [M_second_diagonal]

lemma M_first_monotone : MonotoneOn PPrimaryLabel.d1 (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (PPrimaryLabel.d1_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun a ha => PPrimaryLabel.d1_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun a ha => (M_second_positive (Ioo_subset_Icc_self ha)).le)

lemma M_first_diagonal : (243/250:ℝ)<PPrimaryLabel.d1 outerDiagonal := by
  norm_num [RoleLabel.d1,PPrimaryLabel,RoleLabel.primary,PLabel,ratio_diagonal,
    ShortOuterOne.SameContact.arc_diagonal]
  linarith [fine_outer_endpoint_bounds.2]

lemma M_first_lower {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (243/250:ℝ)<PPrimaryLabel.d1 a :=
  M_first_diagonal.trans_le (M_first_monotone primary_diagonal_mem ha ha.1)

lemma M_one_first : (1083/1000:ℝ)<PPrimaryLabel.d1 1 ∧
    PPrimaryLabel.d1 1<271/250 := by
  exact PPrimaryLabel.first_chart_reference
    (l := (129058126439213/100000000000000:ℝ))
    (u := (64529063219607/50000000000000:ℝ))
    (dlo := (1083/1000:ℝ)) (dhi := (271/250:ℝ)) (primary_domain primary_one_mem)
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])

lemma M_first_above_one {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    (1083/1000:ℝ)<PPrimaryLabel.d1 a :=
  M_one_first.1.trans_le (M_first_monotone primary_one_mem
    ⟨primary_one_mem.1.trans ha.1,ha.2⟩ ha.1)

lemma M_monotone : MonotoneOn PPrimaryLabel.outer (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (PPrimaryLabel.outer_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun a ha => PPrimaryLabel.outer_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun a ha => by linarith [M_first_lower (Ioo_subset_Icc_self ha)])

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo
