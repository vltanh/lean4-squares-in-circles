module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveCoreThreeData
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeSpeed

/-!
# Primary T-label growth on the whole early zero-contact height range

One rational height reference, followed by derivative monotonicity,
proves that the second derivative exceeds twice the first derivative.
This supplies both the contact cost curvature and the boundary slope
comparison. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic

lemma primary_second_monotone :
    MonotoneOn TPrimaryLabel.d2 (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (TPrimaryLabel.d2_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun a ha => TPrimaryLabel.d2_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun a ha => (NegativeThree.primary_third_positive (Ioo_subset_Icc_self ha)).le)

lemma primary_first_monotone : MonotoneOn TPrimaryLabel.d1 (Icc (1:ℝ) outerAxial) := by
  have hdom {a : ℝ} (ha : a∈Icc (1:ℝ) outerAxial) : a∈Icc outerDiagonal outerAxial :=
    ⟨primary_one_mem.1.trans ha.1,ha.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun a ha => (TPrimaryLabel.d1_hasDerivAt (primary_domain (hdom ha))).continuousAt.continuousWithinAt)
    (fun a ha => TPrimaryLabel.d1_hasDerivAt (primary_domain (hdom (Ioo_subset_Icc_self ha))))
  intro a ha
  have hh := primary_second_monotone primary_one_mem
    (hdom (Ioo_subset_Icc_self ha)) ha.1.le
  linarith [NegativeThree.primary_one_references.2.2.1]

lemma primary_growth_reference :
    (981/1000:ℝ)<TPrimaryLabel.d1 (147/125) ∧
    TPrimaryLabel.d1 (147/125)<(491/500:ℝ) ∧
    (64/25:ℝ)<TPrimaryLabel.d2 (147/125) := by
  have ha : (147/125:ℝ)∈Icc outerDiagonal outerAxial := by
    constructor <;> linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]
  have h1 := TPrimaryLabel.first_chart_reference (primary_domain ha)
    (l := (105196197649/100000000000:ℝ)) (u := (2103923953/2000000000:ℝ))
    (dlo := (981/1000:ℝ)) (dhi := (491/500:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  have h2 := TPrimaryLabel.second_chart_reference (primary_domain ha)
    (l := (105196197649/100000000000:ℝ)) (u := (2103923953/2000000000:ℝ))
    (dlo := (64/25:ℝ)) (dhi := (257/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  exact ⟨h1.1,h1.2,h2.1⟩

lemma primary_growth {a : ℝ} (ha : a∈Icc (147/125:ℝ) outerAxial) :
    (981/1000:ℝ)<TPrimaryLabel.d1 a ∧ 2*TPrimaryLabel.d1 a<TPrimaryLabel.d2 a := by
  have hdom {a : ℝ} (ha : a∈Icc (147/125:ℝ) outerAxial) : a∈Icc outerDiagonal outerAxial :=
    ⟨by linarith [ha.1,outer_endpoint_bounds.2.2.2],ha.2⟩
  have hr : (147/125:ℝ)∈Icc (147/125:ℝ) outerAxial :=
    ⟨le_rfl,by linarith [outer_endpoint_bounds.1]⟩
  have hm : MonotoneOn (fun a => TPrimaryLabel.d2 a-2*TPrimaryLabel.d1 a)
      (Icc (147/125:ℝ) outerAxial) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a ha => ((TPrimaryLabel.d2_hasDerivAt (primary_domain (hdom ha))).sub
        ((TPrimaryLabel.d1_hasDerivAt (primary_domain (hdom ha))).const_mul 2)).continuousAt.continuousWithinAt)
      (fun a ha => (TPrimaryLabel.d2_hasDerivAt (primary_domain (hdom (Ioo_subset_Icc_self ha)))).sub
        ((TPrimaryLabel.d1_hasDerivAt (primary_domain (hdom (Ioo_subset_Icc_self ha)))).const_mul 2))
      (fun a ha => (NegativeThree.primary_growth_one (hdom (Ioo_subset_Icc_self ha))).le)
  have hh := hm hr ha ha.1
  have hf := primary_first_monotone
    (show (147/125:ℝ)∈Icc (1:ℝ) outerAxial from ⟨by norm_num,hr.2⟩)
    (show a∈Icc (1:ℝ) outerAxial from ⟨by linarith [ha.1],ha.2⟩) ha.1
  exact ⟨primary_growth_reference.1.trans_le hf,by
    linarith [primary_growth_reference.2.1,primary_growth_reference.2.2]⟩

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore
