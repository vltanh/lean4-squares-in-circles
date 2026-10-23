module

public import SquaresInCircles.Eight.TableFree.SecondMixedLHeightGrowth

/-!
# Two affine lower bounds for the L height label

A chord controls the whole concave height range below 1.6. Above 1.6
the global first-derivative lower bound gives one affine minorant.
These two explicit lines suffice for the complete positive-core corner.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.LHeightAffine
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

lemma references : -(800617/1000000:ℝ)<LHeight.eval (171/125) ∧
    -(277727/500000:ℝ)<LHeight.eval (8/5) := by
  have h0 := root_cage (u := (171/125:ℝ))
    (l := (1429746830736/1000000000000:ℝ)) (r := (1429746830737/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  have h1 := root_cage (u := (8/5:ℝ))
    (l := (1164302366226/1000000000000:ℝ)) (r := (1164302366227/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  constructor <;> dsimp [HeightLabel.eval,LHeight] <;> nlinarith [h0.2,h1.2]

theorem low {u : ℝ} (hu : u∈Icc (171/125:ℝ) (8/5)) :
    (132/125)*u-89809/40000<LHeight.eval u := by
  have hdom {y : ℝ} (hy : y∈Icc (171/125:ℝ) (8/5)) : y∈LHeightBounds.heights :=
    ⟨hy.1,by linarith [hy.2]⟩
  have hc : ConcaveOn ℝ (Icc (171/125:ℝ) (8/5))
      (fun y => LHeight.eval y-(132/125)*y+89809/40000) :=
    concave_of_deriv2
      (fun y hy => ((LHeight.eval_hasDerivAt (LHeightBounds.domain (hdom hy))).sub
        ((hasDerivAt_id y).const_mul (132/125))).add_const (89809/40000))
      (fun y hy => (LHeight.d1_hasDerivAt (LHeightBounds.domain (hdom hy))).sub_const (132/125))
      (fun y hy => (LHeightBounds.second_negative_below (hdom hy) hy.2).le)
  have hh := concave_gt_of_endpoints hc hu
    (show (0:ℝ)<LHeight.eval (171/125)-(132/125)*(171/125)+89809/40000 by linarith [references.1])
    (show (0:ℝ)<LHeight.eval (8/5)-(132/125)*(8/5)+89809/40000 by linarith [references.2])
  linarith

theorem high {u : ℝ} (hu : u∈Icc (8/5:ℝ) (383/200)) :
    (19/20)*u-1037727/500000<LHeight.eval u := by
  have hdom {y : ℝ} (hy : y∈Icc (8/5:ℝ) (383/200)) : y∈LHeightBounds.heights :=
    ⟨by linarith [hy.1],hy.2⟩
  have hm : MonotoneOn (fun y => LHeight.eval y-(19/20)*y) (Icc (8/5:ℝ) (383/200)) :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => ((LHeight.eval_hasDerivAt (LHeightBounds.domain (hdom hy))).sub
        ((hasDerivAt_id y).const_mul (19/20))).continuousAt.continuousWithinAt)
      (fun y hy => (LHeight.eval_hasDerivAt (LHeightBounds.domain (hdom (Ioo_subset_Icc_self hy)))).sub
        ((hasDerivAt_id y).const_mul (19/20)))
      (fun y hy => by linarith [LHeightBounds.first_lower (hdom (Ioo_subset_Icc_self hy))])
  have hh := hm (by norm_num) hu hu.1
  linarith [references.2]

end SquaresInCircles.Eight.TableFree.SecondWord.LHeightAffine
