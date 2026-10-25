module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeData
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoPrimaryBound

/-!
# The physical source-diagonal boundary for negative edge three

The target label is increasing and strictly concave.  Its physical
contact coordinate is increasing and strictly concave as well.  Their
composition therefore makes the whole contact cost concave, without
an angle subdivision.  Both true endpoint costs exceed `.93`.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Diagonal

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo.PrimaryDiagonal

def cost (x : ℝ) : ℝ := value outerDiagonal (height x) (Real.pi/2-x)
def first (x : ℝ) : ℝ := -1+KLabel.d1 (height x)*speed x
def second (x : ℝ) : ℝ :=
  KLabel.d2 (height x)*(speed x)^2+KLabel.d1 (height x)*acceleration x

lemma cost_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt cost (first x) x := by
  have hd := (((hasDerivAt_id' x).const_sub (Real.pi/2)).sub_const
    (T outerDiagonal)).add
      ((KLabel.outer_hasDerivAt (outer_domain (target_mem hx))).comp x
        (height_hasDerivAt hx.1))
  have hfun : cost=fun y => (Real.pi/2-y-T outerDiagonal)+KLabel.outer (height y) := by
    funext y
    simp only [cost,value,K]
  rw [hfun]
  exact hd

lemma first_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt first (second x) x := by
  have hd := (((KLabel.d1_hasDerivAt (outer_domain (target_mem hx))).comp x
    (height_hasDerivAt hx.1)).mul (speed_hasDerivAt hx.1)).const_add (-1)
  exact hd.congr_deriv (by simp only [second,Function.comp_apply]; ring)

lemma second_negative {x : ℝ} (hx : Domain x) : second x<0 := by
  have hb := target_mem hx
  have hleft := mul_neg_of_neg_of_pos
    (show KLabel.d2 (height x)<0 by linarith [K_second_upper hb])
    (pow_pos (show 0<speed x by linarith [speed_positive hx.1]) 2)
  have hright := mul_neg_of_pos_of_neg
    (show 0<KLabel.d1 (height x) by linarith [(K_first_bounds hb).1])
    (acceleration_negative hx.1)
  dsimp [second]
  linarith

lemma zero_value : (93/100:ℝ)<cost 0 := by
  have hb : 1-outerDiagonal∈Icc 0 outerDiagonal := by
    constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]
  have hK := K_chord hb
  dsimp [cost,value]
  rw [height_zero]
  linarith [pi_hand_enclosure.1,T_diagonal_upper,K_zero_bounds.1,
    outer_endpoint_bounds.2.2.2]

lemma endpoint_value {e : ℝ} (he : e∈Icc (2/5) (139/250))
    (hc : height e=outerDiagonal) : (93/100:ℝ)<cost e := by
  dsimp [cost,value]
  rw [hc]
  linarith [pi_hand_enclosure.1,he.2,T_diagonal_upper,K_diagonal_lower]

theorem cost_lower {x : ℝ} (hx : Domain x) : (93/100:ℝ)<cost x := by
  obtain ⟨e,he,hc⟩ := end_contact
  have hefull : e∈Icc 0 (7/10) := ⟨by linarith [he.1],by linarith [he.2]⟩
  have hed : Domain e := ⟨hefull,by rw [hc]⟩
  have hxe := bounded_by_end hx he hc
  have hconcave : ConcaveOn ℝ (Icc 0 e) cost := by
    apply concave_of_deriv2
      (fun t ht => cost_hasDerivAt (before hed ht))
      (fun t ht => first_hasDerivAt (before hed ht))
    intro t ht
    exact (second_negative (before hed ht)).le
  exact concave_gt_of_endpoints hconcave ⟨hx.1.1,hxe⟩ zero_value
    (endpoint_value he hc)

theorem original_contact {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.lowerSource A B x=outerDiagonal) :
    (93/100:ℝ)<value outerDiagonal B (Real.pi/2-x) := by
  have he := original_height ht hx hc
  have hd : Domain x := ⟨hx,by rw [he]; exact (NegativeTwo.source_mem ht).2⟩
  simpa only [cost,he] using cost_lower hd

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Diagonal
