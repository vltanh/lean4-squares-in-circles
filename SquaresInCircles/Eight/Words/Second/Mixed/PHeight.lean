module

public import SquaresInCircles.Eight.Words.Second.Mixed.HeightLabel

/-!
# Eight squares: the exact negative P label in height coordinates

The third and fourth derivatives are positive on the whole displayed
radical domain. Actual outer heights lie above 1.399, so Taylor lower
bounds based there apply to every original source point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord
open CommonQuarter CorePairGeometry Arithmetic

def PHeight : HeightLabel := ⟨92374843/250000000,-2363/100000,2211/20000,192359/200000⟩

lemma PHeight_actual {a b : ℝ} (hs : OuterState a b) : PHeight.eval (a+1/2)= -P b := by
  have hc := hs.2.2
  norm_num [Q0] at hc
  rw [HeightLabel.eval,HeightLabel.actual_root hs,
    show P b=PLabel.eval a b from PLabel.outer_actual hs]
  norm_num [PHeight,PLabel,RoleLabel.eval]
  linear_combination (2363/100000)*hc

namespace PHeightBounds
open HeightLabel

def heights : Set ℝ := Icc 1 (383/200)
def physicalHeights : Set ℝ := Icc (1399/1000) (383/200)

lemma physical_subset : physicalHeights⊆heights := fun _ hu => ⟨by linarith [hu.1],hu.2⟩

lemma domain {u : ℝ} (hu : u∈heights) : 0<Q0-u^2 := by
  have hp := pow_le_pow_left₀ (by linarith [hu.1] : 0≤u) hu.2 2
  norm_num [Q0]
  nlinarith

lemma actual_height {a b : ℝ} (hs : OuterState a b) : a+1/2∈physicalHeights := by
  have ha : a∈Icc outerDiagonal outerAxial :=
    ⟨(CommonQuarter.outer_bounds hs).1,(CommonQuarter.outer_bounds hs).2.1⟩
  exact ⟨by linarith [ha.1,fine_outer_endpoint_bounds.2],
    by linarith [ha.2,outer_endpoint_bounds.2.1]⟩

lemma third_positive {u : ℝ} (hu : u∈heights) : 0<PHeight.d3 u := by
  have he := PHeight.d3_mul (domain hu)
  have hr := pow_pos (root_pos (domain hu)) 5
  have hn : 0<PHeight.w*u-PHeight.k*Q0 := by
    norm_num [PHeight,Q0]
    linarith [hu.1]
  have hp := mul_pos (show 0<3*Q0 by norm_num [Q0]) hn
  nlinarith

lemma fourth_positive {u : ℝ} (hu : u∈heights) : 0<PHeight.d4 u := by
  have he := PHeight.fourth_growth_identity (domain hu) 0
  have hn : 0<PHeight.w*u-PHeight.k*Q0 := by
    norm_num [PHeight,Q0]
    linarith [hu.1]
  have h1 := mul_pos (show 0<PHeight.w by norm_num [PHeight]) (domain hu)
  have h2 := mul_pos (show 0<5*u by linarith [hu.1]) hn
  have hp := mul_pos (show 0<3*Q0 by norm_num [Q0]) (add_pos h1 h2)
  have hr := pow_pos (root_pos (domain hu)) 7
  norm_num at he
  nlinarith

lemma second_monotone : MonotoneOn PHeight.d2 heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u hu => (PHeight.d2_hasDerivAt (domain hu)).continuousAt.continuousWithinAt)
    (fun u hu => PHeight.d2_hasDerivAt (domain (Ioo_subset_Icc_self hu)))
    (fun u hu => (third_positive (Ioo_subset_Icc_self hu)).le)

lemma third_monotone : MonotoneOn PHeight.d3 heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u hu => (PHeight.d3_hasDerivAt (domain hu)).continuousAt.continuousWithinAt)
    (fun u hu => PHeight.d3_hasDerivAt (domain (Ioo_subset_Icc_self hu)))
    (fun u hu => (fourth_positive (Ioo_subset_Icc_self hu)).le)

end PHeightBounds
end SquaresInCircles.Eight.SecondWord
