module

public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeThreeAligned
public import SquaresInCircles.Eight.TableFree.SecondOuterLabelBounds

/-!
# Finite L-label growth from the actual outer circle

The unit-primary circle point anchors the upper mixed arguments.
Circle subtraction gives a rational chord bound, and the proved
whole-arc derivative bound gives its exact label increment.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.EdgeThreeAligned
open CommonQuarter CorePairGeometry Arithmetic

lemma L_lipschitz {b c : ℝ} (hb : b∈Icc (0:ℝ) outerDiagonal)
    (hc : c∈Icc (0:ℝ) outerDiagonal) (hbc : b≤c) :
    L c-L b≤(147/125)*(c-b) := by
  have hd : ∀z∈Icc (0:ℝ) outerDiagonal,
      HasDerivAt (fun y => L y-(147/125)*y) (LLabel.d1 z-147/125) z := by
    intro z hz
    simpa [L] using (LLabel.outer_hasDerivAt (outer_domain hz)).sub
      ((hasDerivAt_id z).const_mul (147/125))
  have hm : AntitoneOn (fun y => L y-(147/125)*y) (Icc (0:ℝ) outerDiagonal) :=
    antiOn_of_hasDeriv_nonpos
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz => hd z (Ioo_subset_Icc_self hz))
      (fun z hz => by linarith [(L_first_bounds (Ioo_subset_Icc_self hz)).2])
  have hh := hm hb hc hbc
  linarith

lemma L_zero : L 0=(793/20000:ℝ) := by
  norm_num [L,LLabel,RoleLabel.outer,RoleLabel.eval]

lemma L_global_affine {B : ℝ} (hB : B∈Icc (0:ℝ) outerDiagonal) :
    L B≤793/20000+(147/125)*B := by
  have hh := L_lipschitz
    (show (0:ℝ)∈Icc (0:ℝ) outerDiagonal from ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩)
    hB hB.1
  rw [L_zero] at hh
  linarith

lemma unit_circle_chord {A B : ℝ} (ht : OuterState A B) (hA : A≤1) :
    B-B1≤(7/6)*(1-A) := by
  have hB := (unit_target_cut ht).2 hA
  have hQ := ht.2.2
  have hQ1 := unit_state.2.2
  have hpos := mul_nonneg (sub_nonneg.mpr hB)
    (show 0≤B+B1+1-18/7 by linarith [B1_bounds.1])
  have hs := sq_nonneg (1-A)
  nlinarith

lemma unit_label_increment {A B : ℝ} (ht : OuterState A B) (hA : A≤1) :
    L B-L B1≤(343/250)*(1-A) := by
  have hdB : B∈Icc (0:ℝ) outerDiagonal :=
    ⟨(outer_bounds ht).2.2.1,(outer_bounds ht).2.2.2.1⟩
  have hl := L_lipschitz B1_domain hdB ((unit_target_cut ht).2 hA)
  have hc := unit_circle_chord ht hA
  linarith

lemma upper_trig {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) :
    (19121/25000:ℝ)<Real.cos x ∧ Real.cos x≤1 ∧
    0≤Real.sin x ∧ Real.sin x≤x ∧
    0≤1-Real.cos x ∧ 1-Real.cos x≤(7/20)*x := by
  have ht := positive_trig hx
  have hq := Real.one_sub_sq_div_two_le_cos x
  have hp := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.2.1,by linarith [ht.2.1],?_⟩
  nlinarith

lemma short_upper_trig {x : ℝ} (hx : x∈Icc (0:ℝ) (11/100)) :
    (19879/20000:ℝ)≤Real.cos x ∧
    1-Real.cos x≤(11/200)*x := by
  have hq := Real.one_sub_sq_div_two_le_cos x
  have hp := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hs := pow_le_pow_left₀ hx.1 hx.2 2
  constructor <;> nlinarith

lemma negative_core_upper {a b : ℝ} (hs : CoreState a b) :
    MixedThree.negativeCore a b≤en+gn*b := by
  rcases hs with ⟨rfl,hb,hbu⟩ | ⟨hb,hba,hq⟩
  · dsimp [MixedThree.negativeCore,en,LPrimaryZero.e,gn]
    nlinarith [sq_nonneg b]
  · have ha := (CoreAngleEndpoint.corner_diagonal hb hba hq).2
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hb 2
    dsimp [MixedThree.negativeCore,en,LPrimaryZero.e,gn]
    nlinarith [CoreAngleEndpoint.diagonal_bounds.1]

lemma negative_core_coarse {a b : ℝ} (hs : CoreState a b) :
    MixedThree.negativeCore a b<(57/100:ℝ) := by
  have hh := negative_core_upper hs
  have hb := CoreAngleEndpoint.state_bounds hs
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hbd := hb.2.2.2.2
  dsimp [en,LPrimaryZero.e,gn] at hh
  nlinarith [hd.2]

lemma positive_label_diagonal : L outerDiagonal<(95446/125000:ℝ) := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤449607/500000) hd.1.le 2
  norm_num [L,LLabel,RoleLabel.outer,RoleLabel.eval,ShortOuterOne.SameContact.arc_diagonal]
  nlinarith

lemma positive_large_angle {b A B φ : ℝ} (ht : OuterState A B)
    (hb : 0≤b) (hφ : (42/25:ℝ)≤φ) :
    threshold<positiveCost b B φ := by
  have hL := L_monotone
    (show B∈Icc (0:ℝ) outerDiagonal from
      ⟨(outer_bounds ht).2.2.1,(outer_bounds ht).2.2.2.1⟩)
    (show outerDiagonal∈Icc (0:ℝ) outerDiagonal from
      ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩) (outer_bounds ht).2.2.2.1
  have hgb := mul_nonneg (by norm_num : (0:ℝ)≤gp) hb
  dsimp [positiveCost,threshold,ep] at *
  linarith [positive_label_diagonal]

end SquaresInCircles.Eight.TableFree.SecondWord.EdgeThreeAligned
