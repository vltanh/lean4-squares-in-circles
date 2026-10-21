module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreePrimary
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeAligned

/-!
# Two primary-height slope bounds for the opposite edge-three contact

The transformed source label has positive third derivative on the entire
primary circle chart.  Its first derivative is therefore convex, and two
rational-height references bound it on the complete initial primary arcs.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open NegativeThree (TPrimaryLabel)

lemma primary_eleven_mem : (11/10:ℝ)∈Icc outerDiagonal outerAxial := by
  constructor <;> linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]

lemma primary_six_fifths_mem : (6/5:ℝ)∈Icc outerDiagonal outerAxial := by
  constructor <;> linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]

lemma primary_eleven_first : TPrimaryLabel.d1 (11/10)<(17/20:ℝ) := by
  have hh := TPrimaryLabel.first_chart_reference (primary_domain primary_eleven_mem)
    (l := (116430236/10^8:ℝ)) (u := (116430237/10^8:ℝ))
    (dlo := (4/5:ℝ)) (dhi := (17/20:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  exact hh.2

lemma primary_six_fifths_first : TPrimaryLabel.d1 (6/5)<(1051/1000:ℝ) := by
  have hh := TPrimaryLabel.first_chart_reference (primary_domain primary_six_fifths_mem)
    (l := (101271911/10^8:ℝ)) (u := (101271912/10^8:ℝ))
    (dlo := (1:ℝ)) (dhi := (1051/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  exact hh.2

lemma primary_first_upper_from_endpoints {a u m : ℝ}
    (hu : u∈Icc outerDiagonal outerAxial) (ha : a∈Icc outerDiagonal u)
    (hl : TPrimaryLabel.d1 outerDiagonal<m) (hr : TPrimaryLabel.d1 u<m) :
    TPrimaryLabel.d1 a<m := by
  have hdom {t : ℝ} (ht : t∈Icc outerDiagonal u) :
      t∈Icc outerDiagonal outerAxial := ⟨ht.1,ht.2.trans hu.2⟩
  have hc : ConcaveOn ℝ (Icc outerDiagonal u) (fun t => -TPrimaryLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (TPrimaryLabel.d1_hasDerivAt (primary_domain (hdom ht))).neg)
      (fun t ht => (TPrimaryLabel.d2_hasDerivAt (primary_domain (hdom ht))).neg)
      (fun t ht => by linarith [NegativeThree.primary_third_positive (hdom ht)])
  have hh := concave_gt_of_endpoints hc ha
    (show -m< -TPrimaryLabel.d1 outerDiagonal by linarith)
    (show -m< -TPrimaryLabel.d1 u by linarith)
  linarith

lemma primary_first_eleven {a : ℝ} (ha : a∈Icc outerDiagonal (11/10)) :
    TPrimaryLabel.d1 a<(17/20:ℝ) :=
  primary_first_upper_from_endpoints primary_eleven_mem ha
    (by linarith [NegativeThree.primary_diagonal_first]) primary_eleven_first

lemma primary_first_six_fifths {a : ℝ} (ha : a∈Icc outerDiagonal (6/5)) :
    TPrimaryLabel.d1 a<(1051/1000:ℝ) :=
  primary_first_upper_from_endpoints primary_six_fifths_mem ha
    (by linarith [NegativeThree.primary_diagonal_first]) primary_six_fifths_first

lemma fifth_mem : (1/5:ℝ)∈Icc 0 outerDiagonal := by
  constructor <;> linarith [fine_outer_endpoint_bounds.2]

lemma fifth_primary_lower : (135083/100000:ℝ)<arc (1/5) := by
  have hh := shifted_chart_reference (outer_domain fifth_mem)
    (l := (185083/100000:ℝ)) (u := (185084/100000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  dsimp [U] at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree
