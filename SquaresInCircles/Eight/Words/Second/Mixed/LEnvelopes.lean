module

public import SquaresInCircles.Eight.Words.Second.Outer.LBounds
public import SquaresInCircles.Eight.Words.Second.Outer.ConcaveSlope

/-!
# Eight squares: three whole-arc affine bounds for the actual L label

One tangent parabola controls the initial concave arc. A concave
derivative then reduces the remaining interval to its two endpoints.
The references are fixed rational points of the unchanged Q0 circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedLEnvelopes
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma half_references : LLabel.d1 (1/2)<(5/8:ℝ) ∧ LLabel.d2 (1/2)< -(3/100:ℝ) := by
  have h1 := LLabel.first_chart_reference (outer_domain L_half_mem)
    (l := (170751281107931/100000000000000:ℝ))
    (u := (170751281107932/100000000000000:ℝ))
    (dlo := (3/5:ℝ)) (dhi := (5/8:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  have h2 := LLabel.second_chart_reference (outer_domain L_half_mem)
    (l := (170751281107931/100000000000000:ℝ))
    (u := (170751281107932/100000000000000:ℝ))
    (dlo := (-1:ℝ)) (dhi := (-(3/100):ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact ⟨h1.2,h2.2⟩

lemma affine_half {r q c δ k B : ℝ} (hr : r∈Icc (0:ℝ) (1/2))
    (hvalue : L r<c) (hslope : |LLabel.d1 r-q|<δ) (_hδ : 0≤δ)
    (hgap : c-q*r+δ^2/(3/50)≤k) (hB : B∈Icc (0:ℝ) (1/2)) : L B<k+q*B := by
  have hdom {y : ℝ} (hy : y∈Icc (0:ℝ) (1/2)) : y∈Icc 0 outerDiagonal :=
    ⟨hy.1,hy.2.trans L_half_mem.2⟩
  have ht := curvature_tangent (f := fun y => q*y-L y) (d := fun y => q-LLabel.d1 y)
    (dd := fun y => -LLabel.d2 y) (κ := (3/100:ℝ)) hB hr
    (fun y hy => by simpa [L] using LLabel.affine_difference_hasDerivAt q (outer_domain (hdom hy)))
    (fun y hy => (LLabel.d1_hasDerivAt (outer_domain (hdom hy))).const_sub q)
    (fun y hy => by
      have hm := L_second_monotone (hdom hy) L_half_mem hy.2
      linarith [half_references.2])
  have hd := abs_lt.mp hslope
  have hprod := mul_pos (show 0<δ+(LLabel.d1 r-q) by linarith [hd.1])
    (show 0<δ-(LLabel.d1 r-q) by linarith [hd.2])
  have hs := sq_nonneg ((3/100)*(B-r)+(q-LLabel.d1 r))
  nlinarith

lemma affine_continue {q k t B : ℝ} (ht : t∈Icc (1/2:ℝ) outerDiagonal)
    (hhalf : ∀y∈Icc (0:ℝ) (1/2),L y<k+q*y)
    (hslope : LLabel.d1 (1/2)<q) (hend : L t<k+q*t)
    (hB : B∈Icc (0:ℝ) t) : L B<k+q*B := by
  by_cases he : B≤1/2
  · exact hhalf B ⟨hB.1,he⟩
  · have hdom {y : ℝ} (hy : y∈Icc (1/2:ℝ) t) : y∈Icc 0 outerDiagonal :=
      ⟨by linarith [hy.1],hy.2.trans ht.2⟩
    have hm := MinimumCalculus.endpoint_minimum_of_third_nonpos
      (f := fun y => q*y-L y) (d := fun y => q-LLabel.d1 y)
      (dd := fun y => -LLabel.d2 y) (ddd := fun y => -LLabel.d3 y)
      (show B∈Icc (1/2:ℝ) t from ⟨by linarith,hB.2⟩)
      (fun y hy => by simpa [L] using LLabel.affine_difference_hasDerivAt q (outer_domain (hdom hy)))
      (fun y hy => (LLabel.d1_hasDerivAt (outer_domain (hdom hy))).const_sub q)
      (fun y hy => (LLabel.d2_hasDerivAt (outer_domain (hdom hy))).neg)
      (fun y hy => neg_nonpos.mpr (L_third_positive (hdom hy)).le)
      (by linarith)
    have hl := hhalf (1/2) (by norm_num)
    have hmin : -k< min (q*(1/2)-L (1/2)) (q*t-L t) := lt_min (by linarith) (by linarith)
    linarith

lemma reference_3424 : L (214/625)<(346979939/1000000000:ℝ) ∧
    |LLabel.d1 (214/625)-(69/100)|<(7/500000:ℝ) := by
  have hb := Asymmetric.rational_outer_mem (show (214/625:ℝ)∈Icc 0 (899/1000) by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (1790520103210/1000000000000:ℝ)) (u := (1790520103211/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hd := LLabel.first_chart_reference (outer_domain hb)
    (l := (1790520103210/1000000000000:ℝ)) (u := (1790520103211/1000000000000:ℝ))
    (dlo := (69/100:ℝ)) (dhi := (345007/500000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  constructor
  · dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel,U] at *
    nlinarith [hr.1]
  · rw [abs_lt]
    constructor <;> linarith [hd.1,hd.2]

lemma reference_794 : L (397/500)<(111/1000:ℝ)+(69/100)*(397/500) := by
  have hb := Asymmetric.rational_outer_mem (show (397/500:ℝ)∈Icc 0 (899/1000) by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (1497051769311/1000000000000:ℝ)) (u := (1497051769312/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel,U] at *
  nlinarith [hr.1]

theorem late_transverse {B : ℝ} (hB : B∈Icc (0:ℝ) (397/500)) :
    L B<(111/1000:ℝ)+(69/100)*B := by
  apply affine_continue
    (show (397/500:ℝ)∈Icc (1/2:ℝ) outerDiagonal from
      ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num : (397/500:ℝ)∈Icc 0 (899/1000))).2⟩)
    (fun y hy => affine_half (r := (214/625:ℝ)) (c := (346979939/1000000000:ℝ))
      (δ := (7/500000:ℝ)) (by norm_num) reference_3424.1 reference_3424.2
      (by norm_num) (by norm_num) hy)
    (by linarith [half_references.1]) reference_794 hB

lemma reference_42 : L (21/50)<(797087493/2000000000:ℝ) ∧
    |LLabel.d1 (21/50)-(12867969/20000000)|<(1/1000000000:ℝ) := by
  have hb := Asymmetric.rational_outer_mem (show (21/50:ℝ)∈Icc 0 (899/1000) by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (175191323986092/100000000000000:ℝ)) (u := (175191323986093/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hd := LLabel.first_chart_reference (outer_domain hb)
    (l := (175191323986092/100000000000000:ℝ)) (u := (175191323986093/100000000000000:ℝ))
    (dlo := (643398449/1000000000:ℝ)) (dhi := (12867969/20000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  constructor
  · dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel,U] at *
    nlinarith [hr.1]
  · rw [abs_lt]
    constructor <;> linarith [hd.1,hd.2]

lemma reference_65 : L (13/20)<(128316398/1000000000:ℝ)+(12867969/20000000)*(13/20) := by
  have hb := Asymmetric.rational_outer_mem (show (13/20:ℝ)∈Icc 0 (899/1000) by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (1610310529059/1000000000000:ℝ)) (u := (1610310529060/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel,U] at *
  nlinarith [hr.1]

theorem primary {B : ℝ} (hB : B∈Icc (0:ℝ) (13/20)) :
    L B<(128316398/1000000000:ℝ)+(12867969/20000000)*B := by
  apply affine_continue
    (show (13/20:ℝ)∈Icc (1/2:ℝ) outerDiagonal from
      ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num : (13/20:ℝ)∈Icc 0 (899/1000))).2⟩)
    (fun y hy => affine_half (r := (21/50:ℝ)) (c := (797087493/2000000000:ℝ))
      (δ := (1/1000000000:ℝ)) (by norm_num) reference_42.1 reference_42.2
      (by norm_num) (by norm_num) hy)
    (by linarith [half_references.1]) reference_65 hB

end SquaresInCircles.Eight.SecondWord.MixedLEnvelopes
