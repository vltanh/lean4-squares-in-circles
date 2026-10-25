module

public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeFirstContact

/-!
# Eight squares: the actual meeting point of the two diagonal contact boundaries

The original source coordinate at a diagonal target decreases
strictly with the angle.  Two fixed Taylor references locate its
unique crossing of the source diagonal between `1.014` and `1.015`.
The crossing is constructed by the intermediate value theorem.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalContact

open CommonQuarter CorePairGeometry Arithmetic

def parameter : ℝ := 1/2-outerDiagonal
def height (φ : ℝ) : ℝ := FirstContact.source outerDiagonal φ
def heightFirst (φ : ℝ) : ℝ :=
  (1/2-outerDiagonal)*Real.cos φ-(outerDiagonal+1/2)*Real.sin φ
def heightSecond (φ : ℝ) : ℝ := 1/2-height φ

lemma diagonal_mem : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
lemma parameter_mem : parameter∈Icc (-2/5:ℝ) (1/2) := by
  dsimp [parameter]
  constructor <;> linarith [outer_endpoint_bounds.2.2.2,fine_outer_endpoint_bounds.2]

lemma height_formula (φ : ℝ) :
    height φ=1/2+(1/2-outerDiagonal)*Real.sin φ+
      (outerDiagonal+1/2)*Real.cos φ := by
  dsimp [height,FirstContact.source,U,W]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  ring

lemma height_hasDerivAt (φ : ℝ) : HasDerivAt height (heightFirst φ) φ := by
  have hd := (((Real.hasDerivAt_sin φ).const_mul (1/2-outerDiagonal)).const_add
    (1/2)).add ((Real.hasDerivAt_cos φ).const_mul (outerDiagonal+1/2))
  convert hd using 1
  · ext t
    exact height_formula t
  · dsimp [heightFirst]
    ring

lemma heightFirst_hasDerivAt (φ : ℝ) :
    HasDerivAt heightFirst (heightSecond φ) φ := by
  have hd := ((Real.hasDerivAt_cos φ).const_mul (1/2-outerDiagonal)).sub
    ((Real.hasDerivAt_sin φ).const_mul (outerDiagonal+1/2))
  convert hd using 1
  · rfl
  · rw [heightSecond,height_formula]
    ring

lemma heightFirst_upper {φ : ℝ} (hφ : Lower φ) : heightFirst φ<(-1:ℝ) := by
  have ht := lower_trig hφ
  have hfirst := mul_nonpos_of_nonpos_of_nonneg
    (show 1/2-outerDiagonal≤0 by linarith [fine_outer_endpoint_bounds.2]) ht.2.2.1
  have hlast := mul_lt_mul''
    (show (1399/1000:ℝ)<outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
    ht.1 (by norm_num : (0:ℝ)≤1399/1000) (by norm_num : (0:ℝ)≤19121/25000)
  dsimp [heightFirst]
  linarith

lemma height_antitone : AntitoneOn height (Icc lowerAngle (Real.pi/2)) :=
  antiOn_of_hasDeriv_nonpos
    (fun φ _ => (height_hasDerivAt φ).continuousAt.continuousWithinAt)
    (fun φ _ => height_hasDerivAt φ)
    (fun φ hφ => by linarith [heightFirst_upper (Ioo_subset_Icc_self hφ)])

lemma height_shift_antitone :
    AntitoneOn (fun φ => height φ+φ) (Icc lowerAngle (Real.pi/2)) :=
  antiOn_of_hasDeriv_nonpos
    (fun φ _ => ((height_hasDerivAt φ).add (hasDerivAt_id φ)).continuousAt.continuousWithinAt)
    (fun φ _ => (height_hasDerivAt φ).add (hasDerivAt_id φ))
    (fun φ hφ => by linarith [heightFirst_upper (Ioo_subset_Icc_self hφ)])

lemma reference_lower : outerDiagonal<height (507/500) := by
  have ht := PointProducts.trig (show (0:ℝ)≤507/500 by norm_num)
  have hneg : 1/2-outerDiagonal∈Icc
      (1/2-(89921406510941/10^14:ℝ)) (1/2-(89921406510940/10^14:ℝ)) :=
    ⟨by linarith [diagonal_fine.2],by linarith [diagonal_fine.1]⟩
  have hpos : outerDiagonal+1/2∈Icc
      ((89921406510940/10^14:ℝ)+1/2) ((89921406510941/10^14:ℝ)+1/2) :=
    ⟨by linarith [diagonal_fine.1],by linarith [diagonal_fine.2]⟩
  have hs := PointProducts.product hneg ht.1
  have hc := PointProducts.product hpos ht.2
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at hs hc
  rw [height_formula]
  linarith [hs.1,hc.1,diagonal_fine.2]

lemma reference_upper : height (203/200)<outerDiagonal := by
  have ht := PointProducts.trig (show (0:ℝ)≤203/200 by norm_num)
  have hneg : 1/2-outerDiagonal∈Icc
      (1/2-(89921406510941/10^14:ℝ)) (1/2-(89921406510940/10^14:ℝ)) :=
    ⟨by linarith [diagonal_fine.2],by linarith [diagonal_fine.1]⟩
  have hpos : outerDiagonal+1/2∈Icc
      ((89921406510940/10^14:ℝ)+1/2) ((89921406510941/10^14:ℝ)+1/2) :=
    ⟨by linarith [diagonal_fine.1],by linarith [diagonal_fine.2]⟩
  have hs := PointProducts.product hneg ht.1
  have hc := PointProducts.product hpos ht.2
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at hs hc
  rw [height_formula]
  linarith [hs.2,hc.2,diagonal_fine.1]

lemma join_lower {e : ℝ} (he : e∈Icc (507/500:ℝ) (203/200)) : Lower e := by
  constructor
  · dsimp [lowerAngle]
    linarith [he.1,pi_hand_enclosure.2]
  · linarith [he.2,pi_hand_enclosure.1]

theorem exists_join : ∃ e : ℝ, e∈Icc (507/500:ℝ) (203/200) ∧ height e=outerDiagonal := by
  have hc : Continuous height := continuous_iff_continuousAt.mpr
    (fun t => (height_hasDerivAt t).continuousAt)
  obtain ⟨e,he,hh⟩ := intermediate_value_Icc (show (507/500:ℝ)≤203/200 by norm_num)
    hc.neg.continuousOn
    (show -outerDiagonal∈Icc (-height (507/500)) (-height (203/200)) from
      ⟨by linarith [reference_lower],by linarith [reference_upper]⟩)
  have hh' : -height e=-outerDiagonal := hh
  exact ⟨e,he,by linarith⟩

lemma before_join {φ e : ℝ} (hφ : Lower φ)
    (he : e∈Icc (507/500:ℝ) (203/200)) (hc : height e=outerDiagonal)
    (hh : outerDiagonal≤height φ) : φ≤e := by
  rcases le_total φ e with h | h
  · exact h
  · have hs : height φ+φ≤height e+e := height_shift_antitone (join_lower he) hφ h
    rw [hc] at hs
    linarith

lemma after_join {φ e : ℝ} (hφ : Lower φ)
    (he : e∈Icc (507/500:ℝ) (203/200)) (hc : height e=outerDiagonal)
    (hh : height φ≤outerDiagonal) : e≤φ := by
  rcases le_total e φ with h | h
  · exact h
  · have hs : height e+e≤height φ+φ := height_shift_antitone hφ (join_lower he) h
    rw [hc] at hs
    linarith

lemma corner_value {e : ℝ} (he : e∈Icc (507/500:ℝ) (203/200)) :
    (44889/50000:ℝ)<value outerDiagonal outerDiagonal e := by
  dsimp [value]
  linarith [he.1,V_diagonal_bounds.1,L_diagonal_upper]

end SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalContact
