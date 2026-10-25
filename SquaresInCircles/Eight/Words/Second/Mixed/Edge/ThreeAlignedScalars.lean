module

public import SquaresInCircles.Eight.Words.Second.Mixed.LPrimaryZeroReferences

/-!
# Eight squares: the two remaining aligned mixed costs in height coordinates

The positive-core cost is concave between the outer diagonal and height
1.5. For the negative-core cost, a convex derivative settles the lower
height interval; one strong-convexity reference at height 1.64 settles
the entire remaining interval. Both estimates use the actual L label.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.EdgeThreeAligned
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

def threshold : ℝ := 17953/20000
def gp : ℝ := 1303/1250
def ep : ℝ := 1449/100000
def gn : ℝ := 98439/100000
def zn : ℝ := 2667/50000
abbrev en := LPrimaryZero.e

def positiveHeight (u : ℝ) : ℝ := Real.pi/2-ep+gp*(3/2-u)+LHeight.eval u
def positiveHeightD (u : ℝ) : ℝ := LHeight.d1 u-gp
def negativeHeight (u : ℝ) : ℝ :=
  Real.pi/2-en-gn*(u-3/2)+zn*(u-3/2)^2+LHeight.eval u
def negativeHeightD (u : ℝ) : ℝ := LHeight.d1 u-gn+2*zn*(u-3/2)
def negativeHeightDD (u : ℝ) : ℝ := LHeight.d2 u+2*zn

lemma positiveHeight_hasDerivAt {u : ℝ} (hu : u∈LHeightBounds.heights) :
    HasDerivAt positiveHeight (positiveHeightD u) u := by
  exact (((((hasDerivAt_id u).const_sub (3/2)).const_mul gp).const_add
    (Real.pi/2-ep)).fun_add (LHeight.eval_hasDerivAt (LHeightBounds.domain hu))).congr_deriv
    (by simp only [positiveHeightD]; ring)

lemma positiveHeightD_hasDerivAt {u : ℝ} (hu : u∈LHeightBounds.heights) :
    HasDerivAt positiveHeightD (LHeight.d2 u) u :=
  (LHeight.d1_hasDerivAt (LHeightBounds.domain hu)).sub_const gp

lemma negativeHeight_hasDerivAt {u : ℝ} (hu : u∈LHeightBounds.heights) :
    HasDerivAt negativeHeight (negativeHeightD u) u := by
  exact ((((((hasDerivAt_id u).sub_const (3/2)).const_mul gn).const_sub
    (Real.pi/2-en)).fun_add ((((hasDerivAt_id u).sub_const (3/2)).fun_pow 2).const_mul zn)).fun_add
      (LHeight.eval_hasDerivAt (LHeightBounds.domain hu))).congr_deriv
    (by simp only [negativeHeightD,id,Nat.cast_ofNat,mul_one]; ring)

lemma negativeHeightD_hasDerivAt {u : ℝ} (hu : u∈LHeightBounds.heights) :
    HasDerivAt negativeHeightD (negativeHeightDD u) u := by
  exact (((LHeight.d1_hasDerivAt (LHeightBounds.domain hu)).sub_const gn).fun_add
    (((hasDerivAt_id u).sub_const (3/2)).const_mul (2*zn))).congr_deriv
    (by simp only [negativeHeightDD]; ring)

lemma negativeHeightDD_hasDerivAt {u : ℝ} (hu : u∈LHeightBounds.heights) :
    HasDerivAt negativeHeightDD (LHeight.d3 u) u :=
  (LHeight.d2_hasDerivAt (LHeightBounds.domain hu)).add_const (2*zn)

lemma positive_zero : (361/400:ℝ)<positiveHeight (3/2) := by
  norm_num [positiveHeight,gp,ep]
  linarith [LPrimaryZero.aligned_height_value,pi_hand_enclosure.1]

lemma negative_zero : (4489/5000:ℝ)<negativeHeight (3/2) := by
  have h := LPrimaryZero.aligned_cost
  have hU : LPrimaryZero.U (Real.pi/2)=3/2 := by
    simp only [LPrimaryZero.U,PrimaryZero.U,PrimaryZero.m,Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    norm_num
  rw [LPrimaryZero.K,hU] at h
  simp only [negativeHeight,en]
  linarith

lemma diagonal_state : OuterState outerDiagonal outerDiagonal := by
  have hd : outerDiagonal∈Icc (0:ℝ) outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  simpa [ShortOuterOne.SameContact.arc_diagonal] using ShortOuterOne.SameContact.arc_state hd

lemma positive_diagonal : (89779/100000:ℝ)<positiveHeight (outerDiagonal+1/2) := by
  have hM := LHeight_actual diagonal_state
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤449607/500000) hd.1.le 2
  dsimp [positiveHeight]
  rw [hM]
  norm_num [gp,ep,L,RoleLabel.outer,RoleLabel.eval,LLabel,ShortOuterOne.SameContact.arc_diagonal]
  nlinarith [pi_hand_enclosure.1]

theorem positive_height_lower {u : ℝ} (hu : u∈Icc (outerDiagonal+1/2) (3/2)) :
    (89779/100000:ℝ)<positiveHeight u := by
  have hdom : ∀z∈Icc (outerDiagonal+1/2) (3/2),z∈LHeightBounds.heights := by
    intro z hz
    exact ⟨by linarith [hz.1,outer_endpoint_bounds.2.2.1],by linarith [hz.2]⟩
  have hc : ConcaveOn ℝ (Icc (outerDiagonal+1/2) (3/2)) positiveHeight :=
    concave_of_deriv2 (fun z hz => positiveHeight_hasDerivAt (hdom z hz))
      (fun z hz => positiveHeightD_hasDerivAt (hdom z hz))
      (fun z hz => (LHeightBounds.second_negative_below (hdom z hz) (by linarith [hz.2])).le)
  exact concave_gt_of_endpoints hc hu positive_diagonal (by linarith [positive_zero])

lemma negative_join_value : (89793/100000:ℝ)<negativeHeight (81/50) := by
  have hr := root_cage (u := (81/50:ℝ))
    (l := (1136309816907/1000000000000:ℝ))
    (r := (284077454227/250000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  norm_num [negativeHeight,en,LPrimaryZero.e,gn,zn,LHeight,HeightLabel.eval,Q0]
  nlinarith [hr.2,pi_hand_enclosure.1]

lemma negative_join_derivatives :
    negativeHeightD (81/50)<0 ∧ (33/100:ℝ)<negativeHeightDD (81/50) := by
  have hu : (81/50:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
  have hr := root_cage (u := (81/50:ℝ))
    (l := (1136309816907/1000000000000:ℝ))
    (r := (284077454227/250000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  have hp := root_pos (LHeightBounds.domain hu)
  have h1 := LHeight.d1_mul (LHeightBounds.domain hu)
  have h2 := LHeight.d2_mul (LHeightBounds.domain hu)
  have h3l := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1136309816907/1000000000000) hr.1.le 3
  have h3u := pow_le_pow_left₀ hp.le hr.2.le 3
  have hv : LHeight.v=37437/25000 := rfl
  have hk : LHeight.k=94721/50000 := rfl
  have hw : LHeight.w=629979/100000 := rfl
  rw [hv,hk,hw] at h1 h2
  norm_num [Q0] at h1 h2
  constructor
  · have hh : LHeight.d1 (81/50)<(24/25:ℝ) := by
      apply (mul_lt_mul_iff_left₀ hp).mp
      nlinarith [hr.1,hr.2]
    dsimp [negativeHeightD,gn,zn]
    linarith
  · have hh : (9/40:ℝ)<LHeight.d2 (81/50) := by
      apply (mul_lt_mul_iff_left₀ (pow_pos hp 3)).mp
      nlinarith
    dsimp [negativeHeightDD,zn]
    linarith

lemma negative_reference :
    (89779/100000:ℝ)<negativeHeight (41/25) ∧
    |negativeHeightD (41/25)|<1/625 := by
  have hu : (41/25:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
  have hr := root_cage (u := (41/25:ℝ))
    (l := (1107248842853/1000000000000:ℝ))
    (r := (553624421427/500000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  have hp := root_pos (LHeightBounds.domain hu)
  have h1 := LHeight.d1_mul (LHeightBounds.domain hu)
  have hv : LHeight.v=37437/25000 := rfl
  have hk : LHeight.k=94721/50000 := rfl
  have hw : LHeight.w=629979/100000 := rfl
  rw [hv,hk,hw] at h1
  norm_num [Q0] at h1
  constructor
  · norm_num [negativeHeight,en,LPrimaryZero.e,gn,zn,LHeight,HeightLabel.eval,Q0]
    nlinarith [hr.2,pi_hand_enclosure.1]
  · have hl : (48393/50000:ℝ)<LHeight.d1 (41/25) := by
      apply (mul_lt_mul_iff_left₀ hp).mp
      nlinarith [hr.1,hr.2]
    have hh : LHeight.d1 (41/25)<(24197/25000:ℝ) := by
      apply (mul_lt_mul_iff_left₀ hp).mp
      nlinarith [hr.1,hr.2]
    rw [abs_lt]
    dsimp [negativeHeightD,gn,zn]
    constructor <;> linarith

/-- A convex derivative ending nonpositive permits only a maximum
before the right endpoint, so the two endpoints control the interval. -/
private lemma r29_endpoint_minimum {f d : ℝ → ℝ} {l u x : ℝ}
    (hx : x∈Icc l u) (hd : ∀t∈Icc l u,HasDerivAt f (d t) t)
    (hc : ConcaveOn ℝ (Icc l u) (fun t => -d t)) (hu : d u≤0) :
    min (f l) (f u)≤f x := by
  by_cases hdx : d x≤0
  · have hm : AntitoneOn f (Icc x u) := by
      apply antiOn_of_hasDeriv_nonpos
      · exact fun t ht => (hd t ⟨hx.1.trans ht.1,ht.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => hd t ⟨hx.1.trans ht.1.le,ht.2.le⟩
      · intro t ht
        have hh := hc.min_le_of_mem_Icc hx ⟨hx.1.trans hx.2,le_rfl⟩
          (Ioo_subset_Icc_self ht)
        have hn : 0 ≤ min (-d x) (-d u) := le_min (by linarith) (by linarith)
        linarith
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)
  · have hm : MonotoneOn f (Icc l x) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact fun t ht => (hd t ⟨ht.1,ht.2.trans hx.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => hd t ⟨ht.1.le,ht.2.le.trans hx.2⟩
      · intro t ht
        by_contra! hdt
        have hh := hc.min_le_of_mem_Icc ⟨ht.1.le,ht.2.le.trans hx.2⟩
          ⟨hx.1.trans hx.2,le_rfl⟩ ⟨ht.2.le,hx.2⟩
        have hn : 0 ≤ min (-d t) (-d u) := le_min (by linarith) (by linarith)
        linarith
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)

lemma negative_lower_piece {u : ℝ} (hu : u∈Icc (3/2) (81/50)) :
    (4489/5000:ℝ)<negativeHeight u := by
  have hdom : ∀z∈Icc (3/2) (81/50),z∈LHeightBounds.heights :=
    fun z hz => ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hc : ConcaveOn ℝ (Icc (3/2) (81/50)) (fun z => -negativeHeightD z) :=
    concave_of_deriv2 (fun z hz => (negativeHeightD_hasDerivAt (hdom z hz)).neg)
      (fun z hz => (negativeHeightDD_hasDerivAt (hdom z hz)).neg)
      (fun z hz => neg_nonpos.mpr (LHeightBounds.third_positive (hdom z hz)).le)
  have hm := r29_endpoint_minimum hu
    (fun z hz => negativeHeight_hasDerivAt (hdom z hz)) hc negative_join_derivatives.1.le
  exact (lt_min negative_zero (by linarith [negative_join_value])).trans_le hm

lemma negative_upper_piece {u : ℝ} (hu : u∈Icc (81/50) (383/200)) :
    (44889/50000:ℝ)<negativeHeight u := by
  have hdom : ∀z∈Icc (81/50) (383/200),z∈LHeightBounds.heights :=
    fun z hz => ⟨by linarith [hz.1],hz.2⟩
  have hc : ∀z∈Icc (81/50) (383/200),(33/100:ℝ)≤negativeHeightDD z := by
    intro z hz
    have hm := LHeightBounds.second_monotone
      (show (81/50:ℝ)∈LHeightBounds.heights by norm_num [LHeightBounds.heights])
      (hdom z hz) hz.1
    have hj := negative_join_derivatives.2
    dsimp [negativeHeightDD] at *
    linarith
  have ht := curvature_tangent (f := negativeHeight) (d := negativeHeightD) (dd := negativeHeightDD)
    (κ := (33/100:ℝ)) hu (show (41/25:ℝ)∈Icc (81/50) (383/200) by norm_num)
    (fun z hz => negativeHeight_hasDerivAt (hdom z hz))
    (fun z hz => negativeHeightD_hasDerivAt (hdom z hz)) hc
  have hd := abs_lt.mp negative_reference.2
  have hp := mul_pos (show 0<negativeHeightD (41/25)+1/625 by linarith [hd.1])
    (show 0<(1/625:ℝ)-negativeHeightD (41/25) by linarith [hd.2])
  have hs := sq_nonneg ((33/100)*(u-41/25)+negativeHeightD (41/25))
  nlinarith [negative_reference.1]

theorem negative_height_lower {u : ℝ} (hu : u∈Icc (3/2) (383/200)) :
    (44889/50000:ℝ)<negativeHeight u := by
  by_cases he : u≤81/50
  · linarith [negative_lower_piece (show u∈Icc (3/2) (81/50) from ⟨hu.1,he⟩)]
  · exact negative_upper_piece ⟨by linarith,hu.2⟩

end SquaresInCircles.Eight.SecondWord.EdgeThreeAligned
