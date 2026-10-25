module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreThreeZeroCurve
public import SquaresInCircles.Eight.Words.Second.Mixed.TSmallEnvelope

/-!
# Eight squares: the complete primary zero-boundary slope comparison

The product of the primary label slope and sine decreases on the
entire contact interval. Its terminal lower bound makes the relaxed
contact cost decrease in the original transverse coordinate up to
the zero boundary.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore.Zero
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def product (φ : ℝ) : ℝ := TPrimaryLabel.d1 (a φ)*Real.sin φ

lemma product_hasDerivAt {φ : ℝ} (hφ : φ∈angles) :
    HasDerivAt product (-TPrimaryLabel.d2 (a φ)*v φ*Real.sin φ+
      TPrimaryLabel.d1 (a φ)*Real.cos φ) φ := by
  have hD := TPrimaryLabel.d1_hasDerivAt
    (primary_domain (NegativeTwo.primary_mem (physical hφ)))
  have hc0 := hD.comp φ (a_hasDerivAt φ)
  have hc : HasDerivAt (fun x => TPrimaryLabel.d1 (a x)) (TPrimaryLabel.d2 (a φ)*-v φ) φ := hc0
  have h := hc.mul (Real.hasDerivAt_sin φ)
  exact h.congr_deriv (by ring)

lemma product_antitone : AntitoneOn product angles := by
  apply antiOn_of_hasDeriv_nonpos
    (fun φ hφ => (product_hasDerivAt hφ).continuousAt.continuousWithinAt)
    (fun φ hφ => product_hasDerivAt (Ioo_subset_Icc_self hφ))
  intro φ hφ
  have h := Ioo_subset_Icc_self hφ
  have hg := primary_growth (primary_mem h)
  have ht := trig h
  have hv := harmonic_bounds h
  have hvs : (7037/10000:ℝ)≤v φ*Real.sin φ := by
    have hh := mul_le_mul hv.2.2.1.le ht.1.le (by norm_num : (0:ℝ)≤227/250)
      (by linarith [hv.2.2.1] : 0≤v φ)
    linarith
  have hp := mul_lt_mul_of_pos_right hg.2 (by linarith : 0<v φ*Real.sin φ)
  have hq := mul_neg_of_pos_of_neg (show 0<TPrimaryLabel.d1 (a φ) by linarith [hg.1])
    (show Real.cos φ-2*(v φ*Real.sin φ)<0 by linarith [ht.2.2.2])
  nlinarith

lemma product_lower {φ : ℝ} (hφ : φ∈angles) : g<product φ := by
  have he : (7/5:ℝ)∈angles := by norm_num [angles]
  have hm := product_antitone hφ he hφ.2
  have hg := primary_growth (primary_mem he)
  have hp := mul_le_mul hg.1.le PrimaryZero.terminal_trig.1
    (by norm_num : (0:ℝ)≤123181215/125000000)
    (by linarith [hg.1] : 0≤TPrimaryLabel.d1 (a (7/5)))
  dsimp [product,g] at *
  linarith

def contactD (φ y : ℝ) : ℝ := g*ratio y/Real.sin φ-TLabel.d1 y

lemma contact_hasDerivAt {φ y : ℝ} (_hφ : φ∈angles) (hy : y∈Icc 0 outerDiagonal) :
    HasDerivAt (fun y => primaryContact y φ) (contactD φ y) y := by
  have hT : HasDerivAt T (TLabel.d1 y) y := TLabel.outer_hasDerivAt (outer_domain hy)
  have hd := ((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hy)).sub_const (1/2)).sub_const
    ((13/12)*Real.cos φ)).div_const (Real.sin φ)).sub_const (1/2)
  have h := (hT.const_sub (φ-c)).sub (hd.const_mul g)
  exact h.congr_deriv (by simp only [contactD]; ring)

lemma contactD_monotone {φ : ℝ} (hφ : φ∈angles) :
    MonotoneOn (contactD φ) (Icc (0:ℝ) (b φ)) := by
  have hdom {y : ℝ} (hy : y∈Icc (0:ℝ) (b φ)) : y∈Icc 0 outerDiagonal :=
    ⟨hy.1,hy.2.trans (NegativeTwo.source_mem (physical hφ)).2⟩
  have hd {y : ℝ} (hy : y∈Icc (0:ℝ) (b φ)) :
      HasDerivAt (contactD φ) (g*ratioD y/Real.sin φ-TLabel.d2 y) y := by
    have h := (((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (hdom hy))).const_mul
      g).div_const (Real.sin φ)).sub (TLabel.d1_hasDerivAt (outer_domain (hdom hy)))
    exact h
  apply monoOn_of_hasDeriv_nonneg (fun y hy => (hd hy).continuousAt.continuousWithinAt)
    (fun y hy => hd (Ioo_subset_Icc_self hy))
  intro y hy
  have hr := ShortOuterOne.SameContact.ratioD_pos (outer_domain (hdom (Ioo_subset_Icc_self hy)))
  have hT := MixedTSmall.concave_second
    (show y∈Icc (0:ℝ) (3/5) from ⟨hy.1.le,hy.2.le.trans (source_mem hφ).2⟩)
  have hp := div_pos (mul_pos (show 0<g by norm_num [g]) hr)
    (show 0<Real.sin φ by linarith [(trig hφ).1])
  linarith

lemma contactD_boundary {φ : ℝ} (hφ : φ∈angles) : contactD φ (b φ)<0 := by
  have hs := physical hφ
  have ht := trig hφ
  have hr : 0<ratio (b φ) := by
    dsimp [ratio]
    rw [(ShortOuterOne.SameContact.actual_arc hs).1]
    exact div_pos (by linarith [hs.1]) (by linarith [hs.1,hs.2.1])
  have he := NegativeThree.primary_first_exchange hs
  have hd : g/Real.sin φ<TPrimaryLabel.d1 (a φ) :=
    (div_lt_iff₀ (show 0<Real.sin φ by linarith [ht.1])).2 (product_lower hφ)
  have hp := mul_lt_mul_of_pos_right hd hr
  have hq : g*ratio (b φ)/Real.sin φ=g/Real.sin φ*ratio (b φ) := by ring
  dsimp only [contactD]
  rw [←he,hq]
  linarith

lemma contact_antitone {φ : ℝ} (hφ : φ∈angles) :
    AntitoneOn (fun y => primaryContact y φ) (Icc (0:ℝ) (b φ)) := by
  have hdom {y : ℝ} (hy : y∈Icc (0:ℝ) (b φ)) : y∈Icc 0 outerDiagonal :=
    ⟨hy.1,hy.2.trans (NegativeTwo.source_mem (physical hφ)).2⟩
  apply antiOn_of_hasDeriv_nonpos
    (fun y hy => (contact_hasDerivAt hφ (hdom hy)).continuousAt.continuousWithinAt)
    (fun y hy => contact_hasDerivAt hφ (hdom (Ioo_subset_Icc_self hy)))
  intro y hy
  have hm := contactD_monotone hφ (Ioo_subset_Icc_self hy)
    (show b φ∈Icc (0:ℝ) (b φ) from ⟨(source_mem hφ).1,le_rfl⟩) hy.2.le
  exact hm.trans (contactD_boundary hφ).le

lemma boundary_identity {φ : ℝ} (hφ : φ∈angles) : primaryContact (b φ) φ=K φ := by
  have hs := physical hφ
  have he := (ShortOuterOne.SameContact.actual_arc hs).1
  have hp : primaryCut (a φ) φ=0 := by
    dsimp [primaryCut,MixedTwo.PositiveCore.primaryCut,a,U,PrimaryZero.U,PrimaryZero.m]
    field_simp [ne_of_gt (show 0<Real.sin φ by linarith [(trig hφ).1])]
    ring
  dsimp [primaryContact]
  rw [he,hp,cost_eq hφ]
  ring

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore.Zero
