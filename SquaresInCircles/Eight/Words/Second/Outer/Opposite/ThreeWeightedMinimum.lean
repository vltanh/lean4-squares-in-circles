module

public import Mathlib.Tactic
public import SquaresInCircles.Common.Analysis

/-!
# Eight squares: minimum calculus in an increasing explicit parameter

The positive weight is the derivative of the coordinate being used
to measure curvature.  These statements avoid differentiating any
chosen inverse function.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.WeightedMinimum

lemma tangent {f d dd g w : ℝ→ℝ} {l u x t κ : ℝ}
    (hx : x∈Icc l u) (ht : t∈Icc l u)
    (hf : ∀ y∈Icc l u, HasDerivAt f (d y*w y) y)
    (hd : ∀ y∈Icc l u, HasDerivAt d (dd y*w y) y)
    (hg : ∀ y∈Icc l u, HasDerivAt g (w y) y)
    (hw : ∀ y∈Icc l u, 0≤w y) (hdd : ∀ y∈Icc l u, κ≤dd y) :
    f t+d t*(g x-g t)+κ/2*(g x-g t)^2≤f x := by
  let H : ℝ→ℝ := fun y => d y-κ*g y
  have hH {y : ℝ} (hy : y∈Icc l u) : HasDerivAt H ((dd y-κ)*w y) y := by
    have h : HasDerivAt H (dd y*w y-κ*w y) y := (hd y hy).sub ((hg y hy).const_mul κ)
    convert h using 1
    ring
  have hmono : MonotoneOn H (Icc l u) :=
    monoOn_of_hasDeriv_nonneg (fun y hy => (hH hy).continuousAt.continuousWithinAt)
      (fun y hy => hH (Ioo_subset_Icc_self hy))
      (fun y hy => mul_nonneg (sub_nonneg.mpr (hdd y (Ioo_subset_Icc_self hy)))
        (hw y (Ioo_subset_Icc_self hy)))
  let F : ℝ→ℝ := fun y => f y-d t*g y-κ/2*(g y-g t)^2
  have hF {y : ℝ} (hy : y∈Icc l u) : HasDerivAt F ((H y-H t)*w y) y := by
    have hsq : HasDerivAt (fun z => (g z-g t)^2) (2*(g y-g t)*w y) y := by
      convert ((hg y hy).sub_const (g t)).fun_pow 2 using 1
      norm_num
    have h : HasDerivAt F (d y*w y-d t*w y-κ/2*(2*(g y-g t)*w y)) y :=
      ((hf y hy).sub ((hg y hy).const_mul (d t))).sub (hsq.const_mul (κ/2))
    convert h using 1
    simp only [H]
    ring
  have hFt : F t≤F x := by
    rcases le_total t x with htx | hxt
    · have hdom {y : ℝ} (hy : y∈Icc t x) : y∈Icc l u :=
        ⟨ht.1.trans hy.1,hy.2.trans hx.2⟩
      have hm : MonotoneOn F (Icc t x) :=
        monoOn_of_hasDeriv_nonneg (fun y hy => (hF (hdom hy)).continuousAt.continuousWithinAt)
          (fun y hy => hF (hdom (Ioo_subset_Icc_self hy)))
          (fun y hy => mul_nonneg
            (sub_nonneg.mpr (hmono ht (hdom (Ioo_subset_Icc_self hy)) hy.1.le))
            (hw y (hdom (Ioo_subset_Icc_self hy))))
      exact hm ⟨le_rfl,htx⟩ ⟨htx,le_rfl⟩ htx
    · have hdom {y : ℝ} (hy : y∈Icc x t) : y∈Icc l u :=
        ⟨hx.1.trans hy.1,hy.2.trans ht.2⟩
      have hm : AntitoneOn F (Icc x t) :=
        antiOn_of_hasDeriv_nonpos (fun y hy => (hF (hdom hy)).continuousAt.continuousWithinAt)
          (fun y hy => hF (hdom (Ioo_subset_Icc_self hy)))
          (fun y hy => mul_nonpos_of_nonpos_of_nonneg
            (sub_nonpos.mpr (hmono (hdom (Ioo_subset_Icc_self hy)) ht hy.2.le))
            (hw y (hdom (Ioo_subset_Icc_self hy))))
      exact hm ⟨le_rfl,hxt⟩ ⟨hxt,le_rfl⟩ hxt
  dsimp [F] at hFt
  linarith

lemma endpoint {f d dd w : ℝ→ℝ} {l u x : ℝ} (hx : x∈Icc l u)
    (hf : ∀ y∈Icc l u, HasDerivAt f (d y*w y) y)
    (hd : ∀ y∈Icc l u, HasDerivAt d (dd y*w y) y)
    (hw : ∀ y∈Icc l u, 0≤w y) (hdd : AntitoneOn dd (Icc l u))
    (hleft : 0<d l) : min (f l) (f u)≤f x := by
  have hl : l∈Icc l u := ⟨le_rfl,hx.1.trans hx.2⟩
  have hu : u∈Icc l u := ⟨hx.1.trans hx.2,le_rfl⟩
  by_cases hxpos : 0≤d x
  · have hsign {y : ℝ} (hy : y∈Icc l x) : 0≤d y := by
      have hy' : y∈Icc l u := ⟨hy.1,hy.2.trans hx.2⟩
      by_cases hcurv : 0≤dd y
      · have hdom {z : ℝ} (hz : z∈Icc l y) : z∈Icc l u :=
          ⟨hz.1,(hz.2.trans hy.2).trans hx.2⟩
        have hm : MonotoneOn d (Icc l y) :=
          monoOn_of_hasDeriv_nonneg (fun z hz => (hd z (hdom hz)).continuousAt.continuousWithinAt)
            (fun z hz => hd z (hdom (Ioo_subset_Icc_self hz)))
            (fun z hz => mul_nonneg
              (hcurv.trans (hdd (hdom (Ioo_subset_Icc_self hz)) hy' hz.2.le))
              (hw z (hdom (Ioo_subset_Icc_self hz))))
        exact hleft.le.trans (hm ⟨le_rfl,hy.1⟩ ⟨hy.1,le_rfl⟩ hy.1)
      · have hcurv' : dd y≤0 := (lt_of_not_ge hcurv).le
        have hdom {z : ℝ} (hz : z∈Icc y x) : z∈Icc l u :=
          ⟨hy.1.trans hz.1,hz.2.trans hx.2⟩
        have hm : AntitoneOn d (Icc y x) :=
          antiOn_of_hasDeriv_nonpos (fun z hz => (hd z (hdom hz)).continuousAt.continuousWithinAt)
            (fun z hz => hd z (hdom (Ioo_subset_Icc_self hz)))
            (fun z hz => mul_nonpos_of_nonpos_of_nonneg
              ((hdd hy' (hdom (Ioo_subset_Icc_self hz)) hz.1.le).trans hcurv')
              (hw z (hdom (Ioo_subset_Icc_self hz))))
        exact hxpos.trans (hm ⟨le_rfl,hy.2⟩ ⟨hy.2,le_rfl⟩ hy.2)
    have hdom {y : ℝ} (hy : y∈Icc l x) : y∈Icc l u := ⟨hy.1,hy.2.trans hx.2⟩
    have hm : MonotoneOn f (Icc l x) :=
      monoOn_of_hasDeriv_nonneg (fun y hy => (hf y (hdom hy)).continuousAt.continuousWithinAt)
        (fun y hy => hf y (hdom (Ioo_subset_Icc_self hy)))
        (fun y hy => mul_nonneg (hsign (Ioo_subset_Icc_self hy))
          (hw y (hdom (Ioo_subset_Icc_self hy))))
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)
  · have hxneg : d x<0 := lt_of_not_ge hxpos
    have hcurv : dd x<0 := by
      by_contra hn
      have hc : 0≤dd x := le_of_not_gt hn
      have hdom {y : ℝ} (hy : y∈Icc l x) : y∈Icc l u := ⟨hy.1,hy.2.trans hx.2⟩
      have hm : MonotoneOn d (Icc l x) :=
        monoOn_of_hasDeriv_nonneg (fun y hy => (hd y (hdom hy)).continuousAt.continuousWithinAt)
          (fun y hy => hd y (hdom (Ioo_subset_Icc_self hy)))
          (fun y hy => mul_nonneg
            (hc.trans (hdd (hdom (Ioo_subset_Icc_self hy)) hx hy.2.le))
            (hw y (hdom (Ioo_subset_Icc_self hy))))
      have hh := hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1
      linarith
    have hdom {y : ℝ} (hy : y∈Icc x u) : y∈Icc l u := ⟨hx.1.trans hy.1,hy.2⟩
    have hdanti : AntitoneOn d (Icc x u) :=
      antiOn_of_hasDeriv_nonpos (fun y hy => (hd y (hdom hy)).continuousAt.continuousWithinAt)
        (fun y hy => hd y (hdom (Ioo_subset_Icc_self hy)))
        (fun y hy => mul_nonpos_of_nonpos_of_nonneg
          ((hdd hx (hdom (Ioo_subset_Icc_self hy)) hy.1.le).trans hcurv.le)
          (hw y (hdom (Ioo_subset_Icc_self hy))))
    have hfanti : AntitoneOn f (Icc x u) :=
      antiOn_of_hasDeriv_nonpos (fun y hy => (hf y (hdom hy)).continuousAt.continuousWithinAt)
        (fun y hy => hf y (hdom (Ioo_subset_Icc_self hy)))
        (fun y hy => mul_nonpos_of_nonpos_of_nonneg
          ((hdanti ⟨le_rfl,hx.2⟩ (Ioo_subset_Icc_self hy) hy.1.le).trans hxneg.le)
          (hw y (hdom (Ioo_subset_Icc_self hy))))
    exact (min_le_right _ _).trans (hfanti ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)

end SquaresInCircles.Eight.SecondWord.OppositeThree.WeightedMinimum
