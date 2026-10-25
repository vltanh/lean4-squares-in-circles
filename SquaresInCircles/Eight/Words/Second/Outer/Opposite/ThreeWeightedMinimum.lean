module

public import Mathlib.Tactic
public import SquaresInCircles.Common.Analysis
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerCriticalRootReferences

/-!
# Eight squares: minimum calculus in an increasing explicit parameter

The positive weight is the derivative of the coordinate being used
to measure curvature.  These statements avoid differentiating any
chosen inverse function.
-/

section
/-!
## The actual curved exit of the reverse critical contact

The exit is where the recovered primary height equals the free
coordinate plus one.  Its marker is strictly decreasing on the whole
continued target interval, so every physical critical point occurs
before this aligned exit.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open LowerInverse LowerEnvelope

def exitMarker (B : ℝ) : ℝ := height B-B-3/2

lemma exitMarker_hasDerivAt {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    HasDerivAt exitMarker (-D B-1) B :=
  ((height_hasDerivAt hB).sub (hasDerivAt_id B)).sub_const (3/2)

lemma exitMarker_strictAnti : StrictAntiOn exitMarker (Icc (3/100) (3/20)) := by
  have hm : StrictMonoOn (fun B => -exitMarker B) (Icc (3/100) (3/20)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    · intro B hB
      exact (exitMarker_hasDerivAt hB).neg.continuousAt.continuousWithinAt
    · intro B hB
      exact (exitMarker_hasDerivAt (interior_subset hB)).neg.hasDerivWithinAt
    · intro B hB
      have hh := D_positive (mem_short (interior_subset hB))
      linarith
  intro B hB C hC hBC
  have hh := hm hB hC hBC
  linarith

lemma half_before_end : halfPoint<endPoint := by
  by_contra hn
  have hh := source_monotone end_domain.1 half_domain.1 (le_of_not_gt hn)
  rw [end_source,half_source] at hh
  norm_num at hh

lemma half_marker_positive : 0<exitMarker halfPoint := by
  have hu := (LowerGeometry.middle_U (by norm_num : (1/2:ℝ)∈Icc (2/5) (1/2))).1
  have he : height halfPoint=U (1/2) := by rw [←source_U half_domain.1,half_source]
  dsimp [exitMarker]
  rw [he]
  linarith [half_domain.1.2]

lemma end_marker_negative : exitMarker endPoint<0 := by
  by_contra hn
  have hm : 0≤exitMarker endPoint := le_of_not_gt hn
  have hu := source_U end_domain.1
  have hd : LowerContact.Domain endPoint (source endPoint) := by
    refine ⟨mem_outer end_domain.1,source_domain end_domain,?_⟩
    dsimp [exitMarker] at hm
    dsimp [U] at hu
    linarith
  have hv := LowerContact.physical_speed hd
  change W (source endPoint)≤LowerInverse.speed (z endPoint) (source endPoint) at hv
  rw [critical_speed end_domain.1,end_source] at hv
  norm_num [W] at hv
  have hp := p_positive (mem_outer end_domain.1)
  have hpl := (label_bounds end_domain.1).1
  have hh : 11/10*p endPoint≤1 := by
    have := mul_le_mul_of_nonneg_right hv hp.le
    rwa [inv_mul_cancel₀ hp.ne'] at this
  linarith

lemma exists_exit : ∃ B, B∈Icc halfPoint endPoint ∧ exitMarker B=0 := by
  have hdom {B : ℝ} (hB : B∈Icc halfPoint endPoint) : Domain B :=
    domain_between half_domain end_domain hB
  have hc : ContinuousOn (fun B => -exitMarker B) (Icc halfPoint endPoint) :=
    fun B hB => (exitMarker_hasDerivAt (hdom hB).1).neg.continuousAt.continuousWithinAt
  obtain ⟨B,hB,he⟩ := intermediate_value_Icc half_before_end.le hc
    (show (0:ℝ)∈Icc (-exitMarker halfPoint) (-exitMarker endPoint) from
      ⟨by linarith [half_marker_positive],by linarith [end_marker_negative]⟩)
  exact ⟨B,hB,by linarith⟩

def exitPoint : ℝ := Classical.choose exists_exit
lemma exit_mem : exitPoint∈Icc halfPoint endPoint := (Classical.choose_spec exists_exit).1
lemma exit_zero : exitMarker exitPoint=0 := (Classical.choose_spec exists_exit).2
lemma exit_domain : Domain exitPoint := domain_between half_domain end_domain exit_mem

lemma physical_before_exit {B : ℝ} (hB : Domain B) (hp : B≤arc (source B)-1) : B≤exitPoint := by
  have hm : 0≤exitMarker B := by
    have hu := source_U hB.1
    dsimp [U] at hu
    dsimp [exitMarker]
    linarith
  by_contra hn
  have hh := exitMarker_strictAnti exit_domain.1 hB.1 (lt_of_not_ge hn)
  rw [exit_zero] at hh
  linarith

lemma exit_aligned : exitPoint=arc (source exitPoint)-1 := by
  have hu := source_U exit_domain.1
  have he := exit_zero
  dsimp [U] at hu
  dsimp [exitMarker] at he
  linarith

lemma exit_value : (44889/50000:ℝ)<cost exitPoint := by
  have hd : LowerContact.Domain exitPoint (source exitPoint) :=
    ⟨mem_outer exit_domain.1,source_domain exit_domain,exit_aligned.le⟩
  exact LowerContact.aligned_lower true hd exit_aligned

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
end
end
end

section
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
end
end
end
