module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetCorner
public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetJDiagonal

/-!
# The full J negative target contact

Uncompiled source draft.  This follows §8: the side minimum is the
first feasible target diagonal, and corner concavity leaves the join,
the first feasible target diagonal, and the core diagonal.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.JContact
open CommonQuarter CorePairGeometry Arithmetic

lemma boundary_first_positive {x : ℝ} (hx : x∈angles) : boundary₁ 0 (7/12) outerDiagonal x>0 := by
  have hd := outer_endpoint_bounds
  have hsq : (outerDiagonal-1/2)^2<(2/5:ℝ)^2 := by
    nlinarith [hd.2.2.1,hd.2.2.2]
  have hdisc : (13/12)*g 0-1-(g 0)^2*(outerDiagonal-1/2)^2/4>0 := by
    norm_num [g]
    nlinarith
  have hnum : 0<(Real.sin x)^2-g 0*(outerDiagonal-1/2)*Real.sin x+
      g 0*((7/12:ℝ)+1/2)-1 := by
    nlinarith [sq_nonneg (Real.sin x-g 0*(outerDiagonal-1/2)/2)]
  exact div_pos hnum (sq_pos_of_pos (by linarith [(cosine_bounds hx).1]))

lemma boundary_lower {x : ℝ} (hx : x∈angles) : (17953/20000:ℝ)<boundary 0 (7/12) outerDiagonal x := by
  have hm : MonotoneOn (boundary 0 (7/12) outerDiagonal) angles :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (boundary_hasDerivAt 0 (7/12) outerDiagonal ht).continuousAt.continuousWithinAt)
      (fun t ht => boundary_hasDerivAt 0 (7/12) outerDiagonal (Ioo_subset_Icc_self ht))
      (fun t ht => (boundary_first_positive (Ioo_subset_Icc_self ht)).le)
  have hh := hm (by norm_num [angles,cap]) hx hx.1
  rw [boundary_zero] at hh
  linarith [J_aligned (show outerDiagonal∈Icc 0 outerDiagonal from
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩)]

lemma side {x b : ℝ} (hx : x∈angles) (hb : b∈Icc (0:ℝ) (1/2))
    (hf : contact (7/12) b x≤outerDiagonal) : (17953/20000:ℝ)<sideCost 0 x b := by
  let e := inverse (7/12) outerDiagonal x
  have he0 : 0≤e := inverse_side_nonnegative hx
  have heb : e≤b := inverse_le_of_contact hx hf
  have heq : contact (7/12) e x=outerDiagonal := contact_inverse (7/12) outerDiagonal hx
  have hdom {t : ℝ} (ht : t∈Icc e b) : contact (7/12) t x∈Shape.band := by
    apply side_contact_band hx ⟨he0.trans ht.1,ht.2.trans hb.2⟩
    have hm := side_contact_antitone hx ht.1
    rw [heq] at hm
    exact hm
  have hm : MonotoneOn (sideCost 0 x) (Icc e b) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (sideCost_hasDerivAt 0 x t (Shape.band_domain (hdom ht))).continuousAt.continuousWithinAt
    · exact fun t ht => sideCost_hasDerivAt 0 x t (Shape.band_domain (hdom (Ioo_subset_Icc_self ht)))
    · intro t ht
      have h1 := Shape.J_first_bounds (hdom (Ioo_subset_Icc_self ht))
      have hp := mul_le_mul_of_nonneg_left (Real.cos_le_one x)
        (show 0≤JLabel.d1 (contact (7/12) t x) by linarith [h1.1])
      norm_num [side₁,F,g]
      linarith [h1.2]
  have hh := hm ⟨le_rfl,heb⟩ ⟨heb,le_rfl⟩ heb
  change sideCost 0 x (inverse (7/12) outerDiagonal x)≤ sideCost 0 x b at hh
  rw [side_at_entry 0 hx] at hh
  exact (boundary_lower hx).trans_le hh

lemma first_corner {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (he : cornerB x b=outerDiagonal) : (17953/20000:ℝ)<cornerCost 0 x b := by
  have hg := (slope_bounds 0).1
  have hc : cornerCost 0 x b=-x+c 0+g 0*b+J outerDiagonal := by
    rw [cornerCost,he]
    rfl
  rw [hc]
  by_cases hs : x≤41/100
  · have hp := mul_le_mul_of_nonneg_left hb.1 hg.le
    linarith [BoundaryReferences.J_first.1]
  · have hh := Corner.inverse_monotone
      (show (41/100:ℝ)∈angles by norm_num [angles,cap]) hx (by linarith)
    have hbL := Corner.first_coordinate hx hb he
    have hp := mul_le_mul_of_nonneg_left
      (show (5249/10000:ℝ)≤b by linarith [BoundaryReferences.J_first.2.2]) hg.le
    linarith [BoundaryReferences.J_first.2.1,hx.2]

lemma corner {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (hf : cornerB x b≤outerDiagonal) : (17953/20000:ℝ)<cornerCost 0 x b := by
  apply Corner.endpoints 0 hx hb hf
  · exact fun t ht htf => (Corner.J_second_negative hx ht htf).le
  · intro hj
    have hcontact : contact (7/12) (1/2) x≤outerDiagonal := by
      simpa only [cornerB,MixedCorner.join] using hj
    exact side hx (by norm_num) hcontact
  · exact fun t ht he _ => first_corner hx ht he
  · exact JDiagonal.lower hx

lemma core {a b x : ℝ} (hs : CoreState a b) (hx : x∈angles)
    (hf : contact a b x≤outerDiagonal) :
    (17953/20000:ℝ)< -x+c 0+g 0*b+J (contact a b x) := by
  rcases hs with ⟨rfl,hb0,hb1⟩ | ⟨hb0,hba,hcircle⟩
  · exact side hx ⟨hb0,hb1⟩ hf
  · obtain ⟨hb,rfl⟩ := MixedCorner.actual hb0 hba hcircle
    exact corner hx hb hf

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.JContact
