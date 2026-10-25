module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoDiagonalReferences

/-!
# The entire diagonal-source lower contact

Before angle `2/5`, the increasing second derivative and negative final
slope force an endpoint minimum.  Afterwards its curvature exceeds
`3/10`, so the tangent parabola at angle `1/2` bounds the complete
physical tail.  The original contact endpoints are included.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.DiagonalSource

open CommonQuarter CorePairGeometry Arithmetic

lemma zero_value : (8977827/10000000:ℝ)<cost 0 := by
  have hz := domain_before four_domain (show (0:ℝ)∈Icc 0 (2/5) by norm_num)
  have hh := aligned_contact_lower diagonal_mem (domain_data hz).1
    (show TargetContact.B outerDiagonal 0=height 0 from rfl)
  simpa only [cost,sub_zero] using hh

lemma early_bound {x : ℝ} (hx : x∈Icc 0 (2/5)) :
    (8977827/10000000:ℝ)<cost x := by
  have hh := MinimumCalculus.endpoint_minimum hx
    (fun t ht => cost_hasDerivAt (domain_before four_domain ht))
    (fun t ht => first_hasDerivAt (domain_before four_domain ht))
    (fun t ht => second_hasDerivAt (domain_before four_domain ht))
    (fun t ht => (third_positive (domain_before four_domain ht)).le)
    four_first
  exact (lt_min zero_value (by linarith [four_value])).trans_le hh

lemma tail_bound {x : ℝ} (hx : Domain x) (hfour : 2/5≤x) :
    (2253/2500:ℝ)<cost x := by
  let u : ℝ := max x (1/2)
  have hu : Domain u := by
    by_cases hh : x≤1/2
    · simpa only [u,max_eq_right hh] using five_domain
    · simpa only [u,max_eq_left (le_of_not_ge hh)] using hx
  have hxu : x≤u := le_max_left _ _
  have h5u : (1/2:ℝ)≤u := le_max_right _ _
  have hdom {t : ℝ} (ht : t∈Icc (2/5) u) : Domain t :=
    domain_before hu ⟨by linarith [ht.1],ht.2⟩
  have hcurvature {t : ℝ} (ht : t∈Icc (2/5) u) : (3/10:ℝ)≤ second t := by
    have hm := second_monotone hu
      (show (2/5:ℝ)∈Icc 0 u from ⟨by norm_num,by linarith [h5u]⟩)
      ⟨by linarith [ht.1],ht.2⟩ ht.1
    exact four_second.le.trans hm
  have htan := curvature_tangent (κ := (3/10:ℝ))
    (show x∈Icc (2/5) u from ⟨hfour,hxu⟩)
    (show (1/2:ℝ)∈Icc (2/5) u from ⟨by norm_num,h5u⟩)
    (fun t ht => cost_hasDerivAt (hdom ht))
    (fun t ht => first_hasDerivAt (hdom ht))
    (fun t ht => hcurvature ht)
  have hfirst : (first (1/2))^2<(11/500:ℝ)^2 := by
    nlinarith [(abs_lt.mp five_first).1,(abs_lt.mp five_first).2]
  have hsq := sq_nonneg ((3/10:ℝ)*(x-1/2)+first (1/2))
  nlinarith [five_value]

theorem cost_lower {x : ℝ} (hx : Domain x) :
    (8977827/10000000:ℝ)<cost x := by
  rcases le_total x (2/5) with h|h
  · exact early_bound ⟨hx.1.1,h⟩
  · linarith [tail_bound hx h]

theorem original_contact {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : TargetContact.B outerDiagonal x=B) :
    (8977827/10000000:ℝ)<value outerDiagonal B (Real.pi/2-x) := by
  have hd : Domain x := ⟨hx,by change TargetContact.B outerDiagonal x≤outerDiagonal; rw [hc]; exact hB.2⟩
  have hh := cost_lower hd
  simpa only [cost,height,hc] using hh

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.DiagonalSource
