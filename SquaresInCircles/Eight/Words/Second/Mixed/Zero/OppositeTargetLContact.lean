module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetBoundaryReferences
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetCorner
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetLDiagonal
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetLSide

/-!
# Eight squares: the full L negative target contact

The first feasible corner follows §10.3,
starting at the written `.377` comparison.  Corner concavity then
joins that endpoint to the full side and diagonal bounds.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.LContact
open CommonQuarter CorePairGeometry Arithmetic

lemma sine_monotone : MonotoneOn Real.sin angles :=
  monoOn_of_hasDeriv_nonneg
    (fun t _ => (Real.hasDerivAt_sin t).continuousAt.continuousWithinAt)
    (fun t _ => Real.hasDerivAt_sin t)
    (fun t ht => by linarith [(cosine_bounds (Ioo_subset_Icc_self ht)).1])

lemma entry_angle {x : ℝ} (hx : x∈angles) (hj : outerDiagonal<cornerB x (1/2)) :
    (377/1000:ℝ)<x := by
  by_contra! he
  have hm := sine_monotone hx
    (show (377/1000:ℝ)∈angles by norm_num [angles,cap]) he
  rw [cornerB_join] at hj
  linarith [BoundaryReferences.L_first.2.2.2]

lemma boundary_first_positive {x : ℝ} (hx : x∈Icc (377/1000:ℝ) cap) :
    0<boundary₁ 2 CoreAngleEndpoint.diagonal outerDiagonal x := by
  have ha : x∈angles := ⟨by linarith [hx.1],hx.2⟩
  have hm := sine_monotone
    (show (377/1000:ℝ)∈angles by norm_num [angles,cap]) ha hx.1
  have hg : g 2*(outerDiagonal-1/2)<(2/5:ℝ) := by
    norm_num [g]
    linarith [outer_endpoint_bounds.2.2.2]
  have hp := mul_nonneg (sub_nonneg.mpr hm)
    (show 0≤Real.sin x+Real.sin (377/1000)-g 2*(outerDiagonal-1/2) by
      linarith [BoundaryReferences.L_first.2.2.1])
  have hn : 0<(Real.sin x)^2-g 2*(outerDiagonal-1/2)*Real.sin x+
      g 2*(CoreAngleEndpoint.diagonal+1/2)-1 := by
    nlinarith [BoundaryReferences.L_first.2.1]
  exact div_pos hn (sq_pos_of_pos (by linarith [(cosine_bounds ha).1]))

lemma boundary_lower {x : ℝ} (hx : x∈Icc (377/1000:ℝ) cap) :
    (17953/20000:ℝ)<boundary 2 CoreAngleEndpoint.diagonal outerDiagonal x := by
  have ha {t : ℝ} (ht : t∈Icc (377/1000:ℝ) cap) : t∈angles :=
    ⟨by linarith [ht.1],ht.2⟩
  have hm : MonotoneOn (boundary 2 CoreAngleEndpoint.diagonal outerDiagonal)
      (Icc (377/1000:ℝ) cap) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (boundary_hasDerivAt 2 CoreAngleEndpoint.diagonal outerDiagonal
        (ha ht)).continuousAt.continuousWithinAt)
      (fun t ht => boundary_hasDerivAt 2 CoreAngleEndpoint.diagonal outerDiagonal
        (ha (Ioo_subset_Icc_self ht)))
      (fun t ht => (boundary_first_positive (Ioo_subset_Icc_self ht)).le)
  have hh := hm (by norm_num [cap]) hx hx.1
  linarith [BoundaryReferences.L_first.1]

lemma first_corner {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (he : cornerB x b=outerDiagonal) (hj : outerDiagonal<cornerB x (1/2)) :
    (17953/20000:ℝ)<cornerCost 2 x b := by
  have hangle := entry_angle hx hj
  have hbL := Corner.first_coordinate hx hb he
  have hp := mul_le_mul_of_nonneg_left hbL (slope_bounds 2).1.le
  have hl := boundary_lower ⟨hangle.le,hx.2⟩
  dsimp [boundary] at hl
  rw [cornerCost,he]
  linarith

lemma corner {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (hf : cornerB x b≤outerDiagonal) : (17953/20000:ℝ)<cornerCost 2 x b := by
  apply Corner.endpoints 2 hx hb hf
  · exact fun t ht htf => (Corner.L_second_negative hx ht htf).le
  · intro hj
    have hcontact : contact (7/12) (1/2) x≤outerDiagonal := by
      simpa only [cornerB,MixedCorner.join] using hj
    exact LSide.side hx (by norm_num) hcontact
  · exact fun t ht he hj => first_corner hx ht he hj
  · exact LDiagonal.lower hx

lemma core {a b x : ℝ} (hs : CoreState a b) (hx : x∈angles)
    (hf : contact a b x≤outerDiagonal) :
    (17953/20000:ℝ)< -x+c 2+g 2*b+L (contact a b x) := by
  rcases hs with ⟨rfl,hb0,hb1⟩ | ⟨hb0,hba,hcircle⟩
  · exact LSide.side hx ⟨hb0,hb1⟩ hf
  · obtain ⟨hb,rfl⟩ := MixedCorner.actual hb0 hba hcircle
    exact corner hx hb hf

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.LContact
