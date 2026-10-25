module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetPositive
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetJContact
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetLDiagonal
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.SameCycle

/-!
# Eight squares: every original opposite-sign mixed zero edge of the second word

J, P and L are the three literal core-to-outer
roles.  Exact reflection gives the reverse radial order.  The independent
original zero-owner theorem accounts for every original axis, including
weak ties, before invoking either secondary estimate.
-/

section
/-!
## The uniform L side-loss estimate

Complete one square in the angle derivative (`slope_lower`), integrate the resulting uniform
lower slope (`uniform_loss`), then use the single aligned tangent parabola (`aligned_tangent`).
The result is the side bound `side`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.LSide
open CommonQuarter CorePairGeometry Arithmetic

def n (B : ℝ) : ℝ := (13/12)*g 2-1-(g 2)^2*(B-1/2)^2/4
def K (B : ℝ) : ℝ :=
  9010079/10000000-(1/10000)*(B-1027/1250)+(1/4)*(B-1027/1250)^2+(273/500)*n B
def K₁ (B : ℝ) : ℝ :=
  -(1/10000)+(1/2)*(B-1027/1250)-(273/1000)*(g 2)^2*(B-1/2)

lemma slope_lower {B x : ℝ} (hx : x∈angles) :
    n B/(Real.cos x)^2≤boundary₁ 2 (7/12) B x := by
  have hden : 0<(Real.cos x)^2 := sq_pos_of_pos (by linarith [(cosine_bounds hx).1])
  have hn : n B≤(Real.sin x)^2-g 2*(B-1/2)*Real.sin x+g 2*((7/12:ℝ)+1/2)-1 := by
    dsimp [n]
    nlinarith [sq_nonneg (Real.sin x-g 2*(B-1/2)/2)]
  apply (div_le_div_iff₀ hden hden).2
  exact mul_le_mul_of_nonneg_right hn hden.le

lemma negative_late {B : ℝ} (hB : (1/2:ℝ)≤B) (hn : n B<0) : (21/25:ℝ)<B := by
  by_contra! hu
  have hs := pow_le_pow_left₀ (sub_nonneg.mpr hB)
    (show B-1/2≤(17/50:ℝ) by linarith) 2
  norm_num [n,g] at hn
  nlinarith

lemma nonnegative_case {B x : ℝ} (hB : B∈Icc (1/2:ℝ) outerDiagonal)
    (hx : x∈angles) (hn : 0≤n B) : (17953/20000:ℝ)<boundary 2 (7/12) B x := by
  have hm : MonotoneOn (boundary 2 (7/12) B) angles :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (boundary_hasDerivAt 2 (7/12) B ht).continuousAt.continuousWithinAt)
      (fun t ht => boundary_hasDerivAt 2 (7/12) B (Ioo_subset_Icc_self ht))
      (fun t ht => (div_nonneg hn (sq_nonneg (Real.cos t))).trans
        (slope_lower (Ioo_subset_Icc_self ht)))
  have hh := hm (by norm_num [angles,cap]) hx hx.1
  rw [boundary_zero] at hh
  linarith [L_aligned ⟨by linarith [hB.1],hB.2⟩]

lemma negative_slope {B x : ℝ} (hx : x∈angles) (hn : n B<0) :
    n B/(81/100)≤boundary₁ 2 (7/12) B x := by
  have hc := (cosine_bounds hx).2
  have hden : 0<(Real.cos x)^2 := by linarith
  have hh : n B/(81/100)≤n B/(Real.cos x)^2 := by
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<81/100) hden).2
    exact mul_le_mul_of_nonpos_left hc.le hn.le
  exact hh.trans (slope_lower hx)

lemma uniform_loss {B x : ℝ} (hx : x∈angles) (hn : n B<0) :
    aligned 2 B+(273/500)*n B<boundary 2 (7/12) B x := by
  have hd (t : ℝ) (ht : t∈angles) :
      HasDerivAt (fun y => boundary 2 (7/12) B y-(n B/(81/100))*y)
        (boundary₁ 2 (7/12) B t-n B/(81/100)) t := by
    have h := (boundary_hasDerivAt 2 (7/12) B ht).fun_sub
      ((hasDerivAt_id' (x:=t)).const_mul (n B/(81/100)))
    rw [mul_one] at h
    exact h
  have hm : MonotoneOn (fun y => boundary 2 (7/12) B y-(n B/(81/100))*y) angles :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hd t (Ioo_subset_Icc_self ht))
      (fun t ht => sub_nonneg.mpr (negative_slope (Ioo_subset_Icc_self ht) hn))
  have hh := hm (by norm_num [angles,cap]) hx hx.1
  simp only [mul_zero,sub_zero,boundary_zero] at hh
  have hx2 : x≤5519/12500 := hx.2
  have hcoef : x/(81/100)<(273/500:ℝ) := by linarith
  have hp := mul_lt_mul_of_neg_right hcoef hn
  linarith

lemma aligned_tangent {B : ℝ} (hB : B∈Icc (21/25:ℝ) outerDiagonal) :
    9010079/10000000-(1/10000)*(B-1027/1250)+(1/4)*(B-1027/1250)^2<aligned 2 B := by
  have ht := L_aligned_tangent ⟨by linarith [hB.1],hB.2⟩
  have hs := (abs_lt.mp References.L_minimum.2).1
  have hp := mul_pos (show 0<alignedD 2 (1027/1250)+1/10000 by linarith)
    (show 0<B-1027/1250 by linarith [hB.1])
  nlinarith [References.L_minimum.1]

lemma K_hasDerivAt (B : ℝ) : HasDerivAt K (K₁ B) B := by
  have hn : HasDerivAt n (-(g 2)^2*(B-1/2)/2) B := by
    have h : HasDerivAt n _ B :=
      (((((hasDerivAt_id' (x:=B)).sub_const (1/2)).fun_pow 2).const_mul
        ((g 2)^2)).div_const 4).const_sub ((13/12)*g 2-1)
    exact h.congr_deriv (by simp only [Nat.reduceSub,pow_one,Nat.cast_ofNat]; ring)
  have h : HasDerivAt K _ B :=
    (((((hasDerivAt_id' (x:=B)).sub_const (1027/1250)).const_mul (1/10000)).const_sub
      (9010079/10000000)).fun_add
        ((((hasDerivAt_id' (x:=B)).sub_const (1027/1250)).fun_pow 2).const_mul (1/4))).fun_add
          (hn.const_mul (273/500))
  exact h.congr_deriv (by simp only [K₁,Nat.reduceSub,pow_one,Nat.cast_ofNat]; ring)

lemma K_first_negative {B : ℝ} (hB : B∈Icc (21/25:ℝ) (9/10)) : K₁ B<0 := by
  norm_num [K₁,g]
  linarith [hB.2]

lemma K_lower {B : ℝ} (hB : B∈Icc (21/25:ℝ) (9/10)) : (17953/20000:ℝ)<K B := by
  have hm : AntitoneOn K (Icc (21/25:ℝ) (9/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun t _ => (K_hasDerivAt t).continuousAt.continuousWithinAt)
      (fun t _ => K_hasDerivAt t)
      (fun t ht => (K_first_negative (Ioo_subset_Icc_self ht)).le)
  have hh := hm hB (by norm_num) hB.2
  have he : (17953/20000:ℝ)<K (9/10) := by norm_num [K,n,g]
  exact he.trans_le hh

lemma boundary_lower {B x : ℝ} (hB : B∈Icc (1/2:ℝ) outerDiagonal) (hx : x∈angles) :
    (17953/20000:ℝ)<boundary 2 (7/12) B x := by
  by_cases hn : 0≤n B
  · exact nonnegative_case hB hx hn
  · have hneg : n B<0 := lt_of_not_ge hn
    have hlate := negative_late hB.1 hneg
    have ht := aligned_tangent ⟨hlate.le,hB.2⟩
    have hk := K_lower ⟨hlate.le,by linarith [hB.2,outer_endpoint_bounds.2.2.2]⟩
    have hl := uniform_loss hx hneg
    dsimp [K] at hk
    linarith

lemma side {x b : ℝ} (hx : x∈angles) (hb : b∈Icc (0:ℝ) (1/2))
    (hf : contact (7/12) b x≤outerDiagonal) : (17953/20000:ℝ)<sideCost 2 x b := by
  rw [side_as_boundary 2 hx]
  exact boundary_lower ⟨side_contact_lower hx hb,hf⟩ hx

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.LSide
end
end
end

section
/-!
## The full L negative target contact

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
end
end
end

section
/-!
## All three opposite mixed zero target-secondary families

This restores the original target after the
first-contact lower bound and then joins the two closed angle signs.
The physical radius, source point, target point, and weak owner are the
ones supplied to the theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target
open CommonQuarter CorePairGeometry Arithmetic

theorem negative_projection (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤-a*Real.sin x+b*Real.cos x+B) :
    (17953/20000:ℝ)< -x+c r+g r*b+(F r).outer B := by
  have hc : x∈angles := ⟨hx.1,(original_angle hs ht hx hm).le⟩
  have hcontact := original_contact hs ht hc hm
  have hrestore := original_cost r hs ht hc hm
  have hl : (17953/20000:ℝ)< -x+c r+g r*b+(F r).outer (contact a b x) := by
    fin_cases r
    · exact JContact.core hs hc hcontact.1.2
    · exact PContact.core hs hc hcontact.1.2
    · exact LContact.core hs hc hcontact.1.2
  exact hl.trans_le hrestore

theorem original (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 (-1) x) :
    (17953/20000:ℝ)<x+c r+g r*b+(F r).outer B := by
  by_cases hp : 0≤x
  · exact TargetPositive.original r hs ht ⟨hp,(abs_le.mp hx).2⟩ hm
  · have hx' : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have hsin : Real.sin x≤0 := by
      have hh := (positive_trig hx').2.2.1
      simpa only [Real.sin_neg,neg_nonneg] using hh
    have hw := signed_width hx
    rw [abs_of_nonpos hsin] at hw
    have hprojection : pairWidth x≤a*Real.sin x+b*Real.cos x+B := by
      norm_num [Eight.forwardMargin] at hm
      linarith
    rw [hw] at hprojection
    have hh := negative_projection r hs ht hx' (by
      simp only [Real.sin_neg,Real.cos_neg,mul_neg]
      linarith)
    simpa only [neg_neg] using hh

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

lemma zero_roles (i : Vertex) (hi : WordProblems.wrongWord .second i=0) :
    i=0 ∨ i=1 ∨ i=4 := by
  fin_cases i <;> simp [WordProblems.wrongWord] at hi ⊢

theorem original_core_row (r : Row) {kind : RadialKind} (hk : kind≠.outer)
    {a b A B x : ℝ} (hs : State kind a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) x) :
    (17953/20000:ℝ)<cost (role r) kind .outer true false a b A B x := by
  have hc : CoreState a b := by simpa [State,hk] using hs
  rw [literal r kind hk ht]
  rcases hj with rfl | rfl
  · exact Source.original r hc ht hx hm
  · exact Target.original r hc ht hx hm

theorem original_core {i : Vertex} (hi : WordProblems.wrongWord .second i=0)
    {kind : RadialKind} (hk : kind≠.outer)
    {a b A B x : ℝ} (hs : State kind a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) x) :
    threshold i<cost i kind .outer true false a b A B x := by
  rw [threshold_value]
  rcases zero_roles i hi with rfl | rfl | rfl
  · simpa [role] using original_core_row (0:Row) hk hs ht hx j hj hm
  · simpa [role] using original_core_row (1:Row) hk hs ht hx j hj hm
  · simpa [role] using original_core_row (2:Row) hk hs ht hx j hj hm

theorem original {i : Vertex} (hi : WordProblems.wrongWord .second i=0)
    {source target : RadialKind} (hmixed : Same.Mixed source target)
    {a b A B x : ℝ} (hs : State source a b) (ht : State target A B) (hx : |x|≤7/10)
    (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) x) :
    threshold i<cost i source target true false a b A B x := by
  rcases hmixed with ⟨rfl,hcore⟩ | ⟨hcore,rfl⟩
  · have ho : OuterState a b := by simpa [State] using hs
    have hir : WordProblems.wrongWord .second (reverseEdge i)=0 := by
      rcases zero_roles i hi with rfl | rfl | rfl <;>
        norm_num [WordProblems.wrongWord,reverseEdge]
    have hh : threshold (reverseEdge i)<cost (reverseEdge i) target .outer
        true false A B a b x := by
      rcases hj with rfl | rfl
      · exact original_core hir hcore ht ho hx 2 (Or.inr rfl)
          (by simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm)
      · exact original_core hir hcore ht ho hx 0 (Or.inl rfl)
          (by simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm)
    have he := cost_reflection i .outer target true false a b A B x
    norm_num at he
    rw [he,threshold_value] at hh
    simpa only [threshold_value] using hh
  · have ho : OuterState A B := by simpa [State] using ht
    exact original_core hi hcore hs ho hx j hj hm

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : Same.Mixed (C.kind i) (C.kind (next i)))
    (hsg : positiveOf C i≠positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hx : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hword : WordProblems.wrongWord .second i=0 := by simpa [hw] using hi
  have ha := actual_allowed C F hgap .second hw i
  have hsigns : positiveOf C i=true ∧ positiveOf C (next i)=false := by
    cases hs : positiveOf C i <;> cases ht : positiveOf C (next i) <;>
      simp_all [WordProblems.allowed]
  have haxis : j=0 ∨ j=2 := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hm := original_margin C F hgap i j howner
  have hh := original hword hmixed (actual_state C i) (actual_state C (next i)) hx j haxis
    (by simpa [hsigns.1,hsigns.2,WordProblems.sign] using hm)
  have he : cost i (C.kind i) (C.kind (next i)) true false
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (phaseValue F hgap i)=
      phaseValue F hgap i+wrongMarker C .second i-wrongMarker C .second (next i) := by
    simp only [cost,label,wrongMarker,hsigns.1,hsigns.2]
  rwa [he] at hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : Same.Mixed (C.kind i) (C.kind (next i)))
    (hsg : positiveOf C i≠positiveOf C (next i)) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hi hmixed hsg j howner

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite
end
end
end
