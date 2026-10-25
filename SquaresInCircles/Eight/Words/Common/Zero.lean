module

public import SquaresInCircles.Eight.Words.Common.ZeroEndpoint
public import SquaresInCircles.Eight.Words.Common.ZeroPrimary
public import SquaresInCircles.Eight.Words.Common.ZeroSame

/-!
# Eight squares: the common-label bound for a zero quarter increment

An edge with quarter increment zero has cost above `391/400` for each of its four weak owners
(`zero_cost`). The source-secondary owner is split by the signs of the two squares
(`zero_secondary_cost`); the impossible negative-to-positive sign uses the physical ray gap.
Reflection and reversal keep that same gap and move the target owners to the source-owner
formulas. `actual_zero` applies this to an edge of the boundary cycle with its frame lift.
-/

section
/-!
## All positive-to-negative source-secondary zero-quarter contacts

The core/outer and outer/outer cases use the two complete endpoint
supports. The reverse mixed order retains its original separator; on the
negative half that separator forces an angle below `1/2`, after which the
core-weight support is concave with ample reserve at both endpoints.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

lemma positive_core_support {l x : ℝ} (hl : 0≤l ∧ l≤6/5)
    (hx : x∈Icc 0 (7/10)) :
    l≤x+l*pairWidth x-l*(7/12)*Real.sin x := by
  have ht := positive_trig hx
  have hc := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := x))
    (show 0≤l/2 by linarith [hl.1])
  have hs := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
    (show 0≤l/12 by linarith [hl.1])
  have hx2 := mul_le_mul_of_nonneg_right hx.2 hx.1
  have hm := mul_le_mul_of_nonneg_left hx2 (show 0≤l/4 by linarith [hl.1])
  have hlx := mul_le_mul_of_nonneg_right hl.2 hx.1
  have hw := signed_width (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩)
  rw [abs_of_nonneg ht.2.2.1] at hw
  rw [hw]
  nlinarith

lemma negative_core_support {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (11/10:ℝ)< -x+(291/500)*(1+Real.cos x)+(6111/5000)*Real.sin x := by
  have h := trig_concave_gt (α := (-1:ℝ)) (A := (6111/5000:ℝ))
    (B := (291/500:ℝ)) (m := (11/10:ℝ)-291/500)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Real.pi_gt_three]) hx
    (by norm_num)
    (by linarith [cap_trig.1,cap_trig.2.2.1])
  linarith

lemma zero_opposite_core_core {a b A B φ : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : CorePairGeometry.CoreState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (391/400:ℝ)<φ+coreLabel a b+coreLabel A B := by
  have hsl := core_label_lower hs
  have htl := core_label_lower ht
  have hta := CoreAngleEndpoint.state_bounds ht
  have hmul := mul_nonneg (show (0:ℝ)≤291/250 by norm_num) hm
  norm_num [forwardMargin] at hmul
  by_cases hp : 0≤φ
  · have hx : φ∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hφ).2⟩
    have tr := positive_trig hx
    have hAs := mul_le_mul_of_nonneg_right hta.2.1 tr.2.2.1
    have hBc := mul_nonneg hta.2.2.1 (by linarith [tr.2.1] : 0≤1-Real.cos φ)
    have hsupport := positive_core_support (l := (291/250:ℝ)) (by norm_num) hx
    nlinarith
  · let x : ℝ := -φ
    have hx : x∈Icc 0 (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; linarith [(abs_le.mp hφ).1]⟩
    have tr := positive_trig hx
    have ha : (11/20:ℝ)≤A := by
      rcases ht with ⟨rfl,_,_⟩ | ⟨hB,hBA,hcircle⟩
      · norm_num
      · linarith [(CorePairGeometry.corner_geometry hB hBA hcircle).1]
    have hAs := mul_le_mul_of_nonneg_right ha tr.2.2.1
    have hBc := mul_nonneg hta.2.2.1 (by linarith [tr.2.1] : 0≤1-Real.cos x)
    have he : φ= -x := by dsimp [x]; ring
    have hw := signed_width hφ
    rw [he,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hw
    rw [he,Real.cos_neg,Real.sin_neg,hw] at hmul
    rw [he]
    have hsupport := negative_core_support hx
    nlinarith

lemma zero_opposite_core_outer {a b A B φ : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (391/400:ℝ)<φ+coreLabel a b+outerLabel A B := by
  let u : ℝ := (13/200)-(203/200)*Real.sin φ
  let v : ℝ := (203/200)-(203/200)*Real.cos φ
  have hv : 0≤v := by dsimp [v]; linarith [Real.cos_le_one φ]
  have htarget := outer_endpoints_lower (X := u) (Y := v)
    (m := min (u*outerAxial) ((u+v)*outerDiagonal)) ht hv
    (min_le_left _ _) (min_le_right _ _)
  have hsource := core_label_lower hs
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  have he := zero_core_outer_opposite_endpoints hφ
  have hmin : (391/400:ℝ)-(φ+(203/200)*pairWidth φ-9/100)<
      min (u*outerAxial) ((u+v)*outerDiagonal) := by
    dsimp [u,v]
    exact lt_min (by linarith [he.1]) (by linarith [he.2])
  have hmul := mul_nonneg (show (0:ℝ)≤203/200 by norm_num) hm
  norm_num [forwardMargin] at hmul
  dsimp [u,v] at htarget hmin
  dsimp [outerLabel]
  nlinarith

lemma zero_opposite_outer_outer {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (391/400:ℝ)<φ+outerLabel a b+outerLabel A B := by
  let u : ℝ := (13/200)-(39/40)*Real.sin φ
  let v : ℝ := (203/200)-(39/40)*Real.cos φ
  have hv : 0≤v := by dsimp [v]; linarith [Real.cos_le_one φ]
  have htarget := outer_endpoints_lower (X := u) (Y := v)
    (m := min (u*outerAxial) ((u+v)*outerDiagonal)) ht hv
    (min_le_left _ _) (min_le_right _ _)
  have hsource := outer_endpoints_lower (X := (13/200:ℝ)) (Y := (1/25:ℝ))
    (m := (13/200)*outerAxial) hs (by norm_num) le_rfl
    (by linarith [outer_endpoint_bounds.2.1,outer_endpoint_bounds.2.2.1])
  have he := zero_outer_opposite_endpoints hφ
  have hmin : (391/400:ℝ)-(φ+(39/40)*pairWidth φ-9/50+(13/200)*outerAxial)<
      min (u*outerAxial) ((u+v)*outerDiagonal) := by
    dsimp [u,v]
    exact lt_min (by linarith [he.1]) (by linarith [he.2])
  have hmul := mul_nonneg (show (0:ℝ)≤39/40 by norm_num) hm
  norm_num [forwardMargin] at hmul
  dsimp [u,v] at htarget hmin
  dsimp [outerLabel]
  nlinarith

lemma zero_outer_core_negative_angle {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 0 a b A B 1 (-1) (-x)) : x<1/2 := by
  have hso := outer_bounds hs
  have hco := CoreAngleEndpoint.state_bounds ht
  have hA : (11/20:ℝ)<A := by
    rcases ht with ⟨rfl,_,_⟩ | ⟨hB,hBA,hcircle⟩
    · norm_num
    · linarith [(CorePairGeometry.corner_geometry hB hBA hcircle).1]
  have hb : b<9/10 := hso.2.2.2.1.trans_lt outer_endpoint_bounds.2.2.2
  have hB : B<14/25 := by linarith [hco.2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
  have tr := positive_trig hx
  have hAs := mul_le_mul_of_nonneg_right hA.le tr.2.2.1
  have hBc := mul_le_mul_of_nonneg_right hB.le (by linarith [tr.1] : 0≤Real.cos x)
  have hw := signed_width (x := -x) (by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2)
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hw
  norm_num [forwardMargin,Real.sin_neg,Real.cos_neg] at hm
  rw [hw] at hm
  by_contra! hbad
  have hsin := sin_mono (show (1/2:ℝ)∈Icc 0 (7/10) by norm_num) hx hbad
  have hlower := Real.sin_ge_sub_cube (show (0:ℝ)≤1/2 by norm_num)
  norm_num at hlower
  nlinarith [tr.2.1]

lemma zero_opposite_outer_core {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (391/400:ℝ)<φ+outerLabel a b+coreLabel A B := by
  have hso := outer_bounds hs
  have hco := CoreAngleEndpoint.state_bounds ht
  have hcore := core_label_lower ht
  by_cases hp : 0≤φ
  · have hx : φ∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hφ).2⟩
    have tr := positive_trig hx
    have hsource : -(643/20000:ℝ)≤outerLabel a b-(203/200)*b := by
      dsimp [outerLabel]
      linarith [hso.1,outer_endpoint_bounds.2.2.1]
    have hAs := mul_le_mul_of_nonneg_right hco.2.1 tr.2.2.1
    have hBc := mul_nonneg hco.2.2.1 (by linarith [tr.2.1] : 0≤1-Real.cos φ)
    have hmul := mul_nonneg (show (0:ℝ)≤203/200 by norm_num) hm
    norm_num [forwardMargin] at hmul
    have hlower := positive_core_support (l := (203/200:ℝ)) (by norm_num) hx
    nlinarith
  · let x : ℝ := -φ
    have hx : x∈Icc 0 (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; linarith [(abs_le.mp hφ).1]⟩
    have he : φ= -x := by dsimp [x]; ring
    have hm' : 0≤forwardMargin 0 a b A B 1 (-1) (-x) := by simpa [he] using hm
    have hxhalf := zero_outer_core_negative_angle hs ht hx hm'
    have tr := positive_trig hx
    have hA : (11/20:ℝ)≤A := by
      rcases ht with ⟨rfl,_,_⟩ | ⟨hB,hBA,hcircle⟩
      · norm_num
      · linarith [(CorePairGeometry.corner_geometry hB hBA hcircle).1]
    have hsource : -9/100-(21/250)*outerDiagonal≤outerLabel a b-(291/250)*b := by
      dsimp [outerLabel]
      linarith [hso.1,hso.2.2.2.1]
    have hAs := mul_le_mul_of_nonneg_right hA tr.2.2.1
    have hBc := mul_nonneg hco.2.2.1 (by linarith [tr.2.1] : 0≤1-Real.cos x)
    have hmul := mul_nonneg (show (0:ℝ)≤291/250 by norm_num) hm'
    have hw := signed_width (x := -x) (by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2)
    rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hw
    norm_num [forwardMargin,Real.sin_neg,Real.cos_neg] at hmul
    rw [hw] at hmul
    have hsupport : (391/400:ℝ)< -x-9/100-(21/250)*outerDiagonal+
        (291/500)*(1+Real.cos x)+(6111/5000)*Real.sin x := by
      have htaylorS := Real.sin_ge_sub_cube (show (0:ℝ)≤1/2 by norm_num)
      have htaylorC := Real.one_sub_sq_div_two_le_cos (x := (1/2:ℝ))
      have hh := trig_concave_gt (α := (-1:ℝ)) (A := (6111/5000:ℝ))
        (B := (291/500:ℝ))
        (m := (391/400:ℝ)+9/100+(21/250)*outerDiagonal-291/500)
        (by norm_num) (by norm_num) (by norm_num)
        (by linarith [Real.pi_gt_three]) (show x∈Icc 0 (1/2) from ⟨hx.1,hxhalf.le⟩)
        (by norm_num; linarith [outer_endpoint_bounds.2.2.2])
        (by norm_num at htaylorS htaylorC ⊢; linarith [outer_endpoint_bounds.2.2.2])
      linarith
    rw [he]
    nlinarith

/-- All radial orders on the original source-secondary axis. -/
theorem zero_opposite_secondary {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (391/400:ℝ)<φ+label source a b+label target A B := by
  by_cases hso : source=.outer <;> by_cases hto : target=.outer
  · have hs' : OuterState a b := by simpa [State,hso] using hs
    have ht' : OuterState A B := by simpa [State,hto] using ht
    simpa [label,hso,hto] using zero_opposite_outer_outer hs' ht' hφ hm
  · have hs' : OuterState a b := by simpa [State,hso] using hs
    have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
    simpa [label,hso,hto] using zero_opposite_outer_core hs' ht' hφ hm
  · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
    have ht' : OuterState A B := by simpa [State,hto] using ht
    simpa [label,hso,hto] using zero_opposite_core_outer hs' ht' hφ hm
  · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
    have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
    simpa [label,hso,hto] using zero_opposite_core_core hs' ht' hφ hm

end SquaresInCircles.Eight.CommonQuarter
end
end
end

section
@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.CommonQuarter

open WordProblems

lemma gap_reverse (σ τ : Bool) (a b A B φ : ℝ) :
    φ+(sign (!τ):ℝ)*Real.arctan (B/A)-(sign (!σ):ℝ)*Real.arctan (b/a)=
      φ+(sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A) := by
  cases σ <;> cases τ <;> norm_num [sign] <;> ring

/-- The source-secondary owner for every pair of signs, on the original state pair. -/
theorem zero_secondary_cost {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hφ : |φ|≤7/10)
    (hg : (19/25:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A))
    (hm : 0≤forwardMargin 0 a b A B (sign σ) (sign τ) φ) :
    (391/400:ℝ)<cost source target σ τ a b A B φ := by
  cases σ <;> cases τ
  · exact zero_same_secondary hs ht false hφ hm
  · have hg' : (19/25:ℝ)<φ-Real.arctan (b/a)-Real.arctan (B/A) := by
      have h := hg
      simp only [sign, Bool.false_eq_true, ite_false, ite_true, Rat.cast_neg,
        Rat.cast_one] at h
      linarith
    exact (zero_negative_positive_false hs ht hφ hg').elim
  · have hm' : 0≤forwardMargin 0 a b A B 1 (-1) φ := by simpa [sign] using hm
    simpa [cost,sign] using zero_opposite_secondary hs ht hφ hm'
  · exact zero_same_secondary hs ht true hφ hm

/-- The continuous zero-quarter inequality, for every owner, closed radial state and signed tie
choice. -/
theorem zero_cost {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hφ : |φ|≤7/10)
    (hg : (19/25:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A))
    (j : Fin 4) (hm : 0≤forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (391/400:ℝ)<cost source target σ τ a b A B φ := by
  have hgr : (19/25:ℝ)<φ+(sign (!τ):ℝ)*Real.arctan (B/A)-
      (sign (!σ):ℝ)*Real.arctan (b/a) := by
    rwa [gap_reverse]
  fin_cases j
  · exact zero_secondary_cost hs ht σ τ hφ hg hm
  · have hr : 0≤forwardMargin 3 A B a b (sign (!τ)) (sign (!σ)) φ := by
      simpa using (margin_reverse 1 σ τ a b A B φ).symm ▸ hm
    simpa [cost_reverse] using zero_primary_cost ht hs (!τ) (!σ) hφ hgr hr
  · have hr : 0≤forwardMargin 0 A B a b (sign (!τ)) (sign (!σ)) φ := by
      simpa using (margin_reverse 2 σ τ a b A B φ).symm ▸ hm
    simpa [cost_reverse] using zero_secondary_cost ht hs (!τ) (!σ) hφ hgr hr
  · exact zero_primary_cost hs ht σ τ hφ hg hm

/-- The common zero cost on the boundary cycle and its frame lift. -/
theorem actual_zero (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (391/400:ℝ)<QuarterWordGeometry.phaseValue F hgap i+
      QuarterWordGeometry.commonMarker C i-QuarterWordGeometry.commonMarker C (next i) := by
  have hm := QuarterWordGeometry.original_margin C F hgap i j hj
  have hp : |QuarterWordGeometry.phaseValue F hgap i|≤7/10 := by
    simpa [QuarterWordGeometry.phaseValue,hk] using
      (QuarterWordGeometry.difference_small F i).le
  have he := QuarterWordGeometry.phase_gap C F hgap i
  rw [QuarterWordGeometry.alpha_formula,QuarterWordGeometry.alpha_formula] at he
  have hg : (19/25:ℝ)<QuarterWordGeometry.phaseValue F hgap i+
      (sign (QuarterWordGeometry.positiveOf C i):ℝ)*Real.arctan (C.b i/C.a i)-
      (sign (QuarterWordGeometry.positiveOf C (next i)):ℝ)*
        Real.arctan (C.b (next i)/C.a (next i)) := by
    rw [he]
    exact hgap i
  have h := zero_cost (actual_state C i) (actual_state C (next i))
    (QuarterWordGeometry.positiveOf C i) (QuarterWordGeometry.positiveOf C (next i)) hp hg j hm
  simpa [cost,QuarterWordGeometry.commonMarker,commonValue_eq] using h

end SquaresInCircles.Eight.CommonQuarter
end
end
end
