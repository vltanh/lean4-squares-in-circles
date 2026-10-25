module

public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.ThreePositiveUpper
public import SquaresInCircles.Eight.Words.Second.Mixed.LPrimaryZeroCost
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoCornerReferences
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.SourceThreeTransverse
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle

/-!
# Eight squares: original-cycle and reflected final mixed role-three rows

Every weak owner of the original negative-core to positive-outer edge
passes to the completed scalar estimate. Reflection supplies its role-five
negative-outer to positive-core counterpart with the same original points.
-/

section
/-!
## The two physical exits of the lower primary contact

At B≤.43 the primary contact already has the original transverse
separator. At B≥.43 its zero-source entry lies after 1.32. The latter
entry is obtained from continuity of the actual side coordinate and
retains the same outer point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Primary
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

lemma small_height {A B : ℝ} (ht : OuterState A B) (hB : B≤43/100) :
    (623/500:ℝ)<A := by
  have hq := ht.2.2
  have hv2 := pow_le_pow_left₀ (show 0≤B+1/2 by linarith [ht.1])
    (show B+1/2≤93/100 by linarith) 2
  by_contra hn
  have ha : A≤623/500 := le_of_not_gt hn
  have ha2 := pow_le_pow_left₀ (show 0≤A+1/2 by linarith [ht.1,ht.2.1])
    (show A+1/2≤873/500 by linarith) 2
  norm_num [Q0] at hq
  nlinarith

lemma small_transverse {A B φ : ℝ} (ht : OuterState A B) (hB : B≤43/100)
    (hφ : Lower φ) (hb : 0≤b A φ) :
    (1+Real.sin φ+Real.cos φ)/2≤-b A φ+A*Real.sin φ-B*Real.cos φ := by
  have htr := lower_trig hφ
  have hu : b A φ<(83/200:ℝ) :=
    (b_upper ht hφ).trans_lt (by linarith [(outer_bounds ht).2.1,outer_endpoint_bounds.2.1])
  let w : ℝ := k*Real.sin φ-(b A φ+1/2)*Real.cos φ
  have hw : 0<w := by
    have hp := mul_nonneg (show 0≤183/200-(b A φ+1/2) by linarith) htr.2.2.1
    dsimp [w,k]
    nlinarith [htr.1,htr.2.2.2.1]
  have hharm : ((b A φ+1/2)*Real.sin φ+k*Real.cos φ)^2+w^2=(b A φ+1/2)^2+k^2 := by
    dsimp [w]
    linear_combination ((b A φ+1/2)^2+k^2)*(Real.sin_sq_add_cos_sq φ)
  rw [equation hφ] at hharm
  have hq := ht.2.2
  have hb2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2)
    (show (1/2:ℝ)≤b A φ+1/2 by linarith) 2
  have hw2 : (B+1/2)^2<w^2 := by
    norm_num [k,Q0] at hharm hq
    nlinarith [small_height ht hB]
  have hgap : B+1/2≤w := by nlinarith [ht.1]
  have hpay := mul_nonneg htr.2.2.1 (show 0≤w-(B+1/2) by linarith)
  have hid : -b A φ+A*Real.sin φ-B*Real.cos φ-(1+Real.sin φ+Real.cos φ)/2=
      Real.cos φ*(w-(B+1/2)) := by
    dsimp [w]
    linear_combination -Real.sin φ*(equation (A := A) hφ)+
      (b A φ+1/2)*(Real.sin_sq_add_cos_sq φ)
  linarith

lemma small_lower {A B φ : ℝ} (ht : OuterState A B) (hB : B≤43/100)
    (hφ : Lower φ) (hb : 0≤b A φ) : γ<F A B φ := by
  have hu : b A φ≤1/2 := by
    linarith [b_upper ht hφ,(outer_bounds ht).2.1,outer_endpoint_bounds.2.1]
  have hs : CoreState (7/12) (b A φ) := Or.inl ⟨rfl,hb,hu⟩
  have hh := transverse_original hs ht hφ (small_transverse ht hB hφ hb)
  simpa [F,value,sideValue,EdgeThreeAligned.negativeCost,EdgeThreeAligned.negativeSideCost,
    EdgeThreeAligned.sideH_eq] using hh

lemma large_height {A B : ℝ} (ht : OuterState A B) (hB : (43/100:ℝ)≤B) :
    A<(1247/1000:ℝ) := by
  have hq := ht.2.2
  have hv2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤93/100)
    (show (93/100:ℝ)≤B+1/2 by linarith) 2
  by_contra hn
  have ha : 1247/1000≤A := le_of_not_gt hn
  have ha2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1747/1000)
    (show (1747/1000:ℝ)≤A+1/2 by linarith) 2
  norm_num [Q0] at hq
  nlinarith

lemma initial_negative {A B : ℝ} (ht : OuterState A B) (hB : (43/100:ℝ)≤B) :
    b A (33/25)<0 := by
  have hφ : (33/25:ℝ)∈LPrimaryZero.angles := ⟨le_rfl,by linarith [pi_hand_enclosure.1]⟩
  have he := equation (A := A) (late_lower hφ)
  have htr := LPrimaryZero.initial_trig
  by_contra hn
  have hp := mul_nonneg (show 0≤b A (33/25) from le_of_not_gt hn)
    (sine_positive (late_lower hφ)).le
  dsimp [k] at he
  nlinarith [large_height ht hB,htr.1,htr.2.2.1]

lemma feasible_late {A B φ : ℝ} (ht : OuterState A B) (hB : (43/100:ℝ)≤B)
    (hφ : Lower φ) (hb : 0≤b A φ) : φ∈LPrimaryZero.angles := by
  refine ⟨?_,hφ.2⟩
  by_contra hn
  have hcut : (33/25:ℝ)∈LPrimaryZero.angles := ⟨le_rfl,by linarith [pi_hand_enclosure.1]⟩
  have hh := b_monotone ht hφ (late_lower hcut) (show φ≤33/25 by linarith)
  linarith [initial_negative ht hB]

lemma zero_entry {A B φ : ℝ} (ht : OuterState A B) (hB : (43/100:ℝ)≤B)
    (hφ : Lower φ) (hb : 0≤b A φ) :
    ∃ θ : ℝ, θ∈Icc (33/25) φ ∧ b A θ=0 := by
  have hl := feasible_late ht hB hφ hb
  have hc : ContinuousOn (b A) (Icc (33/25) φ) := by
    intro θ hθ
    exact (b_hasDerivAt (A := A) (late_lower
      (show θ∈LPrimaryZero.angles from ⟨hθ.1,hθ.2.trans hφ.2⟩))).continuousAt.continuousWithinAt
  exact intermediate_value_Icc hl.1 hc
    (show (0:ℝ)∈Icc (b A (33/25)) (b A φ) from ⟨(initial_negative ht hB).le,hb⟩)

lemma zero_lower {A B θ : ℝ} (ht : OuterState A B) (hθ : θ∈LPrimaryZero.angles)
    (hz : b A θ=0) : γ<F A B θ := by
  have he := equation (A := A) (late_lower hθ)
  rw [hz] at he
  have hheight : A+1/2=LPrimaryZero.U θ := by
    dsimp [LPrimaryZero.U,PrimaryZero.U,PrimaryZero.m]
    dsimp [k] at he
    linarith
  have hh := LPrimaryZero.actual_negative ht hθ hheight
  simpa [F,hz,sideValue,EdgeThreeAligned.negativeSideCost,EdgeThreeAligned.sideH,
    e,EdgeThreeAligned.en,γ,EdgeThreeAligned.threshold] using hh

lemma aligned_lower {A B : ℝ} (ht : OuterState A B) (hA : 1≤A) : γ<F A B (Real.pi/2) := by
  have hh := EdgeThreeAligned.negative_side_aligned (b := A-1) ht (by linarith) (by linarith)
  rw [F,b_aligned]
  dsimp [γ,EdgeThreeAligned.threshold]
  linarith

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Primary
end
end
end

section
/-!
## Every original lower primary negative-core owner

The small-target contact has the already proved transverse separator.
For every larger target, its physical zero-source entry and alignment
bound the whole concave contact path. The original source is compared
with that same path before any endpoint argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Primary
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower)

lemma large_lower {A B φ : ℝ} (ht : OuterState A B) (hB : (43/100:ℝ)≤B)
    (hφ : Lower φ) (hb : 0≤b A φ) : γ<F A B φ := by
  obtain ⟨θ,hθ,hzero⟩ := zero_entry ht hB hφ hb
  have hentry : θ∈LPrimaryZero.angles := ⟨hθ.1,hθ.2.trans hφ.2⟩
  have hdom {x : ℝ} (hx : x∈Icc θ (Real.pi/2)) : x∈LPrimaryZero.angles :=
    ⟨hθ.1.trans hx.1,hx.2⟩
  have hnonneg (x : ℝ) (hx : x∈Icc θ (Real.pi/2)) : 0≤b A x := by
    have hh := b_monotone ht (late_lower hentry) (late_lower (hdom hx)) hx.1
    rw [hzero] at hh
    exact hh
  have hc : ConcaveOn ℝ (Icc θ (Real.pi/2)) (F A B) :=
    concave_of_deriv2 (fun x hx => F_hasDerivAt (B := B) (late_lower (hdom hx)))
      (fun x hx => F1_hasDerivAt (late_lower (hdom hx)))
      (fun x hx => (curvature_negative ht (hdom hx) (hnonneg x hx)).le)
  have hA : 1≤A := by linarith [b_upper ht hφ]
  exact concave_gt_of_endpoints hc ⟨hθ.2,hφ.2⟩
    (zero_lower ht hentry hzero) (aligned_lower ht hA)

theorem original {a b₀ A B φ : ℝ} (hs : CoreState a b₀)
    (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-a*Real.cos φ-b₀*Real.sin φ+A) :
    γ<value a b₀ B φ := by
  have hh := original_contact hs ht hφ hsep
  have hmin : γ<F A B φ := by
    by_cases he : B≤43/100
    · exact small_lower ht he hφ hh.2.1
    · exact large_lower ht (by linarith) hφ hh.2.1
  exact hmin.trans_le hh.2.2.2.2

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Primary
end
end
end

section
/-!
## All original negative-core to positive-outer role-three owners

The completed lower transverse and primary estimates join the upper
finite aligned comparison. Both remaining lower axes are excluded at
their original signed projections. Every weak tie and core-side join
is included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig lower_width)

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) : γ<value a b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  by_cases hlo : φ≤Real.pi/2
  · have hlow : Lower φ := ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hlo⟩
    have htr := lower_trig hlow
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    fin_cases j
    · apply transverse_original hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · apply Primary.original hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · have ha := mul_nonneg (show 0≤a by linarith [hcore.1])
        (show 0≤1-Real.sin φ by linarith [htr.2.1])
      have hb := mul_nonneg hcore.2.2.1 htr.2.2.1
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      nlinarith [hcore.2.1,ht.1]
    · have hAc := mul_nonneg (show 0≤A by linarith [ht.1,ht.2.1]) htr.2.2.1
      have hBs := mul_nonneg ht.1 (show 0≤Real.sin φ by linarith [htr.1])
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith [hcore.2.1]
  · let x := φ-Real.pi/2
    have hx : x∈Icc (0:ℝ) (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; exact (abs_le.mp hφ).2⟩
    have hφeq : φ=Real.pi/2+x := by dsimp [x]; ring
    rw [hφeq] at hm ⊢
    exact EdgeThreeAligned.negative_upper_original hs ht hx j hm

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    SecondWord.threshold 3<cost 3 kind .outer false true a b A B φ := by
  rw [threshold_value,core_outer_negative_positive hk ht]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Role (i : Vertex) (source target : RadialKind) (σ τ : Bool) : Prop :=
  (i=3 ∧ source≠.outer ∧ target=.outer ∧ σ=false ∧ τ=true) ∨
  (i=5 ∧ source=.outer ∧ target≠.outer ∧ σ=false ∧ τ=true)

theorem original_role {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hrole : Role i source target σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    SecondWord.threshold i<cost i source target σ τ a b A B φ := by
  rcases hrole with ⟨rfl,hk,rfl,rfl,rfl⟩ | ⟨rfl,rfl,hk,rfl,rfl⟩
  · exact literal hk (by simpa [State,hk] using hs) (by simpa [State] using ht)
      hφ j (by simpa [WordProblems.sign] using hm)
  · have hs' : OuterState a b := by simpa [State] using hs
    have ht' : CoreState A B := by simpa [State,hk] using ht
    have heq := margin_reflection j a b A B (-1) 1 φ
    have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) 1 φ := by
      norm_num at heq
      rw [heq]
      simpa [WordProblems.sign] using hm
    have hh := literal hk ht' hs' hφ (reflectedOwner j) hrev
    have he := cost_reflection (3:Vertex) target .outer false true A B a b φ
    norm_num [reverseEdge] at he
    rw [←he] at hh
    simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  exact original_role hrole (actual_state C i) (actual_state C (next i)) hφ j
    (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole j howner

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource
end
end
end
