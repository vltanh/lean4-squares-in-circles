module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeSourceThreePrimaryData

/-!
# The two physical exits of the lower primary contact

At B≤.43 the primary contact already has the original transverse
separator. At B≥.43 its zero-source entry lies after 1.32. The latter
entry is obtained from continuity of the actual side coordinate and
retains the same outer point. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Primary
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

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Primary
