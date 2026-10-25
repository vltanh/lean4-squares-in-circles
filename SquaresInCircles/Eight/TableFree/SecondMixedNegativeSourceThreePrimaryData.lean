module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeSourceThreeTransverse

/-!
# The original lower primary contact for the negative core

The weak primary separator forces the source onto its straight side.
Its exact contact coordinate increases with angle on the full lower
half and remains below A-1. On the later zero-entry range the contact
cost is strictly concave. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Primary
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

def k : ℝ := 13/12
def b (A φ : ℝ) : ℝ := (A-1/2-k*Real.cos φ)/Real.sin φ-1/2
def b1 (A φ : ℝ) : ℝ := (k-(A-1/2)*Real.cos φ)/(Real.sin φ)^2
def b2 (A φ : ℝ) : ℝ := (A-1/2)/Real.sin φ-
  2*(k-(A-1/2)*Real.cos φ)*Real.cos φ/(Real.sin φ)^3
def F (A B φ : ℝ) : ℝ := sideValue (b A φ) B φ
def F1 (A φ : ℝ) : ℝ := 1-(g-2*z*b A φ)*b1 A φ
def F2 (A φ : ℝ) : ℝ := 2*z*(b1 A φ)^2-(g-2*z*b A φ)*b2 A φ

lemma sine_positive {φ : ℝ} (hφ : Lower φ) : 0<Real.sin φ := by linarith [(lower_trig hφ).1]

lemma equation {A φ : ℝ} (hφ : Lower φ) :
    (b A φ+1/2)*Real.sin φ+k*Real.cos φ=A-1/2 := by
  dsimp [b]
  field_simp [(sine_positive hφ).ne']
  ring

lemma b_hasDerivAt {A φ : ℝ} (hφ : Lower φ) : HasDerivAt (b A) (b1 A φ) φ := by
  have hs := sine_positive hφ
  have hd := ((((Real.hasDerivAt_cos φ).const_mul k).const_sub (A-1/2)).div
    (Real.hasDerivAt_sin φ) hs.ne').sub_const (1/2)
  convert hd using 1
  · rfl
  · dsimp [b1]
    field_simp [hs.ne']
    nlinarith [congrArg (fun x : ℝ => k*x) (Real.sin_sq_add_cos_sq φ)]

lemma b1_hasDerivAt {A φ : ℝ} (hφ : Lower φ) : HasDerivAt (b1 A) (b2 A φ) φ := by
  have hs := sine_positive hφ
  have hn : HasDerivAt (fun x => k-(A-1/2)*Real.cos x) ((A-1/2)*Real.sin φ) φ := by
    have h := ((Real.hasDerivAt_cos φ).const_mul (A-1/2)).const_sub k
    exact h.congr_deriv (by ring)
  have hdn : HasDerivAt (fun x => (Real.sin x)^2) (2*Real.sin φ*Real.cos φ) φ := by
    have h := (Real.hasDerivAt_sin φ).pow 2
    exact h.congr_deriv (by norm_num <;> ring)
  have hd := hn.div hdn (pow_ne_zero 2 hs.ne')
  have hf : b1 A=fun x => (k-(A-1/2)*Real.cos x)/(Real.sin x)^2 := rfl
  rw [hf]
  refine hd.congr_deriv ?_
  simp only [b2]
  field_simp

lemma first_identity {A φ : ℝ} (hφ : Lower φ) :
    b1 A φ=k-(b A φ+1/2)*(Real.cos φ/Real.sin φ) := by
  dsimp [b1,b]
  field_simp [(sine_positive hφ).ne']
  nlinarith [congrArg (fun x : ℝ => k*x) (Real.sin_sq_add_cos_sq φ)]

lemma second_identity {A φ : ℝ} (hφ : Lower φ) :
    b2 A φ=(b A φ+1/2)*(1+2*(Real.cos φ/Real.sin φ)^2)-k*(Real.cos φ/Real.sin φ) := by
  dsimp [b2,b]
  field_simp [(sine_positive hφ).ne']
  nlinarith [congrArg (fun x : ℝ => 2*k*Real.cos φ*x) (Real.sin_sq_add_cos_sq φ)]

lemma b1_positive {A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ) : 0<b1 A φ := by
  have hAlo : (89/100:ℝ)<A := outer_endpoint_bounds.2.2.1.trans_le (outer_bounds ht).1
  have hAhi := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hp := mul_nonneg (show 0≤A-1/2 by linarith)
    (show 0≤1-Real.cos φ by linarith [Real.cos_le_one φ])
  apply div_pos _ (pow_pos (sine_positive hφ) 2)
  dsimp [k]
  nlinarith

lemma b_monotone {A B : ℝ} (ht : OuterState A B) :
    MonotoneOn (b A) (Icc lowerAngle (Real.pi/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun φ hφ => (b_hasDerivAt hφ).continuousAt.continuousWithinAt)
    (fun φ hφ => b_hasDerivAt (Ioo_subset_Icc_self hφ))
    (fun φ hφ => (b1_positive ht (Ioo_subset_Icc_self hφ)).le)

lemma b_upper {A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ) : b A φ≤A-1 := by
  have htr := lower_trig hφ
  have hAlo : (89/100:ℝ)<A := outer_endpoint_bounds.2.2.1.trans_le (outer_bounds ht).1
  have hAhi := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hp := mul_nonneg (show 0≤A-1/2 by linarith)
    (show 0≤Real.sin φ+Real.cos φ-1 by linarith [htr.2.2.2.2])
  have hq := mul_nonneg (show 0≤k-(A-1/2) by dsimp [k]; linarith) htr.2.2.1
  apply (mul_le_mul_iff_left₀ (sine_positive hφ)).mp
  nlinarith [equation (A := A) hφ]

lemma b_aligned (A : ℝ) : b A (Real.pi/2)=A-1 := by norm_num [b,k] <;> ring

lemma original_contact {a b₀ A B φ : ℝ} (hs : CoreState a b₀)
    (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-a*Real.cos φ-b₀*Real.sin φ+A) :
    a=7/12 ∧ 0≤b A φ ∧ b A φ<(83/200:ℝ) ∧ 1≤A ∧ F A B φ≤value a b₀ B φ := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  have htr := lower_trig hφ
  have hAhi := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hside : b₀<1/2 := by
    by_contra hn
    have hb : 1/2≤b₀ := le_of_not_gt hn
    have ha : 1/2≤a := hb.trans hcore.2.2.2.1
    have hp := mul_nonneg (sub_nonneg.mpr ha) htr.2.2.1
    have hq := mul_nonneg (sub_nonneg.mpr hb) (sine_positive hφ).le
    nlinarith [htr.2.2.2.2]
  have ha := (CommonQuarter.core_small_side hs hside).1
  have he := equation (A := A) hφ
  have hbc : b₀≤b A φ := by
    apply (mul_le_mul_iff_left₀ (sine_positive hφ)).mp
    rw [ha] at hsep
    dsimp [k] at he
    nlinarith
  have hu := b_upper ht hφ
  have hm := EdgeThreeAligned.sideH_mono hcore.2.2.1
    (show b A φ≤1/2 by linarith) hbc
  refine ⟨ha,by linarith [hcore.2.2.1],by linarith,by linarith [hcore.2.2.1],?_⟩
  dsimp [F,sideValue,value,EdgeThreeAligned.negativeSideCost,EdgeThreeAligned.negativeCost]
  rw [ha,EdgeThreeAligned.sideH_eq]
  linarith

lemma F_hasDerivAt {A B φ : ℝ} (hφ : Lower φ) : HasDerivAt (F A B) (F1 A φ) φ := by
  have h := ((hasDerivAt_id φ).sub
    ((((b_hasDerivAt (A := A) hφ).const_mul g).const_add e).sub
      (((b_hasDerivAt (A := A) hφ).pow 2).const_mul z))).sub_const (L B)
  exact h.congr_deriv (by simp only [F1]; push_cast; ring)

lemma F1_hasDerivAt {A φ : ℝ} (hφ : Lower φ) : HasDerivAt (F1 A) (F2 A φ) φ := by
  have h := ((((b_hasDerivAt (A := A) hφ).const_mul (2*z)).const_sub g).mul
    (b1_hasDerivAt (A := A) hφ)).const_sub 1
  exact h.congr_deriv (by simp only [F2]; ring)

lemma late_lower {φ : ℝ} (hφ : φ∈LPrimaryZero.angles) : Lower φ :=
  ⟨by dsimp [lowerAngle]; linarith [hφ.1,pi_hand_enclosure.2],hφ.2⟩

lemma curvature_negative {A B φ : ℝ} (ht : OuterState A B)
    (hφ : φ∈LPrimaryZero.angles) (hb : 0≤b A φ) : F2 A φ<0 := by
  have hl := late_lower hφ
  have htr := LPrimaryZero.trig hφ
  have hs := sine_positive hl
  have hu : b A φ<(83/200:ℝ) :=
    (b_upper ht hl).trans_lt (by linarith [(outer_bounds ht).2.1,outer_endpoint_bounds.2.1])
  let t := Real.cos φ/Real.sin φ
  have ht0 : 0≤t := div_nonneg htr.2.2.1 hs.le
  have hthi : t<(261/1000:ℝ) := by
    apply (div_lt_iff₀ hs).2
    linarith [htr.1,htr.2.2.2]
  have hd := b1_positive ht hl
  have hdhi : b1 A φ≤k := by
    have hp := mul_nonneg (show 0≤b A φ+1/2 by linarith) ht0
    rw [first_identity hl]
    linarith
  have hd2 : (b1 A φ)^2≤(13/12:ℝ)^2 := by
    exact pow_le_pow_left₀ hd.le (by simpa [k] using hdhi) 2
  have hdd : (21/100:ℝ)<b2 A φ := by
    have hp := mul_nonneg hb (show 0≤1+2*t^2 by positivity)
    have hsq := sq_nonneg t
    rw [second_identity hl]
    change (21/100:ℝ)<(b A φ+1/2)*(1+2*t^2)-k*t
    dsimp [k]
    nlinarith
  have hcoef : (47/50:ℝ)<g-2*z*b A φ := by
    dsimp [g,z,EdgeThreeAligned.gn,EdgeThreeAligned.zn]
    linarith
  have hproduct := mul_le_mul hcoef.le hdd.le (by norm_num : (0:ℝ)≤21/100)
    (by linarith : 0≤g-2*z*b A φ)
  have hz : z=2667/50000 := by norm_num [z,EdgeThreeAligned.zn]
  simp only [F2]
  rw [hz] at hproduct ⊢
  norm_num at hd2
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Primary
