module

public import SquaresInCircles.Eight.Frames.Diagonal.Tails
public import SquaresInCircles.Eight.Frames.High.HighCircleScalars
public import SquaresInCircles.Eight.Frames.High.LowSecondNormPolynomial
public import SquaresInCircles.Eight.Frames.High.LowUpperConstant
public import SquaresInCircles.Eight.Frames.High.HighVaryingScalars
public import SquaresInCircles.Eight.Frames.Mid.HighVaryingCalculus

/-!
# Eight squares: all actual high/high central witnesses

Every sign pair is covered from its actual infeasible initial interval
through its complete angular tail.  No endpoint minimizer, preferred
owner, or concentrated frame is assumed.
-/

section
/-!
## The high/high supports

The forms of `FrameHighHighFixedCalculus` bound the cost of a high/high pair with a nonnegative
central margin: the source is bounded by the circle support, or, for a positive source and
`17/50 ≤ l ≤ 43/100`, by its axial end (`circle_source`, `axial_source`), the target by an end of
the high arc, and then the cost by the form `F` (`fixed_support`); if `F` exceeds `9099/10000`
at both ends of the arc, so does the cost (`fixed_endpoints`). For a negative source the
multiplier `FrameHighHighVaryingCalculus.lam x` varies with the angle, with its own form
(`varying_form`). Each form comes from the central margin itself, before any scalar bound is
used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighSupportForms
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameDiagonalSupport

theorem circle_source (i : Bool) (l : ℝ) {b : ℝ} (hb : b∈arc false) :
    FrameHighHighFixedCalculus.sourceValue true i l≤ source false i l b := by
  rw [FrameHighHighFixedCalculus.sourceValue_eq]
  exact source_circle_lower false i l hb

theorem axial_source {l b : ℝ} (hb : b∈arc false)
    (hl : l∈Icc (17/50:ℝ) (43/100)) :
    FrameHighHighFixedCalculus.sourceValue false true l≤ source false true l b := by
  rw [FrameHighHighFixedCalculus.sourceValue_eq]
  exact FrameMidHighSupports.positive_high_source hb hl

theorem fixed_support (circle i j cut : Bool) {l b B x : ℝ}
    (hl : 0≤l) (hx : x∈Icc 0 (Real.pi/2))
    (hm : 0≤central i j (A b) b (A B) B x)
    (hs : FrameHighHighFixedCalculus.sourceValue circle i l≤ source false i l b)
    (ht : target false j l x (FrameHighHighFixedCalculus.endB cut)≤target false j l x B) :
    FrameHighHighFixedCalculus.F circle i j cut l x≤cost false false i j b B x := by
  have h := FrameDiagonalSupport.support hl hm hs ht
  rwa [FrameHighHighFixedCalculus.support_formula circle i j cut l hx] at h

theorem fixed_endpoints (circle i j : Bool) {l b B x : ℝ}
    (hl : 0≤l) (hx : x∈Icc 0 (Real.pi/2))
    (hm : 0≤central i j (A b) b (A B) B x)
    (hs : FrameHighHighFixedCalculus.sourceValue circle i l≤ source false i l b)
    (ht : min (target false j l x 0) (target false j l x b1)≤target false j l x B)
    (hval : ∀ cut : Bool, (9099/10000:ℝ)<FrameHighHighFixedCalculus.F circle i j cut l x) :
    (9099/10000:ℝ)<cost false false i j b B x := by
  by_cases he : target false j l x 0≤target false j l x b1
  · rw [min_eq_left he] at ht
    exact (hval false).trans_le (fixed_support circle i j false hl hx hm hs ht)
  · rw [min_eq_right (lt_of_not_ge he).le] at ht
    exact (hval true).trans_le (fixed_support circle i j true hl hx hm hs ht)

theorem varying_form {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    base false false false false (FrameHighHighVaryingCalculus.lam x) x+
      sourceCircle false false (FrameHighHighVaryingCalculus.lam x)+
      target false false (FrameHighHighVaryingCalculus.lam x) x b1=
        FrameHighHighVaryingCalculus.F x := by
  have hn : Real.sqrt
      ((sourceU false false (FrameHighHighVaryingCalculus.lam x))^2+
       (sourceV false false (FrameHighHighVaryingCalculus.lam x))^2)=
        FrameHighHighVaryingCalculus.N x := by
    rw [FrameHighHighVaryingCalculus.N_literal]
    congr 1
    dsimp [sourceU,sourceV,primary,transverse,sign]
    ring
  rw [fixed_target_first false false false false (FrameHighHighVaryingCalculus.lam x)
    b1 (sourceCircle false false (FrameHighHighVaryingCalculus.lam x)) hx]
  rw [sourceCircle,hn,A_b1]
  dsimp [FrameHighHighVaryingCalculus.F,FrameHighHighVaryingCalculus.X,
    FrameHighHighVaryingCalculus.Y,constant,marker,H,sourceU,primary,sign]
  simp only [A_b1]
  ring

end SquaresInCircles.Eight.FrameHighHighSupportForms
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighCentral
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameDiagonalSupport FrameHighHighSupports FrameHighHighSupportForms
open FrameDiagonalTrigonometry

theorem positive_first {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc false)
    (hx : x∈Icc (7/20:ℝ) (6/5))
    (hm : 0≤central true true (A b) b (A B) B x) :
    (9099/10000:ℝ)<cost false false true true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  apply fixed_endpoints false true true (by norm_num : (0:ℝ)≤39/100) hxq hm
    (axial_source hb (show (39/100:ℝ)∈Icc (17/50) (43/100) by norm_num))
    (positive_target_endpoints hB hx)
  exact fun cut => FrameHighHighFixedScalars.positive_lower cut hx

theorem positive_last {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc false)
    (hx : x∈Icc (6/5:ℝ) (Real.pi/2))
    (hm : 0≤central true true (A b) b (A B) B x) :
    (9099/10000:ℝ)<cost false false true true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨by linarith [hx.1],hx.2⟩
  have hs := FrameDiagonalSupport.support (by norm_num : (0:ℝ)≤39/100) hm
    (FrameMidHighSupports.positive_high_source hb
      (show (39/100:ℝ)∈Icc (17/50) (43/100) by norm_num))
    (target_circle_lower false true (39/100) x hB)
  have hf := FrameHighHighCircleScalars.support_formula true false (39/100) hxq
  simp only [FrameHighHighFixedCalculus.endB,Bool.false_eq_true,↓reduceIte] at hf
  rw [hf] at hs
  exact (FrameHighHighCircleScalars.positive_lower hx).trans_le hs

theorem plus_minus_first {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc false)
    (hx : x∈Icc (7/20:ℝ) (3/5))
    (hm : 0≤central true false (A b) b (A B) B x) :
    (9099/10000:ℝ)<cost false false true false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  exact (FrameHighHighFixedScalars.plus_minus_first_lower hx).trans_le
    (fixed_support true true false true (by norm_num : (0:ℝ)≤11/20) hxq hm
      (circle_source true (11/20) hb)
      (FrameMidHighSupports.high_target_early hB ⟨by linarith [hx.1],by linarith [hx.2]⟩))

theorem plus_minus_middle {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc false)
    (hx : x∈Icc (3/5:ℝ) (4/5))
    (hm : 0≤central true false (A b) b (A B) B x) :
    (9099/10000:ℝ)<cost false false true false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  exact (FrameHighHighFixedScalars.plus_minus_middle_lower hx).trans_le
    (fixed_support false true false true (by norm_num : (0:ℝ)≤43/100) hxq hm
      (axial_source hb (show (43/100:ℝ)∈Icc (17/50) (43/100) by norm_num))
      (middle_negative_target hB hx))

theorem plus_minus_last {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc false)
    (hx : x∈Icc (4/5:ℝ) (21/20))
    (hm : 0≤central true false (A b) b (A B) B x) :
    (9099/10000:ℝ)<cost false false true false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  apply fixed_endpoints false true false (by norm_num : (0:ℝ)≤17/50) hxq hm
    (axial_source hb (show (17/50:ℝ)∈Icc (17/50) (43/100) by norm_num))
    (small_negative_target_endpoints hB)
  exact fun cut => FrameHighHighFixedScalars.plus_minus_last_lower cut hx.1

theorem negative_first {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc false)
    (hx : x∈Icc (3/5:ℝ) (19/20))
    (hm : 0≤central false false (A b) b (A B) B x) :
    (9099/10000:ℝ)<cost false false false false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hl := FrameHighHighVaryingCalculus.multiplier_bounds hx
  have hs := FrameDiagonalSupport.support (show 0≤FrameHighHighVaryingCalculus.lam x by linarith [hl.1]) hm
    (source_circle_lower false false (FrameHighHighVaryingCalculus.lam x) hb)
    (varying_negative_target hB hx)
  rw [varying_form hxq] at hs
  exact (FrameHighHighVaryingScalars.lower hx).trans_le hs

theorem negative_last {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc false)
    (hx : x∈Icc (19/20:ℝ) (127/100))
    (hm : 0≤central false false (A b) b (A B) B x) :
    (9099/10000:ℝ)<cost false false false false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  apply fixed_endpoints true false false (by norm_num : (0:ℝ)≤17/50) hxq hm
    (circle_source false (17/50) hb) (small_negative_target_endpoints hB)
  exact fun cut => FrameHighHighFixedScalars.minus_minus_last_lower cut hx.1

theorem opposite_first {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc false)
    (hx : x∈Icc (1:ℝ) (13/10))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (9099/10000:ℝ)<cost false false false true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  exact (FrameHighHighFixedScalars.minus_plus_first_lower hx).trans_le
    (fixed_support true false true false (by norm_num : (0:ℝ)≤2/5) hxq hm
      (circle_source false (2/5) hb) (FrameMidHighSupports.high_target_opposite hB hx))

theorem opposite_last {b B x : ℝ} (hb : b∈arc false) (hB : B∈arc false)
    (hx : x∈Icc (13/10:ℝ) (15543/10000))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (9099/10000:ℝ)<cost false false false true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩
  have hs := FrameDiagonalSupport.support (by norm_num : (0:ℝ)≤73/200) hm (opposite_source_cut hb)
    (target_circle_lower false true (73/200) x hB)
  have hf := FrameHighHighCircleScalars.support_formula false true (73/200) hxq
  simp only [FrameHighHighFixedCalculus.endB,↓reduceIte] at hf
  rw [hf] at hs
  exact (FrameHighHighCircleScalars.opposite_lower hx).trans_le hs

theorem central_lower (i j : Bool) {b B x : ℝ}
    (hb : b∈arc false) (hB : B∈arc false) (hx : 0≤x)
    (hm : 0≤central i j (A b) b (A B) B x) :
    (9099/10000:ℝ)<cost false false i j b B x := by
  by_cases ht : FrameDiagonalTails.hhTail i j≤x
  · exact FrameDiagonalTails.high_high i j hb hB ht
  have hc := FrameDiagonalCuts.central_cut false false i j (Or.inl rfl) hb hB hx hm
  cases i <;> cases j
  · change ¬(127/100:ℝ)≤x at ht
    change (3/5:ℝ)<x at hc
    by_cases h : x≤19/20
    · exact negative_first hb hB ⟨hc.le,h⟩ hm
    · exact negative_last hb hB ⟨(lt_of_not_ge h).le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(15543/10000:ℝ)≤x at ht
    change (1:ℝ)<x at hc
    by_cases h : x≤13/10
    · exact opposite_first hb hB ⟨hc.le,h⟩ hm
    · exact opposite_last hb hB ⟨(lt_of_not_ge h).le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(21/20:ℝ)≤x at ht
    change (7/20:ℝ)<x at hc
    by_cases h1 : x≤3/5
    · exact plus_minus_first hb hB ⟨hc.le,h1⟩ hm
    by_cases h2 : x≤4/5
    · exact plus_minus_middle hb hB ⟨(lt_of_not_ge h1).le,h2⟩ hm
    · exact plus_minus_last hb hB ⟨(lt_of_not_ge h2).le,(lt_of_not_ge ht).le⟩ hm
  · change ¬Real.pi/2≤x at ht
    change (7/20:ℝ)<x at hc
    by_cases h : x≤6/5
    · exact positive_first hb hB ⟨hc.le,h⟩ hm
    · exact positive_last hb hB ⟨(lt_of_not_ge h).le,(lt_of_not_ge ht).le⟩ hm

end SquaresInCircles.Eight.FrameHighHighCentral
end
end
end
