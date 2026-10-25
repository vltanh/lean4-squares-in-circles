module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Core.HighHighSecondaryScalars
public import SquaresInCircles.Eight.Frames.Core.HighSecondaryNorm
public import SquaresInCircles.Eight.Frames.Core.LowCancellation
public import SquaresInCircles.Eight.Frames.Core.MidContactData

/-!
# Eight squares: the complete original core/low frame-pair inequality

Both orientations, both original signs and all four weak forward axes
are included.  The only angular premise is the original exterior gap.
The proof derives each angle cut from separation and covers target axes
by reflected reversal, preserving their actual cost and all ties.
-/

section
/-!
## The actual high-arc endpoint supports for a core transverse axis

The two endpoint coordinates are the middle/high cut and the diagonal.
Their positive-target supports have endpoint minima because the negative
first derivative is concave.  The negative-angle supports are concave
directly.  The negative-target continuation uses the actual high cut.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighSecondaryEndpoints
open FramePair FrameCircleArc FrameHighArc FramePairCalculus
open FrameMidArc (g a2 b2 a2_bounds b2_bounds)
open FrameCoreMidScalars (ap cp trigAffine trigAffine_deriv trigAffine_monotone)

def endpointA (r : Bool) : ℝ := if r then c0 else a2
def endpointB (r : Bool) : ℝ := if r then c0 else b2
def endpointH (r : Bool) : ℝ := if r then Real.pi/4 else H2
def D (r : Bool) : ℝ := cp+g*endpointB r
def B (r : Bool) : ℝ := g*endpointA r-cp
def C (r : Bool) : ℝ := cp+g*endpointA r
def positiveFirst (r : Bool) : ℝ → ℝ :=
  trigAffine 1 (ap-endpointH r) (D r) (-B r)
def positiveFirstD (r : Bool) (x : ℝ) : ℝ :=
  1-D r*Real.sin x-B r*Real.cos x
def negativeFirst (r : Bool) : ℝ → ℝ :=
  trigAffine (-1) (ap-endpointH r) (D r) (C r)
def negativeDiagonal (z : ℝ) : ℝ :=
  -z+ap+Real.pi/4+(cp-g*c0)*Real.cos z+(cp+g*c0)*Real.sin z
def diagonalPulse (z : ℝ) : ℝ := B true*Real.sin z+D true*Real.cos z
def negativeCut (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+H2-g*a2*Real.sin x-g*b2*Real.cos x+g*pairWidth x

theorem endpoint_minimum_of_concave_negative_derivative
    {f d : ℝ → ℝ} {l u x : ℝ} (hx : x∈Icc l u)
    (hd : ∀t∈Icc l u,HasDerivAt f (d t) t)
    (hc : ConcaveOn ℝ (Icc l u) (fun t => -d t)) (hu : d u≤0) :
    min (f l) (f u)≤f x := by
  have hlu : l≤u := hx.1.trans hx.2
  by_cases hdx : d x≤0
  · have hm : AntitoneOn f (Icc x u) := by
      apply antiOn_of_hasDeriv_nonpos
      · exact fun t ht => (hd t ⟨hx.1.trans ht.1,ht.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => hd t ⟨hx.1.trans ht.1.le,ht.2.le⟩
      · intro t ht
        have hh := hc.min_le_of_mem_Icc hx ⟨hlu,le_rfl⟩ (Ioo_subset_Icc_self ht)
        have hp : 0≤ min (-d x) (-d u) := le_min (by linarith) (by linarith)
        linarith
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)
  · have hm : MonotoneOn f (Icc l x) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact fun t ht => (hd t ⟨ht.1,ht.2.trans hx.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => hd t ⟨ht.1.le,ht.2.le.trans hx.2⟩
      · intro t ht
        by_contra! hdt
        have hh := hc.min_le_of_mem_Icc ⟨ht.1.le,ht.2.le.trans hx.2⟩
          ⟨hlu,le_rfl⟩ ⟨ht.2.le,hx.2⟩
        have hp : 0≤ min (-d t) (-d u) := le_min (by linarith) (by linarith)
        exact hdx (by linarith)
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)

theorem cut_coefficients :
    (501/500:ℝ)<D false ∧ D false<1003/1000 ∧
      (843/1000:ℝ)<B false ∧ B false<211/250 ∧ endpointH false<58/125 := by
  obtain ⟨ha1,ha2⟩ := a2_bounds
  obtain ⟨hb1,hb2⟩ := b2_bounds
  have hh := H2_bounds.2
  dsimp [D,B,endpointA,endpointB,endpointH,cp,g]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> norm_num <;> linarith

theorem diagonal_coefficients :
    (1417/1000:ℝ)<D true ∧ D true<709/500 ∧
      (13/25:ℝ)<B true ∧ B true<521/1000 ∧ endpointH true<393/500 := by
  obtain ⟨hd1,hd2⟩ := FrameHighArc.diagonal_bounds
  have hp := Arithmetic.pi_hand_enclosure.2
  dsimp [D,B,endpointA,endpointB,endpointH,cp,g]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> norm_num <;> linarith

theorem coefficient_lower (r : Bool) :
    1<D r ∧ (51/100:ℝ)<B r ∧ (7/5:ℝ)<C r := by
  have he : C r=B r+2*cp := by dsimp [B,C]; ring
  cases r
  · obtain ⟨h1,-,h3,-,-⟩ := cut_coefficients
    norm_num [cp,g] at he
    refine ⟨?_,?_,?_⟩ <;> linarith
  · obtain ⟨h1,-,h3,-,-⟩ := diagonal_coefficients
    norm_num [cp,g] at he
    refine ⟨?_,?_,?_⟩ <;> linarith

theorem trig_negative_end :
    (29/40:ℝ)<Real.sin (203/250:ℝ) ∧ (86/125:ℝ)<Real.cos (203/250:ℝ) := by
  have hs := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤203/250 by norm_num)
  have hc := Arithmetic.cos10_le_cos (show (0:ℝ)≤203/250 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at *
  constructor <;> linarith

theorem positiveFirst_deriv (r : Bool) (x : ℝ) :
    HasDerivAt (positiveFirst r) (positiveFirstD r x) x := by
  convert trigAffine_deriv 1 (ap-endpointH r) (D r) (-B r) x using 1 <;>
    dsimp [positiveFirst,positiveFirstD]
  ring

theorem positiveFirst_negative_derivative_concave (r : Bool) :
    ConcaveOn ℝ (Icc (0:ℝ) (7/5)) (fun x => -positiveFirstD r x) := by
  apply concave_of_deriv2
    (f' := fun x => D r*Real.cos x-B r*Real.sin x)
    (f'' := fun x => -D r*Real.sin x-B r*Real.cos x)
  · intro x _
    have h := (((Real.hasDerivAt_sin x).const_mul (D r)).fun_add
      ((Real.hasDerivAt_cos x).const_mul (B r))).sub_const 1
    convert h using 1
    · funext y; simp only [positiveFirstD]; ring
    · ring
  · intro x _
    convert ((Real.hasDerivAt_cos x).const_mul (D r)).fun_sub
      ((Real.hasDerivAt_sin x).const_mul (B r)) using 1
    ring
  · intro x hx
    have ht := FrameLowPair.quadrant
      (show x∈Icc 0 (Real.pi/2) from ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
    have h1 := mul_nonneg (show 0≤D r by linarith [(coefficient_lower r).1]) ht.1
    have h2 := mul_nonneg (show 0≤B r by linarith [(coefficient_lower r).2.1]) ht.2.2.1
    linarith

theorem positiveFirst_end_derivative (r : Bool) : positiveFirstD r (7/5)<0 := by
  have ht := FrameCoreHighSecondaryNorm.trig_seven_fifths
  have hD := mul_lt_mul_of_pos_right (coefficient_lower r).1 (by linarith [ht.1] : 0<Real.sin (7/5:ℝ))
  have hB := mul_lt_mul_of_pos_right (coefficient_lower r).2.1
    (by linarith [ht.2.2.1] : 0<Real.cos (7/5:ℝ))
  dsimp [positiveFirstD]
  nlinarith

theorem positiveFirst_endpoints (r : Bool) :
    (9/10:ℝ)<positiveFirst r 0 ∧ (9/10:ℝ)<positiveFirst r (7/5) := by
  have ht := FrameCoreHighSecondaryNorm.trig_seven_fifths
  have hs0 : 0≤Real.sin (7/5:ℝ) := by linarith [ht.1]
  have hc0 : 0≤Real.cos (7/5:ℝ) := by linarith [ht.2.2.1]
  cases r
  · have h := cut_coefficients
    have hD := mul_le_mul_of_nonneg_right h.1.le hc0
    have hB := mul_le_mul_of_nonneg_right h.2.2.2.1.le hs0
    constructor
    · simp only [positiveFirst,trigAffine,Real.sin_zero,Real.cos_zero,mul_zero,mul_one]
      norm_num [ap,g] at *
      linarith
    · dsimp [positiveFirst,trigAffine]
      norm_num [ap,g] at *
      nlinarith
  · have h := diagonal_coefficients
    have hD := mul_le_mul_of_nonneg_right h.1.le hc0
    have hB := mul_le_mul_of_nonneg_right h.2.2.2.1.le hs0
    constructor
    · simp only [positiveFirst,trigAffine,Real.sin_zero,Real.cos_zero,mul_zero,mul_one]
      norm_num [ap,g] at *
      linarith
    · dsimp [positiveFirst,trigAffine]
      norm_num [ap,g] at *
      nlinarith

theorem positiveFirst_lower (r : Bool) {x : ℝ} (hx : x∈Icc (0:ℝ) (7/5)) :
    (9/10:ℝ)<positiveFirst r x := by
  have hh := endpoint_minimum_of_concave_negative_derivative hx
    (fun x _ => positiveFirst_deriv r x) (positiveFirst_negative_derivative_concave r)
    (positiveFirst_end_derivative r).le
  exact (lt_min (positiveFirst_endpoints r).1 (positiveFirst_endpoints r).2).trans_le hh

theorem negativeFirst_concave (r : Bool) :
    ConcaveOn ℝ (Icc (0:ℝ) (203/250)) (negativeFirst r) := by
  apply concave_of_deriv2
    (f' := fun z => -1-D r*Real.sin z+C r*Real.cos z)
    (f'' := fun z => -D r*Real.cos z-C r*Real.sin z)
  · intro z _
    exact trigAffine_deriv (-1) (ap-endpointH r) (D r) (C r) z
  · intro z _
    convert ((((Real.hasDerivAt_sin z).const_mul (D r)).neg).const_add (-1)).add
      ((Real.hasDerivAt_cos z).const_mul (C r)) using 1
    ring
  · intro z hz
    have ht := FrameLowPair.quadrant
      (show z∈Icc 0 (Real.pi/2) from ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩)
    have h1 := mul_nonneg (show 0≤D r by linarith [(coefficient_lower r).1]) ht.2.2.1
    have h2 := mul_nonneg (show 0≤C r by linarith [(coefficient_lower r).2.2]) ht.1
    linarith

theorem negativeFirst_endpoints (r : Bool) :
    (9/10:ℝ)<negativeFirst r 0 ∧ (9/10:ℝ)<negativeFirst r (203/250) := by
  have he : C r=B r+2*cp := by dsimp [B,C]; ring
  have hzero : negativeFirst r 0=positiveFirst r 0 := by
    simp [negativeFirst,positiveFirst,trigAffine]
  refine ⟨hzero.symm ▸ (positiveFirst_endpoints r).1,?_⟩
  have ht := trig_negative_end
  have hs0 : 0≤Real.sin (203/250:ℝ) := by linarith [ht.1]
  have hc0 : 0≤Real.cos (203/250:ℝ) := by linarith [ht.2]
  cases r
  · have h := cut_coefficients
    have hD := mul_le_mul_of_nonneg_right h.1.le hc0
    have hC : (87/50:ℝ)<C false := by norm_num [cp,g] at he; linarith [h.2.2.1]
    have hCs := mul_le_mul_of_nonneg_right hC.le hs0
    dsimp [negativeFirst,trigAffine]
    norm_num [ap,g] at *
    nlinarith
  · have h := diagonal_coefficients
    have hD := mul_le_mul_of_nonneg_right h.1.le hc0
    have hC : (1417/1000:ℝ)<C true := by norm_num [cp,g] at he; linarith [h.2.2.1]
    have hCs := mul_le_mul_of_nonneg_right hC.le hs0
    dsimp [negativeFirst,trigAffine]
    norm_num [ap,g] at *
    nlinarith

theorem negativeFirst_lower (r : Bool) {z : ℝ} (hz : z∈Icc (0:ℝ) (203/250)) :
    (9/10:ℝ)<negativeFirst r z :=
  concave_gt_of_endpoints (negativeFirst_concave r) hz
    (negativeFirst_endpoints r).1 (negativeFirst_endpoints r).2

theorem diagonalPulse_concave :
    ConcaveOn ℝ (Icc (0:ℝ) (203/250)) diagonalPulse := by
  apply concave_of_deriv2
    (f' := fun z => B true*Real.cos z-D true*Real.sin z)
    (f'' := fun z => -B true*Real.sin z-D true*Real.cos z)
  · intro z _
    have h := ((Real.hasDerivAt_sin z).const_mul (B true)).fun_add
      ((Real.hasDerivAt_cos z).const_mul (D true))
    convert h using 1
    · rfl
    · ring
  · intro z _
    convert ((Real.hasDerivAt_cos z).const_mul (B true)).fun_sub
      ((Real.hasDerivAt_sin z).const_mul (D true)) using 1
    ring
  · intro z hz
    have ht := FrameLowPair.quadrant
      (show z∈Icc 0 (Real.pi/2) from ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩)
    have h1 := mul_nonneg (show 0≤B true by linarith [diagonal_coefficients.2.2.1]) ht.1
    have h2 := mul_nonneg (show 0≤D true by linarith [diagonal_coefficients.1]) ht.2.2.1
    linarith

theorem diagonalPulse_lower {z : ℝ} (hz : z∈Icc (0:ℝ) (203/250)) : 1<diagonalPulse z := by
  apply concave_gt_of_endpoints diagonalPulse_concave hz
  · simpa [diagonalPulse] using (coefficient_lower true).1
  · have ht := trig_negative_end
    have hB := mul_le_mul_of_nonneg_right diagonal_coefficients.2.2.1.le
      (show 0≤Real.sin (203/250:ℝ) by linarith [ht.1])
    have hD := mul_le_mul_of_nonneg_right diagonal_coefficients.1.le
      (show 0≤Real.cos (203/250:ℝ) by linarith [ht.2])
    dsimp [diagonalPulse]
    nlinarith

theorem negativeDiagonal_deriv (z : ℝ) :
    HasDerivAt negativeDiagonal (-1+diagonalPulse z) z := by
  have h := ((((hasDerivAt_id' z).neg.add_const ap).add_const (Real.pi/4)).fun_add
    ((Real.hasDerivAt_cos z).const_mul (cp-g*c0))).fun_add
      ((Real.hasDerivAt_sin z).const_mul (cp+g*c0))
  convert h using 1
  · rfl
  · simp only [diagonalPulse,B,D,endpointA,endpointB,↓reduceIte]
    ring

theorem negativeDiagonal_lower {z : ℝ} (hz : z∈Icc (0:ℝ) (203/250)) :
    (8939/10000:ℝ)<negativeDiagonal z := by
  have hm : MonotoneOn negativeDiagonal (Icc (0:ℝ) (203/250)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => (negativeDiagonal_deriv z).continuousAt.continuousWithinAt
    · exact fun z _ => negativeDiagonal_deriv z
    · intro z hz
      linarith [diagonalPulse_lower (Ioo_subset_Icc_self hz)]
  have hh := hm ⟨le_rfl,by norm_num⟩ hz hz.1
  have he : negativeDiagonal 0=FrameCoreHighHighSecondaryScalars.parallelValue := by
    simp [negativeDiagonal,FrameCoreHighHighSecondaryScalars.parallelValue,ap,cp]
    ring
  rw [he] at hh
  exact FrameCoreHighHighSecondaryScalars.parallel_lower.trans_le hh

theorem negativeCut_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (5/2)) :
    (9/10:ℝ)<negativeCut x := by
  let a : ℝ := cp-g*b2
  let b : ℝ := -B false
  let c : ℝ := ap+H2
  have ha : -(53/500:ℝ)<a ∧ a< -(13/125:ℝ) := by
    have he : a=2*cp-D false := by dsimp [a,D,endpointB]; ring
    norm_num [cp,g] at he
    constructor <;> linarith [cut_coefficients.1,cut_coefficients.2.1]
  have hb : -(211/250:ℝ)<b ∧ b< -(843/1000:ℝ) := by
    dsimp [b]
    constructor <;> linarith [cut_coefficients.2.2.1,cut_coefficients.2.2.2.1]
  have hm1 : MonotoneOn (trigAffine 1 c a b) (Icc (6/5:ℝ) (Real.pi/2)) :=
    trigAffine_monotone (by norm_num) (by nlinarith)
  have hm2 : MonotoneOn (trigAffine 1 c (-D false) b) (Icc (Real.pi/2) (5/2:ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t _ => (trigAffine_deriv 1 c (-D false) b t).continuousAt.continuousWithinAt
    · exact fun t _ => trigAffine_deriv 1 c (-D false) b t
    · intro t ht
      have hs := second_signs
        (show t∈Icc (Real.pi/2) Real.pi from
          ⟨ht.1.le,by linarith [ht.2,FrameLowPair.pi_lower]⟩)
      have h1 := mul_nonneg (show 0≤D false by linarith [cut_coefficients.1]) hs.1
      have h2 := mul_nonneg_of_nonpos_of_nonpos (by linarith [hb.2] : b≤0) hs.2
      linarith
  have he1 {t : ℝ} (ht : t∈Icc 0 (Real.pi/2)) :
      negativeCut t=trigAffine 1 c a b t := by
    dsimp [negativeCut,trigAffine,c,a,b,B,endpointA,ap,cp]
    rw [(first_width ht).1,(first_width ht).2]
    ring
  have he2 {t : ℝ} (ht : t∈Icc (Real.pi/2) Real.pi) :
      negativeCut t=trigAffine 1 c (-D false) b t := by
    dsimp [negativeCut,trigAffine,c,b,B,D,endpointA,endpointB,ap,cp]
    rw [(second_width ht).1,(second_width ht).2]
    ring
  have hstart : (9/10:ℝ)<negativeCut (6/5) := by
    rw [he1 ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩]
    have ht := FrameLowPair.quadrant
      (show (6/5:ℝ)∈Icc 0 (Real.pi/2) by constructor <;> linarith [FrameLowPair.pi_lower])
    have hA := mul_le_mul_of_nonneg_right ha.1.le ht.2.2.1
    have hB := mul_le_mul_of_nonneg_right hb.1.le ht.1
    dsimp [trigAffine,c]
    norm_num [ap,g] at *
    nlinarith [H2_bounds.1]
  by_cases hq : x≤Real.pi/2
  · have hh := hm1 ⟨le_rfl,by linarith [FrameLowPair.pi_lower]⟩ ⟨hx.1,hq⟩ hx.1
    rw [← he1 ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩,
      ← he1 ⟨by linarith [hx.1],hq⟩] at hh
    exact hstart.trans_le hh
  · have h1 := hm1 ⟨le_rfl,by linarith [FrameLowPair.pi_lower]⟩
      ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ (by linarith [FrameLowPair.pi_lower])
    have h2 := hm2 ⟨le_rfl,by linarith [Arithmetic.pi_hand_enclosure.2]⟩
      ⟨(lt_of_not_ge hq).le,hx.2⟩ (lt_of_not_ge hq).le
    rw [← he1 ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩,
      ← he1 ⟨by positivity,le_rfl⟩] at h1
    rw [← he2 ⟨le_rfl,by linarith [Real.pi_pos]⟩,
      ← he2 ⟨(lt_of_not_ge hq).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩] at h2
    exact hstart.trans_le (h1.trans h2)

end SquaresInCircles.Eight.FrameCoreHighSecondaryEndpoints
end
end
end

section
/-!
## The original core-source primary axis against a low state

The negative tangent is charged by the actual low coordinate forced by
separation.  For the positive tangent, the full-circle norm is controlled
by the unit-speed chord inequality on one complete interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreLowCorePrimary
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g K)
open FrameCoreLowGeometry

theorem radius_upper : R<(1979/1000:ℝ) := by
  have hR := R_sq
  have hp := R_pos
  norm_num [Q0] at hR
  nlinarith

theorem trig_seven_fourths :
    (49/50:ℝ)<Real.sin (7/4:ℝ) ∧ -(37/200:ℝ)<Real.cos (7/4:ℝ) := by
  have hs := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤7/4 by norm_num)
  have hc := Arithmetic.cos10_le_cos (show (0:ℝ)≤7/4 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,
    Arithmetic.cos8] at *
  constructor <;> linarith

theorem trig_nineteen_tenths :
    (473/500:ℝ)<Real.sin (19/10:ℝ) ∧ Real.sin (19/10:ℝ)<947/1000 ∧
      -(81/250:ℝ)<Real.cos (19/10:ℝ) ∧ Real.cos (19/10:ℝ)< -(8/25) := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤19/10 by norm_num)
  have hsU := Arithmetic.sin_le_sin9 (show (0:ℝ)≤19/10 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤19/10 by norm_num)
  have hcU := Arithmetic.cos_le_cos8 (show (0:ℝ)≤19/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem negative_target_coordinate {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (Real.pi/2) (7/4:ℝ)) (hm : 0≤coreLowPrimary false a B x) :
    (28487/117600:ℝ)<B := by
  have hcore := core_bounds hc
  have hlow := low_bounds hB
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := second_signs hxq
  have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
    (by linarith [FrameLowPair.pi_lower] : (7/4:ℝ)≤Real.pi) hx
    (by rw [Real.sin_pi_div_two]; norm_num : (49/50:ℝ)<Real.sin (Real.pi/2))
    trig_seven_fourths.1
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower] : (7/4:ℝ)≤Real.pi) hx.2
  have hd : -Real.cos x<(37/200:ℝ) := by linarith [trig_seven_fourths.2]
  have hA := mul_le_mul_of_nonneg_right
    (show A B-1/2≤183/200 by linarith [hlow.2.2.2]) (neg_nonneg.mpr ht.2)
  have hAd : (A B-1/2)*(-Real.cos x)<(183/200:ℝ)*(37/200) := by linarith
  have hBs := mul_le_mul_of_nonneg_left hs.le
    (show 0≤1/2-B by linarith [hlow.2.1])
  have hsf : sign false= -1 := by simp [sign]
  dsimp only [coreLowPrimary] at hm
  rw [hsf,(second_width hxq).1] at hm
  linarith [hcore.2.1]

theorem core_primary_negative (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1)
    (hx : Real.pi/2≤x) (hm : 0≤coreLowPrimary false a B x) :
    (91/100:ℝ)<coreLowCost i false a b B x := by
  have hsource := (FrameCoreArc.signed_label_bounds i hc).1
  have htarget := L_bounds hB
  have hch := CorePairGeometry.charge_upper x
  have hsf : sign false= -1 := by simp [sign]
  dsimp only [coreLowCost]
  rw [hsf]
  by_cases hlarge : (7/4:ℝ)≤x
  · linarith
  · have hBmin := negative_target_coordinate hc hB ⟨hx,(lt_of_not_ge hlarge).le⟩ hm
    have hlabel := (low_label_linear hB).1
    have hpi : (6283/2000:ℝ)<Real.pi := by linarith [Arithmetic.pi_hand_enclosure.1]
    have huv : (0:ℝ)≤v-u := by norm_num [u,v]
    have hm2 := mul_le_mul_of_nonneg_left hBmin.le huv
    norm_num [u,v] at hm2 hlabel
    linarith

theorem positive_target_cut {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : Real.pi/2≤x)
    (hm : 0≤coreLowPrimary true a B x) : (19/10:ℝ)<x := by
  by_contra! hsmall
  have hcore := core_bounds hc
  have hlow := low_bounds hB
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx,by linarith [hsmall,FrameLowPair.pi_lower]⟩
  have ht := second_signs hxq
  have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
    (by linarith [FrameLowPair.pi_lower] : (19/10:ℝ)≤Real.pi) ⟨hx,hsmall⟩
    (by rw [Real.sin_pi_div_two]; norm_num : (9/10:ℝ)<Real.sin (Real.pi/2))
    (by linarith [trig_nineteen_tenths.1] : (9/10:ℝ)<Real.sin (19/10:ℝ))
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower] : (19/10:ℝ)≤Real.pi) hsmall
  have hd : -Real.cos x<(1/3:ℝ) := by linarith [trig_nineteen_tenths.2.2.1]
  have hA := mul_le_mul_of_nonneg_right
    (show A B-1/2≤183/200 by linarith [hlow.2.2.2]) (neg_nonneg.mpr ht.2)
  have hBsin := mul_nonneg hB.1 ht.1
  have hst : sign true=1 := by simp [sign]
  dsimp only [coreLowPrimary] at hm
  rw [hst,(second_width hxq).1] at hm
  linarith [hcore.2.1]

def N (x : ℝ) : ℝ := Real.sqrt ((u-Real.cos x)^2+(v-Real.sin x)^2)

theorem N_nonneg (x : ℝ) : 0≤N x := Real.sqrt_nonneg _
theorem N_sq (x : ℝ) : (N x)^2=(u-Real.cos x)^2+(v-Real.sin x)^2 :=
  Real.sq_sqrt (by positivity)

/-- The exact chord bound gives the unit-speed estimate for the actual norm. -/
theorem N_growth {x y : ℝ} (hxy : y≤x) : N x≤N y+(x-y) := by
  let dx : ℝ := Real.cos y-Real.cos x
  let dy : ℝ := Real.sin y-Real.sin x
  let dot : ℝ := (u-Real.cos y)*dx+(v-Real.sin y)*dy
  have hdist : dx^2+dy^2≤(x-y)^2 := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := x-y)
    rw [Real.cos_sub] at hc
    dsimp [dx,dy]
    nlinarith [Real.sin_sq_add_cos_sq x,Real.sin_sq_add_cos_sq y]
  have hid : (N y)^2*(dx^2+dy^2)-dot^2=
      ((u-Real.cos y)*dy-(v-Real.sin y)*dx)^2 := by
    rw [N_sq]
    dsimp [dot]
    ring
  have hh := mul_le_mul_of_nonneg_left hdist (sq_nonneg (N y))
  have hdotsq : dot^2≤(N y*(x-y))^2 := by
    rw [mul_pow]
    linarith [sq_nonneg ((u-Real.cos y)*dy-(v-Real.sin y)*dx)]
  have hp := mul_nonneg (N_nonneg y) (sub_nonneg.mpr hxy)
  have hdot : dot≤N y*(x-y) := (abs_le_of_sq_le_sq' hdotsq hp).2
  have hsum : (N x)^2=(N y)^2+2*dot+dx^2+dy^2 := by
    rw [N_sq,N_sq]
    dsimp [dot,dx,dy]
    ring
  have hnonneg : 0≤N y+(x-y) := add_nonneg (N_nonneg y) (sub_nonneg.mpr hxy)
  refine le_of_pow_le_pow_left₀ two_ne_zero hnonneg ?_
  rw [hsum]
  linarith

theorem N_start : N (19/10)<(3/4:ℝ) := by
  have hs := sin_lower_seven (show (0:ℝ)≤19/10 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤19/10 by norm_num)
  have hN := N_sq (19/10)
  have ht := Real.sin_sq_add_cos_sq (19/10:ℝ)
  norm_num at hs hc
  dsimp only [u,v] at hN
  refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_
  rw [hN]
  linarith

theorem norm_support_lower {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    (51/50:ℝ)<x-Real.cos x+345707/800000-R*N x := by
  have hN := (N_growth hx.1).trans_lt (by linarith [N_start] :
    N (19/10)+(x-19/10)<3/4+(x-19/10))
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤19/10)
    (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  have hcU : Real.cos x< -(8/25:ℝ) := hc.trans_lt trig_nineteen_tenths.2.2.2
  have hRN : R*N x<(1979/1000)*(3/4+(x-19/10)) :=
    mul_lt_mul'' radius_upper hN R_pos.le (N_nonneg x)
  linarith [hx.2]

theorem core_primary_circle (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (19/10:ℝ) (41/20)) (hm : 0≤coreLowPrimary true a B x) :
    x-Real.cos x+345707/800000-R*N x<coreLowCost i true a b B x := by
  have hsource : -coreLabel a b≤ sign i*coreLabel a b := by
    have hp := (label_bounds hc).1
    cases i <;> norm_num [sign]
    linarith
  have hdiag := diagonal_support (X := K-1) (Y := -g) hc
    (by norm_num [K]) (by norm_num [g])
  have hdiagState : CoreState diagonal diagonal := by
    right
    exact ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl,
      by nlinarith [CoreAngleEndpoint.diagonal_sq]⟩
  have hdiagLabel := (label_bounds hdiagState).2
  have htarget := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (Real.cos x-u) (Real.sin x-v)
  have he : Real.sqrt ((Real.cos x-u)^2+(Real.sin x-v)^2)=N x := by
    unfold N
    congr 1
    ring
  rw [he] at htarget
  have hch := CorePairGeometry.charge_upper x
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hw := (second_width hxq).1
  dsimp [coreLowCost,coreLowPrimary,coreLabel,L,sign] at *
  rw [hw] at hm
  have hu := mul_lt_mul_of_pos_left a0_bounds.1 (show 0<u by norm_num [u])
  dsimp [u,v,K,g] at *
  nlinarith [CoreAngleEndpoint.diagonal_bounds.2]

theorem core_primary (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (-(3/10:ℝ)) (41/20)) (hm : 0≤coreLowPrimary k a B x) :
    (91/100:ℝ)<coreLowCost i k a b B x := by
  have hcut := core_primary_angle k hc hB hx.1 hm
  cases k with
  | false => exact core_primary_negative i hc hB hcut.le hm
  | true =>
      have hcut' := positive_target_cut hc hB hcut.le hm
      have hdom : x∈Icc (19/10:ℝ) (41/20) := ⟨hcut'.le,hx.2⟩
      exact (lt_trans (by norm_num) (norm_support_lower hdom)).trans
        (core_primary_circle i hc hB hdom hm)

end SquaresInCircles.Eight.FrameCoreLowCorePrimary
end
end
end

section
/-!
## The two remaining whole-interval low-source scalar bounds

The short-angle functions have opposite fixed derivative signs.  The
rounded-target envelope retains the actual circle radical and has negative
derivative throughout its complete interval.  No angle cells are used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreLowLowScalars
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreLowCorePrimary

def sourceFloor : ℝ :=
  u*(2829/2000)+(u+3+v)/2-(1979/1000)*(1787/500)
def shortConstant : ℝ := 159/100+sourceFloor-1/200
def Hminus (x : ℝ) : ℝ :=
  x+shortConstant+g/2+(79/25)*Real.cos x-(9/100)*Real.sin x
def Hplus (x : ℝ) : ℝ :=
  x+shortConstant-g/2+(79/25)*Real.cos x+(291/100)*Real.sin x

theorem Hminus_deriv (x : ℝ) :
    HasDerivAt Hminus (1-(79/25)*Real.sin x-(9/100)*Real.cos x) x := by
  have h := (((((hasDerivAt_id' x).add_const shortConstant).add_const (g/2)).fun_add
    ((Real.hasDerivAt_cos x).const_mul (79/25))).fun_sub
    ((Real.hasDerivAt_sin x).const_mul (9/100)))
  have e : 1-(79/25)*Real.sin x-(9/100)*Real.cos x=
      1+(79/25)*-Real.sin x-(9/100)*Real.cos x := by ring
  rw [e]
  exact h

theorem Hplus_deriv (x : ℝ) :
    HasDerivAt Hplus (1-(79/25)*Real.sin x+(291/100)*Real.cos x) x := by
  have h := (((((hasDerivAt_id' x).add_const shortConstant).sub_const (g/2)).fun_add
    ((Real.hasDerivAt_cos x).const_mul (79/25))).fun_add
    ((Real.hasDerivAt_sin x).const_mul (291/100)))
  have e : 1-(79/25)*Real.sin x+(291/100)*Real.cos x=
      1+(79/25)*-Real.sin x+(291/100)*Real.cos x := by ring
  rw [e]
  exact h

theorem short_trig {x : ℝ} (hx : x∈Icc (3/10:ℝ) (3/5)) :
    (591/2000:ℝ)≤Real.sin x ∧ Real.sin x≤3/5 ∧ (41/50:ℝ)≤Real.cos x := by
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(3/10:ℝ))
    (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  have hs0 := Real.sin_ge_sub_cube (show (0:ℝ)≤3/10 by norm_num)
  have hsU := Real.sin_le (show 0≤x by linarith [hx.1])
  have hx2 := pow_le_pow_left₀ (show 0≤x by linarith [hx.1]) hx.2 2
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  norm_num at hs0
  refine ⟨?_,?_,?_⟩ <;> linarith [hx.2]

theorem Hminus_antitone : AntitoneOn Hminus (Icc (3/10:ℝ) (3/5)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (Hminus_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => Hminus_deriv x
  · intro x hx
    have ht := short_trig (Ioo_subset_Icc_self hx)
    linarith

theorem Hplus_monotone : MonotoneOn Hplus (Icc (3/10:ℝ) (3/5)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (Hplus_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => Hplus_deriv x
  · intro x hx
    have ht := short_trig (Ioo_subset_Icc_self hx)
    linarith

theorem short_lower {x : ℝ} (hx : x∈Icc (3/10:ℝ) (3/5)) :
    (91/100:ℝ)< min (Hminus x) (Hplus x) := by
  have hm := Hminus_antitone hx ⟨by norm_num,le_rfl⟩ hx.2
  have hp := Hplus_monotone ⟨le_rfl,by norm_num⟩ hx hx.1
  have ht := short_trig (show (3/5:ℝ)∈Icc (3/10:ℝ) (3/5) by constructor <;> norm_num)
  have hc0 := Real.one_sub_sq_div_two_le_cos (x := (3/10:ℝ))
  have hs0 := Real.sin_ge_sub_cube (show (0:ℝ)≤3/10 by norm_num)
  have hleft : (1:ℝ)<Hminus (3/5) := by
    dsimp [Hminus,shortConstant,sourceFloor,u,v,g]
    linarith [ht.2.1,ht.2.2]
  have hright : (121/125:ℝ)<Hplus (3/10) := by
    dsimp [Hplus,shortConstant,sourceFloor,u,v,g]
    norm_num at hc0 hs0
    linarith
  apply lt_min <;> linarith

def capK (x : ℝ) : ℝ := 1+Real.sin x+Real.cos x/12
def capY (x : ℝ) : ℝ := Real.sqrt (Q0-(capK x)^2)
def capB (x : ℝ) : ℝ := capY x-1/2
def capD (x : ℝ) : ℝ := capK x*(-Real.cos x+Real.sin x/12)/capY x
def J (x : ℝ) : ℝ := x-4119/5000-v*capB x

theorem sine_second_antitone : AntitoneOn Real.sin (Icc (Real.pi/2) Real.pi) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (Real.hasDerivAt_sin x).continuousAt.continuousWithinAt
  · exact fun x _ => Real.hasDerivAt_sin x
  · exact fun x hx => (second_signs (Ioo_subset_Icc_self hx)).2

theorem rounded_trig {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    (887/1000:ℝ)<Real.sin x ∧ Real.sin x<947/1000 ∧
      (8/25:ℝ)< -Real.cos x ∧ -Real.cos x<231/500 := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hsecond := FrameCoreLowCancellation.second_trig ⟨hxq.1,hx.2⟩
  have hs := sine_second_antitone
    (show (19/10:ℝ)∈Icc (Real.pi/2) Real.pi by
      constructor <;> linarith [Arithmetic.pi_hand_enclosure.2,FrameLowPair.pi_lower])
    hxq hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤19/10)
    hxq.2 hx.1
  exact ⟨hsecond.1,hs.trans_lt trig_nineteen_tenths.2.1,
    by linarith [trig_nineteen_tenths.2.2.2],by linarith [hsecond.2.1]⟩

theorem capK_bounds {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    (3697/2000:ℝ)<capK x ∧ capK x<1921/1000 := by
  have ht := rounded_trig hx
  dsimp [capK]
  constructor <;> linarith

theorem cap_radicand_pos {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    0<Q0-(capK x)^2 := by
  have hk := capK_bounds hx
  norm_num [Q0]
  nlinarith

theorem capY_bounds {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    0<capY x ∧ capY x<73/100 := by
  have hk := capK_bounds hx
  have hy0 : 0<capY x := Real.sqrt_pos.mpr (cap_radicand_pos hx)
  have hysq : (capY x)^2=Q0-(capK x)^2 := Real.sq_sqrt (cap_radicand_pos hx).le
  refine ⟨hy0,?_⟩
  norm_num [Q0] at hysq
  nlinarith

theorem capK_deriv (x : ℝ) : HasDerivAt capK (Real.cos x-Real.sin x/12) x := by
  have h := ((Real.hasDerivAt_sin x).const_add 1).fun_add
    ((Real.hasDerivAt_cos x).div_const 12)
  have e : Real.cos x-Real.sin x/12=Real.cos x+-Real.sin x/12 := by ring
  rw [e]
  exact h

theorem capB_deriv {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    HasDerivAt capB (capD x) x := by
  have hd := ((hasDerivAt_const x Q0).sub ((capK_deriv x).pow 2)).sqrt
    (cap_radicand_pos hx).ne'
  convert hd.sub_const (1/2) using 1
  · rfl
  · dsimp [capD,capY]
    ring

theorem cap_gain {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) : 1<v*capD x := by
  have ht := rounded_trig hx
  have hk := capK_bounds hx
  have hy := capY_bounds hx
  have hs : (8/25:ℝ)+(887/1000)/12< -Real.cos x+Real.sin x/12 := by linarith
  have hprod := mul_lt_mul'' hk.1 hs (by norm_num) (by norm_num)
  have hscaled := mul_lt_mul_of_pos_left hprod (show 0<v by norm_num [v])
  have hn : capY x<v*(capK x*(-Real.cos x+Real.sin x/12)) := by
    dsimp only [v] at hscaled ⊢
    linarith [hy.2]
  dsimp [capD]
  rw [← mul_div_assoc,lt_div_iff₀ hy.1]
  linarith

theorem J_deriv {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    HasDerivAt J (1-v*capD x) x := by
  exact ((hasDerivAt_id x).sub_const (4119/5000)).sub ((capB_deriv hx).const_mul v)

theorem J_antitone : AntitoneOn J (Icc (19/10:ℝ) (41/20)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (J_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => J_deriv (Ioo_subset_Icc_self hx)
  · exact fun x hx => by linarith [cap_gain (Ioo_subset_Icc_self hx)]

theorem J_lower {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) : (39/40:ℝ)<J x := by
  have hm := J_antitone hx ⟨by norm_num,le_rfl⟩ hx.2
  have hy := capY_bounds (show (41/20:ℝ)∈Icc (19/10:ℝ) (41/20) by
    constructor <;> norm_num)
  have he : (39/40:ℝ)<J (41/20) := by
    dsimp [J,capB,v]
    linarith [hy.2]
  exact he.trans_le hm

end SquaresInCircles.Eight.FrameCoreLowLowScalars
end
end
end

section
/-!
## The complete original low-source primary witness

The short interval uses the actual core equation and one completed square.
The remaining straight-side and negative-tangent cases use cancellation
with the exact low endpoint.  A positive rounded-core target forces an
actual circle cap, whose scalar envelope is proved on its whole interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreLowLowPrimary
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g K)
open FrameCoreLowGeometry FrameCoreLowLowScalars

def CancellationSide (k : Bool) (a B : ℝ) : Prop :=
  k=false ∨ (a=7/12 ∧ B≤1/2)

theorem side_linear_lower {w B : ℝ} (hB : B∈Icc (0:ℝ) (1/2)) :
    min (w/2) (-w/2)≤w*B := by
  by_cases hw : 0≤w
  · have hp := mul_nonneg hw hB.1
    exact (min_le_right _ _).trans (by linarith)
  · have hh := mul_le_mul_of_nonpos_left hB.2 (le_of_not_ge hw)
    exact (min_le_left _ _).trans (by linarith)

theorem corner_quadratic {a B : ℝ} (hc : CoreState a B) (hB : 1/2≤B) :
    6*(B-1/2)^2≤7/12-a := by
  rcases hc with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
  · have he : B=1/2 := by linarith
    rw [he]
    norm_num
  · have ha := CorePairGeometry.corner_geometry hb hab hcircle
    have hprod := mul_nonneg (show 0≤7/12-a by linarith [ha.2.1])
      (show 0≤7/12-a by linarith [ha.2.1])
    nlinarith

theorem short_target (k : Bool) {a B x : ℝ}
    (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/10:ℝ) (3/5)) :
    3*(7/12)*Real.cos x+min ((g-3*Real.sin x)/2) (-(g-3*Real.sin x)/2)-1/200≤
      -sign k*coreLabel a B+3*a*Real.cos x+3*sign k*B*Real.sin x := by
  have hcore := core_bounds hc
  have ht := short_trig hx
  have hc1 := Real.cos_le_one x
  have hlow : g-9/5≤g-3*Real.sin x := by linarith [ht.2.1]
  cases k with
  | false =>
      by_cases hBside : B≤1/2
      · have ha : a=7/12 := by
          rcases hc with ⟨ha,_,_⟩ | ⟨hb,hab,hcircle⟩
          · exact ha
          · have he : B=1/2 := by linarith
            rw [he] at hcircle
            have hap : 1/2<a := by
              linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]
            nlinarith
        have hh := side_linear_lower (w := g-3*Real.sin x) ⟨hcore.2.2.1,hBside⟩
        dsimp [coreLabel,sign]
        rw [ha]
        nlinarith
      · have hB : 1/2≤B := (lt_of_not_ge hBside).le
        have hd : 0≤B-1/2 := sub_nonneg.mpr hB
        have he : 0≤7/12-a := sub_nonneg.mpr hcore.2.1
        have hquad := corner_quadratic hc hB
        have hcD : K-3≤K-3*Real.cos x := by linarith
        have heD := mul_le_mul_of_nonneg_right hcD he
        have hquadD := mul_le_mul_of_nonneg_left hquad (show 0≤K-3 by norm_num [K])
        have hwD := mul_le_mul_of_nonneg_right hlow hd
        have hsquare : -(1/200:ℝ)≤
            6*(K-3)*(B-1/2)^2+(g-9/5)*(B-1/2) := by
          have hs := sq_nonneg ((B-1/2)-(9/5-g)/(12*(K-3)))
          norm_num [K,g] at hs ⊢
          nlinarith
        have hm := min_le_left ((g-3*Real.sin x)/2) (-(g-3*Real.sin x)/2)
        dsimp [coreLabel,sign]
        nlinarith
  | true =>
      have ha : a=7/12 := by
        rcases hside with h | h
        · cases h
        · exact h.1
      have hB : B≤1/2 := by
        rcases hside with h | h
        · cases h
        · exact h.2
      have hh := side_linear_lower (w := -(g-3*Real.sin x)) ⟨hcore.2.2.1,hB⟩
      have hmin : min ((g-3*Real.sin x)/2) (-(g-3*Real.sin x)/2)=
          min (-(g-3*Real.sin x)/2) (-(-(g-3*Real.sin x))/2) := by
        rw [neg_neg,min_comm]
      rw [← hmin] at hh
      dsimp [coreLabel,sign]
      rw [ha]
      nlinarith

theorem short_source {b : ℝ} (hb : b∈Icc 0 b1) : sourceFloor< -L b-3*A b := by
  have hs := circle_linear_lower (A_circle ⟨hb.1,hb.2.trans b1_mem.2⟩) (-u-3) (-v)
  obtain ⟨N,hN⟩ : ∃ N, N=Real.sqrt ((-u-3)^2+(-v)^2) := ⟨_,rfl⟩
  rw [← hN] at hs
  have hroot : N<(1787/500:ℝ) := by
    rw [hN,Real.sqrt_lt' (by norm_num)]
    norm_num [u,v]
  have hN0 : 0≤N := hN ▸ Real.sqrt_nonneg _
  have hRN := mul_lt_mul' FrameCoreLowCorePrimary.radius_upper.le hroot hN0
    (by norm_num : (0:ℝ)<1979/1000)
  have hu : 0<u := by norm_num [u]
  have ha := mul_lt_mul_of_pos_left a0_bounds.1 hu
  dsimp [sourceFloor,L]
  linarith

theorem short_primary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/10:ℝ) (3/5)) (hm : 0≤lowCorePrimary k b a B x) :
    (91/100:ℝ)<lowCoreCost i k b a B x := by
  have hsource := short_source hb
  have hsign := FrameLowPair.minus_label_le i hb
  have htarget := short_target k hc hside hx
  have hw := first_width
    (show x∈Icc 0 (Real.pi/2) from
      ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  let base : ℝ := x-(9/50)*periodicFrameCost x+sourceFloor+
    3*pairWidth x+3*(7/12)*Real.cos x-1/200
  have he0 : base+(g-3*Real.sin x)/2=Hminus x := by
    dsimp [base,Hminus,shortConstant]
    rw [hw.1,hw.2]
    ring
  have he1 : base+(-(g-3*Real.sin x)/2)=Hplus x := by
    dsimp [base,Hplus,shortConstant]
    rw [hw.1,hw.2]
    ring
  have h0 := (short_lower hx).trans_le (min_le_left (Hminus x) (Hplus x))
  have h1 := (short_lower hx).trans_le (min_le_right (Hminus x) (Hplus x))
  have hmin : (91/100:ℝ)-base<
      min ((g-3*Real.sin x)/2) (-(g-3*Real.sin x)/2) := by
    apply lt_min <;> linarith
  dsimp [base,lowCoreCost,lowCorePrimary] at *
  nlinarith

theorem cancellation_target (k : Bool) {a B x : ℝ}
    (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/5:ℝ) (41/20)) :
    (g/Real.sin x)*(7/12)*Real.cos x≤
      -sign k*coreLabel a B+(g/Real.sin x)*a*Real.cos x+
        (g/Real.sin x)*sign k*B*Real.sin x := by
  have hs := FrameCoreLowCancellation.interval_sine hx
  have hs0 : 0<Real.sin x := by linarith
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hlamU : g/Real.sin x<2 := (div_lt_iff₀ hs0).2 (by dsimp [g]; linarith)
  have hclam := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hlam0
  have hcan : (g/Real.sin x)*Real.sin x=g := div_mul_cancel₀ _ hs0.ne'
  cases k with
  | false =>
      have ht := positive_support (r := -(g/Real.sin x)*Real.cos x)
        (z := (g/Real.sin x)*Real.sin x) hc
        (by dsimp [K]; nlinarith) (by rw [hcan])
      have hsg : sign false=-1 := rfl
      rw [hsg]
      linarith
  | true =>
      have ha : a=7/12 := by
        rcases hside with h | h
        · cases h
        · exact h.1
      subst a
      have hcB : (g/Real.sin x)*1*B*Real.sin x=g*B := by
        rw [mul_one,mul_right_comm,hcan]
      dsimp [coreLabel,sign]
      linarith

theorem cancellation_source_antitone {x : ℝ} (hx : x∈Icc (3/5:ℝ) (41/20)) :
    AntitoneOn (linear (-u-g/Real.sin x) (-v)) (Icc 0 b1) := by
  have hs := FrameCoreLowCancellation.interval_sine hx
  have hs0 : 0<Real.sin x := by linarith
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hlamU : g/Real.sin x<(1911/1000:ℝ) :=
    (div_lt_iff₀ hs0).2 (by dsimp [g]; linarith)
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => (linear_hasDerivAt ⟨hb.1,hb.2.trans b1_mem.2⟩ _
      _).continuousAt.continuousWithinAt
  · exact fun b hb => linear_hasDerivAt ⟨hb.1.le,hb.2.le.trans b1_mem.2⟩ _ _
  · intro b hb
    have hr := slope_bounds (Ioo_subset_Icc_self hb)
    have hm := mul_le_mul_of_nonneg_left hr.2.le
      (show 0≤u+g/Real.sin x by dsimp [u]; linarith)
    have hAd : Ad b=-FrameLowArc.slope b := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [hAd]
    dsimp only [u,v] at hm ⊢
    linarith

theorem cancellation_endpoint (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/5:ℝ) (41/20)) (hm : 0≤lowCorePrimary k b a B x) :
    FrameCoreLowCancellation.G x≤lowCoreCost i k b a B x := by
  have hs := FrameCoreLowCancellation.interval_sine hx
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) (by linarith)
  have hscaled := mul_nonneg hlam0 hm
  have hsource := cancellation_source_antitone hx hb ⟨b1_mem.1,le_rfl⟩ hb.2
  dsimp [linear] at hsource
  rw [A_b1] at hsource
  have hsign := FrameLowPair.minus_label_le i hb
  have htarget := cancellation_target k hc hside hx
  dsimp [FrameCoreLowCancellation.G,FrameCoreMidScalars.ac,
    lowCoreCost,lowCorePrimary,L,L1] at *
  nlinarith

theorem cancellation_primary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hside : CancellationSide k a B)
    (hx : x∈Icc (3/10:ℝ) (41/20)) (hm : 0≤lowCorePrimary k b a B x) :
    (91/100:ℝ)<lowCoreCost i k b a B x := by
  by_cases hshort : x≤3/5
  · exact short_primary i k hb hc hside ⟨hx.1,hshort⟩ hm
  · have hdom : x∈Icc (3/5:ℝ) (41/20) := ⟨(lt_of_not_ge hshort).le,hx.2⟩
    exact (FrameCoreLowCancellation.G_lower hdom).trans_le
      (cancellation_endpoint i k hb hc hside hdom hm)

theorem rounded_primary_quadrant_false {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤lowCorePrimary true b a B x) : False := by
  have hcore := core_bounds hc
  have hlow := low_bounds hb
  have ht := FrameLowPair.quadrant hx
  have hA := mul_le_mul_of_nonneg_right
    (show (1/2:ℝ)≤a by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]) ht.2.2.1
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  have hw := (first_width hx).1
  have hsc : 1≤Real.sin x+Real.cos x := by linarith [width_one_le x]
  dsimp [lowCorePrimary,sign] at hm
  rw [hw] at hm
  nlinarith

theorem rounded_primary_cap {b a B x : ℝ}
    (hc : CoreState a B) (hB : 1/2≤B) (hx : x∈Icc (Real.pi/2) Real.pi)
    (hm : 0≤lowCorePrimary true b a B x) : capK x≤A b+1/2 := by
  have hcore := core_bounds hc
  have ht := second_signs hx
  have hA := mul_le_mul_of_nonpos_right hcore.2.1 ht.2
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  dsimp [lowCorePrimary,sign] at hm
  rw [(second_width hx).1] at hm
  dsimp [capK]
  nlinarith

theorem rounded_primary_cut {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/10:ℝ) (41/20)) (hm : 0≤lowCorePrimary true b a B x) :
    (19/10:ℝ)<x := by
  by_contra! hsmall
  by_cases hfirst : x≤Real.pi/2
  · exact rounded_primary_quadrant_false hb hc hB ⟨by linarith [hx.1],hfirst⟩ hm
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hfirst).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hcap := rounded_primary_cap hc hB hxq hm
    have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
      (by linarith [FrameLowPair.pi_lower] : (19/10:ℝ)≤Real.pi)
      (show x∈Icc (Real.pi/2) (19/10:ℝ) from ⟨hxq.1,hsmall⟩)
      (by rw [Real.sin_pi_div_two]; norm_num : (473/500:ℝ)<Real.sin (Real.pi/2))
      FrameCoreLowCorePrimary.trig_nineteen_tenths.1
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hsmall
    have ha := (A_low_bounds hb).2
    dsimp [capK] at hcap
    linarith [FrameCoreLowCorePrimary.trig_nineteen_tenths.2.2.1,a0_bounds.2]

theorem rounded_tangent_cap {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (19/10:ℝ) (41/20)) (hm : 0≤lowCorePrimary true b a B x) :
    b≤capB x := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hcap := rounded_primary_cap hc hB hxq hm
  have hk := capK_bounds hx
  have hy := capY_bounds hx
  have hs : (capY x)^2=Q0-(capK x)^2 := Real.sq_sqrt (cap_radicand_pos hx).le
  have hcircle := A_circle ⟨hb.1,hb.2.trans b1_mem.2⟩
  have hA := pow_le_pow_left₀ (show 0≤capK x by linarith [hk.1]) hcap 2
  have hbp : 0≤b+1/2 := by linarith [hb.1]
  dsimp [capB]
  nlinarith

theorem rounded_primary (i : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/10:ℝ) (41/20)) (hm : 0≤lowCorePrimary true b a B x) :
    (91/100:ℝ)<lowCoreCost i true b a B x := by
  have hcut := rounded_primary_cut hb hc hB hx hm
  have hdom : x∈Icc (19/10:ℝ) (41/20) := ⟨hcut.le,hx.2⟩
  have hcap := rounded_tangent_cap hb hc hB hdom hm
  have hlabel := (low_label_linear hb).2
  have hscaled := mul_le_mul_of_nonneg_left hcap (show 0≤v by norm_num [v])
  have hsource := FrameLowPair.minus_label_le i hb
  have htarget := (label_bounds hc).2
  have hch := CorePairGeometry.charge_upper x
  have hscalar := J_lower hdom
  dsimp [lowCoreCost,J,sign] at *
  nlinarith

theorem low_primary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B)
    (hx : x∈Icc (-(3/10:ℝ)) (41/20)) (hm : 0≤lowCorePrimary k b a B x) :
    (91/100:ℝ)<lowCoreCost i k b a B x := by
  have hcut := low_primary_angle k hb hc hx.1 hm
  have hdom : x∈Icc (3/10:ℝ) (41/20) := ⟨hcut.le,hx.2⟩
  cases k with
  | false => exact cancellation_primary i false hb hc (Or.inl rfl) hdom hm
  | true =>
      by_cases hB : B<1/2
      · have ha := (label_side hc hB).1
        exact cancellation_primary i true hb hc (Or.inr ⟨ha,hB.le⟩) hdom hm
      · exact rounded_primary i hb hc (le_of_not_gt hB) hdom hm

end SquaresInCircles.Eight.FrameCoreLowLowPrimary
end
end
end

section
/-!
## The original core/low secondary witnesses

The multiplier acts on the actual weak margin.  The negative low tangent
is handled by the two arc endpoints; the positive tangent uses the whole
circle support followed by an antitone arc functional.  A low source
secondary witness has already been excluded for all original signs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreLowSecondary
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreLowGeometry FrameCoreLowEndpoint

def negativeAxial (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-g*a0*Real.sin x+g*pairWidth x
def negativeEndpoint (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+L1-g*a1*Real.sin x-g*b1*Real.cos x+g*pairWidth x
def positiveEndpoint (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-L1-g*a1*Real.sin x+g*b1*Real.cos x+g*pairWidth x

theorem negativeAxial_lower {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    (91/100:ℝ)<negativeAxial x := by
  by_cases hq : x≤Real.pi/2
  · have hw := first_width ⟨hx.1,hq⟩
    have he : negativeAxial x=axial x := by
      dsimp [negativeAxial,axial,axialB,FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact axial_lower ⟨hx.1,hq⟩
  · have hw := second_width ⟨(lt_of_not_ge hq).le,hx.2⟩
    have he : negativeAxial x=axialSecond x := by
      dsimp [negativeAxial,axialSecond,axialB,FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact axialSecond_lower ⟨(lt_of_not_ge hq).le,hx.2⟩

theorem negativeEndpoint_lower {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    (91/100:ℝ)<negativeEndpoint x := by
  by_cases hq : x≤Real.pi/2
  · have hw := first_width ⟨hx.1,hq⟩
    have he : negativeEndpoint x=negativeCut x := by
      dsimp [negativeEndpoint,negativeCut,cutB,FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact negativeCut_lower ⟨hx.1,hq⟩
  · have hw := second_width ⟨(lt_of_not_ge hq).le,hx.2⟩
    have he : negativeEndpoint x=negativeCutSecond x := by
      dsimp [negativeEndpoint,negativeCutSecond,cutB,
        FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact negativeCutSecond_lower ⟨(lt_of_not_ge hq).le,hx.2⟩

theorem negative_target_endpoints {B x : ℝ} (hB : B∈Icc 0 b1) :
    min (linear (u-g*Real.sin x) (v-g*Real.cos x) 0)
      (linear (u-g*Real.sin x) (v-g*Real.cos x) b1)≤
        linear (u-g*Real.sin x) (v-g*Real.cos x) B := by
  by_cases hp : 0≤u-g*Real.sin x
  · exact linear_endpoint_lower hp (by norm_num) b1_mem.2 hB
  · have hq : 0≤v-g*Real.cos x := by
      have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one x) (show 0≤g by norm_num [g])
      dsimp [g,v] at *
      linarith
    exact (min_le_left _ _).trans (linear_monotone (le_of_not_ge hp) hq
      ⟨le_rfl,b1_mem.1.trans b1_mem.2⟩ ⟨hB.1,hB.2.trans b1_mem.2⟩ hB.1)

theorem core_secondary_negative (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : x∈Icc 0 Real.pi)
    (hm : 0≤coreLowSecondary i false a b B x) :
    (91/100:ℝ)<coreLowCost i false a b B x := by
  have hs := core_secondary_source_floor i false hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have ht := negative_target_endpoints (x := x) hB
  have h0 := negativeAxial_lower hx
  have h1 := negativeEndpoint_lower hx
  obtain ⟨base,hbase⟩ : ∃ base : ℝ, base=x-(9/50)*periodicFrameCost x-u*a0+g*pairWidth x :=
    ⟨_,rfl⟩
  have he0 : base+linear (u-g*Real.sin x) (v-g*Real.cos x) 0=negativeAxial x := by
    rw [hbase]
    dsimp [linear,negativeAxial]
    rw [A_zero]
    ring
  have he1 : base+linear (u-g*Real.sin x) (v-g*Real.cos x) b1=negativeEndpoint x := by
    rw [hbase]
    dsimp [linear,negativeEndpoint,L1]
    rw [A_b1]
    ring
  have hmin : (91/100:ℝ)-base<
      min (linear (u-g*Real.sin x) (v-g*Real.cos x) 0)
        (linear (u-g*Real.sin x) (v-g*Real.cos x) b1) := by
    apply lt_min <;> linarith
  have hh := hmin.trans_le ht
  rw [hbase] at hh
  dsimp only [linear,coreLowCost,coreLowSecondary,L] at hh hscaled hm ⊢
  simp only [sign,Bool.false_eq_true,↓reduceIte] at hs hscaled hm ⊢
  linarith

theorem core_secondary_full_circle (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : x∈Icc 0 (6/5:ℝ))
    (hm : 0≤coreLowSecondary i true a b B x) :
    FrameCoreLowNorm.F x≤coreLowCost i true a b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := core_secondary_source_floor i true hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have ht := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (-u-g*Real.sin x) (g*Real.cos x-v)
  have hn : Real.sqrt ((-u-g*Real.sin x)^2+(g*Real.cos x-v)^2)=
      FrameCoreLowNorm.N x := by
    unfold FrameCoreLowNorm.N
    congr 1
    linear_combination g^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  have hw := first_width hxq
  dsimp [coreLowSecondary,coreLowCost,FrameCoreLowNorm.F,L] at *
  simp only [sign,ite_true,one_mul] at *
  rw [hw.1] at hscaled
  rw [hw.2]
  nlinarith

theorem positive_target_antitone {x : ℝ} (hx : x∈Icc (6/5:ℝ) (41/20)) :
    AntitoneOn (linear (-u-g*Real.sin x) (g*Real.cos x-v)) (Icc 0 b1) := by
  have hs : 0≤Real.sin x := by
    linarith [FrameCoreLowCancellation.interval_sine
      (show x∈Icc (3/5:ℝ) (41/20) from ⟨by linarith [hx.1],hx.2⟩)]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤6/5)
    (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  have hcU : Real.cos x≤363/1000 := by
    linarith [FrameCoreMidScalars.trig_six_fifths.2.2.2]
  have hp : 0≤u+g*Real.sin x := by
    have hh := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hs
    dsimp [u]
    linarith
  apply antiOn_of_hasDeriv_nonpos
  · exact fun B hB => (linear_hasDerivAt ⟨hB.1,hB.2.trans b1_mem.2⟩ _
      _).continuousAt.continuousWithinAt
  · exact fun B hB => linear_hasDerivAt ⟨hB.1.le,hB.2.le.trans b1_mem.2⟩ _ _
  · intro B hB
    have hr := slope_bounds (Ioo_subset_Icc_self hB)
    have hm := mul_le_mul_of_nonneg_left hr.2.le hp
    have hsin := mul_le_mul_of_nonneg_left (Real.sin_le_one x)
      (show (0:ℝ)≤(23/50)*g by norm_num [g])
    have hcos := mul_le_mul_of_nonneg_left hcU (show (0:ℝ)≤g by norm_num [g])
    have hAd : Ad B=-FrameLowArc.slope B := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [hAd]
    dsimp only [u,v,g] at hm hsin hcos ⊢
    linarith

theorem core_secondary_endpoint (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : x∈Icc (6/5:ℝ) (41/20))
    (hm : 0≤coreLowSecondary i true a b B x) :
    positiveEndpoint x≤coreLowCost i true a b B x := by
  have hs := core_secondary_source_floor i true hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have ht := positive_target_antitone hx hB ⟨b1_mem.1,le_rfl⟩ hB.2
  dsimp [linear] at ht
  rw [A_b1] at ht
  dsimp [positiveEndpoint,coreLowCost,coreLowSecondary,L,L1] at *
  simp only [sign,ite_true,one_mul] at *
  nlinarith

theorem positiveEndpoint_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (41/20)) :
    (91/100:ℝ)<positiveEndpoint x := by
  by_cases hq : x≤Real.pi/2
  · have hw := first_width ⟨by linarith [hx.1],hq⟩
    have he : positiveEndpoint x=positiveCut x := by
      dsimp [positiveEndpoint,positiveCut,cutB,
        FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact positiveCut_lower ⟨hx.1,hq⟩
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hq).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hw := second_width hxq
    have he : positiveEndpoint x=positiveCutSecond x := by
      dsimp [positiveEndpoint,positiveCutSecond,cutB,
        FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact positiveCutSecond_lower hxq

theorem core_secondary_positive (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : x∈Icc 0 (41/20:ℝ))
    (hm : 0≤coreLowSecondary i true a b B x) :
    (91/100:ℝ)<coreLowCost i true a b B x := by
  by_cases hcut : x≤6/5
  · have hdom : x∈Icc 0 (6/5:ℝ) := ⟨hx.1,hcut⟩
    exact (FrameCoreLowNorm.full_circle_lower hdom).trans_le
      (core_secondary_full_circle i hc hB hdom hm)
  · have hdom : x∈Icc (6/5:ℝ) (41/20) := ⟨(lt_of_not_ge hcut).le,hx.2⟩
    exact (positiveEndpoint_lower hdom).trans_le (core_secondary_endpoint i hc hB hdom hm)

theorem core_secondary (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : x∈Icc (-(3/10:ℝ)) (41/20))
    (hm : 0≤coreLowSecondary i k a b B x) :
    (91/100:ℝ)<coreLowCost i k a b B x := by
  have hx0 := core_secondary_angle i k hc hB hx.1 hm
  cases k with
  | false =>
    exact core_secondary_negative i hc hB
      ⟨hx0.le,by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm
  | true => exact core_secondary_positive i hc hB ⟨hx0.le,hx.2⟩ hm

end SquaresInCircles.Eight.FrameCoreLowSecondary
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreLowPair
open FramePair FrameCircleArc FrameLowArc FrameCoreArc
open FrameCoreLowGeometry FrameCoreLowSecondary FrameCoreLowCorePrimary FrameCoreLowLowPrimary

theorem core_low_angle (s t : FramePair.State)
    (ht : t.branch=.low) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(3/10:ℝ)<x := by
  have hs := s.offset_range
  have hh := low_offset_bounds t ht
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem low_core_angle (s t : FramePair.State)
    (hs : s.branch=.low) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(3/10:ℝ)<x := by
  have ht := t.offset_range
  have hh := low_offset_bounds s hs
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem state_core_low_cost (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.low) (x : ℝ) :
    s.cost t x=coreLowCost s.positive t.positive s.a s.b t.b x := by
  rw [State.cost,state_core_label s hs,state_low_label t ht]
  rfl

theorem state_low_core_cost (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch.type=0) (x : ℝ) :
    s.cost t x=lowCoreCost s.positive t.positive s.b t.a t.b x := by
  rw [State.cost,state_low_label s hs,state_core_label t ht]
  rfl

theorem state_core_low_secondary (s t : FramePair.State)
    (ht : t.branch=.low) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤coreLowSecondary s.positive t.positive s.a s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,(state_low_chart t ht).1]
  rfl

theorem state_core_low_primary (s t : FramePair.State)
    (ht : t.branch=.low) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤coreLowPrimary t.positive s.a t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_low_chart t ht).1]
  rfl

theorem state_low_core_secondary (s t : FramePair.State) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤lowCoreSecondary s.positive t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero]
  rfl

theorem state_low_core_primary (s t : FramePair.State)
    (hs : s.branch=.low) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤lowCorePrimary t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_low_chart s hs).1]
  rfl

theorem source_core_secondary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (91/100:ℝ)<s.cost t x := by
  have hcore := state_core_chart s hs
  have hlow := (state_low_chart t ht).2
  rw [state_core_low_cost s t hs ht]
  by_cases hlarge : (41/20:ℝ)≤x
  · exact core_low_tail s.positive t.positive hcore hlow hlarge
  · exact core_secondary s.positive t.positive hcore hlow
      ⟨(core_low_angle s t ht hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_low_secondary s t ht x).mp hm)

theorem source_core_primary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (91/100:ℝ)<s.cost t x := by
  have hcore := state_core_chart s hs
  have hlow := (state_low_chart t ht).2
  rw [state_core_low_cost s t hs ht]
  by_cases hlarge : (41/20:ℝ)≤x
  · exact core_low_tail s.positive t.positive hcore hlow hlarge
  · exact core_primary s.positive t.positive hcore hlow
      ⟨(core_low_angle s t ht hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_low_primary s t ht x).mp hm)

theorem source_low_secondary (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch.type=0) {x : ℝ}
    (hm : s.Feasible t 0 x) : False := by
  exact low_secondary_false s.positive t.positive (state_low_chart s hs).2
    (state_core_chart t ht) ((state_low_core_secondary s t x).mp hm)

theorem source_low_primary (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch.type=0) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (91/100:ℝ)<s.cost t x := by
  have hlow := (state_low_chart s hs).2
  have hcore := state_core_chart t ht
  rw [state_low_core_cost s t hs ht]
  by_cases hlarge : (41/20:ℝ)≤x
  · exact low_core_tail s.positive t.positive hlow hcore hlarge
  · exact low_primary s.positive t.positive hlow hcore
      ⟨(low_core_angle s t hs hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_low_core_primary s t hs x).mp hm)

/-- Every original weak forward witness in the core-to-low orientation. -/
theorem core_low_pair (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.low) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(91/100:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_core_secondary s t hs ht hgap hm
  · have hh := source_low_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · exact (source_low_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      ((s.target_secondary_reverse t x).mp hm)).elim
  · exact source_core_primary s t hs ht hgap hm

/-- Every original weak forward witness in the low-to-core orientation. -/
theorem low_core_pair (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch.type=0) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(91/100:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact (source_low_secondary s t hs ht hm).elim
  · have hh := source_core_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_core_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_low_primary s t hs ht hgap hm

theorem core_low_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : (branchOf C i).type=0) (hj : branchOf C (next i)=.low)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact core_low_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem low_core_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.low) (hj : (branchOf C (next i)).type=0)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact low_core_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.FrameCoreLowPair
end
end
end
