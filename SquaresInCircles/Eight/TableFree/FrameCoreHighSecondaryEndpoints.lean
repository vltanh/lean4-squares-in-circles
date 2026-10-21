module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighSecondaryScalars

/-!
# The actual high-arc endpoint supports for a core transverse axis

The two endpoint coordinates are the middle/high cut and the diagonal.
Their positive-target supports have endpoint minima because the negative
first derivative is concave.  The negative-angle supports are concave
directly.  The negative-target continuation uses the actual high cut.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighSecondaryEndpoints
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
        have hp : 0≤min (-d x) (-d u) := le_min (by linarith) (by linarith)
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
        have hp : 0≤min (-d t) (-d u) := le_min (by linarith) (by linarith)
        exact hdx (by linarith)
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)

theorem cut_coefficients :
    (501/500:ℝ)<D false ∧ D false<1003/1000 ∧
      (843/1000:ℝ)<B false ∧ B false<211/250 ∧ endpointH false<58/125 := by
  have ha := a2_bounds
  have hb := b2_bounds
  have hh := H2_bounds.2
  dsimp [D,B,endpointA,endpointB,endpointH,cp,g] at *
  repeat' constructor <;> linarith

theorem diagonal_coefficients :
    (1417/1000:ℝ)<D true ∧ D true<709/500 ∧
      (13/25:ℝ)<B true ∧ B true<521/1000 ∧ endpointH true<393/500 := by
  have hd := FrameHighArc.diagonal_bounds
  have hp := Arithmetic.pi_hand_enclosure.2
  dsimp [D,B,endpointA,endpointB,endpointH,cp,g] at *
  repeat' constructor <;> linarith

theorem coefficient_lower (r : Bool) :
    1<D r ∧ (51/100:ℝ)<B r ∧ (7/5:ℝ)<C r := by
  have he : C r=B r+2*cp := by dsimp [B,C]; ring
  cases r
  · have hh := cut_coefficients
    norm_num [cp,g] at he
    repeat' constructor <;> linarith
  · have hh := diagonal_coefficients
    norm_num [cp,g] at he
    repeat' constructor <;> linarith

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
    dsimp [positiveFirst,positiveFirstD] <;> ring

theorem positiveFirst_negative_derivative_concave (r : Bool) :
    ConcaveOn ℝ (Icc (0:ℝ) (7/5)) (fun x => -positiveFirstD r x) := by
  apply concave_of_deriv2
    (f' := fun x => D r*Real.cos x-B r*Real.sin x)
    (f'' := fun x => -D r*Real.sin x-B r*Real.cos x)
  · intro x _
    convert ((((Real.hasDerivAt_sin x).const_mul (D r)).add
      ((Real.hasDerivAt_cos x).const_mul (B r))).sub_const 1) using 1 <;>
      dsimp [positiveFirstD] <;> ring
  · intro x _
    convert ((Real.hasDerivAt_cos x).const_mul (D r)).sub
      ((Real.hasDerivAt_sin x).const_mul (B r)) using 1 <;> ring
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
      ((Real.hasDerivAt_cos z).const_mul (C r)) using 1 <;> ring
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
    convert ((Real.hasDerivAt_sin z).const_mul (B true)).add
      ((Real.hasDerivAt_cos z).const_mul (D true)) using 1 <;> dsimp [diagonalPulse] <;> ring
  · intro z _
    convert ((Real.hasDerivAt_cos z).const_mul (B true)).sub
      ((Real.hasDerivAt_sin z).const_mul (D true)) using 1 <;> ring
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
  convert (((((hasDerivAt_id z).neg).add_const ap).add_const (Real.pi/4)).add
    ((Real.hasDerivAt_cos z).const_mul (cp-g*c0))).add
      ((Real.hasDerivAt_sin z).const_mul (cp+g*c0)) using 1 <;>
    dsimp [negativeDiagonal,diagonalPulse,B,D,endpointA,endpointB] <;> ring

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
  have ha : -(53/500:ℝ)<a ∧ a<-(13/125:ℝ) := by
    have he : a=2*cp-D false := by dsimp [a,D,endpointB]; ring
    norm_num [cp,g] at he
    constructor <;> linarith [cut_coefficients.1,cut_coefficients.2.1]
  have hb : -(211/250:ℝ)<b ∧ b<-(843/1000:ℝ) := by
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

end SquaresInCircles.Eight.TableFree.FrameCoreHighSecondaryEndpoints
