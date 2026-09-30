module
public import SquaresInCircles.Six.ProofTools.RationalInterval
public import SquaresInCircles.Six.ProofTools.Taylor
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# Sound trigonometric interval evaluation

A midpoint is only an expansion center, never a sampled proof. Its value is
bounded by the proved Taylor polynomials after an exact 2pi-period reduction;
the full input interval is covered by the global 1-Lipschitz inequalities for
sine and cosine. Critical points and intervals crossing zero need no special
sampling argument. The period-index heuristic affects sharpness, not soundness.
-/

namespace SquaresInCircles.Six.ProofTools
namespace RInterval

def piInterval : RInterval :=
  ⟨314159265358979323846/100000000000000000000,
   314159265358979323847/100000000000000000000⟩

lemma mem_piInterval : piInterval.Mem Real.pi := by
  constructor <;> norm_num [piInterval]
  · linarith [Real.pi_gt_d20]
  · linarith [Real.pi_lt_d20]

def polyInterval : List ℚ → RInterval → RInterval
  | [], _ => point 0
  | q :: qs, I => add (point q) (mul I (polyInterval qs I))

lemma mem_polyInterval {I : RInterval} {x : ℝ} (hx : I.Mem x) (qs : List ℚ) :
    (polyInterval qs I).Mem (evalPoly qs x) := by
  induction qs with
  | nil => exact mem_point 0
  | cons q qs ih => exact mem_add (mem_point q) (mem_mul hx ih)

private def positiveSin (I : RInterval) : RInterval :=
  ⟨(polyInterval sinLowerCoeffs (absolute I)).lo,
    (polyInterval sinUpperCoeffs (absolute I)).hi⟩

private def positiveCos (I : RInterval) : RInterval :=
  ⟨(polyInterval cosLowerCoeffs (absolute I)).lo,
    (polyInterval cosUpperCoeffs (absolute I)).hi⟩

private lemma mem_positiveSin {I : RInterval} {x : ℝ} (hx : I.Mem x) :
    (positiveSin I).Mem (Real.sin |x|) := by
  have hlo := mem_polyInterval (mem_absolute hx) sinLowerCoeffs
  have hhi := mem_polyInterval (mem_absolute hx) sinUpperCoeffs
  have hb := sin_taylor_bracket (abs_nonneg x)
  exact ⟨hlo.1.trans hb.1,hb.2.trans hhi.2⟩

private lemma mem_positiveCos {I : RInterval} {x : ℝ} (hx : I.Mem x) :
    (positiveCos I).Mem (Real.cos |x|) := by
  have hlo := mem_polyInterval (mem_absolute hx) cosLowerCoeffs
  have hhi := mem_polyInterval (mem_absolute hx) cosUpperCoeffs
  have hb := cos_taylor_bracket (abs_nonneg x)
  exact ⟨hlo.1.trans hb.1,hb.2.trans hhi.2⟩

def rawSin (I : RInterval) : RInterval :=
  let P := positiveSin I
  if 0 ≤ I.lo then P else if I.hi ≤ 0 then neg P else hull P (neg P)

def rawCos (I : RInterval) : RInterval := positiveCos I

lemma mem_rawSin {I : RInterval} {x : ℝ} (hx : I.Mem x) : (rawSin I).Mem (Real.sin x) := by
  have hp := mem_positiveSin hx
  unfold rawSin
  split_ifs with hl hh
  · have hx0 : 0 ≤ x := (by exact_mod_cast hl).trans hx.1
    simpa only [abs_of_nonneg hx0] using hp
  · have hx0 : x ≤ 0 := hx.2.trans (by exact_mod_cast hh)
    have hn := mem_neg hp
    simpa only [abs_of_nonpos hx0, Real.sin_neg, neg_neg] using hn
  · by_cases hx0 : 0 ≤ x
    · apply mem_hull_left
      simpa only [abs_of_nonneg hx0] using hp
    · apply mem_hull_right
      have hn := mem_neg hp
      simpa only [abs_of_neg (lt_of_not_ge hx0), Real.sin_neg, neg_neg] using hn

lemma mem_rawCos {I : RInterval} {x : ℝ} (hx : I.Mem x) : (rawCos I).Mem (Real.cos x) := by
  simpa only [Real.cos_abs] using mem_positiveCos hx

/-- Any integer is sound here; this choice keeps the polynomial argument small. -/
def periodIndex (m : ℚ) : ℤ :=
  ⌊m / (6283185307179586/1000000000000000 : ℚ) + 1/2⌋

def reduced (m : ℚ) : RInterval :=
  sub (point m) (mul (point (periodIndex m : ℚ)) (mul (point 2) piInterval))

lemma mem_reduced (m : ℚ) :
    (reduced m).Mem ((m : ℝ) - (periodIndex m : ℝ) * (2 * Real.pi)) := by
  have hh := mem_sub (mem_point m)
    (mem_mul (mem_point (periodIndex m : ℚ)) (mem_mul (mem_point 2) mem_piInterval))
  simpa using hh

def sinCenter (m : ℚ) : RInterval := rawSin (reduced m)
def cosCenter (m : ℚ) : RInterval := rawCos (reduced m)

lemma mem_sinCenter (m : ℚ) : (sinCenter m).Mem (Real.sin (m : ℝ)) := by
  simpa only [Real.sin_sub_int_mul_two_pi] using mem_rawSin (mem_reduced m)

lemma mem_cosCenter (m : ℚ) : (cosCenter m).Mem (Real.cos (m : ℝ)) := by
  simpa only [Real.cos_sub_int_mul_two_pi] using mem_rawCos (mem_reduced m)

def midpoint (I : RInterval) : ℚ := (I.lo+I.hi)/2
def radius (I : RInterval) : ℚ := (I.hi-I.lo)/2
def errorInterval (I : RInterval) : RInterval := ⟨-radius I,radius I⟩
def unitInterval : RInterval := ⟨-1,1⟩

def sine (I : RInterval) : RInterval :=
  meet (add (sinCenter (midpoint I)) (errorInterval I)) unitInterval

def cosine (I : RInterval) : RInterval :=
  meet (add (cosCenter (midpoint I)) (errorInterval I)) unitInterval

lemma abs_sub_midpoint_le {I : RInterval} {x : ℝ} (hx : I.Mem x) :
    |x - (midpoint I : ℝ)| ≤ (radius I : ℝ) := by
  apply abs_le.mpr
  constructor <;> dsimp [midpoint,radius] <;> push_cast <;> linarith [hx.1,hx.2]

lemma mem_sine {I : RInterval} {x : ℝ} (hx : I.Mem x) : (sine I).Mem (Real.sin x) := by
  have herror := (Real.abs_sin_sub_sin_le x (midpoint I)).trans (abs_sub_midpoint_le hx)
  have he : (errorInterval I).Mem (Real.sin x - Real.sin (midpoint I)) := by
    have ha := abs_le.mp herror
    simpa only [Mem, errorInterval, Rat.cast_neg] using ha
  apply mem_meet
  · have hh := mem_add (mem_sinCenter (midpoint I)) he
    have hid : Real.sin (midpoint I) + (Real.sin x - Real.sin (midpoint I)) = Real.sin x := by ring
    rwa [hid] at hh
  · exact ⟨Real.neg_one_le_sin x,Real.sin_le_one x⟩

lemma mem_cosine {I : RInterval} {x : ℝ} (hx : I.Mem x) : (cosine I).Mem (Real.cos x) := by
  have herror := (Real.abs_cos_sub_cos_le x (midpoint I)).trans (abs_sub_midpoint_le hx)
  have he : (errorInterval I).Mem (Real.cos x - Real.cos (midpoint I)) := by
    have ha := abs_le.mp herror
    simpa only [Mem, errorInterval, Rat.cast_neg] using ha
  apply mem_meet
  · have hh := mem_add (mem_cosCenter (midpoint I)) he
    have hid : Real.cos (midpoint I) + (Real.cos x - Real.cos (midpoint I)) = Real.cos x := by ring
    rwa [hid] at hh
  · exact ⟨Real.neg_one_le_cos x,Real.cos_le_one x⟩

end RInterval
end SquaresInCircles.Six.ProofTools
