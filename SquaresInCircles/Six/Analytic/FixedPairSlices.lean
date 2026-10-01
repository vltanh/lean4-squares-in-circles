import SquaresInCircles.Six.Analytic.FixedPairFormula
import SquaresInCircles.Six.Analytic.RotatingLength

/-!
# The coordinate and diagonal slices of the fixed pair

The only slice directions are the two coordinates and n=w. The data below
are exact rotating-vector identities for the four geometric source axes.
They are not sampled derivatives or a numerical partition.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress

structure Wave where
  rotor : ℝ
  baseSq : ℝ
  cosine : ℝ
  sine : ℝ

def Wave.constant (z : ℝ) : Wave := ⟨0,z,0,0⟩
def Wave.parameter (W : Wave) : ℝ := W.rotor^2+W.baseSq
def Wave.arg (W : Wave) (x : ℝ) : ℝ := harmonicArg W.parameter W.cosine W.sine x
def Wave.curvature (W : Wave) (R x : ℝ) : ℝ := harmonicCurvature R W.parameter W.cosine W.sine x

def sliceN (k : Fin 3) (n w x : ℝ) : ℝ := if k=1 then n else x
def sliceW (k : Fin 3) (n w x : ℝ) : ℝ := if k=0 then w else x

def northWave (no : Bool) (u : Fin 4) (k : Fin 3) (n w : ℝ) : Wave :=
  if k=0 then
    if no then
      ![⟨rStar,1,2*rStar*Real.sin w,-2*rStar*Real.cos w⟩,
        ⟨rStar,1,2*rStar*Real.cos w,2*rStar*Real.sin w⟩,
        .constant ((1+rStar)^2),.constant (1+rStar^2)] u
    else
      ![.constant (1+rStar^2+2*rStar*Real.sin w),
        .constant (1+rStar^2+2*rStar*Real.cos w),
        ⟨rStar,1,2*rStar,0⟩,⟨rStar,1,0,2*rStar⟩] u
  else if k=1 then
    if no then
      ![⟨rStar,1,-2*rStar*Real.sin n,2*rStar*Real.cos n⟩,
        ⟨rStar,1,2*rStar*Real.cos n,2*rStar*Real.sin n⟩,
        .constant ((1+rStar)^2),.constant (1+rStar^2)] u
    else
      ![⟨rStar,1,0,2*rStar⟩,⟨rStar,1,2*rStar,0⟩,
        .constant (1+rStar^2+2*rStar*Real.cos n),
        .constant (1+rStar^2+2*rStar*Real.sin n)] u
  else
    if no then
      ![.constant (1+rStar^2),.constant ((1+rStar)^2),
        .constant ((1+rStar)^2),.constant (1+rStar^2)] u
    else
      ![⟨rStar,1,0,2*rStar⟩,⟨rStar,1,2*rStar,0⟩,
        ⟨rStar,1,2*rStar,0⟩,⟨rStar,1,0,2*rStar⟩] u

def westWave (wo : Bool) (u : Fin 4) (k : Fin 3) (n w : ℝ) : Wave :=
  if k=0 then
    if wo then
      ![.constant ((1+rStar)^2+mStar^2),.constant (1+(mStar-rStar)^2),
        ⟨rStar,1+mStar^2,2*rStar*Real.sin w-2*rStar*mStar*Real.cos w,
          -2*rStar*Real.cos w-2*rStar*mStar*Real.sin w⟩,
        ⟨rStar,1+mStar^2,2*rStar*Real.cos w+2*rStar*mStar*Real.sin w,
          2*rStar*Real.sin w-2*rStar*mStar*Real.cos w⟩] u
    else
      ![.constant (1+rStar^2+mStar^2+2*rStar*Real.cos w+2*mStar*Real.sin w),
        .constant (1+(mStar-rStar)^2+2*(mStar-rStar)*Real.sin w),
        ⟨rStar,1+mStar^2+2*mStar*Real.sin w,-2*rStar*mStar*Real.cos w,
          -2*rStar-2*rStar*mStar*Real.sin w⟩,
        ⟨rStar,1+mStar^2+2*mStar*Real.sin w,2*rStar+2*rStar*mStar*Real.sin w,
          -2*rStar*mStar*Real.cos w⟩] u
  else if k=1 then
    if wo then
      ![.constant ((1+rStar)^2+mStar^2),.constant (1+(mStar-rStar)^2),
        ⟨rStar,1+mStar^2,-2*rStar*Real.sin n-2*rStar*mStar*Real.cos n,
          2*rStar*Real.cos n-2*rStar*mStar*Real.sin n⟩,
        ⟨rStar,1+mStar^2,2*rStar*Real.cos n-2*rStar*mStar*Real.sin n,
          2*rStar*Real.sin n+2*rStar*mStar*Real.cos n⟩] u
    else
      ![⟨1,rStar^2+mStar^2,2*rStar,2*mStar⟩,
        ⟨1,(mStar-rStar)^2,0,2*(mStar-rStar)⟩,
        ⟨mStar,1+rStar^2-2*rStar*Real.sin n,-2*rStar*mStar*Real.cos n,
          2*mStar-2*rStar*mStar*Real.sin n⟩,
        ⟨mStar,1+rStar^2+2*rStar*Real.cos n,-2*rStar*mStar*Real.sin n,
          2*mStar+2*rStar*mStar*Real.cos n⟩] u
  else
    if wo then
      ![.constant ((1+rStar)^2+mStar^2),.constant (1+(mStar-rStar)^2),
        .constant (1+(mStar-rStar)^2),.constant ((1+rStar)^2+mStar^2)] u
    else
      ![⟨1,rStar^2+mStar^2,2*rStar,2*mStar⟩,
        ⟨1,(mStar-rStar)^2,0,2*(mStar-rStar)⟩,
        ⟨1,(mStar-rStar)^2,0,2*(mStar-rStar)⟩,
        ⟨1,rStar^2+mStar^2,2*rStar,2*mStar⟩] u

private lemma sin_sq_replace (x : ℝ) : Real.sin x^2=1-Real.cos x^2 := by
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma northWave_arg (no : Bool) (u : Fin 4) (k : Fin 3) (n w x : ℝ) :
    (northWave no u k n w).arg x=northSq no u (sliceN k n w x) (sliceW k n w x) := by
  fin_cases k <;> cases no <;> fin_cases u
  all_goals norm_num [northWave,Wave.arg,Wave.parameter,Wave.constant,harmonicArg,
    northSq,sliceN,sliceW,Real.sin_sub,Real.cos_sub]
  all_goals ring_nf
  all_goals simp only [sin_sq_replace x,sin_sq_replace n,sin_sq_replace w]
  all_goals ring

lemma westWave_arg (wo : Bool) (u : Fin 4) (k : Fin 3) (n w x : ℝ) :
    (westWave wo u k n w).arg x=westSq wo u (sliceN k n w x) (sliceW k n w x) := by
  fin_cases k <;> cases wo <;> fin_cases u
  all_goals norm_num [westWave,Wave.arg,Wave.parameter,Wave.constant,harmonicArg,
    westSq,sliceN,sliceW,Real.sin_sub,Real.cos_sub]
  all_goals ring_nf
  all_goals simp only [sin_sq_replace x,sin_sq_replace n,sin_sq_replace w]
  all_goals ring

lemma northWave_amplitude (no : Bool) (u : Fin 4) (k : Fin 3) (n w : ℝ) :
    (northWave no u k n w).cosine^2+(northWave no u k n w).sine^2=
      4*(northWave no u k n w).rotor^2*(northWave no u k n w).baseSq := by
  fin_cases k <;> cases no <;> fin_cases u
  all_goals norm_num [northWave,Wave.constant]
  all_goals ring_nf
  all_goals simp only [sin_sq_replace n,sin_sq_replace w]
  all_goals ring

lemma westWave_amplitude (wo : Bool) (u : Fin 4) (k : Fin 3) (n w : ℝ) :
    (westWave wo u k n w).cosine^2+(westWave wo u k n w).sine^2=
      4*(westWave wo u k n w).rotor^2*(westWave wo u k n w).baseSq := by
  fin_cases k <;> cases wo <;> fin_cases u
  all_goals norm_num [westWave,Wave.constant]
  all_goals ring_nf
  all_goals simp only [sin_sq_replace n,sin_sq_replace w]
  all_goals ring

@[simp] lemma Wave.constant_curvature (z R x : ℝ) : (Wave.constant z).curvature R x=0 := by
  simp [Wave.curvature,Wave.constant,Wave.parameter,harmonicCurvature]

lemma Wave.curvature_bound {W : Wave} {R x A B : ℝ}
    (hR : 0≤R) (ha : 0≤W.rotor) (hb : 0≤W.baseSq)
    (hamp : W.cosine^2+W.sine^2=4*W.rotor^2*W.baseSq)
    (hx : 0<W.arg x) (hA : W.rotor≤A) (hB : W.baseSq≤B^2) (hB0 : 0≤B)
    (hab : 0<W.rotor+Real.sqrt W.baseSq) :
    W.curvature R x≤R*A*B/(A+B) := by
  have hbsq := Real.sq_sqrt hb
  have hbroot := Real.sqrt_nonneg W.baseSq
  have hbup : Real.sqrt W.baseSq≤B := by nlinarith
  have hp : W.parameter=W.rotor^2+(Real.sqrt W.baseSq)^2 := by
    rw [hbsq]
    rfl
  have hqt : W.cosine^2+W.sine^2=4*W.rotor^2*(Real.sqrt W.baseSq)^2 := by rwa [hbsq]
  have h := harmonicCurvature_le_harmonic_mean hR ha hbroot hab hp hqt hx
  have hm := harmonic_mean_mono ha hbroot hab hA hbup
  have hmul := mul_le_mul_of_nonneg_left hm hR
  dsimp [Wave.curvature]
  calc
    _≤R*W.rotor*Real.sqrt W.baseSq/(W.rotor+Real.sqrt W.baseSq) := h
    _≤R*A*B/(A+B) := by simpa only [mul_div_assoc,mul_assoc] using hmul

end SquaresInCircles.Six.Analytic.FixedPair
