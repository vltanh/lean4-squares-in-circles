module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2HighSplit
public import SquaresInCircles.Eight.TableFree.GlobalGASecantDPositiveEndpoint
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LowStress

/-!
# Negative DE3, nonnegative selected A total, and positive BT3

Uncompiled definitions of Sections 1--3 of
`HAND_G3_NEGATIVE_DE3_POSITIVE_BT3_WITH_NONNEGATIVE_A_TOTAL_EXCLUSION.md`.
The original TD0 angle is a separate secant-D singleton. The original
EH0 angle remains in H's ordinary pair. The three ordinary coefficient
pairs are fixed by the total theta and do not vary with the A/BT split
or the genuine DE magnitude. The high tilt, unlike the old TD tilt,
depends on the fixed total angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

abbrev Family := NegativeDEPositiveTD.Family
abbrev Split := NegativeDEPositiveTD.Split

namespace Explicit

abbrev L : ℝ := 1/6
abbrev K : ℝ := 13/12
abbrev sec := NegativeELargeA.secant
abbrev left : Family→ℝ := NegativeDEPositiveTD.Explicit.left
abbrev right : Family→ℝ := NegativeDEPositiveTD.Explicit.right
abbrev splitA := NegativeDEPositiveTD.Explicit.splitA
abbrev splitT := NegativeDEPositiveTD.Explicit.splitT

def k : Family→ℝ→ℝ
  | .low,θ => PositiveBT3.lowK θ
  | .high,θ => NegativeDEPositiveTD.Explicit.k .high θ
def l : Family→ℝ→ℝ
  | .low,_ => 1
  | .high,θ => NegativeDEPositiveTD.Explicit.l .high θ
def m : Family→ℝ→ℝ
  | .low,θ => PositiveBT3.lowM θ
  | .high,θ => NegativeDEPositiveTD.Explicit.c .high θ
def eta : Family→ℝ→ℝ
  | .low,_ => 293/1000
  | .high,θ => 293/1000+(1351/10000)*(θ-L)
def sigma (f : Family) (θ : ℝ) : ℝ := fullSupport 1 (eta f θ)
def c (f : Family) (θ z : ℝ) : ℝ := m f θ*(Real.cos z+eta f θ*Real.sin z)

def p (f : Family) (θ : ℝ) : Fin 3→ℝ := ![k f θ,k f θ,min (l f θ) (m f θ)]
def q (f : Family) (θ : ℝ) : Fin 3→ℝ := ![1,l f θ,max (l f θ) (m f θ)]
def U (f : Family) (θ : ℝ) (i : Fin 3) (t : ℝ) : ℝ :=
  OrdinaryAngleConcavity.U R (p f θ i) (q f θ i) t
def V (f : Family) (θ : ℝ) (i : Fin 3) (t : ℝ) : ℝ :=
  OrdinaryAngleConcavity.V R (p f θ i) (q f θ i) t

/-- Sorted support at the original common circle; no D angle was removed. -/
def baseline (f : Family) (a z s : ℝ) : ℝ :=
  let θ := a+z
  k f θ+2*l f θ+m f θ*edgeWidth z+c f θ z+sec s+1-
    m f θ*sigma f θ*Real.sin z+l f θ*TwoPositive.ASupport.charge a-
    fullSupport 1 (k f θ)-fullSupport (k f θ) (l f θ)-
    fullSupport (l f θ) (m f θ)-PositiveBT3.sortedSupport (sec s) (c f θ z)+
    K*Real.tan s-(sec s-1)/2

/-- This is used only after the sorted support has been bounded above. -/
def fullBaseline (f : Family) (a z s : ℝ) : ℝ :=
  let θ := a+z
  k f θ+2*l f θ+m f θ*edgeWidth z+c f θ z+sec s+1-
    m f θ*sigma f θ*Real.sin z+l f θ*TwoPositive.ASupport.charge a-
    fullSupport 1 (k f θ)-fullSupport (k f θ) (l f θ)-
    fullSupport (l f θ) (m f θ)-fullSupport (sec s) (c f θ z)+
    K*Real.tan s-(sec s-1)/2

def gamma (f : Family) (θ z s : ℝ) : ℝ := SecantD.slope*max (sec s) (c f θ z)

theorem frame_domain (f : Family) {θ : ℝ} (hθ : θ∈Icc (left f) (right f)) :
    θ∈Icc 0 frameCap := NegativeDEPositiveTD.Explicit.family_frame_domain f hθ

theorem baseline_correction (f : Family) (a z s : ℝ) :
    baseline f a z s=baseline f a z 0+SecantD.PositiveEndpoint.correction (c f (a+z) z) s := by
  simp only [baseline,SecantD.PositiveEndpoint.correction,sec,NegativeELargeA.secant,
    Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,sub_zero,add_zero]
  dsimp [K]
  ring

theorem full_lower (f : Family) (a z s : ℝ) : fullBaseline f a z s≤baseline f a z s := by
  have hh := PositiveBT3.sortedSupport_le_full (f:=sec s) (g:=c f (a+z) z)
  dsimp [fullBaseline,baseline]
  linarith

theorem full_correction (f : Family) (a z : ℝ) {s : ℝ} (hs : s∈Icc 0 frameCap) :
    fullBaseline f a z s=fullBaseline f a z 0+secantGain qCap (c f (a+z) z) s := by
  rw [secantGain_eq_secant_expression qCap (c f (a+z) z) (NegativeESecant.cos_pos hs)]
  simp only [fullBaseline,fullSupport,sec,NegativeELargeA.secant,
    Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,sub_zero,add_zero,one_pow]
  dsimp [K]
  ring

end Explicit
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT
