module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Data

/-!
# The three exact support branches for positive BT3

Uncompiled transcription of (8)--(9) in the sorted-D companion.
Every branch is an upper bound on the same original sorted circle.
The full-circle comparison is used only in the indicated scalar
branch arguments; the normalization retains the diagonal support.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem raw_sorted_support {a b f g : ℝ}
    (ha : 0<a) (hb : 0≤b) (hs : b≤a)
    (hc : (a+1/2)^2+(b+1/2)^2≤qCap) (hf : 0≤f) (hg : 0≤g) :
    f*a+g*b≤sortedSupport f g := by
  unfold sortedSupport
  split_ifs with hfg haxis
  · have hh := raw_clipped_support hc hs (by linarith) (add_nonneg hf hg)
    simpa only [clippedSupport,if_pos hfg] using hh
  · have hh := actual_axial_support (P:=⟨a,b⟩) hb
      (q:=qCap) (by simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hb] using hc)
      le_rfl hf haxis
    exact hh
  · exact raw_full_support hc

theorem actual_sorted_support {q f g : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : P.y≤0) (hc : P.Contained q) (hq : q≤qCap)
    (hf : 0≤f) (hg : 0≤g) :
    f*P.a+g*(-P.y)≤sortedSupport f g := by
  apply raw_sorted_support hs.1 (by linarith)
  · simpa only [abs_of_nonpos hy] using hs.2
  · simpa only [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hy] using hc.trans hq
  · exact hf
  · exact hg

theorem sortedSupport_le_full {f g : ℝ} : sortedSupport f g≤fullSupport f g := by
  unfold sortedSupport
  split_ifs with hfg haxis
  · have hh := raw_full_support (a:=diagonal) (b:=diagonal) (f:=f) (g:=g)
      (by nlinarith [diagonal_circle])
    simpa only [diagonalSupport,add_mul] using hh
  · have hh := raw_full_support (a:=axial) (b:=0) (f:=f) (g:=g)
      (by nlinarith [axial_circle])
    simpa using hh
  · exact le_rfl

theorem sortedSupport_diagonal {f g : ℝ} (hfg : f≤g) :
    sortedSupport f g=diagonalSupport f g := by simp [sortedSupport,hfg]

theorem sortedSupport_axis {f g : ℝ} (hg : 0<g)
    (haxis : (axial+1/2)*g≤f/2) : sortedSupport f g=f*axial := by
  have hfg : ¬f≤g := by
    intro hh
    have hp := mul_lt_mul_of_pos_right
      (show (1/2:ℝ)<axial+1/2 by linarith [axial_bounds.1]) hg
    linarith
  simp [sortedSupport,hfg,haxis]

theorem full_at_axis {f g : ℝ} (hf : 0≤f) (hg : 0≤g)
    (he : (axial+1/2)*g=f/2) : fullSupport f g=f*axial := by
  have hN := Real.sqrt_nonneg (f^2+g^2)
  have hN2 := Real.sq_sqrt (show 0≤f^2+g^2 by positivity)
  have hR := Real.sqrt_nonneg qCap
  have hA : 0≤axial+1/2 := by linarith [axial_bounds.1]
  have htarget : 0≤f*(axial+1/2)+g/2 := by positivity
  have hcross : (R*Real.sqrt (f^2+g^2))^2=(f*(axial+1/2)+g/2)^2 := by
    rw [mul_pow,radius_sq,hN2]
    have hfexpr : f=2*(axial+1/2)*g := by linarith
    rw [hfexpr]
    nlinarith [congrArg (fun v : ℝ => g^2*v) axial_circle,
      congrArg (fun v : ℝ => 4*(axial+1/2)^2*g^2*v) axial_circle]
  have hh : R*Real.sqrt (f^2+g^2)=f*(axial+1/2)+g/2 := by
    nlinarith [mul_nonneg hR hN]
  dsimp [fullSupport]
  linarith

def psi (x : ℝ) : ℝ := Real.cos x+max 0 (Real.sin x)-1
def fullD (c x y : ℝ) : ℝ :=
  c*psi x+psi y+(1+c)*(diagonal+1/2)-R*pairNorm 1 c (x+y)

theorem width_psi {x : ℝ} (hx : |x|≤frameCap) :
    edgeWidth x-1+(Real.sin x+Real.cos x)/2=psi x+1/2 := by
  have hc : 0<Real.cos x := transport_cos_pos hx
  dsimp [edgeWidth,pairWidth,psi]
  rw [abs_of_pos hc]
  by_cases hs : 0≤Real.sin x
  · rw [abs_of_nonneg hs,max_eq_right hs]
    ring
  · rw [abs_of_neg (lt_of_not_ge hs),max_eq_left (le_of_not_ge hs)]
    ring

theorem fullD_identity {c x y : ℝ} (hx : |x|≤frameCap) (hy : |y|≤frameCap) :
    fullD c x y=c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*diagonal-
      fullSupport (forceA c x y) (forceB c x y) := by
  have hX := width_psi hx
  have hY := width_psi hy
  dsimp [fullSupport]
  rw [force_norm]
  dsimp [fullD,forceA,forceB]
  nlinarith [congrArg (fun t : ℝ => c*t) hX]

theorem fullD_lower {c x y : ℝ} (hx : |x|≤frameCap) (hy : |y|≤frameCap) :
    fullD c x y≤D c x y := by
  rw [fullD_identity hx hy]
  dsimp [D]
  linarith [sortedSupport_le_full (f:=forceA c x y) (g:=forceB c x y)]

theorem fullD_mixed {c t n : ℝ} (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    fullD c t (-n)=c*(Real.cos t+Real.sin t-1)+Real.cos n-1+
      (1+c)*(diagonal+1/2)-R*pairNorm 1 c (t-n) := by
  have hst := (transport_trig ht).2.2.1
  have hsn := (transport_trig hn).2.2.1
  simp [fullD,psi,Real.cos_neg,Real.sin_neg,max_eq_right hst,
    max_eq_left (show -Real.sin n≤0 by linarith),sub_eq_add_neg]

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3
