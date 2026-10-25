module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighPositivePolynomial

/-!
# The original positive high-primary projection

A fixed rational-radius multiplier turns the original owner-3 witness
into the whole-interval scalar already proved.  The target retains its
actual signed tangent and may lie on either core piece or any outer
chart.  No optimized support point replaces a state.  Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

open FramePair FrameCircleArc GlobalZeroSign GlobalOuterAnchor

def positiveLambda (z : ℝ) : ℝ := kappa*(Real.cos z+
  (Real.sin z-(c0-1/2))*Real.sin z/positiveRadius)
def positiveNormBound (z : ℝ) : ℝ := kappa*Real.sin z*
  (1+(Real.sin z-(c0-1/2))^2/(2*positiveRadius^2))

/-- Decreasing a signed corner coordinate preserves containment in
the original circle, including a negative or zero target tangent. -/
theorem signed_target_circle (t : State) :
    (t.a+1/2)^2+(transverse t+1/2)^2≤Q0 := by
  have hc := state_circle t
  cases hsign : t.positive <;>
    simp [transverse,FramePair.sign,hsign] <;> nlinarith [t.b_nonneg]

theorem signed_target_support (t : State) {f g M : ℝ}
    (hM : 0≤M) (hnorm : f^2+g^2≤M^2) :
    f*t.a+g*transverse t≤positiveRadius*M-(f+g)/2 := by
  have hR : 0≤positiveRadius := by norm_num [positiveRadius]
  have hc : normSq (t.a+1/2,transverse t+1/2)≤positiveRadius^2 := by
    have hh := signed_target_circle t
    dsimp [normSq,positiveRadius,Q0] at *
    linarith
  have hs := dot_le_radius (v:=(f,g)) hR hc
  have hN : Real.sqrt (f^2+g^2)≤M := by
    have hsq := Real.sq_sqrt (show 0≤f^2+g^2 by positivity)
    nlinarith [Real.sqrt_nonneg (f^2+g^2)]
  have hmul := mul_le_mul_of_nonneg_left hN hR
  dsimp [dot,vectorLength,normSq] at hs
  linarith

/-- The multiplier is strictly positive, and its source coefficient
is nonnegative, on the entire original angle interval. -/
theorem positiveLambda_bounds {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<positiveLambda z ∧ positiveLambda z≤kappa := by
  have tr := transport_trig hz
  have heL : (399/1000:ℝ)<c0-1/2 := by linarith [diagonal_bounds.1]
  have heU : c0-1/2<(2/5:ℝ) := by linarith [diagonal_bounds.2]
  have hsU : Real.sin z<(13/20:ℝ) := by linarith [tr.2.2.2.1]
  have hprod := mul_nonneg tr.2.2.1 (show 0≤(2/5:ℝ)-(c0-1/2) by linarith)
  have heSin : (3/5)*Real.sin z≤c0-1/2 := by linarith
  have hsmall := mul_nonneg tr.2.2.1 (sub_nonneg.mpr heSin)
  have hcos : Real.cos z+(Real.sin z)^2/2≤1 := by
    nlinarith [sq_nonneg (1-Real.cos z),Real.sin_sq_add_cos_sq z]
  constructor
  · dsimp [positiveLambda,kappa,positiveRadius]
    nlinarith [sq_nonneg (Real.sin z),tr.1]
  · dsimp [positiveLambda,kappa,positiveRadius]
    nlinarith [sq_nonneg (Real.sin z)]

theorem positiveNormBound_nonnegative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤positiveNormBound z := by
  have hs := (transport_trig hz).2.2.1
  dsimp [positiveNormBound,kappa,positiveRadius]
  positivity

theorem positiveNormBound_support (z : ℝ) :
    (positiveLambda z*Real.sin z)^2+
      (kappa-positiveLambda z*Real.cos z)^2≤(positiveNormBound z)^2 := by
  have hu := Real.sin_sq_add_cos_sq z
  have hi : (positiveLambda z*Real.sin z)^2+
      (kappa-positiveLambda z*Real.cos z)^2=
      kappa^2*(Real.sin z)^2+(positiveLambda z-kappa*Real.cos z)^2 := by
    nlinarith [congrArg (fun r : ℝ => (positiveLambda z)^2*r) hu,
      congrArg (fun r : ℝ => kappa^2*r) hu]
  have hr : (positiveNormBound z)^2-
      (kappa^2*(Real.sin z)^2+(positiveLambda z-kappa*Real.cos z)^2)=
      (kappa*Real.sin z*(Real.sin z-(c0-1/2))^2/(2*positiveRadius^2))^2 := by
    dsimp [positiveNormBound,positiveLambda,kappa,positiveRadius]
    ring
  rw [hi]
  nlinarith only [hr,sq_nonneg
    (kappa*Real.sin z*(Real.sin z-(c0-1/2))^2/(2*positiveRadius^2))]

theorem positive_primary_dual_identity (z : ℝ) :
    z+kappa*(c0-1/2)+positiveLambda z*(Real.sin z-(c0-1/2))-
      positiveRadius*positiveNormBound z=positivePrimaryScalar z (c0-1/2) := by
  dsimp [positiveLambda,positiveNormBound,positivePrimaryScalar,positiveRadius]
  ring

/-- The weak original projection gives the same quantitative scalar
for every target, before any sign or radial classification is used. -/
theorem positive_primary_transfer (s t : State) (hs : s.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a+t.a*Real.sin z-transverse t*Real.cos z) :
    positivePrimaryScalar z (c0-1/2)≤quarterCharge s (transverse t) z-kappa := by
  have hlam := positiveLambda_bounds hz
  have hproj := mul_le_mul_of_nonneg_left hm hlam.1.le
  have hchart := state_outer_chart s hs
  have ha : c0≤ s.a := by simpa only [← hchart.1] using (A_bounds hchart.2).1
  have hsource := mul_nonneg (sub_nonneg.mpr hlam.2) (sub_nonneg.mpr ha)
  have htarget := signed_target_support t (positiveNormBound_nonnegative hz)
    (positiveNormBound_support z)
  have hJ := mul_nonneg (show 0≤rho by norm_num [rho]) (J_nonnegative s hs)
  have hsin := (transport_trig hz).2.2.1
  dsimp [GlobalOuterAnchor.width] at hproj
  rw [abs_of_nonneg hsin] at hproj
  rw [← positive_primary_dual_identity z]
  dsimp [quarterCharge,potential]
  nlinarith only [hproj,hsource,htarget,hJ]

theorem positive_primary_charge (s t : State) (hs : s.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a+t.a*Real.sin z-transverse t*Real.cos z) :
    kappa≤quarterCharge s (transverse t) z ∧
      (0<z → kappa<quarterCharge s (transverse t) z) := by
  have htransfer := positive_primary_transfer s t hs hz hm
  have hscalar := positive_primary_scalar hz
  exact ⟨by linarith [hz.1,hscalar.1],fun hpos => by linarith [hscalar.2 hpos]⟩

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
