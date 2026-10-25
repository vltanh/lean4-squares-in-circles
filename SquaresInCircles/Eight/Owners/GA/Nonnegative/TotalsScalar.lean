module

public import SquaresInCircles.Eight.Owners.GA.ChargeSubadditive
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsSplit
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveScalar

/-!
# Eight squares: the complete scalar theorem for nonnegative A and E totals

Below 1/6 the primary
charges are combined and the original clipped-D low split is used.
Above 1/6 the explicit triangle or rectangle weights are constructed
at theta = a + z and the unchanged E total. Every concentration
endpoint is discharged internally on its full original domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals
open Secondary PositiveTD PositiveAngularEnvelope OrdinaryAngleConcavity

def scalar (k l c a z e : ℝ) (i j : Fin 4) : ℝ :=
  PositiveTD.baseline k l c z+l*TwoPositive.ASupport.charge a+
    TwoPositive.ASupport.charge e+
      TwoPositive.endpoint k l (PositiveTD.tilted c z) (a+z+e) i j

theorem low_scalar_positive {a z e : ℝ}
    (ha : 0≤a) (hz : 0≤z) (he : 0≤e) (ht : a+z+e≤1/6) (i j : Fin 4) :
    0<scalar (PositiveTD.Explicit.lowK (a+z+e)) (PositiveTD.Explicit.lowL (a+z+e))
      (PositiveTD.Explicit.lowC (a+z+e)) a z e i j := by
  have htlow : a+z+e∈Icc 0 (1/6:ℝ) := ⟨by linarith,ht⟩
  have hasplit : a+e∈Icc 0 (a+z+e) := ⟨by linarith,by linarith⟩
  have hl := (PositiveTD.Explicit.low_ranges htlow).2.2.1
  have hcharge := PrimaryCharge.weighted ha he
    (show a+e≤frameCap by dsimp [frameCap]; linarith) hl.le
  have hh := TwoPositive.low_split_positive htlow hasplit i j
  have hzId : a+z+e-(a+e)=z := by ring
  simp only [TwoPositive.splitScalar,TwoPositive.splitBase,hzId] at hh
  dsimp [scalar]
  linarith

theorem large_scalar_positive (r : Region) {x y a z e : ℝ}
    (hd : Explicit.Domain r x y) (ha : 0≤a) (hz : 0≤z)
    (hθ : Explicit.theta r x y=a+z) (he : Explicit.e r x y=e)
    (i j : Fin 4) :
    0<scalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) a z e i j := by
  have hasplit : a∈Icc 0 (Explicit.theta r x y) := ⟨ha,by rw [hθ]; linarith⟩
  have hh := Analytic.large_concentration_positive r hd hasplit i j
  have hid : a+z-a=z := by ring
  simp only [Analytic.concentrationScalar,hθ,he,hid] at hh
  have hbase := Analytic.fullBaseline_le (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) z
  dsimp only [scalar]
  linarith

/-- The constructed weights apply to the actual three nonnegative
totals. In particular no separate endpoint inequalities or large-total
positivity are hypotheses of the physical source theorem. -/
theorem explicit_positive {a z e : ℝ}
    (ha : 0≤a) (hz : 0≤z) (he : 0≤e) (ht : a+z+e≤frameCap) :
    ∃k l c : ℝ,k∈Icc (1/2:ℝ) (17/20) ∧ l∈Icc k (2*k) ∧ c∈Icc k 2 ∧
      (l≤2*PositiveTD.tilted c z ∧ PositiveTD.tilted c z≤2*l) ∧
      ∀i j : Fin 4,0<scalar k l c a z e i j := by
  by_cases hlow : a+z+e≤1/6
  · have hδ : a+z+e∈Icc 0 (1/6:ℝ) := ⟨by linarith,hlow⟩
    have hzδ : z∈Icc 0 (a+z+e) := ⟨hz,by linarith⟩
    have hd := TwoPositive.low_split_domain hδ hzδ
    exact ⟨PositiveTD.Explicit.lowK (a+z+e),PositiveTD.Explicit.lowL (a+z+e),
      PositiveTD.Explicit.lowC (a+z+e),hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,
      low_scalar_positive ha hz he hlow⟩
  · have hδ : (a+z)+e∈Icc (1/6:ℝ) frameCap := ⟨(lt_of_not_ge hlow).le,ht⟩
    obtain ⟨r,x,y,hd,hθ,hE⟩ := Explicit.coordinates (by linarith : 0≤a+z) he hδ
    have hzθ : z∈Icc 0 (Explicit.theta r x y) := ⟨hz,by rw [hθ]; linarith⟩
    have hc := Explicit.coefficient_domain r hd hzθ
    exact ⟨Explicit.k r x y,Explicit.l r x y,Explicit.c r x y,
      hc.1,hc.2.1,hc.2.2.1,⟨hc.2.2.2.1,hc.2.2.2.2⟩,
      large_scalar_positive r hd ha hz hθ hE⟩

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals
