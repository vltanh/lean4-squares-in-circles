module

public import SquaresInCircles.Eight.TableFree.OneNegativeAnchorConcentration
public import SquaresInCircles.Eight.TableFree.MiddlePhysicalStress

/-!
# The unchanged AB2 penalty and the two-circle middle comparison

Uncompiled source draft.  The complete AB2 width comparison uses the
already proved correlated lower coefficient `.585+.255L`, which is below
both anchor-order coefficient families.  This includes A outside the
G--B interval.  The final theorem supports the original A and B circles
once each and uses only the scalar radial consequence of the original
BT3 contact.  It does not assert a new T square or a geometric motion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.OneNegativeAnchorConcentration
open Candidate PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open ActualOrdinaryBlocks CorrelatedSameBlock MiddlePhysicalStress
open SignedStress SecondaryEStress

theorem below_width {l L d : ℝ} (hl : 0≤l)
    (hratio : PositiveStressCoefficients.ratio L≤l)
    (hL : L∈Icc 0 frameCap) (hd : d∈Icc 0 (frameCap-L)) :
    Real.cos L+l≤Real.cos (L+d)+l*phi d := by
  let f (u : ℝ) := Real.cos (L+u)+l*phi u
  have hc : ConcaveOn ℝ (Icc 0 (frameCap-L)) f := by
    apply concave_of_deriv2
      (f' := fun u => -Real.sin (L+u)+l*(Real.cos u-Real.sin u))
      (f'' := fun u => -Real.cos (L+u)-l*phi u)
    · intro u _
      have hraw := (((hasDerivAt_id u).const_add L).cos).add
        ((phi_hasDerivAt u).const_mul l)
      convert hraw using 1
      · rfl
      · ring
    · intro u _
      have hraw := (((hasDerivAt_id u).const_add L).sin.neg).add
        (((Real.hasDerivAt_cos u).sub (Real.hasDerivAt_sin u)).const_mul l)
      convert hraw using 1
      · rfl
      · dsimp [phi]
        ring
    · intro u hu
      have hu' : u∈Icc 0 frameCap := ⟨hu.1,by linarith [hu.2,hL.1]⟩
      have hLu : L+u∈Icc 0 frameCap := ⟨by linarith [hL.1,hu.1],by linarith [hu.2]⟩
      have hcos : 0≤Real.cos (L+u) := by have hh := (transport_trig hLu).1; linarith
      have hphi : 0≤phi u := (by norm_num : (0:ℝ)≤1).trans (one_le_phi hu')
      nlinarith [mul_nonneg hl hphi]
  have hu : frameCap-L∈Icc 0 frameCap := ⟨by linarith [hL.2],by linarith [hL.1]⟩
  have hmore := mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr (one_le_phi hu))
  have hs := correlated_saturated_trig hL
  have hend : Real.cos L+l≤f (frameCap-L) := by
    dsimp [f]
    rw [show L+(frameCap-L)=frameCap by ring]
    nlinarith
  have hmin := hc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (frameCap-L) by exact ⟨le_rfl,by linarith [hL.2]⟩)
    (show frameCap-L∈Icc 0 (frameCap-L) by exact ⟨by linarith [hL.2],le_rfl⟩) hd
  have hz : f 0=Real.cos L+l := by simp [f,phi]
  rw [hz,min_eq_left hend] at hmin
  exact hmin

/-- Original AB2 width, with the real A frame in any relative order. -/
theorem secondary_penalty {l mu L x d : ℝ} (hw : Weights l mu L)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hbalance : x+d= -L) :
    Real.cos L+l≤(1+psi x)+l*(1+psi d) := by
  obtain ⟨hL,hl,hlu,hmu1,hmu,_,hratio⟩ := hw.bounds
  have hl0 : 0≤l := by linarith
  have hl1 : l≤1 := hlu.trans hmu1
  by_cases hx0 : 0≤x
  · have hx' : x∈Icc 0 frameCap := ⟨hx0,(le_abs_self x).trans hx⟩
    have hdEq : d= -(x+L) := by linarith
    have hsum : x+L∈Icc 0 frameCap := ⟨add_nonneg hx0 hL.1,by
      rw [hdEq,abs_neg,abs_of_nonneg (add_nonneg hx0 hL.1)] at hd
      exact hd⟩
    have hsur := MiddleAngularPenalty.negative_surplus
      (l := 1) (by norm_num) hx0 hL.1 hsum.2
    have hmore := mul_nonneg (sub_nonneg.mpr hl1)
      (show 0≤1-Real.cos (x+L) by linarith [Real.cos_le_one (x+L)])
    rw [hdEq,psi_positive hx',psi_negative hsum]
    nlinarith
  by_cases hd0 : 0≤d
  · have hd' : d∈Icc 0 frameCap := ⟨hd0,(le_abs_self d).trans hd⟩
    have hxEq : x= -(L+d) := by linarith
    have hsum : L+d∈Icc 0 frameCap := ⟨add_nonneg hL.1 hd0,by
      rw [hxEq,abs_neg,abs_of_nonneg (add_nonneg hL.1 hd0)] at hx
      exact hx⟩
    have hwidth := below_width hl0 hratio hL
      (show d∈Icc 0 (frameCap-L) by exact ⟨hd0,by linarith [hsum.2]⟩)
    rw [hxEq,psi_negative hsum,psi_positive hd']
    nlinarith
  have hnx : -x∈Icc 0 frameCap :=
    ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hx0)] using hx⟩
  have hnd : -d∈Icc 0 frameCap :=
    ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hd0)] using hd⟩
  have hsum : -x+-d=L := by linarith
  have hc := concave_zero_subadditive cosine_increment_concave (by simp)
    hnx.1 hnd.1 (show -x+-d≤frameCap by rw [hsum]; exact hL.2)
  rw [hsum] at hc
  have hψx : 1+psi x=Real.cos (-x) := by
    have hh := psi_negative hnx
    simp only [neg_neg] at hh
    linarith
  have hψd : 1+psi d=Real.cos (-d) := by
    have hh := psi_negative hnd
    simp only [neg_neg] at hh
    linarith
  have hmore := mul_nonneg (sub_nonneg.mpr hl1)
    (show 0≤1-Real.cos (-d) by linarith [Real.cos_le_one (-d)])
  rw [hψx,hψd]
  nlinarith

/-- The original GA0--AB2 contact pair with the scalar BT reference.
The combined A force depends on `x+d`, so its norm already lies at B. -/
theorem reference_two {G A B : SignedPoint} {l mu x d te : ℝ}
    (hA : A.Contained (R^2)) (hB : B.Contained (R^2))
    (hyA : 0≤A.y) (hyB : B.y≤0) (hl : 0≤l) (hmu : 0≤mu)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap)
    (hGA : quarterFeasible G A x 0) (hAB : zeroFeasible A B d 2)
    (hBT : 1+te≤B.a) :
    -G.y+mu*te≤R*(pairNorm 1 l (x+d)+pairNorm mu l 0)-
      1/2-3*mu/2-l-(1+psi x)-l*(1+psi d) := by
  have hsupA := positive_rotated_support EndpointRotationPenalty.R_nonneg hA hyA 1 l d x
  have hsupB := negative_rotated_support EndpointRotationPenalty.R_nonneg hB hyB mu l 0 0
  simp only [work,rotatedPair,Real.sin_zero,Real.cos_zero,phi_zero,
    zero_add,add_zero,mul_zero,mul_one,one_mul] at hsupA hsupB
  have hGA' : edgeWidth x≤G.y+A.a*Real.cos x+A.y*Real.sin x := by
    simpa [quarterFeasible,quarterProjection] using hGA
  have hAB' : edgeWidth d≤A.a*Real.sin d+A.y*Real.cos d-B.y := by
    simpa [zeroFeasible,zeroProjection] using hAB
  have hABw := mul_le_mul_of_nonneg_left hAB' hl
  have hBTw := mul_le_mul_of_nonneg_left hBT hmu
  have hwx := width_add_half_phi hx
  have hwd := width_add_half_phi hd
  have hwld := congrArg (fun z : ℝ => l*z) hwd
  rw [add_comm d x] at hsupA
  dsimp [phi] at hsupA hsupB hwx hwd hwld
  nlinarith

theorem reference_zero {G A B : SignedPoint} {l mu x d te : ℝ}
    (hA : A.Contained (R^2)) (hB : B.Contained (R^2))
    (hyA : 0≤A.y) (hyB : B.y≤0) (hl : 0≤l) (hmu : 0≤mu)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap)
    (hGA : quarterFeasible G A x 0) (hAB : zeroFeasible A B d 0)
    (hBT : 1+te≤B.a) :
    -G.y+mu*te≤angular l mu x d-1/2-3*mu/2-l := by
  let Tref : SignedPoint := ⟨0,te⟩
  have hBTref : quarterFeasible B Tref 0 2 := by
    simpa [quarterFeasible,quarterProjection,edgeWidth,Tref] using hBT
  have hh := signed_three_zero EndpointRotationPenalty.R_nonneg hA hB hyA hyB
    (show (0:ℝ)≤1 by norm_num) hl hmu hx hd
    (show |(0:ℝ)|≤frameCap by norm_num [frameCap]) hGA hAB hBTref
  dsimp [Tref] at hh
  simp only [one_mul,add_zero,psi_zero] at hh
  dsimp [angular]
  linarith

/-- The complete original two-circle middle estimate for either AB
owner.  The only additional scalar is the genuine BT3 radial bound. -/
theorem reference_middle {G A B : SignedPoint} {l mu L x d te : ℝ}
    (hw : Weights l mu L)
    (hA : A.Contained (R^2)) (hB : B.Contained (R^2))
    (hyA : 0≤A.y) (hyB : B.y≤0)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hbalance : x+d= -L)
    (hGA : quarterFeasible G A x 0)
    (hAB : zeroFeasible A B d 0 ∨ zeroFeasible A B d 2)
    (hBT : 1+te≤B.a) :
    -G.y+mu*te≤max (endpointB l mu L) (endpointG l mu L)-1/2-3*mu/2-l := by
  obtain ⟨_,hl,_,_,hmu,_,_⟩ := hw.bounds
  rcases hAB with hAB | hAB
  · have hr := reference_zero hA hB hyA hyB (by linarith) (by linarith)
      hx hd hGA hAB hBT
    linarith [angular_concentrates hw hx hd hbalance]
  · have hr := reference_two hA hB hyA hyB (by linarith) (by linarith)
      hx hd hGA hAB hBT
    rw [hbalance] at hr
    have hp := secondary_penalty hw hx hd hbalance
    have he := le_max_left (endpointB l mu L) (endpointG l mu L)
    dsimp [endpointB] at he
    linarith

end SquaresInCircles.Eight.TableFree.OneNegativeAnchorConcentration
