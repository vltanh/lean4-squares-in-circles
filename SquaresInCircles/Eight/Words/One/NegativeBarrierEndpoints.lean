module

public import SquaresInCircles.Eight.Owners.Direct.NegativeTCoupledArc
public import SquaresInCircles.Eight.Owners.Direct.NegativeTCycle
public import SquaresInCircles.Eight.Owners.Full.ERates
public import SquaresInCircles.Eight.Words.FirstNegativeSlack
public import SquaresInCircles.Eight.Words.Middle.PhysicalStress
public import SquaresInCircles.Eight.Words.One.NegativeAnchorSlopes
public import SquaresInCircles.Eight.Words.Wrong.SignCaptureGeometry

/-!
# Eight squares: local states for the negative-T order obstruction

The two attained transport endpoints become local barrier data with BT3, without BT2, with
aligned TD and with the original mixed owners kept (`FullCoupledStop.local_barrier`,
`PositiveDEStop.local_barrier`). The points are the ones constructed on the original circles.
-/

section
/-!
## Concentration of the original A frame in the one-negative stress

The original A frame is allowed on either
side of G and B.  Between them, convexity gives the two endpoint bounds.
On either exterior interval, the derivative is strictly negative in the
outward parameter.  No alignment or movement of the original A is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OneNegativeAnchorConcentration
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity

def angular (l mu x d : ℝ) : ℝ :=
  R*(pairNorm 1 l x+pairNorm mu l d)-(1+psi x)-l*(1+psi d)

def endpointB (l mu L : ℝ) : ℝ :=
  R*(pairNorm 1 l (-L)+pairNorm mu l 0)-Real.cos L-l

def endpointG (l mu L : ℝ) : ℝ :=
  R*(pairNorm 1 l 0+pairNorm mu l (-L))-1-l*Real.cos L

def upperLine (l mu L t : ℝ) : ℝ :=
  positiveSupport 1 l 1 t+negativeSupport mu l l (L+t)

def lowerLine (l mu L t : ℝ) : ℝ :=
  negativeSupport 1 l 1 (L+t)+positiveSupport mu l l t

theorem upperLine_antitone {l mu L : ℝ} (hw : Weights l mu L) :
    AntitoneOn (upperLine l mu L) (Icc 0 (frameCap-L)) := by
  obtain ⟨hL,hl,hlu,hmu1,hmu,_,_⟩ := hw.bounds
  have hl0 : 0<l := by linarith
  have hmu0 : 0< mu := by linarith
  have hl1 : l≤1 := hlu.trans hmu1
  have hpos := positiveSlope_mono hl0 hl1 (by linarith : (1:ℝ)≤2*l) hl1
  have hneg := negativeSlope_mono hmu0 hl0 (le_refl l)
  have hcap : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hd (t : ℝ) (ht : t∈Icc 0 (frameCap-L)) :
      HasDerivAt (upperLine l mu L)
        (positiveSlope 1 l 1 t+negativeSlope mu l l (L+t)) t := by
    have ht' : t∈Icc 0 frameCap := ⟨ht.1,by linarith [ht.2,hL.1]⟩
    have hLt : L+t∈Icc 0 frameCap := ⟨by linarith [hL.1,ht.1],by linarith [ht.2]⟩
    have hraw := (positiveSupport_hasDerivAt (a := 1) (c := 1) (by norm_num) hl0 ht').add
      ((negativeSupport_hasDerivAt (c := l) hmu0 hl0 hLt).comp t
        ((hasDerivAt_id t).const_add L))
    convert hraw using 1
    · rfl
    · ring
  apply antiOn_of_hasDeriv_nonpos
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · exact fun t ht => hd t (Ioo_subset_Icc_self ht)
  · intro t ht
    have ht' : t∈Icc 0 frameCap := ⟨ht.1.le,by linarith [ht.2,hL.1]⟩
    have hLt : L+t∈Icc 0 frameCap := ⟨by linarith [hL.1,ht.1],by linarith [ht.2]⟩
    have hp := hpos ht' hcap ht'.2
    have hn := hneg hLt hcap hLt.2
    linarith [upper_exterior_cap hw]

theorem lowerLine_antitone {l mu L : ℝ} (hw : Weights l mu L) :
    AntitoneOn (lowerLine l mu L) (Icc 0 (frameCap-L)) := by
  obtain ⟨hL,hl,hlu,hmu1,hmu,_,_⟩ := hw.bounds
  have hl0 : 0<l := by linarith
  have hmu0 : 0< mu := by linarith
  have hl1 : l≤1 := hlu.trans hmu1
  have hneg := negativeSlope_mono (show (0:ℝ)<1 by norm_num) hl0 hl1
  have hpos := positiveSlope_mono hl0 hlu (by linarith : mu≤2*l) (le_refl l)
  have hcap : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hd (t : ℝ) (ht : t∈Icc 0 (frameCap-L)) :
      HasDerivAt (lowerLine l mu L)
        (negativeSlope 1 l 1 (L+t)+positiveSlope mu l l t) t := by
    have ht' : t∈Icc 0 frameCap := ⟨ht.1,by linarith [ht.2,hL.1]⟩
    have hLt : L+t∈Icc 0 frameCap := ⟨by linarith [hL.1,ht.1],by linarith [ht.2]⟩
    have hraw := ((negativeSupport_hasDerivAt (a := 1) (c := 1) (by norm_num) hl0 hLt).comp t
      ((hasDerivAt_id t).const_add L)).add (positiveSupport_hasDerivAt (c := l) hmu0 hl0 ht')
    convert hraw using 1
    · rfl
    · ring
  apply antiOn_of_hasDeriv_nonpos
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · exact fun t ht => hd t (Ioo_subset_Icc_self ht)
  · intro t ht
    have ht' : t∈Icc 0 frameCap := ⟨ht.1.le,by linarith [ht.2,hL.1]⟩
    have hLt : L+t∈Icc 0 frameCap := ⟨by linarith [hL.1,ht.1],by linarith [ht.2]⟩
    have hn := hneg hLt hcap hLt.2
    have hp := hpos ht' hcap ht'.2
    linarith [lower_exterior_cap hw]

theorem angular_upper {l mu L x d : ℝ} (hw : Weights l mu L)
    (hx : x∈Icc 0 frameCap) (hd : |d|≤frameCap) (hbalance : x+d= -L) :
    angular l mu x d≤endpointG l mu L := by
  have hL := hw.bounds.1
  have hdEq : d= -(L+x) := by linarith
  have hsum : L+x∈Icc 0 frameCap :=
    ⟨add_nonneg hL.1 hx.1,by rw [hdEq,abs_neg,abs_of_nonneg (add_nonneg hL.1 hx.1)] at hd; exact hd⟩
  have hx' : x∈Icc 0 (frameCap-L) := ⟨hx.1,by linarith [hsum.2]⟩
  have hmon := upperLine_antitone hw
    (show (0:ℝ)∈Icc 0 (frameCap-L) by exact ⟨le_rfl,by linarith [hL.2]⟩) hx' hx.1
  have he : angular l mu x d=upperLine l mu L x := by
    rw [angular,hdEq,psi_positive hx,psi_negative hsum]
    dsimp [upperLine,positiveSupport,negativeSupport,OneNegativeAnchorPolynomial.negativeSupport]
    ring
  have hz : upperLine l mu L 0=endpointG l mu L := by
    simp [upperLine,positiveSupport,negativeSupport,OneNegativeAnchorPolynomial.negativeSupport,
      endpointG,PositiveAngularEnvelope.phi]
    ring
  simpa only [he,hz] using hmon

theorem angular_lower {l mu L x d : ℝ} (hw : Weights l mu L)
    (hx : |x|≤frameCap) (hd : d∈Icc 0 frameCap) (hbalance : x+d= -L) :
    angular l mu x d≤endpointB l mu L := by
  have hL := hw.bounds.1
  have hxEq : x= -(L+d) := by linarith
  have hsum : L+d∈Icc 0 frameCap :=
    ⟨add_nonneg hL.1 hd.1,by rw [hxEq,abs_neg,abs_of_nonneg (add_nonneg hL.1 hd.1)] at hx; exact hx⟩
  have hd' : d∈Icc 0 (frameCap-L) := ⟨hd.1,by linarith [hsum.2]⟩
  have hmon := lowerLine_antitone hw
    (show (0:ℝ)∈Icc 0 (frameCap-L) by exact ⟨le_rfl,by linarith [hL.2]⟩) hd' hd.1
  have he : angular l mu x d=lowerLine l mu L d := by
    rw [angular,hxEq,psi_negative hsum,psi_positive hd]
    dsimp [lowerLine,positiveSupport,negativeSupport,OneNegativeAnchorPolynomial.negativeSupport]
    ring
  have hz : lowerLine l mu L 0=endpointB l mu L := by
    simp [lowerLine,positiveSupport,negativeSupport,OneNegativeAnchorPolynomial.negativeSupport,
      endpointB,PositiveAngularEnvelope.phi]
    ring
  simpa only [he,hz] using hmon

/-- The actual signed A and AB errors reduce to their two common-frame
endpoints, including the two unbounded-order alternatives for A. -/
theorem angular_concentrates {l mu L x d : ℝ} (hw : Weights l mu L)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hbalance : x+d= -L) :
    angular l mu x d≤ max (endpointB l mu L) (endpointG l mu L) := by
  by_cases hx0 : 0≤x
  · exact (angular_upper hw ⟨hx0,(le_abs_self x).trans hx⟩ hd hbalance).trans
      (le_max_right _ _)
  by_cases hd0 : 0≤d
  · exact (angular_lower hw hx ⟨hd0,(le_abs_self d).trans hd⟩ hbalance).trans
      (le_max_left _ _)
  obtain ⟨hL,hl,hlu,hmu1,hmu,_,_⟩ := hw.bounds
  have hl0 : 0<l := by linarith
  have hmu0 : 0< mu := by linarith
  have hnx : -x∈Icc 0 frameCap :=
    ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hx0)] using hx⟩
  have hnd : -d∈Icc 0 frameCap :=
    ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hd0)] using hd⟩
  have hsum : -x+-d=L := by linarith
  have hsplit := WrongSignCaptureGeometry.convex_split
    (OneNegativeAnchorPolynomial.negativeSupport_convex
      (show (0:ℝ)<1 by norm_num) hl0 (hlu.trans hmu1))
    (OneNegativeAnchorPolynomial.negativeSupport_convex hmu0 hl0 (le_refl l))
    hnx.1 hnd.1 (show -x+-d≤frameCap by rw [hsum]; exact hL.2)
  have hψx : 1+psi x=Real.cos (-x) := by
    have hh := psi_negative hnx
    simp only [neg_neg] at hh
    linarith
  have hψd : 1+psi d=Real.cos (-d) := by
    have hh := psi_negative hnd
    simp only [neg_neg] at hh
    linarith
  rw [hsum] at hsplit
  change angular l mu x d≤ max (endpointB l mu L) (endpointG l mu L)
  rw [angular,hψx,hψd]
  have hleft : negativeSupport 1 l 1 (-x)+negativeSupport mu l l (-d)=
      R*(pairNorm 1 l x+pairNorm mu l d)-Real.cos (-x)-l*Real.cos (-d) := by
    simp [negativeSupport,OneNegativeAnchorPolynomial.negativeSupport]
    ring
  have heG : negativeSupport 1 l 1 0+negativeSupport mu l l L=endpointG l mu L := by
    simp [negativeSupport,OneNegativeAnchorPolynomial.negativeSupport,endpointG]
    ring
  have heB : negativeSupport 1 l 1 L+negativeSupport mu l l 0=endpointB l mu L := by
    simp [negativeSupport,OneNegativeAnchorPolynomial.negativeSupport,endpointB]
    ring
  rw [hleft,heG,heB,max_comm] at hsplit
  exact hsplit

end SquaresInCircles.Eight.OneNegativeAnchorConcentration
end
end
end

section
/-!
## The unchanged AB2 penalty and the two-circle middle comparison

The AB2 width comparison (`secondary_penalty`) uses the correlated lower coefficient
`.585+.255L`, which is below both anchor-order coefficient families; A may lie outside the G--B
interval. The final theorem `reference_middle` supports the original A and B circles once each
and uses only the scalar radial consequence of the original BT3 contact, with no new T square and
no geometric motion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OneNegativeAnchorConcentration
open Candidate PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open ActualOrdinaryBlocks CorrelatedSameBlock MiddlePhysicalStress
open SignedStress SecondaryEStress

theorem below_width {l L d : ℝ} (hl : 0≤l)
    (hratio : PositiveStressCoefficients.ratio L≤l)
    (hL : L∈Icc 0 frameCap) (hd : d∈Icc 0 (frameCap-L)) :
    Real.cos L+l≤Real.cos (L+d)+l*PositiveAngularEnvelope.phi d := by
  let f (u : ℝ) := Real.cos (L+u)+l*PositiveAngularEnvelope.phi u
  have hc : ConcaveOn ℝ (Icc 0 (frameCap-L)) f := by
    apply concave_of_deriv2
      (f' := fun u => -Real.sin (L+u)+l*(Real.cos u-Real.sin u))
      (f'' := fun u => -Real.cos (L+u)-l*PositiveAngularEnvelope.phi u)
    · intro u _
      have hraw := (((hasDerivAt_id u).const_add L).cos).add
        ((phi_hasDerivAt u).const_mul l)
      convert hraw using 1
      · rfl
      · simp only [id]
        ring
    · intro u _
      have hraw := (((hasDerivAt_id u).const_add L).sin.neg).add
        (((Real.hasDerivAt_cos u).sub (Real.hasDerivAt_sin u)).const_mul l)
      convert hraw using 1
      · rfl
      · dsimp [PositiveAngularEnvelope.phi]
        ring
    · intro u hu
      have hu' : u∈Icc 0 frameCap := ⟨hu.1,by linarith [hu.2,hL.1]⟩
      have hLu : L+u∈Icc 0 frameCap := ⟨by linarith [hL.1,hu.1],by linarith [hu.2]⟩
      have hcos : 0≤Real.cos (L+u) := by have hh := (transport_trig hLu).1; linarith
      have hPositiveAngularEnvelope.phi : 0≤PositiveAngularEnvelope.phi u := (by norm_num : (0:ℝ)≤1).trans (one_le_phi hu')
      nlinarith [mul_nonneg hl hPositiveAngularEnvelope.phi]
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
  have hz : f 0=Real.cos L+l := by simp [f,PositiveAngularEnvelope.phi]
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
    (hyA : 0≤A.y) (hyB : B.y≤0) (hl : 0≤l) (hmu : 0≤ mu)
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
  dsimp [PositiveAngularEnvelope.phi] at hsupA hsupB hwx hwd hwld
  nlinarith

theorem reference_zero {G A B : SignedPoint} {l mu x d te : ℝ}
    (hA : A.Contained (R^2)) (hB : B.Contained (R^2))
    (hyA : 0≤A.y) (hyB : B.y≤0) (hl : 0≤l) (hmu : 0≤ mu)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap)
    (hGA : quarterFeasible G A x 0) (hAB : zeroFeasible A B d 0)
    (hBT : 1+te≤B.a) :
    -G.y+mu*te≤angular l mu x d-1/2-3*mu/2-l := by
  let Tref : SignedPoint := ⟨0,te⟩
  have hBTref : quarterFeasible B Tref 0 2 := by
    simp only [quarterFeasible,quarterProjection,Tref,edgeWidth_zero]
    simp
    linarith
  have hh := signed_three_zero EndpointRotationPenalty.R_nonneg hA hB hyA hyB
    (show (0:ℝ)≤1 by norm_num) hl hmu hx hd
    (show |(0:ℝ)|≤frameCap by norm_num [frameCap]) hGA hAB hBTref
  dsimp [Tref] at hh
  simp only [one_mul,add_zero,psi_zero] at hh
  dsimp [angular]
  linarith

/-- The original two-circle middle estimate for either AB owner. The only additional scalar is
the BT3 radial bound. -/
theorem reference_middle {G A B : SignedPoint} {l mu L x d te : ℝ}
    (hw : Weights l mu L)
    (hA : A.Contained (R^2)) (hB : B.Contained (R^2))
    (hyA : 0≤A.y) (hyB : B.y≤0)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hbalance : x+d= -L)
    (hGA : quarterFeasible G A x 0)
    (hAB : zeroFeasible A B d 0 ∨ zeroFeasible A B d 2)
    (hBT : 1+te≤B.a) :
    -G.y+mu*te≤ max (endpointB l mu L) (endpointG l mu L)-1/2-3*mu/2-l := by
  obtain ⟨_,hl,_,_,hmu,_,_⟩ := hw.bounds
  rcases hAB with hAB | hAB
  · have hr := reference_zero (l := l) (mu := mu) hA hB hyA hyB (by linarith) (by linarith)
      hx hd hGA hAB hBT
    linarith [angular_concentrates hw hx hd hbalance]
  · have hr := reference_two (l := l) (mu := mu) hA hB hyA hyB (by linarith) (by linarith)
      hx hd hGA hAB hBT
    rw [hbalance] at hr
    have hp := secondary_penalty hw hx hd hbalance
    have he := le_max_left (endpointB l mu L) (endpointG l mu L)
    have heB : endpointB l mu L=R*(pairNorm 1 l (-L)+pairNorm mu l 0)-Real.cos L-l := rfl
    linarith

end SquaresInCircles.Eight.OneNegativeAnchorConcentration
end
end
end

section
/-!
## The actual cycle at an unconverted negative-T order barrier

A barrier is a complete necessary seven-cycle retaining
GA0, BT3, the original HG implication, and both original mixed witnesses.
Its H frame is at or below D. No assertion that such a state is impossible
is built into this construction; that is the separate global anchor-order
theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate

structure NegativeTBarrier (q : ℝ) where
  cycle : SignedCycle
  necessary : cycle.Necessary q
  anchors_normal : cycle.NormalAnchors
  E_nonpos : (cycle.point E).y≤0
  witnesses : cycle.Witnesses
  zero_signs : cycle.ZeroSignImplications witnesses
  GA_hard : cycle.Feasible G 0
  BT_secondary : cycle.Feasible B 3
  BT_unavailable : ¬cycle.Feasible B 2
  TD_aligned : cycle.theta T=cycle.theta D
  negative_BT : cycle.theta D<cycle.theta B
  T_nonneg : 0≤(cycle.point T).y
  H_not_above : cycle.theta H≤cycle.theta D

namespace DirectNegativeT

structure LocalBarrier {q t : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (E H : SignedPoint) (e h : ℝ) (jDE jEH : Fin 4) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  Dpoint : SignedPoint
  Tpoint : SignedPoint
  Epoint : SignedPoint
  Etheta : ℝ
  E_frame : Etheta=e ∨ Etheta∈Icc (-t) 0
  E_advance : e≤Etheta
  D_sorted : Dpoint.Sorted
  T_sorted : Tpoint.Sorted
  E_sorted : Epoint.Sorted
  D_core : Dpoint.AvoidsCore
  T_core : Tpoint.Core
  E_core : Epoint.AvoidsCore
  D_circle_nonincrease : Dpoint.circle≤D.circle
  T_inside : Tpoint.circle<q
  E_contained : Epoint.Contained q
  E_radial : Epoint.Boundary q
  E_circle_nonincrease : Epoint.circle≤E.circle
  D_negative : Dpoint.y<0
  T_positive : 0<Tpoint.y
  E_nonpos : Epoint.y≤0
  TD0 : zeroFeasible Tpoint Dpoint 0 0
  BT3 : quarterFeasible B Tpoint (-angle) 3
  BT_unavailable : ¬quarterFeasible B Tpoint (-angle) 2
  DE : quarterFeasible Dpoint Epoint (Etheta+angle) jDE
  EH : quarterFeasible Epoint H (h-Etheta) jEH
  bad_order : h+angle≤0

theorem LocalBarrier.angle_positive {q t e h : ℝ} {D T B E H : SignedPoint}
    {I : Source q t D T B} {jDE jEH : Fin 4}
    (O : LocalBarrier I E H e h jDE jEH) : 0<O.angle := by
  apply lt_of_le_of_ne O.angle_mem.1
  intro heq
  have hBT3 : quarterFeasible B O.Tpoint 0 3 := by simpa [← heq] using O.BT3
  have hBT2 : quarterFeasible B O.Tpoint 0 2 := (quarter_high_tie _ _).2 hBT3
  exact O.BT_unavailable (by simpa [← heq] using hBT2)

namespace LocalBarrier

variable {q : ℝ} {C : SignedCycle}
variable {I : Source q (C.theta B-C.theta D) (C.point D) (C.point T) (C.point B)}
variable {jDE jEH : Fin 4}

def cycle (O : LocalBarrier I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH) : SignedCycle :=
  replaceTDE C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta

theorem unchanged (O : LocalBarrier I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (i : Vertex) (hiD : i≠D) (hiT : i≠T) (hiE : i≠E) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i :=
  replaceTDE_unchanged C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta i hiD hiT hiE

theorem necessary (O : LocalBarrier I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (hn : C.Necessary q) : O.cycle.Necessary q := by
  have hDB : C.theta D≤C.theta B := by linarith [I.tilt_pos]
  have hEframe : C.theta B+O.Etheta=C.theta E ∨
      C.theta B+O.Etheta∈Icc (min (C.theta D) (C.theta B)) (max (C.theta D) (C.theta B)) := by
    rcases O.E_frame with hh | hh
    · left; linarith
    · right
      rw [min_eq_left hDB,max_eq_right hDB]
      constructor <;> linarith [hh.1,hh.2]
  have hnE := SignedCycle.necessary_replace_clamped (v := E) (a := D) (b := B)
    hn O.E_sorted O.E_contained O.E_core hEframe
  have hDframe : C.theta B-O.angle∈
      Icc (min ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta D)
        ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta B))
      (max ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta D)
        ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta B)) := by
    simp only [replacePoint,Function.update_of_ne (by decide : D≠E),
      Function.update_of_ne (by decide : B≠E),min_eq_left hDB,max_eq_right hDB,mem_Icc]
    constructor <;> linarith [O.angle_mem.1,O.angle_mem.2]
  have hnD := SignedCycle.necessary_replace_clamped (v := D) (a := D) (b := B)
    hnE O.D_sorted (O.D_circle_nonincrease.trans (hn.contained D)) O.D_core (Or.inr hDframe)
  apply SignedCycle.necessary_replace_clamped (v := T) (a := D) (b := D)
    hnD O.T_sorted O.T_inside.le O.T_core.ge
  right
  simp [replacePoint]

theorem normal (O : LocalBarrier I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (ha : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · rw [(O.unchanged H (by decide) (by decide) (by decide)).1]; exact ha.H_nonneg
  · rw [(O.unchanged A (by decide) (by decide) (by decide)).1]; exact ha.A_nonneg
  · rw [(O.unchanged B (by decide) (by decide) (by decide)).1]; exact ha.B_nonpos
  · simpa [cycle,replaceTDE,replacePoint,T,D,E] using O.D_negative.le

def witnesses (w : C.Witnesses)
    (O : LocalBarrier I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E)) :
    O.cycle.Witnesses where
  owner := ![w.owner H,w.owner G,w.owner A,3,w.owner T,w.owner D,w.owner E]
  feasible i := by
    fin_cases i
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta H
        (Or.inl rfl) _).2 (w.feasible H)
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta G
        (Or.inr (Or.inl rfl)) _).2 (w.feasible G)
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta A
        (Or.inr (Or.inr rfl)) _).2 (w.feasible A)
    · exact (replaceTDE_BT C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta 3).2 O.BT3
    · apply (replaceTDE_TD C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta _).2
      have hj : w.owner T=0 ∨ w.owner T=2 := by
        simpa [SignedCycle.normalOwners,T] using w.allowed T
      rcases hj with hj | hj
      · simpa [hj] using O.TD0
      · simpa [hj] using (zero_owner_tie _ _).1 O.TD0
    · exact (replaceTDE_DE C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta _).2 O.DE
    · exact (replaceTDE_EH C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta _).2 O.EH
  allowed i := by
    fin_cases i
    · simpa [H] using w.allowed H
    · simpa [G] using w.allowed G
    · simpa [A] using w.allowed A
    · norm_num [SignedCycle.normalOwners,B]
    · simpa [T] using w.allowed T
    · simpa [D] using w.allowed D
    · simpa [E] using w.allowed E

theorem zero_signs (w : C.Witnesses)
    (O : LocalBarrier I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hz : C.ZeroSignImplications w) : O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro hj
    have hj' : w.owner H=2 := by simpa [witnesses,H] using hj
    rw [(O.unchanged G (by decide) (by decide) (by decide)).1]
    exact hz.HG_canceling hj'
  · intro _
    simpa [cycle,replaceTDE,replacePoint] using O.T_positive

theorem ordered (w : C.Witnesses)
    (O : LocalBarrier I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (hz : C.ZeroSignImplications w) : O.cycle.Ordered :=
  SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses w) (O.zero_signs w hz)

def barrier (w : C.Witnesses)
    (O : LocalBarrier I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hn : C.Necessary q) (ha : C.NormalAnchors) (hz : C.ZeroSignImplications w)
    (hGA : C.Feasible G 0) : NegativeTBarrier q where
  cycle := O.cycle
  necessary := O.necessary hn
  anchors_normal := O.normal ha
  E_nonpos := by simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.E_nonpos
  witnesses := O.witnesses w
  zero_signs := O.zero_signs w hz
  GA_hard := (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta G
    (Or.inr (Or.inl rfl)) 0).2 hGA
  BT_secondary := (replaceTDE_BT C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta 3).2 O.BT3
  BT_unavailable := by
    intro hh
    exact O.BT_unavailable ((replaceTDE_BT C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta 2).1 hh)
  TD_aligned := by simp [cycle,replaceTDE,replacePoint,D,T,E]
  negative_BT := by
    have hh : C.theta B-O.angle<C.theta B := by linarith [O.angle_positive]
    simpa [cycle,replaceTDE,replacePoint,D,T,E,B] using hh
  T_nonneg := by simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.T_positive.le
  H_not_above := by
    have hh : C.theta H≤C.theta B-O.angle := by linarith [O.bad_order]
    simpa [cycle,replaceTDE,replacePoint,D,T,E,H] using hh

end LocalBarrier
end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
/-!
## The full .22 coupled D/T/E continuation with arbitrary H

At aligned DE contact E has tangent magnitude 1-a_D,
which is below .156. Thus a true-core E is flat along this part of the
motion even if the original E was curved. The actual outer E circle gives
the sharper contact-speed bound below one. H is only assumed contained
and outside the true core.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap
open OutsideE (contactSpeed contactSpeed_positive)

def fullCoupledPoint (kind : FullE.ArcKind) (q qD P x : ℝ) : SignedPoint :=
  kind.point q (coupledTangent qD P x)

def fullCoupledSlack (kind : FullE.ArcKind) (q qD P e : ℝ) (H : SignedPoint)
    (j : Fin 4) (x : ℝ) : ℝ :=
  FullE.mixedSlack kind q H j (e+x) (coupledTangent qD P x)

def fullCoupledDerivative (kind : FullE.ArcKind) (q qD P e : ℝ) (H : SignedPoint)
    (j : Fin 4) (x : ℝ) : ℝ :=
  -FullE.mixedRate kind q H j (e+x) (coupledTangent qD P x) (primaryGain qD P x)

theorem short_tan_bound_full {p : ℝ} (hp : p∈Icc 0 (11/50 : ℝ)) :
    0≤Real.sin p/Real.cos p ∧ Real.sin p/Real.cos p<28/125 := by
  have ht := transport_trig (show p∈Icc 0 (7/10 : ℝ) from ⟨hp.1,by linarith [hp.2]⟩)
  have hc : 0<Real.cos p := by linarith [ht.1]
  have hsmono : Real.sin p≤Real.sin (11/50 : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hp.1,Real.pi_pos]) (by linarith [Real.pi_gt_three]) hp.2
  have hs := sin_upper_five (show (0:ℝ)≤11/50 by norm_num)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := p)
  have hp2 := pow_le_pow_left₀ hp.1 hp.2 2
  refine ⟨div_nonneg ht.2.2.1 hc.le,(div_lt_iff₀ hc).2 ?_⟩
  norm_num at hs
  nlinarith

theorem full_coupled_speed_bound (kind : FullE.ArcKind) {q b p : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap) (hb : b∈Ico 0 (39/250 : ℝ))
    (hp : p∈Icc 0 (11/50 : ℝ)) :
    contactSpeed (kind.primary q b) b (kind.slope q b) p<199/200 := by
  have ht := short_tan_bound_full hp
  have hc : 0<Real.cos p := transport_cos_pos (by
    rw [abs_of_nonneg hp.1]; linarith [hp.2])
  cases kind with
  | trueCore =>
    have haflat : FullE.ArcKind.trueCore.primary q b=7/12 :=
      TrueCoreE.primary_flat (by linarith [hb.2])
    have hvflat : FullE.ArcKind.trueCore.slope q b=0 :=
      TrueCoreE.slope_flat (by linarith [hb.2])
    rw [haflat,hvflat]
    have heq : contactSpeed (7/12) b 0 p=1/12+(b+1/2)*(Real.sin p/Real.cos p) := by
      dsimp [contactSpeed]
      field_simp [hc.ne']
      ring
    have hm := mul_le_mul (show b+1/2≤82/125 by linarith [hb.2]) ht.2.le ht.1
      (by norm_num : (0:ℝ)≤82/125)
    rw [heq]
    nlinarith
  | outerCircle =>
    let X := Real.sqrt (q-(b+1/2)^2)
    let Y := b+1/2
    let v := Y/X
    let z := Real.sin p/Real.cos p
    have hY : 1/2≤Y ∧ Y<82/125 := by dsimp [Y]; constructor <;> linarith [hb.1,hb.2]
    have hrad : (933/500 : ℝ)^2<q-Y^2 := by
      dsimp [qLow] at hqL
      nlinarith
    have hrad0 : 0<q-Y^2 := by linarith
    have hX0 : 0<X := Real.sqrt_pos.mpr hrad0
    have hX2 : X^2=q-Y^2 := Real.sq_sqrt hrad0.le
    have hXL : 933/500<X := by nlinarith
    have hXU : X<383/200 := by
      dsimp [qCap] at hqU
      nlinarith
    have hv : 0≤v ∧ v<44/125 := by
      refine ⟨div_nonneg (by linarith [hY.1]) hX0.le,(div_lt_iff₀ hX0).2 ?_⟩
      nlinarith [hY.2]
    have hz : 0≤z ∧ z<28/125 := ht
    have hvz : 0≤v*z := mul_nonneg hv.1 hz.1
    have hden : 0<1+v*z := by linarith
    have hfrac : v*z/(1+v*z)≤v*z := by
      apply (div_le_iff₀ hden).2
      nlinarith [sq_nonneg (v*z)]
    have heq : contactSpeed (X-1/2) b v p=X-1+v*z/(1+v*z) := by
      have hYeq : b+1/2=v*X := by dsimp [v,Y]; field_simp [hX0.ne']
      have hcs : Real.cos p+v*Real.sin p=Real.cos p*(1+v*z) := by
        dsimp [z]
        field_simp [hc.ne']
      have hD : 0<Real.cos p+v*Real.sin p := by rw [hcs]; exact mul_pos hc hden
      dsimp [contactSpeed]
      rw [hYeq]
      dsimp [z]
      field_simp [hc.ne',hD.ne']
      ring
    have hproduct := mul_le_mul hv.2.le hz.2.le hz.1 (by norm_num : (0:ℝ)≤44/125)
    change contactSpeed (X-1/2) b v p<199/200
    rw [heq]
    nlinarith


theorem fullCoupled_DE_contact (kind : FullE.ArcKind) (q qD P x : ℝ) (j : Fin 4)
    (hj : j=2 ∨ j=3) :
    quarterProjection (Dpath qD P x) (fullCoupledPoint kind q qD P x) 0 j=edgeWidth 0 := by
  rcases hj with rfl | rfl <;>
    simp [quarterProjection,Dpath,fullCoupledPoint,coupledTangent,FullE.ArcKind.point,
      SignedPoint.reflect,edgeWidth_zero]

theorem fullCoupledSlack_actual (kind : FullE.ArcKind) {q qD P e x : ℝ} (H : SignedPoint)
    (j : Fin 4) (hj : j=0 ∨ j=1) (hp : e+x∈Icc 0 (7/10 : ℝ)) :
    fullCoupledSlack kind q qD P e H j x=
      quarterProjection (fullCoupledPoint kind q qD P x) H (e+x) j-edgeWidth (e+x) :=
  FullE.mixedSlack_actual kind q H (coupledTangent qD P x) hj hp

theorem fullCoupled_hasDerivAt {q qD P e x : ℝ} {E H : SignedPoint}
    {kind : FullE.ArcKind} (I : FullE.ArcSource q E kind) (hqL : qLow≤q)
    (hb : coupledTangent qD P x∈Icc 0 (-E.y))
    (hc : Real.cos x≠0) (hrad : 0<qD-(2-value P x)^2) (j : Fin 4) :
    HasDerivAt (fullCoupledSlack kind q qD P e H j)
      (fullCoupledDerivative kind q qD P e H j x) x := by
  have hD := (movingAnchor_derivatives hc hrad).1
  have hbder : HasDerivAt (coupledTangent qD P) (primaryGain qD P x) x :=
    (hD.const_sub 1).congr_deriv (neg_neg _)
  have hpder : HasDerivAt (fun z : ℝ => e+z) 1 x := (hasDerivAt_id x).const_add e
  have hcder := (Real.hasDerivAt_cos (e+x)).comp x hpder
  have hsder := (Real.hasDerivAt_sin (e+x)).comp x hpder
  by_cases hj : j=0
  · subst hj
    have hfun : fullCoupledSlack kind q qD P e H 0=fun y =>
        (H.a-1/2)*Real.cos (e+y)+(H.y-1/2)*Real.sin (e+y)-coupledTangent qD P y-1/2 := by
      funext y
      simp only [fullCoupledSlack,FullE.mixedSlack,DirectNegativeE.lowSlack,↓reduceIte]
    rw [hfun]
    have hraw := (((hcder.const_mul (H.a-1/2)).add (hsder.const_mul (H.y-1/2))).sub
      hbder).sub_const (1/2)
    refine hraw.congr_deriv ?_
    simp only [fullCoupledDerivative,FullE.mixedRate,DirectNegativeE.lowAngularRate,↓reduceIte]
    ring
  · have ha := (I.derivative hqL hb).1.comp x hbder
    have hfun : fullCoupledSlack kind q qD P e H j=fun y =>
        H.a-1/2+(kind.primary q (coupledTangent qD P y)-1/2)*Real.sin (e+y)-
          (coupledTangent qD P y+1/2)*Real.cos (e+y) := by
      funext y
      simp only [fullCoupledSlack,FullE.mixedSlack,FullE.highSlack,hj,↓reduceIte]
    rw [hfun]
    have hraw := ((hasDerivAt_const x (H.a-1/2)).add
      ((ha.sub_const (1/2)).mul hsder)).sub ((hbder.add_const (1/2)).mul hcder)
    refine hraw.congr_deriv ?_
    simp only [fullCoupledDerivative,FullE.mixedRate,hj,↓reduceIte,Function.comp_apply]
    ring

theorem Source.full_coupled_derivative_negative {q t e x : ℝ} {D T B E H : SignedPoint}
    {kind : FullE.ArcKind} (I : Source q t D T B) (J : FullE.ArcSource q E kind)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q)
    (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0)
    (hb : coupledTangent D.circle (B.a-1/2) x∈Icc 0 (-E.y))
    (hp : e+x∈Icc 0 (11/50 : ℝ)) (j : Fin 4) (hj : j=0 ∨ j=1) :
    fullCoupledDerivative kind q D.circle (B.a-1/2) e H j x< -(1/250) := by
  let a := primaryGain D.circle (B.a-1/2) x
  let b := coupledTangent D.circle (B.a-1/2) x
  have ha : 1<a := I.primary_gain hqU hx hnot
  let K := I.atAngle hqU hx hnot
  have hc := K.cuts hqU
  have hDa : 211/250<(movingAnchor D.circle (B.a-1/2) x).a := by
    have hsort := K.H_sorted.2
    rw [abs_of_nonneg K.H_nonneg] at hsort
    have h := hc.2.2.2.1.trans_le hsort
    rw [SignedPoint.reflect_circle] at h
    exact h
  have hbsmall : b<39/250 := by dsimp [b,coupledTangent]; linarith
  have hpwide : e+x∈Icc 0 (7/10 : ℝ) := ⟨hp.1,by linarith [hp.2]⟩
  rcases hj with rfl | rfl
  · have hrate := FullE.lowSpeed_bounds hHs hHcore hHc hqU hpwide
    have hh : DirectNegativeE.lowAngularRate H (e+x)<2/5 := hrate.2.1.trans_lt hrate.2.2
    simp only [fullCoupledDerivative,FullE.mixedRate,ite_true]
    dsimp [a] at ha
    linarith
  · let den := Real.cos (e+x)+kind.slope q b*Real.sin (e+x)
    let U := (kind.primary q b-1/2)*Real.cos (e+x)+(b+1/2)*Real.sin (e+x)
    let β := contactSpeed (kind.primary q b) b (kind.slope q b) (e+x)
    have hgeom := J.geometry hqL hb
    have hv := (J.derivative hqL hb).2
    have hdenβ := contactSpeed_positive hgeom.2.2.2.2.2.1 hb.1 hv.1 hpwide
    have hβ : β<199/200 := full_coupled_speed_bound kind hqL hqU ⟨hb.1,hbsmall⟩ hp
    have hcos : 97/100<Real.cos (e+x) := by
      have hh := Real.one_sub_sq_div_two_le_cos (x := e+x)
      have hs := pow_le_pow_left₀ hp.1 hp.2 2
      nlinarith
    have hden : 97/100<den := by
      have hprod := mul_nonneg hv.1 (transport_trig hpwide).2.2.1
      dsimp [den]
      linarith
    have hid : β*den=U := by
      dsimp [β,contactSpeed,den,U]; exact div_mul_cancel₀ _ hdenβ.1.ne'
    have hgap := mul_pos (show 0<a-β-1/200 by linarith) hdenβ.1
    have hreserve : 1/250<a*den-U := by nlinarith
    norm_num only [fullCoupledDerivative,FullE.mixedRate,show (1:Fin 4)≠0 by decide,ite_false]
    change -(a*den-U)< -(1/250)
    linarith


end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
/-!
## First hard contact or the actual H=D barrier

The coupled motion stops at the first BT2 contact or
at H=D, whichever comes first. Its original EH inequality has a strict
reserve at that attained state. The H=D alternative is an explicit
geometric state for the global anchor-order theorem, never an assumed
local impossibility.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap

structure FullCoupledStop {q t : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (kind : FullE.ArcKind) (E H : SignedPoint) (e : ℝ) (j : Fin 4) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  tangent_mem : coupledTangent D.circle (B.a-1/2) angle∈Icc 0 (-E.y)
  tangent_positive : 0<coupledTangent D.circle (B.a-1/2) angle
  error_mem : e+angle∈Icc 0 (11/50 : ℝ)
  terminal : quarterFeasible (point (B.a-1/2) angle) B.reflect (-angle) 0 ∨ e+angle=0
  mixed_strict : 0<fullCoupledSlack kind q D.circle (B.a-1/2) e H j angle

theorem Source.full_coupled_stop {q t e : ℝ} {D T B E H : SignedPoint}
    {kind : FullE.ArcKind} (I : Source q t D T B) (J : FullE.ArcSource q E kind)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q)
    (he : e+t∈Ioc 0 (11/50 : ℝ))
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E 0 jDE) (hEH : quarterFeasible E H (e+t) jEH) :
    Nonempty (FullCoupledStop I kind E H e jEH) := by
  obtain ⟨O⟩ := I.first_hard hqU
  let P := B.a-1/2
  let r := max O.angle (-e)
  let b : ℝ → ℝ := coupledTangent D.circle P
  let L : ℝ → ℝ := fullCoupledSlack kind q D.circle P e H jEH
  let F : ℝ → ℝ := fun x => L x-(t-x)/500
  let dF : ℝ → ℝ := fun x => fullCoupledDerivative kind q D.circle P e H jEH x+1/500
  have hrO : O.angle≤r := le_max_left _ _
  have hre : -e≤r := le_max_right _ _
  have hr0 : 0≤r := O.angle_mem.1.trans hrO
  have hrt : r<t := max_lt_iff.mpr ⟨O.angle_mem.2,by linarith [he.1]⟩
  have heX (x : ℝ) (hx : x∈Icc r t) : e+x∈Icc 0 (11/50 : ℝ) := by
    constructor <;> linarith [hx.1,hx.2,he.2]
  have hDEraw : 1≤D.a-E.y := by
    rcases hjDE with rfl | rfl <;>
      simpa [quarterFeasible,quarterProjection,edgeWidth_zero] using hDE
  have hbupper {x : ℝ} (hx : x∈Icc r t) : b x≤ -E.y := by
    have hh := (I.path_geometry hqU ⟨hr0.trans hx.1,hx.2⟩).2.2.1
    rw [SignedPoint.reflect_circle] at hh
    change D.a≤(movingAnchor D.circle P x).a at hh
    dsimp [b,coupledTangent]
    linarith
  have hbpositive {x : ℝ} (hx : x∈Icc r t) : 0<b x := by
    have hOx : O.angle≤x := hrO.trans hx.1
    rcases eq_or_lt_of_le hOx with heq | hlt
    · have hcut := (O.high_anchor hqU).2.2
      have hh : (movingAnchor D.circle P O.angle).a<1 := by
        rw [SignedPoint.reflect_circle] at hcut; exact hcut
      rw [← heq]
      dsimp [b,coupledTangent]
      linarith
    · have hnot := O.later_unavailable ⟨hlt,hx.2⟩
      have hcut := ((I.atAngle hqU ⟨O.angle_mem.1.trans_lt hlt,hx.2⟩ hnot).cuts hqU).2.2.2.2.1
      have hh : (movingAnchor D.circle P x).a<1 := by
        rw [SignedPoint.reflect_circle] at hcut; exact hcut
      dsimp [b,coupledTangent]
      linarith
  have hbmem {x : ℝ} (hx : x∈Icc r t) : b x∈Icc 0 (-E.y) :=
    ⟨(hbpositive hx).le,hbupper hx⟩
  have hterminal : quarterFeasible (point P r) B.reflect (-r) 0 ∨ e+r=0 := by
    rcases le_total O.angle (-e) with hle | hle
    · right
      dsimp [r]
      rw [max_eq_right hle]
      ring
    · left
      simpa [r,max_eq_left hle,P,SignedPoint.reflect] using O.hard
  have hderiv (x : ℝ) (hx : x∈Icc r t) : HasDerivAt F (dF x) x := by
    have hx0 : 0≤x := hr0.trans hx.1
    have hc : Real.cos x≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hx0]; exact hx.2.trans I.tilt_cap)).ne'
    have hg := I.path_geometry hqU ⟨hx0,hx.2⟩
    have hL := fullCoupled_hasDerivAt (e := e) (H := H) J hqL (hbmem hx) hc
      (by have h6 := hg.2.2.2.2.2.2; rw [SignedPoint.reflect_circle] at h6; exact h6) jEH
    exact (hL.sub (((hasDerivAt_id x).const_sub t).div_const 500)).congr_deriv
      (by dsimp only [dF]; ring)
  have hcont : ContinuousOn F (Icc r t) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hFt : 0≤F t := by
    have hm := J.mixed_projection_mono (H := H) hqL (hbmem ⟨hrt.le,le_rfl⟩)
      ⟨he.1.le,by linarith [he.2]⟩ jEH hjEH
    have hf : quarterFeasible (kind.point q (b t)) H (e+t) jEH := hEH.trans hm
    have hLstart : 0≤L t := by
      dsimp [L]
      rw [fullCoupledSlack_actual kind H jEH hjEH ⟨he.1.le,by linarith [he.2]⟩]
      exact sub_nonneg.mpr hf
    simpa [F] using hLstart
  have hbarrier : 0≤F r := left_sublevel_barrier hrt hcont
    (fun x hx => hderiv x (Ioo_subset_Icc_self hx))
    (fun x hx _ => by
      have hnot := O.later_unavailable ⟨hrO.trans_lt hx.1,hx.2.le⟩
      have hh := I.full_coupled_derivative_negative J hqL hqU hHs hHcore hHc
        ⟨hr0.trans_lt hx.1,hx.2.le⟩ hnot (hbmem (Ioo_subset_Icc_self hx))
        (heX x (Ioo_subset_Icc_self hx)) jEH hjEH
      dsimp [dF,P]
      linarith) hFt
  have hstrict : 0<L r := by
    have hgrowth : 0<(t-r)/500 := div_pos (sub_pos.mpr hrt) (by norm_num)
    dsimp [F] at hbarrier
    linarith
  exact ⟨{
    angle := r
    angle_mem := ⟨hr0,hrt⟩
    tangent_mem := hbmem ⟨le_rfl,hrt.le⟩
    tangent_positive := hbpositive ⟨le_rfl,hrt.le⟩
    error_mem := heX r ⟨le_rfl,hrt.le⟩
    terminal := hterminal
    mixed_strict := hstrict }⟩


end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
/-!
## Strict original-D loss at the full coupled hard endpoint

Once BT2 is actual, the proved EH reserve pays for a
small D-primary decrease and an equal E-tangent increase. Both original
DE axes remain aligned contact. E stays on its actual original outer
circle or full true-core arc, and the loss is recorded at D itself.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap

theorem FullCoupledStop.hard_endpoint {q t h : ℝ} {D T B E H : SignedPoint}
    {kind : FullE.ArcKind} {I : Source q t D T B} {jDE jEH : Fin 4}
    (O : FullCoupledStop I kind E H h jEH) (J : FullE.ArcSource q E kind)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E 0 jDE)
    (hhard : quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0) :
    Nonempty (LocalEndpoint I E H (-t) h jDE jEH) := by
  let D₀ := Dpath D.circle (B.a-1/2) O.angle
  let T₀ := Tpath (B.a-1/2) O.angle
  let b := coupledTangent D.circle (B.a-1/2) O.angle
  have hg := I.path_data hqU O.angle_mem
  have hDEraw : 1≤D.a-E.y := by
    rcases hjDE with rfl | rfl <;>
      simpa [quarterFeasible,quarterProjection,edgeWidth_zero] using hDE
  have hbupper : b< -E.y := by
    have hprim := hg.D_primary
    dsimp [b,coupledTangent,Dpath,SignedPoint.reflect] at *
    linarith
  let cap := min ((D₀.a-|D₀.y|)/2) (min ((D₀.a-7/12)/2) ((-E.y-b)/2))
  have hcap : 0<cap := by
    apply lt_min
    · exact div_pos (sub_pos.mpr hg.D_nondiagonal) (by norm_num)
    · apply lt_min
      · exact div_pos (by linarith [hg.D_primary_high]) (by norm_num)
      · exact div_pos (by linarith) (by norm_num)
  let M : ℝ → ℝ := fun η => quarterProjection (kind.point q (b+η)) H (h+O.angle) jEH-
    edgeWidth (h+O.angle)
  have hprimary := kind.continuous_primary q
  have hM : Continuous M := by
    dsimp [M,quarterProjection,FullE.ArcKind.point]
    fin_cases jEH <;> fun_prop
  have hMzero : 0<M 0 := by
    have hh := O.mixed_strict
    rw [fullCoupledSlack_actual kind H jEH hjEH ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩]
      at hh
    simpa [M,b,fullCoupledPoint] using hh
  have hpositive : ∀ᶠ η in 𝓝[>] (0:ℝ), 0<M η :=
    (hM.continuousAt.tendsto.eventually (eventually_gt_nhds hMzero)).filter_mono
      nhdsWithin_le_nhds
  have hbound : ∀ᶠ η in 𝓝[>] (0:ℝ), η<cap :=
    (eventually_lt_nhds hcap).filter_mono nhdsWithin_le_nhds
  obtain ⟨η,hη,hηcap,hMη⟩ := (eventually_mem_nhdsWithin.and (hbound.and hpositive)).exists
  replace hη : 0<η := hη
  have hηsort : η<(D₀.a-|D₀.y|)/2 := hηcap.trans_le (min_le_left _ _)
  have hηcore : η<(D₀.a-7/12)/2 :=
    hηcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηradial : η<(-E.y-b)/2 :=
    hηcap.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let D' : SignedPoint := ⟨D₀.a-η,D₀.y⟩
  let E' := kind.point q (b+η)
  have hbη : b+η∈Icc 0 (-E.y) := by
    constructor <;> linarith [O.tangent_mem.1]
  have hEg := J.geometry hqL hbη
  have hDs : D'.Sorted := by
    constructor
    · dsimp [D']; linarith [hg.D_primary_high]
    · dsimp [D']; linarith
  have hDnd : |D'.y|<D'.a := by dsimp [D']; linarith [hg.D_nondiagonal]
  have hDcore : D'.AvoidsCore := by
    have ha : 7/12≤D'.a := by dsimp [D']; linarith
    unfold SignedPoint.AvoidsCore SignedPoint.coreDistance
    rw [max_eq_left (by linarith : 0≤D'.a-1/2)]
    nlinarith [sq_nonneg (max (|D'.y|-1/2) 0)]
  have hDloss : D'.circle<D.circle := by
    rw [← hg.D_circle]
    have hprod := mul_pos hη (show 0<2*(D₀.a+1/2)-η by linarith [hg.D_primary_high])
    show (D₀.a-η+1/2)^2+(|D₀.y|+1/2)^2<(D₀.a+1/2)^2+(|D₀.y|+1/2)^2
    linarith
  have hTD0 : zeroFeasible T₀ D' 0 0 := by
    have h := hg.TD0
    simp only [zeroFeasible,zeroProjection,Matrix.cons_val_zero,Real.sin_zero,Real.cos_zero,
      mul_zero,mul_one,add_zero] at h ⊢
    exact h
  have hBT2 : quarterFeasible B T₀ (-O.angle) 2 := by
    apply (quarterFeasible_reflect B T₀ (-O.angle) 2).1
    simpa [T₀,Tpath,reflectedOwner] using hhard
  have hDEfinal : quarterFeasible D' E' 0 jDE := by
    rcases hjDE with rfl | rfl <;>
      simp [quarterFeasible,quarterProjection,D',E',b,coupledTangent,D₀,Dpath,
        SignedPoint.reflect,FullE.ArcKind.point,edgeWidth_zero] <;> linarith
  have hEHfinal : quarterFeasible E' H (h+O.angle) jEH := sub_nonneg.mp hMη.le
  exact ⟨{
    angle := O.angle
    angle_mem := O.angle_mem
    Dpoint := D'
    Tpoint := T₀
    Epoint := E'
    Etheta := -O.angle
    E_frame := Or.inr ⟨by linarith [O.angle_mem.2],neg_nonpos.mpr O.angle_mem.1⟩
    E_advance := by linarith [O.angle_mem.2]
    D_sorted := hDs
    T_sorted := hg.T_sorted
    E_sorted := hEg.1
    D_core := hDcore
    T_core := hg.T_core
    E_core := hEg.2.2.1
    D_circle_loss := hDloss
    T_inside := hg.T_inside
    E_contained := hEg.2.1
    E_radial := hEg.2.2.2.1
    E_circle_nonincrease := hEg.2.2.2.2.1
    D_negative := hg.D_negative
    T_positive := hg.T_positive
    E_nonpos := by dsimp [E',FullE.ArcKind.point]; linarith [hbη.1]
    D_nondiagonal := hDnd
    T_nondiagonal := hg.T_nondiagonal
    D_tangent_decreases := hg.D_tangent
    TD0 := hTD0
    TD2 := (zero_owner_tie _ _).1 hTD0
    BT2 := hBT2
    DE := by simpa using hDEfinal
    EH := by simpa using hEHfinal }⟩


end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap

theorem path_BT3 {q t x : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (hx : x∈Icc 0 t) :
    quarterFeasible B (Tpath (B.a-1/2) x) (-x) 3 := by
  have hp : quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 1 := by
    exact (actual_primary_contact
      (show B.reflect.a=(B.a-1/2)+1/2 by simp [SignedPoint.reflect])
      ⟨hx.1,hx.2.trans I.tilt_cap⟩).ge
  apply (quarterFeasible_reflect B (Tpath (B.a-1/2) x) (-x) 3).1
  simpa [Tpath,reflectedOwner] using hp

theorem path_BT2_unavailable {B : SignedPoint} {x : ℝ}
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0) :
    ¬quarterFeasible B (Tpath (B.a-1/2) x) (-x) 2 := by
  intro hf
  apply hnot
  simpa [Tpath,reflectedOwner] using
    (quarterFeasible_reflect B (Tpath (B.a-1/2) x) (-x) 2).2 hf

def FullCoupledStop.local_barrier {q t h : ℝ} {D T B E H : SignedPoint}
    {kind : FullE.ArcKind} {I : Source q t D T B} {jDE jEH : Fin 4}
    (O : FullCoupledStop I kind E H h jEH) (J : FullE.ArcSource q E kind)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hnot : ¬quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0) :
    LocalBarrier I E H (-t) h jDE jEH := by
  have hg := I.path_data hqU O.angle_mem
  have hEg := J.geometry hqL O.tangent_mem
  have hEH : quarterFeasible (fullCoupledPoint kind q D.circle (B.a-1/2) O.angle)
      H (h+O.angle) jEH := by
    have hh := O.mixed_strict.le
    rw [fullCoupledSlack_actual kind H jEH hjEH
      ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩] at hh
    exact sub_nonneg.mp hh
  exact {
    angle := O.angle
    angle_mem := O.angle_mem
    Dpoint := Dpath D.circle (B.a-1/2) O.angle
    Tpoint := Tpath (B.a-1/2) O.angle
    Epoint := fullCoupledPoint kind q D.circle (B.a-1/2) O.angle
    Etheta := -O.angle
    E_frame := Or.inr ⟨by linarith [O.angle_mem.2],neg_nonpos.mpr O.angle_mem.1⟩
    E_advance := by linarith [O.angle_mem.2]
    D_sorted := hg.D_sorted
    T_sorted := hg.T_sorted
    E_sorted := hEg.1
    D_core := hg.D_core
    T_core := hg.T_core
    E_core := hEg.2.2.1
    D_circle_nonincrease := hg.D_circle.le
    T_inside := hg.T_inside
    E_contained := hEg.2.1
    E_radial := hEg.2.2.2.1
    E_circle_nonincrease := hEg.2.2.2.2.1
    D_negative := hg.D_negative
    T_positive := hg.T_positive
    E_nonpos := by
      dsimp [fullCoupledPoint,FullE.ArcKind.point]
      linarith [O.tangent_mem.1]
    TD0 := hg.TD0
    BT3 := path_BT3 I ⟨O.angle_mem.1,O.angle_mem.2.le⟩
    BT_unavailable := path_BT2_unavailable hnot
    DE := by
      simpa [quarterFeasible] using (fullCoupled_DE_contact kind q D.circle (B.a-1/2) O.angle jDE hjDE).ge
    EH := by simpa using hEH
    bad_order := (O.terminal.resolve_left hnot).le }

def PositiveDEStop.local_barrier {q t e h : ℝ} {D T B E H : SignedPoint}
    {I : Source q t D T B} {jDE jEH : Fin 4}
    (O : PositiveDEStop I E e jDE) (hqU : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (hjDE : jDE=2 ∨ jDE=3)
    (hEH : quarterFeasible E H (h-e) jEH)
    (hnot : ¬quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0)
    (hbad : h+O.angle≤0) : LocalBarrier I E H e h jDE jEH := by
  have hg := I.path_data hqU O.angle_mem
  have hDE : quarterFeasible (Dpath D.circle (B.a-1/2) O.angle) E (e+O.angle) jDE := by
    have hh := O.mixed_strict.le
    rw [positiveDESlack_actual E jDE hjDE ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩] at hh
    exact sub_nonneg.mp hh
  exact {
    angle := O.angle
    angle_mem := O.angle_mem
    Dpoint := Dpath D.circle (B.a-1/2) O.angle
    Tpoint := Tpath (B.a-1/2) O.angle
    Epoint := E
    Etheta := e
    E_frame := Or.inl rfl
    E_advance := le_rfl
    D_sorted := hg.D_sorted
    T_sorted := hg.T_sorted
    E_sorted := hEs
    D_core := hg.D_core
    T_core := hg.T_core
    E_core := hEcore
    D_circle_nonincrease := hg.D_circle.le
    T_inside := hg.T_inside
    E_contained := hEc
    E_radial := hEr
    E_circle_nonincrease := le_rfl
    D_negative := hg.D_negative
    T_positive := hg.T_positive
    E_nonpos := hEy
    TD0 := hg.TD0
    BT3 := path_BT3 I ⟨O.angle_mem.1,O.angle_mem.2.le⟩
    BT_unavailable := path_BT2_unavailable hnot
    DE := hDE
    EH := hEH
    bad_order := hbad }

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end
