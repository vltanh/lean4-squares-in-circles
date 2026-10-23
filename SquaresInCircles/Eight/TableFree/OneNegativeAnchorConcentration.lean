module

public import SquaresInCircles.Eight.TableFree.OneNegativeAnchorSlopes

/-!
# Concentration of the original A frame in the one-negative stress

Uncompiled source draft.  The original A frame is allowed on either
side of G and B.  Between them, convexity gives the two endpoint bounds.
On either exterior interval, the derivative is strictly negative in the
outward parameter.  No alignment or movement of the original A is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.OneNegativeAnchorConcentration
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
  have hmu0 : 0<mu := by linarith
  have hl1 : l≤1 := hlu.trans hmu1
  have hpos := positiveSlope_mono hl0 hl1 (by linarith : (1:ℝ)≤2*l) hl1
  have hneg := negativeSlope_mono hmu0 hl0 (le_refl l)
  have hcap : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hd (t : ℝ) (ht : t∈Icc 0 (frameCap-L)) :
      HasDerivAt (upperLine l mu L)
        (positiveSlope 1 l 1 t+negativeSlope mu l l (L+t)) t := by
    have ht' : t∈Icc 0 frameCap := ⟨ht.1,by linarith [ht.2,hL.1]⟩
    have hLt : L+t∈Icc 0 frameCap := ⟨by linarith [hL.1,ht.1],by linarith [ht.2]⟩
    have hraw := (positiveSupport_hasDerivAt (by norm_num) hl0 ht').add
      ((negativeSupport_hasDerivAt hmu0 hl0 hLt).comp t
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
  have hmu0 : 0<mu := by linarith
  have hl1 : l≤1 := hlu.trans hmu1
  have hneg := negativeSlope_mono (show (0:ℝ)<1 by norm_num) hl0 hl1
  have hpos := positiveSlope_mono hl0 hlu (by linarith : mu≤2*l) (le_refl l)
  have hcap : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hd (t : ℝ) (ht : t∈Icc 0 (frameCap-L)) :
      HasDerivAt (lowerLine l mu L)
        (negativeSlope 1 l 1 (L+t)+positiveSlope mu l l t) t := by
    have ht' : t∈Icc 0 frameCap := ⟨ht.1,by linarith [ht.2,hL.1]⟩
    have hLt : L+t∈Icc 0 frameCap := ⟨by linarith [hL.1,ht.1],by linarith [ht.2]⟩
    have hraw := ((negativeSupport_hasDerivAt (by norm_num) hl0 hLt).comp t
      ((hasDerivAt_id t).const_add L)).add (positiveSupport_hasDerivAt hmu0 hl0 ht')
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
      endpointG,phi]
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
      endpointB,phi]
    ring
  simpa only [he,hz] using hmon

/-- The actual signed A and AB errors reduce to their two common-frame
endpoints, including the two unbounded-order alternatives for A. -/
theorem angular_concentrates {l mu L x d : ℝ} (hw : Weights l mu L)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hbalance : x+d= -L) :
    angular l mu x d≤max (endpointB l mu L) (endpointG l mu L) := by
  by_cases hx0 : 0≤x
  · exact (angular_upper hw ⟨hx0,(le_abs_self x).trans hx⟩ hd hbalance).trans
      (le_max_right _ _)
  by_cases hd0 : 0≤d
  · exact (angular_lower hw hx ⟨hd0,(le_abs_self d).trans hd⟩ hbalance).trans
      (le_max_left _ _)
  obtain ⟨hL,hl,hlu,hmu1,hmu,_,_⟩ := hw.bounds
  have hl0 : 0<l := by linarith
  have hmu0 : 0<mu := by linarith
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
  change angular l mu x d≤max (endpointB l mu L) (endpointG l mu L)
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

end SquaresInCircles.Eight.TableFree.OneNegativeAnchorConcentration
