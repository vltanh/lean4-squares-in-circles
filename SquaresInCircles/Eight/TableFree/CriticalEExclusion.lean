module

public import SquaresInCircles.Eight.TableFree.CriticalEWeightBounds
public import SquaresInCircles.Eight.TableFree.CriticalEEnvelope
public import SquaresInCircles.Eight.TableFree.ExceptionalELowExclusion

/-!
# Sharp exclusion of positive G error at an original positive-E contact

Uncompiled source. Every coefficient is selected from the actual
position-minimizing circle chain at the fixed geometric stationary
radius. The original points remain contained at their original common
radius. The E endpoint is nonnegative by the exact radial identity;
the G endpoint is strictly stronger. Concavity then forces the original
G error to be zero, including weak-owner ties and a nonzero EH0 error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalEExclusion
open Candidate ExactFamily.FiveCornerGeometry ExceptionalContactStress ExceptionalContactSupport

def K (q t : ℝ) : ℝ := CriticalEFamily.k q t (minimizingPosition q t)
def L (q t : ℝ) : ℝ := CriticalEFamily.ell q t (minimizingPosition q t)
def Cc (q t : ℝ) : ℝ := CriticalEFamily.c q t (minimizingPosition q t)
def Eta (q t : ℝ) : ℝ := CriticalEFamily.eta q (minimizingPosition q t)

theorem coefficient_bounds {q t : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    CriticalECoefficients.Bounds t (K q t) (L q t) (Cc q t) (Eta q t) := by
  exact CriticalEWeightBounds.minimizing_bounds
    (by simpa [CriticalEPolynomials.qLower,CriticalEPolynomials.qUpper,qLow,qTrial] using hq) ht

theorem scalar_endpoints {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hq : d.q∈Icc qLow qTrial) {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    0≤atE (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t+
      OrdinaryAngleConcavity.V (Real.sqrt d.q) (L d.q t) (Cc d.q t) t ∧
    0<atG (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t+
      OrdinaryAngleConcavity.V (Real.sqrt d.q) (L d.q t) (Cc d.q t) t := by
  have hb := coefficient_bounds hq ht
  have hE := CriticalEFamily.minimizing_endpoint hd (CriticalEPosition.angle_mem ht)
  change 0≤atE (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t+
    OrdinaryAngleConcavity.V (Real.sqrt d.q) (L d.q t) (Cc d.q t) t at hE
  have hR := Real.sqrt_nonneg d.q
  have hR2 := Real.sq_sqrt (show 0≤d.q by norm_num [qLow] at hq; linarith [hq.1])
  have hG := E_lt_G hR
    (show K d.q t∈Ico 0 1 from ⟨by linarith [hb.k_lower],by linarith [hb.k_upper]⟩)
    (hb.tilt_bounds (show t∈Icc 0 t from ⟨hb.angle.1,le_rfl⟩)).1
    (hb.contactScalar_lt hR (by simpa only [hR2] using hq.1))
  exact ⟨hE,by linarith⟩

theorem fixed_endpoints {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hq : d.q∈Icc qLow qTrial) {C : SignedCycle} {ab : Fin 4} {t : ℝ}
    (hab : ab=0 ∨ ab=2) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained d.q)
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t) (hcontact : Contact C) :
    0≤value C ab (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t 0 ∧
    0<value C ab (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t t := by
  have hb := coefficient_bounds hq ht
  have hR := Real.sqrt_nonneg d.q
  have hR2 := Real.sq_sqrt (show 0≤d.q by norm_num [qLow] at hq; linarith [hq.1])
  have hQL : qLow≤(Real.sqrt d.q)^2 := by simpa only [hR2] using hq.1
  have hQU : (Real.sqrt d.q)^2≤qCap := by rw [hR2]; exact hq.2.trans uniform_radius_order.2.2.1.le
  have hc' : ∀ i,(C.point i).Contained ((Real.sqrt d.q)^2) := by simpa only [hR2] using hc
  have hz : (0:ℝ)∈Icc 0 t := ⟨le_rfl,hb.angle.1⟩
  have ht' : t∈Icc 0 t := ⟨hb.angle.1,le_rfl⟩
  have hL0 := CriticalEEnvelope.original_increment hab hR hQL hQU hb hz ht' ha hvar hG hD htotal
  have hL1 := CriticalEEnvelope.original_increment hab hR hQL hQU hb ht' hz ha hvar hG hD htotal
  have hv0 := value_lower hab hR (by linarith [hb.eta_lower] : 0≤Eta d.q t)
    hb.angle hz hs hc' hn ha hcontact
  have hv1 := value_lower hab hR (by linarith [hb.eta_lower] : 0≤Eta d.q t)
    hb.angle ht' hs hc' hn ha hcontact
  rw [sub_zero,baseline_at_E hb.angle] at hv0
  rw [sub_self,baseline_at_G hb.angle] at hv1
  obtain ⟨hE,hGG⟩ := scalar_endpoints hd hq ht
  constructor <;> linarith

/-- The full original critical-strip conclusion. q is still the
original common squared radius; only a support upper bound uses d.q. -/
theorem original_G_zero {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (ht : delta C.theta G+delta C.theta D∈Icc (1/10:ℝ) (4/25))
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : delta C.theta G=0 := by
  by_contra hne
  have hGpos : 0<delta C.theta G := lt_of_le_of_ne hG (Ne.symm hne)
  let t := delta C.theta G+delta C.theta D
  have ht' : t∈Icc (1/10:ℝ) (4/25) := ht
  have hb := coefficient_bounds hsharp ht'
  have htotal : delta C.theta G+delta C.theta D=t := rfl
  have hx : delta C.theta G∈Ioc 0 t := ⟨hGpos,by dsimp [t]; linarith⟩
  have hR := Real.sqrt_nonneg d.q
  have hR2 := Real.sq_sqrt (show 0≤d.q by norm_num [qLow] at hsharp; linarith [hsharp.1])
  have hcap : d.q≤qCap := hsharp.2.trans uniform_radius_order.2.2.1.le
  have hc : ∀ i,(C.point i).Contained d.q := fun i => (hC.contained i).trans hq
  have hc' : ∀ i,(C.point i).Contained ((Real.sqrt d.q)^2) := by simpa only [hR2] using hc
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hc i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hconc := ExceptionalContactStress.concave ab hR
    (by simpa only [hR2] using hcap)
    (show K d.q t∈Icc (431/500:ℝ) 1 by constructor <;> linarith [hb.k_lower,hb.k_upper])
    (show Eta d.q t∈Icc (1/4:ℝ) (327/1000) by constructor <;> linarith [hb.eta_lower,hb.eta_upper])
    hb.angle hC.sorted hcCap ha hEy
  obtain ⟨h0,h1⟩ := fixed_endpoints hd hsharp hab ht' hC.sorted hc hn ha hvar hG hD htotal hcontact
  have hpos := ExceptionalContactCurvature.positive_of_positive_right hconc hx h0 h1
  have hnec := ExceptionalContactStress.necessary hab hR
    (by linarith [hb.k_lower]) hb.ell_pos.le (by linarith [hb.c_lower])
    (by linarith [hb.eta_lower]) hb.angle hG hD htotal hC.sorted hc' hn hcontact hf
  exact (not_lt_of_ge hnec) hpos

end SquaresInCircles.Eight.TableFree.CriticalEExclusion

namespace SquaresInCircles.Eight.TableFree.ExceptionalEComplete
open Candidate ExceptionalContactStress

/-- The entire total-angle domain is covered by the sharp critical
family and the proved rational-radius outside intervals. -/
theorem original_G_zero {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : delta C.theta G=0 := by
  by_cases ht : delta C.theta G+delta C.theta D∈Icc (1/10:ℝ) (4/25)
  · exact CriticalEExclusion.original_G_zero hd hsharp hq hC hn hvar hab hG hD ht hEy hcontact hf
  · have hout : delta C.theta G+delta C.theta D≤1/10 ∨ 4/25≤delta C.theta G+delta C.theta D := by
      by_cases hl : delta C.theta G+delta C.theta D≤1/10
      · exact Or.inl hl
      · exact Or.inr (by by_contra! hh; exact ht ⟨(lt_of_not_ge hl).le,hh.le⟩)
    exact (ExceptionalEOutside.original_false hQL (hq.trans hsharp.2) hC hn hvar hab hG hD
      hout hEy hcontact hf).elim

end SquaresInCircles.Eight.TableFree.ExceptionalEComplete
