module

public import SquaresInCircles.Eight.TableFree.CriticalPositiveTEndpoints
public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTOutside

/-!
# Original positive-T contact closure at the stationary radius

Uncompiled transcription. The exact scalar is nonnegative at z=0
and strictly increasing on the fixed-t triangle. The G face is strict
whenever its length is positive. Concavity on the original G/E split
therefore forces both original primary errors to vanish. All points,
the actual EH contact, and the original common ceiling are retained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalPositiveTExclusion
open Candidate ExceptionalContactStress ExceptionalPositiveTStress

theorem original_G_T_zero {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4} (td : Bool)
    (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hT : 0≤primary C td)
    (ht : delta C.theta G+delta C.theta D+primary C td∈Icc (1/10:ℝ) (4/25))
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td) 3 0 i)) :
    delta C.theta G=0 ∧ primary C td=0 := by
  let z := primary C td
  let t := delta C.theta G+delta C.theta D+z
  have htotal : delta C.theta G+delta C.theta D+primary C td=t := rfl
  have ht' : t∈Icc (1/10:ℝ) (4/25) := ht
  have hz : z∈Icc 0 t := ⟨hT,by dsimp [t]; linarith⟩
  have hx : delta C.theta G∈Icc 0 (t-z) := ⟨hG,by dsimp [t]; linarith⟩
  have hb := CriticalPositiveTDerivative.coefficients hsharp ht' hz
  have hR := Real.sqrt_nonneg d.q
  have hR2 := Real.sq_sqrt (show 0≤d.q by norm_num [qLow] at hsharp; linarith [hsharp.1])
  have hcap : d.q≤qCap := hsharp.2.trans uniform_radius_order.2.2.1.le
  have hc : ∀ i,(C.point i).Contained d.q := fun i => (hC.contained i).trans hq
  have hc' : ∀ i,(C.point i).Contained ((Real.sqrt d.q)^2) := by simpa only [hR2] using hc
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hc i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hconc := ExceptionalPositiveTStress.concave ab td hR
    (by simpa only [hR2] using hcap)
    (show CriticalPositiveTDerivative.k d.q t z∈Icc (431/500:ℝ) (521/500) by
      constructor <;> linarith [hb.k_lower,hb.k_upper])
    (show CriticalPositiveTDerivative.eta d.q t∈Icc (1/4:ℝ) (327/1000) by
      constructor <;> linarith [hb.eta_lower,hb.eta_upper])
    hb.angle hz hC.sorted hcCap ha hEy
    (l:=CriticalPositiveTDerivative.ell d.q t z) (c:=CriticalPositiveTDerivative.c d.q t z)
  obtain ⟨h0,h1,hstrict⟩ := CriticalPositiveTEndpoints.fixed_endpoints hsharp ht' hz td hab
    rfl hC.sorted hc hn ha hvar hG hD htotal hcontact
  have hnonneg := CriticalPositiveTDerivative.scalar_nonneg hd hsharp ht' hz
  have hnec := ExceptionalPositiveTStress.necessary td hab hR
    (show 0≤CriticalPositiveTDerivative.k d.q t z by linarith [hb.k_lower]) hb.ell_pos.le
    (show 0≤CriticalPositiveTDerivative.c d.q t z by linarith [hb.c_lower])
    (show 0≤CriticalPositiveTDerivative.eta d.q t by linarith [hb.eta_lower])
    hb.angle hz rfl hG hD (by simpa only [z] using htotal) hC.sorted hc' hn hcontact hf
  constructor
  · by_contra hne
    have hGpos : 0<delta C.theta G := lt_of_le_of_ne hG (Ne.symm hne)
    have hright : 0<t-z := hGpos.trans_le hx.2
    have hpos := ExceptionalContactCurvature.positive_of_positive_right hconc
      ⟨hGpos,hx.2⟩ (hnonneg.trans h0) (hnonneg.trans_lt (hstrict hright))
    exact (not_lt_of_ge hnec) hpos
  · by_contra hne
    have hzpos : 0<z := lt_of_le_of_ne hz.1 (Ne.symm hne)
    have hs := CriticalPositiveTDerivative.scalar_pos_of_z_pos hd hsharp ht' ⟨hzpos,hz.2⟩
    have hscalar : 0<CriticalPositiveTDerivative.scalar d.q t z := by nlinarith
    have hmin := hconc.min_le_of_mem_Icc
      (show (0:ℝ)∈Icc 0 (t-z) from ⟨le_rfl,by linarith [hz.2]⟩)
      (show t-z∈Icc 0 (t-z) from ⟨by linarith [hz.2],le_rfl⟩) hx
    have hpos := (lt_min (hscalar.trans_le h0) (hscalar.trans_le h1)).trans_le hmin
    exact (not_lt_of_ge hnec) hpos

end SquaresInCircles.Eight.TableFree.CriticalPositiveTExclusion

namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTComplete
open Candidate ExceptionalContactStress ExceptionalPositiveTStress

/-- The original full-domain contact theorem: outside the critical
strip the scalar reserve is strict; on the strip the actual sharp zero
is retained and the two original primary errors are forced to zero. -/
theorem original_G_T_zero {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4} (td : Bool)
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hT : 0≤primary C td)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td) 3 0 i)) :
    delta C.theta G=0 ∧ primary C td=0 := by
  by_cases ht : delta C.theta G+delta C.theta D+primary C td∈Icc (1/10:ℝ) (4/25)
  · exact CriticalPositiveTExclusion.original_G_T_zero hd hsharp td hq hC hn hvar hab
      hG hD hT ht hEy hcontact hf
  · have hout : delta C.theta G+delta C.theta D+primary C td≤1/10 ∨
        4/25≤delta C.theta G+delta C.theta D+primary C td := by
      by_cases hl : delta C.theta G+delta C.theta D+primary C td≤1/10
      · exact Or.inl hl
      · exact Or.inr (by by_contra! hh; exact ht ⟨(lt_of_not_ge hl).le,hh.le⟩)
    exact (ExceptionalPositiveTOutside.original_false td hQL (hq.trans hsharp.2) hC hn hvar
      hab hG hD hT hEy hcontact hout hf).elim

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTComplete
