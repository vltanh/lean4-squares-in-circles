module

public import SquaresInCircles.Eight.TableFree.NegativeTDSpanCharge
public import SquaresInCircles.Eight.TableFree.PositiveTDSpanScalars
public import SquaresInCircles.Eight.TableFree.AlignedNegativeOutsideEntry

/-!
# Original H--D span for either actual transverse TD owner

Uncompiled source. Every TD2 angle sign is handled from the original
BT2/TD2 inequalities, the original sorted-circle and core inequalities,
and the actual middle stress. The resulting strict span is immediately
fed into the same-q outside-E and H/G transport assembly. Reflection is
used only for this E-free scalar statement, never to change the E sign
in an entry construction.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace TD2Span
open SpanNormBounds PositiveAngularEnvelope

theorem actual_negative_charge {q z v : ℝ} {B T D : SignedPoint}
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBc : B.Contained q) (hDc : D.Contained q)
    (hTc : T.AvoidsCore) (hDc0 : D.AvoidsCore) (hq : q≤qCap)
    (hyD : D.y≤0) (hz : z∈Ioc 0 frameCap)
    (hBT : quarterFeasible B T v 2) (hTD : zeroFeasible T D (-z) 2) :
    z<3/10 ∧ 1-c+NegativeTDSpanCharge.J z≤T.y := by
  obtain ⟨hyl,hyu,ha,hshort⟩ := NegativeTDSpanCharge.actual_negative_cuts
    hBs hTs hDs hBc hDc hTc hDc0 hq hyD hz hBT hTD
  have hD := SignedPoint.contained_minor_le_diagonal hDs (hDc.trans hq)
  rw [abs_of_nonpos hyD] at hD
  change -D.y≤c at hD
  have hzi : z∈Icc 0 frameCap := ⟨hz.1.le,hz.2⟩
  have hs0 := (transport_trig hzi).2.2.1
  have hc1 := Real.cos_le_one z
  have h1 := mul_le_mul_of_nonneg_right ha hs0
  have h2 := mul_le_mul_of_nonneg_right hyl.le (by linarith : 0≤1-Real.cos z)
  have hh := hTD
  rw [zeroFeasible,edgeWidth_negative_formula hzi] at hh
  simp only [zeroProjection,Matrix.cons_val_two,Real.sin_neg,Real.cos_neg] at hh
  refine ⟨hshort,?_⟩
  unfold NegativeTDSpanCharge.J
  nlinarith

theorem actual_positive_charge {q w : ℝ} {T D : SignedPoint}
    (hTs : T.Sorted) (hDs : D.Sorted) (hTc : T.Contained q) (hDc : D.Contained q)
    (hq : q≤qCap) (hyD : D.y≤0) (hw : w∈Icc 0 (12/25:ℝ))
    (hTD : zeroFeasible T D w 2) :
    1-c-EndpointBudgetScalars.positiveGain w≤T.y := by
  have hD := SignedPoint.contained_minor_le_diagonal hDs (hDc.trans hq)
  rw [abs_of_nonpos hyD] at hD
  change -D.y≤c at hD
  have hwi : w∈Icc 0 frameCap := ⟨hw.1,by norm_num [frameCap] at *; linarith [hw.2]⟩
  have hsup := EndpointECharge.positive_J_short hTs (hTc.trans hq)
    (show w∈Icc 0 (1/2:ℝ) by constructor <;> linarith [hw.1,hw.2])
  have hcos := Real.cos_le_one w
  have hsign := mul_le_mul_of_nonneg_right (neg_le_abs T.y) (by linarith : 0≤1-Real.cos w)
  have hh := hTD
  rw [zeroFeasible,edgeWidth_positive_formula hwi] at hh
  simp only [zeroProjection,Matrix.cons_val_two] at hh
  dsimp [EPairMinimum.J] at hsup
  nlinarith

end TD2Span

namespace AlignedNegative

theorem aligned_negative_TD2_span {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (halign : C.theta G=C.theta H)
    (ht : C.theta A<C.theta H) (hyG : (C.point G).y≤0)
    (hGA : C.Feasible G 1) (hnot : ¬C.Feasible G 0)
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2) :
    C.theta H-C.theta D<11/50 := by
  let I := sourceOfCycle hn ha w halign ht hyG hGA hnot
  let t := C.theta H-C.theta A
  let u := C.theta A-C.theta D
  let s := C.theta T-C.theta A
  let e := C.theta D-C.theta T
  have hcuts := I.cuts hq
  have hti : t∈Icc 0 (9/100:ℝ) := ⟨sub_nonneg.mpr ht.le,hcuts.2.2.2.2.2.1.le⟩
  have hBTactual : quarterFeasible (C.point B) (C.point T) (C.theta T-C.theta B) 2 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
      B,T,quarterFeasible,sub_nonneg] using hBT
  have hTDactual : zeroFeasible (C.point T) (C.point D) e 2 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
      T,D,zeroFeasible,sub_nonneg,e] using hTD
  have heabs : |e|≤frameCap := hn.spread D T
  have hsabs : |s|≤frameCap := hn.spread T A
  have hNzero (l : ℝ) : SpanNormBounds.N l 0=Real.sqrt (1+l^2) := by
    simp [SpanNormBounds.N,PositiveAngularEnvelope.pairNorm_zero,add_comm]
  by_cases he0 : e=0
  · have hTD0 : C.Feasible T 0 := by
      have hh := (zero_owner_tie (C.point T) (C.point D)).2 (by simpa [he0] using hTDactual)
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
        T,D,zeroFeasible,sub_nonneg,show C.theta D-C.theta T=0 from he0] using hh
    exact aligned_negative_TD0_span hn hq ha w halign ht hyG hGA hnot hBT hTD0
  by_contra! hlong
  have hui : u∈Icc 0 frameCap := ⟨by dsimp [u,t] at *; linarith [hti.2],
    (le_abs_self u).trans (hn.spread A D)⟩
  by_cases hen : e<0
  · have hz : -e∈Ioc 0 frameCap := ⟨neg_pos.mpr hen,(neg_le_abs e).trans heabs⟩
    obtain ⟨hzshort,hcharge⟩ := TD2Span.actual_negative_charge
      (hn.sorted B) (hn.sorted T) (hn.sorted D) (hn.contained B) (hn.contained D)
      (hn.core T) (hn.core D) hq ha.D_nonpos hz
      hBTactual (by simpa only [neg_neg] using hTDactual)
    have hJ := NegativeTDSpanCharge.charge_lower ⟨hz.1.le,hzshort.le⟩
    have hcompress := MiddleAngularStress.subadditive
      (show TD0Span.lambda∈Icc (13/20:ℝ) (23/25) by norm_num [TD0Span.lambda])
      hsabs heabs
      (show |s+e|≤frameCap by convert hn.spread D A using 1 <;> congr 1 <;> dsimp [s,e] <;> ring)
    have hsum : s+e= -u := by dsimp [s,e,u]; ring
    rw [hsum,MiddleAngularStress.B_of_nonpos (neg_nonpos.mpr hui.1),neg_neg,
      MiddleAngularStress.B_of_nonpos hen.le] at hcompress
    have hstress := SignedCycle.middle_stress hq hn ha w hBT (I.primary_lower hq)
      (show TD0Span.lambda∈Icc (13/20:ℝ) (23/25) by norm_num [TD0Span.lambda])
    have hpos := TD0Span.scalar_positive hti hui (by dsimp [u,t]; linarith)
    rw [hNzero] at hpos
    change TD0Span.f t+2+2*TD0Span.lambda-
      2*Real.sqrt qCap*Real.sqrt (1+TD0Span.lambda^2)+
      MiddleAngularStress.B TD0Span.lambda s+(C.point T).y≤0 at hstress
    change SpanNormBounds.V TD0Span.lambda u≤MiddleAngularStress.B TD0Span.lambda s+
      SpanNormBounds.V TD0Span.lambda (-e) at hcompress
    dsimp [SpanNormBounds.R] at hpos
    linarith
  · have hep : 0<e := lt_of_le_of_ne (le_of_not_gt hen) (Ne.symm he0)
    let v := -s
    have hvi : v∈Icc (13/100:ℝ) frameCap := by
      constructor
      · dsimp [v,s,u,e,t] at *
        linarith [hti.2]
      · exact (neg_le_abs s).trans hsabs
    have htv : 11/50≤t+v ∧ t+v≤frameCap := by
      constructor
      · dsimp [t,v,s,e] at *
        linarith
      · have hh := hn.spread H T
        have hht := (le_abs_self (C.theta H-C.theta T)).trans hh
        dsimp [t,v,s]
        linarith
    have hemax : e≤t+v-11/50 := by dsimp [e,t,v,s]; linarith
    have hei : e∈Icc 0 (12/25:ℝ) :=
      ⟨hep.le,by norm_num [frameCap] at htv; linarith [htv.2]⟩
    have hcharge := TD2Span.actual_positive_charge (hn.sorted T) (hn.sorted D)
      (hn.contained T) (hn.contained D) hq ha.D_nonpos hei hTDactual
    have hl := PositiveTDSpanScalars.weight_bounds hvi
    have hstress := SignedCycle.middle_stress hq hn ha w hBT (I.primary_lower hq) hl
    have hpos := PositiveTDSpanScalars.domain_positive hti hvi htv ⟨hep.le,hemax⟩
    have hsneg : s≤0 := by dsimp [v] at hvi; linarith [hvi.1]
    rw [MiddleAngularStress.B_of_nonpos hsneg] at hstress
    rw [PositiveTDSpanScalars.F,PositiveTDSpanScalars.base_as_stress,hNzero] at hpos
    change TD0Span.f t+2+2*PositiveTDSpanScalars.weight v-
      2*Real.sqrt qCap*Real.sqrt (1+(PositiveTDSpanScalars.weight v)^2)+
      SpanNormBounds.V (PositiveTDSpanScalars.weight v) v+(C.point T).y≤0 at hstress
    dsimp [SpanNormBounds.R] at hpos
    linarith

/-- Original-data .22 span for either actual normal TD owner. -/
theorem aligned_negative_span {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (halign : C.theta G=C.theta H)
    (ht : C.theta A<C.theta H) (hyG : (C.point G).y≤0)
    (hGA : C.Feasible G 1) (hnot : ¬C.Feasible G 0) (hBT : C.Feasible B 2) :
    C.theta H-C.theta D<11/50 := by
  have how : w.owner T=0 ∨ w.owner T=2 := by
    simpa [SignedCycle.normalOwners,T] using w.allowed T
  rcases how with how | how
  · exact aligned_negative_TD0_span hn hq ha w halign ht hyG hGA hnot hBT
      (by simpa [how] using w.feasible T)
  · exact aligned_negative_TD2_span hn hq ha w halign ht hyG hGA hnot hBT
      (by simpa [how] using w.feasible T)

/-- The scalar span is now discharged before the concrete E and H/G
transports. The original H-circle loss is retained by the output record. -/
theorem aligned_negative_boundary_entry {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q) (hqL : qLow≤q) (hqU : q≤qCap)
    (halign : I.cycle.theta G=I.cycle.theta H)
    (ht : I.cycle.theta A<I.cycle.theta H)
    (hyG : (I.cycle.point G).y≤0) (hGA : I.cycle.Feasible G 1)
    (hnot : ¬I.cycle.Feasible G 0) (hBT : I.cycle.Feasible B 2) :
    Nonempty (NegativeGEntry q I.cycle I.witnesses) :=
  aligned_negative_boundary_entry_of_span I hqL hqU halign ht hyG hGA hnot hBT
    (aligned_negative_span I.necessary hqU I.anchors_normal I.witnesses
      halign ht hyG hGA hnot hBT).le

/-- E-free reflected statement for the opposite actual negative primary.
Only this scalar necessary-cycle argument is reflected; no E point or
transport endpoint is changed. -/
theorem opposite_aligned_negative_span {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (halign : C.theta T=C.theta D)
    (ht : C.theta D<C.theta B) (hyT : 0≤(C.point T).y)
    (hBT : C.Feasible B 3) (hnot : ¬C.Feasible B 2) (hGA : C.Feasible G 0) :
    C.theta H-C.theta D<11/50 := by
  have hgal : C.reflected.theta G=C.reflected.theta H := by
    simpa [SignedCycle.reflected,reflectedIndex,G,H,T,D] using congrArg (fun z : ℝ => C.theta B-z) halign
  have hgt : C.reflected.theta A<C.reflected.theta H := by
    simp [SignedCycle.reflected,reflectedIndex,A,H,B,D]
    linarith
  have hgy : (C.reflected.point G).y≤0 := by
    simpa [SignedCycle.reflected,reflectedIndex,G,T,SignedPoint.reflect] using neg_nonpos.mpr hyT
  have hga : C.reflected.Feasible G 1 := by
    simpa [reflectedIndex,next,G,A,B,reflectedOwner] using
      (SignedCycle.reflected_feasible C G 3).2 hBT
  have hnoga : ¬C.reflected.Feasible G 0 := by
    intro hh
    have h := (SignedCycle.reflected_feasible C G 2).1
      (by simpa [reflectedOwner] using hh)
    exact hnot (by simpa [reflectedIndex,next,G,A,B] using h)
  have hbt : C.reflected.Feasible B 2 := by
    simpa [reflectedIndex,next,B,T,G,reflectedOwner] using
      (SignedCycle.reflected_feasible C B 0).2 hGA
  have hh := aligned_negative_span hn.reflected hq (SignedCycle.reflected_normal ha)
    w.reflected hgal hgt hgy hga hnoga hbt
  simp only [SignedCycle.reflected,reflectedIndex,H,D] at hh
  linarith

end AlignedNegative
end SquaresInCircles.Eight.TableFree
