module

public import SquaresInCircles.Eight.TableFree.BothNegativeSpanPolynomial
public import SquaresInCircles.Eight.TableFree.BothNegativeEntry
public import SquaresInCircles.Eight.TableFree.TD2Span

/-!
# Original .21 span and complete aligned two-negative hard entry

Uncompiled source. The two short primary errors and corner caps come
from the actual original GA1/BT3 contacts and the unavailable alternatives.
Both actual AB owners are then contradicted by the same whole-square
scalar bound. The proven original span is immediately used in the
retained-sign two-primary construction, including both original anchor
circle losses. No E reflection is used by that construction.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace BothNegativeSpan
open BothNegativeSpanPolynomial

theorem X_eq_f (z : ℝ) : X z=TD0Span.f z+1/2 := by
  unfold X TD0Span.f
  ring

theorem actual_corner_caps {q t : ℝ} {H G A : SignedPoint}
    (I : AlignedNegative.Source q t H G A) (hq : q≤qCap) :
    t∈Ioc 0 (9/100:ℝ) ∧ X t≤A.a+1/2 ∧ A.y+1/2≤Y t := by
  have hc := I.cuts hq
  have ht : t∈Ioc 0 (9/100:ℝ) := ⟨I.tilt_pos,hc.2.2.2.2.2.1.le⟩
  have hX : X t≤A.a+1/2 := by rw [X_eq_f]; linarith [I.primary_lower hq]
  have hX0 : 0≤X t := by linarith [(domain_bounds ⟨ht.1.le,ht.2⟩).1]
  have hcircle : (A.a+1/2)^2+(A.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg I.A_nonneg] using I.A_contained.trans hq
  have hX2 := pow_le_pow_left₀ hX0 hX 2
  have hrad : 0≤qCap-(X t)^2 := by nlinarith [sq_nonneg (A.y+1/2)]
  have hY := Real.sqrt_nonneg (qCap-(X t)^2)
  have hY2 := Real.sq_sqrt hrad
  refine ⟨ht,hX,?_⟩
  dsimp [Y]
  nlinarith

/-- The aligned actual transverse witnesses force the two signs. -/
theorem aligned_signs {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (w : C.Witnesses)
    (hHG : C.theta G=C.theta H) (hTD : C.theta T=C.theta D) :
    (C.point G).y<0 ∧ 0<(C.point T).y := by
  have hH := (SignedPoint.coordinate_bounds (hn.sorted H) (hn.core H) (hn.contained H) hq).2.2
  have hD := (SignedPoint.coordinate_bounds (hn.sorted D) (hn.core D) (hn.contained D) hq).2.2
  have hHG0 : 1≤(C.point H).y-(C.point G).y := by
    have hw := w.feasible H
    have ho : w.owner H=0 ∨ w.owner H=2 := by simpa [SignedCycle.normalOwners,H] using w.allowed H
    rcases ho with ho | ho <;>
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
        H,G,ho,hHG,zeroProjection,edgeWidth_zero] using hw
  have hTD0 : 1≤(C.point T).y-(C.point D).y := by
    have hw := w.feasible T
    have ho : w.owner T=0 ∨ w.owner T=2 := by simpa [SignedCycle.normalOwners,T] using w.allowed T
    rcases ho with ho | ho <;>
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
        T,D,ho,hTD,zeroProjection,edgeWidth_zero] using hw
  exact ⟨by linarith [le_abs_self (C.point H).y],by linarith [neg_le_abs (C.point D).y]⟩

/-- The opposite local source uses the original D/T/B triple. Its local
reflection supplies scalar bounds only and does not move or reflect E. -/
def oppositeSource {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (ha : C.NormalAnchors) (w : C.Witnesses)
    (hTD : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3) (hnot : ¬C.Feasible B 2) :
    AlignedNegative.Source q (C.theta B-C.theta D)
      (C.point D).reflect (C.point T).reflect (C.point B).reflect := by
  let u := C.theta B-C.theta D
  have he : C.theta T-C.theta B= -u := by dsimp [u]; rw [hTD]; ring
  have hbt : quarterFeasible (C.point B) (C.point T) (-u) 3 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
      B,T,quarterFeasible,sub_nonneg,he] using hBT
  have hnobt : ¬quarterFeasible (C.point B) (C.point T) (-u) 2 := by
    intro hh
    apply hnot
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
      B,T,quarterFeasible,sub_nonneg,he] using hh
  have hga : quarterFeasible (C.point T).reflect (C.point B).reflect (-u) 1 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect (C.point B) (C.point T) (-u) 3).2 hbt
  have hnoga : ¬quarterFeasible (C.point T).reflect (C.point B).reflect (-u) 0 := by
    intro hh
    exact hnobt ((quarterFeasible_reflect (C.point B) (C.point T) (-u) 2).1
      (by simpa [reflectedOwner] using hh))
  have htransverse : 1≤(C.point T).y-(C.point D).y := by
    have hw := w.feasible T
    have ho : w.owner T=0 ∨ w.owner T=2 := by simpa [SignedCycle.normalOwners,T] using w.allowed T
    rcases ho with ho | ho <;>
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
        T,D,ho,hTD,zeroProjection,edgeWidth_zero] using hw
  exact {
    H_sorted := by simpa using hn.sorted D
    G_sorted := by simpa using hn.sorted T
    A_sorted := by simpa using hn.sorted B
    H_contained := by simpa using hn.contained D
    G_contained := by simpa using hn.contained T
    A_contained := by simpa using hn.contained B
    H_core := by simpa using hn.core D
    G_core := by simpa using hn.core T
    A_core := by simpa using hn.core B
    H_nonneg := by simpa [SignedPoint.reflect] using neg_nonneg.mpr ha.D_nonpos
    G_nonpos := by simpa [SignedPoint.reflect] using neg_nonpos.mpr hyT
    A_nonneg := by simpa [SignedPoint.reflect] using neg_nonneg.mpr ha.B_nonpos
    tilt_pos := sub_pos.mpr ht
    tilt_cap := (le_abs_self _).trans (hn.spread B D)
    HG := by simpa [zeroFeasible,zeroProjection,SignedPoint.reflect,edgeWidth_zero] using htransverse
    GA := hga
    no_hard := hnoga }

/-- The AB0 cap inequality at the unchanged frames. -/
theorem actual_AB0_cap {A B : SignedPoint} {t u v : ℝ}
    (hv : v∈Icc 0 frameCap)
    (hXA : X t≤A.a+1/2) (hYA : A.y+1/2≤Y t)
    (hXB : X u≤B.a+1/2) (hYB : -B.y+1/2≤Y u)
    (hAB : zeroFeasible A B (-v) 0) :
    0≤Y t+(Y u-1)*Real.cos v-X u*Real.sin v-1 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hv
  have h1 := mul_le_mul_of_nonneg_right hYB (by linarith : 0≤Real.cos v)
  have h2 := mul_le_mul_of_nonneg_right hXB hs0
  have hh := hAB
  rw [zeroFeasible,edgeWidth_negative_formula hv] at hh
  simp only [zeroProjection,Matrix.cons_val_zero,Real.sin_neg,Real.cos_neg] at hh
  nlinarith

theorem actual_AB2_cap {A B : SignedPoint} {t u v : ℝ}
    (hv : v∈Icc 0 frameCap)
    (hXA : X t≤A.a+1/2) (hYA : A.y+1/2≤Y t)
    (hXB : X u≤B.a+1/2) (hYB : -B.y+1/2≤Y u)
    (hAB : zeroFeasible A B (-v) 2) :
    0≤Y u+(Y t-1)*Real.cos v-X t*Real.sin v-1 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hv
  have h1 := mul_le_mul_of_nonneg_right hYA (by linarith : 0≤Real.cos v)
  have h2 := mul_le_mul_of_nonneg_right hXA hs0
  have hh := hAB
  rw [zeroFeasible,edgeWidth_negative_formula hv] at hh
  simp only [zeroProjection,Matrix.cons_val_two,Real.sin_neg,Real.cos_neg] at hh
  nlinarith

/-- Enlarging the original AB magnitude only decreases the cap. -/
theorem cap_negative {t u v : ℝ}
    (ht : t∈Icc 0 (9/100:ℝ)) (hu : u∈Icc 0 (9/100:ℝ))
    (hv : v∈Icc 0 frameCap) (hlower : 21/100-t-u≤v) :
    Y t+(Y u-1)*Real.cos v-X u*Real.sin v-1<0 := by
  have hv0 : 21/100-t-u∈Icc 0 frameCap := by
    constructor <;> norm_num [frameCap] at * <;> linarith [ht.1,ht.2,hu.1,hu.2]
  have hc := CorrelatedSameBlock.cos_anti hv0 hv hlower
  have hs := CorrelatedSameBlock.sin_mono hv0 hv hlower
  have hdom := domain_bounds hu
  have hY0 : 0≤Y u-1 := by linarith [hdom.2.2.1]
  have hX0 : 0≤X u := by linarith [hdom.1]
  have h1 := mul_le_mul_of_nonneg_left hc hY0
  have h2 := mul_le_mul_of_nonneg_left hs hX0
  have hneg := square_negative ht hu
  linarith

end BothNegativeSpan

namespace AlignedNegative

/-- The strict .21 span is a theorem of the original two-negative cycle.
No E data, radial equality, G/T sign assumption or transformed endpoint
occurs among its hypotheses. -/
theorem both_aligned_negative_span {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors) (w : C.Witnesses)
    (hHG : C.theta G=C.theta H) (htG : C.theta A<C.theta H)
    (hGA : C.Feasible G 1) (hnotGA : ¬C.Feasible G 0)
    (hTD : C.theta T=C.theta D) (htT : C.theta D<C.theta B)
    (hBT : C.Feasible B 3) (hnotBT : ¬C.Feasible B 2) :
    C.theta H-C.theta D<21/100 := by
  obtain ⟨hyG,hyT⟩ := BothNegativeSpan.aligned_signs hn hq w hHG hTD
  let I := sourceOfCycle hn ha w hHG htG hyG.le hGA hnotGA
  let J := BothNegativeSpan.oppositeSource hn ha w hTD htT hyT.le hBT hnotBT
  obtain ⟨ht,hXA,hYA⟩ := BothNegativeSpan.actual_corner_caps I hq
  obtain ⟨hu,hXB,hYB⟩ := BothNegativeSpan.actual_corner_caps J hq
  let t := C.theta H-C.theta A
  let u := C.theta B-C.theta D
  let v := C.theta A-C.theta B
  change t∈Ioc 0 (9/100:ℝ) at ht
  change u∈Ioc 0 (9/100:ℝ) at hu
  change BothNegativeSpanPolynomial.X t≤(C.point A).a+1/2 at hXA
  change (C.point A).y+1/2≤BothNegativeSpanPolynomial.Y t at hYA
  change BothNegativeSpanPolynomial.X u≤(C.point B).a+1/2 at hXB
  change -(C.point B).y+1/2≤BothNegativeSpanPolynomial.Y u at hYB
  by_contra! hlong
  have hv0 : 0≤v := by dsimp [v,t,u] at *; linarith [ht.2,hu.2]
  have hvi : v∈Icc 0 frameCap := ⟨hv0,(le_abs_self v).trans (hn.spread A B)⟩
  have hvL : 21/100-t-u≤v := by dsimp [t,u,v]; linarith
  have hown : w.owner A=0 ∨ w.owner A=2 := by
    simpa [SignedCycle.normalOwners,A] using w.allowed A
  have hfeas := w.feasible A
  rcases hown with ho | ho
  · have hab : zeroFeasible (C.point A) (C.point B) (-v) 0 := by
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
        A,B,zeroFeasible,sub_nonneg,ho,v] using hfeas
    have hcap := BothNegativeSpan.actual_AB0_cap hvi hXA hYA hXB hYB hab
    have hneg := BothNegativeSpan.cap_negative ⟨ht.1.le,ht.2⟩ ⟨hu.1.le,hu.2⟩ hvi hvL
    linarith
  · have hab : zeroFeasible (C.point A) (C.point B) (-v) 2 := by
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
        A,B,zeroFeasible,sub_nonneg,ho,v] using hfeas
    have hcap := BothNegativeSpan.actual_AB2_cap hvi hXA hYA hXB hYB hab
    have hneg := BothNegativeSpan.cap_negative ⟨hu.1.le,hu.2⟩ ⟨ht.1.le,ht.2⟩ hvi (by linarith)
    linarith

/-- Complete same-q aligned two-negative entry with the original span
proved internally, retaining strict losses on both original H and D. -/
theorem both_negative_hard_entry {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (htG : I.cycle.theta A<I.cycle.theta H)
    (hGA : I.cycle.Feasible G 1) (hnotGA : ¬I.cycle.Feasible G 0)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (htT : I.cycle.theta D<I.cycle.theta B)
    (hBT : I.cycle.Feasible B 3) (hnotBT : ¬I.cycle.Feasible B 2) :
    Nonempty (BothNegativeEntry q I.cycle I.witnesses) := by
  obtain ⟨hyG,hyT⟩ := BothNegativeSpan.aligned_signs I.necessary hqU I.witnesses hHG hTD
  have hspan := both_aligned_negative_span I.necessary hqU I.anchors_normal I.witnesses
    hHG htG hGA hnotGA hTD htT hBT hnotBT
  exact both_negative_hard_entry_of_span I hqL hqU hHG htG hyG.le hGA hnotGA
    hTD htT hyT.le hBT hnotBT hspan

end AlignedNegative
end SquaresInCircles.Eight.TableFree
