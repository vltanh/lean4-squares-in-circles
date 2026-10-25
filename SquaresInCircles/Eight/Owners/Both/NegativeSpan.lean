module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Both.NegativeEntry
public import SquaresInCircles.Eight.Owners.Both.NegativeSpanPolynomial
public import SquaresInCircles.Eight.Owners.TD0Span

/-!
# Eight squares: the H–D span `21/100` and the aligned two-negative hard entry

On a necessary cycle with HG and TD aligned, owner `1` on GA without owner `0`, and owner `3` on
BT without owner `2`, the two primary errors are short and the corners satisfy caps
(`actual_corner_caps`, `oppositeSource`). Both owners of AB then contradict the same scalar bound
on the whole square of short errors (`actual_AB0_cap`, `actual_AB2_cap`, `cap_negative`) unless the
H–D span is below `21/100` (`both_aligned_negative_span`). With this span the two-primary
construction of `both_negative_hard_entry_of_span`, which keeps the sign of E and records strict
losses on the original circles of H and D, gives the hard entry (`both_negative_hard_entry`); it
does not reflect E.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace BothNegativeSpan
open BothNegativeSpanPolynomial

private theorem r51_zero_feasible {C : SignedCycle} {i : Vertex} (hi : word i=0) (j : Fin 4) :
    C.Feasible i j ↔
      zeroFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  rw [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,ite_eq_left hi,zeroFeasible,sub_nonneg]
  rfl

private theorem r51_quarter_feasible {C : SignedCycle} {i : Vertex} (hi : word i≠0)
    (j : Fin 4) :
    C.Feasible i j ↔
      quarterFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  rw [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,ite_eq_right hi,quarterFeasible,
    sub_nonneg]
  rfl

private theorem r51_transverse {C : SignedCycle} {i : Vertex} (hi : word i=0)
    (hθ : C.theta (next i)=C.theta i) {j : Fin 4} (hj : j=0 ∨ j=2) (hf : C.Feasible i j) :
    1≤(C.point i).y-(C.point (next i)).y := by
  rw [r51_zero_feasible hi,hθ,sub_self,zeroFeasible,edgeWidth_zero,zeroProjection_aligned] at hf
  rcases hj with rfl | rfl <;> simpa using hf

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
  have hy2 := sq_nonneg (A.y+1/2)
  simp only [qCap] at hcircle
  refine ⟨ht,hX,?_⟩
  dsimp [Y]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by simp only [qCap]; linarith))

/-- With HG and TD aligned, the transverse witnesses force `G.y < 0 < T.y`. -/
theorem aligned_signs {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (w : C.Witnesses)
    (hHG : C.theta G=C.theta H) (hTD : C.theta T=C.theta D) :
    (C.point G).y<0 ∧ 0<(C.point T).y := by
  have hH := (SignedPoint.coordinate_bounds (hn.sorted H) (hn.core H) (hn.contained H) hq).2.2
  have hD := (SignedPoint.coordinate_bounds (hn.sorted D) (hn.core D) (hn.contained D) hq).2.2
  have hHG0 : 1≤(C.point H).y-(C.point G).y := by
    have ho : w.owner H=0 ∨ w.owner H=2 := by simpa [SignedCycle.normalOwners,H] using w.allowed H
    exact r51_transverse (i := H) rfl hHG ho (w.feasible H)
  have hTD0 : 1≤(C.point T).y-(C.point D).y := by
    have ho : w.owner T=0 ∨ w.owner T=2 := by simpa [SignedCycle.normalOwners,T] using w.allowed T
    exact r51_transverse (i := T) rfl hTD.symm ho (w.feasible T)
  exact ⟨by linarith [le_abs_self (C.point H).y],by linarith [neg_le_abs (C.point D).y]⟩

/-- The local source on the T side, from the reflected triple D, T, B of the cycle. The reflection
supplies scalar bounds only; it moves no point and does not reflect E. -/
theorem oppositeSource {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (ha : C.NormalAnchors) (w : C.Witnesses)
    (hTD : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3) (hnot : ¬C.Feasible B 2) :
    AlignedNegative.Source q (C.theta B-C.theta D)
      (C.point D).reflect (C.point T).reflect (C.point B).reflect := by
  let u := C.theta B-C.theta D
  have he : C.theta T-C.theta B= -u := by dsimp [u]; rw [hTD]; ring
  have hbt : quarterFeasible (C.point B) (C.point T) (-u) 3 := by
    have h := (r51_quarter_feasible (C := C) (i := B) (by decide) 3).1 hBT
    change quarterFeasible (C.point B) (C.point T) (C.theta T-C.theta B) 3 at h
    rwa [he] at h
  have hnobt : ¬quarterFeasible (C.point B) (C.point T) (-u) 2 := by
    intro hh
    apply hnot
    refine (r51_quarter_feasible (C := C) (i := B) (by decide) 2).2 ?_
    change quarterFeasible (C.point B) (C.point T) (C.theta T-C.theta B) 2
    rwa [he]
  have hga : quarterFeasible (C.point T).reflect (C.point B).reflect (-u) 1 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect (C.point B) (C.point T) (-u) 3).2 hbt
  have hnoga : ¬quarterFeasible (C.point T).reflect (C.point B).reflect (-u) 0 := by
    intro hh
    exact hnobt ((quarterFeasible_reflect (C.point B) (C.point T) (-u) 2).1
      (by simpa [reflectedOwner] using hh))
  have htransverse : 1≤(C.point T).y-(C.point D).y := by
    have ho : w.owner T=0 ∨ w.owner T=2 := by simpa [SignedCycle.normalOwners,T] using w.allowed T
    exact r51_transverse (i := T) rfl hTD.symm ho (w.feasible T)
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
    HG := by
      simp only [zeroFeasible,edgeWidth_zero,zeroProjection_aligned,SignedPoint.reflect]
      simp
      linarith
    GA := hga
    no_hard := hnoga }

/-- The cap inequality of an AB0 witness, at the frames of the cycle. -/
theorem actual_AB0_cap {A B : SignedPoint} {t u v : ℝ}
    (hv : v∈Icc 0 frameCap)
    (_hXA : X t≤A.a+1/2) (hYA : A.y+1/2≤Y t)
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
    (_hXB : X u≤B.a+1/2) (hYB : -B.y+1/2≤Y u)
    (hAB : zeroFeasible A B (-v) 2) :
    0≤Y u+(Y t-1)*Real.cos v-X t*Real.sin v-1 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hv
  have h1 := mul_le_mul_of_nonneg_right hYA (by linarith : 0≤Real.cos v)
  have h2 := mul_le_mul_of_nonneg_right hXA hs0
  have hh := hAB
  rw [zeroFeasible,edgeWidth_negative_formula hv] at hh
  have hp : zeroProjection A B (-v) 2=A.a*Real.sin (-v)+A.y*Real.cos (-v)-B.y := rfl
  rw [hp,Real.sin_neg,Real.cos_neg] at hh
  linarith

/-- The cap is negative once the AB angle `v` is at least `21/100 - t - u`: enlarging the AB
magnitude only decreases it. -/
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

/-- On a necessary two-negative cycle with HG and TD aligned, the H–D span is below `21/100`. The
hypotheses involve neither E, nor a radial equality, nor a sign of G or T. -/
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
  have hfeas := (BothNegativeSpan.r51_zero_feasible (C := C) (i := A) rfl _).1 (w.feasible A)
  change zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) (w.owner A) at hfeas
  rw [show C.theta B-C.theta A=-v by dsimp [v]; ring] at hfeas
  rcases hown with ho | ho
  · have hab : zeroFeasible (C.point A) (C.point B) (-v) 0 := by rwa [ho] at hfeas
    have hcap := BothNegativeSpan.actual_AB0_cap hvi hXA hYA hXB hYB hab
    have hneg := BothNegativeSpan.cap_negative ⟨ht.1.le,ht.2⟩ ⟨hu.1.le,hu.2⟩ hvi hvL
    linarith
  · have hab : zeroFeasible (C.point A) (C.point B) (-v) 2 := by rwa [ho] at hfeas
    have hcap := BothNegativeSpan.actual_AB2_cap hvi hXA hYA hXB hYB hab
    have hneg := BothNegativeSpan.cap_negative ⟨hu.1.le,hu.2⟩ ⟨ht.1.le,ht.2⟩ hvi (by linarith)
    linarith

/-- The aligned two-negative hard entry at the same `q`, with strict losses on the original circles
of H and D; the span is proved by `both_aligned_negative_span`. -/
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
end SquaresInCircles.Eight
