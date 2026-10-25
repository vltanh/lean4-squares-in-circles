module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Boundary.ActualOrdinaryBlocks

/-!
# Eight squares: same-state reselection of every nonpositive outer-E primary

The comparison uses E's original outer equality and
the anchor's containment at that same q. Both E tangent signs are
included. No point, frame, radius, gap, or variation is changed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OuterEPrimaryComparison
open Candidate PositiveAngularEnvelope

theorem trigonometric_comparison {s : ℝ} (hs : s∈Icc 0 frameCap) :
    0≤Real.sin s ∧ 0≤1-Real.cos s ∧ 1-Real.cos s≤(2/5)*Real.sin s := by
  have hsin := Real.sin_ge_sub_cube hs.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  have h0 : 0 ≤ s := hs.1
  have h1 : s ≤ 7/10 := hs.2
  have hs2 : s^2≤(7/10)*s := by nlinarith
  have hs3 : s^3≤(49/100)*s := by nlinarith
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_three]),
    sub_nonneg.mpr (Real.cos_le_one s),by linarith⟩

structure PairDomain (A Y a b : ℝ) : Prop where
  A_nonneg : 0≤A
  Y_nonneg : 0≤Y
  a_nonneg : 0≤a
  b_nonneg : 0≤b
  outer_sorted : Y≤A
  anchor_sorted : b≤a
  A_upper : A<3/2
  a_upper : a<3/2
  Y_upper : Y<1
  b_upper : b<1
  circle_comparison : (a-Y)*(a+Y+1)≤(A-b)*(A+b+1)

theorem coordinate_bounds {q : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (hc : p.Contained q) (hq : q≤qCap) : p.a<3/2 ∧ |p.y|<1 := by
  have hcircle : (p.a+1/2)^2+(|p.y|+1/2)^2≤qCap := hc.trans hq
  have hb := abs_nonneg p.y
  have hsort : (|p.y|+1/2)^2≤(p.a+1/2)^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith [hs.2]) 2
  have hcap : qCap<4 := by norm_num [qCap]
  constructor
  · nlinarith [sq_nonneg (|p.y|+1/2),hs.1]
  · nlinarith

theorem actual_domain {q : ℝ} {E P : SignedPoint}
    (hE : E.Sorted) (hEq : E.Outer q) (hP : P.Sorted) (hPq : P.Contained q)
    (hq : q≤qCap) : PairDomain E.a |E.y| P.a |P.y| := by
  have hEr := coordinate_bounds hE (show E.Contained q from hEq.le) hq
  have hPr := coordinate_bounds hP hPq hq
  have hcircle : (P.a+1/2)^2+(|P.y|+1/2)^2≤(E.a+1/2)^2+(|E.y|+1/2)^2 := by
    change P.circle≤E.circle
    rw [hEq]
    exact hPq
  exact ⟨hE.1.le,abs_nonneg _,hP.1.le,abs_nonneg _,hE.2,hP.2,
    hEr.1,hPr.1,hEr.2,hPr.2,by nlinarith⟩

theorem minus_comparison {A Y a b s : ℝ} (h : PairDomain A Y a b)
    (hs : s∈Icc 0 frameCap) :
    0≤(A-b)*Real.sin s-(a-Y)*(1-Real.cos s) := by
  have ht := trigonometric_comparison hs
  by_cases hdiff : a≤Y
  · have hAb : 0≤A-b := by linarith [h.outer_sorted,h.anchor_sorted]
    have h1 := mul_nonneg hAb ht.1
    have h2 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdiff) ht.2.1
    linarith
  · have hdiff' : 0≤a-Y := by linarith
    have hden : 0<A+b+1 := by linarith [h.A_nonneg,h.b_nonneg]
    have hnum : (2/5)*(A+b+1)≤a+Y+1 := by
      linarith [h.A_upper,h.anchor_sorted,h.a_nonneg,h.Y_nonneg]
    have hmul := mul_le_mul_of_nonneg_left hnum hdiff'
    have hcoef : (2/5)*(a-Y)≤A-b := by
      apply (mul_le_mul_iff_left₀ hden).mp
      nlinarith [h.circle_comparison]
    have hfirst := mul_le_mul_of_nonneg_right hcoef ht.1
    have hsecond := mul_le_mul_of_nonneg_left ht.2.2 hdiff'
    nlinarith

theorem plus_comparison {A Y a b s : ℝ} (h : PairDomain A Y a b)
    (hs : s∈Icc 0 frameCap)
    (hprimary : edgeWidth (-s)≤a-A*Real.sin s-Y*Real.cos s) :
    0≤(A-b)*Real.sin s-(a+Y)*(1-Real.cos s) := by
  have ht := trigonometric_comparison hs
  have hwidth := edgeWidth_ge_one (-s)
  have hphi : 0≤Real.sin s-(1-Real.cos s) := by linarith [ht.1,ht.2.2]
  have hrot1 := mul_nonneg (sub_nonneg.mpr h.outer_sorted) ht.1
  have hrot2 := mul_nonneg h.Y_nonneg hphi
  have hdiff : 1≤a-Y := by nlinarith
  have hsum : 0≤a+Y := add_nonneg h.a_nonneg h.Y_nonneg
  have hsumU : a+Y<2 := by linarith [h.a_upper]
  have hden : 0<A+b+1 := by linarith [h.A_nonneg,h.b_nonneg]
  have hdenU : A+b+1≤7/2 := by linarith [h.A_upper,h.b_upper]
  have hproduct := mul_le_mul_of_nonneg_left hdenU
    (show 0≤(2/5)*(a+Y) by positivity)
  have hnum := mul_le_mul_of_nonneg_right hdiff
    (show 0≤a+Y+1 by linarith)
  have hcoef : (2/5)*(a+Y)≤A-b := by
    apply (mul_le_mul_iff_left₀ hden).mp
    nlinarith [h.circle_comparison]
  have hfirst := mul_le_mul_of_nonneg_right hcoef ht.1
  have hsecond := mul_le_mul_of_nonneg_left ht.2.2 hsum
  nlinarith

theorem DE_negative {q s : ℝ} {D E : SignedPoint}
    (hE : E.Sorted) (hEq : E.Outer q) (hD : D.Sorted) (hDq : D.Contained q)
    (hq : q≤qCap) (hyD : D.y≤0) (hs : s∈Icc 0 frameCap)
    (hf : quarterFeasible D E (-s) 3) : quarterFeasible D E (-s) 2 := by
  have hg := actual_domain hE hEq hD hDq hq
  have hf3 : edgeWidth (-s) ≤ D.a+E.a*Real.sin (-s)-E.y*Real.cos (-s) := hf
  rw [Real.sin_neg,Real.cos_neg] at hf3
  have hcomp : 0≤(E.a+D.y)*Real.sin s-(D.a+E.y)*(1-Real.cos s) := by
    by_cases hyE : E.y≤0
    · have hh := minus_comparison hg hs
      simpa only [abs_of_nonpos hyE,abs_of_nonpos hyD,sub_neg_eq_add] using hh
    · have hyE' : 0≤E.y := (lt_of_not_ge hyE).le
      have hprimary : edgeWidth (-s)≤D.a-E.a*Real.sin s-|E.y| * Real.cos s := by
        rw [abs_of_nonneg hyE']; linarith
      have hh := plus_comparison hg hs hprimary
      simpa only [abs_of_nonneg hyE',abs_of_nonpos hyD,sub_neg_eq_add] using hh
  show edgeWidth (-s) ≤ D.a*Real.cos (-s)-D.y*Real.sin (-s)-E.y
  rw [Real.sin_neg,Real.cos_neg]
  nlinarith

theorem EH_negative {q s : ℝ} {E H : SignedPoint}
    (hE : E.Sorted) (hEq : E.Outer q) (hH : H.Sorted) (hHq : H.Contained q)
    (hq : q≤qCap) (hyH : 0≤H.y) (hs : s∈Icc 0 frameCap)
    (hf : quarterFeasible E H (-s) 1) : quarterFeasible E H (-s) 0 := by
  have hf' : quarterFeasible H.reflect E.reflect (-s) 3 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect E H (-s) 1).2 hf
  have hh := DE_negative (D := H.reflect) (E := E.reflect)
    (by simpa using hE) (by simpa using hEq) (by simpa using hH)
    (by simpa using hHq) hq (by simpa [SignedPoint.reflect] using neg_nonpos.mpr hyH) hs hf'
  exact (quarterFeasible_reflect E H (-s) 0).1 (by simpa [reflectedOwner] using hh)

theorem DE_nonpositive {q d : ℝ} {D E : SignedPoint}
    (hE : E.Sorted) (hEq : E.Outer q) (hD : D.Sorted) (hDq : D.Contained q)
    (hq : q≤qCap) (hyD : D.y≤0) (hd : d≤0) (hsmall : |d|≤frameCap)
    (hf : quarterFeasible D E d 3) : quarterFeasible D E d 2 := by
  have hs : -d∈Icc 0 frameCap := ⟨neg_nonneg.mpr hd,(neg_le_abs _).trans hsmall⟩
  simpa only [neg_neg] using DE_negative hE hEq hD hDq hq hyD hs (by simpa using hf)

theorem EH_nonpositive {q d : ℝ} {E H : SignedPoint}
    (hE : E.Sorted) (hEq : E.Outer q) (hH : H.Sorted) (hHq : H.Contained q)
    (hq : q≤qCap) (hyH : 0≤H.y) (hd : d≤0) (hsmall : |d|≤frameCap)
    (hf : quarterFeasible E H d 1) : quarterFeasible E H d 0 := by
  have hs : -d∈Icc 0 frameCap := ⟨neg_nonneg.mpr hd,(neg_le_abs _).trans hsmall⟩
  simpa only [neg_neg] using EH_negative hE hEq hH hHq hq hyH hs (by simpa using hf)

theorem cycle_DE {q : ℝ} {C : SignedCycle} (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hq : q≤qCap) (hE : (C.point E).Outer q) (hd : delta C.theta D≤0)
    (hf : C.Feasible D 3) : C.Feasible D 2 := by
  have hlocal : quarterFeasible (C.point D) (C.point E) (delta C.theta D) 3 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,next,D,E,
      quarterFeasible,sub_nonneg] using hf
  have hh := DE_nonpositive (hC.sorted E) hE (hC.sorted D) (hC.contained D) hq hn.D_nonpos
    hd (hC.spread (next D) D) hlocal
  simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,next,D,E,
    quarterFeasible,sub_nonneg] using hh

theorem cycle_EH {q : ℝ} {C : SignedCycle} (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hq : q≤qCap) (hE : (C.point E).Outer q) (hd : delta C.theta E≤0)
    (hf : C.Feasible E 1) : C.Feasible E 0 := by
  have hlocal : quarterFeasible (C.point E) (C.point H) (delta C.theta E) 1 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,next,E,H,
      quarterFeasible,sub_nonneg] using hf
  have hh := EH_nonpositive (hC.sorted E) hE (hC.sorted H) (hC.contained H) hq hn.H_nonneg
    hd (hC.spread (next E) E) hlocal
  simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,next,E,H,
    quarterFeasible,sub_nonneg] using hh

end SquaresInCircles.Eight.OuterEPrimaryComparison
