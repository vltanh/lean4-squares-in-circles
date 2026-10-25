module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Boundary.ActualOrdinaryBlocks
public import SquaresInCircles.Eight.Owners.Quarter.SignScalar

/-!
# Eight squares: endpoint domains beside a putative core quarter anchor

Beside a core vertex, the zero and high-quarter projections determine the only exceptional marker
cases. A negative left endpoint forces the zero owner `2`, a positive error and an outer left point
(`left_negative_domain`); a positive right endpoint forces the quarter owner `3`, a positive error
and an outer right point (`right_positive_domain`). In each case a coefficient `mass` bounds the
signed marker of the endpoint (`left_mass_exists`, `right_mass_exists`).
-/

section
/-!
## The original common marker dominates `.86` times the transverse coordinate

The proof covers each complete intrinsic chart and both core pieces.
No vertex is moved and a chart-junction marker is not reselected.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalOuterAnchor

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign
open FrameCircleArc FrameLowArc FrameMidArc

def k : ℝ := 43/50
def m : ℝ := 111/100

theorem marker_lower (s : State) : k*s.b≤unsigned s := by
  by_cases hcore : s.branch.type=0
  · have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hcore)).2.1
    have hh := core_marker_lower s hcore
    dsimp [k]
    nlinarith [s.b_nonneg]
  · cases hb : s.branch with
    | coreSide | coreCorner => simp [hb,Branch.type] at hcore
    | low =>
        have hax := axial_loss s hcore
        have hid : (a0-s.a)*(a0+s.a+1)=s.b^2+s.b := by
          have hcircle := s.outer_eq hcore
          have haxis := CommonQuarter.axial_circle
          change (a0+1/2)^2+(1/2:ℝ)^2=Q0 at haxis
          nlinarith
        have hcut : 4*s.b ≤ s.a := by simpa [hb,TypeMem] using s.type_mem
        have hden : s.b+1≤(2/5)*(a0+s.a+1) := by
          nlinarith [a0_bounds.1,primary_lower s]
        have hprod := mul_le_mul_of_nonneg_left hden s.b_nonneg
        have hdenpos : 0<a0+s.a+1 := by linarith [a0_bounds.1,s.a_pos]
        have hloss : a0-s.a≤(2/5)*s.b := by
          have hh : (a0-s.a-(2/5)*s.b)*(a0+s.a+1)≤0 := by nlinarith
          have hn := nonpos_of_mul_nonpos_left hh hdenpos
          linarith
        dsimp [unsigned]
        rw [hb]
        dsimp [FramePair.label,k]
        nlinarith [s.b_nonneg]
    | middle =>
        have hchart := state_mid_chart s hb
        have hh := linear_endpoint_lower (p := (1489593/1000000:ℝ))
          (q := (720219/1000000:ℝ)) (by norm_num) b1_mem.1 b2_mem.2 hchart.2
        have hleft : (85723/40000:ℝ)≤linear (1489593/1000000) (720219/1000000) b1 := by
          rw [linear,A_b1]
          dsimp [b1]
          nlinarith [a1_bounds.1]
        have hright : (85723/40000:ℝ)≤linear (1489593/1000000) (720219/1000000) b2 := by
          rw [linear,A_b2]
          dsimp [b2]
          nlinarith [a2_bounds.1]
        have hlow := (le_min hleft hright).trans hh
        dsimp [unsigned]
        rw [hb]
        dsimp [FramePair.label,k]
        rw [hchart.1]
        dsimp [linear] at hlow
        linarith
    | high =>
        let u : ℝ := 8898/15625
        let v : ℝ := 43/50-195443/500000
        have hsupport := state_support s u v
        have hnorm : Real.sqrt (u^2+v^2)<37/50 := by
          have hh := Real.sq_sqrt (show 0≤u^2+v^2 by positivity)
          have hz := Real.sqrt_nonneg (u^2+v^2)
          dsimp [u,v] at *
          nlinarith
        have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
        have hprod := (mul_lt_mul_of_pos_left hnorm hR).trans
          (mul_lt_mul_of_pos_right CommonQuarter.radius_bounds.2
            (by norm_num : (0:ℝ)<37/50))
        dsimp [unsigned]
        rw [hb]
        dsimp [FramePair.label,k,u,v] at *
        nlinarith [c0_bounds.1,Arithmetic.pi_hand_enclosure.1]

end SquaresInCircles.Eight.GlobalOuterAnchor
end
end
end

section
/-!
## Whole-interval scalar costs for two-edge radial anchor rigidity

The tangent quotient is bounded directly by alternating Taylor
polynomials on the full frame interval.  Negative angle costs share
the one actual endpoint-frame budget of their consecutive path.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalOuterAnchor

def secondaryAngle (lam d : ℝ) : ℝ := d+lam*(|Real.sin d|-Real.sin d)/2
def primaryAngle (lam a d : ℝ) : ℝ := d+lam*(|Real.sin d|/2-a*Real.sin d)/Real.cos d
def negativeCost (z : ℝ) : ℝ := -z+k*Real.sin z

theorem signed_trig {d : ℝ} (hd : |d|≤frameCap) :
    19/25<Real.cos d ∧ Real.cos d≤1 ∧ |Real.sin d|<13/20 := by
  have hc := CommonQuarter.signed_cos (by simpa only [frameCap] using hd)
  have hs := CommonQuarter.signed_sin (by simpa only [frameCap] using hd)
  exact ⟨by linarith,hc.2,by linarith⟩

theorem secant_upper {d : ℝ} (hd : |d|≤frameCap) :
    0<1/Real.cos d ∧ 1≤1/Real.cos d ∧ 1/Real.cos d<25/19 := by
  have ht := signed_trig hd
  have hc : 0<Real.cos d := by linarith [ht.1]
  refine ⟨div_pos (by norm_num) hc,?_,?_⟩
  · exact (le_div_iff₀ hc).2 (by linarith [ht.2.1])
  · exact (div_lt_iff₀ hc).2 (by linarith [ht.1])

theorem sine_cosine_sum_upper (d : ℝ) : Real.sin d+Real.cos d<10/7 := by
  by_contra! hn
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10/7) hn 2
  nlinarith [Real.sin_sq_add_cos_sq d,sq_nonneg (Real.sin d-Real.cos d)]

theorem tangent_ratio {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0≤Real.sin x/Real.cos x ∧ Real.sin x/Real.cos x≤(61/50)*x := by
  have ht := transport_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  refine ⟨div_nonneg ht.2.2.1 hc.le,?_⟩
  apply (div_le_iff₀ hc).2
  have hxU : x≤(7/10:ℝ) := by simpa only [frameCap] using hx.2
  have h2 := pow_le_pow_left₀ hx.1 hxU 2
  have h6 := pow_le_pow_left₀ hx.1 hxU 6
  norm_num at h2 h6
  have hpoly : 0≤(11/50:ℝ)-(133/300)*x^2+(17/400)*x^4-(61/36000)*x^6 := by
    nlinarith [pow_nonneg hx.1 4]
  have hprod := mul_nonneg hx.1 hpoly
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_six hx.1)
    (show 0≤(61/50:ℝ)*x from mul_nonneg (by norm_num) hx.1)
  have hsin := sin_upper_five hx.1
  nlinarith only [hprod,hcos,hsin]

theorem sine_le_ratio {x : ℝ} (hx : x∈Icc 0 frameCap) :
    Real.sin x≤Real.sin x/Real.cos x := by
  have ht := transport_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  apply (le_div_iff₀ hc).2
  nlinarith [mul_nonneg ht.2.2.1 (sub_nonneg.mpr (Real.cos_le_one x))]

theorem secondary_positive {lam d : ℝ} (hd : d∈Icc 0 frameCap) :
    secondaryAngle lam d=d := by
  rw [secondaryAngle,abs_of_nonneg (transport_trig hd).2.2.1]
  ring

theorem secondary_negative {lam x : ℝ} (hx : x∈Icc 0 frameCap) :
    secondaryAngle lam (-x)= -x+lam*Real.sin x := by
  rw [secondaryAngle,Real.sin_neg,abs_neg,
    abs_of_nonneg (transport_trig hx).2.2.1]
  ring

theorem primary_positive {lam a d : ℝ} (hd : d∈Icc 0 frameCap) :
    primaryAngle lam a d=d-lam*(a-1/2)*(Real.sin d/Real.cos d) := by
  rw [primaryAngle,abs_of_nonneg (transport_trig hd).2.2.1]
  ring

theorem primary_negative {lam a x : ℝ} (hx : x∈Icc 0 frameCap) :
    primaryAngle lam a (-x)= -x+lam*(a+1/2)*(Real.sin x/Real.cos x) := by
  rw [primaryAngle,Real.sin_neg,Real.cos_neg,abs_neg,
    abs_of_nonneg (transport_trig hx).2.2.1]
  ring

theorem primary_k_positive_nonneg {a d : ℝ}
    (ha : a≤283/200) (hd : d∈Icc 0 frameCap) : 0≤primaryAngle k a d := by
  have hr := tangent_ratio hd
  have h₁ := mul_le_mul_of_nonneg_right (show a-1/2≤(183/200:ℝ) by linarith) hr.1
  have h₂ := mul_le_mul_of_nonneg_left hr.2 (by norm_num : (0:ℝ)≤183/200)
  rw [primary_positive hd]
  dsimp [k]
  nlinarith [hd.1]

theorem primary_m_positive_lower {a d : ℝ}
    (ha : a≤283/200) (hd : d∈Icc 0 frameCap) :
    -(17/100:ℝ)<primaryAngle m a d := by
  have hr := tangent_ratio hd
  have h₁ := mul_le_mul_of_nonneg_right (show a-1/2≤(183/200:ℝ) by linarith) hr.1
  have h₂ := mul_le_mul_of_nonneg_left hr.2 (by norm_num : (0:ℝ)≤183/200)
  rw [primary_positive hd]
  dsimp [m,frameCap] at *
  nlinarith [hd.2]

theorem primary_k_negative_lower {a x : ℝ}
    (ha : 447/800≤a) (hx : x∈Icc 0 frameCap) :
    negativeCost x≤primaryAngle k a (-x) := by
  have hr := tangent_ratio hx
  have hprod := mul_le_mul_of_nonneg_right (show 1≤a+1/2 by linarith) hr.1
  have hs := sine_le_ratio hx
  rw [primary_negative hx]
  dsimp [negativeCost,k]
  nlinarith

theorem secondary_k_lower {d : ℝ} (hd : |d|≤frameCap) :
    negativeCost (max 0 (-d))≤ secondaryAngle k d := by
  by_cases hp : 0≤d
  · rw [max_eq_left (by linarith : -d≤0),secondary_positive ⟨hp,(le_abs_self d).trans hd⟩]
    simpa [negativeCost] using hp
  · have hn : d≤0 := by linarith
    rw [max_eq_right (by linarith : 0≤ -d)]
    have hh := secondary_negative (lam:=k) (show -d∈Icc 0 frameCap from
      ⟨by linarith,(neg_le_abs d).trans hd⟩)
    simpa only [neg_neg,negativeCost] using hh.ge

theorem primary_k_lower {a d : ℝ} (ha : 447/800≤a) (hA : a≤283/200)
    (hd : |d|≤frameCap) :
    negativeCost (max 0 (-d))≤primaryAngle k a d := by
  by_cases hp : 0≤d
  · rw [max_eq_left (by linarith : -d≤0)]
    simpa [negativeCost] using primary_k_positive_nonneg hA ⟨hp,(le_abs_self d).trans hd⟩
  · rw [max_eq_right (by linarith : 0≤ -d)]
    have hh := primary_k_negative_lower ha
      (show -d∈Icc 0 frameCap from ⟨by linarith,(neg_le_abs d).trans hd⟩)
    simpa only [neg_neg] using hh

theorem negative_cost_sum {x y : ℝ} (hx : 0≤x) (hy : 0≤y)
    (hsum : x+y≤frameCap) : -(3/20:ℝ)<negativeCost x+negativeCost y := by
  have hsx := Real.sin_ge_sub_cube hx
  have hsy := Real.sin_ge_sub_cube hy
  have hcube := pow_le_pow_left₀ (add_nonneg hx hy) hsum 3
  have hcross := mul_nonneg (mul_nonneg hx hy) (add_nonneg hx hy)
  have hcubes : x^3+y^3≤(7/10:ℝ)^3 := by
    dsimp [frameCap] at hcube
    nlinarith
  dsimp [negativeCost,k,frameCap] at *
  nlinarith

theorem negative_cost_lower {x : ℝ} (hx : x∈Icc 0 frameCap) :
    -(3/20:ℝ)<negativeCost x := by
  have hh := negative_cost_sum hx.1 (show (0:ℝ)≤0 by norm_num)
    (by simpa only [add_zero] using hx.2)
  simpa [negativeCost] using hh

theorem negative_parts_sum {v d : ℝ} (hv : |v|≤frameCap) (hd : |d|≤frameCap)
    (hsum : |v+d|≤frameCap) : max 0 (-v)+max 0 (-d)≤frameCap := by
  by_cases hv0 : 0≤v <;> by_cases hd0 : 0≤d
  · simp only [max_eq_left (by linarith : -v≤0),max_eq_left (by linarith : -d≤0),zero_add]
    norm_num [frameCap]
  · rw [max_eq_left (by linarith : -v≤0),max_eq_right (by linarith : 0≤ -d),zero_add]
    exact (neg_le_abs d).trans hd
  · rw [max_eq_right (by linarith : 0≤ -v),max_eq_left (by linarith : -d≤0),add_zero]
    exact (neg_le_abs v).trans hv
  · rw [max_eq_right (by linarith : 0≤ -v),max_eq_right (by linarith : 0≤ -d)]
    linarith [(neg_le_abs (v+d)).trans hsum]

end SquaresInCircles.Eight.GlobalOuterAnchor
end
end
end

section
/-!
## Same-state reselection of every nonpositive outer-E primary

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
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalOuterAnchor

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign

def width (d : ℝ) : ℝ := (1+Real.cos d+|Real.sin d|)/2
def transverse (s : State) : ℝ := sign s.positive*s.b
def mass (bad : Bool) : ℝ := if bad then m else k
def leftOwner (primary : Bool) : Fin 4 := if primary then 2 else 0
def rightOwner (primary : Bool) : Fin 4 := if primary then 3 else 2

def leftProjection (primary : Bool) (s c : State) (d : ℝ) : ℝ :=
  if primary then s.a*Real.sin d+transverse s*Real.cos d+c.b
  else transverse s+c.a*Real.sin d+c.b*Real.cos d

def rightProjection (primary : Bool) (c t : State) (d : ℝ) : ℝ :=
  if primary then c.a+t.a*Real.sin d-transverse t*Real.cos d
  else c.a*Real.cos d+c.b*Real.sin d-transverse t

theorem width_ge_one {d : ℝ} (hd : |d|≤frameCap) : 1≤width d := by
  rw [width,← CommonQuarter.signed_width (by simpa only [frameCap] using hd)]
  exact CommonQuarter.width_ge_one d

theorem left_margin (s c : State) (p : Bool) {d : ℝ} (hd : |d|≤frameCap)
    (hc : transverse c≤0) :
    s.Feasible c (leftOwner p) d ↔ width d≤leftProjection p s c d := by
  have hy := transverse_nonpos_eq c hc
  cases p <;>
    simp [leftOwner,leftProjection,transverse,State.Feasible,forwardMargin,
      CommonQuarter.signed_width (by simpa only [frameCap] using hd),width,hy]

theorem right_margin (c t : State) (p : Bool) {d : ℝ} (hd : |d|≤frameCap)
    (hc : transverse c≤0) :
    c.Feasible t (rightOwner p) (Real.pi/2+d) ↔ width d≤rightProjection p c t d := by
  have hy := transverse_nonpos_eq c hc
  cases p <;>
    simp [rightOwner,rightProjection,transverse,State.Feasible,forwardMargin,
      Real.sin_add,Real.cos_add,
      CommonQuarter.quarter_width (by simpa only [frameCap] using hd),width,hy]

theorem core_bounds (c : State) (hc : c.branch.type=0) :
    c.a≤7/12 ∧ c.b≤7/12 ∧ c.a^2+c.b^2<1 := by
  have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart c hc)).2.1
  have hb := c.canonical.trans ha
  have h1 := pow_le_pow_left₀ c.a_pos.le ha 2
  have h2 := pow_le_pow_left₀ c.b_nonneg hb 2
  exact ⟨ha,hb,by norm_num at h1 h2; linarith⟩

theorem sine_nonpos {d : ℝ} (hd : |d|≤frameCap) (hn : d≤0) : Real.sin d≤0 := by
  have hx : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
  have hh := (transport_trig hx).2.2.1
  simpa only [Real.sin_neg,neg_nonneg] using hh

theorem left_negative_domain (s c : State) (p : Bool) {d : ℝ}
    (hcore : c.branch.type=0) (hd : |d|≤frameCap)
    (hs : transverse s<0) (hm : width d≤leftProjection p s c d) :
    p=true ∧ 0<d ∧ s.branch.type≠0 := by
  have hcb := core_bounds c hcore
  have hw := width_ge_one hd
  have hcos : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  cases p with
  | false =>
      exfalso
      have hproj := FrameCoreArc.projection_lt (a:=c.a) (b:=c.b)
        (by norm_num : (0:ℝ)<1) (by rw [one_pow]; exact hcb.2.2) d
      simp only [leftProjection,Bool.false_eq_true,ite_false] at hm
      linarith
  | true =>
      simp only [leftProjection,ite_true] at hm
      have hnegprod := mul_nonpos_of_nonpos_of_nonneg hs.le hcos
      have hdpos : 0<d := by
        by_contra! hn
        have hsin := sine_nonpos hd hn
        have hprod := mul_nonpos_of_nonneg_of_nonpos s.a_pos.le hsin
        linarith [hcb.2.1]
      have ht := transport_trig ⟨hdpos.le,(le_abs_self d).trans hd⟩
      have houter : s.branch.type≠0 := by
        intro hsCore
        have ha := (core_bounds s hsCore).1
        have hp := mul_le_mul ha
          (show Real.sin d≤13/20 by linarith [ht.2.2.2.1]) ht.2.2.1
          (by norm_num : (0:ℝ)≤7/12)
        linarith [hcb.2.1]
      exact ⟨rfl,hdpos,houter⟩

theorem right_positive_domain (c t : State) (p : Bool) {d : ℝ}
    (hcore : c.branch.type=0) (hd : |d|≤frameCap)
    (ht : 0<transverse t) (hm : width d≤rightProjection p c t d) :
    p=true ∧ 0<d ∧ t.branch.type≠0 := by
  have hcb := core_bounds c hcore
  have hw := width_ge_one hd
  have hcos : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  cases p with
  | false =>
      exfalso
      have hproj := FrameCoreArc.projection_lt (a:=c.b) (b:=c.a)
        (by norm_num : (0:ℝ)<1) (by nlinarith [hcb.2.2]) d
      simp only [rightProjection,Bool.false_eq_true,ite_false] at hm
      linarith
  | true =>
      simp only [rightProjection,ite_true] at hm
      have hposprod := mul_nonneg ht.le hcos
      have hdpos : 0<d := by
        by_contra! hn
        have hsin := sine_nonpos hd hn
        have hprod := mul_nonpos_of_nonneg_of_nonpos t.a_pos.le hsin
        linarith [hcb.1]
      have tr := transport_trig ⟨hdpos.le,(le_abs_self d).trans hd⟩
      have houter : t.branch.type≠0 := by
        intro htCore
        have ha := (core_bounds t htCore).1
        have hp := mul_le_mul ha
          (show Real.sin d≤13/20 by linarith [tr.2.2.2.1]) tr.2.2.1
          (by norm_num : (0:ℝ)≤7/12)
        linarith [hcb.1]
      exact ⟨rfl,hdpos,houter⟩

theorem transverse_of_nonneg (s : State) (hs : 0≤transverse s) : transverse s=s.b := by
  cases hp : s.positive <;> simp [transverse,FramePair.sign,hp] at hs ⊢
  linarith [s.b_nonneg]

/-- A coefficient `mass bad` bounds the signed marker of the source,
`mass bad * transverse s ≤ s.signedLabel`, where `bad` occurs only for owner `2` at positive
error. -/
theorem left_mass_exists (s c : State) (p : Bool) {d : ℝ}
    (hcore : c.branch.type=0) (hd : |d|≤frameCap)
    (hm : width d≤leftProjection p s c d) :
    ∃bad : Bool, mass bad*transverse s≤ s.signedLabel ∧
      (bad=true → p=true ∧ 0<d) := by
  by_cases hs : 0≤transverse s
  · refine ⟨false,?_,by simp⟩
    rw [signed_of_nonneg s hs,transverse_of_nonneg s hs]
    exact marker_lower s
  · have hn : transverse s<0 := by linarith
    obtain ⟨hp,hdpos,houter⟩ := left_negative_domain s c p hcore hd hn hm
    refine ⟨true,?_,fun _ => ⟨hp,hdpos⟩⟩
    have hy := transverse_nonpos_eq s hn.le
    have hu := marker_outer_upper s houter
    rw [signed_of_nonpos s hn.le]
    change m*(sign s.positive*s.b)≤ -unsigned s
    rw [hy]
    dsimp [m]
    linarith

/-- The same at the right endpoint, with the sign of the marker reversed in the telescoping path
charge. -/
theorem right_mass_exists (c t : State) (p : Bool) {d : ℝ}
    (hcore : c.branch.type=0) (hd : |d|≤frameCap)
    (hm : width d≤rightProjection p c t d) :
    ∃bad : Bool, -(mass bad*transverse t)≤ -t.signedLabel ∧
      (bad=true → p=true ∧ 0<d) := by
  by_cases ht : transverse t≤0
  · refine ⟨false,?_,by simp⟩
    have hy := transverse_nonpos_eq t ht
    rw [signed_of_nonpos t ht]
    change -(k*(sign t.positive*t.b))≤ -(-unsigned t)
    rw [hy]
    linarith [marker_lower t]
  · have hp : 0<transverse t := by linarith
    obtain ⟨hq,hdpos,houter⟩ := right_positive_domain c t p hcore hd hp hm
    refine ⟨true,?_,fun _ => ⟨hq,hdpos⟩⟩
    rw [signed_of_nonneg t hp.le,transverse_of_nonneg t hp.le]
    have hu := marker_outer_upper t houter
    dsimp [mass,m]
    linarith

end SquaresInCircles.Eight.GlobalOuterAnchor
end
end
end
