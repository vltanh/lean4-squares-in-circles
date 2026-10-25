module

public import SquaresInCircles.Eight.TableFree.GlobalOuterAnchorDomain

/-!
# The original negative low-quarter primary and its comparison vector

For a negative source and a positive target, a negative original owner 1
either has the actual owner 0 as well, or forces its source onto the flat
core side with a small transverse coordinate.  The proof compares the
same target corner with one explicit vector.  It does not move a frame,
replace a circle, or assume a preferred weak separator.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalQuarterNegativePrimary

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor

theorem low_zero_margin (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hs : transverse s≤0) (ht : 0≤transverse t) :
    s.Feasible t 0 (Real.pi/2+d) ↔
      GlobalOuterAnchor.width d≤ -s.b+t.a*Real.cos d+t.b*Real.sin d := by
  have hsy := transverse_nonpos_eq s hs
  have hty := transverse_of_nonneg t ht
  change sign t.positive*t.b=t.b at hty
  simp only [State.Feasible,forwardMargin,Matrix.cons_val,Real.sin_add,Real.cos_add,
    Real.sin_pi_div_two,Real.cos_pi_div_two,one_mul,zero_mul,
    CommonQuarter.quarter_width (by simpa only [frameCap] using hd),GlobalOuterAnchor.width]
  simp only [hsy,hty]
  constructor <;> intro hh <;> linarith

theorem low_one_margin (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (hs : transverse s≤0) :
    s.Feasible t 1 (Real.pi/2+d) ↔
      GlobalOuterAnchor.width d≤t.a+s.a*Real.sin d-s.b*Real.cos d := by
  rw [quarter_one_margin s t hd,transverse_nonpos_eq s hs,GlobalOuterAnchor.width]
  constructor <;> intro hh <;> linarith

/-- The corner comparison is strict precisely when the original
secondary is not feasible.  In particular every original tie remains
available in the secondary alternative. -/
theorem comparison_circle (s t : State) {z : ℝ}
    (hz : z∈Ioc 0 frameCap)
    (hs : transverse s≤0) (ht : 0≤transverse t)
    (hp : s.Feasible t 1 (Real.pi/2-z))
    (hn : ¬s.Feasible t 0 (Real.pi/2-z)) :
    (s.a+1/2)^2+(s.b+3/2)^2<Q0 ∧ s.branch.type=0 := by
  have tr := transport_trig (show z∈Icc 0 frameCap from ⟨hz.1.le,hz.2⟩)
  have hz2 : z≤7/10 := hz.2
  have hu : 0<Real.sin z :=
    Real.sin_pos_of_pos_of_lt_pi hz.1 (by linarith [Real.pi_gt_three])
  have hunit : Real.sin z^2+Real.cos z^2=1 := Real.sin_sq_add_cos_sq z
  have hsum : 1≤Real.sin z+Real.cos z := by
    have hh := one_le_abs_cos_add_abs_sin z
    rw [abs_of_pos (by linarith [tr.1] : 0<Real.cos z),abs_of_pos hu] at hh
    linarith
  have hd : |-z|≤frameCap := by rw [abs_neg,abs_of_pos hz.1]; exact hz.2
  have hp' := (low_one_margin s t hd hs).1 (by simpa only [sub_eq_add_neg] using hp)
  have hn' : ¬GlobalOuterAnchor.width (-z)≤ -s.b+t.a*Real.cos (-z)+t.b*Real.sin (-z) :=
    fun hh => hn (by simpa only [sub_eq_add_neg] using (low_zero_margin s t hd hs ht).2 hh)
  rw [not_le] at hn'
  have hwidth : GlobalOuterAnchor.width (-z)=(1+Real.cos z+Real.sin z)/2 := by
    simp [GlobalOuterAnchor.width,abs_of_pos hu]
  rw [hwidth,Real.sin_neg,Real.cos_neg] at hp' hn'
  have hc : 0<Real.cos z := by linarith [tr.1]
  have hcu : Real.sin z<Real.cos z := tr.2.2.2.2
  have hcone : Real.cos z≤1 := tr.2.1
  generalize Real.cos z=c at *
  generalize Real.sin z=u at *
  -- the comparison vector `(X₀,Y₀)` and the target corner `(X,Y)`
  have hK : 0<s.a+1/2 := by linarith [s.a_pos]
  have hD : 0<s.b+1/2 := by linarith [s.b_nonneg]
  have hKD : s.b+1/2 ≤ s.a+1/2 := by linarith [s.canonical]
  have hY₀ : 0<(s.a+1/2)*c-(s.b+1/2)*u := by
    have h1 := mul_nonneg (sub_nonneg.mpr hKD) hc.le
    have h2 := mul_pos hD (sub_pos.mpr hcu)
    linarith
  have hX : 1+(s.b+1/2)*c+(s.a+1/2)*u≤t.a+1/2 := by linarith
  have hdiff : 0<u*((t.b+1/2)-((s.a+1/2)*c-(s.b+1/2)*u))+
      (1-c)*((t.a+1/2)-(1+(s.b+1/2)*c+(s.a+1/2)*u)) := by
    have hh : (s.b+1/2)*(u^2+c^2)=(s.b+1/2)*1 := by rw [hunit]
    linarith
  have hcoef : 0<u*(1+(s.b+1/2)*c+(s.a+1/2)*u)-(1-c)*((s.a+1/2)*c-(s.b+1/2)*u) := by
    have h1 := mul_pos hu (show 0<1+(s.b+1/2) by linarith)
    have h2 := mul_nonneg hK.le (sub_nonneg.mpr hcone)
    have hh : (s.a+1/2)*(u^2+c^2)=(s.a+1/2)*1 := by rw [hunit]
    linarith
  have hdotpos : 0<(1+(s.b+1/2)*c+(s.a+1/2)*u)*((t.a+1/2)-(1+(s.b+1/2)*c+(s.a+1/2)*u))+
      ((s.a+1/2)*c-(s.b+1/2)*u)*((t.b+1/2)-((s.a+1/2)*c-(s.b+1/2)*u)) := by
    have h1 := mul_nonneg hcoef.le (sub_nonneg.mpr hX)
    have h2 := mul_pos hY₀ hdiff
    have hh : 0<u*((1+(s.b+1/2)*c+(s.a+1/2)*u)*((t.a+1/2)-(1+(s.b+1/2)*c+(s.a+1/2)*u))+
        ((s.a+1/2)*c-(s.b+1/2)*u)*((t.b+1/2)-((s.a+1/2)*c-(s.b+1/2)*u))) := by
      linarith
    exact (mul_pos_iff_of_pos_left hu).1 hh
  have hnorm : (1+(s.b+1/2)*c+(s.a+1/2)*u)^2+((s.a+1/2)*c-(s.b+1/2)*u)^2<
      (t.a+1/2)^2+(t.b+1/2)^2 := by
    linarith [sq_nonneg ((t.a+1/2)-(1+(s.b+1/2)*c+(s.a+1/2)*u)),
      sq_nonneg ((t.b+1/2)-((s.a+1/2)*c-(s.b+1/2)*u))]
  have hidentity : (1+(s.b+1/2)*c+(s.a+1/2)*u)^2+((s.a+1/2)*c-(s.b+1/2)*u)^2=
      1+(s.a+1/2)^2+(s.b+1/2)^2+2*((s.b+1/2)*c+(s.a+1/2)*u) := by
    linear_combination ((s.a+1/2)^2+(s.b+1/2)^2)*hunit
  have hmiddle : s.b+1/2≤(s.b+1/2)*c+(s.a+1/2)*u := by
    have h1 := mul_nonneg (sub_nonneg.mpr hKD) hu.le
    have h2 := mul_nonneg hD.le (sub_nonneg.mpr hsum)
    linarith
  have hcircle : (t.a+1/2)^2+(t.b+1/2)^2≤Q0 := state_circle t
  have hnecessary : (s.a+1/2)^2+(s.b+1/2+1)^2<Q0 := by linarith
  have hcore : s.branch.type=0 := by
    by_contra ho
    have he : (s.a+1/2)^2+(s.b+1/2)^2=Q0 := s.outer_eq ho
    linarith
  constructor
  · linarith
  · exact hcore

/-- The exceptional primary forces the actual flat-core source and the
strict transverse and angle cuts used in the common stress. -/
theorem exceptional_domain (s t : State) {z : ℝ}
    (hz : z∈Ioc 0 frameCap)
    (hs : transverse s≤0) (ht : 0≤transverse t)
    (hp : s.Feasible t 1 (Real.pi/2-z))
    (hn : ¬s.Feasible t 0 (Real.pi/2-z)) :
    s.branch.type=0 ∧ s.a=7/12 ∧ s.b<39/250 ∧ z<9/20 := by
  obtain ⟨hcircle,hcore⟩ := comparison_circle s t hz hs ht hp hn
  have hb : s.b<1/2 := by
    by_contra! hh
    have ha : 1≤ s.a+1/2 := by linarith [s.canonical]
    have hy : 2≤ s.b+3/2 := by linarith
    norm_num [Q0] at hcircle
    nlinarith
  have ha : s.a=7/12 :=
    (CommonQuarter.core_small_side (FrameCoreArc.state_core_chart s hcore) hb).1
  have hsmall : s.b<39/250 := by
    rw [ha] at hcircle
    norm_num [Q0] at hcircle
    by_contra! hh
    nlinarith [s.b_nonneg]
  have hd : |-z|≤frameCap := by rw [abs_neg,abs_of_pos hz.1]; exact hz.2
  have hm := (low_one_margin s t hd hs).1
    (by simpa only [sub_eq_add_neg] using hp)
  have tr := transport_trig (show z∈Icc 0 frameCap from ⟨hz.1.le,hz.2⟩)
  have hwidth : GlobalOuterAnchor.width (-z)=(1+Real.cos z+Real.sin z)/2 := by
    simp [GlobalOuterAnchor.width,abs_of_nonneg tr.2.2.1]
  rw [hwidth,Real.sin_neg,Real.cos_neg,ha] at hm
  have hmono : MonotoneOn (fun u : ℝ => 1+(1/2)*Real.cos u+(13/12)*Real.sin u)
      (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · fun_prop
    · intro u _
      convert ((hasDerivAt_const u 1).add ((Real.hasDerivAt_cos u).const_mul (1/2))).add
        ((Real.hasDerivAt_sin u).const_mul (13/12)) using 1 <;> ring
    · intro u hu
      have hh := transport_trig (Ioo_subset_Icc_self hu)
      linarith [hh.1,hh.2.2.2.1]
  have hangle : z<9/20 := by
    by_contra! hh
    have hlow := hmono (show (9/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
      ⟨hz.1.le,hz.2⟩ hh
    have hc := cos_lower_six (show (0:ℝ)≤9/20 by norm_num)
    have hsin := sin_lower_seven (show (0:ℝ)≤9/20 by norm_num)
    have hbprod := mul_nonneg s.b_nonneg (show 0≤Real.cos z by linarith [tr.1])
    have htbound := (coordinates t).2.1
    norm_num at hc hsin
    nlinarith
  exact ⟨hcore,ha,hsmall,hangle⟩

theorem secondary_of_large_source (s t : State) {z : ℝ}
    (hz : z∈Icc 0 frameCap)
    (hs : transverse s≤0) (ht : 0≤transverse t)
    (hb : 29/100<s.b)
    (hp : s.Feasible t 1 (Real.pi/2-z)) :
    s.Feasible t 0 (Real.pi/2-z) := by
  by_cases hz0 : z=0
  · subst z
    have h1 := (low_one_margin s t (d:=0) (by norm_num [frameCap]) hs).1 (by simpa using hp)
    have h2 := (low_zero_margin s t (d:=0) (by norm_num [frameCap]) hs ht).2
      (by simp only [Real.sin_zero,Real.cos_zero] at h1 ⊢; linarith)
    simpa using h2
  · by_contra hn
    have hh := (exceptional_domain s t ⟨lt_of_le_of_ne hz.1 (Ne.symm hz0),hz.2⟩
      hs ht hp hn).2.2.1
    linarith

/-- Deleting the negative exceptional primary pays the full `.09` times
its angle.  A cubic sine lower bound already gives a strict reserve. -/
theorem exceptional_gain (s t : State) {z : ℝ}
    (hz : z∈Ioc 0 frameCap)
    (hs : transverse s≤0) (ht : 0≤transverse t)
    (hp : s.Feasible t 1 (Real.pi/2-z))
    (hn : ¬s.Feasible t 0 (Real.pi/2-z)) :
    (9/100)*z< -z+(13/10)*((s.a+1/2)*Real.sin z-
      (s.b+1/2)*(1-Real.cos z)) := by
  obtain ⟨_,ha,hb,hzsmall⟩ := exceptional_domain s t hz hs ht hp hn
  have hz0 : 0<z := hz.1
  have hsin := Real.sin_ge_sub_cube hz.1.le
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hcost : 0≤1-Real.cos z := sub_nonneg.mpr (Real.cos_le_one z)
  have hcoeff := mul_le_mul_of_nonneg_right
    (show s.b+1/2≤82/125 by linarith) hcost
  have hsq : z^2≤(9/20)*z := by nlinarith [mul_nonneg hz.1.le (by linarith : 0≤9/20-z)]
  have hcube : z^3≤(81/400)*z := by
    have hh := mul_le_mul_of_nonneg_left hsq hz.1.le
    nlinarith
  rw [ha]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalQuarterNegativePrimary
