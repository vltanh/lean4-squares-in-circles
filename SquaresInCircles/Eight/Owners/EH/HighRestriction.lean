module

public import SquaresInCircles.Eight.Owners.All.HighCycle
public import SquaresInCircles.Eight.Owners.EH.Support
public import SquaresInCircles.Eight.Owners.Zero.SourceOuter

/-!
# Eight squares: a high EH axis forces every BT axis low

A weak EH witness of a high owner makes every GA witness high (`frame_GA_high_of_EH_high`); with
the sign implication at DE, a high BT witness would then make all four quarter edges high, which
the all-high cycle obstruction excludes (`frame_high_EH_high_BT_false`). The conclusions quantify
over the weak witnesses of the cycle.
-/

section
/-!
## Opposed errors use one original intermediate circle

The common state receives both forces before its circle is supported.
The positive residual has the usual full-circle cost; the negative
residual has the primary-lower-bound cost.  This supplies the complete
remaining three-error reserve for either original HG secondary.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalEH

open FramePair ZeroPrimary GlobalZeroSign GlobalOuterAnchor

theorem one_sub_cos_le_half_sin {z : ℝ} (hz : z∈Icc 0 frameCap) :
    1-Real.cos z≤(1/2)*Real.sin z := by
  have hc := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hs := Real.sin_ge_sub_cube hz.1
  have hz2 : z≤7/10 := hz.2
  have h2 : z^2≤(7/10)*z := by
    nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz2)]
  have h3 : z^3≤(49/100)*z := by
    have hh := mul_le_mul_of_nonneg_left h2 hz.1
    nlinarith
  nlinarith

theorem cosine_sine_residual {z t : ℝ}
    (hz : z∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) :
    1+Real.sin (t-z)≤Real.cos z+Real.sin t := by
  have tz := transport_trig hz
  have tt := transport_trig ht
  have hsmall := one_sub_cos_le_half_sin hz
  have h1 := mul_nonneg (show 0≤Real.cos t-1/2 by linarith [tt.1]) tz.2.2.1
  have h2 := mul_nonneg (sub_nonneg.mpr tz.2.1) tt.2.2.1
  rw [Real.sin_sub]
  nlinarith

theorem residual_norm {z t : ℝ}
    (hz : z∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) (hzt : z≤t) :
    Real.sqrt ((Real.sin t-Real.sin z)^2+(Real.cos z-Real.cos t)^2)=
      2*Real.sin ((t-z)/2) := by
  have hh : (t-z)/2∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc] at hz ht ⊢
    constructor <;> linarith [ht.2,hz.1]
  have tr := transport_trig hh
  have hunitT := Real.sin_sq_add_cos_sq t
  have hunitZ := Real.sin_sq_add_cos_sq z
  have hunitH := Real.sin_sq_add_cos_sq ((t-z)/2)
  have hsub := Real.cos_sub t z
  have hdouble : Real.cos (t-z)=2*(Real.cos ((t-z)/2))^2-1 := by
    have hh := Real.cos_two_mul ((t-z)/2)
    rwa [show 2*((t-z)/2)=t-z by ring] at hh
  have hid : (Real.sin t-Real.sin z)^2+(Real.cos z-Real.cos t)^2=
      (2*Real.sin ((t-z)/2))^2 := by
    linear_combination hunitT+hunitZ+2*hsub-2*hdouble-4*hunitH
  have hp : 0≤2*Real.sin ((t-z)/2) := mul_nonneg (by norm_num) tr.2.2.1
  rw [hid,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]

theorem paired_nonnegative (s : State) {z t : ℝ}
    (hz : z∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) (hzt : z≤t) :
    positiveCost (t-z)≤zeroError s (-z)+primaryError s t := by
  have tz := transport_trig hz
  have tt := transport_trig ht
  have hs := state_support s (Real.sin t-Real.sin z) (Real.cos z-Real.cos t)
  rw [residual_norm hz ht hzt] at hs
  have hangle := cosine_sine_residual hz ht
  dsimp [zeroError,primaryError,positiveCost,GlobalOuterAnchor.width,lam]
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg tz.2.2.1,
    abs_of_nonneg tt.2.2.1]
  nlinarith

def pairedBase (w u : ℝ) : ℝ :=
  ((Real.sin (u+w)+Real.cos (u+w)-1)+(Real.sin u+Real.cos u-1))/2+
    primaryLower*(Real.sin (u+w)-Real.sin u)

def pairedBaseDerivative (w u : ℝ) : ℝ :=
  ((1+2*primaryLower)*Real.cos (u+w)+(1-2*primaryLower)*Real.cos u-
    Real.sin (u+w)-Real.sin u)/2

theorem pairedBase_derivative (w u : ℝ) :
    HasDerivAt (pairedBase w) (pairedBaseDerivative w u) u := by
  have hsin := ((hasDerivAt_id u).add_const w).sin
  have hcos := ((hasDerivAt_id u).add_const w).cos
  convert ((((hsin.add hcos).sub_const 1).add
    (((Real.hasDerivAt_sin u).add (Real.hasDerivAt_cos u)).sub_const 1)).div_const 2).add
      ((hsin.sub (Real.hasDerivAt_sin u)).const_mul primaryLower) using 1
  · rfl
  · dsimp [pairedBaseDerivative]
    ring

theorem pairedBase_at_zero {w t : ℝ} (hw : 0≤w) (ht : 0≤t)
    (hsum : t+w≤frameCap) : pairedBase w 0≤pairedBase w t := by
  have hsum' : t+w≤7/10 := hsum
  have hm : MonotoneOn (pairedBase w) (Icc 0 t) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun u _ => (pairedBase_derivative w u).continuousAt.continuousWithinAt
    · intro u _
      exact pairedBase_derivative w u
    · intro u hu
      have hU : u∈Icc 0 frameCap := ⟨hu.1.le,by simp only [frameCap]; linarith [hu.2]⟩
      have hUW : u+w∈Icc 0 frameCap :=
        ⟨by linarith [hu.1],by simp only [frameCap]; linarith [hu.2]⟩
      have tr := transport_trig hU
      have trw := transport_trig hUW
      have h1 := mul_nonneg
        (show 0≤Real.cos (u+w)-191/250 by linarith [trw.1])
        (show 0≤1+2*primaryLower by norm_num [primaryLower])
      have h2 := mul_nonneg (sub_nonneg.mpr tr.2.1)
        (show 0≤2*primaryLower-1 by norm_num [primaryLower])
      dsimp [pairedBaseDerivative,primaryLower] at *
      linarith [tr.2.2.2.1,trw.2.2.2.1]
  exact hm ⟨le_rfl,ht⟩ ⟨ht,le_rfl⟩ ht

theorem paired_nonpositive (s : State) {z t : ℝ}
    (hz : z∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) (htz : t≤z) :
    negativeCost (z-t)≤zeroError s (-z)+primaryError s t := by
  have tz := transport_trig hz
  have tt := transport_trig ht
  have hsin : Real.sin t≤Real.sin z :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [ht.1,Real.pi_pos])
      (by dsimp [frameCap] at hz; linarith [hz.2,Real.pi_gt_three]) htz
  have hcos : Real.cos z≤Real.cos t :=
    Real.cos_le_cos_of_nonneg_of_le_pi ht.1
      (by dsimp [frameCap] at hz; linarith [hz.2,Real.pi_gt_three]) htz
  have ha := mul_le_mul_of_nonpos_right (primary_lower s).le (sub_nonpos.mpr hsin)
  have hb := mul_nonpos_of_nonneg_of_nonpos s.b_nonneg (sub_nonpos.mpr hcos)
  have hbase := pairedBase_at_zero (show 0≤z-t by linarith) ht.1
    (show t+(z-t)≤frameCap by linarith [hz.2])
  have hid : t+(z-t)=z := by ring
  simp only [pairedBase,zero_add,Real.sin_zero,Real.cos_zero,hid] at hbase
  dsimp [negativeCost,zeroError,primaryError,GlobalOuterAnchor.width,lam]
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg tz.2.2.1,
    abs_of_nonneg tt.2.2.1]
  nlinarith

theorem paired_reserve (s u : State) {r z t : ℝ}
    (hr : r∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap)
    (hspan : |r+t-z|≤frameCap) :
    11/4<pathBase+primaryError u r+zeroError s (-z)+primaryError s t+
      (9/50)*frameCost |r+t-z| := by
  have hrCost := primaryError_positive u hr
  by_cases hzt : z≤t
  · have hs : t-z∈Icc 0 frameCap := by
      simp only [frameCap,mem_Icc] at hz ht ⊢
      constructor <;> linarith [ht.2,hz.1]
    have hp := paired_nonnegative s hz ht hzt
    have hrBound := positiveCost_lower hr
    have hsBound := positiveCost_lower hs
    have htotal : r+t-z∈Icc 0 frameCap :=
      ⟨by linarith [hr.1],(le_abs_self _).trans hspan⟩
    have hh := augmentation_lower htotal
    rw [abs_of_nonneg htotal.1]
    dsimp [pathBase,frameCap] at *
    linarith [htotal.1,htotal.2]
  · have htz : t≤z := le_of_not_ge hzt
    have hw : z-t∈Icc 0 frameCap := by
      simp only [frameCap,mem_Icc] at hz ht ⊢
      constructor <;> linarith [hz.2,ht.1]
    have hp := paired_nonpositive s hz ht htz
    have hh := two_cost_reserve hr hw
    have hid : r-(z-t)=r+t-z := by ring
    rw [hid] at hh
    linarith

def remainingCost (h g : State) (zeroTarget : Bool) (r v t : ℝ) : ℝ :=
  primaryError h r+zeroError (if zeroTarget then h else g) v+primaryError g t

/-- Every surviving primary-error sign and either original zero owner
are covered on their full intrinsic frame domain. -/
theorem remaining_reserve (h g : State) (zeroTarget : Bool) {r v t : ℝ}
    (hr : r∈Icc 0 frameCap) (hv : |v|≤frameCap) (ht : t∈Icc 0 frameCap)
    (hspan : |r+v+t|≤frameCap) :
    11/4<pathBase+remainingCost h g zeroTarget r v t+(9/50)*frameCost |r+v+t| := by
  by_cases hvpos : 0≤v
  · have hvframe : v∈Icc 0 frameCap := ⟨hvpos,(le_abs_self v).trans hv⟩
    have hsum : r+v+t∈Icc 0 frameCap :=
      ⟨by linarith [hr.1,ht.1],(le_abs_self _).trans hspan⟩
    have hH := (positiveCost_lower hr).trans (primaryError_positive h hr)
    have hG := (positiveCost_lower ht).trans (primaryError_positive g ht)
    have hZ := (positiveCost_lower hvframe).trans
      (zeroError_positive (if zeroTarget then h else g) hvframe)
    have hreturn := augmentation_lower hsum
    rw [abs_of_nonneg hsum.1]
    dsimp [remainingCost,pathBase,frameCap] at *
    linarith [hsum.1,hsum.2]
  · have hz : -v∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs v).trans hv⟩
    cases zeroTarget
    · have hid : r+t-(-v)=r+v+t := by ring
      have hh := paired_reserve g h hr hz ht (by simpa only [hid] using hspan)
      rw [hid] at hh
      simp only [remainingCost,neg_neg,Bool.false_eq_true,↓reduceIte] at hh ⊢
      linarith
    · have hid : t+r-(-v)=r+v+t := by ring
      have hh := paired_reserve h g ht hz hr (by simpa only [hid] using hspan)
      rw [hid] at hh
      simp only [neg_neg] at hh
      dsimp [remainingCost]
      linarith

end SquaresInCircles.Eight.GlobalEH
end
end
end

section
/-!
## The complete original high-EH/low-GA three-edge charge

The two endpoint reductions preserve feasible axes at the original
errors.  Their scalar deletion gains pay for the full change in the
return allowance.  Every quarter-primary alternative and both original
HG secondary owners are covered on the actual six frame-difference
bounds.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalEH

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor
open GlobalQuarterNegativePrimary

theorem frameCost_increment {x y : ℝ} (hx : |x|≤frameCap) (hy : |y|≤frameCap) :
    frameCost |x|-frameCost |y|≤|x-y|/2 := by
  have hhalf : MonotoneOn (fun z : ℝ => z/2-frameCost z) (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg (d := fun z => 1/2-(Real.cos z-Real.sin z)/2)
    · exact fun z _ =>
        (((hasDerivAt_id' z).div_const 2).fun_sub
          (frameCost_hasDerivAt z)).continuousAt.continuousWithinAt
    · intro z _
      exact ((hasDerivAt_id' z).div_const 2).fun_sub (frameCost_hasDerivAt z)
    · intro z hz
      have tr := transport_trig (Ioo_subset_Icc_self hz)
      show 0≤1/2-(Real.cos z-Real.sin z)/2
      linarith [tr.2.1,tr.2.2.1]
  have hdom (z : ℝ) (hz : |z|≤frameCap) : |z|∈Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,?_⟩
    dsimp [frameCap] at hz
    linarith [Real.pi_gt_three]
  by_cases hxy : |y|≤|x|
  · have hh := hhalf ⟨abs_nonneg _,hy⟩ ⟨abs_nonneg _,hx⟩ hxy
    have htri : |x|≤|x-y|+|y| := by simpa using abs_sub_le x y 0
    simp only at hh
    linarith
  · have hh := frameCost_monotone (hdom x hx) (hdom y hy) (le_of_not_ge hxy)
    linarith [abs_nonneg (x-y)]

theorem deletion_allowance {r v t r' t' : ℝ}
    (hbefore : |r+v+t|≤frameCap) (hafter : |r'+v+t'|≤frameCap) :
    (9/50)*frameCost |r'+v+t'|≤(9/50)*frameCost |r+v+t|+
      (9/100)*(|r-r'|+|t-t'|) := by
  have hh := frameCost_increment hafter hbefore
  have hid : (r'+v+t')-(r+v+t)=(r'-r)+(t'-t) := by ring
  rw [hid] at hh
  have htri : |(r'-r)+(t'-t)|≤|r-r'|+|t-t'| := by
    simpa only [abs_sub_comm] using abs_add_le (r'-r) (t'-t)
  linarith

def lowProjection (s t : State) (primary : Bool) (d : ℝ) : ℝ :=
  if primary then t.a+s.a*Real.sin d-s.b*Real.cos d
  else -s.b+t.a*Real.cos d+t.b*Real.sin d

def zeroOwner (target : Bool) : Fin 4 := if target then 2 else 0

def zeroProjection (h g : State) (target : Bool) (v : ℝ) : ℝ :=
  if target then h.a*Real.sin v+h.b*Real.cos v+g.b
  else h.b+g.a*Real.sin v+g.b*Real.cos v

def pathCharge (e a : State) (r v t : ℝ) : ℝ :=
  Real.pi+r+v+t-unsigned e-unsigned a

theorem lowProjection_margin (s t : State) (primary : Bool) {d : ℝ}
    (hd : |d|≤frameCap) (hs : transverse s≤0) (ht : 0≤transverse t) :
    s.Feasible t (lowOwner primary) (Real.pi/2+d) ↔
      GlobalOuterAnchor.width d≤lowProjection s t primary d := by
  cases primary
  · exact low_zero_margin s t hd hs ht
  · exact low_one_margin s t hd hs

theorem zeroProjection_margin (h g : State) (target : Bool) {v : ℝ}
    (hv : |v|≤frameCap) (hh : 0≤transverse h) (hg : transverse g≤0) :
    h.Feasible g (zeroOwner target) v ↔ GlobalOuterAnchor.width v≤zeroProjection h g target v := by
  have hhy := transverse_of_nonneg h hh
  have hgy := transverse_nonpos_eq g hg
  change sign h.positive*h.b=h.b at hhy
  cases target <;>
    simp only [zeroOwner,zeroProjection,Bool.false_eq_true,↓reduceIte,
      State.Feasible,forwardMargin,Matrix.cons_val,
      CommonQuarter.signed_width (by simpa only [frameCap] using hv),GlobalOuterAnchor.width]
  all_goals rw [hhy,hgy]; constructor <;> intro hh <;> linarith

theorem stress_lower (e h g a : State) (p q u : Bool) {r v t : ℝ}
    (hE : GlobalOuterAnchor.width r≤lowProjection h e p r)
    (hZ : GlobalOuterAnchor.width v≤zeroProjection h g q v)
    (hA : GlobalOuterAnchor.width t≤lowProjection g a u t) :
    Real.pi+3*lam+lowCost h e p r+
      zeroError (if q then h else g) v+lowCost g a u t≤pathCharge e a r v t := by
  cases p <;> cases q <;> cases u <;>
    dsimp [lowCost,lowProjection,zeroProjection,primaryError,zeroError,
      rotatedCost,pathCharge,lam] at * <;> nlinarith

/-- All original high EH owners and all original low GA owners, both
HG secondaries, all error signs, and both radial kinds at every state. -/
theorem original_path_charge (e h g a : State) {r v t : ℝ}
    (hr : |r|≤frameCap) (hv : |v|≤frameCap) (ht : |t|≤frameCap)
    (hrv : |r+v|≤frameCap) (hvt : |v+t|≤frameCap) (hsum : |r+v+t|≤frameCap)
    (he : transverse e≤0) (hh : 0≤transverse h)
    (hg : transverse g≤0) (ha : 0≤transverse a)
    (jE jZ jA : Fin 4) (hEowner : jE=2 ∨ jE=3)
    (hZowner : jZ=0 ∨ jZ=2) (hAowner : jA=0 ∨ jA=1)
    (hEH : e.Feasible h jE (Real.pi/2+r))
    (hHG : h.Feasible g jZ v)
    (hGA : g.Feasible a jA (Real.pi/2+t)) :
    11/4<pathCharge e a r v t+(9/50)*frameCost |r+v+t| := by
  have hhflip : transverse h.flip≤0 := by
    simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonpos.mpr hh
  have heflip : 0≤transverse e.flip := by
    simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonneg.mpr he
  obtain ⟨j,hj,haxis⟩ : ∃j : Fin 4,(j=0 ∨ j=1) ∧
      h.flip.Feasible e.flip j (Real.pi/2+r) := by
    rcases hEowner with rfl | rfl
    · exact ⟨0,Or.inl rfl,(State.target_secondary_reverse e h _).1 hEH⟩
    · refine ⟨1,Or.inr rfl,?_⟩
      apply (State.target_primary_reverse h.flip e.flip _).2
      simpa [State.flip] using hEH
  obtain ⟨RE⟩ := low_reduction h.flip e.flip hr hhflip heflip j hj haxis
  obtain ⟨RA⟩ := low_reduction g a ht hg ha jA hAowner hGA
  obtain ⟨q,hq⟩ : ∃q : Bool,zeroOwner q=jZ := by
    rcases hZowner with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  have hEprojection : GlobalOuterAnchor.width r≤lowProjection h e RE.primary r := by
    have hp := (lowProjection_margin h.flip e.flip RE.primary hr hhflip heflip).1 RE.feasible
    simpa only [lowProjection,State.flip] using hp
  have hAprojection : GlobalOuterAnchor.width t≤lowProjection g a RA.primary t :=
    (lowProjection_margin g a RA.primary ht hg ha).1 RA.feasible
  have hZprojection : GlobalOuterAnchor.width v≤zeroProjection h g q v :=
    (zeroProjection_margin h g q hv hh hg).1 (by simpa only [hq] using hHG)
  have hstress := stress_lower e h g a RE.primary q RA.primary
    hEprojection hZprojection hAprojection
  have hEcost : -endpointCap+primaryError h RE.error+(9/100)*|r-RE.error|<
      lowCost h e RE.primary r := by
    simpa only [primaryError,lowCost,rotatedCost,unsigned,State.flip] using RE.cost_gain
  have hAcost := RA.cost_gain
  have hRE : RE.error∈Icc 0 frameCap := by
    refine ⟨RE.error_nonneg,?_⟩
    rcases RE.error_eq with heq | heq
    · rw [heq]; norm_num [frameCap]
    · rw [heq]; exact (le_abs_self r).trans hr
  have hRA : RA.error∈Icc 0 frameCap := by
    refine ⟨RA.error_nonneg,?_⟩
    rcases RA.error_eq with heq | heq
    · rw [heq]; norm_num [frameCap]
    · rw [heq]; exact (le_abs_self t).trans ht
  have hspan : |RE.error+v+RA.error|≤frameCap := by
    rcases RE.error_eq with heq | heq <;> rcases RA.error_eq with haq | haq
    · simpa only [heq,haq,zero_add,add_zero] using hv
    · simpa only [heq,haq,zero_add] using hvt
    · simpa only [heq,haq,add_zero] using hrv
    · simpa only [heq,haq] using hsum
  have hremaining := remaining_reserve h g q hRE hv hRA hspan
  have hallowance := deletion_allowance hsum hspan
  have hbase := path_base
  dsimp [remainingCost] at hremaining
  simp only [lam,endpointCap,pathBase] at hstress hEcost hAcost hbase hremaining
  linarith

end SquaresInCircles.Eight.GlobalEH
end
end
end

section
/-!
## Every original high EH axis is excluded in the presence of a low GA axis

The complete three-edge charge is joined to four unchanged original G1
edges.  Their return allowance is bounded by the metric triangle
inequality on the actual four-edge frame path.  No other quarter-owner,
anchor, middle-order or mismatch hypothesis is used.  Fixed-ray
expansion preserves both putative original witnesses at every source
radius in the full interval.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalEH

open Candidate FramePair QuarterWordGeometry GlobalOuterAnchor GlobalQuarterSign

theorem four_edge_return (C : BoundaryCycle Q0) (F : QuarterLift C) :
    frameCost |F.theta A-F.theta E|≤
      frameCost |difference F A|+frameCost |difference F B|+
      frameCost |difference F T|+frameCost |difference F D| := by
  have hrange (i j : Vertex) : |F.theta j-F.theta i|∈Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,?_⟩
    linarith [theta_spread F i j,Real.pi_gt_three]
  have hAT := frameCost_triangle (hrange A B) (hrange B T) (hrange A T)
    ((abs_sub_le (F.theta T) (F.theta B) (F.theta A)).trans_eq (add_comm _ _))
  have hAD := frameCost_triangle (hrange A T) (hrange T D) (hrange A D)
    ((abs_sub_le (F.theta D) (F.theta T) (F.theta A)).trans_eq (add_comm _ _))
  have hAE := frameCost_triangle (hrange A D) (hrange D E) (hrange A E)
    ((abs_sub_le (F.theta E) (F.theta D) (F.theta A)).trans_eq (add_comm _ _))
  have hsum : frameCost |F.theta E-F.theta A|≤
      frameCost |F.theta B-F.theta A|+frameCost |F.theta T-F.theta B|+
      frameCost |F.theta D-F.theta T|+frameCost |F.theta E-F.theta D| := by linarith
  have hA : difference F A=F.theta B-F.theta A := by
    simp only [difference,show next A=B by decide]
  have hB : difference F B=F.theta T-F.theta B := by
    simp only [difference,show next B=T by decide]
  have hT : difference F T=F.theta D-F.theta T := by
    simp only [difference,show next T=D by decide]
  have hD : difference F D=F.theta E-F.theta D := by
    simp only [difference,show next D=E by decide]
  rw [hA,hB,hT,hD,abs_sub_comm (F.theta A) (F.theta E)]
  exact hsum

theorem ceiling_high_low_false (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hquarter : F.quarter=offsets)
    (jE jG : Fin 4) (hEowner : jE=2 ∨ jE=3) (hGowner : jG=0 ∨ jG=1)
    (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H))
    (hGA : (forwardAxis jG).Feasible (C.square G) (C.square A)) : False := by
  let hgap : ∀i,19/25<angleGap C.beta i := boundary_gap_lower C le_rfl
  have hinc (i : Vertex) : integerQuarterIncrement F.quarter i=word i := by
    rw [hquarter,GlobalZeroSign.offset_increment]
  have hiE : integerQuarterIncrement F.quarter E=1 := by simpa [word,E] using hinc E
  have hiH : integerQuarterIncrement F.quarter H=0 := by simpa [word,H] using hinc H
  have hiG : integerQuarterIncrement F.quarter G=1 := by simpa [word,G] using hinc G
  have hEsign := GlobalQuarterSign.ceiling_source_negative C F E hiE jE hEowner
    (by simpa [E,H,next] using hEH)
  have hHsign := GlobalZeroLow.ceiling_zero_low_source_positive C F H hiH
    (by simpa [H,G,next] using hiG) jG hGowner (by simpa [H,G,A,next] using hGA)
  have hGsign : C.tangent G<0 := by
    simpa [E,H,G,next] using GlobalZeroLow.ceiling_high_zero_target_negative C F E hiE
      (by simpa [E,H,next] using hiH) jE hEowner (by simpa [E,H,next] using hEH)
  have hAsign : 0<C.tangent A := by
    simpa [G,A,next] using GlobalQuarterSign.ceiling_target_positive C F G hiG jG hGowner
      (by simpa [G,A,next] using hGA)
  have he : transverse (stateOf C E)≤0 := by
    have hh := (div_lt_iff₀ (C.a_pos E)).1 hEsign
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  have hh : 0≤transverse (stateOf C H) := by
    have hh := (lt_div_iff₀ (C.a_pos H)).1 hHsign
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  have hg : transverse (stateOf C G)≤0 := by
    have hh := (div_lt_iff₀ (C.a_pos G)).1 hGsign
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  have ha : 0≤transverse (stateOf C A) := by
    have hh := (lt_div_iff₀ (C.a_pos A)).1 hAsign
    simpa only [transverse,stateOf,signOf_spec,mul_zero,zero_mul] using hh.le
  obtain ⟨jZ,hjZ⟩ := boundary_forward_complete C le_rfl H (C.selected H) (C.feasible H)
  have hHG : (forwardAxis jZ).Feasible (C.square H) (C.square (next H)) := by
    simpa only [hjZ] using C.feasible H
  have hZowner := GlobalZeroSign.secondary C (by norm_num [Q0]) F H hiH jZ hHG
  have hphaseE : pairAngle C E=Real.pi/2+difference F E := by
    simpa [hiE,add_comm] using pair_angle_increment C F hgap E
  have hphaseH : pairAngle C H=difference F H := by
    simpa [hiH] using pair_angle_increment C F hgap H
  have hphaseG : pairAngle C G=Real.pi/2+difference F G := by
    simpa [hiG,add_comm] using pair_angle_increment C F hgap G
  have hpairE : (stateOf C E).Feasible (stateOf C H) jE (Real.pi/2+difference F E) := by
    have hp := stateOf_feasible C E jE (by simpa [E,H,next] using hEH)
    rw [hphaseE] at hp
    simpa [E,H,next] using hp
  have hpairH : (stateOf C H).Feasible (stateOf C G) jZ (difference F H) := by
    have hp := stateOf_feasible C H jZ hHG
    rw [hphaseH] at hp
    simpa [H,G,next] using hp
  have hpairG : (stateOf C G).Feasible (stateOf C A) jG (Real.pi/2+difference F G) := by
    have hp := stateOf_feasible C G jG (by simpa [G,A,next] using hGA)
    rw [hphaseG] at hp
    simpa [G,A,next] using hp
  have hnE : next E=H := by decide
  have hnH : next H=G := by decide
  have hnG : next G=A := by decide
  have hEHsum : difference F E+difference F H=F.theta G-F.theta E := by
    simp only [difference,hnE,hnH]
    ring
  have hHGsum : difference F H+difference F G=F.theta A-F.theta H := by
    simp only [difference,hnH,hnG]
    ring
  have hsum : difference F E+difference F H+difference F G=F.theta A-F.theta E := by
    simp only [difference,hnE,hnH,hnG]
    ring
  have hpath := original_path_charge (stateOf C E) (stateOf C H) (stateOf C G) (stateOf C A)
    (by simpa only [frameCap] using (difference_small F E).le)
    (by simpa only [frameCap] using (difference_small F H).le)
    (by simpa only [frameCap] using (difference_small F G).le)
    (by rw [hEHsum]; simpa only [frameCap] using (theta_spread F E G).le)
    (by rw [hHGsum]; simpa only [frameCap] using (theta_spread F H A).le)
    (by rw [hsum]; simpa only [frameCap] using (theta_spread F E A).le)
    he hh hg ha jE jZ jG hEowner hZowner hGowner hpairE hpairH hpairG
  let cost : Vertex→ℝ := fun i => phaseValue F hgap i+
    (stateOf C i).signedLabel-(stateOf C (next i)).signedLabel
  have hpair (i : Vertex) : (8833/10000:ℝ)+(9/50)*frameCost |difference F i|<cost i := by
    have hp := (ZeroPrimary.handGamma_lower (branchOf C i).type
      (branchOf C (next i)).type).trans_lt (FrameAllPairs.all_pair C i)
    rw [ZeroPrimary.frame_pair_cost C F hgap i] at hp
    dsimp [cost]
    linarith
  have hphaseE' : phaseValue F hgap E=Real.pi/2+difference F E := by
    linarith [phase_gap C F hgap E,pairAngle_gap C E]
  have hphaseH' : phaseValue F hgap H=difference F H := by
    linarith [phase_gap C F hgap H,pairAngle_gap C H]
  have hphaseG' : phaseValue F hgap G=Real.pi/2+difference F G := by
    linarith [phase_gap C F hgap G,pairAngle_gap C G]
  have hcharge : cost E+cost H+cost G=
      pathCharge (stateOf C E) (stateOf C A) (difference F E) (difference F H) (difference F G) := by
    dsimp only [cost,pathCharge]
    rw [hphaseE',hphaseH',hphaseG',hnE,hnH,hnG]
    have heLabel := signed_of_nonpos (stateOf C E) he
    have haLabel := signed_of_nonneg (stateOf C A) ha
    rw [heLabel,haLabel]
    ring
  have hbudget : (∑i,cost i)=2*Real.pi := marker_budget C F hgap
    (fun i => (stateOf C i).signedLabel)
  have hsplit : (∑i,cost i)=cost H+cost G+cost A+cost B+cost T+cost D+cost E := by
    rw [Fin.sum_univ_seven]
    rfl
  rw [hsplit] at hbudget
  have hreturn := four_edge_return C F
  rw [← hsum] at hreturn
  have hA := hpair A
  have hB := hpair B
  have hT := hpair T
  have hD := hpair D
  linarith [Arithmetic.two_pi_lt_710_over_113]

theorem original_high_low_false {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C) (hquarter : F.quarter=offsets)
    (jE jG : Fin 4) (hEowner : jE=2 ∨ jE=3) (hGowner : jG=0 ∨ jG=1)
    (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H))
    (hGA : (forwardAxis jG).Feasible (C.square G) (C.square A)) : False := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G' : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  apply ceiling_high_low_false D G' hquarter jE jG hEowner hGowner
  · have hh := hR.preserves_all_axes E (forwardAxis jE) (by simpa [E,H,next] using hEH)
    simpa [E,H,next] using hh
  · have hh := hR.preserves_all_axes G (forwardAxis jG) (by simpa [G,A,next] using hGA)
    simpa [G,A,next] using hh

/-- The low GA premise is one actual witness.  The conclusion covers
every original EH axis separately, including all weak ties. -/
theorem frame_EH_low_of_GA_low {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (jG : Fin 4) (hGowner : jG=0 ∨ jG=1)
    (hGA : (forwardAxis jG).Feasible (C.square G) (C.square A))
    (jE : Fin 4) (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H)) :
    jE=0 ∨ jE=1 := by
  by_contra hbad
  have hEowner : jE=2 ∨ jE=3 := by fin_cases jE <;> simp_all
  obtain ⟨G',hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  exact original_high_low_false C hq G' hGquarter jE jG hEowner hGowner hEH hGA

end SquaresInCircles.Eight.GlobalEH
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalEH

open Candidate

theorem frame_GA_high_of_EH_high {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (jE : Fin 4) (hE : jE=2 ∨ jE=3)
    (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H))
    (jG : Fin 4) (hGA : (forwardAxis jG).Feasible (C.square G) (C.square A)) :
    jG=2 ∨ jG=3 := by
  by_contra hn
  have hG : jG=0 ∨ jG=1 := by fin_cases jG <;> simp_all
  have he := frame_EH_low_of_GA_low F hq jG hG hGA jE hEH
  rcases hE with rfl | rfl <;> rcases he with he | he <;> norm_num at he

theorem frame_high_EH_high_BT_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (jE jB : Fin 4) (hE : jE=2 ∨ jE=3) (hB : jB=2 ∨ jB=3)
    (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H))
    (hBT : (forwardAxis jB).Feasible (C.square B) (C.square T)) : False := by
  have hex (i : Vertex) :
      ∃ k : Fin 4,(forwardAxis k).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨k,hk⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨k,hk ▸ C.feasible i⟩
  choose original horiginal using hex
  let owner : Vertex→Fin 4 := fun i => if i=E then jE else if i=B then jB else original i
  have hf (i : Vertex) :
      (forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)) := by
    by_cases hiE : i=E
    · subst i
      simpa [owner,E,H,next] using hEH
    · by_cases hiB : i=B
      · subst i
        simpa [owner,B,T,E,next] using hBT
      · simpa only [owner,hiE,hiB,↓reduceIte] using horiginal i
  have hGowner : owner G=2 ∨ owner G=3 :=
    frame_GA_high_of_EH_high F hq jE hE hEH (owner G)
      (by simpa [G,A,next] using hf G)
  have hEnegative := GlobalQuarterOuter.frame_high_anchor F hq E
    (by norm_num [word,E]) jE hE (by simpa [E,H,next] using hEH)
  have hDE := GlobalQuarterSign.frame_DE F hq hEnegative.2.le
  have hDowner : owner D=2 ∨ owner D=3 :=
    hDE.2 (owner D) (by simpa [D,E,next] using hf D)
  have hBowner : owner B=2 ∨ owner B=3 := by simpa [owner,B,E] using hB
  have hEowner : owner E=2 ∨ owner E=3 := by simpa [owner] using hE
  apply GlobalAllHigh.frame_all_high_false F hq owner hf
  intro i hi
  have hcases : i=G ∨ i=B ∨ i=D ∨ i=E := by
    revert hi
    fin_cases i <;> decide
  rcases hcases with rfl | rfl | rfl | rfl
  · exact hGowner
  · exact hBowner
  · exact hDowner
  · exact hEowner

end SquaresInCircles.Eight.GlobalEH
end
end
end
