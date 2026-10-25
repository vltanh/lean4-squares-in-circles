module

public import SquaresInCircles.Eight.Owners.EH.PairedErrors

/-!
# Eight squares: the complete original high-EH/low-GA three-edge charge

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
