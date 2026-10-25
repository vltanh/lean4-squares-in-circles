module

public import SquaresInCircles.Eight.Owners.GA.Target.OuterReference
public import SquaresInCircles.Eight.Owners.GA.Target.PathData

/-!
# Eight squares: the complete original high-GA three-edge path with a large target

Both original zero owners, every error sign, both target
radial kinds, and all original chart markers remain in the statement.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target
open FramePair ZeroPrimary GlobalOuterAnchor

theorem outer_path (h g a b : State) (p r : Bool) {v u w : ℝ}
    (hh : h.branch.type≠0) (hg : g.branch.type≠0)
    (ha : a.branch.type≠0) (hb : b.branch.type≠0) (haB : (1/2:ℝ)≤a.b)
    (hv : |v|≤frameCap) (hu : u∈Icc 0 frameCap) (hw : |w|≤frameCap)
    (hspan : |v+u+w|≤frameCap)
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u)
    (hAB : GlobalOuterAnchor.width w≤GlobalEH.zeroProjection a b r w) :
    (11/4:ℝ)<pathCharge h b v u w+(9/50)*frameCost |v+u+w| := by
  have hforce := outer_force h g a b p r hh hg ha hb haB hu hHG hGA hAB
  have hzH : (9/100)*|v|≤zeroError (if p then h else g) v := by
    cases p
    · exact outer_lower g hg hv
    · exact outer_lower h hh hv
  have hzA : (9/100)*|w|≤zeroError (if r then a else b) w := by
    cases r
    · exact outer_lower b hb hw
    · exact outer_lower a ha hw
  have hallow := return_allowance hu hspan
  have hj := Outer.scalar_lower (outer_domain g a hg ha haB hu hGA)
  have hpi := Arithmetic.pi_hand_enclosure.1
  dsimp [Outer.J,frameCost] at *
  linarith

theorem core_path (h g a b : State) (p r : Bool) {v u w : ℝ}
    (hh : h.branch.type≠0) (hg : g.branch.type≠0)
    (ha : a.branch.type=0) (hb : b.branch.type≠0) (haB : (1/2:ℝ)≤a.b)
    (hv : |v|≤frameCap) (hu : u∈Icc 0 frameCap) (hw : |w|≤frameCap)
    (hspan : |v+u+w|≤frameCap)
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u)
    (hAB : GlobalOuterAnchor.width w≤GlobalEH.zeroProjection a b r w) :
    (11/4:ℝ)<pathCharge h b v u w+(9/50)*frameCost |v+u+w| := by
  have hul := Core.angle_lower g a ha haB hu hGA
  have herror := Core.error_lower a ha ⟨hul.le,hu.2⟩
  have hforce := core_force h g a b p r hh hb haB hu hHG hGA hAB
  have hzH : (9/100)*|v|≤zeroError (if p then h else g) v := by
    cases p
    · exact outer_lower g hg hv
    · exact outer_lower h hh hv
  have hzA : -(4/25)*|w|≤zeroError (if r then a else b) w := by
    cases r
    · exact (show -(4/25)*|w|≤(9/100)*|w| by linarith [abs_nonneg w]).trans
        (outer_lower b hb hw)
    · exact large_target_lower a haB hw
  have hallow := return_allowance hu hspan
  have hcost : 0≤frameCost u := frameCost_nonneg
    ⟨hu.1,by dsimp [frameCap] at hu; linarith [hu.2,Real.pi_gt_three]⟩
  have hbase := Core.base_lower
  have hpi := Arithmetic.pi_hand_enclosure.1
  dsimp [frameCap] at hw
  linarith

theorem original_path (h g a b : State) {v u w : ℝ}
    (hhOuter : h.branch.type≠0) (hgOuter : g.branch.type≠0) (hbOuter : b.branch.type≠0)
    (hh : 0≤transverse h) (hg : transverse g≤0)
    (ha : (1/2:ℝ)≤transverse a) (hb : transverse b≤0)
    (hv : |v|≤frameCap) (hu : |u|≤frameCap) (hw : |w|≤frameCap)
    (hspan : |v+u+w|≤frameCap)
    (jH jG jA : Fin 4) (hHowner : jH=0 ∨ jH=2)
    (hGowner : jG=2 ∨ jG=3) (hAowner : jA=0 ∨ jA=2)
    (hHG : h.Feasible g jH v)
    (hGA : g.Feasible a jG (Real.pi/2+u))
    (hAB : a.Feasible b jA w) :
    (11/4:ℝ)<pathCharge h b v u w+(9/50)*frameCost |v+u+w| := by
  obtain ⟨p,hp⟩ : ∃p : Bool,rightOwner p=jG := by
    rcases hGowner with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  have hd := original_GA_domain g a p hu hg ha (by simpa [hp] using hGA)
  have hup : u∈Icc 0 frameCap := ⟨hd.2.1.le,(le_abs_self u).trans hu⟩
  have hay : transverse a=a.b := transverse_of_nonneg a (by linarith)
  have hab : (1/2:ℝ)≤a.b := by simpa only [hay] using ha
  obtain ⟨z,hz⟩ : ∃z : Bool,GlobalEH.zeroOwner z=jH := by
    rcases hHowner with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  obtain ⟨r,hr⟩ : ∃r : Bool,GlobalEH.zeroOwner r=jA := by
    rcases hAowner with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  have hHG' := (GlobalEH.zeroProjection_margin h g z hv hh hg).1 (by simpa [hz] using hHG)
  have hAB' := (GlobalEH.zeroProjection_margin a b r hw (by linarith) hb).1 (by simpa [hr] using hAB)
  by_cases hcore : a.branch.type=0
  · exact core_path h g a b z r hhOuter hgOuter hcore hbOuter hab hv hup hw hspan
      hHG' hd.2.2 hAB'
  · exact outer_path h g a b z r hhOuter hgOuter hcore hbOuter hab hv hup hw hspan
      hHG' hd.2.2 hAB'

end SquaresInCircles.Eight.GlobalGA.Target
