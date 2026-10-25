module

public import SquaresInCircles.Eight.Owners.BT.ZeroExclusion
public import SquaresInCircles.Eight.Owners.BT.CoreDE3Support
public import SquaresInCircles.Eight.Owners.BT.HighPrimaryTail
public import SquaresInCircles.Eight.Owners.BT.ErrorComparisons
public import SquaresInCircles.Eight.Owners.BT.OneNegativeAB0Cap
public import SquaresInCircles.Eight.Owners.BT.OneNegativeAligned
public import SquaresInCircles.Eight.Owners.BT.SoftCapPrefix

/-!
# Eight squares: no low owner on BT

When the tangent of E is nonpositive, every weak witness of BT has owner `2` or `3`
(`frame_BT_high`). Owner `1` is excluded on a boundary cycle at `Q0` (`ceiling_BT1_false`), and
fixed-ray expansion transfers the exclusion to every radius `q ∈ [5/2, Q0]` (`frame_BT1_false`).
This covers every sign of the AB and BT errors, both zero owners at AB and TD, both high owners of
DE and every radial chart of E.
-/

section
/-!
## The TD–DE tail after an aligned prefix

Given the prefix charge `kappa * (2 - t.a) ≤ P`, the weak TD and DE projections make the path
charge `π + P + w + y + unsigned e` exceed `pathThreshold` (`aligned_path`). The two scalar
families of the tail, the ordinary one (`aligned_ordinary_path`) and the core one
(`aligned_core_path`), need only this prefix charge; the states, signs, errors and weak owners of
TD and DE are those of the path, with their strengthened multipliers.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open FramePair FrameCircleArc GlobalOuterAnchor

theorem reducedDE2Tail_zero (b t d e : State) (td : Bool) (c eWeight s u : ℝ) :
    reducedDE2Tail b t d e td c eWeight 0 s u=
      Real.pi+kappa*(2-t.a)+zeroDual td t d (-s) c+
        quarterDual d e 2 (-u) eWeight+ZeroPrimary.unsigned e := by
  simp [reducedDE2Tail,quarterDual,projection,GlobalOuterAnchor.width]
  ring

theorem reducedCoreTail_zero (b t d e : State) (td : Bool) (c eWeight s u : ℝ) :
    CoreDE3.reduced b t d e td c eWeight 0 s u=
      Real.pi+kappa*(2-t.a)+zeroDual td t d (-s) c+
        quarterDual d e 3 (-u) eWeight+ZeroPrimary.unsigned e := by
  simp [CoreDE3.reduced,quarterDual,projection,GlobalOuterAnchor.width]
  ring

theorem aligned_ordinary_path (b t d e : State) (td : Bool) (jD : Fin 4) {P w y : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hpref : kappa*(2-t.a)≤P) (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-w) 0+max (-y) 0≤frameCap)
    (hjD : jD=2 ∨ jD=3) (hordinary : jD=2 ∨ 0≤y ∨ e.branch.type≠0)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width y≤projection true d e y jD) :
    pathThreshold<Real.pi+P+w+y+ZeroPrimary.unsigned e := by
  let i := tailChart e.branch.type
  let z := max (-w) 0+max (-y) 0
  let c := strengthenedWeight i z
  have hz : z∈Icc 0 frameCap := ⟨by dsimp [z]; positivity,hcap⟩
  have hcBounds := strengthened_bounds i hz
  have hc : 0≤c := by dsimp [c]; linarith [hcBounds.1]
  have hcu : c≤kappa := hcBounds.2.1
  have heBounds := tailChart_weight_bounds i
  have hTDdual := (retain_zero t d td hw hc hcu).trans
    (zeroDual_le_error t d td hc hTD)
  have hDEdual := (retain_DE d e jD hd he hjD hy heBounds.1.le heBounds.2 hordinary).trans
    (quarterDual_le_error d e jD heBounds.1.le hDE)
  have hstrict := reduced_de2_strict b t d e td ht hd he
    (r := 0) (by norm_num) (le_max_right (-w) 0) (le_max_right (-y) 0)
    (by simpa only [zero_add] using hcap)
  rw [reducedDE2Tail_zero] at hstrict
  simp only [zero_add] at hstrict
  dsimp [retainedNegative,c,z,i] at hTDdual hDEdual
  linarith

theorem aligned_core_path (b t d e : State) (td : Bool) {P w u : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hcore : e.branch.type=0) (hpref : kappa*(2-t.a)≤P)
    (hw : |w|≤frameCap) (hu : u∈Icc 0 frameCap) (hcap : max (-w) 0+u≤frameCap)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width (-u)≤projection true d e (-u) 3) :
    pathThreshold<Real.pi+P+w-u+ZeroPrimary.unsigned e := by
  have hs := negative_part_range hw
  have hc := CoreDE3.weight_pos hs
  have hcu := (CoreDE3.weight_bounds hs).2.2
  have heWeight : 0≤CoreDE3.endpointWeight u :=
    (show 0≤kappa by norm_num [kappa]).trans (CoreDE3.endpointWeight_bounds hu).1
  have hTDdual := (retain_zero t d td hw hc.le hcu).trans
    (zeroDual_le_error t d td hc.le hTD)
  have hDEdual := quarterDual_le_error d e 3 heWeight hDE
  have hscalar := CoreDE3.tail_strict td (r := 0) (by norm_num) hs.1 hu.1
    (by simpa only [zero_add] using hcap)
  have hsupport := CoreDE3.support b t d e td (c := CoreDE3.weight (max (-w) 0))
    ht hd he hcore (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hs hu
  simp only [zero_add] at hscalar
  have hstrict := hscalar.trans_le hsupport
  rw [reducedCoreTail_zero] at hstrict
  dsimp [retainedNegative] at hTDdual
  linarith

/-- The path charge exceeds `pathThreshold` for every owner `jD ∈ {2, 3}` of DE: its owner, radial
kind and error choose between the ordinary and the core scalar families. -/
theorem aligned_path (b t d e : State) (td : Bool) (jD : Fin 4) {P w y : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hpref : kappa*(2-t.a)≤P) (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-w) 0+max (-y) 0≤frameCap) (hjD : jD=2 ∨ jD=3)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width y≤projection true d e y jD) :
    pathThreshold<Real.pi+P+w+y+ZeroPrimary.unsigned e := by
  by_cases ho : jD=2 ∨ 0≤y ∨ e.branch.type≠0
  · exact aligned_ordinary_path b t d e td jD ht hd he hpref hw hy hcap hjD ho hTD hDE
  · have hnotTwo : jD≠2 := fun h => ho (Or.inl h)
    have hyneg : y<0 := lt_of_not_ge (fun h => ho (Or.inr (Or.inl h)))
    have hcore : e.branch.type=0 := by
      by_contra hn
      exact ho (Or.inr (Or.inr hn))
    have hthree := hjD.resolve_left hnotTwo
    have hu : -y∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs y).trans hy⟩
    have hcap' : max (-w) 0+(-y)≤frameCap := by
      simpa only [max_eq_left (show 0≤-y by linarith)] using hcap
    have hh := aligned_core_path b t d e td ht hd he hcore hpref hw hu hcap' hTD
      (by simpa only [neg_neg,hthree] using hDE)
    simpa only [sub_neg_eq_add] using hh

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
/-!
## Original-cycle exclusion for the dominating AB0 error

The actual AB0 and BT1 witnesses give an aligned-prefix charge when
the nonnegative AB error dominates the magnitude of negative BT.
The complete unchanged TD--DE tail then contradicts the original
three-edge return.  Fixed-ray expansion preserves both witnesses
and the error order at every admissible source radius.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OneNegative

open Candidate FramePair GlobalOuterAnchor

theorem ceiling_AB0_dominating_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hAB : (forwardAxis 0).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hnegative : delta F.theta B≤0)
    (hdominates : -delta F.theta B≤delta F.theta A) : False := by
  obtain ⟨L⟩ := lowSource F hE 1 (Or.inr rfl) hBT
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hABp : GlobalOuterAnchor.width (delta F.theta A)≤
      projection false (stateOf C A) (stateOf C B) (delta F.theta A) 0 := by
    simpa [A,B,next] using frame_zero_projection F A (by norm_num [word,A]) 0
      (by simpa [A,B,next] using hAB)
  have hpref : kappa*(2-(stateOf C T).a)≤
      delta F.theta A+delta F.theta B+kappa*(stateOf C A).b := by
    have hh := AB0_dominating_charge (stateOf C A) (stateOf C B) (stateOf C T)
      L.A_positive (show 0≤-delta F.theta B by linarith) hdominates
      ((le_abs_self (delta F.theta A)).trans (hdelta A)) hABp
      (by simpa only [neg_neg] using L.BT_projection)
    simpa only [sub_neg_eq_add] using hh
  have hcap : max (-delta F.theta T) 0+max (-delta F.theta D) 0≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    have hb : 0≤ max (-delta F.theta B) 0 := le_max_right _ _
    linarith
  have hpath := aligned_path (stateOf C B) (stateOf C T) (stateOf C D)
    (stateOf C E) L.TD L.DE L.T_positive L.D_negative L.E_negative hpref
    (hdelta T) (hdelta D) hcap L.DE_owner L.TD_projection L.DE_projection
  have hreturn := frame_tail_cap F hE L.A_tangent.le
  dsimp [tailCharge] at hreturn
  linarith

end SquaresInCircles.Eight.GlobalBT.OneNegative
end
end
end

section
/-!
## Complete original tail bounds after a necessary high-primary prefix

Positive TD and DE errors are removed only through their proved
dual comparisons.  Every remaining negative allocation is paid by
the continuous ordinary or core-E scalar family, with its explicit
multiplier at least three fifths.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor

theorem ordinary_path (a t d e : State) (td : Bool) (jD : Fin 4) {z P w y : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hz : z∈Icc 0 frameCap) (hpref : «prefix» z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(«prefix» z-t.a/Real.cos z)≤P)
    (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-w) 0+max (-y) 0≤frameCap)
    (hjD : jD=2 ∨ jD=3) (hordinary : jD=2 ∨ 0≤y ∨ e.branch.type≠0)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width y≤projection true d e y jD) :
    pathThreshold<Real.pi+P+w+y+ZeroPrimary.unsigned e := by
  let i := tailChart e.branch.type
  let v := max (-w) 0+max (-y) 0
  let c := strengthenedWeight i v
  have hv : v∈Icc 0 frameCap := ⟨by dsimp [v]; positivity,hcap⟩
  have hc := strengthened_bounds i hv
  have hc0 : 0≤c := by dsimp [c]; linarith [hc.1]
  have hew := tailChart_weight_bounds i
  have hTDdual := (retain_zero t d td hw hc0 hc.2.1).trans
    (zeroDual_le_error t d td hc0 hTD)
  have hDEdual := (retain_DE d e jD hd he hjD hy hew.1.le hew.2 hordinary).trans
    (quarterDual_le_error d e jD hew.1.le hDE)
  have hscalar := strengthened_de2Tail i td (r := 0) (by norm_num)
    (le_max_right (-w) 0) (le_max_right (-y) 0)
    (by simpa only [zero_add] using hcap)
  have hsupport := ordinary_support a t d e td ht hd he hc.1 hz
    (negative_part_range hw) (negative_part_range hy) hpref hcharge (tailChart_marker e)
  simp only [zero_add] at hscalar
  have hstrict := hscalar.trans_le hsupport
  dsimp [retainedNegative,c,v,i] at hTDdual hDEdual
  linarith

theorem core_path (a t d e : State) (td : Bool) {z P w u : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hcore : e.branch.type=0) (hz : z∈Icc 0 frameCap)
    (hpref : «prefix» z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(«prefix» z-t.a/Real.cos z)≤P)
    (hw : |w|≤frameCap) (hu : u∈Icc 0 frameCap) (hcap : max (-w) 0+u≤frameCap)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width (-u)≤projection true d e (-u) 3) :
    pathThreshold<Real.pi+P+w-u+ZeroPrimary.unsigned e := by
  have hs := negative_part_range hw
  have hc := CoreDE3.weight_bounds hs
  have hcpos := CoreDE3.weight_pos hs
  have hew : 0≤CoreDE3.endpointWeight u :=
    (show 0≤kappa by norm_num [kappa]).trans (CoreDE3.endpointWeight_bounds hu).1
  have hTDdual := (retain_zero t d td hw hcpos.le hc.2.2).trans
    (zeroDual_le_error t d td hcpos.le hTD)
  have hDEdual := quarterDual_le_error d e 3 hew hDE
  have hscalar := CoreDE3.tail_strict td (r := 0) (by norm_num) hs.1 hu.1
    (by simpa only [zero_add] using hcap)
  have hsupport := core_support a t d e td ht hd he hcore hc.1 hz hs hu hpref hcharge
  simp only [zero_add] at hscalar
  have hstrict := hscalar.trans_le hsupport
  dsimp [retainedNegative] at hTDdual
  linarith

/-- Both original TD owners and every DE kind/sign/owner are covered. -/
theorem path (a t d e : State) (td : Bool) (jD : Fin 4) {z P w y : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hz : z∈Icc 0 frameCap) (hpref : «prefix» z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(«prefix» z-t.a/Real.cos z)≤P)
    (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-w) 0+max (-y) 0≤frameCap) (hjD : jD=2 ∨ jD=3)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width y≤projection true d e y jD) :
    pathThreshold<Real.pi+P+w+y+ZeroPrimary.unsigned e := by
  by_cases ho : jD=2 ∨ 0≤y ∨ e.branch.type≠0
  · exact ordinary_path a t d e td jD ht hd he hz hpref hcharge hw hy hcap hjD ho hTD hDE
  · have hnotTwo : jD≠2 := fun h => ho (Or.inl h)
    have hyneg : y<0 := lt_of_not_ge (fun h => ho (Or.inr (Or.inl h)))
    have hcore : e.branch.type=0 := by
      by_contra hn
      exact ho (Or.inr (Or.inr hn))
    have hthree := hjD.resolve_left hnotTwo
    have hu : -y∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs y).trans hy⟩
    have hcap' : max (-w) 0+(-y)≤frameCap := by
      simpa only [max_eq_left (show 0≤-y by linarith)] using hcap
    have hh := core_path a t d e td ht hd he hcore hz hpref hcharge hw hu hcap' hTD
      (by simpa only [neg_neg,hthree] using hDE)
    simpa only [sub_neg_eq_add] using hh

end SquaresInCircles.Eight.GlobalBT.HighPrimary
end
end
end

section
/-!
## Original BT1 exclusion when AB has nonpositive error

Both actual AB owners, both TD owners and every DE family are covered.
The cap and charge are derived from the original two prefix contacts;
the complete transported tail contradicts the original return charge.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OneNegative

open Candidate FramePair GlobalOuterAnchor

theorem ceiling_nonpositive_AB_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hABnegative : delta F.theta A≤0) (hBTnegative : delta F.theta B≤0) : False := by
  obtain ⟨L⟩ := lowSource F hE 1 (Or.inr rfl) hBT
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hw : -delta F.theta A∈Icc 0 frameCap :=
    ⟨by linarith,(neg_le_abs (delta F.theta A)).trans (hdelta A)⟩
  have hz : -delta F.theta B∈Icc 0 frameCap :=
    ⟨by linarith,(neg_le_abs (delta F.theta B)).trans (hdelta B)⟩
  have hp := nonpositive_prefix (stateOf C A) (stateOf C B) (stateOf C T) L.AB
    L.A_positive hw hz
    (by simpa only [neg_neg] using L.AB_projection)
    (by simpa only [neg_neg] using L.BT_projection)
  have hcharge : -(-delta F.theta B)+
      kappa*(HighPrimary.«prefix» (-delta F.theta B)-(stateOf C T).a/Real.cos (-delta F.theta B))≤
        delta F.theta A+delta F.theta B+kappa*(stateOf C A).b := by
    have hh := hp.2
    nlinarith only [hh,hw.1]
  have hcap : max (-delta F.theta T) 0+max (-delta F.theta D) 0≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    have hb : 0≤ max (-delta F.theta B) 0 := le_max_right _ _
    linarith
  have hpath := HighPrimary.path (stateOf C A) (stateOf C T) (stateOf C D)
    (stateOf C E) L.TD L.DE L.T_positive L.D_negative L.E_negative hz hp.1 hcharge
    (hdelta T) (hdelta D) hcap L.DE_owner L.TD_projection L.DE_projection
  have hreturn := frame_tail_cap F hE L.A_tangent.le
  dsimp [tailCharge] at hreturn
  linarith

end SquaresInCircles.Eight.GlobalBT.OneNegative
end
end
end

section
/-!
## Complete original BT1 exclusion with an actual AB0 witness

All signed AB and BT errors are dispatched.  The intermediate
positive AB range uses its exact effective cap; the dominating range
uses the aligned charge; nonpositive AB and nonnegative BT use their
complete original-cycle obstructions.  Weak ties are included.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OneNegative

open Candidate FramePair GlobalOuterAnchor

theorem ceiling_AB0_intermediate_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hAB : (forwardAxis 0).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hABpositive : 0≤delta F.theta A) (hBTnegative : delta F.theta B≤0)
    (horder : delta F.theta A≤ -delta F.theta B) : False := by
  obtain ⟨L⟩ := lowSource F hE 1 (Or.inr rfl) hBT
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hv : delta F.theta A∈Icc 0 frameCap :=
    ⟨hABpositive,(le_abs_self (delta F.theta A)).trans (hdelta A)⟩
  have hz : -delta F.theta B∈Icc 0 frameCap :=
    ⟨by linarith,(neg_le_abs (delta F.theta B)).trans (hdelta B)⟩
  have hABp : GlobalOuterAnchor.width (delta F.theta A)≤
      projection false (stateOf C A) (stateOf C B) (delta F.theta A) 0 := by
    simpa [A,B,next] using frame_zero_projection F A (by norm_num [word,A]) 0
      (by simpa [A,B,next] using hAB)
  have hp := AB0_effective_cap (stateOf C A) (stateOf C B) (stateOf C T)
    L.A_positive hv hz horder hABp (by simpa only [neg_neg] using L.BT_projection)
  have hr : -delta F.theta B-delta F.theta A∈Icc 0 frameCap :=
    ⟨by linarith,by linarith [hz.2]⟩
  have hcharge : -(-delta F.theta B-delta F.theta A)+
      kappa*(HighPrimary.«prefix» (-delta F.theta B-delta F.theta A)-
        (stateOf C T).a/Real.cos (-delta F.theta B-delta F.theta A))≤
        delta F.theta A+delta F.theta B+kappa*(stateOf C A).b := by
    simpa only [sub_neg_eq_add] using hp.2
  have hcap : max (-delta F.theta T) 0+max (-delta F.theta D) 0≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    have hb : 0≤ max (-delta F.theta B) 0 := le_max_right _ _
    linarith
  have hpath := HighPrimary.path (stateOf C A) (stateOf C T) (stateOf C D)
    (stateOf C E) L.TD L.DE L.T_positive L.D_negative L.E_negative hr hp.1 hcharge
    (hdelta T) (hdelta D) hcap L.DE_owner L.TD_projection L.DE_projection
  have hreturn := frame_tail_cap F hE L.A_tangent.le
  dsimp [tailCharge] at hreturn
  linarith

theorem ceiling_AB0_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hAB : (forwardAxis 0).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T)) : False := by
  by_cases hBTpositive : 0≤delta F.theta B
  · exact OnePositive.ceiling_false F hE hBT hBTpositive
  · have hBTnegative : delta F.theta B≤0 := le_of_not_ge hBTpositive
    by_cases hABnegative : delta F.theta A≤0
    · exact ceiling_nonpositive_AB_false F hE hBT hABnegative hBTnegative
    · by_cases hdom : -delta F.theta B≤delta F.theta A
      · exact ceiling_AB0_dominating_false F hE hAB hBT hBTnegative hdom
      · exact ceiling_AB0_intermediate_false F hE hAB hBT
          (le_of_not_ge hABnegative) hBTnegative (le_of_not_ge hdom)

end SquaresInCircles.Eight.GlobalBT.OneNegative
end
end
end

section
/-!
## The slope-two charge increases at every fixed original T point

Its derivative is independent of the TD force parameters.  A single
quadratic bound is positive over the entire original error interval,
including errors for which the high-primary cap is empty.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.SoftCap

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def low (c eta a b z : ℝ) : ℝ :=
  -z+2*HighPrimary.«prefix» z-(2-kappa)*c0-
    (2/Real.cos z-c*Real.sin eta)*a-c*Real.cos eta*b
def lowD (a z : ℝ) : ℝ :=
  (2*HighPrimary.K-1-(2*a-1)*Real.sin z+(Real.sin z)^2)/(Real.cos z)^2
def value (c eta z a b : ℝ) : ℝ :=
  -z+g (HighPrimary.«prefix» z-a/Real.cos z)+c*Real.sin eta*a-c*Real.cos eta*b

theorem prefix_deriv {z : ℝ} (hz : z∈Icc 0 frameCap) :
    HasDerivAt HighPrimary.«prefix»
      (((1/2)*Real.sin z+HighPrimary.K)/(Real.cos z)^2) z := by
  have hc : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  have hfirst := (hasDerivAt_const z (1/2)).div (Real.hasDerivAt_cos z) hc
  have hsecond := ((Real.hasDerivAt_sin z).const_mul HighPrimary.K).div
    (Real.hasDerivAt_cos z) hc
  convert (hfirst.add hsecond).const_add (3/2) using 1
  · funext x
    dsimp [HighPrimary.«prefix»]
    ring
  · field_simp [hc]
    dsimp [HighPrimary.K]
    nlinarith only [Real.sin_sq_add_cos_sq z]

theorem low_deriv (c eta a b : ℝ) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    HasDerivAt (low c eta a b) (lowD a z) z := by
  have hc : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  have hsec := (hasDerivAt_const z (2:ℝ)).div (Real.hasDerivAt_cos z) hc
  have hlin := (((hasDerivAt_id z).neg).add ((prefix_deriv hz).const_mul 2)).sub_const
    ((2-kappa)*c0)
  have hd := (hlin.sub ((hsec.sub_const (c*Real.sin eta)).mul_const a)).sub_const
    (c*Real.cos eta*b)
  convert hd using 1
  · rfl
  · dsimp [lowD]
    field_simp [hc]
    nlinarith only [Real.sin_sq_add_cos_sq z]

theorem lowD_positive {a z : ℝ} (ha : a≤283/200) (hz : z∈Icc 0 frameCap) :
    0<lowD a z := by
  have tr := transport_trig hz
  have hs : Real.sin z≤13/20 := by linarith [tr.2.2.2.1]
  have hp := mul_le_mul_of_nonneg_right
    (show 2*a-1≤183/100 by linarith) tr.2.2.1
  have hq := mul_nonneg (show 0≤13/20-Real.sin z by linarith)
    (show 0≤59/50-Real.sin z by linarith)
  have hnum : 0<2*HighPrimary.K-1-(2*a-1)*Real.sin z+(Real.sin z)^2 := by
    dsimp [HighPrimary.K]
    nlinarith only [hp,hq]
  exact div_pos hnum (sq_pos_of_pos (by linarith [tr.1]))

theorem low_monotone (c eta b : ℝ) {a : ℝ} (ha : a≤283/200) :
    MonotoneOn (low c eta a b) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z hz => (low_deriv c eta a b hz).continuousAt.continuousWithinAt
  · exact fun z hz => low_deriv c eta a b (Ioo_subset_Icc_self hz)
  · exact fun z hz => (lowD_positive ha (Ioo_subset_Icc_self hz)).le

theorem first_le_value (c eta z a b : ℝ) : HighPrimary.charge c eta z a b≤value c eta z a b := by
  have hh := g_first (HighPrimary.«prefix» z-a/Real.cos z)
  dsimp [HighPrimary.charge,HighPrimary.force,value]
  have hid : kappa/Real.cos z*a=kappa*(a/Real.cos z) := by ring
  linarith only [hh,hid]

theorem low_le_value (c eta z a b : ℝ) : low c eta a b z≤value c eta z a b := by
  have hh := g_second (HighPrimary.«prefix» z-a/Real.cos z)
  dsimp [low,value]
  have hid : 2/Real.cos z*a=2*(a/Real.cos z) := by ring
  linarith only [hh,hid]

theorem cap_equation {z a : ℝ} (hz : z∈Icc 0 frameCap) :
    (HighPrimary.«prefix» z-a/Real.cos z-c0)*Real.cos z=HighPrimary.X z-(a+1/2) := by
  have hc : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  dsimp [HighPrimary.«prefix»,HighPrimary.X,HighPrimary.L]
  field_simp [hc]
  ring

theorem low_eq_first_at_cap {c eta z a b : ℝ} (hz : z∈Icc 0 frameCap)
    (hcap : HighPrimary.X z=a+1/2) : low c eta a b z=HighPrimary.charge c eta z a b := by
  have hcos : 0<Real.cos z := by linarith [(transport_trig hz).1]
  have hh := cap_equation (a := a) hz
  rw [hcap,sub_self] at hh
  have harg : HighPrimary.«prefix» z-a/Real.cos z=c0 := by nlinarith only [hh,hcos]
  have hid : low c eta a b z-HighPrimary.charge c eta z a b=
      (2-kappa)*(HighPrimary.«prefix» z-a/Real.cos z-c0) := by
    dsimp [low,HighPrimary.charge,HighPrimary.force]
    ring
  rw [harg,sub_self,mul_zero] at hid
  linarith only [hid]

theorem low_zero_lower (t : State) (c eta : ℝ)
    (hsmall : t.a+1/2≤HighPrimary.X 0) : HighPrimary.aligned c eta≤low c eta t.a t.b 0 := by
  have hsupport := state_support t (kappa-c*Real.sin eta) (c*Real.cos eta)
  have ha : t.a≤2-c0 := by
    have hh := hsmall
    simp only [HighPrimary.X,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,
      add_zero,HighPrimary.L] at hh
    linarith
  have hp := mul_nonneg (show 0≤2-kappa by norm_num [kappa])
    (show 0≤2-c0-t.a by linarith)
  dsimp [HighPrimary.aligned,HighPrimary.full,low,HighPrimary.«prefix»]
  simp only [Real.cos_zero,Real.sin_zero,mul_zero,div_one,add_zero,neg_zero,zero_add]
  change (kappa-c*Real.sin eta)*t.a+(c*Real.cos eta)*t.b≤
    R*Real.sqrt ((kappa-c*Real.sin eta)^2+(c*Real.cos eta)^2)-
      (kappa-c*Real.sin eta+c*Real.cos eta)/2 at hsupport
  nlinarith only [hsupport,hp]

end SquaresInCircles.Eight.GlobalBT.SoftCap
end
end
end

section
/-!
## Complete pointwise soft-cap transport on the original T disk

T remains fixed throughout the comparison.  If its primary is below
the initial cap, the slope-two charge increases from zero.  Otherwise
the intermediate-value theorem supplies the exact cap crossing of
that same T point; high-primary transport applies there and the
slope-two charge increases afterward.  This covers the whole error
interval without an optimizer or active-set assumption.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.SoftCap

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem onCap_of_primary (t : State) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hprimary : HighPrimary.X z≤t.a+1/2) : HighPrimary.OnCap z := by
  have hc := state_circle t
  have hx : 0≤HighPrimary.X z := by linarith [HighPrimary.X_lower hz]
  have hs := pow_le_pow_left₀ hx hprimary 2
  have hb := t.b_nonneg
  exact ⟨hz,by nlinarith only [hc,hs,hb,sq_nonneg t.b]⟩

theorem transport (t : State) {c eta z : ℝ} (hc : (3/5:ℝ)≤c)
    (heta : eta∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) :
    HighPrimary.aligned c eta≤value c eta z t.a t.b := by
  have ha := (ZeroPrimary.coordinates t).2.1.le
  by_cases hhigh : HighPrimary.X z≤t.a+1/2
  · have hh := HighPrimary.circle_transport (state_circle t) ha hhigh hc heta
      (onCap_of_primary t hz hhigh)
    exact hh.trans (first_le_value c eta z t.a t.b)
  · have hlow : t.a+1/2≤HighPrimary.X z := le_of_not_ge hhigh
    have hmono := low_monotone c eta t.b ha
    by_cases hstart : t.a+1/2≤HighPrimary.X 0
    · have hbase := low_zero_lower t c eta hstart
      have hm := hmono (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz hz.1
      exact hbase.trans (hm.trans (low_le_value c eta z t.a t.b))
    · have hcont : Continuous HighPrimary.X := by unfold HighPrimary.X; fun_prop
      obtain ⟨s,hs,hcross⟩ := intermediate_value_Icc hz.1 hcont.continuousOn
        (show t.a+1/2∈Icc (HighPrimary.X 0) (HighPrimary.X z) from
          ⟨le_of_not_ge hstart,hlow⟩)
      have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hz.2⟩
      have hcap : HighPrimary.OnCap s := onCap_of_primary t hs' hcross.le
      have hbase := HighPrimary.circle_transport (state_circle t) ha hcross.le hc heta hcap
      rw [← low_eq_first_at_cap hs' hcross] at hbase
      exact hbase.trans ((hmono hs' hz hs.2).trans (low_le_value c eta z t.a t.b))

/-- The original two prefix witnesses now give the same explicit T
force bound as the aligned prefix, with the soft penalty discharged. -/
theorem transported_prefix (a b t : State) {v z c eta : ℝ}
    (ha : 0≤transverse a) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hc : (3/5:ℝ)≤c) (heta : eta∈Icc 0 frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 2)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    2*kappa-R*tailNorm kappa c eta+(kappa-c*Real.sin eta+c*Real.cos eta)/2≤
      v-z+kappa*a.b+c*Real.sin eta*t.a-c*Real.cos eta*t.b := by
  have hpref := AB2_prefix a b t ha hv hz hAB hBT
  have ht := transport t hc heta hz
  rw [HighPrimary.aligned_formula] at ht
  dsimp [value] at ht
  linarith only [hpref,ht]

end SquaresInCircles.Eight.GlobalBT.SoftCap
end
end
end

section
/-!
## Both complete original tails after the positive-AB2 soft prefix

The original AB2 and BT1 contacts directly pay the transported T
force.  The unchanged D circle and E marker give the two already
closed continuous tail scalar families for either original TD owner.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.SoftCap

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem ordinary_support (a b t d e : State) (second : Bool)
    {c eWeight margin v z s u : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0)
    (hc : (3/5:ℝ)≤c) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 2)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1)
    (hmarker : margin+eWeight*e.b≤ZeroPrimary.unsigned e) :
    de2Tail second eWeight margin c 0 s u≤
      Real.pi+v-z+kappa*a.b+zeroDual second t d (-s) c+
        quarterDual d e 2 (-u) eWeight+ZeroPrimary.unsigned e := by
  have hty := transverse_of_nonneg t ht
  have hdy : transverse d= -d.b := transverse_nonpos_eq d hd
  have hey : transverse e= -e.b := transverse_nonpos_eq e he
  cases second with
  | false =>
      have hT := transported_prefix a b t ha hv hz hc
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hAB hBT
      have hD := mixed_state_support d eWeight c u s
      rw [add_comm u s] at hD
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero] at hT
      dsimp [de2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,
        mul_one,zero_add]
      nlinarith only [hT,hD,hmarker]
  | true =>
      have hT := transported_prefix a b t ha hv hz hc hs hAB hBT
      have hD := mixed_state_support d eWeight c u 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hD
      dsimp [de2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,
        mul_one,zero_add]
      nlinarith only [hT,hD,hmarker]

theorem core_support (a b t d e : State) (second : Bool) {c v z s u : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0) (hcore : e.branch.type=0)
    (hc : (3/5:ℝ)≤c) (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 2)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    CoreDE3.tail second (CoreDE3.endpointWeight u) c 0 s u≤
      Real.pi+v-z+kappa*a.b+zeroDual second t d (-s) c+
        quarterDual d e 3 (-u) (CoreDE3.endpointWeight u)+ZeroPrimary.unsigned e := by
  have hty := transverse_of_nonneg t ht
  have hdy : transverse d= -d.b := transverse_nonpos_eq d hd
  have hey : transverse e= -e.b := transverse_nonpos_eq e he
  have hmarker := CoreDE3.core_endpoint_marker e hcore hu
  cases second with
  | false =>
      have hT := transported_prefix a b t ha hv hz hc
        (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hAB hBT
      have hD := mixed_state_support d (CoreDE3.endpointWeight u) c 0 s
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,zero_add] at hT hD
      dsimp [CoreDE3.tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,
        mul_one,zero_add]
      nlinarith only [hT,hD,hmarker]
  | true =>
      have hT := transported_prefix a b t ha hv hz hc hs hAB hBT
      have hD := mixed_state_support d (CoreDE3.endpointWeight u) c 0 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hD
      dsimp [CoreDE3.tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_zero,
        mul_one,zero_add]
      nlinarith only [hT,hD,hmarker]

end SquaresInCircles.Eight.GlobalBT.SoftCap
end
end
end

section
/-!
## Complete positive-AB2, negative-BT1 path bound

Every TD sign and owner, every DE sign and owner, and every E radial
chart is included.  Only the actual original AB2 and BT1 projections
are used to discharge the entire prefix transport.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.SoftCap

open FramePair FrameCircleArc GlobalOuterAnchor

theorem ordinary_path (a b t d e : State) (td : Bool) (jD : Fin 4) {v z w y : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0)
    (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-w) 0+max (-y) 0≤frameCap)
    (hjD : jD=2 ∨ jD=3) (hordinary : jD=2 ∨ 0≤y ∨ e.branch.type≠0)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 2)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width y≤projection true d e y jD) :
    pathThreshold<Real.pi+v-z+w+y+kappa*a.b+ZeroPrimary.unsigned e := by
  let i := tailChart e.branch.type
  let p := max (-w) 0+max (-y) 0
  let c := strengthenedWeight i p
  have hp : p∈Icc 0 frameCap := ⟨by dsimp [p]; positivity,hcap⟩
  have hc := strengthened_bounds i hp
  have hc0 : 0≤c := by dsimp [c]; linarith [hc.1]
  have hew := tailChart_weight_bounds i
  have hTDdual := (retain_zero t d td hw hc0 hc.2.1).trans
    (zeroDual_le_error t d td hc0 hTD)
  have hDEdual := (retain_DE d e jD hd he hjD hy hew.1.le hew.2 hordinary).trans
    (quarterDual_le_error d e jD hew.1.le hDE)
  have hscalar := strengthened_de2Tail i td (r := 0) (by norm_num)
    (le_max_right (-w) 0) (le_max_right (-y) 0)
    (by simpa only [zero_add] using hcap)
  have hsupport := ordinary_support a b t d e td ha ht hd he hc.1 hv hz
    (negative_part_range hw) (negative_part_range hy) hAB hBT (tailChart_marker e)
  simp only [zero_add] at hscalar
  have hstrict := hscalar.trans_le hsupport
  dsimp [retainedNegative,c,p,i] at hTDdual hDEdual
  linarith

theorem core_path (a b t d e : State) (td : Bool) {v z w u : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0) (hcore : e.branch.type=0)
    (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hw : |w|≤frameCap) (hu : u∈Icc 0 frameCap) (hcap : max (-w) 0+u≤frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 2)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width (-u)≤projection true d e (-u) 3) :
    pathThreshold<Real.pi+v-z+w-u+kappa*a.b+ZeroPrimary.unsigned e := by
  have hs := negative_part_range hw
  have hc := CoreDE3.weight_bounds hs
  have hcpos := CoreDE3.weight_pos hs
  have hew : 0≤CoreDE3.endpointWeight u :=
    (show 0≤kappa by norm_num [kappa]).trans (CoreDE3.endpointWeight_bounds hu).1
  have hTDdual := (retain_zero t d td hw hcpos.le hc.2.2).trans
    (zeroDual_le_error t d td hcpos.le hTD)
  have hDEdual := quarterDual_le_error d e 3 hew hDE
  have hscalar := CoreDE3.tail_strict td (r := 0) (by norm_num) hs.1 hu.1
    (by simpa only [zero_add] using hcap)
  have hsupport := core_support a b t d e td ha ht hd he hcore hc.1 hv hz hs hu hAB hBT
  simp only [zero_add] at hscalar
  have hstrict := hscalar.trans_le hsupport
  dsimp [retainedNegative] at hTDdual
  linarith

theorem path (a b t d e : State) (td : Bool) (jD : Fin 4) {v z w y : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0)
    (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-w) 0+max (-y) 0≤frameCap) (hjD : jD=2 ∨ jD=3)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 2)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width y≤projection true d e y jD) :
    pathThreshold<Real.pi+v-z+w+y+kappa*a.b+ZeroPrimary.unsigned e := by
  by_cases ho : jD=2 ∨ 0≤y ∨ e.branch.type≠0
  · exact ordinary_path a b t d e td jD ha ht hd he hv hz hw hy hcap hjD ho hAB hBT hTD hDE
  · have hnotTwo : jD≠2 := fun h => ho (Or.inl h)
    have hyneg : y<0 := lt_of_not_ge (fun h => ho (Or.inr (Or.inl h)))
    have hcore : e.branch.type=0 := by
      by_contra hn
      exact ho (Or.inr (Or.inr hn))
    have hthree := hjD.resolve_left hnotTwo
    have hu : -y∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs y).trans hy⟩
    have hcap' : max (-w) 0+(-y)≤frameCap := by
      simpa only [max_eq_left (show 0≤-y by linarith)] using hcap
    have hh := core_path a b t d e td ha ht hd he hcore hv hz hw hu hcap' hAB hBT hTD
      (by simpa only [neg_neg,hthree] using hDE)
    simpa only [sub_neg_eq_add] using hh

end SquaresInCircles.Eight.GlobalBT.SoftCap
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open Candidate FramePair GlobalOuterAnchor

namespace SoftCap

theorem ceiling_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hAB : (forwardAxis 2).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hABpositive : 0≤delta F.theta A) (hBTnegative : delta F.theta B≤0) : False := by
  obtain ⟨L⟩ := lowSource F hE 1 (Or.inr rfl) hBT
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hv : delta F.theta A∈Icc 0 frameCap :=
    ⟨hABpositive,(le_abs_self (delta F.theta A)).trans (hdelta A)⟩
  have hz : -delta F.theta B∈Icc 0 frameCap :=
    ⟨by linarith,(neg_le_abs (delta F.theta B)).trans (hdelta B)⟩
  have hABp : GlobalOuterAnchor.width (delta F.theta A)≤
      projection false (stateOf C A) (stateOf C B) (delta F.theta A) 2 := by
    simpa [A,B,next] using frame_zero_projection F A (by norm_num [word,A]) 2
      (by simpa [A,B,next] using hAB)
  have hcap : max (-delta F.theta T) 0+max (-delta F.theta D) 0≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    have hb : 0≤ max (-delta F.theta B) 0 := le_max_right _ _
    linarith
  have hpath := path (stateOf C A) (stateOf C B) (stateOf C T) (stateOf C D)
    (stateOf C E) L.TD L.DE L.A_positive L.T_positive L.D_negative L.E_negative hv hz
    (hdelta T) (hdelta D) hcap L.DE_owner hABp
    (by simpa only [neg_neg] using L.BT_projection) L.TD_projection L.DE_projection
  simp only [sub_neg_eq_add] at hpath
  have hreturn := frame_tail_cap F hE L.A_tangent.le
  dsimp [tailCharge] at hreturn
  linarith

end SoftCap

theorem ceiling_BT1_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T)) : False := by
  by_cases hBTpositive : 0≤delta F.theta B
  · exact OnePositive.ceiling_false F hE hBT hBTpositive
  · have hBTnegative : delta F.theta B≤0 := le_of_not_ge hBTpositive
    by_cases hABnegative : delta F.theta A≤0
    · exact OneNegative.ceiling_nonpositive_AB_false F hE hBT hABnegative hBTnegative
    · have hABpositive : 0≤delta F.theta A := le_of_not_ge hABnegative
      have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
      obtain ⟨jA,hjA⟩ := F.forward_complete A (C.selected A) (C.feasible A)
      have hf : (forwardAxis jA).Feasible (C.square A) (C.square (next A)) :=
        hjA ▸ C.feasible A
      have hAB : (forwardAxis jA).Feasible (C.square A) (C.square B) := hf
      rcases GlobalZeroSign.of_frame F hq A (by norm_num [word,A]) jA hf with ho | ho
      · rw [ho.1] at hAB
        exact OneNegative.ceiling_AB0_false F hE hAB hBT
      · rw [ho.1] at hAB
        exact SoftCap.ceiling_false F hE hAB hBT hABpositive hBTnegative

theorem frame_BT1_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T)) : False := by
  let K := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C K := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame K := FramePhysicalTransport.candidatePushforward F hR le_rfl
  have hBT' : (forwardAxis 1).Feasible (K.square B) (K.square T) := by
    simpa [B,T,next] using hR.preserves_all_axes B (forwardAxis 1)
      (by simpa [B,T,next] using hBT)
  exact ceiling_BT1_false F' (by simpa only [hR.same_tangents] using hE) hBT'

/-- When `C.tangent E ≤ 0`, every weak BT witness has owner `2` or `3`. -/
theorem frame_BT_high {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square B) (C.square T)) : j=2 ∨ j=3 := by
  fin_cases j
  · exact False.elim (frame_BT0_false F hq hE hj)
  · exact False.elim (frame_BT1_false F hq hE hj)
  · exact Or.inl rfl
  · exact Or.inr rfl

end SquaresInCircles.Eight.GlobalBT
end
end
end
