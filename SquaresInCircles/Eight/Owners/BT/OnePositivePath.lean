module

public import SquaresInCircles.Eight.Owners.BT.CoreDE3Monotone
public import SquaresInCircles.Eight.Owners.BT.CoreDE3Support
public import SquaresInCircles.Eight.Owners.BT.LowSource
public import SquaresInCircles.Eight.Owners.BT.OnePositiveComparison

/-!
# Eight squares: the two tails after a positive BT1 error

An outer T pays the pointwise BT comparison, which deletes a nonnegative BT1 error. The two tail
scalars then apply with BT error zero, the ordinary one (`ordinary_path`) and the core-E
negative-DE3 one (`core_path`), for every owner of AB and TD; so a boundary cycle at `Q0` with
`C.tangent E ≤ 0` has no weak BT1 witness at nonnegative error (`ceiling_false`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OnePositive

open Candidate FramePair FrameCircleArc GlobalOuterAnchor

theorem ordinary_path (a b t d e : State) (ab td : Bool) (jD : Fin 4)
    {v x w y : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0) (hT : t.branch.type≠0)
    (hv : |v|≤frameCap) (hx : x∈Icc 0 frameCap) (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-w) 0+max (-y) 0≤frameCap)
    (hjD : jD=2 ∨ jD=3) (hordinary : jD=2 ∨ 0≤y ∨ e.branch.type≠0)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v (leftOwner ab))
    (hBT : GlobalOuterAnchor.width x≤projection true b t x 1)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width y≤projection true d e y jD) :
    pathThreshold<Real.pi+v+x+w+y+kappa*a.b+ZeroPrimary.unsigned e := by
  let i := tailChart e.branch.type
  let z := max (-w) 0+max (-y) 0
  let c := strengthenedWeight i z
  have hz : z∈Icc 0 frameCap := ⟨by dsimp [z]; positivity,hcap⟩
  have hcBounds := strengthened_bounds i hz
  have hc : 0≤c := by dsimp [c]; linarith [hcBounds.1]
  have hcu : c≤kappa := hcBounds.2.1
  have heBounds := tailChart_weight_bounds i
  have hABdual := (AB_delete a b ab hv).trans
    (zeroDual_le_error a b ab (ABweight_positive hv).le hAB)
  have hBTdual := actual_aligned_charge b t hT hx hBT
  have hTDdual := (retain_zero t d td hw hc hcu).trans
    (zeroDual_le_error t d td hc hTD)
  have hDEdual := (retain_DE d e jD hd he hjD hy heBounds.1.le heBounds.2 hordinary).trans
    (quarterDual_le_error d e jD heBounds.1.le hDE)
  have hstrict := reduced_de2_strict b t d e td ht hd he
    (r := 0) (by norm_num) (le_max_right (-w) 0) (le_max_right (-y) 0)
    (by simpa only [zero_add] using hcap)
  rw [transverse_of_nonneg a ha] at hABdual
  dsimp [reducedDE2Tail] at hstrict
  simp only [zero_add,neg_zero] at hstrict
  dsimp [retainedNegative,c,z,i] at hTDdual hDEdual
  linarith

theorem core_path (a b t d e : State) (ab td : Bool) {v x w u : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0)
    (hT : t.branch.type≠0) (hcore : e.branch.type=0)
    (hv : |v|≤frameCap) (hx : x∈Icc 0 frameCap) (hw : |w|≤frameCap)
    (hu : u∈Icc 0 frameCap) (hcap : max (-w) 0+u≤frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v (leftOwner ab))
    (hBT : GlobalOuterAnchor.width x≤projection true b t x 1)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width (-u)≤projection true d e (-u) 3) :
    pathThreshold<Real.pi+v+x+w-u+kappa*a.b+ZeroPrimary.unsigned e := by
  have hs : max (-w) 0∈Icc 0 frameCap := negative_part_range hw
  have hc := CoreDE3.weight_pos hs
  have hcu := (CoreDE3.weight_bounds hs).2.2
  have heWeight : 0≤CoreDE3.endpointWeight u :=
    (show 0≤kappa by norm_num [kappa]).trans (CoreDE3.endpointWeight_bounds hu).1
  have hABdual := (AB_delete a b ab hv).trans
    (zeroDual_le_error a b ab (ABweight_positive hv).le hAB)
  have hBTdual := actual_aligned_charge b t hT hx hBT
  have hTDdual := (retain_zero t d td hw hc.le hcu).trans
    (zeroDual_le_error t d td hc.le hTD)
  have hDEdual := quarterDual_le_error d e 3 heWeight hDE
  have hscalar := CoreDE3.tail_strict td (r := 0) (by norm_num) hs.1 hu.1
    (by simpa only [zero_add] using hcap)
  have hsupport := CoreDE3.support b t d e td (c := CoreDE3.weight (max (-w) 0)) (r := 0)
    ht hd he hcore (by norm_num [frameCap]) hs hu
  simp only [zero_add] at hscalar
  have hstrict := hscalar.trans_le hsupport
  rw [transverse_of_nonneg a ha] at hABdual
  dsimp [CoreDE3.reduced] at hstrict
  simp only [neg_zero] at hstrict
  dsimp [retainedNegative] at hTDdual
  linarith

theorem ceiling_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hpositive : 0≤delta F.theta B) : False := by
  obtain ⟨L⟩ := lowSource F hE 1 (Or.inr rfl) hBT
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hx : delta F.theta B∈Icc 0 frameCap :=
    ⟨hpositive,(le_abs_self (delta F.theta B)).trans (hdelta B)⟩
  have hcap : max (-delta F.theta T) 0+max (-delta F.theta D) 0≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    rw [max_eq_right (show -delta F.theta B≤0 by linarith),zero_add] at hh
    exact hh
  have hpath : pathThreshold<tailCharge C F.theta := by
    by_cases ho : L.DE=2 ∨ 0≤delta F.theta D ∨ (stateOf C E).branch.type≠0
    · exact ordinary_path (stateOf C A) (stateOf C B) (stateOf C T) (stateOf C D)
        (stateOf C E) L.AB L.TD L.DE L.A_positive L.T_positive L.D_negative L.E_negative
        L.T_outer (hdelta A) hx (hdelta T) (hdelta D) hcap L.DE_owner ho
        L.AB_projection L.BT_projection L.TD_projection L.DE_projection
    · have hnotTwo : L.DE≠2 := fun h => ho (Or.inl h)
      have hnegative : delta F.theta D<0 := by
        exact lt_of_not_ge (fun h => ho (Or.inr (Or.inl h)))
      have hcore : (stateOf C E).branch.type=0 := by
        by_contra hn
        exact ho (Or.inr (Or.inr hn))
      have hDE3 := L.DE_owner.resolve_left hnotTwo
      have hu : -delta F.theta D∈Icc 0 frameCap :=
        ⟨by linarith,(neg_le_abs (delta F.theta D)).trans (hdelta D)⟩
      have hcap' : max (-delta F.theta T) 0+(-delta F.theta D)≤frameCap := by
        simpa only [max_eq_left (show 0≤-delta F.theta D by linarith)] using hcap
      have hh := core_path (stateOf C A) (stateOf C B) (stateOf C T) (stateOf C D)
        (stateOf C E) L.AB L.TD L.A_positive L.T_positive L.D_negative L.E_negative
        L.T_outer hcore (hdelta A) hx (hdelta T) hu hcap'
        L.AB_projection L.BT_projection L.TD_projection
        (by simpa only [neg_neg,hDE3] using L.DE_projection)
      simpa only [tailCharge,sub_neg_eq_add] using hh
  exact (not_lt_of_ge (frame_tail_cap F hE L.A_tangent.le).le) hpath

end SquaresInCircles.Eight.GlobalBT.OnePositive
