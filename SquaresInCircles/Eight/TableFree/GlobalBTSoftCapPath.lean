module

public import SquaresInCircles.Eight.TableFree.GlobalBTSoftCapTail

/-!
# Complete positive-AB2, negative-BT1 path bound

Every TD sign and owner, every DE sign and owner, and every E radial
chart is included.  Only the actual original AB2 and BT1 projections
are used to discharge the entire prefix transport.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.SoftCap

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

end SquaresInCircles.Eight.TableFree.GlobalBT.SoftCap
