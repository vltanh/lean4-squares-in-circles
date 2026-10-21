module

public import SquaresInCircles.Eight.TableFree.GlobalBTHighPrimaryTail

/-!
# Complete original tail bounds after a necessary high-primary prefix

Positive TD and DE errors are removed only through their proved
dual comparisons.  Every remaining negative allocation is paid by
the continuous ordinary or core-E scalar family, with its explicit
multiplier at least three fifths.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor

theorem ordinary_path (a t d e : State) (td : Bool) (jD : Fin 4) {z P w y : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hz : z∈Icc 0 frameCap) (hpref : prefix z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(prefix z-t.a/Real.cos z)≤P)
    (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-w) 0+max (-y) 0≤frameCap)
    (hjD : jD=2 ∨ jD=3) (hordinary : jD=2 ∨ 0≤y ∨ e.branch.type≠0)
    (hTD : width w≤projection false t d w (leftOwner td))
    (hDE : width y≤projection true d e y jD) :
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
    (hpref : prefix z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(prefix z-t.a/Real.cos z)≤P)
    (hw : |w|≤frameCap) (hu : u∈Icc 0 frameCap) (hcap : max (-w) 0+u≤frameCap)
    (hTD : width w≤projection false t d w (leftOwner td))
    (hDE : width (-u)≤projection true d e (-u) 3) :
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
    (hz : z∈Icc 0 frameCap) (hpref : prefix z≤a.b+t.a/Real.cos z)
    (hcharge : -z+kappa*(prefix z-t.a/Real.cos z)≤P)
    (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-w) 0+max (-y) 0≤frameCap) (hjD : jD=2 ∨ jD=3)
    (hTD : width w≤projection false t d w (leftOwner td))
    (hDE : width y≤projection true d e y jD) :
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

end SquaresInCircles.Eight.TableFree.GlobalBT.HighPrimary
