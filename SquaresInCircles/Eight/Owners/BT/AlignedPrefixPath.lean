module

public import SquaresInCircles.Eight.Owners.BT.CoreDE3Monotone
public import SquaresInCircles.Eight.Owners.BT.CoreDE3Support
public import SquaresInCircles.Eight.Owners.BT.DE2Path

/-!
# Eight squares: the TD–DE tail after an aligned prefix

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
  simp [reducedDE2Tail,quarterDual,projection,GlobalOuterAnchor.width] <;> ring

theorem reducedCoreTail_zero (b t d e : State) (td : Bool) (c eWeight s u : ℝ) :
    CoreDE3.reduced b t d e td c eWeight 0 s u=
      Real.pi+kappa*(2-t.a)+zeroDual td t d (-s) c+
        quarterDual d e 3 (-u) eWeight+ZeroPrimary.unsigned e := by
  simp [CoreDE3.reduced,quarterDual,projection,GlobalOuterAnchor.width] <;> ring

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
