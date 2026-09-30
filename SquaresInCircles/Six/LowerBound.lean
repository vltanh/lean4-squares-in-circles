module
public import SquaresInCircles.Six.Analytic.CompleteReduction
public import SquaresInCircles.Six.Goals

@[expose] public section

/-!
# The unrestricted six-square radius lower bound

A hypothetical smaller packing is normalized at the exact candidate ceiling.
CompleteReduction derives both candidate separators and both pair domains
analytically, and the fixed-pair/diagonal closure forces the candidate radius.
This endpoint no longer imports any Classification module, the old pair-envelope
checker, or BalancedClosure. Packing, the theorem statement and the exact
candidate are unchanged. Compilation and the kernel/axiom audit are separate
validation steps and have not been executed in this continuation.
-/

noncomputable section
namespace SquaresInCircles.Six

/-- Every packing of six unit squares in a disk has radius at least the candidate. -/
theorem lower_bound {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) : Six.radius≤R := by
  by_contra! hR
  have hs : R^2<Six.radius^2 := by
    have hm := mul_pos (sub_pos.mpr hR) (show 0<Six.radius+R by linarith [radius_pos,hp.1])
    nlinarith
  have hQ : R^2≤Six.qStar := by simpa only [radius_sq] using hs.le
  obtain ⟨P,_⟩ := Normalization.normalize_of_candidate hp hQ
  have he := Analytic.FixedPair.radius_of_normalized_packing P hQ
  linarith

/-- An inhabitant of the unchanged unrestricted lower-bound goal. -/
theorem lowerBound : Goals.LowerBound := by
  intro S o R hp
  exact lower_bound hp

lemma squared_lower_bound {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) : Six.qStar≤R^2 := by
  have hr := lower_bound hp
  have hm := mul_nonneg (sub_nonneg.mpr hr) (show 0≤R+Six.radius by linarith [hp.1,radius_pos])
  nlinarith [radius_sq]

end SquaresInCircles.Six
