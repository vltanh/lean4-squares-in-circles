import SquaresInCircles.Six.Stress.BalancedClosure

/-!
# The unrestricted six-square radius lower bound

A hypothetical smaller packing lies below the exact candidate ceiling, so the
proved normalization theorem applies. The common concrete stress then forces
its radius to equal the candidate radius, a contradiction. Neither a pin,
sector, separator choice nor a certificate-success hypothesis is added to
Packing or to this theorem.

Compilation and the final kernel/axiom audit remain deferred by the user.
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
  have he := Stress.normalized_radius_eq P hQ
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
