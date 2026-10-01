import SquaresInCircles.Six.Analytic.WestStressGeometry

/-!
# D is not separated along the west side of C

Let W and D be at the phases `π + t` and `π + u`, with `-2/3 ≤ t ≤ u` and
`|u| ≤ 2/5`, let the centre of C lie in `[0, c0]²`, and let W and D be contained
in the disk and avoid the core disk. If W is separated from C along its own axis
and D along the west side of C, then W and D overlap. This is
`west_cardinal_impossible`: disjoint W and D would be separated along the
secondary axis of W or of D, and a stress on this separator and the two
separators from C gives a contradiction.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization.WestCardinal

/-- W separated from C along its own axis and D along the west side of C are not
disjoint. -/
theorem impossible {c:Point} {t u a b A B:ℝ}
    (hc:(0≤c.1 ∧ c.1≤c0) ∧ (0≤c.2 ∧ c.2≤c0))
    (hW:ContainedChart a |b|) (hD:ContainedChart A |B|)
    (hWcore:AvoidsCore a |b|) (hDcore:AvoidsCore A |B|)
    (ht:-2/3≤t) (hu0:-2/5≤u) (hu1:u≤2/5) (htu:t≤u)
    (hCW:0≤centralMargin .own (Real.pi+t) a b c.1 c.2)
    (hCD:0≤centralMargin .west (Real.pi+u) A B c.1 c.2)
    (hWD:∀ p,¬(openSquare (orientedSquare (Real.pi+t) a b) p ∧
      openSquare (orientedSquare (Real.pi+u) A B) p)) : False :=
  Analytic.west_cardinal_impossible hc hW hD hWcore hDcore ht hu0 hu1 htu hCW hCD hWD

end SquaresInCircles.Six.Normalization.WestCardinal
