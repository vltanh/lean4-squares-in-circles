import SquaresInCircles.Six.Analytic.WestStressGeometry

/-!
# Appendix A: analytic exclusion of west-cardinal D

The historical eight-check implementation has been removed. Whole-domain
projection inequalities first leave only the forward W-secondary and
D-secondary normals. Both use the single multiplier triple (3/10,9/20,1/4).
The W case has an explicit radical majorant; the D case uses the displayed
radical curvature identity. Their domain reductions are analytic concavity
arguments with seven geometric vertices, not finite-cover certificates.

The two core-exclusion inputs below are established from the strong central
box before the theorem is called. No pin, sector or A2 conclusion is inserted
as a substitute for those hypotheses. The namespace is retained for compatibility.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization.WestCardinal

/-- Full geometric interface to the analytic Appendix A proof. -/
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
