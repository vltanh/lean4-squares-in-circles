import SquaresInCircles.Six.Stress.DiagonalCapBound

/-!
# The remaining diagonal vertex branch

The d interval is parametrized exactly from [0,1], including d=pi/4. The
comparison premise is the actual support branch condition. The cap case has
already been proved analytically; this strict vertex certificate contains no
candidate zero and requires no deletion of a neighborhood or support wall.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SquaresInCircles.Six.Stress.DiagonalCertificate
open ProofTools PairCertificate

def dE : Expr 3 := er (1/2)+(.pi/4-er (1/2))*.var 2
def betaE : Expr 3 := (.var 0-.var 1)/2
def deltaE : Expr 3 := dE-.pi/4-(.var 0+.var 1)/2

def vertexE : Expr 3 :=
  let cb := Expr.cos betaE
  let sb := Expr.sin betaE
  let cd := Expr.cos deltaE
  let sd := Expr.abs (.sin deltaE)
  let K := (2*(PairCertificate.hE : Smooth 3)*PairCertificate.mE).expr
  K*((3*cb-sb)*cd/2+(cb-sb)*sd/2-(PairCertificate.radiusE : Smooth 3).expr*(cb-sb))

def root : RBox 3 := ![⟨-11/25,2/5⟩,⟨-2/5,11/25⟩,⟨0,1⟩]
def weights : Fin 3 → ℚ := ![1,1,3/10]

def claim : Formula 3 :=
  .imp (.le 1 (2*(PairCertificate.radiusE : Smooth 3).expr*.abs (.sin deltaE)))
    (.lt 0 (lineE (.var 0)+lineE (-.var 1)+vertexE+2*(PairCertificate.baseE : Smooth 3).expr))

theorem checked : certify claim weights 0 96 root=true := by
  decide

noncomputable section

@[simp] lemma denote_dE (w s t : ℝ) : Expr.denote dE ![w,s,t]=1/2+(Real.pi/4-1/2)*t := by
  simp [dE,Expr.denote]

@[simp] lemma denote_betaE (w s t : ℝ) : Expr.denote betaE ![w,s,t]=diagonalBeta w s := by
  simp [betaE,Expr.denote,diagonalBeta]

@[simp] lemma denote_deltaE (w s t : ℝ) :
    Expr.denote deltaE ![w,s,t]=diagonalDelta w s (1/2+(Real.pi/4-1/2)*t) := by
  simp [deltaE,Expr.denote,diagonalDelta]

@[simp] lemma denote_vertexE (w s t : ℝ) :
    Expr.denote vertexE ![w,s,t]=diagonalVertex w s (1/2+(Real.pi/4-1/2)*t) := by
  simp [vertexE,diagonalVertex,diagonalK,Expr.denote]

/-- Strict positivity throughout the vertex branch, including its switch wall. -/
theorem vertex_remainder_positive {w s d : ℝ} (hd : DiagonalDomain w s d)
    (hv : 1≤2*Six.radius*|Real.sin (diagonalDelta w s d)|) :
    0<pairLine w+pairLine (-s)+diagonalVertex w s d+2*pairBase := by
  obtain ⟨t,ht,hdt⟩ := segment_parameter hd.2.2
  have hb : root.Mem ![w,s,t] := by
    intro i
    fin_cases i
    · exact hd.1
    · exact hd.2.1
    · exact ht
  have hc := certify_sound claim weights 0 96 checked hb
  have hp : Formula.Holds
      (.le 1 (2*(PairCertificate.radiusE : Smooth 3).expr*.abs (.sin deltaE))) ![w,s,t] := by
    simpa [Formula.Holds,Expr.denote,← hdt] using hv
  have hh := hc hp
  simpa [Formula.Holds,Expr.denote,← hdt] using hh

end
end SquaresInCircles.Six.Stress.DiagonalCertificate

noncomputable section
namespace SquaresInCircles.Six.Stress

def diagonalRemainder (w s d : ℝ) : ℝ :=
  pairLine w+pairLine (-s)+diagonalValue w s d+2*pairBase

/-- Global diagonal inequality paired with the two common linear envelopes. -/
theorem diagonal_remainder_nonnegative {w s d : ℝ} (hd : DiagonalDomain w s d) :
    0≤diagonalRemainder w s d := by
  rw [diagonalRemainder,diagonal_value_formula hd]
  by_cases hc : 2*Six.radius*|Real.sin (diagonalDelta w s d)|≤1
  · rw [if_pos hc]
    have hh := diagonal_cap_remainder_lower hd
    nlinarith [abs_nonneg w,abs_nonneg s]
  · rw [if_neg hc]
    exact (DiagonalCertificate.vertex_remainder_positive hd (le_of_not_ge hc)).le

/-- Equality in the common diagonal bound has precisely the candidate angles. -/
theorem diagonal_remainder_zero {w s d : ℝ} (hd : DiagonalDomain w s d)
    (heq : diagonalRemainder w s d=0) : w=0 ∧ s=0 ∧ d=Real.pi/4 := by
  rw [diagonalRemainder,diagonal_value_formula hd] at heq
  by_cases hc : 2*Six.radius*|Real.sin (diagonalDelta w s d)|≤1
  · rw [if_pos hc] at heq
    exact diagonal_cap_zero_iff hd heq
  · rw [if_neg hc] at heq
    have hh := DiagonalCertificate.vertex_remainder_positive hd (le_of_not_ge hc)
    linarith

end SquaresInCircles.Six.Stress
