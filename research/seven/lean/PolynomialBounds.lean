import research.seven.lean.Basic

/-!
B and F. These polynomial definitions are copied explicitly so that their sign
proofs do not import either production positivity theorem. The integration
examples in ReplacementChecks identify them with the production definitions.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human

def ratioN (X : ℝ) : ℝ :=
  -500*X^5+800*X^4+1705*X^3-3900*X^2+3120*X-1872

def ratioND (X : ℝ) : ℝ :=
  -2500*X^4+3200*X^3+5115*X^2-7800*X+3120

def ratioNDD (X : ℝ) : ℝ := -10000*X^3+9600*X^2+10230*X-7800

lemma ratioN_hasDeriv (x : ℝ) : HasDerivAt ratioN (ratioND x) x := by
  have hd : DifferentiableAt ℝ ratioN x := by unfold ratioN; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [ratioN,ratioND] <;> ring

lemma ratioND_hasDeriv (x : ℝ) : HasDerivAt ratioND (ratioNDD x) x := by
  have hd : DifferentiableAt ℝ ratioND x := by unfold ratioND; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [ratioND,ratioNDD] <;> ring

lemma ratioNDD_shift (t : ℝ) :
    ratioNDD (8/5+t) = -7816-35850*t-38400*t^2-10000*t^3 := by
  unfold ratioNDD
  ring

lemma ratioNDD_nonpos {X : ℝ} (hX : (8 : ℝ)/5 ≤ X) : ratioNDD X ≤ 0 := by
  have ht : 0 ≤ X-8/5 := by linarith
  have he := ratioNDD_shift (X-8/5)
  rw [show (8/5 : ℝ)+(X-8/5)=X by ring] at he
  rw [he]
  nlinarith [sq_nonneg (X-8/5),pow_nonneg ht 3]

lemma ratio_numerator_pos {X : ℝ} (hX : (8 : ℝ)/5 ≤ X ∧ X ≤ 7/4) :
    0 < ratioN X := by
  apply Seven.positive_of_second_nonpos
    (f := ratioN) (d := ratioND) (dd := ratioNDD) hX
  · unfold ratioN; fun_prop
  · unfold ratioND; fun_prop
  · intro y _; exact ratioN_hasDeriv y
  · intro y _; exact ratioND_hasDeriv y
  · intro y hy; exact ratioNDD_nonpos hy.1
  · norm_num [ratioN]
  · norm_num [ratioN]

def radialP (z : ℝ) : ℝ :=
  201/2000-(201353/7098000)*z-(3091/21840)*z^2
    -(1571239/14196000)*z^3-(23103/7280000)*z^4
    +(977419/182520000)*z^5-(13/6300)*z^6
    -(364297/196560000)*z^7+z^8/90720+z^9/8640-z^11/518400

def radialPD (z : ℝ) : ℝ :=
  -201353/7098000-(3091/10920)*z-(1571239/4732000)*z^2
    -(23103/1820000)*z^3+(977419/36504000)*z^4
    -(13/1050)*z^5-(364297/28080000)*z^6
    +z^7/11340+z^8/960-(11/518400)*z^10

lemma radialP_hasDeriv (z : ℝ) : HasDerivAt radialP (radialPD z) z := by
  have hd : DifferentiableAt ℝ radialP z := by unfold radialP; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [radialP,radialPD] <;> ring

/-- Only three derivative terms are positive. Their entire sum is too small. -/
lemma radial_derivative_bound {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) :
    radialPD z ≤ -(253/547560 : ℝ) := by
  have h4 := (unit_pow_bounds hz 4).2
  have h7 := (unit_pow_bounds hz 7).2
  have h8 := (unit_pow_bounds hz 8).2
  have h2 := pow_nonneg hz.1 2
  have h3 := pow_nonneg hz.1 3
  have h5 := pow_nonneg hz.1 5
  have h6 := pow_nonneg hz.1 6
  have h10 := pow_nonneg hz.1 10
  dsimp [radialPD]
  linarith [hz.1]

lemma radialP_antitone : AntitoneOn radialP (Icc 0 1) := by
  apply Seven.antiOn_of_hasDeriv_nonpos (d := radialPD)
  · unfold radialP; fun_prop
  · intro z _; exact radialP_hasDeriv z
  · intro z hz
    have hh := radial_derivative_bound ⟨hz.1.le,hz.2.le⟩
    linarith

lemma radial_endpoint : (1 : ℝ)/4000 < radialP (5/8) := by
  norm_num [radialP]

theorem radial_polynomial_pos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 5/8) :
    0 < radialP z := by
  have hh := radialP_antitone
    (show z ∈ Icc 0 1 by constructor <;> linarith [hz.1,hz.2])
    (show (5/8 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hz.2
  linarith [radial_endpoint]

end SquaresInCircles.Seven.Human
