module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2CurvatureConstants
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# The literal alternating inverse-power bounds for secant curvature

Uncompiled transcription of the binomial bounds used in Sections 7,
11 and 12 of the negative-A angle companion. Their signs follow from
the derivatives on a whole nonnegative interval. No sampled enclosure
or executable sign certificate is used in the argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.InversePower
open Polynomial

def root (y : ℝ) : ℝ := Real.sqrt (1+y)
def odd (j : ℕ) (y : ℝ) : ℝ := 1/(root y)^(2*j+3)
def coefficient : Fin 6→ℝ := ![1,-3/2,15/4,-105/8,945/16,-10395/32]
def native (j : ℕ) (y : ℝ) : ℝ :=
  if hj : j<6 then coefficient ⟨j,hj⟩*odd j y else 0
def polynomial : Fin 5→ℚ[X]
  | 0 => 1
  | 1 => 1-C (3/2)*X
  | 2 => 1-C (3/2)*X+C (15/8)*X^2
  | 3 => 1-C (3/2)*X+C (15/8)*X^2-C (35/16)*X^3
  | 4 => 1-C (3/2)*X+C (15/8)*X^2-C (35/16)*X^3+C (315/128)*X^4
def truncation (n : Fin 5) (y : ℝ) : ℝ := aeval y (polynomial n)
def remainder (n : Fin 5) (j : ℕ) (y : ℝ) : ℝ :=
  (-1:ℝ)^n.val*(aeval y ((Polynomial.derivative^[j]) (polynomial n))-native j y)

theorem root_positive {y : ℝ} (hy : 0≤y) : 0<root y := Real.sqrt_pos.mpr (by linarith)
theorem root_square {y : ℝ} (hy : 0≤y) : (root y)^2=1+y :=
  Real.sq_sqrt (by linarith)
theorem root_hasDerivAt {y : ℝ} (hy : 0≤y) : HasDerivAt root (1/(2*root y)) y := by
  simpa [root] using ((hasDerivAt_id y).const_add 1).sqrt (by linarith : 1+y≠0)

theorem odd_hasDerivAt {j : ℕ} (hj : j<5) {y : ℝ} (hy : 0≤y) :
    HasDerivAt (odd j) (-((2*j+3:ℕ):ℝ)/2*odd (j+1) y) y := by
  have hr := root_positive hy
  have hh := (hasDerivAt_const y (1:ℝ)).div ((root_hasDerivAt hy).pow (2*j+3))
    (pow_ne_zero _ hr.ne')
  convert hh using 1
  · rfl
  · interval_cases j <;> norm_num [odd] <;> field_simp [hr.ne'] <;> ring

theorem native_hasDerivAt {j : ℕ} (hj : j<5) {y : ℝ} (hy : 0≤y) :
    HasDerivAt (native j) (native (j+1) y) y := by
  have h6 : j<6 := by omega
  have hnext : j+1<6 := by omega
  have hf : native j=(fun x => coefficient ⟨j,h6⟩*odd j x) := by
    funext x
    simp only [native,dif_pos h6]
  rw [hf]
  convert (odd_hasDerivAt hj hy).const_mul (coefficient ⟨j,h6⟩) using 1
  interval_cases j <;> norm_num [native,coefficient] <;> ring

theorem remainder_hasDerivAt (n : Fin 5) {j : ℕ} (hj : j<5) {y : ℝ} (hy : 0≤y) :
    HasDerivAt (remainder n j) (remainder n (j+1) y) y := by
  have hp := CenteredMonomialBounds.aeval_hasDerivAt ((Polynomial.derivative^[j]) (polynomial n)) y
  convert (hp.sub (native_hasDerivAt hj hy)).const_mul ((-1:ℝ)^n.val) using 1
  · rfl
  · simp only [remainder,Function.iterate_succ_apply']

theorem chain_nonnegative {F : ℕ→ℝ→ℝ} {N : ℕ} {u : ℝ} (hu : 0≤u)
    (hzero : ∀j<N,F j 0=0)
    (hd : ∀j<N,∀x∈Icc 0 u,HasDerivAt (F j) (F (j+1) x) x)
    (htop : ∀x∈Icc 0 u,0≤F N x) : ∀x∈Icc 0 u,0≤F 0 x := by
  induction N generalizing F with
  | zero => simpa using htop
  | succ N ih =>
    have hshift : ∀x∈Icc 0 u,0≤F 1 x := by
      apply ih (F:=fun j => F (j+1))
      · intro j hj
        exact hzero (j+1) (by omega)
      · intro j hj x hx
        simpa [Nat.add_assoc] using hd (j+1) (by omega) x hx
      · simpa [Nat.add_comm] using htop
    have hm : MonotoneOn (F 0) (Icc 0 u) := by
      apply monoOn_of_hasDeriv_nonneg
        (fun x hx => (hd 0 (by omega) x hx).continuousAt.continuousWithinAt)
        (fun x hx => hd 0 (by omega) x (Ioo_subset_Icc_self hx))
      exact fun x hx => hshift x (Ioo_subset_Icc_self hx)
    intro x hx
    have hh := hm ⟨le_rfl,hu⟩ hx hx.1
    rw [hzero 0 (by omega)] at hh
    exact hh

theorem initial_remainders (n : Fin 5) {j : ℕ} (hj : j<n.val+1) : remainder n j 0=0 := by
  fin_cases n <;> interval_cases j <;>
    norm_num [remainder,polynomial,native,coefficient,odd,root,
      Function.iterate_succ_apply',Function.iterate_zero]

theorem last_remainder (n : Fin 5) {y : ℝ} (hy : 0≤y) : 0≤remainder n (n.val+1) y := by
  have hp := root_positive hy
  fin_cases n <;>
    norm_num [remainder,polynomial,native,coefficient,odd,
      Function.iterate_succ_apply',Function.iterate_zero] <;> positivity

theorem alternating_remainder (n : Fin 5) {y : ℝ} (hy : 0≤y) :
    0≤(-1:ℝ)^n.val*(truncation n y-odd 0 y) := by
  have hh := chain_nonnegative (F:=remainder n) (N:=n.val+1) hy
    (fun j hj => initial_remainders n hj)
    (fun j hj x hx => remainder_hasDerivAt n (by omega) hx.1)
    (fun x hx => last_remainder n hx.1) y ⟨hy,le_rfl⟩
  simpa [remainder,truncation,native,coefficient] using hh

theorem first_lower {y : ℝ} (hy : 0≤y) : 1-(3/2)*y≤odd 0 y := by
  have hh := alternating_remainder 1 hy
  norm_num [truncation,polynomial] at hh
  linarith
theorem second_upper {y : ℝ} (hy : 0≤y) : odd 0 y≤1-(3/2)*y+(15/8)*y^2 := by
  have hh := alternating_remainder 2 hy
  norm_num [truncation,polynomial] at hh
  linarith
theorem third_lower {y : ℝ} (hy : 0≤y) :
    1-(3/2)*y+(15/8)*y^2-(35/16)*y^3≤odd 0 y := by
  have hh := alternating_remainder 3 hy
  norm_num [truncation,polynomial] at hh
  linarith
theorem fourth_upper {y : ℝ} (hy : 0≤y) :
    odd 0 y≤1-(3/2)*y+(15/8)*y^2-(35/16)*y^3+(315/128)*y^4 := by
  have hh := alternating_remainder 4 hy
  norm_num [truncation,polynomial] at hh
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.InversePower
