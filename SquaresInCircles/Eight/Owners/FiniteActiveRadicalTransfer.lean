module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic

/-!
# Eight squares: A finite positive-mass radical transfer with inactive summands

Each positive auxiliary multiplies its
own square comparison. Multiplication by the product of the other
positive auxiliaries removes every denominator. An inactive term has
zero actual norm; it is absent from the numerator as well. This single
lemma treats three- and four-norm endpoint expressions without adding
a spurious norm to the sorted-D baseline.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.FiniteActiveRadicalTransfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A purely real, division-free version of the rational auxiliary estimate. -/
theorem positive (active : ι→Prop) [DecidablePred active]
    (mass norm upper : ι→ℝ) {R Rbar A B : ℝ}
    (hmass : ∀i,0< mass i) (hnorm : ∀i,0≤norm i)
    (hupper : ∀i,(norm i)^2≤upper i)
    (hinactive : ∀i,¬active i→norm i=0)
    (hR : R≤Rbar) (hRbar : 0≤Rbar) (hA : A≤B)
    (hnum : 0<2*A*(∏i,mass i)-Rbar*
      ∑i,if active i then (upper i+(mass i)^2)*∏j∈Finset.univ.erase i,mass j else 0) :
    0<B-R*∑i,norm i := by
  let total : ℝ := ∏i,mass i
  let others (i : ι) : ℝ := ∏j∈Finset.univ.erase i,mass j
  have htotal : 0<total := Finset.prod_pos (fun i _ => hmass i)
  have hothers (i : ι) : 0≤others i :=
    (Finset.prod_pos (fun j _ => hmass j)).le
  have hfactor (i : ι) : total=mass i*others i := by
    have hi : insert i (Finset.univ.erase i)=(Finset.univ : Finset ι) :=
      Finset.insert_erase (Finset.mem_univ i)
    calc
      total=∏j∈insert i (Finset.univ.erase i),mass j :=
        congrArg (fun s : Finset ι => ∏j∈s,mass j) hi.symm
      _=mass i*others i := by
        rw [Finset.prod_insert (by simp)]
  have hterm (i : ι) :
      2*total*R*norm i≤Rbar*(if active i then (upper i+(mass i)^2)*others i else 0) := by
    by_cases hi : active i
    · have hsquare : 2*mass i*norm i≤upper i+(mass i)^2 := by
        nlinarith only [hupper i,sq_nonneg (norm i-mass i)]
      have hscaled := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare hRbar) (hothers i)
      have hrad := mul_le_mul_of_nonneg_left hR
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) htotal.le) (hnorm i))
      simp only [hi,↓reduceIte]
      rw [hfactor i] at hrad ⊢
      linarith only [hscaled,hrad]
    · rw [hinactive i hi]
      simp [hi]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hterm i)
  simp only [←Finset.mul_sum] at hsum
  have hA' := mul_le_mul_of_nonneg_right hA (show 0≤2*total by positivity)
  have hnum' : 0<2*A*total-Rbar*
      ∑i,if active i then (upper i+(mass i)^2)*others i else 0 := hnum
  have hpositive : 0<2*total*(B-R*∑i,norm i) := by
    linarith only [hsum,hA',hnum']
  exact (mul_pos_iff_of_pos_left (show 0<2*total by positivity)).mp hpositive

end SquaresInCircles.Eight.FiniteActiveRadicalTransfer
