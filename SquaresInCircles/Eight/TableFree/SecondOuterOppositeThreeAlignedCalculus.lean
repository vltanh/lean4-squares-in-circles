module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeData

/-!
# The two actual aligned opposite edge-three contacts

The two orders share one physical circle chart and one differentiation
argument.  Their inner coordinate is `arc y - 1`, derived from the
aligned separator.  Its full closed domain and all three derivatives
are retained explicitly.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.Aligned
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def inner (reverse : Bool) : RoleLabel := if reverse then LLabel else TLabel
def outer (reverse : Bool) : RoleLabel := if reverse then TLabel else LLabel
def j (y : ℝ) : ℝ := arc y-1
def cost (reverse : Bool) (y : ℝ) : ℝ :=
  Real.pi/2-(inner reverse).outer (j y)-(outer reverse).outer y
def first (reverse : Bool) (y : ℝ) : ℝ :=
  (inner reverse).d1 (j y)*ratio y-(outer reverse).d1 y
def second (reverse : Bool) (y : ℝ) : ℝ :=
  -(inner reverse).d2 (j y)*(ratio y)^2+
    (inner reverse).d1 (j y)*ratioD y-(outer reverse).d2 y
def third (reverse : Bool) (y : ℝ) : ℝ :=
  (inner reverse).d3 (j y)*(ratio y)^3-
    3*(inner reverse).d2 (j y)*ratio y*ratioD y+
      (inner reverse).d1 (j y)*ratioDD y-(outer reverse).d3 y

lemma mem_outer {y : ℝ} (hy : y∈Icc 0 bOne) : y∈Icc 0 outerDiagonal :=
  ⟨hy.1,hy.2.trans OppositeTwo.bOne_mem.2⟩

lemma j_bounds {y : ℝ} (hy : y∈Icc 0 bOne) : 0≤j y ∧ j y<83/200 := by
  have hlo := ShortOuterOne.SameContact.arc_antitone (outer_domain (mem_outer hy))
    (outer_domain OppositeTwo.bOne_mem) hy.2
  rw [OppositeTwo.bOne_arc] at hlo
  have hhi := (CommonQuarter.outer_bounds
    (ShortOuterOne.SameContact.arc_state (mem_outer hy))).2.1
  dsimp [j]
  exact ⟨by linarith,by linarith [outer_endpoint_bounds.2.1]⟩

lemma j_mem {y : ℝ} (hy : y∈Icc 0 bOne) : j y∈Icc 0 outerDiagonal :=
  ⟨(j_bounds hy).1,by linarith [(j_bounds hy).2,fine_outer_endpoint_bounds.2]⟩

lemma coordinates {y : ℝ} (hy : y∈Icc 0 bOne) :
    (3/2:ℝ)≤U y ∧ W y<1291/1000 ∧ ratio y<861/1000 := by
  have hj := j_bounds hy
  have hw : W y<1291/1000 := by
    dsimp [W]
    linarith [hy.2,OppositeTwo.bOne_bounds.2]
  have hu : (3/2:ℝ)≤U y := by dsimp [U,j] at *; linarith [hj.1]
  refine ⟨hu,hw,?_⟩
  change W y/U y<861/1000
  apply (div_lt_iff₀ (U_positive (outer_domain (mem_outer hy)))).2
  linarith

lemma j_hasDerivAt {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt j (-ratio y) y :=
  (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain (mem_outer hy))).sub_const 1

lemma cost_hasDerivAt (reverse : Bool) {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt (cost reverse) (first reverse y) y := by
  have hi := ((inner reverse).outer_hasDerivAt (outer_domain (j_mem hy))).comp y
    (j_hasDerivAt hy)
  have ho := (outer reverse).outer_hasDerivAt (outer_domain (mem_outer hy))
  convert (hi.const_sub (Real.pi/2)).sub ho using 1 <;> dsimp [cost,first] <;> ring

lemma first_hasDerivAt (reverse : Bool) {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt (first reverse) (second reverse y) y := by
  have hi := ((inner reverse).d1_hasDerivAt (outer_domain (j_mem hy))).comp y
    (j_hasDerivAt hy)
  have hr := ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (mem_outer hy))
  have ho := (outer reverse).d1_hasDerivAt (outer_domain (mem_outer hy))
  convert (hi.mul hr).sub ho using 1 <;> dsimp [first,second] <;> ring

lemma second_hasDerivAt (reverse : Bool) {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt (second reverse) (third reverse y) y := by
  have hi := ((inner reverse).d1_hasDerivAt (outer_domain (j_mem hy))).comp y
    (j_hasDerivAt hy)
  have hi2 := ((inner reverse).d2_hasDerivAt (outer_domain (j_mem hy))).comp y
    (j_hasDerivAt hy)
  have hr := ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (mem_outer hy))
  have hr2 := ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain (mem_outer hy))
  have ho := (outer reverse).d2_hasDerivAt (outer_domain (mem_outer hy))
  convert (((hi2.neg.mul (hr.pow 2)).add (hi.mul hr2)).sub ho) using 1 <;>
    dsimp [second,third] <;> ring

lemma forward_value (y : ℝ) : cost false y=OppositeThree.value (j y) y (Real.pi/2) := rfl
lemma reverse_value (y : ℝ) : cost true y=OppositeThree.value y (j y) (Real.pi/2) := by
  dsimp [cost,inner,outer,OppositeThree.value,T,L]
  ring

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.Aligned
