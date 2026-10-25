module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerThird

/-!
# Both original lower-secondary owners on their exact common contact domain

The contact domain is the actual shifted-circle quarter disk.  The two
costs differ only in which literal label is assigned to its free
coordinate.  Original weak margins compare directly with the inverse
phase; no replacement radius, angle witness, or strict-coordinate
assumption is introduced.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerContact
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def Domain (b B : ℝ) : Prop :=
  b∈Icc 0 outerDiagonal ∧ B∈Icc 0 outerDiagonal ∧ b≤arc B-1
def inner (reverse : Bool) : RoleLabel := if reverse then LLabel else TLabel
def outer (reverse : Bool) : RoleLabel := if reverse then TLabel else LLabel
def cost (reverse : Bool) (b B : ℝ) : ℝ :=
  Real.pi/2+LowerInverse.phase (b+1/2) B-(inner reverse).outer b-(outer reverse).outer B
def freeFirst (reverse : Bool) (b B : ℝ) : ℝ :=
  1/LowerInverse.speed (b+1/2) B-(inner reverse).d1 b
def outerFirst (reverse : Bool) (b B : ℝ) : ℝ :=
  LowerInverse.first (b+1/2) B-(outer reverse).d1 B
def freeSecond (reverse : Bool) (b B : ℝ) : ℝ :=
  (b+1/2)/(LowerInverse.speed (b+1/2) B)^3-(inner reverse).d2 b
def mixed (b B : ℝ) : ℝ := -ratio B/(LowerInverse.speed (b+1/2) B)^3
def outerSecond (reverse : Bool) (b B : ℝ) : ℝ :=
  LowerInverse.second (b+1/2) B-(outer reverse).d2 B
def outerThird (reverse : Bool) (b B : ℝ) : ℝ :=
  LowerInverse.third (b+1/2) B-(outer reverse).d3 B

lemma domain_bounds {b B : ℝ} (hd : Domain b B) :
    b<(83/200:ℝ) ∧ B≤bOne ∧ b+1/2∈LowerInverse.shifts := by
  have hA := NegativeTwo.primary_mem (ShortOuterOne.SameContact.arc_state hd.2.1)
  have hb : b<83/200 := by linarith [hd.2.2,hA.2,outer_endpoint_bounds.2.1]
  have hB : B≤bOne := below_bOne_of_primary_one
    (ShortOuterOne.SameContact.arc_state hd.2.1) (by linarith [hd.1.1,hd.2.2])
  exact ⟨hb,hB,⟨by linarith [hd.1.1],by linarith⟩⟩

lemma domain_circle {b B : ℝ} (hd : Domain b B) :
    (b+3/2)^2+(B+1/2)^2≤Q0 := by
  have hh := (ShortOuterOne.SameContact.arc_state hd.2.1).2.2
  have hp := mul_nonneg (show 0≤arc B-1-b by linarith [hd.2.2])
    (show 0≤arc B+b+2 by linarith [(NegativeTwo.primary_mem
      (ShortOuterOne.SameContact.arc_state hd.2.1)).1,hd.1.1,fine_outer_endpoint_bounds.2])
  nlinarith

lemma physical_speed {b B : ℝ} (hd : Domain b B) :
    W B≤LowerInverse.speed (b+1/2) B := by
  have hh := OppositeTwo.PrimaryInverse.data hd.2.1 (domain_bounds hd).2.2
  have hbase := NegativeTwo.ContactInverse.base_circle hd.2.1
  have hz : b+1/2≤U B-1 := by dsimp [U]; linarith [hd.2.2]
  have hnonneg : 0≤b+1/2 := by linarith [hd.1.1]
  have hw : 0<W B := by dsimp [W]; linarith [hd.2.1.1]
  nlinarith [hh.2.2.1,hh.2.2.2]

lemma cut_domain {b B x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10))
    (hcut : b≤lowerSecondary B x) : Domain b B := by
  have ht := positive_trig hx
  have hA := NegativeTwo.primary_mem (ShortOuterOne.SameContact.arc_state hB)
  have hcos := mul_le_mul_of_nonneg_left ht.2.1
    (show 0≤arc B-1/2 by linarith [hA.1,fine_outer_endpoint_bounds.2])
  have hsin := mul_nonneg (show 0≤B+1/2 by linarith [hB.1]) ht.2.2.1
  dsimp [lowerSecondary] at hcut
  exact ⟨hb,hB,by nlinarith⟩

lemma cost_free_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal)
    (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (fun t => cost reverse t B) (freeFirst reverse b B) b := by
  have hd := (LowerInverse.phase_shift_hasDerivAt hB hz).comp b
    ((hasDerivAt_id b).add_const (1/2))
  convert (((hd.const_add (Real.pi/2)).sub
    ((inner reverse).outer_hasDerivAt (outer_domain hb))).sub_const ((outer reverse).outer B))
    using 1 <;> dsimp [cost,freeFirst] <;> ring

lemma cost_outer_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (cost reverse b) (outerFirst reverse b B) B := by
  have hd := (((LowerInverse.phase_source_hasDerivAt hB hz).const_add (Real.pi/2)).sub_const
    ((inner reverse).outer b)).fun_sub ((outer reverse).outer_hasDerivAt (outer_domain hB))
  exact hd.congr_deriv (by simp only [outerFirst])

lemma freeFirst_free_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal)
    (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (fun t => freeFirst reverse t B) (freeSecond reverse b B) b := by
  have hd := ((LowerInverse.shift_second_hasDerivAt hB hz).comp b
    ((hasDerivAt_id' (x := b)).add_const (1/2))).fun_sub
      ((inner reverse).d1_hasDerivAt (outer_domain hb))
  exact hd.congr_deriv (by simp only [freeSecond]; ring)

lemma freeFirst_outer_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (freeFirst reverse b) (mixed b B) B := by
  convert (LowerInverse.shift_source_hasDerivAt hB hz).sub_const ((inner reverse).d1 b)
    using 1 <;> rfl

lemma outerFirst_free_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (fun t => outerFirst reverse t B) (mixed b B) b := by
  have hd := (LowerInverse.first_shift_hasDerivAt hB hz).comp b
    ((hasDerivAt_id b).add_const (1/2))
  convert hd.sub_const ((outer reverse).d1 B) using 1 <;>
    dsimp [outerFirst,mixed] <;> ring

lemma outerFirst_outer_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (outerFirst reverse b) (outerSecond reverse b B) B := by
  convert (LowerInverse.first_source_hasDerivAt hB hz).sub
    ((outer reverse).d1_hasDerivAt (outer_domain hB)) using 1 <;> rfl

lemma outerSecond_hasDerivAt (reverse : Bool) {b B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) (hz : b+1/2∈LowerInverse.shifts) :
    HasDerivAt (outerSecond reverse b) (outerThird reverse b B) B := by
  convert (LowerInverse.second_source_hasDerivAt hB hz).sub
    ((outer reverse).d2_hasDerivAt (outer_domain hB)) using 1 <;> rfl

lemma aligned_lower (reverse : Bool) {b B : ℝ} (hd : Domain b B)
    (halign : b=arc B-1) : (44889/50000:ℝ)<cost reverse b B := by
  have hphase := LowerInverse.aligned hd.2.1 (z := b+1/2)
    (by dsimp [U]; linarith)
  have hs := ShortOuterOne.SameContact.arc_state hd.1
  have ht := ShortOuterOne.SameContact.arc_state hd.2.1
  cases reverse
  · have hh := aligned_first hs ht (by linarith)
    dsimp [cost,inner,outer,value,T,L] at *
    rw [hphase]
    linarith
  · have hh := aligned_last ht hs (by linarith)
    dsimp [cost,inner,outer,value,T,L] at *
    rw [hphase]
    linarith

theorem original_first_reduction {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2-x)) :
    Domain b B ∧ cost false b B≤value b B (Real.pi/2-x) := by
  have hcut := lower_source_secondary ht hx hm
  have hd := cut_domain (NegativeTwo.source_mem hs) (NegativeTwo.source_mem ht) hx hcut
  have hf := LowerInverse.weak_phase hd.2.1 (domain_bounds hd).2.2 hx
    (by dsimp [lowerSecondary] at hcut; linarith)
  refine ⟨hd,?_⟩
  dsimp [cost,inner,outer,value,T,L]
  linarith

theorem original_third_reduction {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    Domain B b ∧ cost true B b≤value b B (Real.pi/2-x) := by
  have hcut := lower_target_secondary hs hx hm
  have hd := cut_domain (NegativeTwo.source_mem ht) (NegativeTwo.source_mem hs) hx hcut
  have hf := LowerInverse.weak_phase hd.2.1 (domain_bounds hd).2.2 hx
    (by dsimp [lowerSecondary] at hcut; linarith)
  refine ⟨hd,?_⟩
  dsimp [cost,inner,outer,value,T,L]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerContact
