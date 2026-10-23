module

public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeThreeNegativeUpper
public import SquaresInCircles.Eight.TableFree.SecondMixedLPrimaryZeroCost

/-!
# The original negative-core transverse contact

On the lower angle half every feasible transverse source lies strictly
on the straight core side. Increasing its coordinate to contact stays
on that same side and only decreases the cost. These facts retain the
original target and both weak endpoints. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open PositiveThree (Lower lowerAngle lower_trig)

abbrev g := EdgeThreeAligned.gn
abbrev z := EdgeThreeAligned.zn
abbrev e := EdgeThreeAligned.en
abbrev γ := EdgeThreeAligned.threshold
abbrev value := EdgeThreeAligned.negativeCost
abbrev sideValue := EdgeThreeAligned.negativeSideCost

def contact (B φ : ℝ) : ℝ :=
  (arc B-1/2)*Real.sin φ-(B+1/2)*Real.cos φ-1/2
def contactD (B φ : ℝ) : ℝ :=
  (arc B-1/2)*Real.cos φ+(B+1/2)*Real.sin φ
def C (B φ : ℝ) : ℝ := sideValue (contact B φ) B φ
def CD (B φ : ℝ) : ℝ := 1-(g-2*z*contact B φ)*contactD B φ
def CDD (B φ : ℝ) : ℝ :=
  2*z*(contactD B φ)^2+(g-2*z*contact B φ)*(contact B φ+1/2)

lemma contact_hasDerivAt (B φ : ℝ) :
    HasDerivAt (contact B) (contactD B φ) φ := by
  convert (((Real.hasDerivAt_sin φ).const_mul (arc B-1/2)).sub
    ((Real.hasDerivAt_cos φ).const_mul (B+1/2))).sub_const (1/2) using 1 <;>
    dsimp [contact,contactD] <;> ring

lemma contactD_hasDerivAt (B φ : ℝ) :
    HasDerivAt (contactD B) (-(contact B φ+1/2)) φ := by
  convert ((Real.hasDerivAt_cos φ).const_mul (arc B-1/2)).add
    ((Real.hasDerivAt_sin φ).const_mul (B+1/2)) using 1 <;>
    dsimp [contact,contactD] <;> ring

lemma C_hasDerivAt (B φ : ℝ) : HasDerivAt (C B) (CD B φ) φ := by
  convert (((hasDerivAt_id φ).sub
    ((((contact_hasDerivAt B φ).const_mul g).const_add e).sub
      (((contact_hasDerivAt B φ).pow 2).const_mul z))).sub_const (L B)) using 1 <;>
    dsimp [C,CD,sideValue,EdgeThreeAligned.negativeSideCost,EdgeThreeAligned.sideH] <;> ring

lemma CD_hasDerivAt (B φ : ℝ) : HasDerivAt (CD B) (CDD B φ) φ := by
  convert (((((contact_hasDerivAt B φ).const_mul (2*z)).const_sub g).mul
    (contactD_hasDerivAt B φ)).const_sub 1) using 1 <;>
    dsimp [CD,CDD] <;> ring

lemma contact_upper {A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ) :
    contact B φ≤A-1 := by
  have htr := lower_trig hφ
  have ha : (89/100:ℝ)<A := outer_endpoint_bounds.2.2.1.trans_le (outer_bounds ht).1
  have hp := mul_nonneg (show 0≤A-1/2 by linarith) (sub_nonneg.mpr htr.2.1)
  have hq := mul_nonneg (show 0≤B+1/2 by linarith [ht.1]) htr.2.2.1
  dsimp [contact]
  rw [(actual_arc ht).1]
  nlinarith

lemma contactD_positive {A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ) :
    0<contactD B φ := by
  have htr := lower_trig hφ
  have ha : (89/100:ℝ)<A := outer_endpoint_bounds.2.2.1.trans_le (outer_bounds ht).1
  have hp := mul_nonneg (show 0≤A-1/2 by linarith) htr.2.2.1
  have hq := mul_pos (show 0<B+1/2 by linarith [ht.1]) (show 0<Real.sin φ by linarith [htr.1])
  dsimp [contactD]
  rw [(actual_arc ht).1]
  linarith

lemma contact_monotone {A B : ℝ} (ht : OuterState A B) :
    MonotoneOn (contact B) (Icc lowerAngle (Real.pi/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun φ _ => (contact_hasDerivAt B φ).continuousAt.continuousWithinAt)
    (fun φ _ => contact_hasDerivAt B φ)
    (fun φ hφ => (contactD_positive ht (Ioo_subset_Icc_self hφ)).le)

lemma original_contact {a b A B φ : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-b+A*Real.sin φ-B*Real.cos φ) :
    a=7/12 ∧ 0≤contact B φ ∧ contact B φ<(83/200:ℝ) ∧
      1≤A ∧ C B φ≤value a b B φ := by
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  have hA := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hbc : b≤contact B φ := by
    dsimp [contact]
    rw [(actual_arc ht).1]
    linarith
  have hupper := contact_upper ht hφ
  have hside : b<1/2 := by linarith
  have ha := (CommonQuarter.core_small_side hs hside).1
  have hmono := EdgeThreeAligned.sideH_mono hb (by linarith : contact B φ≤1/2) hbc
  refine ⟨ha,by linarith,by linarith,by linarith,?_⟩
  dsimp [C,sideValue,value,EdgeThreeAligned.negativeSideCost,EdgeThreeAligned.negativeCost]
  rw [ha,EdgeThreeAligned.sideH_eq]
  linarith

lemma contact_aligned {A B : ℝ} (ht : OuterState A B) :
    contact B (Real.pi/2)=A-1 := by
  norm_num [contact,(actual_arc ht).1]

lemma aligned_lower {A B : ℝ} (ht : OuterState A B) (hA : 1≤A) :
    γ<C B (Real.pi/2) := by
  have hh := EdgeThreeAligned.negative_side_aligned (b := A-1) ht (by linarith) (by linarith)
  rw [C,contact_aligned ht]
  dsimp [γ,EdgeThreeAligned.threshold]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource
