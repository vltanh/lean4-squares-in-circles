module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneRoleFour
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# Literal data for the three paired same-sign quarter owners

Uncompiled transcription of Section 1 of
`HAND_SHORT_WORD_SAME_SIGN_PRIMARY_COMPLETE_WITHOUT_TABLES.md`.
The source is parametrized by its primary coordinate and the target
by its transverse coordinate. Both are the original outer-circle states.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

abbrev Row := Fin 3
def c : Row→ℝ := ![-53489/100000,-53062/100000,-20704/100000]
def p : Row→ℝ := ![9133/100000,19335/100000,0]
def q : Row→ℝ := ![88074/100000,76744/100000,94766/100000]
def P : Row→ℝ := ![-33147/100000,-20967/100000,-21826/100000]
def t : Row→ℝ := ![11336/10000,83048/100000,83472/100000]
def b0 : ℝ := 1-outerDiagonal
def eta : ℝ := 1/80
def source (r : Row) (a : ℝ) : ℝ := p r*a-q r*arc a
def sourceD (r : Row) (a : ℝ) : ℝ := p r+q r*ratio a
def sourceDD (r : Row) (a : ℝ) : ℝ := q r*ratioD a
def target (r : Row) (B : ℝ) : ℝ := -P r*arc B+t r*B
def targetD (r : Row) (B : ℝ) : ℝ := P r*ratio B+t r
def aligned (r : Row) (B : ℝ) : ℝ := Real.pi/2+c r+source r (1-B)+target r B
def alignedD (r : Row) (B : ℝ) : ℝ := -sourceD r (1-B)+targetD r B
def alignedDD (r : Row) (B : ℝ) : ℝ := sourceDD r (1-B)+P r*ratioD B
def initialAngle (r : Row) (B : ℝ) : ℝ := 1-sourceD r (1-B)*(arc B-1/2)

lemma coefficient_bounds (r : Row) :
    0≤p r ∧ p r≤19335/100000 ∧ (76744/100000:ℝ)≤q r ∧ q r≤94766/100000 ∧
    P r≤0 ∧ 0<t r+P r ∧ (94766/100000:ℝ)≤p r+q r := by
  fin_cases r <;> norm_num [p,q,P,t]

lemma b0_bounds : (1/10:ℝ)<b0 ∧ b0<(101/1000:ℝ) := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  dsimp [b0]
  constructor <;> linarith

lemma b0_mem : b0∈Icc 0 outerDiagonal := by
  dsimp [b0]
  constructor <;> linarith [outer_endpoint_bounds.2.2.1,outer_endpoint_bounds.2.2.2]

lemma aligned_domains {B : ℝ} (hB : B∈Icc 0 b0) :
    B∈Icc 0 outerDiagonal ∧ 1-B∈Icc outerDiagonal 1 ∧
      1-B∈Icc outerDiagonal outerAxial := by
  have ha := outer_endpoint_bounds.1
  have h1 : outerDiagonal≤1-B := by dsimp [b0] at hB; linarith [hB.2]
  exact ⟨⟨hB.1,hB.2.trans b0_mem.2⟩,⟨h1,by linarith [hB.1]⟩,
    ⟨h1,by linarith [hB.1]⟩⟩

lemma primary_domain {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    a∈Icc 0 outerAxial := ⟨by linarith [ha.1,outer_endpoint_bounds.2.2.1],ha.2⟩

lemma primary_ratio_lower {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) : 1≤ratio a := by
  have hs := SameContact.primary_state ha
  have hp := SameContact.shifted_positive (primary_domain ha)
  change 1≤(a+1/2)/(arc a+1/2)
  exact (le_div_iff₀ hp).2 (by linarith [hs.2.1])

lemma source_hasDerivAt (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt (source r) (sourceD r a) a := by
  convert ((hasDerivAt_id a).const_mul (p r)).sub
    ((SameContact.arc_hasDerivAt (primary_domain ha)).const_mul (q r)) using 1 <;>
    dsimp [source,sourceD] <;> ring

lemma sourceD_hasDerivAt (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt (sourceD r) (sourceDD r a) a :=
  ((SameContact.ratio_hasDerivAt (primary_domain ha)).const_mul (q r)).const_add (p r)

lemma sourceD_lower (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (94766/100000:ℝ)≤sourceD r a := by
  have hh := mul_le_mul_of_nonneg_left (primary_ratio_lower ha)
    (show 0≤q r by fin_cases r <;> norm_num [q])
  dsimp [sourceD]
  linarith [(coefficient_bounds r).2.2.2.2.2.2]

lemma source_monotone (r : Row) : MonotoneOn (source r) (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (source_hasDerivAt r ha).continuousAt.continuousWithinAt)
    (fun a ha => source_hasDerivAt r (Ioo_subset_Icc_self ha))
    (fun a ha => by linarith [sourceD_lower r (Ioo_subset_Icc_self ha)])

lemma target_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (target r) (targetD r B) B := by
  convert ((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).const_mul (-P r)).add
    ((hasDerivAt_id B).const_mul (t r)) using 1 <;> dsimp [target,targetD] <;> ring

lemma targetD_positive (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 0<targetD r B := by
  have hr := SecondWord.outer_ratio_bounds hB
  have hh := mul_le_mul_of_nonpos_left hr.2.1 (coefficient_bounds r).2.2.2.2.1
  dsimp [targetD]
  linarith [(coefficient_bounds r).2.2.2.2.2.1]

lemma target_monotone (r : Row) : MonotoneOn (target r) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (target_hasDerivAt r hB).continuousAt.continuousWithinAt)
    (fun B hB => target_hasDerivAt r (Ioo_subset_Icc_self hB))
    (fun B hB => (targetD_positive r (Ioo_subset_Icc_self hB)).le)

lemma aligned_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 b0) :
    HasDerivAt (aligned r) (alignedD r B) B := by
  have hd := aligned_domains hB
  convert (((source_hasDerivAt r hd.2.2).comp B ((hasDerivAt_id B).const_sub 1)).
    const_add (Real.pi/2+c r)).add (target_hasDerivAt r hd.1) using 1 <;>
    dsimp [aligned,alignedD] <;> ring

lemma alignedD_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 b0) :
    HasDerivAt (alignedD r) (alignedDD r B) B := by
  have hd := aligned_domains hB
  convert (((sourceD_hasDerivAt r hd.2.2).comp B ((hasDerivAt_id B).const_sub 1)).neg).add
    (((SameContact.ratio_hasDerivAt (SameContact.outer_domain hd.1)).const_mul (P r)).add_const (t r)) using 1 <;>
    dsimp [alignedD,alignedDD,targetD] <;> ring

lemma aligned_target_root {B : ℝ} (hB : B∈Icc 0 b0) : (377/200:ℝ)<arc B+1/2 := by
  have hl := ShortOuterZero.Opposite.low_radical.1
  have hm := SameContact.arc_antitone (SameContact.outer_domain (aligned_domains hB).1)
    (SameContact.outer_domain b0_mem) hB.2
  change (377/200:ℝ)<arc (1-outerDiagonal)+1/2 at hl
  dsimp [b0] at hm
  linarith

lemma aligned_source_root {B : ℝ} (hB : B∈Icc 0 b0) :
    (129/100:ℝ)<arc (1-B)+1/2 ∧ arc (1-B)+1/2<(7/5:ℝ) := by
  have hd := aligned_domains hB
  have hc := SameContact.arc_circle (primary_domain hd.2.2)
  have hp := SameContact.shifted_positive (primary_domain hd.2.2)
  have hs := SameContact.primary_secondary_mem hd.2.2
  norm_num [Q0] at hc
  constructor
  · have hcoord : 0≤1-B+1/2 ∧ 1-B+1/2≤3/2 := by constructor <;> linarith [hB.1,hd.2.1.1,outer_endpoint_bounds.2.2.1]
    have hsq := pow_le_pow_left₀ hcoord.1 hcoord.2 2
    nlinarith
  · linarith [hs.2,outer_endpoint_bounds.2.2.2]

lemma aligned_curvature {B : ℝ} (hB : B∈Icc 0 b0) : (1:ℝ)<alignedDD 0 B := by
  have hu := aligned_source_root hB
  have hU := aligned_target_root hB
  have hp := SameContact.shifted_positive (SameContact.outer_domain (aligned_domains hB).1)
  have hup := SameContact.shifted_positive (primary_domain (aligned_domains hB).2.2)
  have hu3 := pow_le_pow_left₀ hup.le hu.2.le 3
  have hU3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤377/200) hU.le 3
  have hrlo : Q0/(7/5:ℝ)^3≤ratioD (1-B) := by
    dsimp [ratioD]
    apply (le_div_iff₀ (pow_pos hup 3)).2
    norm_num [Q0] at *
    nlinarith
  have hrhi : ratioD B≤Q0/(377/200:ℝ)^3 := by
    dsimp [ratioD]
    apply (div_le_iff₀ (pow_pos hp 3)).2
    norm_num [Q0] at *
    nlinarith
  norm_num [alignedDD,sourceDD,q,P,Q0] at *
  linarith

lemma aligned_later_derivative (r : Row) (hr : r=1 ∨ r=2)
    {B : ℝ} (hB : B∈Icc 0 b0) : alignedD r B<0 := by
  have hs := primary_ratio_lower (aligned_domains hB).2.2
  have ht := (SecondWord.outer_ratio_bounds (aligned_domains hB).1).1
  rcases hr with rfl | rfl <;>
    norm_num [alignedD,sourceD,targetD,p,q,P,t] <;> linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same
