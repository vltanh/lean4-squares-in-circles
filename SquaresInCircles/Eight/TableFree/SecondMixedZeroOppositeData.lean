module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroData
public import SquaresInCircles.Eight.TableFree.SecondOuterGeneralReference
public import SquaresInCircles.Eight.TableFree.SecondOuterFifthCalculus

/-!
# The three opposite-sign mixed zero reflection classes

Uncompiled source draft.  The row index identifies only the literal
J, P or L role label.  Each analytic statement will retain the full
core side and corner, the physical outer arc and both angle signs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

abbrev Row := Fin 3
def c : Row → ℝ := ![125/100000,19555/100000,4970/100000]
def g : Row → ℝ := ![103981/100000,63132/100000,94831/100000]
def F : Row → RoleLabel := ![JLabel,PLabel,LLabel]
def role : Row → Vertex := ![0,1,4]
def aligned (r : Row) (B : ℝ) : ℝ := c r+g r*(1-B)+(F r).outer B
def alignedD (r : Row) (B : ℝ) : ℝ := (F r).d1 B-g r

lemma slope_bounds (r : Row) : 0<g r ∧ g r≤103981/100000 := by
  fin_cases r <;> norm_num [g]

lemma outer_monotone (r : Row) : MonotoneOn (F r).outer (Icc 0 outerDiagonal) := by
  fin_cases r
  · exact J_monotone
  · exact P_monotone
  · exact L_monotone

lemma aligned_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (aligned r) (alignedD r B) B := by
  convert (((((hasDerivAt_id B).const_sub 1).const_mul (g r)).const_add (c r)).add
    ((F r).outer_hasDerivAt (outer_domain hB))) using 1 <;> dsimp [aligned,alignedD] <;> ring

lemma alignedD_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (alignedD r) ((F r).d2 B) B :=
  ((F r).d1_hasDerivAt (outer_domain hB)).sub_const (g r)

lemma literal (r : Row) (kind : RadialKind) (hk : kind≠.outer)
    {a b A B x : ℝ} (ht : OuterState A B) :
    cost (role r) kind .outer true false a b A B x=
      x+c r+g r*b+(F r).outer B := by
  rw [(F r).outer_actual ht]
  fin_cases r <;> cases kind <;>
    norm_num [cost,label,wrongValue,WordProblems.secondCoefficients,
      WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
      next,c,g,F,role,JLabel,PLabel,LLabel,RoleLabel.eval] at hk ⊢ <;> ring

/-- A convex derivative ending nonpositive permits only a maximum
before the right endpoint.  The two endpoints therefore control the
whole interval; this is used for the initial L aligned arc. -/
lemma endpoint_minimum_of_convex_derivative {f d : ℝ → ℝ} {l u x : ℝ}
    (hx : x∈Icc l u) (hd : ∀t∈Icc l u,HasDerivAt f (d t) t)
    (hc : ConcaveOn ℝ (Icc l u) (fun t => -d t)) (hu : d u≤0) :
    min (f l) (f u)≤f x := by
  by_cases hdx : d x≤0
  · have hm : AntitoneOn f (Icc x u) := by
      apply antiOn_of_hasDeriv_nonpos
      · exact fun t ht => (hd t ⟨hx.1.trans ht.1,ht.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => hd t ⟨hx.1.trans ht.1.le,ht.2.le⟩
      · intro t ht
        have hh := hc.min_le_of_mem_Icc hx ⟨hx.1.trans hx.2,le_rfl⟩
          (Ioo_subset_Icc_self ht)
        have hn : 0≤min (-d x) (-d u) := le_min (by linarith) (by linarith)
        linarith
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)
  · have hm : MonotoneOn f (Icc l x) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact fun t ht => (hd t ⟨ht.1,ht.2.trans hx.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => hd t ⟨ht.1.le,ht.2.le.trans hx.2⟩
      · intro t ht
        by_contra! hdt
        have hh := hc.min_le_of_mem_Icc ⟨ht.1.le,ht.2.le.trans hx.2⟩
          ⟨hx.1.trans hx.2,le_rfl⟩ ⟨ht.2.le,hx.2⟩
        have hn : 0≤min (-d t) (-d u) := le_min (by linarith) (by linarith)
        linarith
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite
