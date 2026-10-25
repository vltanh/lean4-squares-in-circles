module

public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveData

/-!
# Eight squares: translated circle coordinates for the lower opposite edge-five contacts

The square roots are the actual positive circle coordinates. Their
domain includes every interval between a contact and its axial reference.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive
open CommonQuarter CorePairGeometry Arithmetic

def width (u : ℝ) : ℝ := (1+Real.cos u+Real.sin u)/2
def root (v : ℝ) : ℝ := Real.sqrt (Q0-v^2)
def rootD (v : ℝ) : ℝ := -v/root v
def rootDD (v : ℝ) : ℝ := -Q0/(root v)^3
def RootDomain (v : ℝ) : Prop := v∈Icc (1/2) X0
def cShift (r : Bool) : ℝ := c+(-p r+q r+P r+t r)/2
def D (r : Bool) (u : ℝ) : ℝ := P r*Real.cos u-t r*Real.sin u
def E (r : Bool) (u : ℝ) : ℝ := P r*Real.sin u+t r*Real.cos u
def axialZ (u : ℝ) : ℝ := 1/2+Real.cos u
def axialT (u : ℝ) : ℝ := root (axialZ u)
def axial (r : Bool) (u : ℝ) : ℝ := Real.pi/2-u+c+p r*outerAxial+
  (P r+t r)/2-D r u*axialZ u-E r u*axialT u

lemma root_domain_iff {v : ℝ} : RootDomain v↔v-1/2∈Icc 0 outerAxial := by
  rw [RootDomain,X0_eq]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
lemma root_eq_arc {v : ℝ} : root v=SameContact.arc (v-1/2)+1/2 := by
  dsimp [root,SameContact.arc]
  rw [show v-1/2+1/2=v by ring]
  ring
lemma root_positive {v : ℝ} (hv : RootDomain v) : 0<root v := by
  rw [root_eq_arc]
  exact SameContact.shifted_positive (root_domain_iff.1 hv)
lemma root_sq {v : ℝ} (hv : RootDomain v) : (root v)^2=Q0-v^2 := by
  have hsq := pow_le_pow_left₀ (show 0≤v by linarith [hv.1]) hv.2 2
  exact Real.sq_sqrt (by nlinarith [X0_sq])
lemma root_le_X0 {v : ℝ} (hv : RootDomain v) : root v≤X0 := by
  have hv2 : (1/4:ℝ)≤v^2 := by nlinarith [hv.1]
  nlinarith [root_sq hv,X0_sq,root_positive hv,X0_bounds.1]

lemma root_hasDerivAt {v : ℝ} (hv : RootDomain v) : HasDerivAt root (rootD v) v := by
  have hp : 0<Q0-v^2 := by rw [←root_sq hv]; exact pow_pos (root_positive hv) 2
  have h1 : HasDerivAt (fun y : ℝ => Q0-y^2) (-(2*v)) v := by
    simpa using (hasDerivAt_pow 2 v).const_sub Q0
  have hh : HasDerivAt root (-(2*v)/(2*Real.sqrt (Q0-v^2))) v := h1.sqrt hp.ne'
  exact hh.congr_deriv (by simp only [rootD,root]; ring)
lemma rootD_hasDerivAt {v : ℝ} (hv : RootDomain v) : HasDerivAt rootD (rootDD v) v := by
  have hh := ((hasDerivAt_id v).neg).div (root_hasDerivAt hv) (root_positive hv).ne'
  convert hh using 1
  · rfl
  · dsimp [rootD,rootDD]
    field_simp [(root_positive hv).ne']
    nlinarith [root_sq hv]
lemma root_antitone : AntitoneOn root (Icc (1/2) X0) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun v hv => (root_hasDerivAt hv).continuousAt.continuousWithinAt)
    (fun v hv => root_hasDerivAt (Ioo_subset_Icc_self hv))
  intro v hv
  dsimp [rootD]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [hv.1])
    (root_positive (Ioo_subset_Icc_self hv)).le

lemma axialZ_domain {u : ℝ} (hu : u∈Icc 0 (7/10)) : RootDomain (axialZ u) := by
  have ht := positive_trig hu
  exact ⟨by dsimp [axialZ]; linarith [ht.1],by dsimp [axialZ]; linarith [ht.2.1,X0_bounds.1]⟩
lemma axialT_positive {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<axialT u := root_positive (axialZ_domain hu)
lemma axialT_sq {u : ℝ} (hu : u∈Icc 0 (7/10)) : (axialT u)^2=Q0-(axialZ u)^2 :=
  root_sq (axialZ_domain hu)
lemma root_half : root (1/2)=X0 := by norm_num [root,X0]
lemma root_three_halves : root (3/2)=T0 := by norm_num [root,T0]

lemma width_ge_one {u : ℝ} (hu : u∈Icc 0 (7/10)) : 1≤width u := by
  dsimp [width]
  linarith [(positive_trig hu).2.2.2.2.2]

lemma E_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<E r u := by
  have ht := positive_trig hu
  have hP := mul_nonneg (show 0≤P r by linarith [(coefficient_bounds r).2.2.2.2.1]) ht.2.2.1
  have ht' := mul_pos (show 0<t r by linarith [(coefficient_bounds r).2.2.2.2.2.2.1])
    (show 0<Real.cos u by linarith [ht.1])
  dsimp [E]
  linarith

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive
