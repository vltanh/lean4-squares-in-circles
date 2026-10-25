module

public import SquaresInCircles.Eight.TableFree.SecondMixedPHeight

/-!
# A cubic lower bound at every original physical height

All four Taylor coefficients are rational lower bounds at 1.399.
Positive fourth derivative transfers the third-derivative bound to
the entire physical height interval. The polynomial itself increases
down to height one, allowing later separator comparisons to evaluate
it at a lower contact height without asserting a physical contact.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.PHeightTaylor
open CommonQuarter CorePairGeometry Arithmetic HeightLabel PHeightBounds

def r : ℝ := 1399/1000
def c0 : ℝ := -791109861/1000000000
def c1 : ℝ := 243109289/250000000
def c2 : ℝ := 979396819/1000000000
def c3 : ℝ := 79899843/40000000
def poly (u : ℝ) : ℝ := c0+c1*(u-r)+(c2/2)*(u-r)^2+(c3/6)*(u-r)^3
def d1 (u : ℝ) : ℝ := c1+c2*(u-r)+(c3/2)*(u-r)^2
def d2 (u : ℝ) : ℝ := c2+c3*(u-r)

lemma reference_mem : r∈physicalHeights := by norm_num [r,physicalHeights]

lemma reference_bounds : c0<PHeight.eval r ∧ c1<PHeight.d1 r ∧
    c2<PHeight.d2 r ∧ c3<PHeight.d3 r := by
  have hr := root_cage (u := r)
    (l := (1399428097474/1000000000000:ℝ)) (r := (55977123899/40000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [r,Q0]) (by norm_num [r,Q0])
  have hp := root_pos (domain (physical_subset reference_mem))
  have h1 := PHeight.d1_mul (domain (physical_subset reference_mem))
  have h2 := PHeight.d2_mul (domain (physical_subset reference_mem))
  have h3 := PHeight.d3_mul (domain (physical_subset reference_mem))
  have hpow3 := pow_le_pow_left₀ hp.le hr.2.le 3
  have hpow5 := pow_le_pow_left₀ hp.le hr.2.le 5
  simp only [r] at hr hp h1 h2 h3 hpow3 hpow5
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [PHeight,HeightLabel.eval,c0,r,Q0]
    nlinarith [hr.2]
  · apply (mul_lt_mul_iff_left₀ hp).mp
    norm_num [PHeight,c1,r,Q0] at h1 ⊢
    nlinarith [hr.2]
  · apply (mul_lt_mul_iff_left₀ (pow_pos hp 3)).mp
    norm_num [PHeight,c2,r,Q0] at h2 ⊢
    nlinarith
  · apply (mul_lt_mul_iff_left₀ (pow_pos hp 5)).mp
    norm_num [PHeight,c3,r,Q0] at h3 ⊢
    nlinarith

lemma poly_hasDerivAt (u : ℝ) : HasDerivAt poly (d1 u) u := by
  have hd := ((((hasDerivAt_id u).sub_const r).const_mul c1).const_add c0).add
    ((((hasDerivAt_id u).sub_const r).pow 2).const_mul (c2/2))
  convert hd.add ((((hasDerivAt_id u).sub_const r).pow 3).const_mul (c3/6)) using 1
  · funext x
    simp only [poly,Pi.add_apply,Pi.pow_apply,id]
  · simp only [d1,id,Nat.cast_ofNat]
    ring

lemma d1_hasDerivAt (u : ℝ) : HasDerivAt d1 (d2 u) u := by
  convert ((((hasDerivAt_id u).sub_const r).const_mul c2).const_add c1).add
    ((((hasDerivAt_id u).sub_const r).pow 2).const_mul (c3/2)) using 1
  · funext x
    simp only [d1,Pi.add_apply,Pi.pow_apply,id]
  · simp only [d2,id,Nat.cast_ofNat]
    ring

lemma d2_hasDerivAt (u : ℝ) : HasDerivAt d2 c3 u := by
  convert (((hasDerivAt_id u).sub_const r).const_mul c3).const_add c2 using 1
  · funext x
    simp only [d2,id]
  · ring

lemma d2_positive {u : ℝ} (hu : u∈heights) : 0<d2 u := by
  dsimp [d2,c2,c3,r]
  linarith [hu.1]

lemma d1_positive {u : ℝ} (hu : u∈heights) : 0<d1 u := by
  have hp := sq_nonneg (u-r)
  dsimp [d1,c1,c2,c3,r] at *
  nlinarith [hu.1]

lemma poly_monotone : MonotoneOn poly heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u _ => (poly_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => poly_hasDerivAt u)
    (fun u hu => (d1_positive (Ioo_subset_Icc_self hu)).le)

theorem lower {u : ℝ} (hu : u∈physicalHeights) : poly u<PHeight.eval u := by
  have h3 {x : ℝ} (hx : x∈physicalHeights) : 0≤PHeight.d3 x-c3 := by
    have hm := third_monotone (physical_subset reference_mem) (physical_subset hx) hx.1
    linarith [reference_bounds.2.2.2]
  have hm2 : MonotoneOn (fun x => PHeight.d2 x-d2 x) physicalHeights :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => ((PHeight.d2_hasDerivAt (domain (physical_subset hx))).sub
        (d2_hasDerivAt x)).continuousAt.continuousWithinAt)
      (fun x hx => (PHeight.d2_hasDerivAt (domain (physical_subset (Ioo_subset_Icc_self hx)))).sub
        (d2_hasDerivAt x)) (fun x hx => h3 (Ioo_subset_Icc_self hx))
  have h2 {x : ℝ} (hx : x∈physicalHeights) : 0≤PHeight.d2 x-d2 x := by
    have hh := hm2 reference_mem hx hx.1
    have hr : d2 r=c2 := by simp [d2]
    simp only at hh
    rw [hr] at hh
    linarith [reference_bounds.2.2.1]
  have hm1 : MonotoneOn (fun x => PHeight.d1 x-d1 x) physicalHeights :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => ((PHeight.d1_hasDerivAt (domain (physical_subset hx))).sub
        (d1_hasDerivAt x)).continuousAt.continuousWithinAt)
      (fun x hx => (PHeight.d1_hasDerivAt (domain (physical_subset (Ioo_subset_Icc_self hx)))).sub
        (d1_hasDerivAt x)) (fun x hx => h2 (Ioo_subset_Icc_self hx))
  have h1 {x : ℝ} (hx : x∈physicalHeights) : 0≤PHeight.d1 x-d1 x := by
    have hh := hm1 reference_mem hx hx.1
    have hr : d1 r=c1 := by simp [d1]
    simp only at hh
    rw [hr] at hh
    linarith [reference_bounds.2.1]
  have hm : MonotoneOn (fun x => PHeight.eval x-poly x) physicalHeights :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => ((PHeight.eval_hasDerivAt (domain (physical_subset hx))).sub
        (poly_hasDerivAt x)).continuousAt.continuousWithinAt)
      (fun x hx => (PHeight.eval_hasDerivAt (domain (physical_subset (Ioo_subset_Icc_self hx)))).sub
        (poly_hasDerivAt x)) (fun x hx => h1 (Ioo_subset_Icc_self hx))
  have hh := hm reference_mem hu hu.1
  have hr : poly r=c0 := by simp [poly]
  simp only at hh
  rw [hr] at hh
  linarith [reference_bounds.1]

theorem original_lower {a b u : ℝ} (hs : OuterState a b) (hu : u∈heights) (hcut : u≤a+1/2) :
    poly u< -P b := by
  have ha := actual_height hs
  have hm := poly_monotone hu (physical_subset ha) hcut
  have hh := lower ha
  rw [PHeight_actual hs] at hh
  exact hm.trans_lt hh

end SquaresInCircles.Eight.TableFree.SecondWord.PHeightTaylor
