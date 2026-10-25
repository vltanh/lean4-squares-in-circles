module

public import SquaresInCircles.Eight.Words.Second.Mixed.LHeightGrowth
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy

/-!
# Eight squares: the sharper T envelope on the whole initial physical arc

One tangent parabola at .53362 proves the line through .6.  On the
remaining entire interval to .7, the derivative shape reduces the
minimum of the affine difference to its two endpoints.  The two
additional tangents are also global on the whole concave arc to .6.
-/

section
/-!
## Two increasing scalars for complete mixed quarter families

Both estimates hold on the entire lower half of the quarter window,
with a free label slope.  Their values are bounded only at its actual
left endpoint.  The elementary cotangent comparison retains the
aligned endpoint without division.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedAffine
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

def κ : ℝ := outerAxial-1/2
def first (g φ : ℝ) : ℝ := φ+g*(1/2+Real.cos φ/2-κ*Real.sin φ)
def firstD (g φ : ℝ) : ℝ := 1-g*(Real.sin φ/2+κ*Real.cos φ)
def second (g φ : ℝ) : ℝ := φ+g/2+g*(Real.cos φ-κ)/Real.sin φ
def secondD (g φ : ℝ) : ℝ := 1+g*(κ*Real.cos φ-1)/(Real.sin φ)^2

lemma κ_bounds : (457/500:ℝ)<κ ∧ κ<(183/200:ℝ) := by
  dsimp [κ]
  constructor <;> linarith [fine_outer_endpoint_bounds.1,outer_endpoint_bounds.2.1]

lemma left_mem : Lower lowerAngle := ⟨le_rfl,by dsimp [lowerAngle]; linarith⟩

lemma left_trig :
    (19121/25000:ℝ)<Real.sin lowerAngle ∧ Real.sin lowerAngle<15297/20000 ∧
    (64421/100000:ℝ)<Real.cos lowerAngle ∧ Real.cos lowerAngle<32211/50000 := by
  have hh := PointProducts.trig (show (0:ℝ)≤7/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at hh
  simp only [lowerAngle,Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,
    Real.cos_pi_div_two,one_mul,zero_mul,sub_zero,zero_add]
  exact ⟨by linarith [hh.2.1],by linarith [hh.2.2],
    by linarith [hh.1.1],by linarith [hh.1.2]⟩

lemma first_hasDerivAt (g φ : ℝ) : HasDerivAt (first g) (firstD g φ) φ := by
  exact ((hasDerivAt_id φ).add
    (((((Real.hasDerivAt_cos φ).div_const 2).const_add (1/2)).sub
      ((Real.hasDerivAt_sin φ).const_mul κ)).const_mul g)).congr_deriv
    (by dsimp only [firstD]; ring)

lemma firstD_hasDerivAt (g φ : ℝ) :
    HasDerivAt (firstD g) (g*(κ*Real.sin φ-Real.cos φ/2)) φ := by
  exact ((((Real.hasDerivAt_sin φ).div_const 2).add
    ((Real.hasDerivAt_cos φ).const_mul κ)).const_mul g).const_sub 1 |>.congr_deriv (by ring)

lemma firstD_monotone {g : ℝ} (hg : 0≤g) : MonotoneOn (firstD g) (Icc lowerAngle (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro φ hφ
    exact (firstD_hasDerivAt g φ).continuousAt.continuousWithinAt
  · intro φ hφ
    exact firstD_hasDerivAt g φ
  · intro φ hφ
    have ht := lower_trig (Ioo_subset_Icc_self hφ)
    have hm := mul_le_mul κ_bounds.1.le ht.1.le (by norm_num : (0:ℝ)≤19121/25000)
      (by linarith [κ_bounds.1] : 0≤κ)
    exact mul_nonneg hg (by nlinarith [ht.2.2.2.1])

lemma firstD_left {g : ℝ} (hg : g∈Icc (7/10) (197/200)) : 0<firstD g lowerAngle := by
  have ht := left_trig
  have hc := mul_le_mul κ_bounds.2.le ht.2.2.2.le
    (by linarith [ht.2.2.1] : 0≤Real.cos lowerAngle) (by norm_num : (0:ℝ)≤183/200)
  have hs : Real.sin lowerAngle/2+κ*Real.cos lowerAngle<(487/500:ℝ) := by
    nlinarith [ht.2.1]
  have hm := mul_le_mul hg.2 hs.le
    (by nlinarith [ht.1,ht.2.2.1,κ_bounds.1] : 0≤Real.sin lowerAngle/2+κ*Real.cos lowerAngle)
    (by norm_num : (0:ℝ)≤197/200)
  dsimp [firstD]
  nlinarith

lemma first_lower {g φ : ℝ} (hg : g∈Icc (7/10) (197/200)) (hφ : Lower φ) :
    87079/100000+(61/500)*g<first g φ := by
  have hmono : MonotoneOn (first g) (Icc lowerAngle (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (first_hasDerivAt g x).continuousAt.continuousWithinAt)
      (fun x _ => first_hasDerivAt g x)
      (fun x hx => ((firstD_left hg).trans_le
        (firstD_monotone (by linarith [hg.1]) left_mem (Ioo_subset_Icc_self hx) hx.1.le)).le)
  have ht := left_trig
  have hm := mul_le_mul κ_bounds.2.le ht.2.1.le
    (by linarith [ht.1] : 0≤Real.sin lowerAngle) (by norm_num : (0:ℝ)≤183/200)
  have hbase : (61/500:ℝ)<1/2+Real.cos lowerAngle/2-κ*Real.sin lowerAngle := by
    nlinarith [ht.2.2.1]
  have hp := mul_lt_mul_of_pos_left hbase (by linarith [hg.1] : 0<g)
  have ha : (87079/100000:ℝ)<lowerAngle := by dsimp [lowerAngle]; linarith [pi_hand_enclosure.1]
  have hleft : 87079/100000+(61/500)*g<first g lowerAngle := by
    dsimp [first]
    nlinarith
  exact hleft.trans_le (hmono left_mem hφ hφ.1)

lemma second_hasDerivAt (g : ℝ) {φ : ℝ} (hφ : Lower φ) :
    HasDerivAt (second g) (secondD g φ) φ := by
  have hs : Real.sin φ≠0 := ne_of_gt (by linarith [(lower_trig hφ).1])
  have hh := ((Real.hasDerivAt_cos φ).sub_const κ).div (Real.hasDerivAt_sin φ) hs
  have hn : -Real.sin φ*Real.sin φ-(Real.cos φ-κ)*Real.cos φ=κ*Real.cos φ-1 := by
    linear_combination (-1:ℝ)*Real.sin_sq_add_cos_sq φ
  rw [hn] at hh
  convert ((hasDerivAt_id φ).add_const (g/2)).add (hh.const_mul g) using 1
  · funext x
    simp only [second,id,Pi.add_apply,Pi.div_apply]
    ring
  · dsimp only [secondD]
    try ring

lemma secondD_positive {g φ : ℝ} (hg : g∈Icc (7/10) (197/200)) (hφ : Lower φ) :
    0<secondD g φ := by
  have ht := lower_trig hφ
  have hs : 0<Real.sin φ := by linarith [ht.1]
  have hgκ := mul_le_mul hg.1 κ_bounds.1.le (by norm_num : (0:ℝ)≤457/500)
    (by linarith [hg.1] : 0≤g)
  have hh : 0≤g*κ-Real.cos φ+3/500 := by nlinarith [ht.2.2.2.1]
  have hp := mul_nonneg hh ht.2.2.1
  have hnum : 0<(Real.sin φ)^2+g*(κ*Real.cos φ-1) := by
    nlinarith [Real.sin_sq_add_cos_sq φ,hg.2,Real.cos_le_one φ]
  have he : secondD g φ*(Real.sin φ)^2=(Real.sin φ)^2+g*(κ*Real.cos φ-1) := by
    dsimp [secondD]
    field_simp [hs.ne']
  by_contra hn
  have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (sq_nonneg (Real.sin φ))
  rw [he] at hp
  linarith

lemma second_lower {g φ : ℝ} (hg : g∈Icc (7/10) (197/200)) (hφ : Lower φ) :
    87079/100000+(29/200)*g<second g φ := by
  have hmono : MonotoneOn (second g) (Icc lowerAngle (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => (second_hasDerivAt g hx).continuousAt.continuousWithinAt)
      (fun x hx => second_hasDerivAt g (Ioo_subset_Icc_self hx))
      (fun x hx => (secondD_positive hg (Ioo_subset_Icc_self hx)).le)
  have ht := left_trig
  have hs : 0<Real.sin lowerAngle := by linarith [ht.1]
  have hbase : (29/200:ℝ)<1/2+(Real.cos lowerAngle-κ)/Real.sin lowerAngle := by
    have he := div_mul_cancel₀ (Real.cos lowerAngle-κ) hs.ne'
    by_contra hn
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hs.le
    nlinarith [ht.1,ht.2.2.1,κ_bounds.2]
  have hp := mul_lt_mul_of_pos_left hbase (by linarith [hg.1] : 0<g)
  have ha : (87079/100000:ℝ)<lowerAngle := by dsimp [lowerAngle]; linarith [pi_hand_enclosure.1]
  have hleft : 87079/100000+(29/200)*g<second g lowerAngle := by
    have he : second g lowerAngle=lowerAngle+g*(1/2+(Real.cos lowerAngle-κ)/Real.sin lowerAngle) := by
      dsimp only [second]
      ring
    rw [he]
    linarith
  exact hleft.trans_le (hmono left_mem hφ hφ.1)

lemma cotangent_linear {φ : ℝ} (hφ : Lower φ) :
    (Real.pi/2-φ)*Real.sin φ≤Real.cos φ := by
  have hx := lower_deviation hφ
  have hd (x : ℝ) : HasDerivAt (fun y => Real.sin y-y*Real.cos y) (x*Real.sin x) x :=
    ((Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))).congr_deriv
      (by simp only [id]; ring)
  have hm : MonotoneOn (fun y => Real.sin y-y*Real.cos y) (Icc (0:ℝ) (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => hd x)
      (fun x hx => mul_nonneg hx.1.le (positive_trig (Ioo_subset_Icc_self hx)).2.2.1)
  have hh := hm (by norm_num) hx hx.1
  simp only [Real.sin_zero,Real.cos_zero,zero_mul,sub_zero,Real.sin_sub,Real.cos_sub,
    Real.sin_pi_div_two,Real.cos_pi_div_two,one_mul] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.MixedAffine
end
end
end

section
/-!
## The exact negative P label in height coordinates

The third and fourth derivatives are positive on the whole displayed
radical domain. Actual outer heights lie above 1.399, so Taylor lower
bounds based there apply to every original source point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord
open CommonQuarter CorePairGeometry Arithmetic

def PHeight : HeightLabel := ⟨92374843/250000000,-2363/100000,2211/20000,192359/200000⟩

lemma PHeight_actual {a b : ℝ} (hs : OuterState a b) : PHeight.eval (a+1/2)= -P b := by
  have hc := hs.2.2
  norm_num [Q0] at hc
  rw [HeightLabel.eval,HeightLabel.actual_root hs,
    show P b=PLabel.eval a b from PLabel.outer_actual hs]
  norm_num [PHeight,PLabel,RoleLabel.eval]
  linear_combination (2363/100000)*hc

namespace PHeightBounds
open HeightLabel

def heights : Set ℝ := Icc 1 (383/200)
def physicalHeights : Set ℝ := Icc (1399/1000) (383/200)

lemma physical_subset : physicalHeights⊆heights := fun _ hu => ⟨by linarith [hu.1],hu.2⟩

lemma domain {u : ℝ} (hu : u∈heights) : 0<Q0-u^2 := by
  have hp := pow_le_pow_left₀ (by linarith [hu.1] : 0≤u) hu.2 2
  norm_num [Q0]
  nlinarith

lemma actual_height {a b : ℝ} (hs : OuterState a b) : a+1/2∈physicalHeights := by
  have ha : a∈Icc outerDiagonal outerAxial :=
    ⟨(CommonQuarter.outer_bounds hs).1,(CommonQuarter.outer_bounds hs).2.1⟩
  exact ⟨by linarith [ha.1,fine_outer_endpoint_bounds.2],
    by linarith [ha.2,outer_endpoint_bounds.2.1]⟩

lemma third_positive {u : ℝ} (hu : u∈heights) : 0<PHeight.d3 u := by
  have he := PHeight.d3_mul (domain hu)
  have hr := pow_pos (root_pos (domain hu)) 5
  have hn : 0<PHeight.w*u-PHeight.k*Q0 := by
    norm_num [PHeight,Q0]
    linarith [hu.1]
  have hp := mul_pos (show 0<3*Q0 by norm_num [Q0]) hn
  nlinarith

lemma fourth_positive {u : ℝ} (hu : u∈heights) : 0<PHeight.d4 u := by
  have he := PHeight.fourth_growth_identity (domain hu) 0
  have hn : 0<PHeight.w*u-PHeight.k*Q0 := by
    norm_num [PHeight,Q0]
    linarith [hu.1]
  have h1 := mul_pos (show 0<PHeight.w by norm_num [PHeight]) (domain hu)
  have h2 := mul_pos (show 0<5*u by linarith [hu.1]) hn
  have hp := mul_pos (show 0<3*Q0 by norm_num [Q0]) (add_pos h1 h2)
  have hr := pow_pos (root_pos (domain hu)) 7
  norm_num at he
  nlinarith

lemma second_monotone : MonotoneOn PHeight.d2 heights :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hu => (PHeight.d2_hasDerivAt (domain hu)).continuousAt.continuousWithinAt)
    (fun _ hu => PHeight.d2_hasDerivAt (domain (Ioo_subset_Icc_self hu)))
    (fun _ hu => (third_positive (Ioo_subset_Icc_self hu)).le)

lemma third_monotone : MonotoneOn PHeight.d3 heights :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hu => (PHeight.d3_hasDerivAt (domain hu)).continuousAt.continuousWithinAt)
    (fun _ hu => PHeight.d3_hasDerivAt (domain (Ioo_subset_Icc_self hu)))
    (fun _ hu => (fourth_positive (Ioo_subset_Icc_self hu)).le)

end PHeightBounds
end SquaresInCircles.Eight.SecondWord
end
end
end

section
/-!
## A cubic lower bound at every original physical height

All four Taylor coefficients are rational lower bounds at 1.399.
Positive fourth derivative transfers the third-derivative bound to
the entire physical height interval. The polynomial itself increases
down to height one, allowing later separator comparisons to evaluate
it at a lower contact height without asserting a physical contact.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.PHeightTaylor
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
    (fun _ hu => (d1_positive (Ioo_subset_Icc_self hu)).le)

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

end SquaresInCircles.Eight.SecondWord.PHeightTaylor
end
end
end

section
/-!
## The side quadratic lower bound at original physical heights

The actual outer height is always at least 1.399. On that whole
physical interval the negative P label has curvature above .78.
A single reference at 1.4 proves the rational quadratic minorant,
whose own monotonicity permits lower separator heights down to one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.PHeightQuadratic
open CommonQuarter CorePairGeometry Arithmetic HeightLabel PHeightBounds

def c : ℝ := -158027387/200000000
def p : ℝ := 973417553/1000000000
def k : ℝ := 39/100
def poly (u : ℝ) : ℝ := c+p*(u-7/5)+k*(u-7/5)^2
def d1 (u : ℝ) : ℝ := p+2*k*(u-7/5)

lemma reference_bounds : -(395068467/500000000:ℝ)<PHeight.eval (7/5) ∧
    |PHeight.d1 (7/5)-p|<(1/2500000000:ℝ) := by
  have hu : (7/5:ℝ)∈heights := by norm_num [heights]
  have hr := root_cage (u := (7/5:ℝ))
    (l := (1398427688513/1000000000000:ℝ)) (r := (699213844257/500000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  have hp := root_pos (domain hu)
  have he := PHeight.d1_mul (domain hu)
  constructor
  · norm_num [PHeight,HeightLabel.eval,Q0]
    nlinarith [hr.2]
  · rw [abs_lt]
    constructor
    · apply (mul_lt_mul_iff_left₀ hp).mp
      norm_num [PHeight,p,Q0] at he ⊢
      nlinarith [hr.1,hr.2]
    · apply (mul_lt_mul_iff_left₀ hp).mp
      norm_num [PHeight,p,Q0] at he ⊢
      nlinarith [hr.1,hr.2]

lemma poly_hasDerivAt (u : ℝ) : HasDerivAt poly (d1 u) u := by
  convert ((((hasDerivAt_id u).sub_const (7/5)).const_mul p).const_add c).add
    ((((hasDerivAt_id u).sub_const (7/5)).pow 2).const_mul k) using 1
  · funext x
    simp only [poly,Pi.add_apply,Pi.pow_apply,id]
  · dsimp [d1]
    ring

lemma poly_monotone : MonotoneOn poly heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u _ => (poly_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => poly_hasDerivAt u)
    (fun u hu => by dsimp [d1,p,k]; linarith [hu.1])

theorem lower {u : ℝ} (hu : u∈physicalHeights) : poly u<PHeight.eval u := by
  have hr : (7/5:ℝ)∈physicalHeights := by norm_num [physicalHeights]
  have hcurv {x : ℝ} (hx : x∈physicalHeights) : (39/50:ℝ)≤PHeight.d2 x := by
    have hm := second_monotone (physical_subset PHeightTaylor.reference_mem) (physical_subset hx) hx.1
    have hh := PHeightTaylor.reference_bounds.2.2.1
    dsimp [PHeightTaylor.c2] at hh
    linarith
  have ht := curvature_tangent (f := PHeight.eval) (d := PHeight.d1) (dd := PHeight.d2)
    (κ := (39/50:ℝ)) hu hr
    (fun _ hx => PHeight.eval_hasDerivAt (domain (physical_subset hx)))
    (fun _ hx => PHeight.d1_hasDerivAt (domain (physical_subset hx)))
    (fun _ hx => hcurv hx)
  have hd := abs_lt.mp reference_bounds.2
  have hproduct : -(3/12500000000:ℝ)≤(PHeight.d1 (7/5)-p)*(u-7/5) := by
    by_cases he : 0≤u-7/5
    · have hh := mul_le_mul_of_nonneg_right hd.1.le he
      have huHi : u-7/5≤3/5 := by linarith [hu.2]
      nlinarith
    · have hh := mul_le_mul_of_nonpos_right hd.2.le (not_le.mp he).le
      have huLo : -(3/5:ℝ)≤u-7/5 := by linarith [hu.1]
      nlinarith
  dsimp [poly,c,k]
  nlinarith [reference_bounds.1]

theorem original_lower {a b u : ℝ} (hs : OuterState a b) (hu : u∈heights) (hcut : u≤a+1/2) :
    poly u< -P b := by
  have ha := actual_height hs
  have hm := poly_monotone hu (physical_subset ha) hcut
  have hh := lower ha
  rw [PHeight_actual hs] at hh
  exact hm.trans_lt hh

end SquaresInCircles.Eight.SecondWord.PHeightQuadratic
end
end
end

section
/-!
## Whole-interval curvature bounds for the P height minorant

The endpoint-curve curvature is a cubic polynomial with negative
second derivative, so its two rational endpoint values give a uniform
positive bound. The core-coordinate growth comparison is decreasing
on its entire early height range.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.PHeightTaylor
open CommonQuarter CorePairGeometry Arithmetic PHeightBounds

def mass : ℝ := 112479/100000
def curvature (u : ℝ) : ℝ := d2 u*(mass-(u-1)^2)-d1 u*(u-1)
def curvatureD (u : ℝ) : ℝ := c3*(mass-(u-1)^2)-3*d2 u*(u-1)-d1 u
def curvatureDD (u : ℝ) : ℝ := -5*c3*(u-1)-4*d2 u

lemma d1_monotone : MonotoneOn d1 heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u _ => (d1_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => d1_hasDerivAt u)
    (fun _ hu => (d2_positive (Ioo_subset_Icc_self hu)).le)

lemma curvature_hasDerivAt (u : ℝ) : HasDerivAt curvature (curvatureD u) u := by
  have hJ := (((hasDerivAt_id u).sub_const 1).pow 2).const_sub mass
  convert ((d2_hasDerivAt u).mul hJ).sub
    ((d1_hasDerivAt u).mul ((hasDerivAt_id u).sub_const 1)) using 1
  · funext x
    simp only [curvature,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id]
  · simp only [curvatureD,Pi.pow_apply,id,Nat.cast_ofNat]
    ring

lemma curvatureD_hasDerivAt (u : ℝ) : HasDerivAt curvatureD (curvatureDD u) u := by
  have hJ := (((hasDerivAt_id u).sub_const 1).pow 2).const_sub mass
  convert ((hJ.const_mul c3).sub
    (((d2_hasDerivAt u).mul ((hasDerivAt_id u).sub_const 1)).const_mul 3)).sub
      (d1_hasDerivAt u) using 1
  · funext x
    simp only [curvatureD,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id]
    ring
  · simp only [curvatureDD,d2,id,Nat.cast_ofNat]
    ring

theorem curvature_lower {u : ℝ} (hu : u∈Icc (133/100:ℝ) (17/10)) :
    (1/20:ℝ)<curvature u := by
  have hc : ConcaveOn ℝ (Icc (133/100:ℝ) (17/10)) curvature :=
    concave_of_deriv2 (fun u _ => curvature_hasDerivAt u)
      (fun u _ => curvatureD_hasDerivAt u)
      (fun u hu => by
        have hh := d2_positive (show u∈heights from ⟨by linarith [hu.1],by linarith [hu.2]⟩)
        dsimp [curvatureDD,c3]
        linarith [hu.1])
  exact concave_gt_of_endpoints hc hu
    (by norm_num [curvature,d1,d2,mass,r,c1,c2,c3])
    (by norm_num [curvature,d1,d2,mass,r,c1,c2,c3])

theorem early_growth {u : ℝ} (hu : u∈Icc (7/5:ℝ) (17/10)) :
    d2 u<(27/5)*d1 u-25869/6250 := by
  have hm : AntitoneOn (fun u => d2 u-(27/5)*d1 u) (Icc (7/5:ℝ) (17/10)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun u _ => ((d2_hasDerivAt u).sub ((d1_hasDerivAt u).const_mul (27/5))).continuousAt.continuousWithinAt)
      (fun u _ => (d2_hasDerivAt u).sub ((d1_hasDerivAt u).const_mul (27/5)))
    intro u hu
    dsimp [d2,c2,c3,r]
    linarith [hu.1]
  have hh := hm (show (7/5:ℝ)∈Icc (7/5:ℝ) (17/10) by norm_num) hu hu.1
  have hr : d2 (7/5)-(27/5)*d1 (7/5)< -(25869/6250:ℝ) := by
    norm_num [d1,d2,c1,c2,c3,r]
  linarith

lemma late_bounds {u : ℝ} (hu : u∈Icc (133/100:ℝ) (373/250)) :
    (909/1000:ℝ)<d1 u ∧ 0<d2 u ∧ d2 u<(61/50:ℝ) := by
  have hh := d1_monotone
    (show (133/100:ℝ)∈heights by norm_num [heights])
    (show u∈heights from ⟨by linarith [hu.1],by linarith [hu.2]⟩) hu.1
  have hr : (909/1000:ℝ)<d1 (133/100) := by norm_num [d1,c1,c2,c3,r]
  refine ⟨hr.trans_le hh,d2_positive ⟨by linarith [hu.1],by linarith [hu.2]⟩,?_⟩
  dsimp [d2,c2,c3,r]
  linarith [hu.2]

lemma terminal_bounds {u : ℝ} (hu : u∈Icc (6689/5000:ℝ) (701/500)) :
    (4581/5000:ℝ)<d1 u ∧ d2 u<(493/500:ℝ) := by
  have hh := d1_monotone
    (show (6689/5000:ℝ)∈heights by norm_num [heights])
    (show u∈heights from ⟨by linarith [hu.1],by linarith [hu.2]⟩) hu.1
  have hr : (4581/5000:ℝ)<d1 (6689/5000) := by norm_num [d1,c1,c2,c3,r]
  refine ⟨hr.trans_le hh,?_⟩
  dsimp [d2,c2,c3,r]
  linarith [hu.2]

end SquaresInCircles.Eight.SecondWord.PHeightTaylor
end
end
end

section
/-!
## A single affine upper bound for the actual T label

One tangent parabola controls the concave initial arc.  On the entire
remaining arc the concave derivative of the negative label makes its
minimum an endpoint value.  The result holds on the complete physical
outer circle, without an angular or radial cover.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTEnvelope
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def q : ℝ := 633/1000
def k : ℝ := 1109/10000
def difference (b : ℝ) : ℝ := q*b-T b

lemma half_mem : (1/2:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma half_references : T (1/2)<(21037/50000:ℝ) ∧
    |TLabel.d1 (1/2)-q|<(33/10000:ℝ) := by
  have hr := shifted_chart_reference (outer_domain half_mem)
    (l := (170751281/100000000:ℝ)) (u := (85375641/50000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hd := TLabel.first_chart_reference (outer_domain half_mem)
    (l := (170751281/100000000:ℝ)) (u := (85375641/50000000:ℝ))
    (dlo := (6297/10000:ℝ)) (dhi := (63/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  constructor
  · dsimp [T,RoleLabel.outer,RoleLabel.eval,TLabel]
    dsimp [U] at hr
    nlinarith [hr.1]
  · rw [abs_lt]
    norm_num [q]
    constructor <;> linarith [hd.1,hd.2]

lemma difference_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt difference (q-TLabel.d1 b) b :=
  TLabel.affine_difference_hasDerivAt q (outer_domain hb)

lemma early {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) : -k<difference b := by
  have hdom (x : ℝ) (hx : x∈Icc (0:ℝ) (3/5)) : x∈Icc 0 outerDiagonal :=
    ⟨hx.1,hx.2.trans T_six_mem.2⟩
  have ht := curvature_tangent (f := difference) (d := fun x => q-TLabel.d1 x)
    (dd := fun x => -TLabel.d2 x) (κ := (6/125:ℝ)) hb
    (show (1/2:ℝ)∈Icc (0:ℝ) (3/5) by norm_num)
    (fun x hx => difference_hasDerivAt (hdom x hx))
    (fun x hx => (TLabel.d1_hasDerivAt (outer_domain (hdom x hx))).const_sub q)
    (fun x hx => by
      have hm := T_second_monotone (hdom x hx) T_six_mem hx.2
      linarith [T_six_second.2])
  have hd := abs_lt.mp half_references.2
  have hs : (q-TLabel.d1 (1/2))^2<(33/10000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((6/125)*(b-1/2)+(q-TLabel.d1 (1/2)))
  dsimp [difference,q,k] at *
  nlinarith [half_references.1]

lemma late {b : ℝ} (hb : b∈Icc (3/5:ℝ) outerDiagonal) : -k<difference b := by
  have hdom (x : ℝ) (hx : x∈Icc (3/5:ℝ) outerDiagonal) : x∈Icc 0 outerDiagonal :=
    ⟨by linarith [hx.1],hx.2⟩
  have hm := MinimumCalculus.endpoint_minimum_of_third_nonpos
    (f := difference) (d := fun x => q-TLabel.d1 x)
    (dd := fun x => -TLabel.d2 x) (ddd := fun x => -TLabel.d3 x) hb
    (fun x hx => difference_hasDerivAt (hdom x hx))
    (fun x hx => (TLabel.d1_hasDerivAt (outer_domain (hdom x hx))).const_sub q)
    (fun x hx => (TLabel.d2_hasDerivAt (outer_domain (hdom x hx))).neg)
    (fun x hx => by linarith [T_third_lower (hdom x hx)])
    (by norm_num [q]; linarith [T_six_first.2])
  have hl := early (show (3/5:ℝ)∈Icc (0:ℝ) (3/5) by norm_num)
  have hr : -k<difference outerDiagonal := by
    dsimp [difference,q,k]
    linarith [T_diagonal_upper,diagonal_fine.1]
  exact (lt_min hl hr).trans_le hm

theorem upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : T b<k+q*b := by
  have hh : -k<difference b := by
    by_cases he : b≤3/5
    · exact early ⟨hb.1,he⟩
    · exact late ⟨by linarith,hb.2⟩
  dsimp [difference] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.MixedTEnvelope
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTSmall
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def q : ℝ := 31/50
abbrev k := MixedTEnvelope.k
def reference : ℝ := 26681/50000
def difference (b : ℝ) : ℝ := q*b-T b

lemma reference_mem : reference∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [reference])

lemma reference_bounds : T reference<(441739/1000000:ℝ) ∧
    |TLabel.d1 reference-q|<(1/100000:ℝ) := by
  have hr := shifted_chart_reference (outer_domain reference_mem)
    (l := (16873736087/10000000000:ℝ)) (u := (2109217011/1250000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [reference,W,Q0]) (by norm_num [reference,W,Q0])
  have hd := TLabel.first_chart_reference (outer_domain reference_mem)
    (l := (16873736087/10000000000:ℝ)) (u := (2109217011/1250000000:ℝ))
    (dlo := (61999/100000:ℝ)) (dhi := (62001/100000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [reference,W,Q0]) (by norm_num [reference,W,Q0])
    (by norm_num [reference,TLabel,W,Q0]) (by norm_num [reference,TLabel,W,Q0])
  constructor
  · dsimp [T,RoleLabel.outer,RoleLabel.eval,TLabel,reference]
    dsimp [U,reference] at hr
    nlinarith [hr.1]
  · rw [abs_lt]
    norm_num [q]
    constructor <;> linarith [hd.1,hd.2]

lemma difference_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt difference (q-TLabel.d1 b) b :=
  TLabel.affine_difference_hasDerivAt q (outer_domain hb)

lemma early {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) : -k<difference b := by
  have hdom (x : ℝ) (hx : x∈Icc (0:ℝ) (3/5)) : x∈Icc 0 outerDiagonal :=
    ⟨hx.1,hx.2.trans T_six_mem.2⟩
  have ht := curvature_tangent (f := difference) (d := fun x => q-TLabel.d1 x)
    (dd := fun x => -TLabel.d2 x) (κ := (6/125:ℝ)) hb
    (show reference∈Icc (0:ℝ) (3/5) by norm_num [reference])
    (fun x hx => difference_hasDerivAt (hdom x hx))
    (fun x hx => (TLabel.d1_hasDerivAt (outer_domain (hdom x hx))).const_sub q)
    (fun x hx => by
      have hm := T_second_monotone (hdom x hx) T_six_mem hx.2
      linarith [T_six_second.2])
  have hd := abs_lt.mp reference_bounds.2
  have hs : (q-TLabel.d1 reference)^2<(1/100000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((6/125)*(b-reference)+(q-TLabel.d1 reference))
  have hT := reference_bounds.1
  dsimp [difference,q,k,MixedTEnvelope.k,reference] at *
  nlinarith

lemma seven_mem : (7/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)

lemma seven_value : T (7/10)<(27191/50000:ℝ) := by
  have hh := shifted_chart_reference (outer_domain seven_mem)
    (l := (7867/5000:ℝ)) (u := (3147/2000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  dsimp [U] at hh
  norm_num [T,RoleLabel.outer,RoleLabel.eval,TLabel]
  nlinarith [hh.1]

theorem upper {b : ℝ} (hb : b∈Icc (0:ℝ) (7/10)) : T b<k+q*b := by
  have hdom (x : ℝ) (hx : x∈Icc (3/5:ℝ) (7/10)) : x∈Icc 0 outerDiagonal :=
    ⟨by linarith [hx.1],hx.2.trans seven_mem.2⟩
  have hh : -k<difference b := by
    by_cases he : b≤3/5
    · exact early ⟨hb.1,he⟩
    · have hm := MinimumCalculus.endpoint_minimum_of_third_nonpos
        (f := difference) (d := fun x => q-TLabel.d1 x)
        (dd := fun x => -TLabel.d2 x) (ddd := fun x => -TLabel.d3 x)
        (show b∈Icc (3/5:ℝ) (7/10) from ⟨by linarith,hb.2⟩)
        (fun x hx => difference_hasDerivAt (hdom x hx))
        (fun x hx => (TLabel.d1_hasDerivAt (outer_domain (hdom x hx))).const_sub q)
        (fun x hx => (TLabel.d2_hasDerivAt (outer_domain (hdom x hx))).neg)
        (fun x hx => by linarith [T_third_lower (hdom x hx)])
        (by norm_num [q]; linarith [T_six_first.2])
      have hl := early (show (3/5:ℝ)∈Icc (0:ℝ) (3/5) by norm_num)
      have hr : -k<difference (7/10) := by
        dsimp [difference,q,k,MixedTEnvelope.k]
        linarith [seven_value]
      exact (lt_min hl hr).trans_le hm
  dsimp [difference] at hh
  linarith

lemma concave_second {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) : TLabel.d2 b<0 := by
  have hh := T_second_monotone ⟨hb.1,hb.2.trans T_six_mem.2⟩ T_six_mem hb.2
  linarith [T_six_second.2]

lemma first_tangent_reference :
    (1947/2500:ℝ)<TLabel.d1 (13/50) ∧ TLabel.d1 (13/50)<(779/1000:ℝ) ∧
      T (13/50)<(63573/250000:ℝ) := by
  have hd : (13/50:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hr := shifted_chart_reference (outer_domain hd)
    (l := (182701943/100000000:ℝ)) (u := (45675486/25000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := TLabel.first_chart_reference (outer_domain hd)
    (l := (182701943/100000000:ℝ)) (u := (45675486/25000000:ℝ))
    (dlo := (1947/2500:ℝ)) (dhi := (779/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  refine ⟨hh.1,hh.2,?_⟩
  dsimp [U] at hr
  norm_num [T,RoleLabel.outer,RoleLabel.eval,TLabel]
  nlinarith [hr.1]

theorem first_tangent {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) :
    T b≤13/250+(779/1000)*b := by
  have hh := TLabel.tangent_upper
    (fun x hx => outer_domain (show x∈Icc 0 outerDiagonal from ⟨hx.1,hx.2.trans T_six_mem.2⟩))
    hb (show (13/50:ℝ)∈Icc 0 (3/5) by norm_num) (fun _ hx => (concave_second hx).le)
  change T b≤T (13/50)+TLabel.d1 (13/50)*(b-13/50) at hh
  have hp := mul_le_mul_of_nonneg_right first_tangent_reference.2.1.le hb.1
  nlinarith [first_tangent_reference.1,first_tangent_reference.2.2]

lemma second_tangent_reference :
    (70115079/100000000:ℝ)<TLabel.d1 (9/25) ∧ TLabel.d1 (9/25)<(701151/1000000:ℝ) ∧
      T (9/25)<(328119843/1000000000:ℝ) := by
  have hd : (9/25:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hr := shifted_chart_reference (outer_domain hd)
    (l := (178213355279/100000000000:ℝ)) (u := (2227666941/1250000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := TLabel.first_chart_reference (outer_domain hd)
    (l := (178213355279/100000000000:ℝ)) (u := (2227666941/1250000000:ℝ))
    (dlo := (70115079/100000000:ℝ)) (dhi := (701151/1000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  refine ⟨hh.1,hh.2,?_⟩
  dsimp [U] at hr
  norm_num [T,RoleLabel.outer,RoleLabel.eval,TLabel]
  nlinarith [hr.1]

theorem second_tangent {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) :
    T b≤37853/500000+(701151/1000000)*b := by
  have hh := TLabel.tangent_upper
    (fun x hx => outer_domain (show x∈Icc 0 outerDiagonal from ⟨hx.1,hx.2.trans T_six_mem.2⟩))
    hb (show (9/25:ℝ)∈Icc 0 (3/5) by norm_num) (fun _ hx => (concave_second hx).le)
  change T b≤T (9/25)+TLabel.d1 (9/25)*(b-9/25) at hh
  have hp := mul_le_mul_of_nonneg_right second_tangent_reference.2.1.le hb.1
  nlinarith [second_tangent_reference.1,second_tangent_reference.2.2]

end SquaresInCircles.Eight.SecondWord.MixedTSmall
end
end
end
