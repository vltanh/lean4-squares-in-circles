module

public import SquaresInCircles.Eight.ExactFamily.Coordinates
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Order.Compact

/-!
# Full-domain convexity of the actual five-corner radical chain

Uncompiled draft.  No interval certificate, root cover, or numerical root
bracket is imported.  The proof is the strict convexity of the disk, applied
successively to the four actual circle radicals.  In particular it includes
the two radical endpoints; no differentiability assumption is made there.

`strictConvexOn_defect` proves HUMAN_FIVE_CORNER Lemma 2 directly, on the
entire radical domain.  `minimizer_unique` is the resulting global uniqueness
statement at a fixed tilt.  This does not yet prove uniqueness as tilt varies.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

def upper (q x : ℝ) : ℝ := Real.sqrt (q-x^2)
def lowerRight (q u : ℝ) : ℝ := upper q u
def topRight (q u : ℝ) : ℝ := upper q (2-u)
def topLeft (q u : ℝ) : ℝ := 3-topRight q u
def topHeight (q u : ℝ) : ℝ := upper q (topLeft q u)
def lowerHeight (q u : ℝ) : ℝ := 2-topHeight q u
def lowerLeft (q u : ℝ) : ℝ := upper q (lowerHeight q u)

def firstComponent (q c s u : ℝ) : ℝ :=
  2-c*(lowerRight q u-1)+s*u
def secondComponent (q c s u : ℝ) : ℝ :=
  1+c*lowerHeight q u-s*(lowerLeft q u-1)
def defect (q c s u : ℝ) : ℝ :=
  firstComponent q c s u^2+secondComponent q c s u^2-q

/-- Exactly the real-radical domain of the positive downward-height chart.
The circle equations are consequences of these inequalities, not extra
contact or stationarity hypotheses. -/
structure Domain (q u : ℝ) : Prop where
  height_nonneg : 0 ≤ u
  first_radicand : u^2 ≤ q
  second_radicand : (2-u)^2 ≤ q
  third_radicand : topLeft q u^2 ≤ q
  fourth_radicand : lowerHeight q u^2 ≤ q

theorem upper_nonneg (q x : ℝ) : 0 ≤ upper q x := Real.sqrt_nonneg _

theorem upper_circle {q x : ℝ} (hx : x^2 ≤ q) :
    upper q x^2+x^2=q := by
  dsimp [upper]
  rw [Real.sq_sqrt (sub_nonneg.mpr hx)]
  ring

theorem upper_lt_two {q x : ℝ} (hq : q<4) (hx : x^2 ≤ q) :
    upper q x<2 := by
  nlinarith [upper_circle hx,upper_nonneg q x,sq_nonneg x,sq_nonneg (upper q x-2)]

theorem upper_antitone {q x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    upper q y ≤ upper q x := by
  apply Real.sqrt_le_sqrt
  nlinarith

/-- The elementary variance identity is the only convexity calculation. -/
theorem weighted_square_gap (x y a b : ℝ) (hab : a+b=1) :
    a*x^2+b*y^2-(a*x+b*y)^2=a*b*(x-y)^2 := by
  have hb : b=1-a := by linarith
  rw [hb]
  ring

theorem weighted_square_le (x y : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (a*x+b*y)^2 ≤ a*x^2+b*y^2 := by
  have hn := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y))
  linarith [weighted_square_gap x y a b hab]

theorem square_mono_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x^2 ≤ y^2 := by
  have hp := mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg (le_trans hx hxy) hx)
  nlinarith

theorem square_strict_mono_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x<y) :
    x^2<y^2 := by
  have hp := mul_pos (sub_pos.mpr hxy) (by linarith : 0<y+x)
  nlinarith

theorem disk_chord {q x₀ x₁ y₀ y₁ a b : ℝ}
    (h₀ : x₀^2+y₀^2 ≤ q) (h₁ : x₁^2+y₁^2 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (a*x₀+b*x₁)^2+(a*y₀+b*y₁)^2 ≤ q := by
  calc
    _ ≤ a*(x₀^2+y₀^2)+b*(x₁^2+y₁^2) := by
      nlinarith [weighted_square_le x₀ x₁ ha hb hab,
        weighted_square_le y₀ y₁ ha hb hab]
    _ ≤ a*q+b*q := add_le_add
      (mul_le_mul_of_nonneg_left h₀ ha) (mul_le_mul_of_nonneg_left h₁ hb)
    _ = q := by rw [← add_mul,hab,one_mul]

theorem disk_chord_strict {q x₀ x₁ y₀ y₁ a b : ℝ}
    (h₀ : x₀^2+y₀^2 ≤ q) (h₁ : x₁^2+y₁^2 ≤ q) (hxy : x₀≠x₁)
    (ha : 0<a) (hb : 0<b) (hab : a+b=1) :
    (a*x₀+b*x₁)^2+(a*y₀+b*y₁)^2 < q := by
  have hp : 0<a*b*(x₀-x₁)^2 :=
    mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))
  have hn := mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (y₀-y₁))
  have hx := weighted_square_gap x₀ x₁ a b hab
  have hy := weighted_square_gap y₀ y₁ a b hab
  have hq : a*q+b*q=q := by rw [← add_mul,hab,one_mul]
  have h₀' := mul_le_mul_of_nonneg_left h₀ ha.le
  have h₁' := mul_le_mul_of_nonneg_left h₁ hb.le
  nlinarith

/-- A circle chord lies below the actual positive square-root branch. -/
theorem upper_mix {q x y a b : ℝ} (hx : x^2 ≤ q) (hy : y^2 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (a*x+b*y)^2 ≤ q ∧
      a*upper q x+b*upper q y ≤ upper q (a*x+b*y) := by
  have hd := disk_chord
    (by nlinarith [upper_circle hx] : x^2+upper q x^2 ≤ q)
    (by nlinarith [upper_circle hy] : y^2+upper q y^2 ≤ q) ha hb hab
  have hr : (a*x+b*y)^2 ≤ q := by
    nlinarith [sq_nonneg (a*upper q x+b*upper q y)]
  have hn : 0 ≤ a*upper q x+b*upper q y :=
    add_nonneg (mul_nonneg ha (upper_nonneg q x))
      (mul_nonneg hb (upper_nonneg q y))
  refine ⟨hr,?_⟩
  by_contra! hh
  have hs := square_strict_mono_nonneg (upper_nonneg q (a*x+b*y)) hh
  nlinarith [upper_circle hr]

theorem upper_mix_strict {q x y a b : ℝ} (hx : x^2 ≤ q) (hy : y^2 ≤ q)
    (hxy : x≠y) (ha : 0<a) (hb : 0<b) (hab : a+b=1) :
    a*upper q x+b*upper q y < upper q (a*x+b*y) := by
  have hd := disk_chord_strict
    (by nlinarith [upper_circle hx] : x^2+upper q x^2 ≤ q)
    (by nlinarith [upper_circle hy] : y^2+upper q y^2 ≤ q) hxy ha hb hab
  have hr := (upper_mix hx hy ha.le hb.le hab).1
  have hn : 0 ≤ a*upper q x+b*upper q y :=
    add_nonneg (mul_nonneg ha.le (upper_nonneg q x))
      (mul_nonneg hb.le (upper_nonneg q y))
  by_contra! hh
  have hs := square_mono_nonneg (upper_nonneg q (a*x+b*y)) hh
  nlinarith [upper_circle hr]

theorem Domain.height_lt_two {q u : ℝ} (hu : Domain q u) (hq : q<4) : u<2 := by
  nlinarith [hu.first_radicand,hu.height_nonneg,sq_nonneg (u-2)]

theorem Domain.lowerHeight_pos {q u : ℝ} (hu : Domain q u) (hq : q<4) :
    0<lowerHeight q u := by
  have hh := upper_lt_two hq hu.third_radicand
  dsimp [lowerHeight,topHeight]
  linarith

theorem Domain.topLeft_pos {q u : ℝ} (hu : Domain q u) (hq : q<4) :
    0<topLeft q u := by
  have hh := upper_lt_two hq hu.second_radicand
  dsimp [topLeft,topRight]
  linarith

/-- Successive disk chords prove the complete radical-domain closure and
the two concave outer horizontal coordinates.  There is no box restriction
on either endpoint beyond belonging to the radical domain. -/
theorem mix_domain_and_bounds {q u₀ u₁ a b : ℝ} (hq : q<4)
    (h₀ : Domain q u₀) (h₁ : Domain q u₁)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    Domain q (a*u₀+b*u₁) ∧
    a*lowerRight q u₀+b*lowerRight q u₁ ≤ lowerRight q (a*u₀+b*u₁) ∧
    lowerHeight q (a*u₀+b*u₁) ≤ a*lowerHeight q u₀+b*lowerHeight q u₁ ∧
    a*lowerLeft q u₀+b*lowerLeft q u₁ ≤ lowerLeft q (a*u₀+b*u₁) := by
  have hr := upper_mix h₀.first_radicand h₁.first_radicand ha hb hab
  have hU := upper_mix h₀.second_radicand h₁.second_radicand ha hb hab
  have hlinear : a*(2-u₀)+b*(2-u₁)=2-(a*u₀+b*u₁) := by nlinarith [hab]
  rw [hlinear] at hU
  have hV : topLeft q (a*u₀+b*u₁) ≤ a*topLeft q u₀+b*topLeft q u₁ := by
    dsimp [topLeft,topRight]
    nlinarith [hU.2,hab]
  have hVm : 0 ≤ topLeft q (a*u₀+b*u₁) := by
    have hh := upper_lt_two hq hU.1
    dsimp [topLeft,topRight]
    linarith
  have hY := upper_mix h₀.third_radicand h₁.third_radicand ha hb hab
  have hVrad : topLeft q (a*u₀+b*u₁)^2 ≤ q := by
    exact le_trans (square_mono_nonneg hVm hV) hY.1
  have hYm : a*topHeight q u₀+b*topHeight q u₁ ≤ topHeight q (a*u₀+b*u₁) :=
    le_trans hY.2 (upper_antitone hVm hV)
  have hv : lowerHeight q (a*u₀+b*u₁) ≤
      a*lowerHeight q u₀+b*lowerHeight q u₁ := by
    dsimp [lowerHeight]
    nlinarith [hYm,hab]
  have hvm : 0 ≤ lowerHeight q (a*u₀+b*u₁) := by
    have hh := upper_lt_two hq hVrad
    dsimp [lowerHeight,topHeight]
    linarith
  have hw := upper_mix h₀.fourth_radicand h₁.fourth_radicand ha hb hab
  have hvrad : lowerHeight q (a*u₀+b*u₁)^2 ≤ q := by
    exact le_trans (square_mono_nonneg hvm hv) hw.1
  refine ⟨⟨add_nonneg (mul_nonneg ha h₀.height_nonneg)
    (mul_nonneg hb h₁.height_nonneg),hr.1,hU.1,hVrad,hvrad⟩,hr.2,hv,?_⟩
  exact le_trans hw.2 (upper_antitone hvm hv)

theorem domain_convex {q : ℝ} (hq : q<4) :
    Convex ℝ {u : ℝ | Domain q u} := by
  intro u₀ h₀ u₁ h₁ a b ha hb hab
  simpa only [smul_eq_mul] using (mix_domain_and_bounds hq h₀ h₁ ha hb hab).1

theorem components_pos {q c s u : ℝ} (hq : q<4) (hu : Domain q u)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1) :
    0<firstComponent q c s u ∧ 0<secondComponent q c s u := by
  have hr := upper_lt_two hq hu.first_radicand
  have hw := upper_lt_two hq hu.fourth_radicand
  have hv := hu.lowerHeight_pos hq
  have hcr := mul_pos hc (sub_pos.mpr hr)
  have hsw := mul_nonneg hs (sub_nonneg.mpr hw.le)
  have hcv := mul_pos hc hv
  have hsu' := mul_nonneg hs hu.height_nonneg
  constructor
  · dsimp [firstComponent,lowerRight]
    nlinarith
  · dsimp [secondComponent,lowerLeft]
    nlinarith

theorem firstComponent_mix_strict {q c s u₀ u₁ a b : ℝ}
    (h₀ : Domain q u₀) (h₁ : Domain q u₁) (hu : u₀≠u₁)
    (hc : 0<c) (ha : 0<a) (hb : 0<b) (hab : a+b=1) :
    firstComponent q c s (a*u₀+b*u₁) <
      a*firstComponent q c s u₀+b*firstComponent q c s u₁ := by
  have hr := upper_mix_strict h₀.first_radicand h₁.first_radicand hu ha hb hab
  have hcr := mul_lt_mul_of_pos_left hr hc
  have hbase : a*(2+c)+b*(2+c)=2+c := by rw [← add_mul,hab,one_mul]
  dsimp [firstComponent,lowerRight]
  nlinarith

theorem secondComponent_mix {q c s u₀ u₁ a b : ℝ} (hq : q<4)
    (h₀ : Domain q u₀) (h₁ : Domain q u₁)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    secondComponent q c s (a*u₀+b*u₁) ≤
      a*secondComponent q c s u₀+b*secondComponent q c s u₁ := by
  obtain ⟨_,_,hv,hw⟩ := mix_domain_and_bounds hq h₀ h₁ ha hb hab
  have hcv := mul_le_mul_of_nonneg_left hv hc
  have hsw := mul_le_mul_of_nonneg_left hw hs
  have hbase : a*(1+s)+b*(1+s)=1+s := by rw [← add_mul,hab,one_mul]
  dsimp [secondComponent]
  nlinarith

/-- Full-domain strict Jensen inequality for the actual nested radical
formula.  It remains valid for every `0<c≤1`, `0≤s≤1`; unit-circle tilt
coordinates are a special case. -/
theorem defect_mix_strict {q c s u₀ u₁ a b : ℝ} (hq : q<4)
    (h₀ : Domain q u₀) (h₁ : Domain q u₁) (hu : u₀≠u₁)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1)
    (ha : 0<a) (hb : 0<b) (hab : a+b=1) :
    defect q c s (a*u₀+b*u₁) < a*defect q c s u₀+b*defect q c s u₁ := by
  have hm := (mix_domain_and_bounds hq h₀ h₁ ha.le hb.le hab).1
  have hp := components_pos hq hm hc hcu hs hsu
  have h₁m := firstComponent_mix_strict h₀ h₁ hu hc ha hb hab
  have h₂m := secondComponent_mix hq h₀ h₁ hc.le hs ha.le hb.le hab
  have h₁sq : firstComponent q c s (a*u₀+b*u₁)^2 <
      (a*firstComponent q c s u₀+b*firstComponent q c s u₁)^2 := by
    exact square_strict_mono_nonneg hp.1.le h₁m
  have h₂sq : secondComponent q c s (a*u₀+b*u₁)^2 ≤
      (a*secondComponent q c s u₀+b*secondComponent q c s u₁)^2 := by
    exact square_mono_nonneg hp.2.le h₂m
  have hJ₁ := weighted_square_le
    (firstComponent q c s u₀) (firstComponent q c s u₁) ha.le hb.le hab
  have hJ₂ := weighted_square_le
    (secondComponent q c s u₀) (secondComponent q c s u₁) ha.le hb.le hab
  have hqsum : a*q+b*q=q := by rw [← add_mul,hab,one_mul]
  dsimp [defect]
  nlinarith

/-- HUMAN_FIVE_CORNER Lemma 2 on the complete radical domain, including
its endpoints, proved entirely from circle geometry. -/
theorem strictConvexOn_defect {q c s : ℝ} (hq : q<4)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1) :
    StrictConvexOn ℝ {u : ℝ | Domain q u} (defect q c s) := by
  refine ⟨domain_convex hq,?_⟩
  intro u₀ h₀ u₁ h₁ hu a b ha hb hab
  simpa only [smul_eq_mul] using defect_mix_strict hq h₀ h₁ hu
    hc hcu hs hsu ha hb hab

theorem strictConvexOn_halfAngle {q z : ℝ} (hq : q<4)
    (hz : 0 ≤ z) (hzu : z<1) :
    StrictConvexOn ℝ {u : ℝ | Domain q u}
      (defect q (halfAngleCos z) (halfAngleSin z)) := by
  apply strictConvexOn_defect hq
  · apply halfAngleCos_pos
    rw [abs_lt]
    constructor <;> linarith
  · exact halfAngleCos_le_one z
  · dsimp [halfAngleSin]
    exact div_nonneg (by linarith) (halfAngle_den_pos z).le
  · rw [halfAngleSin,div_le_iff₀ (halfAngle_den_pos z)]
    nlinarith [sq_nonneg (z-1)]

/-- Fixed-tilt minimizers in the full domain agree; no local root box
or second-derivative bound occurs in the hypotheses. -/
theorem minimizer_unique {q c s u₀ u₁ : ℝ} (hq : q<4)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1)
    (h₀ : Domain q u₀) (h₁ : Domain q u₁)
    (hm₀ : ∀ u, Domain q u → defect q c s u₀ ≤ defect q c s u)
    (hm₁ : ∀ u, Domain q u → defect q c s u₁ ≤ defect q c s u) : u₀=u₁ := by
  by_contra hu
  have hm := (mix_domain_and_bounds hq h₀ h₁
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).1
  have hj := defect_mix_strict hq h₀ h₁ hu hc hcu hs hsu
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2) (by norm_num)
  have hL := hm₀ _ hm
  have hR := hm₁ _ hm
  linarith

theorem domain_iff (q u : ℝ) : Domain q u ↔
    0 ≤ u ∧ u^2 ≤ q ∧ (2-u)^2 ≤ q ∧
      topLeft q u^2 ≤ q ∧ lowerHeight q u^2 ≤ q := by
  constructor
  · intro h
    exact ⟨h.height_nonneg,h.first_radicand,h.second_radicand,
      h.third_radicand,h.fourth_radicand⟩
  · rintro ⟨h₀,h₁,h₂,h₃,h₄⟩
    exact ⟨h₀,h₁,h₂,h₃,h₄⟩

theorem domain_closed (q : ℝ) : IsClosed {u : ℝ | Domain q u} := by
  have h₀ : IsClosed {u : ℝ | 0 ≤ u} := isClosed_le continuous_const continuous_id
  have h₁ : IsClosed {u : ℝ | u^2 ≤ q} := isClosed_le (by fun_prop) continuous_const
  have h₂ : IsClosed {u : ℝ | (2-u)^2 ≤ q} := isClosed_le (by fun_prop) continuous_const
  have h₃ : IsClosed {u : ℝ | topLeft q u^2 ≤ q} := by
    apply isClosed_le _ continuous_const
    dsimp [topLeft,topRight,upper]
    fun_prop
  have h₄ : IsClosed {u : ℝ | lowerHeight q u^2 ≤ q} := by
    apply isClosed_le _ continuous_const
    dsimp [lowerHeight,topHeight,topLeft,topRight,upper]
    fun_prop
  convert h₀.inter (h₁.inter (h₂.inter (h₃.inter h₄))) using 1
  ext u
  simp only [Set.mem_inter_iff,Set.mem_setOf_eq,domain_iff]

theorem domain_compact {q : ℝ} (hq : q<4) : IsCompact {u : ℝ | Domain q u} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 2)).of_isClosed_subset (domain_closed q)
  intro u hu
  exact ⟨hu.height_nonneg,(hu.height_lt_two hq).le⟩

theorem defect_continuous (q c s : ℝ) : Continuous (defect q c s) := by
  dsimp [defect,firstComponent,secondComponent,lowerRight,lowerLeft,
    lowerHeight,topHeight,topLeft,topRight,upper]
  fun_prop

/-- The symmetric chain proves nonemptiness throughout the entire radius
range in HUMAN_FIVE_CORNER Lemma 1, including its degenerate endpoint. -/
theorem domain_nonempty {q : ℝ} (hql : (25/16:ℝ)^2 ≤ q) (hqu : q<4) :
    Set.Nonempty {u : ℝ | Domain q u} := by
  let H := Real.sqrt (q-9/4)
  have hrad : 0 ≤ q-9/4 := by nlinarith
  have hH : H^2=q-9/4 := Real.sq_sqrt hrad
  have hHn : 0 ≤ H := Real.sqrt_nonneg _
  have hHl : 7/16 ≤ H := by nlinarith
  have hHu : H<2 := by nlinarith
  have hU : topRight q (2-H)=3/2 := by
    have he : q-(2-(2-H))^2=(3/2:ℝ)^2 := by nlinarith
    dsimp [topRight,upper]
    rw [he,Real.sqrt_sq_eq_abs]
    norm_num
  have hV : topLeft q (2-H)=3/2 := by rw [topLeft,hU]; norm_num
  have hv : lowerHeight q (2-H)=2-H := by
    rw [lowerHeight,topHeight,hV]
    norm_num [upper,H]
  refine ⟨2-H,⟨by linarith,?_,?_,?_,?_⟩⟩
  · nlinarith
  · nlinarith
  · rw [hV]
    nlinarith
  · rw [hv]
    nlinarith

theorem existsUnique_minimizer {q c s : ℝ} (hql : (25/16:ℝ)^2 ≤ q) (hqu : q<4)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1) :
    ∃! u, Domain q u ∧ ∀ v, Domain q v → defect q c s u ≤ defect q c s v := by
  obtain ⟨u,hu,hm⟩ := (domain_compact hqu).exists_isMinOn
    (domain_nonempty hql hqu) (defect_continuous q c s).continuousOn
  have hmin : ∀ v, Domain q v → defect q c s u ≤ defect q c s v := by
    intro v hv
    exact hm hv
  refine ⟨u,⟨hu,hmin⟩,?_⟩
  rintro v ⟨hv,hvm⟩
  exact minimizer_unique hqu hc hcu hs hsu hv hu hvm hmin

/-- The geometric chart is the already existing `Coordinates` chain, with
the change of variable `u=-y`; these are exact identities. -/
theorem coordinate_values {d : Coordinates} (hd : d.IsChain) :
    lowerRight d.q (-d.y)=d.x₁ ∧ topRight d.q (-d.y)=d.x₂ ∧
    topLeft d.q (-d.y)= -d.x₃ ∧ topHeight d.q (-d.y)=d.y₃ ∧
    lowerHeight d.q (-d.y)= -d.y₄ ∧ lowerLeft d.q (-d.y)= -d.x₄ := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hd.radicals
  have hr : lowerRight d.q (-d.y)=d.x₁ := by
    simpa [lowerRight,upper,sq_neg] using h₁.symm
  have hU : topRight d.q (-d.y)=d.x₂ := by
    dsimp [topRight,upper]
    convert h₂.symm using 1 <;> congr 1 <;> ring
  have hV : topLeft d.q (-d.y)= -d.x₃ := by
    rw [topLeft,hU]
    dsimp [Coordinates.x₃]
    ring
  have hY : topHeight d.q (-d.y)=d.y₃ := by
    rw [topHeight,hV]
    simpa [upper,sq_neg] using h₃.symm
  have hv : lowerHeight d.q (-d.y)= -d.y₄ := by
    rw [lowerHeight,hY]
    dsimp [Coordinates.y₄]
    ring
  have hw : lowerLeft d.q (-d.y)= -d.x₄ := by
    rw [lowerLeft,hv]
    dsimp [upper]
    rw [sq_neg,h₄]
    ring
  exact ⟨hr,hU,hV,hY,hv,hw⟩

theorem coordinate_domain {d : Coordinates} (hd : d.IsChain) (hy : d.y ≤ 0) :
    Domain d.q (-d.y) := by
  obtain ⟨_,_,hV,_,hv,_⟩ := coordinate_values hd
  refine ⟨by linarith,?_,?_,?_,?_⟩
  · nlinarith [hd.first_circle,sq_nonneg d.x₁]
  · nlinarith [hd.second_circle,sq_nonneg d.x₂]
  · rw [hV,sq_neg]
    nlinarith [hd.third_circle,sq_nonneg d.y₃]
  · rw [hv,sq_neg]
    nlinarith [hd.fourth_circle,sq_nonneg d.x₄]

theorem coordinate_defect {d : Coordinates} (hd : d.IsChain) :
    defect d.q d.c d.s (-d.y)=d.defect := by
  obtain ⟨hr,_,_,_,hv,hw⟩ := coordinate_values hd
  have h₁ : firstComponent d.q d.c d.s (-d.y)= -d.h₁ := by
    rw [firstComponent,hr]
    dsimp [Coordinates.h₁]
    ring
  have h₂ : secondComponent d.q d.c d.s (-d.y)= -d.h₂ := by
    rw [secondComponent,hv,hw]
    dsimp [Coordinates.h₂]
    ring
  rw [defect,h₁,h₂,Coordinates.defect]
  ring

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry
