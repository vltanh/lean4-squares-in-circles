import SquaresInCircles.Three.Exterior
import SquaresInCircles.Common.ArcMetric
import SquaresInCircles.Common.ElementaryTrig
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Three squares: the containing square

A square that contains the disk centre holds an arc of the circle of radius
`3/8` less than `1/12` short of 120 degrees, and the other two squares hold caps
of at least 120 degrees. A clipped cap would make up more than that deficit, so
both caps are full and nearly axial. On the circle of radius `7/16` two nearly
axial squares hold arcs too wide for the angle between their phases, which the
budget on the circle of radius `3/8` keeps below `2π/3+1/12`.
-/
noncomputable section
open Set
namespace SquaresInCircles.Three

/-! ## The arc of the containing square and the radial gap -/

/-- Between the chart angles `-arcsin Q` and `π/2+arcsin P` the sine exceeds
`-Q`. -/
lemma neg_lt_sin {P Q t : ℝ} (hQ : 0 < Q) (h₁ : -Real.arcsin Q < t)
    (h₂ : t < Real.pi/2+Real.arcsin P) : -Q < Real.sin t := by
  by_cases ht : t ≤ Real.pi/2
  · rw [← Real.arcsin_neg] at h₁
    exact (Real.arcsin_lt_iff_lt_sin' ⟨by linarith [Real.neg_pi_div_two_le_arcsin (-Q)],ht⟩).mp h₁
  · have := Real.sin_pos_of_pos_of_lt_pi (x := t) (by linarith [Real.pi_pos])
      (by linarith [Real.arcsin_le_pi_div_two P])
    linarith

/-- On the circle of radius `3/8` about a point of the square centred at
`(a, b)`, `0 ≤ a, b < 1/2`, the far edges are out of reach, and every chart angle
from `-capV b` to `π/2+capV a` lies in the square. -/
lemma containing_mem {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a < 1/2) (hb1 : b < 1/2)
    (ht : t ∈ Ioo (-capV aux b) (Real.pi/2+capV aux a)) :
    |aux*Real.cos t-a| < 1/2 ∧ |aux*Real.sin t-b| < 1/2 := by
  unfold capV at ht
  rw [aux] at ht ⊢
  have hs := neg_lt_sin (by linarith) ht.1 ht.2
  have hc := neg_lt_sin (P := (1/2-b)/(3/8)) (Q := (1/2-a)/(3/8)) (t := Real.pi/2-t)
    (by linarith) (by linarith [ht.2]) (by linarith [ht.1])
  rw [Real.sin_pi_div_two_sub] at hc
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith [Real.cos_le_one t]⟩,
    abs_lt.mpr ⟨by linarith,by linarith [Real.sin_le_one t]⟩⟩

/-- The arc of a containing square, of length `π/2+capV a+capV b`. -/
lemma containing_arc {S : UnitSquare} {o : Point} (C : SquareChart S o) (ho : openSquare S o) :
    ∃ W : OpenArc o aux {p | openSquare S p},
      2*W.halfWidth=Real.pi/2+capV aux C.a+capV aux C.b := by
  have hc := C.origin.mp ho
  have hV (x : ℝ) (hx : x < 1/2) : 0 ≤ capV aux x ∧ capV aux x ≤ Real.pi/2 :=
    ⟨Real.arcsin_nonneg.mpr (by rw [aux]; linarith),Real.arcsin_le_pi_div_two _⟩
  have ha := hV C.a hc.1
  have hb := hV C.b hc.2
  obtain ⟨W,hw,-⟩ := C.arc aux (-capV aux C.b) (Real.pi/2+capV aux C.a)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    fun t ht => containing_mem C.nonneg.1 C.nonneg.2 hc.1 hc.2 ht
  exact ⟨W,by rw [hw]; ring⟩

/-- The radial gap: a containing square holds every circle about `o` of radius
below `1/2-a`, so a disjoint exterior square cannot reach one. -/
lemma gap_from_containing {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o) (hsort : C.b ≤ C.a) (ho : openSquare S o)
    (hDa : 1/2 ≤ D.a) (hDb : D.b ≤ 1/2)
    (hST : Disjoint {p | openSquare S p} {p | openSquare T p}) :
    1/2-C.a ≤ D.a-1/2 := by
  by_contra hn
  push Not at hn
  have hc := C.origin.mp ho
  have hr : 0 < (D.a-C.a)/2 := by linarith
  obtain ⟨A,hA,-⟩ := C.arc ((D.a-C.a)/2) (-Real.pi) Real.pi (by linarith [Real.pi_pos])
    (by linarith) fun t _ => by
      have h₁ := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hr.le
      have h₂ := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos t) hr.le
      have h₃ := mul_le_mul_of_nonneg_left (Real.sin_le_one t) hr.le
      have h₄ := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin t) hr.le
      exact ⟨abs_lt.mpr ⟨by linarith,by linarith [C.nonneg.1]⟩,
        abs_lt.mpr ⟨by linarith,by linarith [C.nonneg.2]⟩⟩
  obtain ⟨B,-,-⟩ := D.cap_arc hr (by linarith [C.nonneg.1]) hDa (by linarith) hDb
  have h := A.centers_separated B hST
  rw [hA] at h
  linarith [direction_diameter A.center B.center,B.positive]

/-! ## Compensation and the deficit -/

/-- `arcsin (1/2+16t/13) - arcsin t` increases while `1/2+16t/13 < 1`. -/
lemma asin_increment_mono {P u : ℝ} (hP : 0 ≤ P) (hPu : P ≤ u) (htop : 1/2+16/13*u < 1) :
    Real.arcsin (1/2+16/13*P)-Real.arcsin P ≤ Real.arcsin (1/2+16/13*u)-Real.arcsin u := by
  refine (strictMonoOn_of_deriv_pos (f := fun t => Real.arcsin (1/2+16/13*t)-Real.arcsin t)
    (convex_Icc P u) (by fun_prop) fun t ht => ?_).monotoneOn
    ⟨le_rfl,hPu⟩ ⟨hPu,le_rfl⟩ hPu
  rw [interior_Icc] at ht
  have h1 : 1/2+16/13*t < 1 := by linarith [ht.2]
  have hd : HasDerivAt (fun t => Real.arcsin (1/2+16/13*t)-Real.arcsin t)
      (1/√(1-(1/2+16/13*t)^2)*(16/13)-1/√(1-t^2)) t := by
    have hg : HasDerivAt (fun z : ℝ => 1/2+16/13*z) (16/13) t :=
      (((hasDerivAt_id' t).const_mul (16/13:ℝ)).const_add (1/2:ℝ)).congr_deriv (by ring)
    exact ((Real.hasDerivAt_arcsin (by linarith [ht.1]) h1.ne).comp t hg).sub
      (Real.hasDerivAt_arcsin (by linarith [ht.1]) (by linarith [ht.1]))
  rw [hd.deriv]
  have hs0 : 0 < √(1-(1/2+16/13*t)^2) := Real.sqrt_pos.2 (by nlinarith [ht.1])
  have hs := one_div_lt_one_div_of_lt hs0 (Real.sqrt_lt_sqrt (by nlinarith [ht.1])
    (show 1-(1/2+16/13*t)^2 < 1-t^2 by nlinarith [ht.1]))
  have := one_div_pos.mpr hs0
  linarith

/-- A clipped cap and the arc of the containing square together exceed 240
degrees: `arcsin v - arcsin u` makes up the deficit `π/6 - arcsin P - arcsin Q`. -/
lemma compensation {P Q u v : ℝ} (hP : 0 ≤ P) (hQ : Q ∈ Icc (0:ℝ) 1)
    (hcentral : 1/2 < 16/13*P+Q) (hPu : P ≤ u) (hv : 1/2+16/13*u ≤ v) (hv1 : v < 1) :
    Real.pi/3 < Real.arcsin v-Real.arcsin u+Real.arcsin P+Real.arcsin Q := by
  have hinc := asin_increment_mono hP hPu (by linarith)
  have hvmono := Real.arcsin_le_arcsin hv
  have hpair := arcsin_sum_gt_of_sin_lt (show 1/2+16/13*P ∈ Icc (0:ℝ) 1 by
    constructor <;> linarith) hQ
    (show Real.pi/6 ∈ Icc (0:ℝ) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
    (by rw [Real.sin_pi_div_six]; linarith)
  linarith

/-! ## Nearly axial squares -/

/-- `cos (π/3+1/24) > 9/20`. -/
lemma cos_third_gt : (9:ℝ)/20 < Real.cos (Real.pi/3+1/24) := by
  rw [Real.cos_add,Real.cos_pi_div_three]
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/24)
  have hs := Real.sin_le (show (0:ℝ) ≤ 1/24 by norm_num)
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi (show (0:ℝ) ≤ 1/24 by norm_num)
    (by linarith [Real.pi_gt_three])
  nlinarith [Real.sin_le_one (Real.pi/3)]

/-- On the circle of radius `7/16` a nearly axial square holds an arc of
half-width more than `π/3+1/24` centred on its phase. -/
lemma wide_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (h : 1/2 ≤ C.a ∧ C.a ≤ 11/16 ∧ C.b ≤ 1/16) :
    ∃ W : OpenArc o (7/16) {p | openSquare S p},
      Real.pi/3+1/24 < W.halfWidth ∧ W.center=C.phase := by
  have hA : Real.pi/3+1/24 < capA (7/16) C.a := by
    calc Real.pi/3+1/24=Real.arccos (Real.cos (Real.pi/3+1/24)) :=
          (Real.arccos_cos (by positivity) (by linarith [Real.pi_gt_three])).symm
      _ < capA (7/16) C.a := Real.arccos_lt_arccos (by linarith [h.1])
          (by linarith [h.2.1,cos_third_gt]) (Real.cos_le_one _)
  have hV : capV (7/16) C.b=Real.pi/2 :=
    Real.arcsin_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith [h.2.2])
  have hA2 : capA (7/16) C.a ≤ Real.pi/2 := Real.arccos_le_pi_div_two.mpr (by linarith [h.1])
  obtain ⟨W,hw,hc⟩ := C.full_cap_arc (by norm_num) (by norm_num) h.1 (by linarith [h.2.1])
    (by linarith [h.2.2]) (hA2.trans_eq hV.symm)
  exact ⟨W,by rw [hw]; exact hA,hc⟩

/-- Two nearly axial squares whose phases are less than `2π/3+1/12` apart
overlap. -/
lemma axial_pair_impossible {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hC : 1/2 ≤ C.a ∧ C.a ≤ 11/16 ∧ C.b ≤ 1/16) (hD : 1/2 ≤ D.a ∧ D.a ≤ 11/16 ∧ D.b ≤ 1/16)
    (hST : Disjoint {p | openSquare S p} {p | openSquare T p})
    (h : dist C.phase D.phase < 2*Real.pi/3+1/12) : False := by
  obtain ⟨A,hA,hAc⟩ := wide_arc C hC
  obtain ⟨B,hB,hBc⟩ := wide_arc D hD
  have hsep := A.centers_separated B hST
  rw [hAc,hBc] at hsep
  linarith

/-! ## The containing case -/

/-- A square that contains the disk centre leaves too little room for the
other two. -/
theorem no_containing (S : Fin 3 → UnitSquare) (o : Point) (hd : InteriorDisjoint S)
    (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ 425/256) (i : Fin 3) :
    ¬ openSquare (S i) o := by
  intro ho
  obtain ⟨j,k,hij,hik,hjk⟩ : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    fin_cases i <;> decide
  choose C hsort using fun l => sorted_square_chart (S l) o
  have hP (l : Fin 3) : P3 (C l).a (C l).b := p3_of_phi (chart_phi (C l) (hφ l))
  have hin := (C i).origin.mp ho
  have hcentral : 16*(C i).a+13*(C i).b < 193/16 := by
    linarith [tangent_lt (u := 1/2) (v := 5/16) (chart_phi (C i) (hφ i)) (by norm_num [phi])
      hin.1.ne]
  have hext (l : Fin 3) (hl : i ≠ l) : 1/2 ≤ (C l).a :=
    (C l).exterior (hsort l) fun h => hd i l hl o ⟨ho,h⟩
  have hbd (l : Fin 3) (hl : i ≠ l) := cap_bounds (hext l hl) (C l).nonneg.2 (hP l)
  obtain ⟨W,hW⟩ := containing_arc (C i) ho
  obtain ⟨B,hB,hBc,hBlo⟩ := exterior_cap (C j) (hext j hij) (hP j)
  obtain ⟨G,hG,hGc,hGlo⟩ := exterior_cap (C k) (hext k hik) (hP k)
  have hbudget := triple_arc_budget W B G (hd.pairwise hij) (hd.pairwise hik) (hd.pairwise hjk)
  -- the deficit of the containing arc
  have hP0 : 0 ≤ (1/2-(C i).a)/aux := by rw [aux]; linarith
  have hQ0 : 0 ≤ (1/2-(C i).b)/aux := by rw [aux]; linarith
  have hQ1 : (1/2-(C i).b)/aux < 1 := by
    refine Real.arcsin_lt_pi_div_two.mp ?_
    unfold capV at hW
    linarith [Real.arcsin_nonneg.mpr hP0,Real.pi_pos]
  have hdef : 2*Real.pi/3-1/12 < 2*W.halfWidth := by
    have hPQ : (1/2-(C i).a)/aux ≤ (1/2-(C i).b)/aux := by rw [aux]; linarith [hsort i]
    have h₁ := arcsin_ge_self hP0 (hPQ.trans hQ1.le)
    have h₂ := arcsin_ge_self hQ0 hQ1.le
    rw [hW]
    unfold capV
    rw [aux] at h₁ h₂ ⊢
    linarith [pi_lt_22_over_7,hsort i]
  -- each other square has a full, nearly axial cap
  have haxial (l : Fin 3) (hl : i ≠ l) (X : OpenArc o aux {p | openSquare (S l) p})
      (hX : X.halfWidth=(capA aux (C l).a+min (capA aux (C l).a) (capV aux (C l).b))/2)
      (hXW : X.halfWidth+W.halfWidth ≤ 2*Real.pi/3) :
      capA aux (C l).a ≤ capV aux (C l).b ∧ 1/2 ≤ (C l).a ∧ (C l).a ≤ 11/16 ∧ (C l).b ≤ 1/16 := by
    obtain ⟨hA,hAπ,-,-,-⟩ := hbd l hl
    have ha := hext l hl
    have hb := (C l).nonneg.2
    have hgap := gap_from_containing (C i) (C l) (hsort i) ho ha (by linarith [(hP l).1])
      (hd.pairwise hl)
    have hfull : capA aux (C l).a ≤ capV aux (C l).b := by
      refine le_of_not_gt fun hclip => ?_
      have hcomp := compensation (P := (1/2-(C i).a)/aux) (Q := (1/2-(C i).b)/aux)
        (u := ((C l).a-1/2)/aux) (v := (1/2-(C l).b)/aux) hP0
        ⟨hQ0,hQ1.le⟩ (by rw [aux]; linarith) (by rw [aux]; linarith)
        (by rw [aux]; linarith [(hP l).1])
        (Real.arcsin_lt_pi_div_two.mp (hclip.trans_le hAπ))
      rw [min_eq_right hclip.le] at hX
      unfold capA capV at hX
      unfold capV at hW
      rw [Real.arccos_eq_pi_div_two_sub_arcsin] at hX
      linarith
    rw [min_eq_left hfull] at hX
    have hu := Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _)
      (by linarith [Real.pi_gt_three]) (show capA aux (C l).a < Real.pi/3+1/24 by linarith)
    rw [Real.cos_arccos (x := ((C l).a-1/2)/aux) (by rw [aux]; linarith)
      (by rw [aux]; linarith [(hP l).2]),aux] at hu
    have := cos_third_gt
    exact ⟨hfull,ha,by linarith [(hP l).2],by linarith [(hP l).2]⟩
  obtain ⟨hBf,hBa⟩ := haxial j hij B hB (by linarith)
  obtain ⟨hGf,hGa⟩ := haxial k hik G hG (by linarith)
  have hdist := (W.third_distance_bounds B G (hd.pairwise hij) (hd.pairwise hik)
    (hd.pairwise hjk)).2
  rw [hBc,hGc,min_eq_left hBf,min_eq_left hGf] at hdist
  simp only [sub_self,zero_div,chartAngle,neg_zero,ite_self,Real.Angle.coe_zero,add_zero] at hdist
  exact axial_pair_impossible (C j) (C k) hBa hGa (hd.pairwise hjk) (by linarith)

end SquaresInCircles.Three
