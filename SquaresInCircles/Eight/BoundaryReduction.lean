module

public import SquaresInCircles.Eight.SeparatingAxis
public import SquaresInCircles.Eight.Frames
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Eight squares: the boundary reduction

A neighbour cycle at a level `q ≤ Q0`, with its centre directions in cyclic order, is moved to a
boundary cycle with the same frames and the same witnesses (`boundary_reduction_exists`). The
squares are moved one at a time by translations. The witnesses on the two edges of the moving
square are two closed half-planes for its centre, and the centre moves along a direction common
to both (`two_halfplanes_recession`), so both witnesses keep separating; only these two
separations are claimed, with their original signed normals. The motion stops at the first
contact with the circle or with the core disk (`first_two_boundary_contact`), which exists
because the centres of the squares in the disk form a bounded set (`ray_leaves_containment`).

The centres stay in the annulus `7/12 ≤ r < 71/50` (`annular_center_radius_lower`,
`annular_center_radius_upper`), where two centres at least `1` apart have directions more than
`3/5` apart (`annular_angle_lower`). Along the motion the centre direction moves continuously
(`straight_line_polar_lift`), so the cyclic order and the gaps below `π` are kept
(`VertexMotion.polarOrder`). Finally each square is given the quarter turn of a canonical frame,
and its witness is transported to that representative (`canonicalBoundaryCycle`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace SquaresInCircles.Eight

lemma normSq_scale (t : ℝ) (p : Point) : normSq (scale t p) = t^2 * normSq p := by
  dsimp [normSq, scale]
  ring

lemma coreDistanceSq_attained (K : UnitSquare) :
    ∃ p, closedSquare K p ∧ normSq p = coreDistanceSq K := by
  obtain ⟨p, hp, he⟩ := exists_clipped_point K (0, 0)
  exact ⟨p, hp, by simpa [coreDistanceSq, sub] using he⟩

lemma coreDistanceSq_le {K : UnitSquare} {p : Point} (hp : closedSquare K p) :
    coreDistanceSq K ≤ normSq p := by
  have hx : max (alpha K (0, 0) - 1/2) 0 ≤ |frameX K p| := by
    apply max_le _ (abs_nonneg _)
    have he : localX K (0, 0) = localX K p - frameX K p := by
      dsimp [localX, frameX]
      ring
    have h := abs_sub (localX K p) (frameX K p)
    rw [← he] at h
    dsimp [alpha]
    linarith [hp.1]
  have hy : max (beta K (0, 0) - 1/2) 0 ≤ |frameY K p| := by
    apply max_le _ (abs_nonneg _)
    have he : localY K (0, 0) = localY K p - frameY K p := by
      dsimp [localY, frameY]
      ring
    have h := abs_sub (localY K p) (frameY K p)
    rw [← he] at h
    dsimp [beta]
    linarith [hp.2]
  have hx₂ := pow_le_pow_left₀ (le_max_right _ _) hx 2
  have hy₂ := pow_le_pow_left₀ (le_max_right _ _) hy 2
  rw [sq_abs] at hx₂ hy₂
  dsimp [coreDistanceSq]
  linarith [frame_norm K p]

theorem coreAvoiding_iff_distance (K : UnitSquare) :
    CoreAvoiding K ↔ coreRadius^2 ≤ coreDistanceSq K := by
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := coreDistanceSq_attained K
    simpa [he] using h p hp
  · intro h p hp
    exact h.trans (coreDistanceSq_le hp)

lemma center_radius_sq (K : UnitSquare) :
    normSq K.center = (alpha K (0, 0))^2 + (beta K (0, 0))^2 := by
  simpa [sub] using local_center_norm K (0, 0)

lemma center_radius_pos {K : UnitSquare} (h : CoreAvoiding K) :
    0 < Real.sqrt (normSq K.center) := by
  have hc := h K.center (by
    norm_num [closedSquare, localX, localY])
  apply Real.sqrt_pos.mpr
  dsimp [coreRadius] at hc
  linarith

lemma annular_center_radius_lower {K : UnitSquare} (h : CoreAvoiding K) :
    7/12 ≤ Real.sqrt (normSq K.center) := by
  have ha := alpha_nonneg K (0, 0)
  have hb := beta_nonneg K (0, 0)
  have hc := (coreAvoiding_iff_distance K).mp h
  have hr := Real.sqrt_nonneg (normSq K.center)
  have hr₂ : Real.sqrt (normSq K.center) ^ 2 = alpha K (0, 0) ^ 2 + beta K (0, 0) ^ 2 := by
    rw [Real.sq_sqrt (normSq_nonneg K.center), center_radius_sq]
  dsimp [coreDistanceSq, coreRadius] at hc
  by_cases hA : alpha K (0, 0) ≤ 1/2
  · rw [max_eq_right (by linarith only [hA])] at hc
    have hB : 1/2 ≤ beta K (0, 0) := by
      by_contra! hh
      rw [max_eq_right (by linarith only [hh])] at hc
      norm_num at hc
    rw [max_eq_left (by linarith only [hB])] at hc
    have hb' : 7/12 ≤ beta K (0, 0) := by nlinarith only [hc, hB]
    nlinarith only [sq_nonneg (alpha K (0, 0)), hc, hr₂, hb', hr]
  · by_cases hB : beta K (0, 0) ≤ 1/2
    · rw [max_eq_left (by linarith only [hA]), max_eq_right (by linarith only [hB])] at hc
      have ha' : 7/12 ≤ alpha K (0, 0) := by nlinarith only [hc, hA]
      nlinarith only [sq_nonneg (beta K (0, 0)), hc, hr₂, ha', hr]
    · nlinarith only [hr₂, hA, hB, ha, hb, hr]

lemma annular_center_radius_upper {K : UnitSquare} {q : ℝ}
    (h : SqContained q K) (hq : q ≤ Q0) :
    Real.sqrt (normSq K.center) < 71/50 := by
  have ha := alpha_nonneg K (0, 0)
  have hb := beta_nonneg K (0, 0)
  have hr := Real.sqrt_nonneg (normSq K.center)
  have hr₂ : Real.sqrt (normSq K.center) ^ 2 = alpha K (0, 0) ^ 2 + beta K (0, 0) ^ 2 := by
    rw [Real.sq_sqrt (normSq_nonneg K.center), center_radius_sq]
  have hsum : Real.sqrt (normSq K.center) ≤ alpha K (0, 0) + beta K (0, 0) := by
    rw [center_radius_sq]
    apply Real.sqrt_le_left (by positivity) |>.2
    linarith [mul_nonneg ha hb]
  have hh := h.trans hq
  dsimp [SqContained, phi, Q0] at hh
  by_contra! hn
  linarith [sq_nonneg (Real.sqrt (normSq K.center) - 71/50)]

lemma signed_axis_center_distance {a : SignedAxis} {K L : UnitSquare}
    (h : a.Feasible K L) : 1 ≤ normSq (sub L.center K.center) := by
  have hp : 1 ≤ a.projection K L := (threshold_ge_one K L).trans h
  have hc := cauchy_sq (a.normal K L) (sub L.center K.center)
  rw [signed_normal_unit] at hc
  dsimp [SignedAxis.projection] at hp
  linarith [sq_nonneg (dot (a.normal K L) (sub L.center K.center) - 1)]

/-- For centre distances `r` and `s` in `[7/12, 71/50]`, the cosine of the angle between two
centres at least `1` apart is at most `17443/21300`. The bound is a maximum at a corner of the
square of `(r, s)`: `1 - r² - s² + (17443/10650) r s` is concave in each variable, so it is
nonnegative once it is at the corners, by two quadratic interpolation identities. -/
lemma annular_cosine_quotient {r s : ℝ}
    (hr : 7/12 ≤ r ∧ r ≤ 71/50) (hs : 7/12 ≤ s ∧ s ≤ 71/50) :
    (r^2+s^2-1)/(2*r*s) ≤ 17443/21300 := by
  let G : ℝ → ℝ → ℝ := fun x y => 1-x^2-y^2+(17443/10650)*x*y
  have hsprod := mul_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr hs.2)
  have ga : 0 ≤ G (7/12) s := by
    dsimp [G]
    linarith only [hs, hsprod]
  have gb : 0 ≤ G (71/50) s := by
    dsimp [G]
    linarith only [hs, hsprod]
  have h₁ := mul_nonneg (sub_nonneg.mpr hr.2) ga
  have h₂ := mul_nonneg (sub_nonneg.mpr hr.1) gb
  have h₃ := mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  have hid : (71/50-7/12)*G r s =
      (71/50-r)*G (7/12) s + (r-7/12)*G (71/50) s +
      (71/50-7/12)*(r-7/12)*(71/50-r) := by
    dsimp [G]
    ring
  have hg : 0 ≤ G r s := by linarith only [h₁, h₂, h₃, hid]
  apply (div_le_iff₀ (by nlinarith only [hr.1, hs.1])).2
  dsimp [G] at hg
  linarith only [hg]

lemma annular_angle_lower {r s θ : ℝ}
    (hr : 7/12 ≤ r ∧ r ≤ 71/50) (hs : 7/12 ≤ s ∧ s ≤ 71/50)
    (hθ : 0 ≤ θ ∧ θ ≤ Real.pi)
    (hd : 1 ≤ r^2+s^2-2*r*s*Real.cos θ) : 3/5 < θ := by
  have hpos : 0 < 2*r*s := by nlinarith only [hr.1, hs.1]
  have hc : Real.cos θ ≤ (r^2+s^2-1)/(2*r*s) := by
    apply (le_div_iff₀ hpos).2
    linarith
  have hbound := hc.trans (annular_cosine_quotient hr hs)
  have hcos : 41/50 ≤ Real.cos (3/5 : ℝ) := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := (3/5 : ℝ))]
  by_contra! hn
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi hθ.1
    (by linarith [Real.pi_gt_three] : (3/5 : ℝ) ≤ Real.pi) hn
  linarith

/-- Two closed half-planes with unit inward normals `n₁` and `n₂` have a common nonzero
recession direction: `n₁ + n₂`, or, when the normals are opposite and their sum vanishes, a
direction perpendicular to them. -/
lemma two_halfplanes_recession {n₁ n₂ : Point}
    (h₁ : normSq n₁ = 1) (h₂ : normSq n₂ = 1) :
    ∃ v : Point, v ≠ (0, 0) ∧ 0 ≤ dot n₁ v ∧ 0 ≤ dot n₂ v := by
  by_cases hn : add n₁ n₂ = (0, 0)
  · refine ⟨(-n₁.2, n₁.1), ?_, ?_, ?_⟩
    · intro h
      have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      dsimp [normSq] at h₁
      simp only at hx hy
      nlinarith only [h₁, hx, hy]
    · dsimp [dot]
      linarith
    · have hx := congrArg Prod.fst hn
      have hy := congrArg Prod.snd hn
      dsimp [add] at hx hy
      dsimp [dot]
      linarith [congrArg (fun x => x * n₁.2) hx, congrArg (fun x => x * n₁.1) hy]
  · refine ⟨add n₁ n₂, hn, ?_, ?_⟩
    all_goals
      have hc := cauchy_sq n₁ n₂
      rw [h₁, h₂] at hc
      have hd : -1 ≤ dot n₁ n₂ := by linarith [sq_nonneg (dot n₁ n₂ + 1)]
      dsimp [dot, add, normSq] at *
      linarith

def radialSquare (K : UnitSquare) (t : ℝ) : UnitSquare :=
  moveCenter K (scale t K.center)

lemma radialSquare_frame (K : UnitSquare) (t : ℝ) : SameFrame (radialSquare K t) K :=
  ⟨rfl, rfl⟩

lemma radialSquare_coordinates (K : UnitSquare) {t : ℝ} (ht : 0 ≤ t) :
    alpha (radialSquare K t) (0, 0) = t * alpha K (0, 0) ∧
    beta (radialSquare K t) (0, 0) = t * beta K (0, 0) := by
  have hx : localX (radialSquare K t) (0, 0) = t * localX K (0, 0) := by
    dsimp [radialSquare, moveCenter, localX, scale]
    ring
  have hy : localY (radialSquare K t) (0, 0) = t * localY K (0, 0) := by
    dsimp [radialSquare, moveCenter, localY, scale]
    ring
  simp [alpha, beta, hx, hy, abs_mul, abs_of_nonneg ht]

lemma radialSquare_core {K : UnitSquare} (hK : CoreAvoiding K) {t : ℝ} (ht : 1 ≤ t) :
    CoreAvoiding (radialSquare K t) := by
  apply (coreAvoiding_iff_distance _).2
  have h := (coreAvoiding_iff_distance K).1 hK
  obtain ⟨hx,hy⟩ := radialSquare_coordinates K (show 0 ≤ t by linarith)
  have ha := alpha_nonneg K (0, 0)
  have hb := beta_nonneg K (0, 0)
  have hax : alpha K (0, 0) ≤ t * alpha K (0, 0) := by nlinarith only [ht, ha]
  have hby : beta K (0, 0) ≤ t * beta K (0, 0) := by nlinarith only [ht, hb]
  have hx' := max_le_max (sub_le_sub_right hax (1/2)) (le_refl (0 : ℝ))
  have hy' := max_le_max (sub_le_sub_right hby (1/2)) (le_refl (0 : ℝ))
  have hx₂ := pow_le_pow_left₀ (le_max_right _ _) hx' 2
  have hy₂ := pow_le_pow_left₀ (le_max_right _ _) hy' 2
  dsimp [coreDistanceSq] at *
  rw [hx,hy]
  linarith

lemma threshold_same_frames {K K' L L' : UnitSquare}
    (hK : SameFrame K' K) (hL : SameFrame L' L) :
    SAT.threshold K' L' = SAT.threshold K L := by
  simp [SAT.threshold, relativeC, relativeS, hK.1, hK.2, hL.1, hL.2]

lemma signed_normal_same_frames {K K' L L' : UnitSquare}
    (hK : SameFrame K' K) (hL : SameFrame L' L) (axis : SignedAxis) :
    axis.normal K' L' = axis.normal K L := by
  cases axis.owner <;>
    simp [SignedAxis.normal, AxisOwner.normal, e, f, hK.1, hK.2, hL.1, hL.2]

lemma translate_pair_feasible {K L : UnitSquare} (axis : SignedAxis)
    (h : axis.Feasible K L) {u v : Point}
    (hproj : 0 ≤ dot (axis.normal K L) (sub v u)) :
    axis.Feasible (moveCenter K (add K.center u)) (moveCenter L (add L.center v)) := by
  have he := threshold_same_frames (moveCenter_sameFrame K (add K.center u))
    (moveCenter_sameFrame L (add L.center v))
  have hn := signed_normal_same_frames (moveCenter_sameFrame K (add K.center u))
    (moveCenter_sameFrame L (add L.center v)) axis
  dsimp [SignedAxis.Feasible] at *
  rw [he]
  dsimp [SignedAxis.projection]
  rw [hn]
  dsimp [moveCenter, dot, sub, add, SignedAxis.projection] at *
  linarith

lemma continuous_center_phi (K : UnitSquare) (p v : Point) :
    Continuous (fun t : ℝ => phi
      (alpha (moveCenter K (add p (scale t v))) (0,0))
      (beta (moveCenter K (add p (scale t v))) (0,0))) := by
  dsimp [phi,alpha,beta,moveCenter,localX,localY,add,scale]
  fun_prop

lemma continuous_center_coreDistance (K : UnitSquare) (p v : Point) :
    Continuous (fun t : ℝ => coreDistanceSq (moveCenter K (add p (scale t v)))) := by
  dsimp [coreDistanceSq,alpha,beta,moveCenter,localX,localY,add,scale]
  fun_prop

/-- The first contact: by compactness the least zero of the minimum of the two clearances
`q - F` and `G - ρ` on `[0, B]` is attained, and both weak constraints hold at every earlier
parameter. It stops the translation of `vertex_motion_exists`. -/
lemma first_two_boundary_contact {F G : ℝ → ℝ} {q ρ B : ℝ}
    (hF : Continuous F) (hG : Continuous G) (hB : 0 < B)
    (hF₀ : F 0 ≤ q) (hG₀ : ρ ≤ G 0) (hFB : q < F B) :
    ∃ t, 0 ≤ t ∧ t ≤ B ∧
      (∀ s, 0 ≤ s ∧ s ≤ t → F s ≤ q ∧ ρ ≤ G s) ∧
      (F t=q ∨ G t=ρ) := by
  let H : ℝ → ℝ := fun t => min (q-F t) (G t-ρ)
  have hH : Continuous H := (continuous_const.sub hF).min (hG.sub continuous_const)
  have hH₀ : 0 ≤ H 0 := le_min (by linarith) (by linarith)
  have hHB : H B < 0 := (min_le_left _ _).trans_lt (by linarith)
  have hzero : ∃ t ∈ Set.Icc 0 B, H t=0 := by
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' hB.le hH.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (H B) (H 0) from ⟨hHB.le,hH₀⟩)
    exact ⟨t,ht,he⟩
  let Z : Set ℝ := Set.Icc 0 B ∩ {t | H t=0}
  have hZ : IsCompact Z := isCompact_Icc.inter_right (isClosed_eq hH continuous_const)
  have hZne : Z.Nonempty := by
    obtain ⟨t,ht,he⟩ := hzero
    exact ⟨t,ht,he⟩
  obtain ⟨t,ht,hmin⟩ := hZ.exists_isMinOn hZne continuousOn_id
  have hall (s : ℝ) (hs : 0 ≤ s ∧ s ≤ t) : 0 ≤ H s := by
    by_contra! hn
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc' hs.1
      hH.continuousOn (show (0 : ℝ) ∈ Set.Icc (H s) (H 0) from ⟨hn.le,hH₀⟩)
    have huZ : u ∈ Z := ⟨⟨hu.1,hu.2.trans (hs.2.trans ht.1.2)⟩,he⟩
    have htu : t ≤ u := hmin huZ
    have hst : s=t := by linarith [hu.2]
    rw [hst,ht.2] at hn
    linarith
  refine ⟨t,ht.1.1,ht.1.2,?_,?_⟩
  · intro s hs
    have h := hall s hs
    have h₁ := h.trans (min_le_left _ _)
    have h₂ := h.trans (min_le_right _ _)
    exact ⟨by linarith,by linarith⟩
  · have he : min (q-F t) (G t-ρ)=0 := ht.2
    rcases le_total (q-F t) (G t-ρ) with h | h
    · rw [min_eq_left h] at he
      exact Or.inl (by linarith)
    · rw [min_eq_right h] at he
      exact Or.inr (by linarith)

lemma center_le_phi (K : UnitSquare) :
    normSq K.center ≤ phi (alpha K (0,0)) (beta K (0,0)) := by
  rw [center_radius_sq]
  dsimp [phi]
  linarith [alpha_nonneg K (0,0),beta_nonneg K (0,0)]

lemma ray_leaves_containment (K : UnitSquare) {q : ℝ} (hq : q ≤ Q0)
    {v : Point} (hv : v ≠ (0,0)) :
    ∃ B : ℝ, 0 < B ∧
      q < phi (alpha (moveCenter K (add K.center (scale B v))) (0,0))
        (beta (moveCenter K (add K.center (scale B v))) (0,0)) := by
  have hv' : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra! h
    exact hv (Prod.ext h.1 h.2)
  have hQ : q < 4 := hq.trans_lt radius_levels.2.2.2
  rcases hv' with hvx | hvy
  · let B := (3+|K.center.1|)/|v.1|
    have hB : 0 < B := div_pos (by positivity) (abs_pos.mpr hvx)
    have hm : B*|v.1|=3+|K.center.1| := by dsimp [B]; field_simp
    have hnorm : 3 ≤ |K.center.1+B*v.1| := by
      have hh := abs_sub (K.center.1+B*v.1) K.center.1
      rw [add_sub_cancel_left,abs_mul,abs_of_pos hB,hm] at hh
      linarith
    refine ⟨B,hB,?_⟩
    have hc := center_le_phi (moveCenter K (add K.center (scale B v)))
    have hcen : normSq (moveCenter K (add K.center (scale B v))).center =
        (K.center.1+B*v.1)^2+(K.center.2+B*v.2)^2 := by
      dsimp [normSq,moveCenter,add,scale]
    rw [hcen] at hc
    nlinarith only [sq_abs (K.center.1+B*v.1), sq_nonneg (K.center.2+B*v.2), hQ, hnorm, hc]
  · let B := (3+|K.center.2|)/|v.2|
    have hB : 0 < B := div_pos (by positivity) (abs_pos.mpr hvy)
    have hm : B*|v.2|=3+|K.center.2| := by dsimp [B]; field_simp
    have hnorm : 3 ≤ |K.center.2+B*v.2| := by
      have hh := abs_sub (K.center.2+B*v.2) K.center.2
      rw [add_sub_cancel_left,abs_mul,abs_of_pos hB,hm] at hh
      linarith
    refine ⟨B,hB,?_⟩
    have hc := center_le_phi (moveCenter K (add K.center (scale B v)))
    have hcen : normSq (moveCenter K (add K.center (scale B v))).center =
        (K.center.1+B*v.1)^2+(K.center.2+B*v.2)^2 := by
      dsimp [normSq,moveCenter,add,scale]
    rw [hcen] at hc
    nlinarith only [sq_abs (K.center.2+B*v.2), sq_nonneg (K.center.1+B*v.1), hQ, hnorm, hc]

private lemma moveCenter_self (K : UnitSquare) : moveCenter K K.center = K := rfl

def movedVertex {q : ℝ} (C : NeighborCycle q) (i : Vertex) (v : Point) (t : ℝ)
    (j : Vertex) : UnitSquare :=
  if j=i then moveCenter (C.square j) (add (C.square j).center (scale t v)) else C.square j

lemma movedVertex_frame {q : ℝ} (C : NeighborCycle q) (i : Vertex) (v : Point) (t : ℝ)
    (j : Vertex) : SameFrame (movedVertex C i v t j) (C.square j) := by
  by_cases h : j=i <;> simp [movedVertex,h,moveCenter,SameFrame]

lemma movedVertex_feasible {q : ℝ} (C : NeighborCycle q) (i : Vertex) {v : Point}
    (hin : 0 ≤ dot ((C.selected (prev i)).normal (C.square (prev i)) (C.square i)) v)
    (hout : dot ((C.selected i).normal (C.square i) (C.square (next i))) v ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) (j : Vertex) :
    (C.selected j).Feasible (movedVertex C i v t j) (movedVertex C i v t (next j)) := by
  have hself : next i ≠ i := by intro h; have := congrArg Fin.val h; fin_cases i <;> norm_num [next] at this
  by_cases hj : j=i
  · subst j
    simp only [movedVertex,hself,↓reduceIte]
    have hh := translate_pair_feasible (C.selected i) (C.feasible i)
      (u := scale t v) (v := (0,0)) (by
        dsimp [dot,sub,scale] at *
        linarith [mul_nonpos_of_nonneg_of_nonpos ht hout])
    simpa [add,moveCenter_self] using hh
  · by_cases hnext : next j=i
    · have hjprev : j=prev i := by rw [← hnext,prev_next]
      subst j
      simp only [movedVertex,hj,next_prev,↓reduceIte]
      have hh := translate_pair_feasible (C.selected (prev i)) (C.feasible (prev i))
        (u := (0,0)) (v := scale t v) (by
          rw [next_prev]
          dsimp [dot,sub,scale] at *
          linarith [mul_nonneg ht hin])
      simpa [add,next_prev,moveCenter_self] using hh
    · simpa [movedVertex,hj,hnext] using C.feasible j

/-- A translation of the square `i` along a fixed direction, with its frame kept, along which
both of its witnesses keep separating, every intermediate square is in the disk and avoids the
core disk, and the last square touches a radial boundary. The continuous path keeps the cyclic
order of the centre directions. -/
structure VertexMotion {q : ℝ} (C : NeighborCycle q) (i : Vertex) where
  direction : Point
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  incoming : 0 ≤ dot ((C.selected (prev i)).normal (C.square (prev i)) (C.square i)) direction
  outgoing : dot ((C.selected i).normal (C.square i) (C.square (next i))) direction ≤ 0
  admissible : ∀ t, 0 ≤ t ∧ t ≤ duration →
    SqContained q (moveCenter (C.square i) (add (C.square i).center (scale t direction))) ∧
    CoreAvoiding (moveCenter (C.square i) (add (C.square i).center (scale t direction)))
  boundary : OnRadialBoundary q
    (moveCenter (C.square i) (add (C.square i).center (scale duration direction)))

theorem vertex_motion_exists {q : ℝ} (C : NeighborCycle q) (hq : q ≤ Q0) (i : Vertex) :
    Nonempty (VertexMotion C i) := by
  let n₁ := (C.selected (prev i)).normal (C.square (prev i)) (C.square i)
  let n₂ := scale (-1) ((C.selected i).normal (C.square i) (C.square (next i)))
  have hn₁ : normSq n₁=1 := signed_normal_unit _ _ _
  have hn₂ : normSq n₂=1 := by
    rw [normSq_scale,signed_normal_unit]
    norm_num
  obtain ⟨v,hv,hvin,hvout⟩ := two_halfplanes_recession hn₁ hn₂
  obtain ⟨B,hB,hFB⟩ := ray_leaves_containment (C.square i) hq hv
  obtain ⟨t,ht,_,hall,hboundary⟩ := first_two_boundary_contact
    (continuous_center_phi (C.square i) (C.square i).center v)
    (continuous_center_coreDistance (C.square i) (C.square i).center v) hB
    (by simpa [moveCenter,add,scale,SqContained] using C.contained i)
    (by simpa [moveCenter,add,scale] using (coreAvoiding_iff_distance _).mp (C.core i)) hFB
  refine ⟨⟨v,t,ht,hvin,?_,?_,hboundary⟩⟩
  · dsimp [n₂,dot,scale] at hvout ⊢
    linarith
  · intro s hs
    have h := hall s hs
    exact ⟨h.1,(coreAvoiding_iff_distance _).mpr h.2⟩

def VertexMotion.cycleAt {q : ℝ} {C : NeighborCycle q} {i : Vertex}
    (M : VertexMotion C i) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ M.duration) : NeighborCycle q where
  square := movedVertex C i M.direction t
  contained j := by
    by_cases h : j=i
    · simpa [movedVertex,h] using (M.admissible t ht).1
    · simpa [movedVertex,h] using C.contained j
  core j := by
    by_cases h : j=i
    · simpa [movedVertex,h] using (M.admissible t ht).2
    · simpa [movedVertex,h] using C.core j
  selected := C.selected
  feasible := movedVertex_feasible C i M.incoming M.outgoing ht.1

def VertexMotion.endpoint {q : ℝ} {C : NeighborCycle q} {i : Vertex}
    (M : VertexMotion C i) : NeighborCycle q := M.cycleAt M.duration ⟨M.duration_nonneg,le_refl _⟩

lemma VertexMotion.endpoint_boundary {q : ℝ} {C : NeighborCycle q} {i : Vertex}
    (M : VertexMotion C i) : OnRadialBoundary q (M.endpoint.square i) := by
  simpa [VertexMotion.endpoint,VertexMotion.cycleAt,movedVertex] using M.boundary

lemma VertexMotion.endpoint_other {q : ℝ} {C : NeighborCycle q} {i : Vertex}
    (M : VertexMotion C i) {j : Vertex} (h : j ≠ i) : M.endpoint.square j=C.square j := by
  simp [VertexMotion.endpoint,VertexMotion.cycleAt,movedVertex,h]

lemma VertexMotion.endpoint_frames {q : ℝ} {C : NeighborCycle q} {i : Vertex}
    (M : VertexMotion C i) (j : Vertex) : SameFrame (M.endpoint.square j) (C.square j) :=
  movedVertex_frame C i M.direction M.duration j

def cross (p v : Point) : ℝ := p.1*v.2-p.2*v.1

lemma dot_sq_add_cross_sq (p v : Point) :
    (dot p v)^2+(cross p v)^2=normSq p*normSq v := by
  dsimp [dot,cross,normSq]
  ring

/-- A centre moving along a segment that avoids the origin has a continuous real polar angle.
The quotient of the moving point by the starting point, as a complex number, stays off the
negative real axis: an antiparallel position would force an earlier point of the segment to be
the origin. -/
lemma straight_line_polar_lift {p v : Point} {T β : ℝ}
    (hT : 0 ≤ T) (hn : ∀ t, 0 ≤ t ∧ t ≤ T → 0 < normSq (add p (scale t v)))
    (hx : p.1=Real.sqrt (normSq p)*Real.cos β)
    (hy : p.2=Real.sqrt (normSq p)*Real.sin β) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Set.Icc 0 T) ∧ θ 0=β ∧
      ∀ t, 0 ≤ t ∧ t ≤ T →
        (add p (scale t v)).1=Real.sqrt (normSq (add p (scale t v)))*Real.cos (θ t) ∧
        (add p (scale t v)).2=Real.sqrt (normSq (add p (scale t v)))*Real.sin (θ t) := by
  let z : ℝ → ℂ := fun t => ⟨dot p (add p (scale t v)),cross p (add p (scale t v))⟩
  have hp : 0 < normSq p := by simpa [add,scale] using hn 0 ⟨le_refl _,hT⟩
  have hzslit (t : ℝ) (ht : t ∈ Set.Icc 0 T) : z t ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hc : cross p (add p (scale t v))=0
    · left
      change 0 < dot p (add p (scale t v))
      by_contra! hd
      have htpos : 0 < t := by
        by_contra! h
        have he : t=0 := by linarith only [ht.1, h]
        subst t
        dsimp [dot,add,scale,normSq] at hd hp
        linarith only [hp, hd]
      let D := normSq p-dot p (add p (scale t v))
      let s := t*normSq p/D
      have hD : 0 < D := by dsimp [D]; linarith only [hp, hd]
      have hs : 0 ≤ s ∧ s ≤ t := by
        constructor
        · exact div_nonneg (mul_nonneg ht.1 hp.le) hD.le
        · apply (div_le_iff₀ hD).2
          have hm := mul_nonpos_of_nonneg_of_nonpos ht.1 hd
          dsimp [D]
          linarith only [hm]
      have hcv : cross p v=0 := by
        have he : cross p (add p (scale t v))=t*cross p v := by dsimp [cross,add,scale]; ring
        rw [he] at hc
        exact (mul_eq_zero.mp hc).resolve_left (ne_of_gt htpos)
      have hcs : cross p (add p (scale s v))=0 := by
        have he : cross p (add p (scale s v))=s*cross p v := by dsimp [cross,add,scale]; ring
        rw [he,hcv,mul_zero]
      have hds : dot p (add p (scale s v))=0 := by
        have hlin (u : ℝ) : dot p (add p (scale u v))=normSq p+u*dot p v := by
          dsimp [dot,add,scale,normSq]; ring
        have hDe : D=-(t*dot p v) := by simp only [D,hlin]; ring
        have hsD : s*D=t*normSq p := by simp only [s]; field_simp
        rw [hlin]
        clear_value s D
        subst hDe
        apply mul_left_cancel₀ (ne_of_gt htpos)
        linear_combination -hsD
      have hidentity := dot_sq_add_cross_sq p (add p (scale s v))
      rw [hds,hcs] at hidentity
      have hpositive := mul_pos hp (hn s ⟨hs.1,hs.2.trans ht.2⟩)
      linarith only [hidentity, hpositive]
    · exact Or.inr hc
  let θ : ℝ → ℝ := fun t => β+Complex.arg (z t)
  have hzcont : Continuous z := by
    have he : z = fun t => (dot p (add p (scale t v)) : ℂ) +
        (cross p (add p (scale t v)) : ℂ) * Complex.I := by
      funext t; exact Complex.mk_eq_add_mul_I _ _
    rw [he]
    dsimp [dot,cross,add,scale]
    fun_prop
  have hθcont : ContinuousOn θ (Set.Icc 0 T) :=
    continuousOn_const.add (Complex.continuousOn_arg.comp hzcont.continuousOn hzslit)
  have hz₀ : Complex.arg (z 0)=0 := by
    apply Complex.arg_eq_zero_iff.mpr
    dsimp [z,dot,cross,add,scale,normSq] at *
    constructor <;> linarith only [hp]
  refine ⟨θ,hθcont,by simp [θ,hz₀],?_⟩
  intro t ht
  let r₀ := Real.sqrt (normSq p)
  let r₁ := Real.sqrt (normSq (add p (scale t v)))
  have hr₀ : 0 < r₀ := Real.sqrt_pos.mpr hp
  have hr₁ : 0 < r₁ := Real.sqrt_pos.mpr (hn t ht)
  have hr₀₂ : r₀^2=normSq p := Real.sq_sqrt hp.le
  have hnorm : ‖z t‖=r₀*r₁ := by
    rw [Complex.norm_def,Complex.normSq_mk,← pow_two,← pow_two,dot_sq_add_cross_sq,
      Real.sqrt_mul hp.le]
  have hcarg := Complex.norm_mul_cos_arg (z t)
  have hsarg := Complex.norm_mul_sin_arg (z t)
  rw [hnorm] at hcarg hsarg
  have hcβ : Real.cos β=p.1/r₀ := (eq_div_iff (ne_of_gt hr₀)).2 (by simpa [mul_comm] using hx.symm)
  have hsβ : Real.sin β=p.2/r₀ := (eq_div_iff (ne_of_gt hr₀)).2 (by simpa [mul_comm] using hy.symm)
  have hca : Real.cos (Complex.arg (z t))=dot p (add p (scale t v))/(r₀*r₁) := by
    apply (eq_div_iff (ne_of_gt (mul_pos hr₀ hr₁))).2
    simpa [z,mul_comm] using hcarg
  have hsa : Real.sin (Complex.arg (z t))=cross p (add p (scale t v))/(r₀*r₁) := by
    apply (eq_div_iff (ne_of_gt (mul_pos hr₀ hr₁))).2
    simpa [z,mul_comm] using hsarg
  constructor
  · change _=r₁*Real.cos (β+Complex.arg (z t))
    rw [Real.cos_add,hcβ,hsβ,hca,hsa]
    field_simp [ne_of_gt hr₀,ne_of_gt hr₁]
    dsimp [normSq,dot,cross,add,scale] at *
    linarith only [congrArg (fun a : ℝ => (p.1+t*v.1)*a) hr₀₂, hr₀₂]
  · change _=r₁*Real.sin (β+Complex.arg (z t))
    rw [Real.sin_add,hcβ,hsβ,hca,hsa]
    field_simp [ne_of_gt hr₀,ne_of_gt hr₁]
    dsimp [normSq,dot,cross,add,scale] at *
    linarith only [congrArg (fun a : ℝ => (p.2+t*v.2)*a) hr₀₂, hr₀₂]

structure PolarOrder {q : ℝ} (C : NeighborCycle q) where
  beta : Vertex → ℝ
  center_cos : ∀ i, (C.square i).center.1=Real.sqrt (normSq (C.square i).center)*Real.cos (beta i)
  center_sin : ∀ i, (C.square i).center.2=Real.sqrt (normSq (C.square i).center)*Real.sin (beta i)
  positive : ∀ i, 0 < angleGap beta i
  below_pi : ∀ i, angleGap beta i < Real.pi

lemma polar_pair_distance {p₁ p₂ : Point} {r₁ r₂ β₁ β₂ : ℝ}
    (hx₁ : p₁.1=r₁*Real.cos β₁) (hy₁ : p₁.2=r₁*Real.sin β₁)
    (hx₂ : p₂.1=r₂*Real.cos β₂) (hy₂ : p₂.2=r₂*Real.sin β₂) :
    normSq (sub p₂ p₁)=r₁^2+r₂^2-2*r₁*r₂*Real.cos (β₂-β₁) := by
  dsimp [normSq,sub]
  rw [hx₁,hy₁,hx₂,hy₂,Real.cos_sub]
  linarith [congrArg (fun x : ℝ => r₁^2*x) (Real.sin_sq_add_cos_sq β₁),
    congrArg (fun x : ℝ => r₂^2*x) (Real.sin_sq_add_cos_sq β₂)]

lemma polar_gap_cosine_bound {q : ℝ} (C : NeighborCycle q) (hq : q ≤ Q0)
    (β : Vertex → ℝ)
    (hx : ∀ i, (C.square i).center.1=Real.sqrt (normSq (C.square i).center)*Real.cos (β i))
    (hy : ∀ i, (C.square i).center.2=Real.sqrt (normSq (C.square i).center)*Real.sin (β i))
    (i : Vertex) : Real.cos (angleGap β i) ≤ 17443/21300 := by
  let r := Real.sqrt (normSq (C.square i).center)
  let s := Real.sqrt (normSq (C.square (next i)).center)
  have hr : 7/12 ≤ r ∧ r ≤ 71/50 :=
    ⟨annular_center_radius_lower (C.core i),(annular_center_radius_upper (C.contained i) hq).le⟩
  have hs : 7/12 ≤ s ∧ s ≤ 71/50 :=
    ⟨annular_center_radius_lower (C.core (next i)),(annular_center_radius_upper (C.contained (next i)) hq).le⟩
  have hdist := signed_axis_center_distance (C.feasible i)
  rw [polar_pair_distance (hx i) (hy i) (hx (next i)) (hy (next i))] at hdist
  have hcos : Real.cos (angleGap β i)=Real.cos (β (next i)-β i) := by
    by_cases hi : i=6 <;> simp [angleGap,hi,Real.cos_add_two_pi]
  rw [← hcos] at hdist
  have hd : Real.cos (angleGap β i) ≤ (r^2+s^2-1)/(2*r*s) := by
    apply (le_div_iff₀ (by nlinarith only [hr.1, hs.1])).2
    linarith
  exact hd.trans (annular_cosine_quotient hr hs)

lemma positive_angle_of_continuous_no_collision {T : ℝ} {δ : ℝ → ℝ}
    (hδ : ContinuousOn δ (Set.Icc 0 T)) (hzero : 0 < δ 0 ∧ δ 0 < 2*Real.pi)
    (hcollision : ∀ t, 0 ≤ t ∧ t ≤ T → Real.cos (δ t) ≠ 1)
    {t : ℝ} (ht : 0 ≤ t ∧ t ≤ T) : 0 < δ t ∧ δ t < 2*Real.pi := by
  have hcont := hδ.mono (show Set.Icc 0 t ⊆ Set.Icc 0 T by intro x hx; exact ⟨hx.1,hx.2.trans ht.2⟩)
  constructor
  · by_contra! hn
    obtain ⟨s,hs,he⟩ := intermediate_value_Icc' ht.1 hcont ⟨hn,hzero.1.le⟩
    exact hcollision s ⟨hs.1,hs.2.trans ht.2⟩ (by rw [he,Real.cos_zero])
  · by_contra! hn
    obtain ⟨s,hs,he⟩ := intermediate_value_Icc ht.1 hcont ⟨hzero.2.le,hn⟩
    exact hcollision s ⟨hs.1,hs.2.trans ht.2⟩ (by rw [he,Real.cos_two_pi])

lemma gap_gt_three_fifths {δ : ℝ} (hδ : 0 < δ) (hcos : Real.cos δ ≤ 17443/21300) :
    3/5 < δ := by
  by_contra! hn
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi hδ.le
    (by linarith [Real.pi_gt_three] : (3/5 : ℝ) ≤ Real.pi) hn
  have hc := Real.one_sub_sq_div_two_le_cos (x := (3/5 : ℝ))
  linarith

lemma seven_gaps_below_pi (β : Vertex → ℝ) (h : ∀ i, 3/5 < angleGap β i) :
    ∀ i, angleGap β i < Real.pi := by
  have hs := angleGap_sum β
  intro i
  have hh := pi_lt_22_over_7
  norm_num [Fin.sum_univ_succ] at hs
  fin_cases i <;> simp only [Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk] <;>
    linarith only [h 0, h 1, h 2, h 3, h 4, h 5, h 6, hh, hs, h]

/-- The lifted gaps cannot cross zero or a full turn. Their uniform annular
lower bound then excludes a half turn by the total seven-gap budget. -/
def VertexMotion.polarOrder {q : ℝ} {C : NeighborCycle q} {i : Vertex}
    (M : VertexMotion C i) (O : PolarOrder C) (hq : q ≤ Q0) : PolarOrder M.endpoint := by
  have hnonzero (t : ℝ) (ht : 0 ≤ t ∧ t ≤ M.duration) :
      0 < normSq (add (C.square i).center (scale t M.direction)) := by
    have hh := center_radius_pos (M.admissible t ht).2
    exact Real.sqrt_pos.mp hh
  choose θ hθ hθ₀ hθpolar using straight_line_polar_lift M.duration_nonneg hnonzero
    (O.center_cos i) (O.center_sin i)
  let β : ℝ → Vertex → ℝ := fun t j => if j=i then θ t else O.beta j
  have hβ₀ : β 0=O.beta := by funext j; by_cases h : j=i <;> simp [β,h,hθ₀]
  have hpolar (t : ℝ) (ht : 0 ≤ t ∧ t ≤ M.duration) (j : Vertex) :
      ((M.cycleAt t ht).square j).center.1=
        Real.sqrt (normSq ((M.cycleAt t ht).square j).center)*Real.cos (β t j) ∧
      ((M.cycleAt t ht).square j).center.2=
        Real.sqrt (normSq ((M.cycleAt t ht).square j).center)*Real.sin (β t j) := by
    by_cases h : j=i
    · simpa [VertexMotion.cycleAt,movedVertex,h,β,moveCenter] using hθpolar t ht
    · simpa [VertexMotion.cycleAt,movedVertex,h,β] using ⟨O.center_cos j,O.center_sin j⟩
  have hgapcont (j : Vertex) : ContinuousOn (fun t => angleGap (β t) j) (Set.Icc 0 M.duration) := by
    dsimp [angleGap,β]
    split_ifs <;> fun_prop
  have hcos (t : ℝ) (ht : 0 ≤ t ∧ t ≤ M.duration) (j : Vertex) :
      Real.cos (angleGap (β t) j) ≤ 17443/21300 :=
    polar_gap_cosine_bound (M.cycleAt t ht) hq (β t)
      (fun j => (hpolar t ht j).1) (fun j => (hpolar t ht j).2) j
  have hpositive (t : ℝ) (ht : 0 ≤ t ∧ t ≤ M.duration) (j : Vertex) :
      0 < angleGap (β t) j :=
    (positive_angle_of_continuous_no_collision (hgapcont j)
      (by rw [hβ₀]; exact ⟨O.positive j,(O.below_pi j).trans (by linarith [Real.pi_pos])⟩)
      (fun s hs he => by have hh := hcos s hs j; rw [he] at hh; norm_num at hh) ht).1
  let ht := And.intro M.duration_nonneg (le_refl M.duration)
  refine ⟨β M.duration,(fun j => (hpolar M.duration ht j).1),
    (fun j => (hpolar M.duration ht j).2),(fun j => hpositive M.duration ht j),?_⟩
  exact seven_gaps_below_pi _ (fun j => gap_gt_three_fifths (hpositive M.duration ht j) (hcos M.duration ht j))

/-- An explicit quarter turn changes only the representative of a square. -/
def turnSquare (k : Fin 4) (K : UnitSquare) : UnitSquare where
  center := K.center
  cosine := ![K.cosine,-K.sine,-K.cosine,K.sine] k
  sine := ![K.sine,K.cosine,-K.sine,-K.cosine] k
  unit := by fin_cases k <;> simp <;> nlinarith [K.unit]

lemma turnSquare_sameSquare (k : Fin 4) (K : UnitSquare) : SameSquare (turnSquare k K) K := by
  have hX (p : Point) :
      localX (turnSquare k K) p=![localX K p,localY K p,-localX K p,-localY K p] k := by
    fin_cases k <;> dsimp [turnSquare,localX,localY] <;> ring
  have hY (p : Point) :
      localY (turnSquare k K) p=![localY K p,-localX K p,-localY K p,localX K p] k := by
    fin_cases k <;> dsimp [turnSquare,localX,localY] <;> ring
  constructor <;> intro p <;> simp only [openSquare,closedSquare,hX,hY] <;> fin_cases k <;>
    simp [abs_neg,and_comm]

lemma turnSquare_physical (k : Fin 4) (K : UnitSquare) : SamePhysicalFrame (turnSquare k K) K := by
  fin_cases k <;> simp [SamePhysicalFrame,turnSquare]

lemma turnSquare_phi (k : Fin 4) (K : UnitSquare) :
    phi (alpha (turnSquare k K) (0,0)) (beta (turnSquare k K) (0,0)) =
      phi (alpha K (0,0)) (beta K (0,0)) := by
  fin_cases k <;> dsimp [turnSquare,alpha,beta,localX,localY,phi] <;>
    simp only [← Real.sqrt_sq_eq_abs] <;> ring_nf

lemma turnSquare_coreDistance (k : Fin 4) (K : UnitSquare) :
    coreDistanceSq (turnSquare k K)=coreDistanceSq K := by
  fin_cases k <;> dsimp [turnSquare,coreDistanceSq,alpha,beta,localX,localY] <;>
    simp only [← Real.sqrt_sq_eq_abs] <;> ring_nf

lemma turnSquare_frame_coordinates (k : Fin 4) (K : UnitSquare) (p : Point) :
    frameX (turnSquare k K) p=![frameX K p,frameY K p,-frameX K p,-frameY K p] k ∧
    frameY (turnSquare k K) p=![frameY K p,-frameX K p,-frameY K p,frameX K p] k := by
  fin_cases k <;> constructor <;> dsimp [turnSquare,frameX,frameY] <;> ring

lemma frame_reconstruct (K : UnitSquare) (p : Point) :
    rotate K (frameX K p,frameY K p)=p := by
  apply Prod.ext <;> dsimp [rotate,frameX,frameY]
  · linear_combination p.1*K.unit
  · linear_combination p.2*K.unit

lemma canonical_quarter_choice (K : UnitSquare) (hp : 0 < normSq K.center) :
    ∃ k : Fin 4, 0 < frameX (turnSquare k K) K.center ∧
      |frameY (turnSquare k K) K.center| ≤ frameX (turnSquare k K) K.center := by
  let x := frameX K K.center
  let y := frameY K K.center
  have hnorm : 0 < x^2+y^2 := by rw [frame_norm]; exact hp
  by_cases hxy : |y| ≤ |x|
  · by_cases hx : 0 ≤ x
    · refine ⟨0,?_,?_⟩
      all_goals
        simp only [(turnSquare_frame_coordinates 0 K K.center).1,
          (turnSquare_frame_coordinates 0 K K.center).2,Matrix.cons_val_zero]
        rw [abs_of_nonneg hx] at hxy
        dsimp [x,y] at *
        nlinarith only [sq_abs (frameY K K.center), abs_nonneg (frameY K K.center), hnorm, hxy, hx]
    · refine ⟨2,?_,?_⟩
      all_goals
        simp only [(turnSquare_frame_coordinates 2 K K.center).1,
          (turnSquare_frame_coordinates 2 K K.center).2,Matrix.cons_val,abs_neg]
        rw [abs_of_neg (lt_of_not_ge hx)] at hxy
        dsimp [x,y] at *
        linarith
  · by_cases hy : 0 ≤ y
    · refine ⟨1,?_,?_⟩
      all_goals
        simp only [(turnSquare_frame_coordinates 1 K K.center).1,
          (turnSquare_frame_coordinates 1 K K.center).2,Matrix.cons_val,abs_neg]
        rw [abs_of_nonneg hy] at hxy
        dsimp [x,y] at *
        linarith [abs_nonneg (frameX K K.center)]
    · refine ⟨3,?_,?_⟩
      all_goals
        simp only [(turnSquare_frame_coordinates 3 K K.center).1,
          (turnSquare_frame_coordinates 3 K K.center).2,Matrix.cons_val]
        rw [abs_of_neg (lt_of_not_ge hy)] at hxy
        dsimp [x,y] at *
        linarith [abs_nonneg (frameX K K.center)]

structure CanonicalSquare (K : UnitSquare) where
  quarter : Fin 4
  a : ℝ
  b : ℝ
  sigma : ℝ
  a_pos : 0 < a
  b_nonneg : 0 ≤ b
  b_le_a : b ≤ a
  sigma_sign : sigma = -1 ∨ sigma = 1
  center_eq : K.center=rotate (turnSquare quarter K) (a,-sigma*b)

def CanonicalSquare.square {K : UnitSquare} (N : CanonicalSquare K) := turnSquare N.quarter K

lemma canonical_square_exists (K : UnitSquare) (hp : 0 < normSq K.center) :
    Nonempty (CanonicalSquare K) := by
  obtain ⟨k,hk,hxy⟩ := canonical_quarter_choice K hp
  let y := frameY (turnSquare k K) K.center
  let σ : ℝ := if y ≤ 0 then 1 else -1
  have hσ : σ = -1 ∨ σ = 1 := by dsimp [σ]; split_ifs <;> simp
  have hy : -σ*|y|=y := by
    dsimp [σ]
    split_ifs with h
    · rw [abs_of_nonpos h]
      ring
    · rw [abs_of_pos (lt_of_not_ge h)]
      ring
  refine ⟨⟨k,frameX (turnSquare k K) K.center,|y|,σ,hk,abs_nonneg _,hxy,hσ,?_⟩⟩
  rw [hy,frame_reconstruct]

lemma CanonicalSquare.coordinates {K : UnitSquare} (N : CanonicalSquare K) :
    alpha N.square (0,0)=N.a ∧ beta N.square (0,0)=N.b := by
  have hc : N.square.center = rotate N.square (N.a,-N.sigma*N.b) := N.center_eq
  have hX : localX N.square (0,0) = -N.a := by
    rw [localX,hc]
    dsimp [rotate]
    linear_combination -N.a*N.square.unit
  have hY : localY N.square (0,0) = N.sigma*N.b := by
    rw [localY,hc]
    dsimp [rotate]
    linear_combination N.sigma*N.b*N.square.unit
  have hσ : |N.sigma|=1 := by rcases N.sigma_sign with h | h <;> simp [h]
  simp [alpha,beta,hX,hY,abs_mul,hσ,abs_of_nonneg N.a_pos.le,abs_of_nonneg N.b_nonneg]

lemma CanonicalSquare.radius_sq {K : UnitSquare} (N : CanonicalSquare K) :
    normSq K.center=N.a^2+N.b^2 := by
  have hh := center_radius_sq N.square
  rw [N.coordinates.1,N.coordinates.2] at hh
  exact hh

lemma CanonicalSquare.boundary_kind {K : UnitSquare} {q : ℝ} (N : CanonicalSquare K)
    (hcore : CoreAvoiding K) (hb : OnRadialBoundary q K) :
    ∃ kind, BoundaryState q kind N.a N.b := by
  have hφ := turnSquare_phi N.quarter K
  have hc := turnSquare_coreDistance N.quarter K
  change phi (alpha N.square (0,0)) (beta N.square (0,0))=_ at hφ
  change coreDistanceSq N.square=_ at hc
  rw [N.coordinates.1,N.coordinates.2] at hφ
  rcases hb with hb | hb
  · exact ⟨.outer,by simpa [BoundaryState,← hφ] using hb⟩
  · have hd : (max (N.a-1/2) 0)^2+(max (N.b-1/2) 0)^2=(1/12 : ℝ)^2 := by
      simpa [coreDistanceSq,N.coordinates.1,N.coordinates.2,coreRadius] using hc.trans hb
    have ha : 1/2 < N.a := by
      by_contra! h
      rw [max_eq_right (by linarith),max_eq_right (by linarith [N.b_le_a])] at hd
      norm_num at hd
    rw [max_eq_left (by linarith)] at hd
    by_cases hNb : N.b ≤ 1/2
    · rw [max_eq_right (by linarith)] at hd
      exact ⟨.coreSide,by dsimp [BoundaryState]; exact ⟨by nlinarith only [hd, ha],hNb⟩⟩
    · rw [max_eq_left (by linarith)] at hd
      exact ⟨.coreCorner,by dsimp [BoundaryState]; exact ⟨by linarith,hd⟩⟩

def quarterAxisLocal (k : Fin 4) (isY : Bool) (sign : AxisSign) : Bool × AxisSign :=
  match k.val,isY with
  | 0,_ => (isY,sign)
  | 1,false => (true,sign.flip)
  | 1,true => (false,sign)
  | 2,_ => (isY,sign.flip)
  | _,false => (true,sign)
  | _,true => (false,sign.flip)

def transportQuarterAxis (k l : Fin 4) (axis : SignedAxis) : SignedAxis :=
  match axis.owner with
  | .sourceX => let a := quarterAxisLocal k false axis.sign; ⟨if a.1 then .sourceY else .sourceX,a.2⟩
  | .sourceY => let a := quarterAxisLocal k true axis.sign; ⟨if a.1 then .sourceY else .sourceX,a.2⟩
  | .targetX => let a := quarterAxisLocal l false axis.sign; ⟨if a.1 then .targetY else .targetX,a.2⟩
  | .targetY => let a := quarterAxisLocal l true axis.sign; ⟨if a.1 then .targetY else .targetX,a.2⟩

lemma transportQuarterAxis_normal (k l : Fin 4) (axis : SignedAxis) (K J : UnitSquare) :
    (transportQuarterAxis k l axis).normal (turnSquare k K) (turnSquare l J)=axis.normal K J := by
  rcases axis with ⟨owner,sign⟩
  fin_cases k <;> fin_cases l <;> cases owner <;> cases sign <;>
    simp [transportQuarterAxis,quarterAxisLocal,turnSquare,SignedAxis.normal,
      AxisOwner.normal,AxisSign.value,AxisSign.flip,e,f,scale]

lemma turnSquare_threshold (k l : Fin 4) (K J : UnitSquare) :
    SAT.threshold (turnSquare k K) (turnSquare l J)=SAT.threshold K J := by
  fin_cases k <;> fin_cases l <;>
    dsimp [turnSquare,SAT.threshold,relativeC,relativeS] <;>
    simp only [← Real.sqrt_sq_eq_abs] <;> ring_nf

lemma transportQuarterAxis_feasible {k l : Fin 4} {axis : SignedAxis} {K J : UnitSquare}
    (h : axis.Feasible K J) :
    (transportQuarterAxis k l axis).Feasible (turnSquare k K) (turnSquare l J) := by
  dsimp [SignedAxis.Feasible] at *
  rw [turnSquare_threshold]
  dsimp [SignedAxis.projection]
  rw [transportQuarterAxis_normal]
  exact h

lemma arctan_polar_coordinates {a b σ : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hσ : σ = -1 ∨ σ = 1) :
    Real.cos (Real.arctan (σ*b/a))=a/Real.sqrt (a^2+b^2) ∧
    Real.sin (Real.arctan (σ*b/a))=σ*b/Real.sqrt (a^2+b^2) := by
  let t := Real.arctan (σ*b/a)
  have htrange := Real.arctan_mem_Ioo (σ*b/a)
  have hcpos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo htrange
  have htan : Real.sin t/Real.cos t=σ*b/a := by
    rw [← Real.tan_eq_sin_div_cos,Real.tan_arctan]
  have hmul : a*Real.sin t=σ*b*Real.cos t := by
    apply (div_eq_div_iff (ne_of_gt hcpos) (ne_of_gt ha)).mp at htan
    linarith only [htan]
  have hσ₂ : σ^2=1 := by rcases hσ with h | h <;> simp [h]
  have hr : 0 < Real.sqrt (a^2+b^2) := Real.sqrt_pos.mpr (by nlinarith only [sq_nonneg b, ha])
  have hr₂ := Real.sq_sqrt (show 0 ≤ a^2+b^2 by positivity)
  have hcos : Real.sqrt (a^2+b^2)*Real.cos t=a := by
    have hsq := congrArg (fun x : ℝ => x^2) hmul
    have hu := congrArg (fun x : ℝ => a^2*x) (Real.sin_sq_add_cos_sq t)
    have hp := mul_pos hr hcpos
    nlinarith only [congrArg (fun x : ℝ => x*Real.cos t^2) hr₂,
      congrArg (fun x : ℝ => x*b^2*Real.cos t^2) hσ₂, hsq, hu, hr₂, hσ₂, ha, hp]
  have hsin : Real.sqrt (a^2+b^2)*Real.sin t=σ*b := by
    nlinarith only [congrArg (fun x : ℝ => Real.sqrt (a^2+b^2)*x) hmul,
      congrArg (fun x : ℝ => σ*b*x) hcos, hmul, hcos, ha]
  exact ⟨(eq_div_iff (ne_of_gt hr)).2 (by linarith only [hcos]),
    (eq_div_iff (ne_of_gt hr)).2 (by linarith only [hsin])⟩

lemma CanonicalSquare.frame_polar {K : UnitSquare} (N : CanonicalSquare K) {β : ℝ}
    (hx : K.center.1=Real.sqrt (normSq K.center)*Real.cos β)
    (hy : K.center.2=Real.sqrt (normSq K.center)*Real.sin β) :
    N.square.cosine=Real.cos (β+Real.arctan (N.sigma*N.b/N.a)) ∧
    N.square.sine=Real.sin (β+Real.arctan (N.sigma*N.b/N.a)) := by
  obtain ⟨hca,hsa⟩ := arctan_polar_coordinates N.a_pos N.b_nonneg N.sigma_sign
  have hr : 0 < Real.sqrt (N.a^2+N.b^2) :=
    Real.sqrt_pos.mpr (by nlinarith only [N.a_pos, sq_nonneg N.b])
  rw [N.radius_sq] at hx hy
  have hx' := congrArg Prod.fst N.center_eq
  have hy' := congrArg Prod.snd N.center_eq
  have hσ₂ : N.sigma^2=1 := by rcases N.sigma_sign with h | h <;> simp [h]
  have hr₂ := Real.sq_sqrt (show 0 ≤ N.a^2+N.b^2 by positivity)
  have hcosβ : Real.cos β=K.center.1/Real.sqrt (N.a^2+N.b^2) := by
    apply (eq_div_iff (ne_of_gt hr)).2; linarith only [hx]
  have hsinβ : Real.sin β=K.center.2/Real.sqrt (N.a^2+N.b^2) := by
    apply (eq_div_iff (ne_of_gt hr)).2; linarith only [hy]
  constructor
  · rw [Real.cos_add,hca,hsa,hcosβ,hsinβ]
    field_simp [ne_of_gt hr]
    dsimp [rotate,CanonicalSquare.square] at *
    linarith only [congrArg (fun x : ℝ => N.a*x) hx', congrArg (fun x : ℝ => N.sigma*N.b*x) hy',
      congrArg (fun x : ℝ => (turnSquare N.quarter K).cosine*x) hr₂,
      congrArg (fun x : ℝ => (turnSquare N.quarter K).cosine*N.b^2*x) hσ₂, hx', hy', hr₂, hσ₂]
  · rw [Real.sin_add,hca,hsa,hcosβ,hsinβ]
    field_simp [ne_of_gt hr]
    dsimp [rotate,CanonicalSquare.square] at *
    linarith only [congrArg (fun x : ℝ => N.sigma*N.b*x) hx', congrArg (fun x : ℝ => N.a*x) hy',
      congrArg (fun x : ℝ => (turnSquare N.quarter K).sine*x) hr₂,
      congrArg (fun x : ℝ => (turnSquare N.quarter K).sine*N.b^2*x) hσ₂, hx', hy', hr₂, hσ₂]

def canonicalBoundaryCycle {q : ℝ} (C : NeighborCycle q) (O : PolarOrder C)
    (hboundary : ∀ i, OnRadialBoundary q (C.square i)) : BoundaryCycle q := by
  let N : (i : Vertex) → CanonicalSquare (C.square i) := fun i =>
    Classical.choice (canonical_square_exists (C.square i) (Real.sqrt_pos.mp (center_radius_pos (C.core i))))
  choose kind hkind using fun i => (N i).boundary_kind (C.core i) (hboundary i)
  refine {
    square := fun i => (N i).square
    contained := ?_
    core := ?_
    selected := fun i => transportQuarterAxis (N i).quarter (N (next i)).quarter (C.selected i)
    feasible := fun i => transportQuarterAxis_feasible (C.feasible i)
    kind := kind
    a := fun i => (N i).a
    b := fun i => (N i).b
    sigma := fun i => (N i).sigma
    a_pos := fun i => (N i).a_pos
    b_nonneg := fun i => (N i).b_nonneg
    b_le_a := fun i => (N i).b_le_a
    sigma_sign := fun i => (N i).sigma_sign
    center_eq := fun i => (N i).center_eq
    boundary := hkind
    beta := O.beta
    center_cos := ?_
    center_sin := ?_
    frame_cos := fun i => ((N i).frame_polar (O.center_cos i) (O.center_sin i)).1
    frame_sin := fun i => ((N i).frame_polar (O.center_cos i) (O.center_sin i)).2
    gap_pos := O.positive
    gap_lt_pi := O.below_pi }
  · intro i
    change phi (alpha (turnSquare (N i).quarter (C.square i)) (0,0))
      (beta (turnSquare (N i).quarter (C.square i)) (0,0)) ≤ q
    rw [turnSquare_phi]
    exact C.contained i
  · intro i p hp
    exact C.core i p ((turnSquare_sameSquare (N i).quarter (C.square i)).2 p |>.mp hp)
  · intro i
    have h := O.center_cos i
    rw [(N i).radius_sq] at h
    exact h
  · intro i
    have h := O.center_sin i
    rw [(N i).radius_sq] at h
    exact h

lemma canonicalBoundaryCycle_physical {q : ℝ} (C : NeighborCycle q) (O : PolarOrder C)
    (hboundary : ∀ i, OnRadialBoundary q (C.square i)) (i : Vertex) :
    SamePhysicalFrame ((canonicalBoundaryCycle C O hboundary).square i) (C.square i) := by
  unfold canonicalBoundaryCycle
  exact turnSquare_physical _ _

lemma canonicalBoundaryCycle_axes {q : ℝ} (C : NeighborCycle q) (O : PolarOrder C)
    (hboundary : ∀ i, OnRadialBoundary q (C.square i)) (i : Vertex) :
    ((canonicalBoundaryCycle C O hboundary).selected i).normal
      ((canonicalBoundaryCycle C O hboundary).square i)
      ((canonicalBoundaryCycle C O hboundary).square (next i)) =
      (C.selected i).normal (C.square i) (C.square (next i)) := by
  unfold canonicalBoundaryCycle
  exact transportQuarterAxis_normal _ _ _ _ _

/-- The finite induction anchors each of the seven labels once. An earlier
anchor remains unchanged when a later label is moved. -/
theorem anchored_cycle_exists {q : ℝ} (C : NeighborCycle q) (O : PolarOrder C) (hq : q ≤ Q0) :
    ∃ D : NeighborCycle q, Nonempty (PolarOrder D) ∧
      (∀ i, OnRadialBoundary q (D.square i)) ∧
      (∀ i, SameFrame (D.square i) (C.square i)) ∧ D.selected=C.selected := by
  have stage (n : ℕ) (hn : n ≤ 7) : ∃ D : NeighborCycle q, Nonempty (PolarOrder D) ∧
      (∀ i : Vertex, i.val < n → OnRadialBoundary q (D.square i)) ∧
      (∀ i, SameFrame (D.square i) (C.square i)) ∧ D.selected=C.selected := by
    induction n with
    | zero => exact ⟨C,⟨O⟩,by intro i hi; omega,fun i => ⟨rfl,rfl⟩,rfl⟩
    | succ n ih =>
      obtain ⟨D,⟨OD⟩,hanchored,hframe,hselected⟩ := ih (by omega)
      let i : Vertex := ⟨n,by omega⟩
      obtain ⟨M⟩ := vertex_motion_exists D hq i
      refine ⟨M.endpoint,⟨M.polarOrder OD hq⟩,?_,?_,hselected⟩
      · intro j hj
        by_cases h : j=i
        · simpa [h] using M.endpoint_boundary
        · rw [M.endpoint_other h]
          exact hanchored j (by
            have hval : j.val ≠ n := by intro he; apply h; exact Fin.ext he
            omega)
      · intro j
        exact ⟨(M.endpoint_frames j).1.trans (hframe j).1,(M.endpoint_frames j).2.trans (hframe j).2⟩
  obtain ⟨D,hO,hb,hf,hs⟩ := stage 7 (le_refl _)
  exact ⟨D,hO,fun i => hb i i.isLt,hf,hs⟩

theorem boundary_reduction_exists {q : ℝ} (C : NeighborCycle q) (O : PolarOrder C)
    (hq : q ≤ Q0) : Nonempty (BoundaryReduction C) := by
  obtain ⟨D,⟨OD⟩,hb,hf,hs⟩ := anchored_cycle_exists C O hq
  refine ⟨{
    raw := D
    raw_frames := hf
    raw_selected := hs
    result := canonicalBoundaryCycle D OD hb
    physical_frames := ?_
    axis_transport := canonicalBoundaryCycle_axes D OD hb }⟩
  intro i
  have h := canonicalBoundaryCycle_physical D OD hb i
  rcases h with h | h | h | h <;>
    simp only [SamePhysicalFrame,hf i |>.1,hf i |>.2] at * <;> aesop

end SquaresInCircles.Eight
