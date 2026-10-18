module

public import SquaresInCircles.Eight.SeparatingAxis
public import SquaresInCircles.Eight.Frames
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The annular boundary reduction

The center is moved in the intersection of its two retained SAT halfplanes.
The endpoint is the first contact with either radial boundary. All feasibility
statements refer to the original signed normals; the argument never asserts
that arbitrary motion away from the disk center preserves separation.

This is an uncompiled source transcription of
`CYCLIC_RADIAL_BOUNDARY_REDUCTION.md`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace SquaresInCircles.Eight

lemma normSq_scale (t : ℝ) (p : Point) : normSq (scale t p) = t^2 * normSq p := by
  dsimp [normSq, scale]
  ring

lemma coreDistanceSq_nonneg (K : UnitSquare) : 0 ≤ coreDistanceSq K := by
  dsimp [coreDistanceSq]
  positivity

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

theorem strictCoreAvoiding_iff_distance (K : UnitSquare) :
    StrictCoreAvoiding K ↔ coreRadius^2 < coreDistanceSq K := by
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := coreDistanceSq_attained K
    simpa [he] using h p hp
  · intro h p hp
    exact h.trans_le (coreDistanceSq_le hp)

lemma center_radius_sq (K : UnitSquare) :
    normSq K.center = (alpha K (0, 0))^2 + (beta K (0, 0))^2 := by
  simpa [sub] using local_center_norm K (0, 0)

lemma center_radius_pos {K : UnitSquare} (h : CoreAvoiding K) :
    0 < Real.sqrt (normSq K.center) := by
  have hc := h K.center (by
    norm_num [closedSquare, localX, localY])
  apply Real.sqrt_pos.mpr
  dsimp [coreRadius] at hc
  nlinarith

lemma annular_center_radius_lower {K : UnitSquare} (h : CoreAvoiding K) :
    7/12 ≤ Real.sqrt (normSq K.center) := by
  have ha := alpha_nonneg K (0, 0)
  have hb := beta_nonneg K (0, 0)
  have hc := (coreAvoiding_iff_distance K).mp h
  have hr := Real.sqrt_nonneg (normSq K.center)
  have hr₂ := Real.sq_sqrt (normSq_nonneg K.center)
  rw [center_radius_sq] at hr₂
  dsimp [coreDistanceSq, coreRadius] at hc
  by_cases hA : alpha K (0, 0) ≤ 1/2
  · rw [max_eq_right (by linarith)] at hc
    have hB : 1/2 ≤ beta K (0, 0) := by
      by_contra! hh
      rw [max_eq_right (by linarith)] at hc
      norm_num at hc
    rw [max_eq_left (by linarith)] at hc
    have hb' : 7/12 ≤ beta K (0, 0) := by nlinarith
    nlinarith [sq_nonneg (alpha K (0, 0))]
  · by_cases hB : beta K (0, 0) ≤ 1/2
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)] at hc
      have ha' : 7/12 ≤ alpha K (0, 0) := by nlinarith
      nlinarith [sq_nonneg (beta K (0, 0))]
    · nlinarith

lemma annular_center_radius_upper {K : UnitSquare} {q : ℝ}
    (h : SqContained q K) (hq : q ≤ Q0) :
    Real.sqrt (normSq K.center) < 71/50 := by
  have ha := alpha_nonneg K (0, 0)
  have hb := beta_nonneg K (0, 0)
  have hr := Real.sqrt_nonneg (normSq K.center)
  have hr₂ := Real.sq_sqrt (normSq_nonneg K.center)
  have hsum : Real.sqrt (normSq K.center) ≤ alpha K (0, 0) + beta K (0, 0) := by
    rw [center_radius_sq]
    apply Real.sqrt_le_left (by positivity) |>.2
    nlinarith [mul_nonneg ha hb]
  have hh := h.trans hq
  dsimp [SqContained, phi, Q0] at hh
  rw [center_radius_sq] at hr₂
  by_contra! hn
  nlinarith [sq_nonneg (Real.sqrt (normSq K.center) - 71/50)]

lemma signed_axis_center_distance {a : SignedAxis} {K L : UnitSquare}
    (h : a.Feasible K L) : 1 ≤ normSq (sub L.center K.center) := by
  have hp : 1 ≤ a.projection K L := (threshold_ge_one K L).trans h
  have hc := cauchy_sq (a.normal K L) (sub L.center K.center)
  rw [signed_normal_unit] at hc
  dsimp [SignedAxis.projection] at hp
  nlinarith [sq_nonneg (dot (a.normal K L) (sub L.center K.center) - 1)]

/-- The corner maximum is proved by separate concavity, encoded as two
quadratic interpolation identities. No sampled angular bound is used. -/
lemma annular_cosine_quotient {r s : ℝ}
    (hr : 7/12 ≤ r ∧ r ≤ 71/50) (hs : 7/12 ≤ s ∧ s ≤ 71/50) :
    (r^2+s^2-1)/(2*r*s) ≤ 17443/21300 := by
  let G : ℝ → ℝ → ℝ := fun x y => 1-x^2-y^2+(17443/10650)*x*y
  have hsprod := mul_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr hs.2)
  have ga : 0 ≤ G (7/12) s := by
    dsimp [G]
    nlinarith
  have gb : 0 ≤ G (71/50) s := by
    dsimp [G]
    nlinarith
  have h₁ := mul_nonneg (sub_nonneg.mpr hr.2) ga
  have h₂ := mul_nonneg (sub_nonneg.mpr hr.1) gb
  have h₃ := mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  have hid : (71/50-7/12)*G r s =
      (71/50-r)*G (7/12) s + (r-7/12)*G (71/50) s +
      (71/50-7/12)*(r-7/12)*(71/50-r) := by
    dsimp [G]
    ring
  have hg : 0 ≤ G r s := by nlinarith
  apply (div_le_iff₀ (by nlinarith [hr.1,hs.1])).2
  dsimp [G] at hg
  nlinarith

lemma annular_angle_lower {r s θ : ℝ}
    (hr : 7/12 ≤ r ∧ r ≤ 71/50) (hs : 7/12 ≤ s ∧ s ≤ 71/50)
    (hθ : 0 ≤ θ ∧ θ ≤ Real.pi)
    (hd : 1 ≤ r^2+s^2-2*r*s*Real.cos θ) : 3/5 < θ := by
  have hpos : 0 < 2*r*s := by nlinarith [hr.1, hs.1]
  have hc : Real.cos θ ≤ (r^2+s^2-1)/(2*r*s) := by
    apply (le_div_iff₀ hpos).2
    nlinarith
  have hbound := hc.trans (annular_cosine_quotient hr hs)
  have hcos : 41/50 ≤ Real.cos (3/5 : ℝ) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := (3/5 : ℝ))]
  by_contra! hn
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi hθ.1
    (by linarith [Real.pi_gt_three] : (3/5 : ℝ) ≤ Real.pi) hn
  linarith

/-- Any two retained halfplanes have a common nonzero recession direction.
The antiparallel case uses a perpendicular direction rather than division
by the vanishing sum of the normals. -/
lemma two_halfplanes_recession {n₁ n₂ : Point}
    (h₁ : normSq n₁ = 1) (h₂ : normSq n₂ = 1) :
    ∃ v : Point, v ≠ (0, 0) ∧ 0 ≤ dot n₁ v ∧ 0 ≤ dot n₂ v := by
  by_cases hn : add n₁ n₂ = (0, 0)
  · refine ⟨(-n₁.2, n₁.1), ?_, ?_, ?_⟩
    · intro h
      have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      dsimp [normSq] at h₁
      simp only [Prod.fst, Prod.snd] at hx hy
      nlinarith
    · dsimp [dot]
      nlinarith
    · have hx := congrArg Prod.fst hn
      have hy := congrArg Prod.snd hn
      dsimp [add] at hx hy
      dsimp [dot]
      nlinarith
  · refine ⟨add n₁ n₂, hn, ?_, ?_⟩
    all_goals
      have hc := cauchy_sq n₁ n₂
      rw [h₁, h₂] at hc
      have hd : -1 ≤ dot n₁ n₂ := by nlinarith [sq_nonneg (dot n₁ n₂ + 1)]
      dsimp [dot, add, normSq] at *
      nlinarith

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
  have hax : alpha K (0, 0) ≤ t * alpha K (0, 0) := by nlinarith
  have hby : beta K (0, 0) ≤ t * beta K (0, 0) := by nlinarith
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
  have he := threshold_same_frames (moveCenter_sameFrame K _) (moveCenter_sameFrame L _)
  have hn := signed_normal_same_frames (moveCenter_sameFrame K _) (moveCenter_sameFrame L _) axis
  dsimp [SignedAxis.Feasible] at *
  rw [he]
  dsimp [SignedAxis.projection]
  rw [hn]
  dsimp [moveCenter, dot, sub, add] at *
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

/-- Compactness in one real parameter: the least zero of the minimum of
the two clearances is attained. Every earlier parameter retains both weak
constraints. This is the first-contact step used by the actual translation. -/
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
  nlinarith [alpha_nonneg K (0,0),beta_nonneg K (0,0)]

lemma ray_leaves_containment (K : UnitSquare) {q : ℝ} (hq : q ≤ Q0)
    {v : Point} (hv : v ≠ (0,0)) :
    ∃ B : ℝ, 0 < B ∧
      q < phi (alpha (moveCenter K (add K.center (scale B v))) (0,0))
        (beta (moveCenter K (add K.center (scale B v))) (0,0)) := by
  have hv' : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra! h
    exact hv (Prod.ext h.1 h.2)
  have hQ : q < 4 := hq.trans_lt radius_levels.2.2.2.2
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
    dsimp [normSq,moveCenter,add,scale] at hc
    nlinarith [sq_abs (K.center.1+B*v.1),sq_nonneg (K.center.2+B*v.2)]
  · let B := (3+|K.center.2|)/|v.2|
    have hB : 0 < B := div_pos (by positivity) (abs_pos.mpr hvy)
    have hm : B*|v.2|=3+|K.center.2| := by dsimp [B]; field_simp
    have hnorm : 3 ≤ |K.center.2+B*v.2| := by
      have hh := abs_sub (K.center.2+B*v.2) K.center.2
      rw [add_sub_cancel_left,abs_mul,abs_of_pos hB,hm] at hh
      linarith
    refine ⟨B,hB,?_⟩
    have hc := center_le_phi (moveCenter K (add K.center (scale B v)))
    dsimp [normSq,moveCenter,add,scale] at hc
    nlinarith [sq_abs (K.center.2+B*v.2),sq_nonneg (K.center.1+B*v.1)]

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
    simp only [movedVertex,if_pos rfl,if_neg hself]
    have hh := translate_pair_feasible (C.selected i) (C.feasible i)
      (u := scale t v) (v := (0,0)) (by
        dsimp [dot,sub,scale] at *
        nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hout])
    simpa [add] using hh
  · by_cases hnext : next j=i
    · have hjprev : j=prev i := by rw [← hnext,prev_next]
      subst j
      simp only [movedVertex,if_neg hj,next_prev,if_pos rfl]
      have hh := translate_pair_feasible (C.selected (prev i)) (C.feasible (prev i))
        (u := (0,0)) (v := scale t v) (by
          rw [next_prev]
          dsimp [dot,sub,scale] at *
          nlinarith [mul_nonneg ht hin])
      simpa [add,next_prev] using hh
    · simpa [movedVertex,hj,hnext] using C.feasible j

/-- One concrete fixed-frame translation, including every intermediate
admissible square. This supplies the continuous path needed for order. -/
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
  · dsimp [n₂,dot,scale] at hvout
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

end SquaresInCircles.Eight
