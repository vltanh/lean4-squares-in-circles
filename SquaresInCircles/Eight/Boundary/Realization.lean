module

public import SquaresInCircles.Eight.Boundary.Candidate.Geometry
public import SquaresInCircles.Eight.Boundary.RadiusTransfer
public import SquaresInCircles.Eight.Frames.PhysicalCycle
public import SquaresInCircles.Eight.Words.Basic

/-!
# Eight squares: signed cycles as boundary cycles

A signed cycle that satisfies `Necessary` at a level `q` and is ordered, whose points lie on the
boundary at that level (the outer circle of the level or the core curve), with a feasible owner
on each edge, is a boundary cycle at the same level (`SignedCycle.realizeBoundary`). It keeps the
squares and the frames of the signed cycle (`realizeBoundary_square`,
`realizeBoundary_canonicalAngle`); the radial kind of a point is read from its position
(`SignedPoint.boundaryKind`, `boundaryKind_spec`), and the polar angles of the centres are the
centre directions, with the physical gaps as their gaps (`actualSquare_polar`,
`polarAngle_gap`). A forward axis separates two consecutive squares of the boundary cycle
exactly when it is feasible on the signed cycle (`realizeBoundary_feasible_iff`). So the theorems
on boundary cycles apply to the cycles produced by the moves: for `q ≤ Q0` their gaps are above
`19/25` (`realized_gap_lower`), and with a strict spread and `C.theta A = 0` their frame angles
form a candidate frame (`realizedFrame`).
-/

section
/-!
## The gaps of a cycle and the four forward axes

A square in the disk of squared radius at most `Q0` that avoids the core disk has its primary
coordinate above `107/200`, by the lower bound on its distance from the origin. By the
common-point lemma `CentralBand.RayData.common_point_B` it then contains the point at distance
`41/40` from the origin in every direction within `19/50` of its centre direction, a closed cap of
half-angle `19/50`. So two disjoint such squares have centre directions more than `19/25` apart
(`exterior_pair_gap`). This holds for the exterior squares of a packing and for the squares of a
boundary cycle alike, and it gives the gaps `19/25 < δᵢ < 3π/4` of a cycle
(`boundary_gap_lower`, `boundary_gap_upper`).

Of the eight signed axes of two consecutive squares of a boundary cycle, only the four forward
axes can separate them (`boundary_forward_complete`). Along `+e` of the source the centre of the
target would be at distance at least `a + 1 > 3/2` from the origin, and in the same way along
`-e` of the target. Along `-f` of the source or of the target the projection is less than
`(3/2)(3/100) + b < 1`, since the angle involved lies in the interval `(-3/100, π)`, on which the
sine exceeds `-3/100` (`backward_sine_lower`). Every separating axis is covered, whichever witness
was chosen.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight

lemma CentralBand.RayData.center_point {K : UnitSquare} (R : CentralBand.RayData K) :
    circlePoint (0,0) R.radius R.direction=K.center := by
  set p := circlePoint (0,0) R.radius R.direction with hp
  have hmem (m : ℝ) : openSquare K
      (sub (circlePoint (0,0) ((1+m)*R.radius) R.direction) (scale m (sub K.center (0,0)))) := by
    apply (R.chart.shifted_membership ((1+m)*R.radius) R.angle m).2
    rw [mul_assoc, R.primary,mul_assoc,R.secondary]
    norm_num
  have hx (m : ℝ) : |(1+m)*localX K p|<1/2 := by
    have h := (hmem m).1
    convert h using 2
    simp only [hp,localX,circlePoint,sub,scale]
    ring
  have hy (m : ℝ) : |(1+m)*localY K p|<1/2 := by
    have h := (hmem m).2
    convert h using 2
    simp only [hp,localY,circlePoint,sub,scale]
    ring
  have hx0 : localX K p=0 := by
    by_contra hn
    have h := hx (1/localX K p-1)
    have he : (1+(1/localX K p-1))*localX K p=1 := by
      rw [show (1:ℝ)+(1/localX K p-1)=1/localX K p by ring]
      exact one_div_mul_cancel hn
    rw [he] at h
    norm_num at h
  have hy0 : localY K p=0 := by
    by_contra hn
    have h := hy (1/localY K p-1)
    have he : (1+(1/localY K p-1))*localY K p=1 := by
      rw [show (1:ℝ)+(1/localY K p-1)=1/localY K p by ring]
      exact one_div_mul_cancel hn
    rw [he] at h
    norm_num at h
  have he := frame_distance K p K.center
  have hxc : localX K K.center=0 := by simp [localX]
  have hyc : localY K K.center=0 := by simp [localY]
  rw [hxc,hyc,hx0,hy0] at he
  have hx2 : (p.1-K.center.1)^2=0 := by
    dsimp [normSq,sub] at he
    nlinarith [sq_nonneg (p.1-K.center.1),sq_nonneg (p.2-K.center.2)]
  have hy2 : (p.2-K.center.2)^2=0 := by
    dsimp [normSq,sub] at he
    nlinarith [sq_nonneg (p.1-K.center.1),sq_nonneg (p.2-K.center.2)]
  apply Prod.ext
  · linarith [sq_eq_zero_iff.1 hx2]
  · linarith [sq_eq_zero_iff.1 hy2]

lemma CentralBand.RayData.direction_of_polar {K : UnitSquare}
    (R : CentralBand.RayData K) {r β : ℝ} (hr : 0 < r)
    (hx : K.center.1=r*Real.cos β) (hy : K.center.2=r*Real.sin β) :
    R.direction=(β:Direction) := by
  have hpx := congrArg Prod.fst R.center_point
  have hpy := congrArg Prod.snd R.center_point
  simp only [circlePoint,zero_add] at hpx hpy
  have hnorm : R.radius^2=r^2 := by
    have hθ := Real.Angle.cos_sq_add_sin_sq R.direction
    have hβ := Real.sin_sq_add_cos_sq β
    rw [hx] at hpx
    rw [hy] at hpy
    nlinarith [congrArg (fun x : ℝ => x^2) hpx,
      congrArg (fun x : ℝ => x^2) hpy]
  have he : R.radius=r := by nlinarith [R.radius_pos]
  rw [he,hx] at hpx
  rw [he,hy] at hpy
  apply angle_ext <;> simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] <;> nlinarith

/-- Two disjoint squares in the disk of squared radius `q ≤ Q0` that avoid the core disk have
centre directions more than `19/25` apart. The squares need not lie on a radial boundary, and no
canonical frame is chosen. -/
theorem exterior_pair_gap {K J : UnitSquare} {q r s β γ : ℝ}
    (hq : q ≤ Q0) (hK : SqContained q K) (hJ : SqContained q J)
    (hcK : CoreAvoiding K) (hcJ : CoreAvoiding J)
    (hr : 0 < r) (hs : 0 < s)
    (hxK : K.center.1=r*Real.cos β) (hyK : K.center.2=r*Real.sin β)
    (hxJ : J.center.1=s*Real.cos γ) (hyJ : J.center.2=s*Real.sin γ)
    (hd : ∀ p,¬(openSquare K p ∧ openSquare J p)) :
    19/25 < dist (β:Direction) (γ:Direction) := by
  have hprimary (L : UnitSquare) (hc : CoreAvoiding L) :
      107/200 < max (alpha L (0,0)) (beta L (0,0)) := by
    have hdist := (coreAvoiding_iff_distance L).1 hc
    obtain ⟨hl,hsq⟩ := primary_distance_lower
      (δ := coreRadius) (by norm_num [coreRadius]) hdist
    by_contra! hbad
    dsimp [coreRadius] at hsq
    nlinarith
  obtain ⟨RK⟩ := CentralBand.ray_data_exists K (by linarith [hprimary K hcK])
  obtain ⟨RJ⟩ := CentralBand.ray_data_exists J (by linarith [hprimary J hcJ])
  have h₁ := RK.common_point_B (by rw [RK.primary_max]; exact (hprimary K hcK).le)
    (hK.mono hq)
  have h₂ := RJ.common_point_B (by rw [RJ.primary_max]; exact (hprimary J hcJ).le)
    (hJ.mono hq)
  have hh := CentralBand.closed_caps_strictly_separated h₁ h₂ hd
  rw [RK.direction_of_polar hr hxK hyK,RJ.direction_of_polar hs hxJ hyJ] at hh
  norm_num at hh
  exact hh

lemma angleGap_direction_distance (β : Vertex → ℝ) (i : Vertex)
    (hp : 0 ≤ angleGap β i) (hu : angleGap β i ≤ Real.pi) :
    dist (β i:Direction) (β (next i):Direction)=angleGap β i := by
  have he : ((angleGap β i:ℝ):Direction)=(β (next i):Direction)-(β i:Direction) := by
    by_cases hi : i=6 <;>
      simp [angleGap,hi,Real.Angle.coe_add,Real.Angle.coe_sub,Real.Angle.coe_two_pi]
  rw [dist_comm,direction_dist,← he]
  exact Real.Angle.abs_toReal_coe_eq_self_iff.2 ⟨hp,hu⟩

theorem polar_order_gap_lower {q : ℝ} (C : NeighborCycle q) (O : PolarOrder C)
    (hq : q ≤ Q0) : ∀ i,19/25 < angleGap O.beta i := by
  intro i
  have h := exterior_pair_gap hq (C.contained i) (C.contained (next i))
    (C.core i) (C.core (next i))
    (center_radius_pos (C.core i)) (center_radius_pos (C.core (next i)))
    (O.center_cos i) (O.center_sin i) (O.center_cos (next i)) (O.center_sin (next i))
    (SignedAxis.disjoint (C.feasible i))
  rwa [angleGap_direction_distance O.beta i (O.positive i).le (O.below_pi i).le] at h

theorem boundary_gap_lower {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0) :
    ∀ i,19/25 < angleGap C.beta i := by
  intro i
  have h := exterior_pair_gap hq (C.contained i) (C.contained (next i))
    (C.core i) (C.core (next i)) (C.radius_pos i) (C.radius_pos (next i))
    (C.center_cos i) (C.center_sin i) (C.center_cos (next i)) (C.center_sin (next i))
    (SignedAxis.disjoint (C.feasible i))
  rwa [angleGap_direction_distance C.beta i (C.gap_pos i).le (C.gap_lt_pi i).le] at h

lemma seven_gaps_three_quarters (β : Vertex → ℝ)
    (hgap : ∀ i,19/25 < angleGap β i) : ∀ i,angleGap β i < 3*Real.pi/4 := by
  intro i
  have hne : (Finset.univ.erase i : Finset Vertex).Nonempty :=
    ⟨i+1,Finset.mem_erase.2 ⟨by simp,Finset.mem_univ _⟩⟩
  have hh := Finset.sum_lt_sum_of_nonempty (f := fun _ => (19/25:ℝ)) (g := angleGap β)
    hne (fun j _ => hgap j)
  have hc : ((Finset.univ.erase i : Finset Vertex).card:ℝ)=6 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  rw [Finset.sum_const,nsmul_eq_mul,hc] at hh
  have hs := Finset.sum_erase_add (s := Finset.univ) (f := angleGap β) (Finset.mem_univ i)
  rw [angleGap_sum] at hs
  linarith [pi_lt_22_over_7]

theorem boundary_gap_upper {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0) :
    ∀ i,angleGap C.beta i < 3*Real.pi/4 :=
  seven_gaps_three_quarters C.beta (boundary_gap_lower C hq)

lemma dot_unit_le_radius {n p : Point} {r : ℝ}
    (hn : normSq n=1) (hr : 0 ≤ r) (hp : normSq p=r^2) : dot n p ≤ r := by
  have h := cauchy_sq n p
  rw [hn,hp,one_mul] at h
  nlinarith

lemma BoundaryCycle.radius_lt_three_halves {q : ℝ} (C : BoundaryCycle q)
    (hq : q ≤ Q0) (i : Vertex) : C.radius i < 3/2 := by
  have h := annular_center_radius_upper (C.contained i) hq
  have he : normSq (C.square i).center=C.radius i^2 := by
    have hσ : C.sigma i^2=1 := by
      rcases C.sigma_sign i with h|h <;> simp [h]
    rw [C.center_eq i]
    dsimp only [rotate,normSq]
    linear_combination (C.a i^2+C.sigma i^2*C.b i^2)*(C.square i).unit+C.b i^2*hσ-C.radius_sq i
  have hsqrt : Real.sqrt (normSq (C.square i).center)=C.radius i := by
    rw [he,Real.sqrt_sq_eq_abs,abs_of_pos (C.radius_pos i)]
  rw [hsqrt] at h
  linarith

lemma BoundaryCycle.minus_source_y_projection {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    (⟨.sourceY,.negative⟩:SignedAxis).projection (C.square i) (C.square (next i))=
      -C.radius (next i)*Real.sin (angleGap C.beta i-C.alpha i)-C.sigma i*C.b i := by
  have hlocal : frameY (C.square i) (C.square i).center= -C.sigma i*C.b i := by
    rw [C.center_eq i,frameY_rotate]
  have htarget : frameY (C.square i) (C.square (next i)).center=
      C.radius (next i)*Real.sin (angleGap C.beta i-C.alpha i) := by
    have hsin : Real.sin (angleGap C.beta i-C.alpha i)=
        Real.sin (C.beta (next i)-(C.beta i+C.alpha i)) := by
      rw [angleGap]
      split_ifs
      · rw [show C.beta (next i)-C.beta i+2*Real.pi-C.alpha i=
          C.beta (next i)-(C.beta i+C.alpha i)+2*Real.pi by ring,Real.sin_add_two_pi]
      · congr 1
        ring
    rw [hsin,Real.sin_sub,frameY,C.frame_cos i,C.frame_sin i,C.center_cos (next i),
      C.center_sin (next i)]
    simp only [BoundaryCycle.radius,BoundaryCycle.alpha,BoundaryCycle.tangent]
    ring
  rw [SignedAxis.projection_eq]
  simp only [AxisSign.value,AxisOwner.projection,frameY_sub,htarget,hlocal]
  ring

lemma BoundaryCycle.minus_target_y_projection {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    (⟨.targetY,.negative⟩:SignedAxis).projection (C.square i) (C.square (next i))=
      -C.radius i*Real.sin (angleGap C.beta i+C.alpha (next i))+C.sigma (next i)*C.b (next i) := by
  have hlocal : frameY (C.square (next i)) (C.square (next i)).center=
      -C.sigma (next i)*C.b (next i) := by rw [C.center_eq (next i),frameY_rotate]
  have hsource : frameY (C.square (next i)) (C.square i).center=
      -C.radius i*Real.sin (angleGap C.beta i+C.alpha (next i)) := by
    have hsin : Real.sin (angleGap C.beta i+C.alpha (next i))=
        Real.sin ((C.beta (next i)+C.alpha (next i))-C.beta i) := by
      rw [angleGap]
      split_ifs
      · rw [show C.beta (next i)-C.beta i+2*Real.pi+C.alpha (next i)=
          (C.beta (next i)+C.alpha (next i))-C.beta i+2*Real.pi by ring,Real.sin_add_two_pi]
      · congr 1
        ring
    rw [hsin,Real.sin_sub,frameY,C.frame_cos (next i),C.frame_sin (next i),C.center_cos i,
      C.center_sin i]
    simp only [BoundaryCycle.radius,BoundaryCycle.alpha,BoundaryCycle.tangent]
    ring
  rw [SignedAxis.projection_eq]
  simp only [AxisSign.value,AxisOwner.projection,frameY_sub,hsource,hlocal]
  ring

lemma backward_sine_lower {x : ℝ} (hx : -3/100 < x ∧ x < Real.pi) :
    -3/100 < Real.sin x := by
  by_cases hn : 0 ≤ x
  · linarith [Real.sin_nonneg_of_nonneg_of_le_pi hn hx.2.le]
  · have h := Real.sin_le (show 0 ≤ -x by linarith)
    rw [Real.sin_neg] at h
    linarith

/-- Every signed axis that separates two consecutive squares of a boundary cycle is a forward
axis. The four other signed axes are excluded one by one, so this holds when several axes
separate the same pair. -/
theorem boundary_forward_complete {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0) :
    ∀ i axis,axis.Feasible (C.square i) (C.square (next i)) →
      ∃ j : Fin 4,axis=forwardAxis j := by
  intro i axis haxis
  have hi := Candidate.canonical_bounds C hq i
  have hj := Candidate.canonical_bounds C hq (next i)
  have hri := C.radius_lt_three_halves hq i
  have hrj := C.radius_lt_three_halves hq (next i)
  have hrl := C.radius_pos i
  have hrr := C.radius_pos (next i)
  have hgap := boundary_gap_lower C hq i
  have hgapU := boundary_gap_upper C hq i
  have hai := C.alpha_range i
  have haj := C.alpha_range (next i)
  have hsin₁ := backward_sine_lower
    (x := angleGap C.beta i-C.alpha i)
    ⟨by linarith [pi_lt_22_over_7],by linarith⟩
  have hsin₂ := backward_sine_lower
    (x := angleGap C.beta i+C.alpha (next i))
    ⟨by linarith [pi_lt_22_over_7],by linarith⟩
  have hb₁ : -C.sigma i*C.b i ≤ C.b i := by
    rcases C.sigma_sign i with h|h <;> simp [h,C.b_nonneg i]
  have hb₂ : C.sigma (next i)*C.b (next i) ≤ C.b (next i) := by
    rcases C.sigma_sign (next i) with h|h <;> simp [h,C.b_nonneg (next i)]
  have hwidth := threshold_ge_one (C.square i) (C.square (next i))
  have hlow : 1 ≤ axis.projection (C.square i) (C.square (next i)) := hwidth.trans haxis
  cases axis with
  | mk owner sign =>
    cases owner <;> cases sign
    · have hdot := dot_unit_le_radius (e_unit (C.square i)) hrr.le
        (p := (C.square (next i)).center)
        (by rw [C.center_polar]; simp [normSq,scale,BoundaryCycle.ray]; nlinarith [Real.sin_sq_add_cos_sq (C.beta (next i))])
      have hlocal : dot (e (C.square i)) (C.square i).center=C.a i := by
        change frameX (C.square i) (C.square i).center=C.a i
        rw [C.center_eq,frameX_rotate]
      dsimp [SignedAxis.projection,SignedAxis.normal,AxisOwner.normal,AxisSign.value,scale,e,dot,sub] at hlow hdot hlocal
      exfalso
      linarith
    · exact ⟨3,rfl⟩
    · exact ⟨0,rfl⟩
    · rw [C.minus_source_y_projection] at hlow
      have hmul := mul_lt_mul_of_pos_left hsin₁ hrr
      exfalso
      nlinarith
    · exact ⟨1,rfl⟩
    · have hdot := dot_unit_le_radius (e_unit (C.square (next i))) hrl.le
        (p := (C.square i).center)
        (by rw [C.center_polar]; simp [normSq,scale,BoundaryCycle.ray]; nlinarith [Real.sin_sq_add_cos_sq (C.beta i)])
      have hlocal : dot (e (C.square (next i))) (C.square (next i)).center=C.a (next i) := by
        change frameX (C.square (next i)) (C.square (next i)).center=C.a (next i)
        rw [C.center_eq,frameX_rotate]
      dsimp [SignedAxis.projection,SignedAxis.normal,AxisOwner.normal,AxisSign.value,scale,e,dot,sub] at hlow hdot hlocal
      exfalso
      linarith
    · exact ⟨2,rfl⟩
    · rw [C.minus_target_y_projection] at hlow
      have hmul := mul_lt_mul_of_pos_left hsin₂ hrl
      exfalso
      nlinarith

end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate

namespace SignedPoint

def canonicalSign (p : SignedPoint) : ℝ := if 0≤p.y then 1 else -1

theorem canonicalSign_values (p : SignedPoint) :
    p.canonicalSign= -1 ∨ p.canonicalSign=1 := by
  by_cases h : 0≤p.y <;> simp [canonicalSign,h]

theorem canonicalSign_mul_abs (p : SignedPoint) :
    p.canonicalSign*|p.y|=p.y := by
  by_cases h : 0≤p.y
  · simp [canonicalSign,h,abs_of_nonneg h]
  · simp [canonicalSign,h,abs_of_neg (lt_of_not_ge h)]

def boundaryKind (q : ℝ) (p : SignedPoint) : RadialKind :=
  if p.circle=q then .outer else
    if |p.y|≤1/2 then .coreSide else .coreCorner

theorem core_primary_gt_half {p : SignedPoint} (hs : p.Sorted)
    (hc : p.Core) : 1/2<p.a := by
  by_contra! ha
  have hy : |p.y|≤1/2 := hs.2.trans ha
  unfold Core coreDistance at hc
  rw [max_eq_right (sub_nonpos.mpr ha),max_eq_right (sub_nonpos.mpr hy)] at hc
  norm_num at hc

/-- A sorted point on the boundary at the level `q` is in the boundary state of its kind: outer
when it lies on the circle of the level, even if it also lies on the core curve; on the core side
when `|y| ≤ 1/2`, the junction with the corner included; on the core corner otherwise. -/
theorem boundaryKind_spec {q : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (hb : p.Boundary q) :
    BoundaryState q (p.boundaryKind q) p.a |p.y| := by
  by_cases ho : p.circle=q
  · rw [boundaryKind,ite_eq_left ho]
    exact ho
  have hc : p.Core := hb.resolve_left ho
  have ha : 1/2<p.a := core_primary_gt_half hs hc
  unfold Core coreDistance at hc
  rw [max_eq_left (by linarith : 0≤p.a-1/2)] at hc
  by_cases hy : |p.y|≤1/2
  · rw [max_eq_right (sub_nonpos.mpr hy)] at hc
    have he : p.a=7/12 := by nlinarith
    rw [boundaryKind,ite_eq_right ho,ite_eq_left hy]
    exact ⟨he,hy⟩
  · have hy' : 1/2≤|p.y| := (lt_of_not_ge hy).le
    rw [max_eq_left (sub_nonneg.mpr hy')] at hc
    rw [boundaryKind,ite_eq_right ho,ite_eq_right hy]
    exact ⟨hy',hc⟩

theorem square_core_iff {p : SignedPoint} (hs : p.Sorted) (t : ℝ) :
    CoreAvoiding (p.square t) ↔ p.AvoidsCore := by
  rw [coreAvoiding_iff_distance]
  simp only [coreDistanceSq,square_alpha hs,square_beta,
    AvoidsCore,coreDistance,coreRadius]

end SignedPoint

namespace SignedCycle

def polarAngle (C : SignedCycle) (i : Vertex) : ℝ :=
  C.actualAngle i-C.localAngle i

theorem polarAngle_gap (C : SignedCycle) (i : Vertex) :
    angleGap C.polarAngle i=C.physicalGap i := by
  fin_cases i <;>
    simp [angleGap,polarAngle,actualAngle,physicalGap,
      Candidate.word,Candidate.offsets,Candidate.delta,next] <;> ring

theorem actualSquare_polar {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted) (i : Vertex) :
    (C.actualSquare i).center.1=
        Real.sqrt ((C.point i).a^2+|(C.point i).y|^2)*Real.cos (C.polarAngle i) ∧
      (C.actualSquare i).center.2=
        Real.sqrt ((C.point i).a^2+|(C.point i).y|^2)*Real.sin (C.polarAngle i) := by
  obtain ⟨hc,ht⟩ := arctan_polar_coordinates (b := |(C.point i).y|) (hs i).1
    (C.point i).canonicalSign_values
  rw [(C.point i).canonicalSign_mul_abs] at hc ht
  have hr : Real.sqrt ((C.point i).a^2+|(C.point i).y|^2)≠0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    nlinarith [(hs i).1,sq_nonneg |(C.point i).y|]
  constructor
  · simp only [actualSquare,SignedPoint.square,polarAngle,localAngle,Real.cos_sub]
    rw [hc,ht]
    dsimp only [actualAngle]
    field_simp [hr]
  · simp only [actualSquare,SignedPoint.square,polarAngle,localAngle,Real.sin_sub]
    rw [hc,ht]
    dsimp only [actualAngle]
    field_simp [hr]

/-- The boundary cycle of a signed cycle whose points lie on the boundary at the level `q`, with
the feasible `owner` of each edge as its witness; the owners need only be feasible. -/
def realizeBoundary {q : ℝ} (C : SignedCycle)
    (hn : C.Necessary q) (ho : C.Ordered)
    (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (hf : ∀ i,C.Feasible i (owner i)) :
    BoundaryCycle q where
  square := C.actualSquare
  contained := actualSquare_contained hn.sorted hn.contained
  core i := (SignedPoint.square_core_iff (hn.sorted i) (C.actualAngle i)).2
    (hn.core i)
  selected i := forwardAxis (owner i)
  feasible i := (C.actualSquare_feasible i (owner i)).2 (hf i)
  kind i := (C.point i).boundaryKind q
  a i := (C.point i).a
  b i := |(C.point i).y|
  sigma i := (C.point i).canonicalSign
  a_pos i := (hn.sorted i).1
  b_nonneg i := abs_nonneg _
  b_le_a i := (hn.sorted i).2
  sigma_sign i := (C.point i).canonicalSign_values
  center_eq i := by
    have h := (C.point i).square_center (C.actualAngle i)
    rw [neg_mul,(C.point i).canonicalSign_mul_abs]
    exact h
  boundary i := SignedPoint.boundaryKind_spec (hn.sorted i) (hr i)
  beta := C.polarAngle
  center_cos i := (actualSquare_polar hn.sorted i).1
  center_sin i := (actualSquare_polar hn.sorted i).2
  frame_cos i := by
    simp [actualSquare,SignedPoint.square,polarAngle,actualAngle,localAngle,
      SignedPoint.canonicalSign_mul_abs]
  frame_sin i := by
    simp [actualSquare,SignedPoint.square,polarAngle,actualAngle,localAngle,
      SignedPoint.canonicalSign_mul_abs]
  gap_pos i := by rw [polarAngle_gap]; exact ho.gap_pos i
  gap_lt_pi i := by rw [polarAngle_gap]; exact ho.gap_lt_pi i

@[simp] theorem realizeBoundary_square {q : ℝ} (C : SignedCycle)
    (hn : C.Necessary q) (ho : C.Ordered)
    (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (hf : ∀ i,C.Feasible i (owner i))
    (i : Vertex) :
    (C.realizeBoundary hn ho hr owner hf).square i=C.actualSquare i := rfl

@[simp] theorem realizeBoundary_canonicalAngle {q : ℝ} (C : SignedCycle)
    (hn : C.Necessary q) (ho : C.Ordered)
    (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (hf : ∀ i,C.Feasible i (owner i))
    (i : Vertex) :
    (C.realizeBoundary hn ho hr owner hf).canonicalAngle i=C.actualAngle i := by
  simp [BoundaryCycle.canonicalAngle,BoundaryCycle.alpha,BoundaryCycle.tangent,
    realizeBoundary,polarAngle,localAngle,SignedPoint.canonicalSign_mul_abs]

/-- For `q ≤ Q0`, the physical gaps of the signed cycle are above `19/25`, by the bound
`boundary_gap_lower` of its boundary cycle. -/
theorem realized_gap_lower {q : ℝ} (C : SignedCycle)
    (hn : C.Necessary q) (ho : C.Ordered)
    (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (hf : ∀ i,C.Feasible i (owner i))
    (hq : q≤Q0) (i : Vertex) : 19/25<C.physicalGap i := by
  have h := boundary_gap_lower (C.realizeBoundary hn ho hr owner hf) hq i
  simpa only [realizeBoundary,polarAngle_gap] using h

/-- For `q ≤ Q0`, a strict spread and `C.theta A = 0`, the frame angles of the signed cycle form
a candidate frame of its boundary cycle. -/
def realizedFrame {q : ℝ} (C : SignedCycle)
    (hn : C.Necessary q) (ho : C.Ordered)
    (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (hf : ∀ i,C.Feasible i (owner i))
    (hq : q≤Q0) (hs : C.StrictSpread) (hA : C.theta A=0) :
    Candidate.Frame (C.realizeBoundary hn ho hr owner hf) where
  theta := C.theta
  theta_A := hA
  canonical_eq i := C.realizeBoundary_canonicalAngle hn ho hr owner hf i
  spread := hs
  gap_lower := boundary_gap_lower _ hq
  gap_upper := boundary_gap_upper _ hq
  forward_complete := boundary_forward_complete _ hq

/-- A forward axis separates two consecutive squares of the boundary cycle exactly when it is
feasible on the signed cycle; ties are kept. -/
theorem realizeBoundary_feasible_iff {q : ℝ} (C : SignedCycle)
    (hn : C.Necessary q) (ho : C.Ordered)
    (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (hf : ∀ i,C.Feasible i (owner i))
    (i : Vertex) (j : Fin 4) :
    (forwardAxis j).Feasible
      ((C.realizeBoundary hn ho hr owner hf).square i)
      ((C.realizeBoundary hn ho hr owner hf).square (next i)) ↔ C.Feasible i j :=
  C.actualSquare_feasible i j

end SignedCycle
end SquaresInCircles.Eight
end
end
end
