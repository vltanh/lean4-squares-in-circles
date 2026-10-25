module

public import SquaresInCircles.Eight.TableFree.PhysicalCycle
public import SquaresInCircles.Eight.BoundaryGeometry

/-!
# Realizing an actual signed boundary descendant

Uncompiled source draft. A signed cycle with true radial boundary states,
positive physical winding gaps and genuine weak neighboring separators is
converted to `BoundaryCycle` at the very same squared radius. The original
signed point and physical square are retained exactly. This lets geometric
boundary theorems apply to a transport descendant without assuming it was
already a normalized boundary record.

The construction does not itself prove a particular owner restriction or
exclude a nearest-axis tie. Those remain separate geometric assertions.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
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

/-- The side/corner junction stays weak. An outer/core intersection is
recorded as outer, with its actual outer radius unchanged. -/
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

/-- This conversion requires actual neighboring slacks, not a conclusion
about their owners. In particular it applies to endpoint states before
the desired global owner classification has been proved. -/
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

/-- The stronger physical gap follows afresh from genuine endpoint squares.
It need not be copied from their source before a G/T motion. -/
theorem realized_gap_lower {q : ℝ} (C : SignedCycle)
    (hn : C.Necessary q) (ho : C.Ordered)
    (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (hf : ∀ i,C.Feasible i (owner i))
    (hq : q≤Q0) (i : Vertex) : 19/25<C.physicalGap i := by
  have h := boundary_gap_lower (C.realizeBoundary hn ho hr owner hf) hq i
  simpa only [realizeBoundary,polarAngle_gap] using h

/-- If the supplied A frame is normalized, the boundary record keeps that
same normalized real frame. No subsequent rotation is inserted. -/
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

/-- Every original scalar owner, including simultaneous weak ties, has
exactly the same feasibility after this realization. -/
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
end SquaresInCircles.Eight.TableFree
