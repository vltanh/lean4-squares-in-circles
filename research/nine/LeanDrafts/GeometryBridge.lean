import SquaresInCircles.Common.Separation
import SquaresInCircles.Common.Frames
import research.nine.LeanDrafts.FiveCoreCapacityData

/-!
# Original Packing to the concrete five-core capacity certificate

UNCOMPILED DRAFT. This file uses the repository's original `UnitSquare`,
`closedSquare`, `openSquare` and `Packing` definitions, read at input commit
71d385e75adc1f5183d35a92dbe18c208dc32f2a. It does not replace their semantics.

The last theorem assumes an actual Packing of nine squares, R² ≤ 1105/256,
an index relabeling, four-corner relabelings, and the five reference-vertex
neighborhoods. It DERIVES center bounds, pairwise center separation, actual
witness membership, and actual witness separation. Thus only the substantive
five-core-neighborhood premise remains to be proved by the D02 argument.

No Lean executable was available. Build, axiom output, and independent replay
remain required. No `sorry`, custom axiom, native reduction, or external proof
oracle is used in these proposed proof terms.
-/

noncomputable section

namespace SquaresInCircles.Nine.GeometryBridgeDraft

open CenterCapacityDraft FiveCoreCapacityDraft

theorem sqdist_eq_normSq (p q : Point) : sqdist p q = normSq (sub p q) := rfl

theorem sqdist_comm (p q : Point) : sqdist p q = sqdist q p := by
  dsimp [sqdist]
  ring

theorem sqdist_translate (p q o : Point) :
    sqdist (sub p o) (sub q o) = sqdist p q := by
  dsimp [sqdist, sub]
  ring

/-- A uniform strict center bound, even at the target radius. The scalar
margin is (91/60)² + 91/60 + 1/2 - 1105/256 = 31/57600. -/
theorem packing_center_bound {n : Nat} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hq : R ^ 2 ≤ (1105 : ℝ) / 256) (i : Fin n) :
    normSq (sub (S i).center o) < ((91 : ℝ) / 60) ^ 2 := by
  rw [local_center_norm]
  have ha := alpha_nonneg (S i) o
  have hb := beta_nonneg (S i) o
  have hphi := (hp.phi_le i).trans hq
  by_contra! hn
  have hsum : alpha (S i) o + beta (S i) o < (91 : ℝ) / 60 := by
    dsimp [phi] at hphi
    nlinarith
  have hplus : 0 < (91 : ℝ) / 60 + alpha (S i) o + beta (S i) o := by linarith
  have hproduct := mul_pos (sub_pos.mpr hsum) hplus
  nlinarith [mul_nonneg ha hb]

/-- Two different actual unit squares have center distance at least one:
otherwise their midpoint is interior to both inscribed half-unit disks. -/
theorem packing_center_separation {n : Nat} {S : Fin n → UnitSquare}
    {o : Point} {R : ℝ} (hp : Packing S o R) (i j : Fin n) (hij : i ≠ j) :
    1 ≤ sqdist (S i).center (S j).center := by
  by_contra! hn
  let m : Point := (((S i).center.1 + (S j).center.1) / 2,
                    ((S i).center.2 + (S j).center.2) / 2)
  have hleft : 4 * normSq (sub m (S i).center) = sqdist (S i).center (S j).center := by
    dsimp [m, normSq, sub, sqdist]
    ring
  have hright : 4 * normSq (sub m (S j).center) = sqdist (S i).center (S j).center := by
    dsimp [m, normSq, sub, sqdist]
    ring
  have hi : openSquare (S i) m := small_disk_in_openSquare (S i) (by nlinarith)
  have hj : openSquare (S j) m := small_disk_in_openSquare (S j) (by nlinarith)
  exact hp.disjoint i j hij m ⟨hi, hj⟩

/-- Every point of one CLOSED core square stays at least a half-unit from a
different square's center. This retains all weak core boundary contacts. -/
theorem packing_closed_point_separation {n : Nat} {S : Fin n → UnitSquare}
    {o : Point} {R : ℝ} (hp : Packing S o R) (i j : Fin n) (hij : i ≠ j)
    (p : Point) (hclosed : closedSquare (S i) p) :
    (1 : ℝ) / 4 ≤ sqdist (S j).center p := by
  by_contra! hn
  have hnear : normSq (sub p (S j).center) < (1 : ℝ) / 4 := by
    rw [← sqdist_eq_normSq, sqdist_comm]
    exact hn
  have hopen := small_disk_in_openSquare (S j) hnear
  exact closed_open_disjoint (S i) (S j) (hp.disjoint i j hij) hclosed hopen

/-- Four actual corners in cyclic order. A separate finite permutation may
reverse or rotate their labels to match a certificate's reference vertices. -/
def corners (S : UnitSquare) : Fin 4 → Point :=
  ![add S.center (rotate S (-(1/2), -(1/2))),
    add S.center (rotate S (1/2, -(1/2))),
    add S.center (rotate S (1/2, 1/2)),
    add S.center (rotate S (-(1/2), 1/2))]

theorem corner_closed (S : UnitSquare) (i : Fin 4) : closedSquare S (corners S i) := by
  fin_cases i <;>
    norm_num [corners, closedSquare, localX_rotated, localY_rotated]

theorem lerp_smul (t : ℝ) (p q : Point) : lerp t p q = (1-t) • p + t • q := by
  ext <;> rfl

theorem abs_lerp_half {a b t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : |a| ≤ 1/2) (hb : |b| ≤ 1/2) : |(1-t)*a+t*b| ≤ 1/2 := by
  have ht : 0 ≤ 1-t := sub_nonneg.mpr ht1
  calc
    |(1-t)*a+t*b| ≤ |(1-t)*a|+|t*b| := abs_add_le _ _
    _ = (1-t)*|a|+t*|b| := by rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg ht0]
    _ ≤ (1-t)*(1/2)+t*(1/2) :=
      add_le_add (mul_le_mul_of_nonneg_left ha ht) (mul_le_mul_of_nonneg_left hb ht0)
    _ = 1/2 := by ring

theorem closedSquare_lerp (S : UnitSquare) (p q : Point) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : closedSquare S p) (hq : closedSquare S q) : closedSquare S (lerp t p q) := by
  obtain ⟨hx, hy⟩ := local_affine S p q (sub_add_cancel 1 t)
  rw [lerp_smul]
  constructor
  · rw [hx]
    exact abs_lerp_half ht0 ht1 hp.1 hq.1
  · rw [hy]
    exact abs_lerp_half ht0 ht1 hp.2 hq.2

/-- A bilinear witness is in the ACTUAL closed square, regardless of how the
four actual corners were relabeled. No reference polygon is treated as real. -/
theorem corner_witness_closed (S : UnitSquare) (labels : Equiv.Perm (Fin 4))
    (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    closedSquare S (witness (fun k => corners S (labels k)) u v) := by
  apply closedSquare_lerp S _ _ v hv0 hv1
  · exact closedSquare_lerp S _ _ u hu0 hu1 (corner_closed S _) (corner_closed S _)
  · exact closedSquare_lerp S _ _ u hu0 hu1 (corner_closed S _) (corner_closed S _)

theorem lerp_translate (t : ℝ) (p q o : Point) :
    lerp t (sub p o) (sub q o) = sub (lerp t p q) o := by
  ext <;> dsimp [lerp, sub] <;> ring

theorem witness_translate (v : Fin 4 → Point) (o : Point) (s t : ℝ) :
    witness (fun i => sub (v i) o) s t = sub (witness v s t) o := by
  simp only [witness, lerp_translate]

def firstFive (i : Fin 5) : Fin 9 := ⟨i.val, by omega⟩
def lastFour (i : Fin 4) : Fin 9 := ⟨5 + i.val, by omega⟩

theorem lastFour_injective : Function.Injective lastFour := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  dsimp [lastFour] at h
  omega

theorem firstFive_ne_lastFour (i : Fin 5) (j : Fin 4) : firstFive i ≠ lastFour j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [firstFive, lastFour] at hv
  omega

/-- Complete physical entry to the version-one capacity certificate. All nine
original squares are present. The five-core vertex neighborhood is the only
extra geometric premise; every capacity, incircle and center premise is proved
from the original Packing. Reversals of individual corner order are allowed. -/
theorem five_core_neighborhood_excludes_packing
    (S : Fin 9 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) (hq : R ^ 2 ≤ (1105 : ℝ) / 256)
    (σ : Equiv.Perm (Fin 9)) (labels : Fin 5 → Equiv.Perm (Fin 4))
    (hvertex : ∀ k v,
      sqdist (referenceVertices k v)
        (sub (corners (S (σ (firstFive k))) (labels k v)) o) ≤ (1 : ℝ) / 625) : False := by
  let actual : Fin 5 → Fin 4 → Point := fun k v =>
    sub (corners (S (σ (firstFive k))) (labels k v)) o
  let extra : Fin 4 → Point := fun i => sub (S (σ (lastFour i))).center o
  apply no_four_from_vertex_neighborhood actual extra hvertex
  · intro i
    have hb := packing_center_bound hp hq (σ (lastFour i))
    simpa [extra, sqdist, normSq, sub] using hb
  · intro i j hij
    have hindex : σ (lastFour i) ≠ σ (lastFour j) := by
      intro h
      exact hij (lastFour_injective (σ.injective h))
    change 1 ≤ sqdist (sub (S (σ (lastFour i))).center o)
      (sub (S (σ (lastFour j))).center o)
    rw [sqdist_translate]
    exact packing_center_separation hp _ _ hindex
  · intro i w
    have hindex : σ (firstFive w.core) ≠ σ (lastFour i) := by
      intro h
      exact firstFive_ne_lastFour w.core i (σ.injective h)
    rcases grid_weight_bounds w.u with ⟨hu0, hu1⟩
    rcases grid_weight_bounds w.v with ⟨hv0, hv1⟩
    have hclosed := corner_witness_closed (S (σ (firstFive w.core))) (labels w.core)
      ((w.u.val : ℝ) / 8) ((w.v.val : ℝ) / 8) hu0 hu1 hv0 hv1
    have hsep := packing_closed_point_separation hp _ _ hindex _ hclosed
    change (1 : ℝ) / 4 ≤ sqdist (sub (S (σ (lastFour i))).center o)
      (witness (fun v => sub (corners (S (σ (firstFive w.core))) (labels w.core v)) o)
        ((w.u.val : ℝ) / 8) ((w.v.val : ℝ) / 8))
    rw [witness_translate, sqdist_translate]
    exact hsep

/-- The same physical theorem in an arbitrary original chart at the disk
center. The chart uses the repository's existing packing-preserving pullback. -/
theorem rotated_five_core_neighborhood_excludes_packing
    (S : Fin 9 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) (hq : R ^ 2 ≤ (1105 : ℝ) / 256) (φ : Direction)
    (σ : Equiv.Perm (Fin 9)) (labels : Fin 5 → Equiv.Perm (Fin 4))
    (hvertex : ∀ k v,
      sqdist (referenceVertices k v)
        (corners (pullSquare o φ (S (σ (firstFive k)))) (labels k v)) ≤ (1 : ℝ) / 625) : False := by
  apply five_core_neighborhood_excludes_packing (fun i => pullSquare o φ (S i))
    (0, 0) R (packing_pull hp φ) hq σ labels
  intro k v
  simpa [sub] using hvertex k v

#print axioms packing_center_bound
#print axioms packing_center_separation
#print axioms packing_closed_point_separation
#print axioms five_core_neighborhood_excludes_packing
#print axioms rotated_five_core_neighborhood_excludes_packing

end SquaresInCircles.Nine.GeometryBridgeDraft
