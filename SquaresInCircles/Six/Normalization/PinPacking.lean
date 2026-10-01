import SquaresInCircles.Six.Normalization.StrongCore
import SquaresInCircles.Six.Normalization.PinCounting
import SquaresInCircles.Six.Analytic.PinWindows
import SquaresInCircles.Six.CongruenceTools

/-!
# The pin-labelled packing

A `PinPacking` is a packing about the origin in the frame of its central square,
whose centre lies in the box `[0, c0]²`; the other five squares are labelled E,
N, W, D and S by the fixed pins they hold. Each of them holds its own pin, has
its phase in the window of its label, and is separated from the central square
along one of the axes allowed for its label. Every packing in a disk of squared
radius at most `Q0` is congruent to one. Each exterior square holds a pin, and
disjoint squares cannot share one, so each holds exactly one pin, which gives
its label; holding no other pin puts its phase in the window, and the
coordinates of the pins give the allowed axes.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

/-- The central square, followed by E, N, W, D and S. -/
def pinModel (c : Point) (t a b : Fin 5 → ℝ) : Fin 6 → UnitSquare :=
  Fin.cases (axisSquare c) (fun i => orientedSquare (t i) (a i) (b i))

@[simp] lemma pinModel_zero (c : Point) (t a b : Fin 5 → ℝ) :
    pinModel c t a b 0 = axisSquare c := rfl

@[simp] lemma pinModel_succ (c : Point) (t a b : Fin 5 → ℝ) (i : Fin 5) :
    pinModel c t a b i.succ = orientedSquare (t i) (a i) (b i) := rfl

/-- The real lift of a direction within `π` of `c`. -/
def liftNear (c : ℝ) (m : Direction) : ℝ := c+(m-(c:Direction)).toReal

lemma liftNear_class (c : ℝ) (m : Direction) : (liftNear c m : Direction) = m := by
  simp only [liftNear,Real.Angle.coe_add,Real.Angle.coe_toReal]
  abel

lemma liftNear_range (c : ℝ) (m : Direction) :
    -Real.pi ≤ liftNear c m-c ∧ liftNear c m-c ≤ Real.pi := by
  dsimp [liftNear]
  exact ⟨by linarith [(m-(c:Direction)).neg_pi_lt_toReal],
    by linarith [(m-(c:Direction)).toReal_le_pi]⟩

structure PinPacking (R : ℝ) where
  center : Point
  phase : Fin 5 → ℝ
  radial : Fin 5 → ℝ
  transverse : Fin 5 → ℝ
  packing : Packing (pinModel center phase radial transverse) (0,0) R
  box : (0 ≤ center.1 ∧ center.1 ≤ c0) ∧ (0 ≤ center.2 ∧ center.2 ≤ c0)
  contained : ∀ i, ContainedChart (radial i) |transverse i|
  avoidsCore : ∀ i, AvoidsCore (radial i) |transverse i|
  pin : ∀ i, openSquare (orientedSquare (phase i) (radial i) (transverse i)) (fixedPin i)
  window : ∀ i, (windowLower i : ℝ) < phase i-phaseCenter i ∧
    phase i-phaseCenter i < (windowUpper i : ℝ)
  separator : ∀ i, ∃ k, 0 ≤ centralMargin k (phase i) (radial i) (transverse i) center.1 center.2
  allowed_separator : ∀ i k,
    0 ≤ centralMargin k (phase i) (radial i) (transverse i) center.1 center.2 → k ∈ allowed i

namespace PinPacking
variable {R : ℝ} (P : PinPacking R)

def model : Fin 6 → UnitSquare := pinModel P.center P.phase P.radial P.transverse

lemma exterior_disjoint : InteriorDisjoint
    (fun i : Fin 5 => orientedSquare (P.phase i) (P.radial i) (P.transverse i)) := by
  intro i j hij
  exact P.packing.disjoint i.succ j.succ ((Fin.succ_injective _).ne hij)

end PinPacking

/-- A packing about the origin whose square `0` is axis-parallel, contains the
origin and has its centre in the closed first quadrant is congruent to a
pin-labelled packing. -/
theorem pinPacking_of_normalized {S : Fin 6 → UnitSquare} {c : Point} {R : ℝ}
    (hp : Packing S (0,0) R) (hQ : R^2 ≤ Q0) (haxis : S 0 = axisSquare c)
    (hinside : openSquare (S 0) (0,0)) (hx0 : 0 ≤ c.1) (hy0 : 0 ≤ c.2) :
    ∃ P : PinPacking R, Congruent S (0,0) P.model := by
  classical
  have hhalf : |c.1| < 1/2 ∧ |c.2| < 1/2 := by
    simpa [haxis,axisSquare_open,openAxisSquare,abs_neg] using hinside
  have hcore := strong_central_box hp hQ (fun p => by rw [haxis]) hx0 hy0
    ((le_abs_self c.1).trans_lt hhalf.1) ((le_abs_self c.2).trans_lt hhalf.2)
  have hCcore : alpha (S 0) (0,0) ≤ c0 ∧ beta (S 0) (0,0) ≤ c0 := by
    simpa [haxis,alpha,beta,localX,localY,axisSquare,abs_neg,
      abs_of_nonneg hx0,abs_of_nonneg hy0] using hcore
  let F : Fin 5 → UnitSquare := fun i => S i.succ
  have hFdisj : InteriorDisjoint F :=
    fun i j hij => hp.disjoint i.succ j.succ ((Fin.succ_injective _).ne hij)
  have hout (i : Fin 5) : ¬ openSquare (F i) (0,0) := by
    intro hi
    exact hp.disjoint i.succ 0 (by intro he; have hh := congrArg Fin.val he; simp at hh)
      (0,0) ⟨hi,hinside⟩
  choose C hsorted using fun i : Fin 5 => sorted_square_chart (F i) (0,0)
  have hc (i : Fin 5) : ContainedChart (C i).a |(C i).signedB| :=
    chart_signed_containment (C i) (hsorted i) (hout i) ((hp.phi_le i.succ).trans hQ)
  have hav (i : Fin 5) : AvoidsCore (C i).a |(C i).signedB| := by
    rw [signedB_abs]
    apply avoidsCore_of_disjoint (C i) (hsorted i) (hout i) hCcore
    exact hp.disjoint i.succ 0 (by intro he; have hh := congrArg Fin.val he; simp at hh)
  have hsat (i : Fin 5) (t : ℝ) (ht : (t:Direction)=(C i).phase) :
      ∃ k, 0 ≤ centralMargin k t (C i).a (C i).signedB c.1 c.2 := by
    apply central_separators_complete (hc i).half_le hx0 hy0
      (by linarith [hcore.1,c0_lt_23_200]) (by linarith [hcore.2,c0_lt_23_200])
    intro p hh
    exact hp.disjoint 0 i.succ
      (by intro he; have hh := congrArg Fin.val he; simp at hh) p
      ⟨by simpa [haxis] using hh.1,(chart_same_open_oriented (C i) ht p).mpr hh.2⟩
  have hcover (i : Fin 5) : ∃ j, openSquare (F i) (fixedPin j) := by
    let t := (C i).phase.toReal
    have ht : (t:Direction)=(C i).phase := Real.Angle.coe_toReal _
    obtain ⟨j,hj⟩ := Analytic.five_pin_cover (hc i) (hav i)
      hx0 hy0 hcore.1 hcore.2 (hsat i t ht)
    exact ⟨j,(chart_same_open_oriented (C i) ht _).mpr hj⟩
  obtain ⟨σ,hσ⟩ := pin_labels_of_covering F fixedPin hFdisj hcover
  let t : Fin 5 → ℝ := fun i => liftNear (phaseCenter i) (C (σ i)).phase
  let a : Fin 5 → ℝ := fun i => (C (σ i)).a
  let b : Fin 5 → ℝ := fun i => (C (σ i)).signedB
  have ht (i : Fin 5) : (t i:Direction)=(C (σ i)).phase := liftNear_class _ _
  have hsame (i : Fin 5) (p : Point) :
      openSquare (F (σ i)) p ↔ openSquare (orientedSquare (t i) (a i) (b i)) p :=
    chart_same_open_oriented (C (σ i)) (ht i) p
  have hpin (i : Fin 5) : openSquare (orientedSquare (t i) (a i) (b i)) (fixedPin i) :=
    (hsame i _).mp (hσ i).1
  have huniq (i j : Fin 5)
      (hj : openSquare (orientedSquare (t i) (a i) (b i)) (fixedPin j)) : j=i :=
    (hσ i).2.2 j ((hsame i (fixedPin j)).mpr hj)
  have hwin (i : Fin 5) : (windowLower i:ℝ)<t i-phaseCenter i ∧
      t i-phaseCenter i<(windowUpper i:ℝ) :=
    Analytic.labelled_window i (hc (σ i)) (hav (σ i)) hx0 hy0 hcore.1 hcore.2
      (hsat (σ i) (t i) (ht i)) (liftNear_range _ _) (huniq i)
  let τ := Six.extendExteriorPerm σ
  have hmodelopen (i : Fin 6) (p : Point) :
      openSquare (pinModel c t a b i) p ↔ openSquare (S (τ i)) p := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [τ,haxis]
    · exact (hsame j p).symm
  have hmodelclosed (i : Fin 6) (p : Point) :
      closedSquare (pinModel c t a b i) p ↔ closedSquare (S (τ i)) p :=
    same_open_same_closed _ _ (hmodelopen i) p
  have hpack : Packing (pinModel c t a b) (0,0) R :=
    Six.packing_of_same_sets (Six.packing_relabel hp τ) hmodelopen hmodelclosed
  let P : PinPacking R := {
    center := c
    phase := t
    radial := a
    transverse := b
    packing := hpack
    box := ⟨⟨hx0,hcore.1⟩,⟨hy0,hcore.2⟩⟩
    contained := fun i => hc (σ i)
    avoidsCore := fun i => hav (σ i)
    pin := hpin
    window := hwin
    separator := fun i => hsat (σ i) (t i) (ht i)
    allowed_separator := fun i k hk =>
      Analytic.allowed_axis_of_pin i (hc (σ i)) (hav (σ i))
        hx0 hy0 hcore.1 hcore.2 (hpin i) k hk }
  refine ⟨P,?_⟩
  exact Six.congruent_of_origin_sets τ (fun i p => (hmodelopen i p).symm)
    (fun i p => (hmodelclosed i p).symm)

/-- Every packing in a disk of squared radius at most `Q0` is congruent to a
pin-labelled packing. -/
theorem pinPacking_of_ceiling {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hQ : R^2 ≤ Q0) :
    ∃ P : PinPacking R, Congruent S o P.model := by
  obtain ⟨F⟩ := Six.normalize_frame_of_ceiling hp hQ
  obtain ⟨P,hP⟩ := pinPacking_of_normalized F.packing hQ F.central_eq F.central_inside
    F.cx_nonneg F.cy_nonneg
  exact ⟨P,Six.congruent_trans F.congruent hP⟩

end SquaresInCircles.Six.Normalization
