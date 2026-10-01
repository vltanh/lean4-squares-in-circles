import SquaresInCircles.Six.Normalization.PinPacking

/-!
# The single global diagonal normalization

The reflection swaps E/N and W/S and fixes D. Its point-set identities preserve
the pins, windows and strong central box. Allowed axes are rederived from the
analytic fixed-pin coordinate lemma, without invoking any window certificate.
The returned congruence records the reflection rather than treating it as a
rotation. The final candidate symmetry must absorb this recorded case later.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

/-- E/N and W/S are exchanged; D is fixed. -/
def mirrorPin : Equiv.Perm (Fin 5) where
  toFun := ![1,0,4,3,2]
  invFun := ![1,0,4,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] lemma mirrorPin_twice (i : Fin 5) : mirrorPin (mirrorPin i) = i := by
  fin_cases i <;> rfl

def pinAngle : Fin 5 → ℝ :=
  ![0,Real.pi/2,(11/12)*Real.pi,(5/4)*Real.pi,(19/12)*Real.pi]

lemma fixedPin_polar (i : Fin 5) :
    fixedPin i = ((9/10)*Real.cos (pinAngle i),(9/10)*Real.sin (pinAngle i)) := by
  fin_cases i <;> simp [fixedPin,pinAngle]

lemma mirror_pin_angle (i : Fin 5) :
    (pinAngle (mirrorPin i) : Direction) = (Real.pi/2-pinAngle i : ℝ) := by
  apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
  fin_cases i
  · exact ⟨0,by norm_num [pinAngle,mirrorPin]⟩
  · exact ⟨0,by norm_num [pinAngle,mirrorPin]⟩
  · exact ⟨1,by dsimp [pinAngle,mirrorPin]; ring⟩
  · exact ⟨1,by dsimp [pinAngle,mirrorPin]; ring⟩
  · exact ⟨1,by dsimp [pinAngle,mirrorPin]; ring⟩

lemma fixedPin_diagonal (i : Fin 5) : Six.diagonalPoint (fixedPin i) = fixedPin (mirrorPin i) := by
  have hc := congrArg (fun z : Direction => z.cos) (mirror_pin_angle i)
  have hs := congrArg (fun z : Direction => z.sin) (mirror_pin_angle i)
  simp only [Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub] at hc hs
  rw [fixedPin_polar,fixedPin_polar]
  apply Prod.ext <;> simp only [Six.diagonalPoint,hc,hs]

/-- The real lifts return to the same labelled windows after reflection. -/
def mirroredPhase (i : Fin 5) (t : ℝ) : ℝ :=
  Real.pi/2-t + if i=0 ∨ i=1 then 0 else 2*Real.pi

lemma mirroredPhase_class (i : Fin 5) (t : ℝ) :
    (mirroredPhase i t : Direction) = (Real.pi/2-t : ℝ) := by
  unfold mirroredPhase
  split_ifs <;> simp [Real.Angle.coe_add]

lemma oriented_phase_open {t T a b : ℝ} (ht : (t:Direction)=(T:Direction)) (p : Point) :
    openSquare (orientedSquare t a b) p ↔ openSquare (orientedSquare T a b) p := by
  have hc := congrArg (fun z : Direction => z.cos) ht
  have hs := congrArg (fun z : Direction => z.sin) ht
  simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] at hc hs
  simp only [openSquare,orientedSquare_localX,orientedSquare_localY,hc,hs]

lemma oriented_diagonal_open (t a b : ℝ) (p : Point) :
    openSquare (orientedSquare (Real.pi/2-t) a (-b)) p ↔
      openSquare (orientedSquare t a b) (Six.diagonalPoint p) := by
  have hx : localX (orientedSquare (Real.pi/2-t) a (-b)) p =
      localX (orientedSquare t a b) (Six.diagonalPoint p) := by
    simp only [orientedSquare_localX,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
      Six.diagonalPoint]
    ring
  have hy : localY (orientedSquare (Real.pi/2-t) a (-b)) p =
      -localY (orientedSquare t a b) (Six.diagonalPoint p) := by
    simp only [orientedSquare_localY,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
      Six.diagonalPoint]
    ring
  simp only [openSquare,hx,hy,abs_neg]

lemma mirrored_oriented_open (i : Fin 5) (t a b : ℝ) (p : Point) :
    openSquare (orientedSquare (mirroredPhase i t) a (-b)) p ↔
      openSquare (orientedSquare t a b) (Six.diagonalPoint p) :=
  (oriented_phase_open (mirroredPhase_class i t) p).trans (oriented_diagonal_open t a b p)

lemma mirrored_window {R : ℝ} (P : PinPacking R) (i : Fin 5) :
    (windowLower i : ℝ) < mirroredPhase i (P.phase (mirrorPin i))-phaseCenter i ∧
      mirroredPhase i (P.phase (mirrorPin i))-phaseCenter i < (windowUpper i : ℝ) := by
  have h := P.window (mirrorPin i)
  fin_cases i <;> norm_num [mirroredPhase,mirrorPin,phaseCenter,windowLower,windowUpper] at * <;>
    constructor <;> linarith [h.1,h.2]

/-- Reflect a pin packing with explicit transformed coordinates and labels. -/
def PinPacking.mirror {R : ℝ} (P : PinPacking R) : PinPacking R := by
  classical
  let c := Six.diagonalPoint P.center
  let t : Fin 5 → ℝ := fun i => mirroredPhase i (P.phase (mirrorPin i))
  let a : Fin 5 → ℝ := fun i => P.radial (mirrorPin i)
  let b : Fin 5 → ℝ := fun i => -P.transverse (mirrorPin i)
  let τ := Six.extendExteriorPerm mirrorPin
  have hopen (i : Fin 6) (p : Point) :
      openSquare (pinModel c t a b i) p ↔
        openSquare (Six.reflectDiagonalSquare (P.model (τ i))) p := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [pinModel_zero,τ,Six.extendExteriorPerm_zero,PinPacking.model,
        Six.reflectDiagonal_open]
      exact (Six.diagonal_axis_open P.center p).symm
    · rw [pinModel_succ,Six.reflectDiagonal_open]
      exact mirrored_oriented_open j _ _ _ p
  have hclosed (i : Fin 6) (p : Point) :
      closedSquare (pinModel c t a b i) p ↔
        closedSquare (Six.reflectDiagonalSquare (P.model (τ i))) p :=
    same_open_same_closed _ _ (hopen i) p
  have hp : Packing (pinModel c t a b) (0,0) R :=
    Six.packing_of_same_sets
      (Six.packing_relabel (Six.packing_reflectDiagonal P.packing) τ) hopen hclosed
  have hbox : (0 ≤ c.1 ∧ c.1 ≤ c0) ∧ (0 ≤ c.2 ∧ c.2 ≤ c0) := ⟨P.box.2,P.box.1⟩
  have hcontained (i : Fin 5) : ContainedChart (a i) |b i| := by
    simpa [a,b,abs_neg] using P.contained (mirrorPin i)
  have havoids (i : Fin 5) : AvoidsCore (a i) |b i| := by
    simpa [a,b,abs_neg] using P.avoidsCore (mirrorPin i)
  have hpin (i : Fin 5) : openSquare (orientedSquare (t i) (a i) (b i)) (fixedPin i) := by
    apply (mirrored_oriented_open i _ _ _ _).mpr
    rw [fixedPin_diagonal]
    exact P.pin (mirrorPin i)
  have hwindow (i : Fin 5) : (windowLower i:ℝ) < t i-phaseCenter i ∧
      t i-phaseCenter i < (windowUpper i:ℝ) := mirrored_window P i
  have hsat (i : Fin 5) : ∃ k, 0 ≤ centralMargin k (t i) (a i) (b i) c.1 c.2 := by
    apply central_separators_complete (hcontained i).half_le hbox.1.1 hbox.2.1
      (by linarith [hbox.1.2,c0_lt_23_200]) (by linarith [hbox.2.2,c0_lt_23_200])
    exact hp.disjoint 0 i.succ (by intro he; have hh := congrArg Fin.val he; simp at hh)
  exact {
    center := c, phase := t, radial := a, transverse := b,
    packing := hp, box := hbox, contained := hcontained, avoidsCore := havoids,
    pin := hpin, window := hwindow, separator := hsat,
    allowed_separator := fun i k hk =>
      Analytic.allowed_axis_of_pin i (hcontained i) (havoids i)
        hbox.1.1 hbox.2.1 hbox.1.2 hbox.2.2 (hpin i) k hk }

lemma PinPacking.mirror_open {R : ℝ} (P : PinPacking R) (i : Fin 6) (p : Point) :
    openSquare (P.mirror.model i) p ↔
      openSquare (Six.reflectDiagonalSquare (P.model (Six.extendExteriorPerm mirrorPin i))) p := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change openSquare (axisSquare (Six.diagonalPoint P.center)) p ↔
      openSquare (Six.reflectDiagonalSquare (axisSquare P.center)) p
    rw [Six.reflectDiagonal_open]
    exact (Six.diagonal_axis_open P.center p).symm
  · change openSquare (orientedSquare (mirroredPhase j (P.phase (mirrorPin j)))
      (P.radial (mirrorPin j)) (-P.transverse (mirrorPin j))) p ↔
      openSquare (Six.reflectDiagonalSquare
        (orientedSquare (P.phase (mirrorPin j)) (P.radial (mirrorPin j))
          (P.transverse (mirrorPin j)))) p
    rw [Six.reflectDiagonal_open]
    exact mirrored_oriented_open j _ _ _ p

/-- Reflecting the reflected labelled model recovers the original point sets,
up to the recorded pin permutation. -/
lemma PinPacking.congruent_reflected_mirror {R : ℝ} (P : PinPacking R) :
    Congruent P.model (0,0) (fun i => Six.reflectDiagonalSquare (P.mirror.model i)) := by
  let τ := Six.extendExteriorPerm mirrorPin
  have ho (i : Fin 6) (p : Point) :
      openSquare (P.model (τ i)) p ↔
        openSquare (Six.reflectDiagonalSquare (P.mirror.model i)) p := by
    rw [Six.reflectDiagonal_open,P.mirror_open,Six.reflectDiagonal_open,
      Six.diagonalPoint_involutive]
  exact Six.congruent_of_origin_sets τ ho
    (fun i => same_open_same_closed _ _ (ho i))

/-- The possible reflection is retained explicitly for the final equality argument. -/
def CongruentOrDiagonal {n : ℕ} (S : Fin n → UnitSquare) (o : Point)
    (M : Fin n → UnitSquare) : Prop :=
  Congruent S o M ∨ Congruent S o (fun i => Six.reflectDiagonalSquare (M i))

theorem normalize_D_half {R : ℝ} (P : PinPacking R) :
    ∃ Q : PinPacking R, Q.phase 3 ≤ 5*Real.pi/4 ∧ CongruentOrDiagonal P.model (0,0) Q.model := by
  by_cases h : P.phase 3 ≤ 5*Real.pi/4
  · exact ⟨P,h,Or.inl (Six.congruent_refl P.model)⟩
  · refine ⟨P.mirror,?_,Or.inr P.congruent_reflected_mirror⟩
    change mirroredPhase 3 (P.phase (mirrorPin 3)) ≤ 5*Real.pi/4
    norm_num [mirroredPhase,mirrorPin]
    linarith

end SquaresInCircles.Six.Normalization
