import SquaresInCircles.Six.Normalization.Complete
import SquaresInCircles.Six.Normalization.DirectedAxes

/-!
# Six squares: the exterior squares of a normalized packing and their pin axes

The five exterior squares E, N, W, D, S of a normalized packing sit at the
phases `θ + t` of the directions `0`, `π/2`, `π`, `5π/4`, `3π/2`. E or N
separated from C along the side of C has its angle below `0.203`, by the
depth of the cap. D is separated from C along its own axis and not along the
west side of C; at a phase `π - v` with `v ≥ 0` the D pin forces `b > 13/100`,
which makes the own margin of D at most its west margin, so the angle of D is
positive. The five pins lie on the circle of radius `9/10`; the chords between
them have positive projection on the axes of the squares in their windows, so
the pairs N, W and E, S are separated along one of four axes directed by the
chord, and W, D and D, S along one of their eight axes other than those the
chords rule out.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- A cap depth of at least `1/2` at an angle `t ≤ π/4` forces
`t < 0.203`: on `[0.203, 1/4]` the cap depth is `capFirst t`, below
`1/2` by the Taylor brackets of `cos` and `sin` at `0.203`. -/
theorem cap_angle_small {height t : ℝ}
    (hh : 1 / 2 ≤ height) (hcap : height ≤ capDepth t)
    (htpi : t ≤ Real.pi / 4) : t < 0.203 := by
  have htq := cap_angle_lt_quarter hh hcap htpi
  by_contra! ht
  have hlow : t ≤ capSwitch := by linarith [capSwitch_gt_29_100]
  obtain ⟨hs, -, -, hc⟩ := trig_bracket (by norm_num) (by linarith [Real.pi_gt_three])
    ⟨ht, htq.le⟩
  norm_num at hs hc
  have hm := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ rho0 - 1 / 2 by linarith [rho0_bounds.1])
  rw [capDepth, ite_eq_left hlow, capFirst] at hcap
  linarith [rho0_bounds.2]

/-- If E is separated from C along the east side of C, its angle is less than
`0.203` in absolute value. -/
theorem NormalizedPacking.east_cardinal_angle_small {R : ℝ} (P : NormalizedPacking R)
    (hE : P.ownAxis 0 = false) : |P.deviation 0| < 0.203 := by
  have hm := P.cardinal_separator 0 hE
  have hcap := P.cardinal_cap_depth 0 hm
  have hangle := P.matching_cardinal_angle 0 hm
  simp only [NormalizedPacking.deviation,matchingCardinal,cardinalCenter,cardinalDepth,
    sub_zero,Matrix.cons_val_zero] at hcap hangle ⊢
  exact cap_angle_small (show (1:ℝ)/2 ≤ 1/2+P.center.1 by linarith [P.box.1.1]) hcap
    (by linarith [Real.pi_gt_d2])

/-- If N is separated from C along the north side of C, its angle from the north
direction is less than `0.203` in absolute value. -/
theorem NormalizedPacking.north_cardinal_angle_small {R : ℝ} (P : NormalizedPacking R)
    (hN : P.ownAxis 1 = false) : |P.deviation 1| < 0.203 := by
  have hm := P.cardinal_separator 1 hN
  have hcap := P.cardinal_cap_depth 1 hm
  have hangle := P.matching_cardinal_angle 1 hm
  simp only [NormalizedPacking.deviation,matchingCardinal,cardinalCenter,cardinalDepth,
    Matrix.cons_val_one,Matrix.cons_val_zero] at hcap hangle ⊢
  exact cap_angle_small (show (1:ℝ)/2 ≤ 1/2+P.center.2 by linarith [P.box.2.1]) hcap
    (by linarith [Real.pi_gt_d2])

end SquaresInCircles.Six.Normalization

namespace SquaresInCircles.Six
open Normalization

lemma diagonal_pin_coordinates : pin 3 = (-(9/10)*hStar,-(9/10)*hStar) := by
  have hc : Real.cos ((5/4:ℝ)*Real.pi) = -hStar := by
    rw [show (5/4:ℝ)*Real.pi=Real.pi/4+Real.pi by ring,Real.cos_add_pi,
      Real.cos_pi_div_four]
    rfl
  have hs : Real.sin ((5/4:ℝ)*Real.pi) = -hStar := by
    rw [show (5/4:ℝ)*Real.pi=Real.pi/4+Real.pi by ring,Real.sin_add_pi,
      Real.sin_pi_div_four]
    rfl
  simp [pin,hc,hs]

lemma small_positive_sine_lower {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 2/5) :
    (24/25)*v ≤ Real.sin v := by
  have hsq := mul_nonneg (sub_nonneg.mpr hv)
    (show 0 ≤ (2:ℝ)/5+v by linarith)
  have hcube := mul_nonneg hv0
    (show 0 ≤ (4:ℝ)/25-v^2 by nlinarith)
  have hs := Real.sin_ge_sub_cube hv0
  nlinarith

lemma small_cosine_linear_lower {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 2/5) :
    1-v/5 ≤ Real.cos v := by
  have hp := mul_nonneg hv0 (sub_nonneg.mpr hv)
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]

lemma diagonal_pin_transverse_lower {a b v : ℝ}
    (hv0 : 0 ≤ v) (hv : v ≤ 2/5)
    (hpin : openSquare (orientedSquare (Real.pi-v) a b) (pin 3)) :
    13/100+(47/100)*v < b := by
  have hp := (abs_lt.mp hpin.2).2
  rw [orientedSquare_localY,diagonal_pin_coordinates] at hp
  simp only [Real.sin_sub,Real.cos_sub,Real.sin_pi,Real.cos_pi,
    zero_mul,neg_one_mul,zero_sub] at hp
  have hs := small_positive_sine_lower hv0 hv
  have hc := small_cosine_linear_lower hv0 hv
  have hsum : 1+(19/25)*v ≤ Real.cos v+Real.sin v := by linarith
  have hsum0 : 0 ≤ Real.cos v+Real.sin v := by linarith
  have hprod := mul_nonneg
    (show 0 ≤ hStar-7/10 by linarith [hStar_bounds.1]) hsum0
  nlinarith

/-- For `0 ≤ v ≤ 2/5`, a square at phase `π - v` with `a ≤ rho0` that holds the
D pin has `(1 - cos v)(a - x) - sin v (b + y) ≤ 0` for `x, y ≥ 0`. -/
lemma diagonal_gap_nonpos {a b x y v : ℝ}
    (hv0 : 0 ≤ v) (hv : v ≤ 2/5) (ha : a ≤ rho0)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hpin : openSquare (orientedSquare (Real.pi-v) a b) (pin 3)) :
    (1-Real.cos v)*(a-x)-Real.sin v*(b+y) ≤ 0 := by
  have hb := diagonal_pin_transverse_lower hv0 hv hpin
  have hs := small_positive_sine_lower hv0 hv
  have hc0 : 0 ≤ 1-Real.cos v := by linarith [Real.cos_le_one v]
  have ha' : a-x ≤ 9/8 := by linarith [rho0_bounds.2]
  have hprodA := mul_le_mul_of_nonneg_right ha' hc0
  have hcos := Real.one_sub_sq_div_two_le_cos (x := v)
  have hprodB := mul_le_mul
    (show (13:ℝ)/100+(47/100)*v ≤ b+y by linarith)
    hs (show 0 ≤ (24:ℝ)/25*v by positivity)
    (show 0 ≤ b+y by linarith)
  have hvSq := mul_nonneg hv0 (sub_nonneg.mpr hv)
  nlinarith

namespace Normalization.NormalizedPacking
variable {R : ℝ} (P : NormalizedPacking R)

/-- The angle of D is positive: D is separated from C along its own axis and not
along the west side of C, but at a phase `π - v` with `v ≥ 0` the D pin makes its
own margin at most its west margin. -/
theorem diagonal_angle_pos : 0 < P.diagonalAngle := by
  have hown := P.diagonal_own
  by_contra! hnonpos
  let v := -P.diagonalAngle
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have hv : v ≤ 2/5 := by
    have hd := P.diagonal_angle_bounds.1
    dsimp [v]
    linarith
  have hphase : P.phase 3=Real.pi-v := by dsimp [v,diagonalAngle]; ring
  have hpin : openSquare (orientedSquare (Real.pi-v) (P.radial 3) (P.transverse 3))
      (pin 3) := by simpa only [hphase] using P.holds_pin 3
  have hbad := diagonal_gap_nonpos hv0 hv (P.contained 3).a_le_rho0 P.box.1.1 P.box.2.1 hpin
  have ho := P.own_separator 3 hown
  have hw := (P.toPinPacking.ownAxis_eq_true 3).mp hown
  have hgap := own_sub_west_margin (-v) (P.radial 3) (P.transverse 3) P.center.1 P.center.2
  rw [show Real.pi+(-v)=P.phase 3 by rw [hphase]; ring,Real.cos_neg,Real.sin_neg] at hgap
  change centralMargin .west (P.phase 3) (P.radial 3) (P.transverse 3) P.center.1 P.center.2<0
    at hw
  linarith

lemma diagonal_angle_range : 0 < P.diagonalAngle ∧ P.diagonalAngle ≤ Real.pi/4 :=
  ⟨P.diagonal_angle_pos,P.diagonal_angle_bounds.2⟩

end Normalization.NormalizedPacking

/-- The primary axis of a square at the phase `t`. -/
def primary (t : ℝ) : Point := (Real.cos t,Real.sin t)
/-- The secondary axis of a square at the phase `t`. -/
def secondary (t : ℝ) : Point := (-Real.sin t,Real.cos t)

lemma centered_chord (r m u : ℝ) :
    sub (polar r (m+u)) (polar r (m-u)) =
      scale (2*r*Real.sin u) (-Real.sin m,Real.cos m) := by
  apply Prod.ext <;> dsimp [sub,polar,scale] <;>
    simp only [Real.cos_add,Real.cos_sub,Real.sin_add,Real.sin_sub] <;> ring

lemma sub_reverse (p q : Point) : sub p q=scale (-1) (sub q p) := by
  apply Prod.ext <;> dsimp [sub,scale] <;> ring

/-- The chord from the pin of W to the pin of D. -/
lemma pin_chord_westDiagonal : sub (pin 3) (pin 2)=
    ((9/10)*Real.sin (Real.pi/12),-(9/10)*Real.cos (Real.pi/12)) := by
  have h := centered_chord (9/10) (13*Real.pi/12) (Real.pi/6)
  have h1 : 13*Real.pi/12+Real.pi/6=(5/4)*Real.pi := by ring
  have h2 : 13*Real.pi/12-Real.pi/6=(11/12)*Real.pi := by ring
  rw [h1,h2,show 13*Real.pi/12=Real.pi+Real.pi/12 by ring,
    sin_pi_add,cos_pi_add,Real.sin_pi_div_six,
    show (2:ℝ)*(9/10)*(1/2)=9/10 by norm_num] at h
  simpa [pin,polar,scale] using h

/-- The chord from the pin of D to the pin of S, the reflection of the chord
W–D in the diagonal. -/
lemma pin_chord_diagonalSouth : sub (pin 4) (pin 3)=
    ((9/10)*Real.cos (Real.pi/12),-(9/10)*Real.sin (Real.pi/12)) := by
  have h := congrArg diagonalPoint pin_chord_westDiagonal
  have hd : ∀ p q : Point, diagonalPoint (sub p q)=sub (diagonalPoint p) (diagonalPoint q) := by
    intro p q
    rfl
  rw [hd,pin_diagonal,pin_diagonal] at h
  change sub (pin 3) (pin 4)=
    (-(9/10)*Real.cos (Real.pi/12),(9/10)*Real.sin (Real.pi/12)) at h
  rw [sub_reverse (pin 4) (pin 3),h]
  apply Prod.ext <;> dsimp [scale] <;> ring

/-- The common length of the chords N–W and E–S. -/
def adjacentChordLength : ℝ := (9/5)*Real.sin (5*Real.pi/24)

lemma adjacentChordLength_pos : 0 < adjacentChordLength := by
  apply mul_pos (by norm_num)
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

lemma pin_chord_northWest : sub (pin 1) (pin 2)=
    polar adjacentChordLength (5*Real.pi/24) := by
  have h := centered_chord (9/10) (17*Real.pi/24) (5*Real.pi/24)
  have h1 : 17*Real.pi/24+5*Real.pi/24=(11/12)*Real.pi := by ring
  have h2 : 17*Real.pi/24-5*Real.pi/24=Real.pi/2 := by ring
  rw [h1,h2,show 17*Real.pi/24=Real.pi/2+5*Real.pi/24 by ring,
    Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two] at h
  have hn : polar (9/10) (Real.pi/2)=pin 1 := by simp [polar,pin]
  have hw : polar (9/10) ((11/12)*Real.pi)=pin 2 := rfl
  rw [hn,hw] at h
  rw [sub_reverse (pin 1) (pin 2),h]
  apply Prod.ext <;> dsimp [scale,polar,adjacentChordLength] <;> ring

lemma pin_chord_eastSouth : sub (pin 0) (pin 4)=
    polar adjacentChordLength (7*Real.pi/24) := by
  have h := congrArg diagonalPoint pin_chord_northWest
  change sub (diagonalPoint (pin 1)) (diagonalPoint (pin 2))=
    diagonalPoint (polar adjacentChordLength (5*Real.pi/24)) at h
  rw [pin_diagonal,pin_diagonal] at h
  change sub (pin 0) (pin 4)=_ at h
  rw [h,show 7*Real.pi/24=Real.pi/2-5*Real.pi/24 by ring]
  apply Prod.ext <;> simp [diagonalPoint,polar,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]

lemma westDiagonal_chord_secondary (t : ℝ) :
    dot (secondary (Real.pi+t)) (sub (pin 3) (pin 2))=
      (9/10)*Real.cos (t-Real.pi/12) := by
  rw [pin_chord_westDiagonal]
  dsimp [dot,secondary]
  rw [cos_pi_add,sin_pi_add,Real.cos_sub]
  ring

lemma diagonalSouth_chord_primary (d : ℝ) :
    dot (primary (Real.pi+d)) (sub (pin 4) (pin 3))=
      -(9/10)*Real.cos (d+Real.pi/12) := by
  rw [pin_chord_diagonalSouth]
  dsimp [dot,primary]
  rw [cos_pi_add,sin_pi_add,Real.cos_add]
  ring

lemma diagonalSouth_chord_secondary (d : ℝ) :
    dot (secondary (Real.pi+d)) (sub (pin 4) (pin 3))=
      (9/10)*Real.sin (d+Real.pi/12) := by
  rw [pin_chord_diagonalSouth]
  dsimp [dot,secondary]
  rw [cos_pi_add,sin_pi_add,Real.sin_add]
  ring

lemma diagonalSouth_chord_south_secondary (s : ℝ) :
    dot (secondary (3*Real.pi/2+s)) (sub (pin 4) (pin 3))=
      (9/10)*Real.cos (s+Real.pi/12) := by
  rw [pin_chord_diagonalSouth]
  dsimp [dot,secondary]
  rw [Real.cos_add,Real.sin_add,south_cos,south_sin,Real.cos_add]
  ring

/-- The directions of the four axes of the pairs N, W and E, S that the chords
between their pins project positively on. -/
def northWestSigns : Fin 4 → Bool := ![false,false,true,false]
def eastSouthSigns : Fin 4 → Bool := ![false,true,true,true]

lemma northWest_chord_projections (w n a b A B : ℝ) (i : Fin 4) :
    dot (preferredPairAxis northWestSigns (orientedSquare (Real.pi+w) a b)
      (orientedSquare (Real.pi/2+n) A B) i) (sub (pin 1) (pin 2)) =
    adjacentChordLength *
      ![Real.cos (5*Real.pi/24-w),Real.sin (5*Real.pi/24-w),
        Real.sin (5*Real.pi/24-n),Real.cos (5*Real.pi/24-n)] i := by
  rw [pin_chord_northWest]
  fin_cases i <;> simp [preferredPairAxis,unsignedPairAxis,northWestSigns,normalX,normalY,
    orientedSquare,dot,scale,polar,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub] <;> ring

lemma eastSouth_chord_projections (s e a b A B : ℝ) (i : Fin 4) :
    dot (preferredPairAxis eastSouthSigns (orientedSquare (3*Real.pi/2+s) a b)
      (orientedSquare e A B) i) (sub (pin 0) (pin 4)) =
    adjacentChordLength *
      ![Real.sin (7*Real.pi/24-s),Real.cos (7*Real.pi/24-s),
        Real.cos (7*Real.pi/24-e),Real.sin (7*Real.pi/24-e)] i := by
  rw [pin_chord_eastSouth]
  fin_cases i <;> simp [preferredPairAxis,unsignedPairAxis,eastSouthSigns,normalX,normalY,
    orientedSquare,dot,scale,polar,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,
    south_cos,south_sin] <;> ring

private lemma sine_cosine_positive {t : ℝ} (ht : 0<t ∧ t<Real.pi/2) :
    0<Real.sin t ∧ 0<Real.cos t :=
  ⟨Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,Real.pi_pos]),
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩⟩

lemma northWest_chord_positive {w n : ℝ}
    (hw : -2/3<w ∧ w<5/8) (hn : -3/10<n ∧ n<5/12)
    (a b A B : ℝ) (i : Fin 4) :
    0 < dot (preferredPairAxis northWestSigns (orientedSquare (Real.pi+w) a b)
      (orientedSquare (Real.pi/2+n) A B) i) (sub (pin 1) (pin 2)) := by
  have hW := sine_cosine_positive
    (show 0<5*Real.pi/24-w ∧ 5*Real.pi/24-w<Real.pi/2 by
      constructor <;> linarith [hw.1,hw.2,Real.pi_gt_d2])
  have hN := sine_cosine_positive
    (show 0<5*Real.pi/24-n ∧ 5*Real.pi/24-n<Real.pi/2 by
      constructor <;> linarith [hn.1,hn.2,Real.pi_gt_d2])
  rw [northWest_chord_projections]
  apply mul_pos adjacentChordLength_pos
  fin_cases i
  · exact hW.2
  · exact hW.1
  · exact hN.1
  · exact hN.2

lemma eastSouth_chord_positive {s e : ℝ}
    (hs : -5/8< s ∧ s<2/3) (he : -5/12<e ∧ e<3/10)
    (a b A B : ℝ) (i : Fin 4) :
    0 < dot (preferredPairAxis eastSouthSigns (orientedSquare (3*Real.pi/2+s) a b)
      (orientedSquare e A B) i) (sub (pin 0) (pin 4)) := by
  have hS := sine_cosine_positive
    (show 0<7*Real.pi/24-s ∧ 7*Real.pi/24-s<Real.pi/2 by
      constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have hE := sine_cosine_positive
    (show 0<7*Real.pi/24-e ∧ 7*Real.pi/24-e<Real.pi/2 by
      constructor <;> linarith [he.1,he.2,Real.pi_gt_d2])
  rw [eastSouth_chord_projections]
  apply mul_pos adjacentChordLength_pos
  fin_cases i
  · exact hS.1
  · exact hS.2
  · exact hE.2
  · exact hE.1

namespace Normalization.NormalizedPacking
variable {R : ℝ} (P : NormalizedPacking R)

/-- The exterior square `i`: E, N, W, D or S. -/
def square (i : Fin 5) : UnitSquare := P.model i.succ

lemma square_def (i : Fin 5) :
    P.square i=orientedSquare (P.phase i) (P.radial i) (P.transverse i) := rfl

lemma phase_from_deviation (i : Fin 5) :
    P.phase i=cardinalCenter (matchingCardinal i)+P.deviation i := by
  dsimp [deviation]
  ring

lemma deviation_windows :
    (-5/12<P.deviation 0 ∧ P.deviation 0<3/10) ∧
    (-3/10<P.deviation 1 ∧ P.deviation 1<5/12) ∧
    (-2/3<P.deviation 2 ∧ P.deviation 2<5/8) ∧
    (-5/8<P.deviation 4 ∧ P.deviation 4<2/3) := by
  have he := P.window 0
  have hn := P.window 1
  have hw := P.window 2
  have hs := P.window 4
  have e : (3/2:ℝ)*Real.pi = 3*Real.pi/2 := by ring
  simpa [deviation,matchingCardinal,cardinalCenter,windowLower,windowUpper,modelPhase,e]
    using And.intro he (And.intro hn (And.intro hw hs))

lemma pair_disjoint (i j : Fin 5) (hij : i≠j) :
    ∀ p, ¬ (openSquare (P.square i) p ∧ openSquare (P.square j) p) :=
  P.toPinPacking.exterior_disjoint i j hij

/-- W and N are separated along one of their four axes, directed from W to N by
`northWestSigns`. -/
theorem northWest_separator : ∃ i : Fin 4,
    SAT.threshold (P.square 2) (P.square 1) ≤
      dot (preferredPairAxis northWestSigns (P.square 2) (P.square 1) i)
        (sub (P.square 1).center (P.square 2).center) := by
  apply preferred_separators_complete northWestSigns _ _ (P.holds_pin 2) (P.holds_pin 1) _
    (P.pair_disjoint 2 1 (by decide))
  have h2 : P.phase 2=Real.pi+P.deviation 2 := P.phase_from_deviation 2
  have h1 : P.phase 1=Real.pi/2+P.deviation 1 := P.phase_from_deviation 1
  intro i
  rw [h2,h1]
  exact northWest_chord_positive P.deviation_windows.2.2.1 P.deviation_windows.2.1 _ _ _ _ i

/-- S and E are separated along one of their four axes, directed from S to E by
`eastSouthSigns`. -/
theorem eastSouth_separator : ∃ i : Fin 4,
    SAT.threshold (P.square 4) (P.square 0) ≤
      dot (preferredPairAxis eastSouthSigns (P.square 4) (P.square 0) i)
        (sub (P.square 0).center (P.square 4).center) := by
  apply preferred_separators_complete eastSouthSigns _ _ (P.holds_pin 4) (P.holds_pin 0) _
    (P.pair_disjoint 4 0 (by decide))
  have h4 : P.phase 4=3*Real.pi/2+P.deviation 4 := P.phase_from_deviation 4
  have h0 : P.phase 0=P.deviation 0 := by
    rw [P.phase_from_deviation 0]
    simp [matchingCardinal,cardinalCenter]
  intro i
  rw [h4,h0]
  exact eastSouth_chord_positive P.deviation_windows.2.2.2 P.deviation_windows.1 _ _ _ _ i

lemma westDiagonal_chord_signs :
    0<dot (normalY (P.square 2)) (sub (pin 3) (pin 2)) ∧
    0<dot (normalY (P.square 3)) (sub (pin 3) (pin 2)) := by
  have hw := P.deviation_windows.2.2.1
  have hd := P.diagonal_angle_range
  have hcw := Real.cos_pos_of_mem_Ioo
    (show P.deviation 2-Real.pi/12 ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hw.1,hw.2,Real.pi_gt_d2])
  have hcd := Real.cos_pos_of_mem_Ioo
    (show P.diagonalAngle-Real.pi/12 ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  constructor
  · change 0<dot (secondary (P.phase 2)) (sub (pin 3) (pin 2))
    rw [P.phase_from_deviation 2]
    change 0<dot (secondary (Real.pi+P.deviation 2)) _
    rw [westDiagonal_chord_secondary]
    exact mul_pos (by norm_num) hcw
  · change 0<dot (secondary (P.phase 3)) (sub (pin 3) (pin 2))
    rw [show P.phase 3=Real.pi+P.diagonalAngle by dsimp [diagonalAngle]; ring,
      westDiagonal_chord_secondary]
    exact mul_pos (by norm_num) hcd

/-- W and D are separated along one of their eight directed axes other than the
negated secondary axes. -/
theorem westDiagonal_separator : ∃ i : Fin 8,
    SAT.threshold (P.square 2) (P.square 3) ≤
      dot (pairNormal i (P.square 2) (P.square 3))
        (sub (P.square 3).center (P.square 2).center) ∧ i≠3 ∧ i≠7 := by
  obtain ⟨i,hi⟩ := directed_pair_separator _ _ (P.pair_disjoint 2 3 (by decide))
  have hp := axis_points_to_pin _ _ (P.holds_pin 2) (P.holds_pin 3) i hi
  refine ⟨i,hi,?_,?_⟩
  · intro h
    subst i
    change 0<dot (scale (-1) (normalY (P.square 2))) _ at hp
    rw [dot_scale_neg] at hp
    linarith [P.westDiagonal_chord_signs.1]
  · intro h
    subst i
    change 0<dot (scale (-1) (normalY (P.square 3))) _ at hp
    rw [dot_scale_neg] at hp
    linarith [P.westDiagonal_chord_signs.2]

lemma diagonalSouth_chord_signs :
    dot (normalX (P.square 3)) (sub (pin 4) (pin 3))<0 ∧
    0<dot (normalY (P.square 3)) (sub (pin 4) (pin 3)) ∧
    0<dot (normalY (P.square 4)) (sub (pin 4) (pin 3)) := by
  have hd := P.diagonal_angle_range
  have hs := P.deviation_windows.2.2.2
  have hds := sine_cosine_positive
    (show 0<P.diagonalAngle+Real.pi/12 ∧ P.diagonalAngle+Real.pi/12<Real.pi/2 by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hsc := Real.cos_pos_of_mem_Ioo
    (show P.deviation 4+Real.pi/12 ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have hD : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [diagonalAngle]; ring
  have hS : P.phase 4=3*Real.pi/2+P.deviation 4 := P.phase_from_deviation 4
  change dot (primary (P.phase 3)) _<0 ∧ 0<dot (secondary (P.phase 3)) _ ∧
    0<dot (secondary (P.phase 4)) _
  rw [hD,hS,diagonalSouth_chord_primary,diagonalSouth_chord_secondary,
    diagonalSouth_chord_south_secondary]
  exact ⟨mul_neg_of_neg_of_pos (by norm_num) hds.2,
    mul_pos (by norm_num) hds.1,mul_pos (by norm_num) hsc⟩

/-- D and S are separated along one of their eight directed axes other than the
primary axis of D and the negated secondary axes. -/
theorem diagonalSouth_separator : ∃ i : Fin 8,
    SAT.threshold (P.square 3) (P.square 4) ≤
      dot (pairNormal i (P.square 3) (P.square 4))
        (sub (P.square 4).center (P.square 3).center) ∧ i≠0 ∧ i≠3 ∧ i≠7 := by
  obtain ⟨i,hi⟩ := directed_pair_separator _ _ (P.pair_disjoint 3 4 (by decide))
  have hp := axis_points_to_pin _ _ (P.holds_pin 3) (P.holds_pin 4) i hi
  refine ⟨i,hi,?_,?_,?_⟩
  · intro h; subst i
    change 0<dot (normalX (P.square 3)) _ at hp
    linarith [P.diagonalSouth_chord_signs.1]
  · intro h; subst i
    change 0<dot (scale (-1) (normalY (P.square 3))) _ at hp
    rw [dot_scale_neg] at hp
    linarith [P.diagonalSouth_chord_signs.2.1]
  · intro h; subst i
    change 0<dot (scale (-1) (normalY (P.square 4))) _ at hp
    rw [dot_scale_neg] at hp
    linarith [P.diagonalSouth_chord_signs.2.2]

end Normalization.NormalizedPacking

open Normalization

/-- W and D are separated along the secondary axis of W, and D and S along the
secondary axis of S, as in the model. -/
def WingSeparators {R : ℝ} (P : NormalizedPacking R) : Prop :=
  SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) ∧
    SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)

end SquaresInCircles.Six
