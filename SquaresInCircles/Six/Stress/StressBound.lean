import SquaresInCircles.Six.Stress.PairEstimate
import SquaresInCircles.Six.Stress.DiagonalEstimate
import SquaresInCircles.Six.Equality.Contacts
import SquaresInCircles.Six.Tails.South
import SquaresInCircles.Six.Separators.DiagonalAngle
import SquaresInCircles.Six.Wings.WestSign

/-!
# The stress bound at the optimal radius

Theorem 10.12: in a normalized packing in the disk of radius `radius`, the five
exterior squares are turned exactly as in the model, and the eight contacts of
the model hold. The stress has weight one on the edges from C to E, N, W and S,
along the axes that separate them from C, weight `rStar` on N–W and E–S, along
axes given by the pins, and weight `mStar` on W–D and D–S, along the secondary
axes of W and S, which separate them. Read in the frames of the squares, the
separating inequalities and the disk bound the value of the pair N, W by
`c.1 - c.2 + mStar (bW + 1/2)`, that of the pair E, S, by the reflection in the
diagonal, by `c.2 - c.1 + mStar (1/2 - bS)`, and the diagonal term by
`mStar (-1 - bW + bS)`; the sum is at most zero. The windows, the signs and the
tails of the angles put them in the domains of the pair estimate and of the
diagonal remainder, which bound the same sum below by `(|n| + |e|)/1000` plus the
remainder. So all the angles vanish, `d = π/4`, and N–W and E–S are separated
along the axes of the model; the separating inequalities are then the contacts.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

/-! ### The pair stress in the frames of N and W -/

/-- The components of `g` in the frame at the angle `t`. -/
def project (t : ℝ) (g : Point) : Point :=
  (Real.cos t*g.1+Real.sin t*g.2,-Real.sin t*g.1+Real.cos t*g.2)

lemma center_dot_project (t a b : ℝ) (g : Point) :
    dot g (orientedSquare t a b).center=dot (project t g) (a,b) := by
  dsimp [dot,project,orientedSquare]
  ring

/-- The normal of C–N: the own axis of N, or the north side of C. -/
def northNormal (own : Bool) (n : ℝ) : Point := if own then (-Real.sin n,Real.cos n) else (0,1)

/-- The normal of C–W: the own axis of W, or the west side of C. -/
def westNormal (own : Bool) (w : ℝ) : Point := if own then (-Real.cos w,-Real.sin w) else (-1,0)

/-- The axis of a facet, directed from W to N. -/
def Facet.axis (n w : ℝ) : Facet → Point
  | .westFirst => (Real.cos w,Real.sin w)
  | .westSecond => (-Real.sin w,Real.cos w)
  | .northFirst => (-Real.sin n,Real.cos n)
  | .northSecond => (Real.cos n,Real.sin n)

/-- The facets in the order of the axes of the pair W, N. -/
def facetOf (i : Fin 4) : Facet := ![.westFirst,.westSecond,.northFirst,.northSecond] i

lemma project_normals (no wo : Bool) (f : Facet) (n w : ℝ) :
    project (Real.pi/2+n) (northNormal no n)=Pair.central no n ∧
    project (Real.pi+w) (westNormal wo w)=Pair.central wo w ∧
    project (Real.pi/2+n) (f.axis n w)=f.north (n-w) ∧
    project (Real.pi+w) (scale (-1) (f.axis n w))=f.west (n-w) := by
  have h1 := Real.sin_sq_add_cos_sq n
  have h2 := Real.sin_sq_add_cos_sq w
  refine ⟨?_,?_,?_,?_⟩
  · cases no <;> apply Prod.ext <;>
      simp [project,northNormal,Pair.central,Real.cos_add,Real.sin_add] <;> linarith
  · cases wo <;> apply Prod.ext <;>
      simp [project,westNormal,Pair.central,Real.cos_add,Real.sin_add] <;> linarith
  · cases f <;> apply Prod.ext <;>
      simp [project,Facet.axis,Facet.north,Real.cos_add,Real.sin_add,Real.cos_sub,
        Real.sin_sub] <;> linarith
  · cases f <;> apply Prod.ext <;>
      simp [project,Facet.axis,Facet.west,scale,Real.cos_add,Real.sin_add,Real.cos_sub,
        Real.sin_sub] <;> linarith

/-- The work of the edges C–N, C–W and N–W, written with the local centres of N
and W, the centre `c` of C, and the forces on N and W. -/
theorem edge_work_identity (no wo : Bool) (f : Facet) (n w an bn aw bw : ℝ) (c : Point) :
    dot (northNormal no n) (sub (orientedSquare (Real.pi/2+n) an bn).center c)+
      dot (westNormal wo w) (sub (orientedSquare (Real.pi+w) aw bw).center c)+
      rStar*dot (f.axis n w)
        (sub (orientedSquare (Real.pi/2+n) an bn).center (orientedSquare (Real.pi+w) aw bw).center)=
      dot (Pair.northForce no f n w) (an,bn)+dot (Pair.westForce wo f n w) (aw,bw)+
        mStar*bw+c.1-c.2+dot (Pair.centralExcess no wo n w) c := by
  obtain ⟨p1,p2,p3,p4⟩ := project_normals no wo f n w
  have hN := center_dot_project (Real.pi/2+n) an bn (northNormal no n)
  have hW := center_dot_project (Real.pi+w) aw bw (westNormal wo w)
  have hNs := center_dot_project (Real.pi/2+n) an bn (f.axis n w)
  have hWs := center_dot_project (Real.pi+w) aw bw (scale (-1) (f.axis n w))
  rw [p1] at hN
  rw [p2] at hW
  rw [p3] at hNs
  rw [p4] at hWs
  have hC : dot (Pair.centralExcess no wo n w) c=
      -(dot (northNormal no n) c+dot (westNormal wo w) c)-c.1+c.2 := by
    cases no <;> cases wo <;> dsimp [northNormal,westNormal,Pair.centralExcess,dot] <;> ring
  rw [hC]
  dsimp [Pair.northForce,Pair.westForce,dot,sub,scale] at *
  linear_combination hN+hW+rStar*hNs+rStar*hWs

/-- The three separating inequalities of C–N, C–W and N–W, with the weights one,
one and `rStar`, the disk and the box `[0, c0]²` for the centre `c` of C bound
the value of the pair by `c.1 - c.2 + mStar (bw + 1/2)`. -/
theorem pair_work_bound (no wo : Bool) (f : Facet) {n w an bn aw bw : ℝ} {c : Point}
    (hc : (0≤c.1 ∧ c.1≤c0) ∧ (0≤c.2 ∧ c.2≤c0))
    (hNbox : (|an|+1/2)^2+(|bn|+1/2)^2≤radius^2)
    (hWbox : (|aw|+1/2)^2+(|bw|+1/2)^2≤radius^2)
    (hN : 1/2+angularWidth n≤dot (northNormal no n)
      (sub (orientedSquare (Real.pi/2+n) an bn).center c))
    (hW : 1/2+angularWidth w≤dot (westNormal wo w)
      (sub (orientedSquare (Real.pi+w) aw bw).center c))
    (hNW : 1/2+angularWidth (n-w)≤dot (f.axis n w)
      (sub (orientedSquare (Real.pi/2+n) an bn).center (orientedSquare (Real.pi+w) aw bw).center)) :
    Pair.value no wo f n w≤c.1-c.2+mStar*(bw+1/2) := by
  have hsum := add_le_add (add_le_add hN hW) (mul_le_mul_of_nonneg_left hNW rStar_pos.le)
  rw [edge_work_identity] at hsum
  have hNs := Pair.work_le_northBound f (Pair.northForce no f n w) hNbox
  have hWs := Pair.work_le_vertexBound (Pair.westForce wo f n w) hWbox
  have hC := Pair.central_excess_support hc no wo n w
  dsimp [dot] at hsum hC
  dsimp [Pair.value,Pair.threshold]
  linarith

/-! ### The separations of a normalized packing -/

/-- The axis that separates C from the exterior square `i`: its primary axis if
it is separated along its own axis, else the normal of the matching side of C. -/
def centralAxis {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) : Point :=
  if P.ownAxis i then primary (P.phase i) else primary (cardinalCenter (matchingCardinal i))

lemma central_axis_separates {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) :
    1/2+angularWidth (P.phase i)≤dot (centralAxis P i) (sub (P.square i).center P.center) := by
  rw [P.square_def]
  cases hbit : P.ownAxis i
  · have hm := P.cardinal_separator i hbit
    fin_cases i
    all_goals simp only [Fin.reduceFinMk,Fin.isValue] at hbit hm ⊢
    all_goals simp only [centralAxis,hbit,Bool.false_eq_true,ite_false,
      Matrix.cons_val,matchingCardinal,cardinalCenter,primary] at hm ⊢
    all_goals simp only [Real.cos_zero,Real.sin_zero,Real.cos_pi,Real.sin_pi,
      Real.cos_pi_div_two,Real.sin_pi_div_two,south_cos,south_sin] at hm ⊢
    all_goals dsimp [centralMargin,centerX,centerY,dot,sub,orientedSquare] at hm ⊢
    all_goals linarith
  · have hm := P.own_separator i hbit
    simp only [centralAxis,hbit,ite_true]
    change 1/2+angularWidth (P.phase i)≤
      frameX (orientedSquare (P.phase i) (P.radial i) (P.transverse i))
        (sub (orientedSquare (P.phase i) (P.radial i) (P.transverse i)).center P.center)
    rw [primary_difference]
    dsimp [centralMargin] at hm
    linarith

lemma central_axis_north {R : ℝ} (P : NormalizedPacking R) :
    centralAxis P 1=northNormal (P.ownAxis 1) (P.deviation 1) := by
  have hn : P.phase 1=Real.pi/2+P.deviation 1 := P.phase_from_deviation 1
  cases hb : P.ownAxis 1 <;>
    simp [centralAxis,northNormal,hb,hn,matchingCardinal,cardinalCenter,
      primary,Real.cos_add,Real.sin_add]

lemma central_axis_west {R : ℝ} (P : NormalizedPacking R) :
    centralAxis P 2=westNormal (P.ownAxis 2) (P.deviation 2) := by
  have hw : P.phase 2=Real.pi+P.deviation 2 := P.phase_from_deviation 2
  cases hb : P.ownAxis 2 <;>
    simp [centralAxis,westNormal,hb,hw,matchingCardinal,cardinalCenter,
      primary,Real.cos_add,Real.sin_add]

lemma preferred_northwest_axis {R : ℝ} (P : NormalizedPacking R) (u : Fin 4) :
    preferredPairAxis northWestSigns (P.square 2) (P.square 1) u=
      (facetOf u).axis (P.deviation 1) (P.deviation 2) := by
  have hn : P.phase 1=Real.pi/2+P.deviation 1 := P.phase_from_deviation 1
  have hw : P.phase 2=Real.pi+P.deviation 2 := P.phase_from_deviation 2
  fin_cases u <;> simp [preferredPairAxis,unsignedPairAxis,northWestSigns,facetOf,Facet.axis,
    P.square_def,hn,hw,normalX,normalY,orientedSquare,scale,Real.cos_add,Real.sin_add]

lemma northwest_threshold (n w an bn aw bw : ℝ) :
    SAT.threshold (orientedSquare (Real.pi+w) aw bw)
      (orientedSquare (Real.pi/2+n) an bn)=1/2+angularWidth (n-w) := by
  rw [oriented_pair_threshold,show (Real.pi/2+n)-(Real.pi+w)=-(Real.pi/2-(n-w)) by ring,
    angularWidth_neg,angularWidth_half_pi_sub]

lemma square_box (P : NormalizedPacking radius) (i : Fin 5) :
    (|P.radial i|+1/2)^2+(|P.transverse i|+1/2)^2≤radius^2 := by
  simpa only [pinModel_succ,orientedSquare_alpha,orientedSquare_beta,phi] using
    P.packing.phi_le i.succ

/-- The value of the pair N, W along a separating axis `u` of N and W. -/
lemma northwest_work (P : NormalizedPacking radius) (u : Fin 4)
    (hsel : SAT.threshold (P.square 2) (P.square 1) ≤
      dot (preferredPairAxis northWestSigns (P.square 2) (P.square 1) u)
        (sub (P.square 1).center (P.square 2).center)) :
    Pair.value (P.ownAxis 1) (P.ownAxis 2) (facetOf u) (P.deviation 1) (P.deviation 2) ≤
      P.center.1-P.center.2+mStar*(P.transverse 2+1/2) := by
  have hn : P.phase 1=Real.pi/2+P.deviation 1 := P.phase_from_deviation 1
  have hw : P.phase 2=Real.pi+P.deviation 2 := P.phase_from_deviation 2
  have hN := central_axis_separates P 1
  have hW := central_axis_separates P 2
  rw [central_axis_north,P.square_def,hn,angularWidth_half_pi_add] at hN
  rw [central_axis_west,P.square_def,hw,angularWidth_pi_add] at hW
  rw [preferred_northwest_axis,P.square_def 2,P.square_def 1,hw,hn,northwest_threshold] at hsel
  exact pair_work_bound (P.ownAxis 1) (P.ownAxis 2) (facetOf u)
    P.box
    (square_box P 1) (square_box P 2) hN hW hsel

/-! ### The pair E, S by the reflection in the diagonal -/

lemma reflected_east_center (e a b : ℝ) :
    (orientedSquare (Real.pi/2-e) a (-b)).center=
      diagonalPoint (orientedSquare e a b).center := by
  apply Prod.ext <;>
    simp [orientedSquare,diagonalPoint,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]
  ring

lemma reflected_south_center (s a b : ℝ) :
    (orientedSquare (Real.pi-s) a (-b)).center=
      diagonalPoint (orientedSquare (3*Real.pi/2+s) a b).center := by
  apply Prod.ext <;>
    simp [orientedSquare,diagonalPoint,Real.cos_pi_sub,Real.sin_pi_sub,
      Real.cos_add,Real.sin_add,south_cos,south_sin]

lemma dot_diagonalPoint (p q : Point) :
    dot (diagonalPoint p) (diagonalPoint q)=dot p q := by
  dsimp [dot,diagonalPoint]
  ring

lemma eastsouth_threshold (e s ae be aS bS : ℝ) :
    SAT.threshold (orientedSquare (3*Real.pi/2+s) aS bS)
      (orientedSquare e ae be)=1/2+angularWidth ((-e)-(-s)) := by
  rw [oriented_pair_threshold,show e-(3*Real.pi/2+s)=(e-s)-3*Real.pi/2 by ring,
    show (-e)-(-s)=-(e-s) by ring,angularWidth_neg]
  simp [angularWidth,Real.cos_sub,Real.sin_sub,south_cos,south_sin,add_comm]
  exact abs_sub_comm _ _

lemma central_axis_east {R : ℝ} (P : NormalizedPacking R) :
    northNormal (P.ownAxis 0) (-P.deviation 0)=diagonalPoint (centralAxis P 0) := by
  have he : P.phase 0=P.deviation 0 := by
    simpa [matchingCardinal,cardinalCenter] using P.phase_from_deviation 0
  cases hb : P.ownAxis 0 <;>
    simp [northNormal,centralAxis,hb,he,matchingCardinal,cardinalCenter,
      primary,diagonalPoint,Real.cos_neg,Real.sin_neg]

lemma central_axis_south {R : ℝ} (P : NormalizedPacking R) :
    westNormal (P.ownAxis 4) (-P.deviation 4)=diagonalPoint (centralAxis P 4) := by
  have hs : P.phase 4=3*Real.pi/2+P.deviation 4 := P.phase_from_deviation 4
  cases hb : P.ownAxis 4 <;>
    simp [westNormal,centralAxis,hb,hs,matchingCardinal,cardinalCenter,
      primary,diagonalPoint,Real.cos_neg,Real.sin_neg,Real.cos_add,Real.sin_add,
      south_cos,south_sin]

lemma preferred_eastsouth_axis {R : ℝ} (P : NormalizedPacking R) (v : Fin 4) :
    (facetOf v).axis (-P.deviation 0) (-P.deviation 4)=
      diagonalPoint (preferredPairAxis eastSouthSigns (P.square 4) (P.square 0) v) := by
  have he : P.phase 0=P.deviation 0 := by
    simpa [matchingCardinal,cardinalCenter] using P.phase_from_deviation 0
  have hs : P.phase 4=3*Real.pi/2+P.deviation 4 := P.phase_from_deviation 4
  fin_cases v <;> apply Prod.ext <;>
    simp [facetOf,Facet.axis,preferredPairAxis,unsignedPairAxis,eastSouthSigns,P.square_def,
      he,hs,normalX,normalY,orientedSquare,scale,diagonalPoint,
      Real.cos_add,Real.sin_add,Real.cos_neg,Real.sin_neg,south_cos,south_sin]

/-- The value of the pair E, S along a separating axis `v` of S and E, read in the
reflection in the diagonal. -/
lemma eastsouth_work (P : NormalizedPacking radius) (v : Fin 4)
    (hsel : SAT.threshold (P.square 4) (P.square 0) ≤
      dot (preferredPairAxis eastSouthSigns (P.square 4) (P.square 0) v)
        (sub (P.square 0).center (P.square 4).center)) :
    Pair.value (P.ownAxis 0) (P.ownAxis 4) (facetOf v) (-P.deviation 0) (-P.deviation 4) ≤
      P.center.2-P.center.1+mStar*(-P.transverse 4+1/2) := by
  have he : P.phase 0=P.deviation 0 := by
    simpa [matchingCardinal,cardinalCenter] using P.phase_from_deviation 0
  have hs : P.phase 4=3*Real.pi/2+P.deviation 4 := P.phase_from_deviation 4
  have hE := central_axis_separates P 0
  have hS := central_axis_separates P 4
  rw [P.square_def,he] at hE
  rw [P.square_def,hs,angularWidth_three_half_pi_add] at hS
  rw [P.square_def 4,P.square_def 0,hs,he,eastsouth_threshold] at hsel
  have hc := P.box
  have hNE : (orientedSquare (Real.pi/2+(-P.deviation 0))
      (P.radial 0) (-P.transverse 0)).center=diagonalPoint (P.square 0).center := by
    rw [P.square_def,he]
    simpa only [sub_eq_add_neg] using
      reflected_east_center (P.deviation 0) (P.radial 0) (P.transverse 0)
  have hWS : (orientedSquare (Real.pi+(-P.deviation 4))
      (P.radial 4) (-P.transverse 4)).center=diagonalPoint (P.square 4).center := by
    rw [P.square_def,hs]
    simpa only [sub_eq_add_neg] using
      reflected_south_center (P.deviation 4) (P.radial 4) (P.transverse 4)
  have hswap (p q : Point) : sub (diagonalPoint p) (diagonalPoint q)=diagonalPoint (sub p q) := rfl
  apply pair_work_bound (P.ownAxis 0) (P.ownAxis 4) (facetOf v)
    (an := P.radial 0) (bn := -P.transverse 0) (aw := P.radial 4)
    (c := diagonalPoint P.center) ⟨hc.2,hc.1⟩
    (by simpa only [abs_neg] using square_box P 0)
    (by simpa only [abs_neg] using square_box P 4)
  · rw [angularWidth_neg,central_axis_east,hNE,hswap,dot_diagonalPoint,P.square_def,he]
    exact hE
  · rw [angularWidth_neg,central_axis_south,hWS,hswap,dot_diagonalPoint,P.square_def,hs]
    exact hS
  · rw [preferred_eastsouth_axis,hNE,hWS,hswap,dot_diagonalPoint,P.square_def 4,
      P.square_def 0,hs,he]
    exact hsel

/-! ### The turned square -/

/-- The separating inequalities of W–D and D–S along the secondary axes of W and
S, with the weight `mStar`, and the support of D bound the diagonal term. -/
lemma diagonal_work (P : NormalizedPacking radius)
    (h : WingSeparators P)
    (hd : DiagonalDomain (P.deviation 2) (P.deviation 4) P.diagonalAngle) :
    diagonalValue (P.deviation 2) (P.deviation 4) P.diagonalAngle≤
      mStar*(-1-P.transverse 2+P.transverse 4) := by
  have hw := Wings.west_wing h.1
  have hs := Wings.south_wing h.2
  dsimp only [Wings.Chart.WestWing,Wings.Chart.SouthWing,Wings.chart] at hw hs
  rw [← sub_eq_add_neg] at hw
  have hsupp := diagonal_work_le hd (square_box P 3)
  have hwm := mul_le_mul_of_nonneg_left hw mStar_pos.le
  have hsm := mul_le_mul_of_nonneg_left hs mStar_pos.le
  dsimp [diagonalValue,diagonalLocalForce] at hsupp ⊢
  nlinarith only [hwm,hsm,hsupp]

/-! ### The domains of the angles -/

/-- The angles of N, W and of E, S, with signs reversed, lie in the domain of the
pair estimate, and those of W, S and D in the domain of the diagonal remainder:
by the windows, the signs of the angles of W and S separated along their own
axes, and the tails. -/
lemma angle_domains {R : ℝ} (P : NormalizedPacking R) :
    Pair.Domain (P.ownAxis 1) (P.ownAxis 2) (P.deviation 1) (P.deviation 2) ∧
    Pair.Domain (P.ownAxis 0) (P.ownAxis 4) (-P.deviation 0) (-P.deviation 4) ∧
    DiagonalDomain (P.deviation 2) (P.deviation 4) P.diagonalAngle := by
  have hn : Pair.nLow (P.ownAxis 1)≤P.deviation 1 ∧
      P.deviation 1≤Pair.nHigh (P.ownAxis 1) := by
    cases h : P.ownAxis 1
    · have := abs_lt.mp (P.north_cardinal_angle_203 h)
      constructor <;> simp only [Pair.nLow,Pair.nHigh,Bool.false_eq_true,ite_false] <;> linarith
    · have := P.deviation_windows.2.1
      constructor <;> simp only [Pair.nLow,Pair.nHigh,ite_true] <;> linarith
  have hw : Pair.wLow (P.ownAxis 2)≤P.deviation 2 ∧
      P.deviation 2≤Pair.wHigh (P.ownAxis 2) := by
    cases h : P.ownAxis 2
    · have := abs_lt.mp (P.cardinal_angle 2 h)
      constructor <;> simp only [Pair.wLow,Pair.wHigh,Bool.false_eq_true,ite_false] <;> linarith
    · have := WestTail.own_west_bound P
        (wing_separators P) h
      have := own_west_negative P h
      constructor <;> simp only [Pair.wLow,Pair.wHigh,ite_true] <;> linarith
  have he : Pair.nLow (P.ownAxis 0)≤-P.deviation 0 ∧
      -P.deviation 0≤Pair.nHigh (P.ownAxis 0) := by
    cases h : P.ownAxis 0
    · have := abs_lt.mp (P.east_cardinal_angle_203 h)
      constructor <;> simp only [Pair.nLow,Pair.nHigh,Bool.false_eq_true,ite_false] <;> linarith
    · have := P.deviation_windows.1
      constructor <;> simp only [Pair.nLow,Pair.nHigh,ite_true] <;> linarith
  have hs : Pair.wLow (P.ownAxis 4)≤-P.deviation 4 ∧
      -P.deviation 4≤Pair.wHigh (P.ownAxis 4) := by
    cases h : P.ownAxis 4
    · have := abs_lt.mp (P.cardinal_angle 4 h)
      constructor <;> simp only [Pair.wLow,Pair.wHigh,Bool.false_eq_true,ite_false] <;> linarith
    · have := SouthTail.own_south_bound P h
      have := own_south_positive P h
      constructor <;> simp only [Pair.wLow,Pair.wHigh,ite_true] <;> linarith
  have hwb : -11/25≤P.deviation 2 ∧ P.deviation 2≤2/5 := by
    cases h : P.ownAxis 2 <;> simp only [h,Pair.wLow,Pair.wHigh,Bool.false_eq_true,ite_false,
      ite_true] at hw <;> constructor <;> linarith
  have hsb : -2/5≤P.deviation 4 ∧ P.deviation 4≤11/25 := by
    cases h : P.ownAxis 4 <;> simp only [h,Pair.wLow,Pair.wHigh,Bool.false_eq_true,ite_false,
      ite_true] at hs <;> constructor <;> linarith
  exact ⟨⟨hn,hw⟩,⟨he,hs⟩,hwb,hsb,(normalized_diagonal_gt_half P).le,
    P.diagonal_angle_bounds.2⟩

/-! ### The theorem -/

/-- At the angles of the model, with N–W and E–S separated along the axes of the
model, the separating inequalities of the stress are the eight contacts. -/
lemma contacts_of_model_angles (P : NormalizedPacking radius)
    (hphase : P.phase=Normalization.modelPhase) {u v : Fin 4} (hu : u=0 ∨ u=3) (hv : v=0 ∨ v=3)
    (hNW : SAT.threshold (P.square 2) (P.square 1) ≤
      dot (preferredPairAxis northWestSigns (P.square 2) (P.square 1) u)
        (sub (P.square 1).center (P.square 2).center))
    (hES : SAT.threshold (P.square 4) (P.square 0) ≤
      dot (preferredPairAxis eastSouthSigns (P.square 4) (P.square 0) v)
        (sub (P.square 0).center (P.square 4).center)) :
    Equality.Contacts P.center P.radial P.transverse := by
  have hp (i : Fin 5) : P.phase i=Normalization.modelPhase i := by rw [hphase]
  have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3; have h4 := hp 4
  simp only [Normalization.modelPhase,Fin.isValue,Matrix.cons_val] at h0 h1 h2 h3 h4
  have hNWaxis : preferredPairAxis northWestSigns (P.square 2) (P.square 1) u=(1,0) := by
    rcases hu with rfl | rfl <;>
      simp [preferredPairAxis,unsignedPairAxis,northWestSigns,P.square_def,h1,h2,normalX,normalY,
        orientedSquare,scale]
  have hESaxis : preferredPairAxis eastSouthSigns (P.square 4) (P.square 0) v=(0,1) := by
    rcases hv with rfl | rfl <;>
      simp [preferredPairAxis,unsignedPairAxis,eastSouthSigns,P.square_def,h0,h4,normalX,normalY,
        orientedSquare,scale,south_cos,south_sin]
  rw [hNWaxis,P.square_def 2,P.square_def 1,h2,h1,oriented_pair_threshold,
    show Real.pi/2-Real.pi=-(Real.pi/2) by ring] at hNW
  rw [hESaxis,P.square_def 4,P.square_def 0,h4,h0,oriented_pair_threshold] at hES
  have hD := wing_separators P
  have hWD := hD.1
  change SAT.threshold (P.square 2) (P.square 3) ≤
    frameY (P.square 2) (sub (P.square 3).center (P.square 2).center) at hWD
  rw [P.square_def 2,P.square_def 3,h2,h3,oriented_pair_threshold,pair_frameY_left,
    show 5*Real.pi/4-Real.pi=Real.pi/4 by ring] at hWD
  have hDS := hD.2
  change SAT.threshold (P.square 3) (P.square 4) ≤
    frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at hDS
  rw [P.square_def 3,P.square_def 4,h3,h4,oriented_pair_threshold,pair_frameY_right,
    show 3*Real.pi/2-5*Real.pi/4=Real.pi/4 by ring] at hDS
  have hside (i : Fin 5) := P.two_choice i
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rcases hside 0 with h | h <;> rw [h0] at h <;>
      norm_num [matchingCardinal,centralMargin,centralNormal,centerX,angularWidth] at h <;>
      linarith
  · rcases hside 1 with h | h <;> rw [h1] at h <;>
      norm_num [matchingCardinal,centralMargin,centralNormal,centerY,angularWidth] at h <;>
      linarith
  · rcases hside 2 with h | h <;> rw [h2] at h <;>
      norm_num [matchingCardinal,centralMargin,centralNormal,centerX,angularWidth] at h <;>
      linarith
  · rcases hside 4 with h | h <;> rw [h4] at h <;>
      norm_num [matchingCardinal,centralMargin,centralNormal,centerY,angularWidth,
        south_cos,south_sin] at h <;>
      linarith
  · simp [angularWidth,dot,sub,orientedSquare] at hNW
    linarith
  · simp [angularWidth,dot,sub,orientedSquare,south_cos,south_sin] at hES
    linarith
  · rw [angularWidth,cos_quarter,sin_quarter,abs_of_pos hStar_pos] at hWD
    nlinarith only [hWD]
  · rw [angularWidth,cos_quarter,sin_quarter,abs_of_pos hStar_pos] at hDS
    nlinarith only [hDS]

/-- Theorem 10.12: in the disk of radius `radius` the exterior squares of a
normalized packing are turned as in the model, and the eight contacts hold. -/
theorem stress_bound (P : NormalizedPacking radius) :
    P.phase=Normalization.modelPhase ∧ Equality.Contacts P.center P.radial P.transverse := by
  obtain ⟨hNW,hES,hdiag⟩ := angle_domains P
  obtain ⟨u,hu⟩ := P.northWest_separator
  obtain ⟨v,hv⟩ := P.eastSouth_separator
  have hwNW := northwest_work P u hu
  have hwES := eastsouth_work P v hv
  have hwD := diagonal_work P (wing_separators P) hdiag
  have hlNW := Pair.lower_bound (facetOf u) hNW
  have hlES := Pair.lower_bound (facetOf v) hES
  rw [abs_neg] at hlES
  have hrem := remainder_nonnegative hdiag
  have hn : P.deviation 1=0 := abs_eq_zero.mp (le_antisymm (by
    dsimp [remainder] at hrem
    nlinarith [abs_nonneg (P.deviation 1),abs_nonneg (P.deviation 0)]) (abs_nonneg _))
  have he : P.deviation 0=0 := abs_eq_zero.mp (le_antisymm (by
    dsimp [remainder] at hrem
    nlinarith [abs_nonneg (P.deviation 1),abs_nonneg (P.deviation 0)]) (abs_nonneg _))
  have hz : remainder (P.deviation 2) (P.deviation 4) P.diagonalAngle=0 := by
    apply le_antisymm _ hrem
    dsimp [remainder]
    nlinarith [abs_nonneg (P.deviation 1),abs_nonneg (P.deviation 0)]
  obtain ⟨hw,hs,hd⟩ := remainder_zero hdiag hz
  have hphase : P.phase=Normalization.modelPhase := by
    funext i
    fin_cases i
    · simpa [matchingCardinal,cardinalCenter,he,Normalization.modelPhase] using P.phase_from_deviation 0
    · simpa [matchingCardinal,cardinalCenter,hn,Normalization.modelPhase] using P.phase_from_deviation 1
    · simpa [matchingCardinal,cardinalCenter,hw,Normalization.modelPhase] using P.phase_from_deviation 2
    · show P.phase 3=5*Real.pi/4
      have := hd; dsimp [NormalizedPacking.diagonalAngle] at this; linarith
    · simpa [matchingCardinal,cardinalCenter,hs,Normalization.modelPhase] using P.phase_from_deviation 4
  rw [hn,hw] at hwNW hlNW
  rw [he,hs,neg_zero] at hwES hlES
  have hD0 : diagonalValue 0 0 (Real.pi/4)=-2*pairBase := by
    have h := hz
    rw [hw,hs,hd] at h
    dsimp [remainder] at h
    norm_num [line] at h
    linarith
  rw [hw,hs,hd,hD0] at hwD
  norm_num [line] at hlNW hlES
  have hmodel (i : Fin 4) (h : (facetOf i).model) : i=0 ∨ i=3 := by
    fin_cases i <;> simp_all [facetOf,Facet.model]
  have hu0 := hmodel u (Pair.model_of_value_origin (by linarith))
  have hv0 := hmodel v (Pair.model_of_value_origin (by linarith))
  exact ⟨hphase,contacts_of_model_angles P hphase hu0 hv0 hu hv⟩

end SquaresInCircles.Six.Stress
