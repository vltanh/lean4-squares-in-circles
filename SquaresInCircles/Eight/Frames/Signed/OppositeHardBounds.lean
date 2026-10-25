module

public import SquaresInCircles.Eight.Owners.Endpoint.RotationPenalty

/-!
# Eight squares: circle and angle bounds for the opposite envelope

The middle tangent of the opposite envelope is split at the rational tangent
`pivot = 3953/5000`, just above the left contact at the angle zero, into a low range of length
`lowLength` and a high range of length `highLength` (`low_domain`, `high_domain`). On each range,
the radii and the angles of the left and the right circles are bounded by polynomials in the
distance `d` to the pivot, with a positive square reserve in the containment at the level `qCap`
(`left_bounds`, `left_square_reserve`, `left_angle_polynomial`, `left_angle_contact`,
`left_angle_transverse`, `high_left_square`, `right_bounds_low`, `right_bounds_high`,
`right_square_low`, `right_square_high`). Each comparison is one polynomial inequality on its
whole interval. The two circle inequalities are enlarged to `qCap` only to derive these upper
bounds; the points, frames and owners stay as they are.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedOppositeHardEnvelope
open EndpointRotationPenalty

def pivot : ℝ := 3953/5000
def lowLength : ℝ := 1453/5000
def highLength : ℝ := 547/5000
def leftRadius (d : ℝ) : ℝ := 3/2+(861/1000)*d-(503/1000)*d^2
def leftAngle (d : ℝ) : ℝ := (673/1000)*d
def rightRadius (x : ℝ) : ℝ := 9237/5000+(48/125)*x-(73/250)*x^2
def rightY (x : ℝ) : ℝ := 3547/5000-x
def referenceAngle (x : ℝ) : ℝ := 12/25+(31/20)*x
def lowTolerance (d : ℝ) : ℝ := 1/500+d/25
def highTolerance (d : ℝ) : ℝ := 1/500+d/10

theorem low_domain {b : ℝ} (hb : b∈Icc (1/2 : ℝ) pivot) :
    pivot-b∈Icc 0 lowLength := by
  dsimp [pivot,lowLength] at *
  constructor <;> linarith [hb.1,hb.2]

theorem high_domain {b : ℝ} (hb : b∈Icc pivot (9/10 : ℝ)) :
    b-pivot∈Icc 0 highLength := by
  dsimp [pivot,highLength] at *
  constructor <;> linarith [hb.1,hb.2]

theorem left_bounds {d : ℝ} (hd : d∈Icc 0 lowLength) :
    leftRadius d∈Icc (3/2 : ℝ) (9/5) ∧
      leftAngle d∈Icc 0 (1/5 : ℝ) ∧
      pivot+1/2-d∈Icc (1 : ℝ) (13/10) := by
  have hd2 := pow_le_pow_left₀ hd.1 hd.2 2
  have hlinear : 0≤861/1000-(503/1000)*d := by
    dsimp [lowLength] at hd
    linarith [hd.2]
  have hprod := mul_nonneg hd.1 hlinear
  dsimp [leftRadius,leftAngle,pivot,lowLength] at *
  refine ⟨⟨by nlinarith,by nlinarith [sq_nonneg d]⟩,
    ⟨by linarith [hd.1],by linarith [hd.2]⟩,?_⟩
  constructor <;> linarith [hd.1,hd.2]

/-- `leftRadius d` is a quadratic majorant of the left circle: the point at the abscissa
`leftRadius d` and the height `pivot + 1/2 - d` lies outside the disk of squared radius `qCap`. -/
theorem left_square_reserve {d : ℝ} (hd : d∈Icc 0 lowLength) :
    qCap<(leftRadius d)^2+(pivot+1/2-d)^2 := by
  have hcoef : 0≤232321/1000000-(433083/500000)*d+
      (253009/1000000)*d^2 := by
    have hs := sq_nonneg (d-lowLength)
    dsimp [lowLength] at hd hs
    nlinarith [hd.2]
  have hid : (leftRadius d)^2+(pivot+1/2-d)^2-qCap=
      1209/25000000+(9/5000)*d+
        d^2*(232321/1000000-(433083/500000)*d+
          (253009/1000000)*d^2) := by
    dsimp [leftRadius,pivot,qCap]
    ring
  have hpositive : 0<1209/25000000+(9/5000)*d+
      d^2*(232321/1000000-(433083/500000)*d+
        (253009/1000000)*d^2) := by
    linarith [mul_nonneg (sq_nonneg d) hcoef,hd.1]
  generalize qCap=Q at hid ⊢
  linarith

/-- One quadratic reserve bounds the left angle polynomial on the whole low range. -/
theorem left_angle_polynomial {d : ℝ} (hd : d∈Icc 0 lowLength) :
    (leftRadius d-1)*(1-(leftAngle d)^2/2+(leftAngle d)^4/24)-
      (pivot+1/2-d)*(leftAngle d-(leftAngle d)^3/6)≤1/2 := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h3 := mul_le_mul_of_nonneg_right hd.2 (sq_nonneg d)
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg d)
  have h5 := pow_nonneg hd.1 5
  have hquadratic :
      -37869/5000000+(227071/4000000)*d-(109/1000)*d^2≤0 := by
    nlinarith [sq_nonneg (d-5677/21800),sq_nonneg d,hd.1]
  have htail :
      -(1294188907233/10000000000000)*d^2+
        (3234333831041/48000000000000)*d^3+
        (58876522884767/8000000000000000)*d^4-
        (103187773557623/24000000000000000)*d^5≤
          -(109/1000)*d^2 := by
    dsimp [lowLength] at h3 h4
    nlinarith [sq_nonneg d]
  have hpoly :
      -37869/5000000+(227071/4000000)*d-
        (1294188907233/10000000000000)*d^2+
        (3234333831041/48000000000000)*d^3+
        (58876522884767/8000000000000000)*d^4-
        (103187773557623/24000000000000000)*d^5≤0 := by linarith
  have hm := mul_nonpos_of_nonneg_of_nonpos hd.1 hpoly
  have hid : (leftRadius d-1)*
      (1-(leftAngle d)^2/2+(leftAngle d)^4/24)-
      (pivot+1/2-d)*(leftAngle d-(leftAngle d)^3/6)-1/2=
      d*(-37869/5000000+(227071/4000000)*d-
        (1294188907233/10000000000000)*d^2+
        (3234333831041/48000000000000)*d^3+
        (58876522884767/8000000000000000)*d^4-
        (103187773557623/24000000000000000)*d^5) := by
    dsimp [leftRadius,leftAngle,pivot]
    ring
  linarith

theorem left_angle_contact {d : ℝ} (hd : d∈Icc 0 lowLength) :
    (leftRadius d-1)*Real.cos (leftAngle d)-
      (pivot+1/2-d)*Real.sin (leftAngle d)≤1/2 := by
  obtain ⟨hR,hz,hY⟩ := left_bounds hd
  have hc := mul_le_mul_of_nonneg_left (cos_upper_four hz.1)
    (show 0≤leftRadius d-1 by linarith [hR.1])
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hz.1)
    (show 0≤pivot+1/2-d by linarith [hY.1])
  linarith [left_angle_polynomial hd]

theorem left_angle_transverse {d : ℝ} (hd : d∈Icc 0 lowLength) :
    charge≤(leftRadius d-1)*Real.sin (leftAngle d)+
        (pivot+1/2-d)*Real.cos (leftAngle d) ∧
      (leftRadius d-1)*Real.sin (leftAngle d)+
        (pivot+1/2-d)*Real.cos (leftAngle d)≤3/2 := by
  obtain ⟨hR,hz,hY⟩ := left_bounds hd
  have hz' : leftAngle d∈Icc 0 frameCap :=
    ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have htr := transport_trig hz'
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hz2 hz.1
  have hsinLower : (149/150)*leftAngle d≤Real.sin (leftAngle d) := by
    nlinarith [Real.sin_ge_sub_cube hz.1]
  have hcosLower : 49/50≤Real.cos (leftAngle d) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := leftAngle d)]
  have hsL := mul_le_mul_of_nonneg_right
    (show (1/2 : ℝ)≤leftRadius d-1 by linarith [hR.1]) htr.2.2.1
  have hcL := mul_le_mul_of_nonneg_left hcosLower
    (show 0≤pivot+1/2-d by linarith [hY.1])
  have hsU := mul_le_mul
    (show leftRadius d-1≤4/5 by linarith [hR.2])
    (Real.sin_le hz.1) htr.2.2.1 (by norm_num : (0:ℝ)≤4/5)
  have hcU := mul_le_mul_of_nonneg_left (Real.cos_le_one (leftAngle d))
    (show 0≤pivot+1/2-d by linarith [hY.1])
  constructor
  · dsimp [leftAngle,pivot,charge,lowLength] at *
    nlinarith [hd.2]
  · linarith [hz.2,hY.2]

theorem high_left_square {d : ℝ} (hd : 0≤d) :
    qCap<(3/2-(43/50)*d)^2+(pivot+1/2+d)^2 := by
  have hid : (3/2-(43/50)*d)^2+(pivot+1/2+d)^2-qCap=
      1209/25000000+(3/2500)*d+(4349/2500)*d^2 := by
    dsimp [pivot,qCap]
    ring
  have hp : 0<1209/25000000+(3/2500)*d+(4349/2500)*d^2 := by positivity
  linarith

theorem right_bounds_low {d : ℝ} (hd : d∈Icc 0 lowLength) :
    rightRadius (-d)∈Icc (17/10 : ℝ) (19/10) ∧
      rightY (-d)∈Icc (7/10 : ℝ) 1 ∧
      referenceAngle (-d)∈Icc 0 (12/25 : ℝ) ∧
      lowTolerance d∈Icc 0 (1/50 : ℝ) := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  dsimp [rightRadius,rightY,referenceAngle,lowTolerance,lowLength] at *
  refine ⟨⟨by nlinarith [hd.1,hd.2],by nlinarith [sq_nonneg d,hd.1]⟩,
    ⟨by linarith [hd.1],by linarith [hd.2]⟩,
    ⟨by linarith [hd.2],by linarith [hd.1]⟩,
    ⟨by linarith [hd.1],by linarith [hd.2]⟩⟩

theorem right_bounds_high {d : ℝ} (hd : d∈Icc 0 highLength) :
    rightRadius d∈Icc (17/10 : ℝ) (19/10) ∧
      rightY d∈Icc (3/5 : ℝ) (71/100) ∧
      referenceAngle d∈Icc (12/25 : ℝ) (13/20) ∧
      highTolerance d∈Icc 0 (1/50 : ℝ) := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  dsimp [rightRadius,rightY,referenceAngle,highTolerance,highLength] at *
  refine ⟨⟨by nlinarith,by nlinarith [sq_nonneg d]⟩,
    ⟨by linarith [hd.2],by linarith [hd.1]⟩,
    ⟨by linarith [hd.1],by linarith [hd.2]⟩,
    ⟨by linarith [hd.1],by linarith [hd.2]⟩⟩

theorem right_square_low {d : ℝ} (hd : d∈Icc 0 lowLength) :
    qCap<(rightRadius (-d))^2+(rightY (-d))^2 := by
  have hbase : 0<6689/12500000-d/312500 := by
    dsimp [lowLength] at hd
    linarith [hd.2]
  have hid : (rightRadius (-d))^2+(rightY (-d))^2-qCap=
      6689/12500000-d/312500+(42859/625000)*d^2+
        (3504/15625)*d^3+(5329/62500)*d^4 := by
    dsimp [rightRadius,rightY,qCap]
    ring
  have hp : 0<6689/12500000-d/312500+(42859/625000)*d^2+
      (3504/15625)*d^3+(5329/62500)*d^4 := by
    linarith [sq_nonneg d,pow_nonneg hd.1 3,pow_nonneg hd.1 4]
  generalize qCap=Q at hid ⊢
  linarith

theorem right_square_high {d : ℝ} (hd : d∈Icc 0 highLength) :
    qCap<(rightRadius d)^2+(rightY d)^2 := by
  have hcoef : 0≤42859/625000-(3504/15625)*d := by
    dsimp [highLength] at hd
    linarith [hd.2]
  have hid : (rightRadius d)^2+(rightY d)^2-qCap=
      6689/12500000+d/312500+
        d^2*(42859/625000-(3504/15625)*d)+(5329/62500)*d^4 := by
    dsimp [rightRadius,rightY,qCap]
    ring
  have hp : 0<6689/12500000+d/312500+
      d^2*(42859/625000-(3504/15625)*d)+(5329/62500)*d^4 := by
    linarith [mul_nonneg (sq_nonneg d) hcoef,hd.1,pow_nonneg hd.1 4]
  generalize qCap=Q at hid ⊢
  linarith

end SquaresInCircles.Eight.SignedOppositeHardEnvelope
