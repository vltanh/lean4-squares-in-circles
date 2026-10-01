import SquaresInCircles.Six.Supports

/-!
# The stress of the pair N, W

The stress bound reads the squares N and W through the forces of four edges, in
the frames of N and W: weight one on C–N and C–W, along the own axis of each
square or along the side of C, weight `rStar` on N–W, along a `Facet`, an axis
of W or of N, and weight `mStar` on W–D along the secondary axis of W. The
value of the pair is the threshold sum of these edges less bounds for the works
of the forces on N and W, and less a penalty for the work of the change of the
force on C, whose centre lies in `[0, c0]²`. The work of a force `(x, y)` on a
square in the disk of radius `radius` is at most `R₆ |(x, y)| - (|x| + |y|)/2`
by Cauchy–Schwarz at the far vertex, and at most `rhoStar |(x, y)|`, since the
centre lies within `rhoStar` of the disk centre. At zero angles, with N–W along
a facet of the contact of the model, the forces are those of the model and the
value is `pairBase`. Elsewhere the value is compared with
`pairBase + line w + |n|/1000`, where the broken line `line w` in the angle of W
is paid for by the turned square.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

/-- The part `line w` of the lower bound of a pair that the turned square pays
for: of slope `-18/25` for `w ≤ 0` and `-13/50` for `w ≥ 0`. -/
def line (w : ℝ) : ℝ := (18/25)*max (-w) 0-(13/50)*max w 0

/-- The axis along which N–W is separated: the primary or secondary axis of W or
of N, directed from W to N. -/
inductive Facet where
  | westFirst | westSecond | northFirst | northSecond
  deriving DecidableEq

namespace Facet

/-- The facets of the contact N–W of the model, horizontal at zero angles. -/
def model : Facet → Bool
  | westFirst => true
  | westSecond => false
  | northFirst => false
  | northSecond => true

/-- The normal of N–W in the frame of N, at `q = n - w`. -/
def north : Facet → ℝ → Point
  | westFirst, q => (-Real.sin q,-Real.cos q)
  | westSecond, q => (Real.cos q,-Real.sin q)
  | northFirst, _ => (1,0)
  | northSecond, _ => (0,-1)

/-- Minus the normal of N–W in the frame of W, at `q = n - w`. -/
def west : Facet → ℝ → Point
  | westFirst, _ => (1,0)
  | westSecond, _ => (0,1)
  | northFirst, q => (-Real.sin q,Real.cos q)
  | northSecond, q => (Real.cos q,Real.sin q)

end Facet

namespace Pair

/-- The normal of C–N in the frame of N at the angle `t`, or of C–W in the frame
of W: the own axis, or the side of C. -/
def central (own : Bool) (t : ℝ) : Point := if own then (1,0) else (Real.cos t,-Real.sin t)

/-- The force on N in its frame. -/
def northForce (no : Bool) (f : Facet) (n w : ℝ) : Point :=
  ((central no n).1+rStar*(f.north (n-w)).1,(central no n).2+rStar*(f.north (n-w)).2)

/-- The force on W in its frame. -/
def westForce (wo : Bool) (f : Facet) (n w : ℝ) : Point :=
  ((central wo w).1+rStar*(f.west (n-w)).1,(central wo w).2+rStar*(f.west (n-w)).2-mStar)

/-- The thresholds of C–N, C–W, N–W with the weight `rStar`, and half that of W–D
with the weight `mStar`. -/
def threshold (n w : ℝ) : ℝ :=
  (1/2+angularWidth n)+(1/2+angularWidth w)+rStar*(1/2+angularWidth (n-w))+mStar/2

/-- A bound for the work of the change of the force on C, for N and W separated
from C along their own axes. -/
def penalty (no wo : Bool) (n w : ℝ) : ℝ :=
  (if no then c0*(max (Real.sin n) 0+1-Real.cos n) else 0)+
    (if wo then c0*max (Real.sin w) 0 else 0)

/-- The far-vertex bound `R₆ |F| - (x - y)/2` for the work of `F = (x, y)`. -/
def vertexBound (F : Point) : ℝ := radius*Real.sqrt (F.1^2+F.2^2)-(F.1-F.2)/2

/-- The bound for the work of the force on N: the far-vertex bound for the
facets of the model, `rhoStar |F|` for the others. -/
def northBound (f : Facet) (F : Point) : ℝ :=
  if f.model then vertexBound F else rhoStar*Real.sqrt (F.1^2+F.2^2)

/-- The value of the pair: thresholds less the bounds for the works and the
penalty. -/
def value (no wo : Bool) (f : Facet) (n w : ℝ) : ℝ :=
  threshold n w-northBound f (northForce no f n w)-vertexBound (westForce wo f n w)-
    penalty no wo n w

/-- The work of `F` on a centre `(a, b)` of a square in the disk of radius
`radius` is at most the far-vertex bound. -/
lemma work_le_vertexBound {a b : ℝ} (F : Point)
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2≤radius^2) : F.1*a+F.2*b≤vertexBound F := by
  have h := box_vertex_support radius_pos.le hbox F.1 F.2
  dsimp [vertexBound]
  linarith [le_abs_self F.1,neg_abs_le F.2]

/-- The centre of a square in the disk of radius `radius` lies within `rhoStar`
of the disk centre. -/
lemma center_radial_bound {a b : ℝ} (hbox : (|a|+1/2)^2+(|b|+1/2)^2≤radius^2) :
    a^2+b^2≤rhoStar^2 := by
  have h := radial_sq_le_of_phi (ρ := rhoStar) (by linarith [rhoStar_bounds.1]) (abs_nonneg a)
    (abs_nonneg b)
    (by rw [rhoStar_identity,← radius_sq]; exact hbox)
  simpa only [sq_abs] using h

lemma work_le_northBound {a b : ℝ} (f : Facet) (F : Point)
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2≤radius^2) : F.1*a+F.2*b≤northBound f F := by
  unfold northBound
  split_ifs
  · exact work_le_vertexBound F hbox
  · have h := dot_le_radius (v := F) (p := (a,b)) (R := rhoStar) (by linarith [rhoStar_bounds.1])
      (by simpa only [normSq] using center_radial_bound hbox)
    simpa only [dot,vectorLength,normSq] using h

/-- At zero angles, along a facet of the contact of the model, the forces are
those of the model and the value is `pairBase`. -/
lemma value_origin (no wo : Bool) {f : Facet} (hf : f.model) : value no wo f 0 0=pairBase := by
  have hN : northForce no f 0 0=(1,-rStar) := by
    cases f <;> cases no <;> simp_all [northForce,central,Facet.north,Facet.model]
  have hW : westForce wo f 0 0=(1+rStar,-mStar) := by
    cases f <;> cases wo <;> simp_all [westForce,central,Facet.west,Facet.model]
  have hp : penalty no wo 0 0=0 := by cases no <;> cases wo <;> norm_num [penalty]
  have ht : threshold 0 0=2+rStar+mStar/2 := by norm_num [threshold,angularWidth]
  have hNl := radius_mul_north_length
  have hWl := radius_mul_west_length
  simp only [value,northBound,hf,ite_true,hN,hW,hp,ht,vertexBound,neg_sq] at hNl hWl ⊢
  rw [one_pow,hNl,hWl]
  dsimp [pairBase]
  ring

/-- The force of the two central edges on C minus its value `(1, -1)` at zero
angles. -/
def centralExcess (no wo : Bool) (n w : ℝ) : Point :=
  ((if no then Real.sin n else 0)+(if wo then Real.cos w-1 else 0),
   (if no then 1-Real.cos n else 0)+(if wo then Real.sin w else 0))

/-- On a centre of C in `[0, c0]²` the work of `centralExcess` is at most the
penalty. -/
lemma central_excess_support {c : Point}
    (hc : (0≤c.1 ∧ c.1≤c0) ∧ (0≤c.2 ∧ c.2≤c0)) (no wo : Bool) (n w : ℝ) :
    dot (centralExcess no wo n w) c≤penalty no wo n w := by
  have hsn : c.1*Real.sin n≤c0*max (Real.sin n) 0 := scalar_box_support hc.1
  have hsw : c.2*Real.sin w≤c0*max (Real.sin w) 0 := scalar_box_support hc.2
  have hwn := mul_nonpos_of_nonneg_of_nonpos hc.1.1 (sub_nonpos.mpr (Real.cos_le_one w))
  have hcn := mul_le_mul_of_nonneg_right hc.2.2 (sub_nonneg.mpr (Real.cos_le_one n))
  cases no <;> cases wo <;> dsimp [centralExcess,penalty,dot] <;> nlinarith

/-! ### The domain of the pair estimate -/

/-- The ends of the ranges of `n` and `w`, by the separators of N and W from C. -/
def nLow (no : Bool) : ℝ := if no then -3/10 else -203/1000
def nHigh (no : Bool) : ℝ := if no then 5/12 else 203/1000
def wLow (wo : Bool) : ℝ := if wo then -11/25 else -2/5
def wHigh (wo : Bool) : ℝ := if wo then 0 else 2/5

/-- The angles of N and W in the pair estimate: `n` in `[-3/10, 5/12]` for N
separated along its own axis, else in `[-203/1000, 203/1000]`; `w` in
`[-11/25, 0]` for W separated along its own axis, else in `[-2/5, 2/5]`. -/
def Domain (no wo : Bool) (n w : ℝ) : Prop :=
  (nLow no≤n ∧ n≤nHigh no) ∧ (wLow wo≤w ∧ w≤wHigh wo)

lemma domain_bounds {no wo : Bool} {n w : ℝ} (h : Domain no wo n w) :
    -3/10≤n ∧ n≤5/12 ∧ -11/25≤w ∧ w≤2/5 ∧ -7/10≤n-w ∧ n-w≤6/7 := by
  obtain ⟨⟨hn0,hn1⟩,hw0,hw1⟩ := h
  cases no <;> cases wo <;> simp only [nLow,nHigh,wLow,wHigh,Bool.false_eq_true,ite_false,
    ite_true] at hn0 hn1 hw0 hw1
  all_goals refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

lemma domain_abs {no wo : Bool} {n w : ℝ} (h : Domain no wo n w) :
    |n|≤5/12 ∧ |w|≤11/25 ∧ |n-w|≤6/7 := by
  obtain ⟨hn0,hn1,hw0,hw1,hq0,hq1⟩ := domain_bounds h
  exact ⟨abs_le.mpr ⟨by linarith,hn1⟩,abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,hq1⟩⟩

/-- The value of the pair less `pairBase`, the line and `|n|/1000`. -/
def gap (no wo : Bool) (f : Facet) (n w : ℝ) : ℝ :=
  value no wo f n w-pairBase-line w-|n|/1000

end Pair
end SquaresInCircles.Six.Stress
