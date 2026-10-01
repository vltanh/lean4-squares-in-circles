import SquaresInCircles.Six.Analytic.ReflectedOwnWings.Profile

/-!
# The reflected case: positivity of the value

The value is positive on `48/175 ≤ s ≤ v ≤ 2/3`, `v + s ≤ 24/25`,
`157/200 ≤ d ≤ 163/175`, for both faces of the box. For fixed `d` the domain in
`(v, s)` is the quadrilateral with vertices `(48/175, 48/175)`, `(2/3, 48/175)`,
`(2/3, 22/75)` and `(12/25, 12/25)`. Concavity along its edges `s = v`,
`v = 2/3` and `v + s = 24/25`, and then in `v`, reduces positivity to the
vertices, and concavity in `d` to the two ends of its interval. At these eight
points Taylor polynomials of `sin` and `cos` bound the value below by `1/500`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.ReflectedOwnWings

def FourVertices (upper : Bool) (d : ℝ) : Prop :=
  0 < value upper (48/175) (48/175) d ∧
  0 < value upper (2/3) (48/175) d ∧
  0 < value upper (2/3) (22/75) d ∧
  0 < value upper (12/25) (12/25) d

private lemma equal_wall_concave (upper : Bool) {d : ℝ}
    (hd : 157/200 ≤ d ∧ d ≤ 163/175) :
    ConcaveOn ℝ (Set.Icc (48/175) (12/25)) (fun s => value upper s s d) := by
  have hw0 := concave_affine_argument (a := 1) (b := 0) (west_concave upper hd)
    (l := 48/175) (u := 12/25) (by
      intro s hs
      constructor <;> linarith [hs.1,hs.2])
  have hw : ConcaveOn ℝ (Set.Icc (48/175) (12/25)) (westSlice upper d) := by
    simpa only [one_mul,add_zero] using hw0
  exact ((concave_constant (constantTerm+diagonalTerm upper d) (48/175) (12/25)).add hw).add
    (south_concave upper hd)

private lemma sum_wall_concave (upper : Bool) {d : ℝ}
    (hd : 157/200 ≤ d ∧ d ≤ 163/175) :
    ConcaveOn ℝ (Set.Icc (22/75) (12/25)) (fun s => value upper (24/25-s) s d) := by
  have hw0 := concave_affine_argument (a := -1) (b := 24/25) (west_concave upper hd)
    (l := 22/75) (u := 12/25) (by
      intro s hs
      constructor <;> linarith [hs.1,hs.2])
  have hw : ConcaveOn ℝ (Set.Icc (22/75) (12/25)) (fun s => westSlice upper d (24/25-s)) := by
    convert hw0 using 1
    funext s
    congr 1
    ring
  have hs0 := concave_affine_argument (a := 1) (b := 0) (south_concave upper hd)
    (l := 22/75) (u := 12/25) (by
      intro s hs
      constructor <;> linarith [hs.1,hs.2])
  have hs : ConcaveOn ℝ (Set.Icc (22/75) (12/25)) (southSlice upper d) := by
    simpa only [one_mul,add_zero] using hs0
  exact ((concave_constant (constantTerm+diagonalTerm upper d) (22/75) (12/25)).add hw).add hs

lemma positive_of_four_vertices (upper : Bool) {v s d : ℝ}
    (hs : 48/175 ≤ s ∧ s ≤ 12/25) (horder : s ≤ v) (hv : v ≤ 2/3)
    (hsum : v+s ≤ 24/25) (hd : 157/200 ≤ d ∧ d ≤ 163/175)
    (he : FourVertices upper d) : 0 < value upper v s d := by
  have hleft : 0 < value upper s s d :=
    positive_on_concave_interval (f := fun x => value upper x x d)
      (equal_wall_concave upper hd) hs he.1 he.2.2.2
  have hcv : ConcaveOn ℝ (Set.Icc 0 (2/3)) (fun x => value upper x s d) :=
    ((concave_constant (constantTerm+diagonalTerm upper d) 0 (2/3)).add
      (west_concave upper hd)).add (concave_constant (southSlice upper d s) 0 (2/3))
  by_cases hcut : s ≤ 22/75
  · have hcs : ConcaveOn ℝ (Set.Icc (48/175) (12/25))
        (fun x => value upper (2/3) x d) :=
      (concave_constant (constantTerm+diagonalTerm upper d+westSlice upper d (2/3))
        (48/175) (12/25)).add (south_concave upper hd)
    have hm := hcs.min_le_of_mem_Icc
      (by norm_num : (48:ℝ)/175 ∈ Set.Icc (48/175) (12/25))
      (by norm_num : (22:ℝ)/75 ∈ Set.Icc (48/175) (12/25)) ⟨hs.1,hcut⟩
    have hright : 0 < value upper (2/3) s d := (lt_min he.2.1 he.2.2.1).trans_le hm
    have hvmin := hcv.min_le_of_mem_Icc
      (show s ∈ Set.Icc 0 (2/3) by constructor <;> linarith [hs.1,hs.2])
      (by norm_num : (2:ℝ)/3 ∈ Set.Icc 0 (2/3)) ⟨horder,hv⟩
    exact (lt_min hleft hright).trans_le hvmin
  · have hl : 0 < value upper (24/25-22/75) (22/75) d := by
      convert he.2.2.1 using 1
      norm_num
    have hu : 0 < value upper (24/25-12/25) (12/25) d := by
      convert he.2.2.2 using 1
      norm_num
    have hright := positive_on_concave_interval (sum_wall_concave upper hd)
      ⟨le_of_not_ge hcut,hs.2⟩ hl hu
    have hvmin := hcv.min_le_of_mem_Icc
      (show s ∈ Set.Icc 0 (2/3) by constructor <;> linarith [hs.1,hs.2])
      (show 24/25-s ∈ Set.Icc 0 (2/3) by constructor <;> linarith [hs.2])
      (show s ≤ v ∧ v ≤ 24/25-s by constructor <;> linarith)
    exact (lt_min hleft hright).trans_le hvmin

private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def cosUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/24
private def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
private def sinUpper (x : ℝ) : ℝ := x-x^3/6+x^5/120

private def lowerPolynomial (upper : Bool) (v s d : ℝ) : ℝ :=
  constantTerm+beta*(A*cosLower v+(1/2+face upper)*sinLower v)+
    gamma*((1/2-face upper)*cosLower s+B*sinLower s)+
    delta*(A*cosLower d+(1/2-face upper)*sinLower d)+
    sinLower (d+v)-chordSin*sinUpper ((d+v)/2)-chordCos*cosUpper ((d+v)/2)-
    B*cosUpper (d-s)+(1/2)*sinLower (d-s)-1/24+(1/24)*cosLower (2*(d-s))

private lemma polynomial_le (upper : Bool) {v s d : ℝ}
    (hv : 0 ≤ v) (hs : 0 ≤ s) (hd : 0 ≤ d) (hr : s ≤ d) :
    lowerPolynomial upper v s d ≤ value upper v s d := by
  have cv := Seven.cos_lower_six hv
  have sv := Seven.sin_lower_seven hv
  have cs := Seven.cos_lower_six hs
  have ss := Seven.sin_lower_seven hs
  have cd := Seven.cos_lower_six hd
  have sd := Seven.sin_lower_seven hd
  have sq := Seven.sin_lower_seven (x := d+v) (by linarith)
  have sh := Seven.sin_upper_five (x := (d+v)/2) (by linarith)
  have ch := Seven.cos_upper_four (x := (d+v)/2) (by linarith)
  have cr := Seven.cos_upper_four (x := d-s) (by linarith)
  have sr := Seven.sin_lower_seven (x := d-s) (by linarith)
  have crr := Seven.cos_lower_six (x := 2*(d-s)) (by linarith)
  cases upper <;>
    dsimp [lowerPolynomial,value,westSlice,southSlice,westTerm,southTerm,diagonalTerm,
      chord,transverse,beta,gamma,delta,A,B,face,chordSin,chordCos,
      cosLower,cosUpper,sinLower,sinUpper] <;>
    linarith only [cv,sv,cs,ss,cd,sd,sq,sh,ch,cr,sr,crr]

private def vertexV (i : Fin 4) : ℝ := ![48/175,2/3,2/3,12/25] i
private def vertexS (i : Fin 4) : ℝ := ![48/175,48/175,22/75,12/25] i
private def endpoint (upper : Bool) : ℝ := if upper then 163/175 else 157/200

private lemma endpoint_margin (face endpointSide : Bool) (i : Fin 4) :
    (1:ℝ)/500 < lowerPolynomial face (vertexV i) (vertexS i) (endpoint endpointSide) := by
  cases face <;> cases endpointSide <;> fin_cases i <;>
    norm_num [lowerPolynomial,constantTerm,beta,gamma,delta,A,B,ReflectedOwnWings.face,
      chordSin,chordCos,cosLower,cosUpper,sinLower,sinUpper,vertexV,vertexS,endpoint]

lemma endpoint_positive (upper endpointSide : Bool) (i : Fin 4) :
    0 < value upper (vertexV i) (vertexS i) (endpoint endpointSide) := by
  have hv : 0 ≤ vertexV i := by fin_cases i <;> norm_num [vertexV]
  have hs : 0 ≤ vertexS i := by fin_cases i <;> norm_num [vertexS]
  have hd : 0 ≤ endpoint endpointSide := by cases endpointSide <;> norm_num [endpoint]
  have hr : vertexS i ≤ endpoint endpointSide := by
    cases endpointSide <;> fin_cases i <;> norm_num [vertexS,endpoint]
  have hp := polynomial_le upper hv hs hd hr
  have hm := endpoint_margin upper endpointSide i
  linarith

lemma vertex_positive (upper : Bool) (i : Fin 4) {d : ℝ}
    (hd : 157/200 ≤ d ∧ d ≤ 163/175) :
    0 < value upper (vertexV i) (vertexS i) d := by
  have hv : 0 ≤ vertexV i ∧ vertexV i ≤ 2/3 := by fin_cases i <;> norm_num [vertexV]
  have hs : 48/175 ≤ vertexS i ∧ vertexS i ≤ 12/25 := by fin_cases i <;> norm_num [vertexS]
  exact positive_on_concave_interval (diagonal_concave upper hv hs) hd
    (endpoint_positive upper false i) (endpoint_positive upper true i)

/-- The value of the reflected stress is positive on its whole domain. -/
theorem positive (upper : Bool) {v s d : ℝ}
    (hs : 48/175 ≤ s ∧ s ≤ 12/25) (horder : s ≤ v) (hv : v ≤ 2/3)
    (hsum : v+s ≤ 24/25) (hd : 157/200 ≤ d ∧ d ≤ 163/175) :
    0 < value upper v s d := by
  exact positive_of_four_vertices upper hs horder hv hsum hd
    ⟨vertex_positive upper 0 hd,vertex_positive upper 1 hd,
      vertex_positive upper 2 hd,vertex_positive upper 3 hd⟩

end SquaresInCircles.Six.Analytic.ReflectedOwnWings
