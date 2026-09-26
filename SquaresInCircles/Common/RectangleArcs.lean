import SquaresInCircles.Common.Charts

/-!
# Arcs of an exterior square

In a chart an exterior square is the unit square centred at `(a, b)` with
`1/2 ≤ a`. A circle of radius `r` about the disk centre crosses the line of its
near edge at the chart angles `± capA r a`, and the lines of its lower and upper
edges at `-capV r b` and `capU r b`. While the circle does not reach the far
edge, the square holds every chart angle between these crossings. Membership is
in the open square, so disjoint squares hold disjoint arcs.
-/
noncomputable section
open Set
namespace SquaresInCircles

/-- The chart angles at which the circle of radius `r` crosses the lines of the
near, lower and upper edges of the square centred at `(a, b)`: `± capA r a`,
`-capV r b` and `capU r b`. -/
def capA (r a : ℝ) : ℝ := Real.arccos ((a-1/2)/r)
def capV (r b : ℝ) : ℝ := Real.arcsin ((1/2-b)/r)
def capU (r b : ℝ) : ℝ := Real.arcsin ((b+1/2)/r)

/-- Every chart angle strictly between the crossings gives a point of the
square on the circle, as long as the circle does not reach the far edge. -/
lemma cap_mem {a b r t : ℝ} (hr : 0 < r) (hfar : r < a+1/2) (hx : (a-1/2)/r ∈ Icc (0:ℝ) 1)
    (ht : t ∈ Ioo (-min (capA r a) (capV r b)) (min (capA r a) (capU r b))) :
    |r*Real.cos t-a| < 1/2 ∧ |r*Real.sin t-b| < 1/2 := by
  have hA := Real.arccos_le_pi_div_two.mpr hx.1
  have hlo := lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1
  have hlo' := lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) ht.1
  have hhi := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have hhi' := lt_of_lt_of_le ht.2 (min_le_right _ _)
  unfold capA capV capU at *
  have htdom : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := ⟨by linarith,by linarith⟩
  have htc : (a-1/2)/r < Real.cos t := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (show Real.arccos ((a-1/2)/r) ≤ Real.pi by linarith [Real.pi_pos]) (abs_lt.mpr ⟨hlo,hhi⟩)
    rwa [Real.cos_arccos (by linarith [hx.1]) hx.2,Real.cos_abs] at hh
  have hts0 : (b-1/2)/r < Real.sin t := by
    refine (Real.arcsin_lt_iff_lt_sin' ⟨htdom.1,htdom.2.le⟩).mp ?_
    rwa [show (b-1/2)/r=-((1/2-b)/r) by ring,Real.arcsin_neg]
  have hts1 : Real.sin t < (b+1/2)/r := (Real.lt_arcsin_iff_sin_lt' ⟨htdom.1.le,htdom.2⟩).mp hhi'
  have hxc := (div_lt_iff₀ hr).mp htc
  have hyc0 := (div_lt_iff₀ hr).mp hts0
  have hyc1 := (lt_div_iff₀ hr).mp hts1
  have hxr := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hr.le
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

/-- The arc of an exterior square: while the circle of radius `r` does not reach
the far edge, the square holds the chart angles from `-min A V` to `min A U`,
where `A = capA r a`, `V = capV r b` and `U = capU r b`. -/
lemma SquareChart.edge_arc {S : UnitSquare} {o : Point} (C : SquareChart S o) {r : ℝ}
    (hr : 0 < r) (ha : 1/2 ≤ C.a) (ha1 : C.a-1/2 ≤ r) (hfar : r < C.a+1/2)
    (hpos : 0 < min (capA r C.a) (capU r C.b)+min (capA r C.a) (capV r C.b)) :
    ∃ W : OpenArc o r {p | openSquare S p},
      W.halfWidth=(min (capA r C.a) (capU r C.b)+min (capA r C.a) (capV r C.b))/2 ∧
      W.center=chartAngle C.phase C.reversed
        ((min (capA r C.a) (capU r C.b)-min (capA r C.a) (capV r C.b))/2) := by
  have hx : (C.a-1/2)/r ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by linarith) hr.le,(div_le_one hr).mpr ha1⟩
  have hA : capA r C.a ≤ Real.pi/2 := Real.arccos_le_pi_div_two.mpr hx.1
  obtain ⟨W,hw,hc⟩ := C.arc r _ _ (by linarith)
    (by linarith [min_le_left (capA r C.a) (capU r C.b),min_le_left (capA r C.a) (capV r C.b),
      Real.pi_pos])
    fun t ht => cap_mem hr hfar hx ht
  exact ⟨W,by rw [hw]; ring,by rw [hc]; congr 1; ring⟩

/-- The cap: on a circle of radius at most `1/2` the upper edge is out of
reach, and the square holds the chart angles from `-min A V` to `A`. -/
lemma SquareChart.cap_arc {S : UnitSquare} {o : Point} (C : SquareChart S o) {r : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 1/2) (ha : 1/2 ≤ C.a) (ha1 : C.a-1/2 < r) (hb : C.b ≤ 1/2) :
    ∃ W : OpenArc o r {p | openSquare S p},
      W.halfWidth=(capA r C.a+min (capA r C.a) (capV r C.b))/2 ∧
      W.center=chartAngle C.phase C.reversed ((capA r C.a-min (capA r C.a) (capV r C.b))/2) := by
  have hU : min (capA r C.a) (capU r C.b)=capA r C.a := by
    rw [capU,Real.arcsin_of_one_le ((le_div_iff₀ hr).mpr (by linarith [C.nonneg.2]))]
    exact min_eq_left (Real.arccos_le_pi_div_two.mpr (div_nonneg (by linarith) hr.le))
  have hA0 : 0 < capA r C.a := Real.arccos_pos.mpr ((div_lt_one hr).mpr ha1)
  have hV : 0 ≤ capV r C.b := Real.arcsin_nonneg.mpr (div_nonneg (by linarith) hr.le)
  obtain ⟨W,hw,hc⟩ := C.edge_arc hr ha ha1.le (by linarith [C.nonneg.2])
    (by rw [hU]; linarith [le_min hA0.le hV])
  rw [hU] at hw hc
  exact ⟨W,hw,hc⟩

/-- A full cap, `A ≤ V`, is centred on the phase and has half-width `A`. -/
lemma SquareChart.full_cap_arc {S : UnitSquare} {o : Point} (C : SquareChart S o) {r : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 1/2) (ha : 1/2 ≤ C.a) (ha1 : C.a-1/2 < r) (hb : C.b ≤ 1/2)
    (hfull : capA r C.a ≤ capV r C.b) :
    ∃ W : OpenArc o r {p | openSquare S p}, W.halfWidth=capA r C.a ∧ W.center=C.phase := by
  obtain ⟨W,hw,hc⟩ := C.cap_arc hr hr2 ha ha1 hb
  rw [min_eq_left hfull] at hw hc
  exact ⟨W,by rw [hw]; ring,by rw [hc]; simp [chartAngle]⟩

end SquaresInCircles
