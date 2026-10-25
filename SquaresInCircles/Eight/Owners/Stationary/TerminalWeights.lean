module

public import SquaresInCircles.Eight.Owners.Canonical.NegativeStress
public import SquaresInCircles.Eight.Owners.Stationary.IntervalAlgebra
public import SquaresInCircles.Eight.Owners.Stationary.PrimitiveForces

/-!
# Eight squares: normalized force weights from the actual circle chain

The five raw masses and all edge weights
below are explicit functions of the nested positive radicals.  Their
positivity and normalization are proved on the full terminal rectangle.
Position stationarity is used only in the separate cancellation identity.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.StationaryTerminal
open Stationary.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

def rawAlpha (q u h : ℝ) : ℝ := positionA q (cosine h) (sine h) u
def rawBeta (q u h : ℝ) : ℝ := rawAlpha q u h*topRight q u/(2-u)
def rawEpsilon (q u h : ℝ) : ℝ :=
  secondComponent q (cosine h) (sine h) u/firstComponent q (cosine h) (sine h) u

/-- The mass order is the original-anchor order A,B,D,E,H. -/
def rawMass (q u h : ℝ) : Fin 5 → ℝ := ![
  cosine h/(2*lowerRight q u),
  rawAlpha q u h/(2*(2-u)),
  rawBeta q u h/(2*topLeft q u),
  sine h*rawEpsilon q u h/(2*lowerLeft q u),
  1/(2*firstComponent q (cosine h) (sine h) u)]

def rawMassSum (q u h : ℝ) : ℝ := ∑i : Fin 5,rawMass q u h i
def omega (q u h : ℝ) : ℝ := 1/rawMassSum q u h

def weights (q u h : ℝ) : CanonicalNegativeStress.Parameters where
  a := omega q u h*rawAlpha q u h
  beta := omega q u h*rawBeta q u h
  delta := omega q u h*rawBeta q u h*topHeight q u/topLeft q u
  epsilon := omega q u h*rawEpsilon q u h
  omega := omega q u h
  mu := fun i => omega q u h*rawMass q u h i

theorem massSum_formula (q u h : ℝ) :
    rawMassSum q u h=rawMass q u h 0+rawMass q u h 1+rawMass q u h 2+
      rawMass q u h 3+rawMass q u h 4 := by
  simp [rawMassSum,Fin.sum_univ_succ]
  ring

/-- The single normalization estimate, before using stationarity. -/
theorem raw_mass_bounds {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    (∀i,(1/40:ℝ)<rawMass q u h i) ∧
      5/4<rawMassSum q u h ∧ rawMassSum q u h<3/2 := by
  have hr := radical_bounds hq hu
  have ht := trig_bounds hh
  have hf := force_bounds hq hu hh
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  let two := Interval.point 2
  let one := Interval.point 1
  let L := Interval.of_bounds hl
  let R := Interval.of_bounds hr.r
  let U := Interval.of_bounds hr.U
  let V := Interval.of_bounds hr.V
  let W := Interval.of_bounds hr.w
  let C := Interval.of_bounds ht.c
  let S := Interval.of_bounds ht.s
  let A := Interval.of_bounds hf.a
  let K1 := Interval.of_bounds hf.k1
  let K2 := Interval.of_bounds hf.k2
  let B : Interval (rawBeta q u h) := (A.mul U).div L (by norm_num [L,Interval.of_bounds])
  let E : Interval (rawEpsilon q u h) := K2.div K1 (by norm_num [K1,Interval.of_bounds])
  let mA : Interval (rawMass q u h 0) := C.div (two.mul R)
    (by norm_num [two,R,Interval.point,Interval.of_bounds,Interval.mul])
  let mB : Interval (rawMass q u h 1) := A.div (two.mul L)
    (by norm_num [two,L,Interval.point,Interval.of_bounds,Interval.mul])
  let mD : Interval (rawMass q u h 2) := B.div (two.mul V)
    (by norm_num [two,V,Interval.point,Interval.of_bounds,Interval.mul])
  let mE : Interval (rawMass q u h 3) := (S.mul E).div (two.mul W)
    (by norm_num [two,W,Interval.point,Interval.of_bounds,Interval.mul])
  let mH : Interval (rawMass q u h 4) := one.div (two.mul K1)
    (by norm_num [two,K1,Interval.point,Interval.of_bounds,Interval.mul])
  have hA := mA.mem
  have hB := mB.mem
  have hD := mD.mem
  have hE := mE.mem
  have hH := mH.mem
  have hsum := ((((mA.add mB).add mD).add mE).add mH).mem
  norm_num [mA,mB,mD,mE,mH,B,E,L,R,U,V,W,C,S,A,K1,K2,two,one,
    Interval.of_bounds,Interval.point,Interval.add,Interval.mul,Interval.div,Interval.inv]
    at hA hB hD hE hH hsum
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact lt_of_lt_of_le (by norm_num) hA.1
    · exact lt_of_lt_of_le (by norm_num) hB.1
    · exact lt_of_lt_of_le (by norm_num) hD.1
    · exact lt_of_lt_of_le (by norm_num) hE.1
    · exact lt_of_lt_of_le (by norm_num) hH.1
  · rw [massSum_formula]
    linarith [hsum.1]
  · rw [massSum_formula]
    linarith [hsum.2]

theorem omega_bounds {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    2/3<omega q u h ∧ omega q u h<4/5 := by
  obtain ⟨_,hmL,hmU⟩ := raw_mass_bounds hq hu hh
  have hm : 0<rawMassSum q u h := by linarith
  dsimp [omega]
  constructor
  · apply (lt_div_iff₀ hm).2
    linarith
  · apply (div_lt_iff₀ hm).2
    linarith

theorem positive {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) : (weights q u h).Positive := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  have hm := (raw_mass_bounds hq hu hh).1
  have ho : 0<omega q u h := by linarith [(omega_bounds hq hu hh).1]
  have ha : 0<rawAlpha q u h := by dsimp [rawAlpha]; linarith [hf.a_lower]
  have hl : 0<2-u := by linarith [hu.2]
  have hU : 0<topRight q u := by linarith [hr.U_lower]
  have hV : 0<topLeft q u := by linarith [hr.V_lower]
  have hY : 0<topHeight q u := by linarith [hr.Y_lower]
  have hb : 0<rawBeta q u h := div_pos (mul_pos ha hU) hl
  have he : 0<rawEpsilon q u h := div_pos (by linarith [hf.k2_lower]) (by linarith [hf.k1_lower])
  refine ⟨(mul_pos ho ha).le,(mul_pos ho hb).le,?_,(mul_pos ho he).le,ho.le,?_⟩
  · exact (div_pos (mul_pos (mul_pos ho hb) hY) hV).le
  · intro i
    exact mul_pos ho (by linarith [hm i])

theorem mass_one {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) : massSum (weights q u h)=1 := by
  have hm : rawMassSum q u h≠0 := ne_of_gt (by linarith [(raw_mass_bounds hq hu hh).2.1])
  dsimp [massSum,weights]
  rw [← Finset.mul_sum]
  change (1/rawMassSum q u h)*rawMassSum q u h=1
  field_simp [hm]

theorem mass_lower {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) (i : Fin 5) :
    1/60<(weights q u h).mu i := by
  have hm := (raw_mass_bounds hq hu hh).1 i
  have ho := (omega_bounds hq hu hh).1
  have hp := mul_lt_mul_of_pos_left hm (by linarith : 0<omega q u h)
  dsimp [weights]
  nlinarith

/-- Exact cancellation at a position stationary point.  No tilt
stationarity or zero-defect equation is required. -/
theorem rawBeta_cancellation {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    rawBeta q u h=rawEpsilon q u h*(topLeft q u/topHeight q u)*
      cosine h*(1+h*lowerHeight q u/lowerLeft q u) := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  have hL : 2-u≠0 := ne_of_gt (by linarith [hu.2])
  have hU : topRight q u≠0 := ne_of_gt (by linarith [hr.U_lower])
  have hY : topHeight q u≠0 := ne_of_gt (by linarith [hr.Y_lower])
  have hK : firstComponent q (cosine h) (sine h) u≠0 := ne_of_gt (by linarith [hf.k1_lower])
  have ha : rawAlpha q u h=
      secondComponent q (cosine h) (sine h) u*slopeRatio q u*
        positionB q (cosine h) (sine h) u/firstComponent q (cosine h) (sine h) u := by
    apply (eq_div_iff hK).2
    dsimp [rawAlpha,positionA,positionB,positionHalf] at hz ⊢
    nlinarith
  rw [rawBeta,ha]
  dsimp [rawEpsilon,slopeRatio,positionB]
  rw [sine_eq]
  field_simp [hL,hU,hY,hK,ne_of_gt (by linarith [hr.w_lower] : 0<lowerLeft q u)]

end SquaresInCircles.Eight.StationaryTerminal
