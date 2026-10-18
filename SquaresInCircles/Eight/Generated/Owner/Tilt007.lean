module

public import SquaresInCircles.Eight.Candidate.Dual

/-! Generated F8 rational data and algebraic proof source. Uncompiled.
No replay status or external decision procedure is a theorem premise. -/

@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open scoped BigOperators
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

def tilt_007_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7245283/20000000), 0, (93207547/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := .zero
    polynomial := [(-15609749895934050417293326777/2898216374295000000000000000), (-36226415/611592), (-236456032158676862917293326777/1449108187147500000000000000), (-36226415/611592), (-152434104807139891805764442259/966072124765000000000000000)]
    bernstein := [(70225093076090479477427774687/452846308483593750000000000000), (1303728320386063608313657643093/7245540935737500000000000000000), (16307316102708240249440597406889/86946491228850000000000000000000), (165266145712096730128593957958489/927429239774400000000000000000000), (22121897867229510992560167346173/145479096435200000000000000000000)]
    reserve := (152062381533/1000000000000) }

theorem tilt_007_000_valid : tilt_007_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_000]
  · intro i; fin_cases i <;> norm_num [tilt_007_000]
  · norm_num [tilt_007_000]
  · norm_num [tilt_007_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_000]

def tilt_007_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4516651/12500000), 0, (46621887/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 0 false false)
    polynomial := [(-15612101441821926867703389277/2898216374295000000000000000), (-18113225887/305796000), (-236458605935651949367703389277/1449108187147500000000000000), (-18113225887/305796000), (-152435036809827323955901129759/966072124765000000000000000)]
    bernstein := [(69830456425636319983127212187/452846308483593750000000000000), (1297444654559546413385179455593/7245540935737500000000000000000), (16232260503393542721253708469389/86946491228850000000000000000000), (164469080929455850704709494020989/927429239774400000000000000000000), (21997392429273343331746591658673/145479096435200000000000000000000)]
    reserve := (151206551101/1000000000000) }

theorem tilt_007_001_valid : tilt_007_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_001]
  · intro i; fin_cases i <;> norm_num [tilt_007_001]
  · norm_num [tilt_007_001]
  · norm_num [tilt_007_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_001]

def tilt_007_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36319623/100000000), 0, (93171321/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 0 false true)
    polynomial := [(-5202477063520885381906442259/966072124765000000000000000), (-12075483893/203864000), (-78817978427987832569406442259/483036062382500000000000000), (-12075483893/203864000), (-152433479792454779756906442259/966072124765000000000000000)]
    bernstein := [(23539906487655399207811258229/150948769494531250000000000000), (436670717454308807758513881031/2415180311912500000000000000000), (5460791547175122508131226468963/28982163742950000000000000000000), (55354406741046175232815529986163/309143079924800000000000000000000), (22246396522301484968543841346173/145479096435200000000000000000000)]
    reserve := (7645908267/50000000000) }

theorem tilt_007_002_valid : tilt_007_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_002]
  · intro i; fin_cases i <;> norm_num [tilt_007_002]
  · norm_num [tilt_007_002]
  · norm_num [tilt_007_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_002]

def tilt_007_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4516651/12500000), 0, (46621887/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 0 true false)
    polynomial := [(-15612101441821926867703389277/2898216374295000000000000000), (-18113225887/305796000), (-236458605935651949367703389277/1449108187147500000000000000), (-18113225887/305796000), (-152435036809827323955901129759/966072124765000000000000000)]
    bernstein := [(69830456425636319983127212187/452846308483593750000000000000), (1297444654559546413385179455593/7245540935737500000000000000000), (16232260503393542721253708469389/86946491228850000000000000000000), (164469080929455850704709494020989/927429239774400000000000000000000), (21997392429273343331746591658673/145479096435200000000000000000000)]
    reserve := (151206551101/1000000000000) }

theorem tilt_007_003_valid : tilt_007_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_003]
  · intro i; fin_cases i <;> norm_num [tilt_007_003]
  · norm_num [tilt_007_003]
  · norm_num [tilt_007_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_003]

def tilt_007_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36319623/100000000), 0, (93171321/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 0 true true)
    polynomial := [(-5202477063520885381906442259/966072124765000000000000000), (-12075483893/203864000), (-78817978427987832569406442259/483036062382500000000000000), (-12075483893/203864000), (-152433479792454779756906442259/966072124765000000000000000)]
    bernstein := [(23539906487655399207811258229/150948769494531250000000000000), (436670717454308807758513881031/2415180311912500000000000000000), (5460791547175122508131226468963/28982163742950000000000000000000), (55354406741046175232815529986163/309143079924800000000000000000000), (22246396522301484968543841346173/145479096435200000000000000000000)]
    reserve := (7645908267/50000000000) }

theorem tilt_007_004_valid : tilt_007_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_004]
  · intro i; fin_cases i <;> norm_num [tilt_007_004]
  · norm_num [tilt_007_004]
  · norm_num [tilt_007_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_004]

def tilt_007_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4516651/12500000), 0, (46621887/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 1 false false)
    polynomial := [(-15612101441821926867703389277/2898216374295000000000000000), (-18113225887/305796000), (-236458605935651949367703389277/1449108187147500000000000000), (-18113225887/305796000), (-152435036809827323955901129759/966072124765000000000000000)]
    bernstein := [(69830456425636319983127212187/452846308483593750000000000000), (1297444654559546413385179455593/7245540935737500000000000000000), (16232260503393542721253708469389/86946491228850000000000000000000), (164469080929455850704709494020989/927429239774400000000000000000000), (21997392429273343331746591658673/145479096435200000000000000000000)]
    reserve := (151206551101/1000000000000) }

theorem tilt_007_005_valid : tilt_007_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_005]
  · intro i; fin_cases i <;> norm_num [tilt_007_005]
  · norm_num [tilt_007_005]
  · norm_num [tilt_007_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_005]

def tilt_007_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36319623/100000000), 0, (93171321/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 1 false true)
    polynomial := [(-5202477063520885381906442259/966072124765000000000000000), (-12075483893/203864000), (-78817978427987832569406442259/483036062382500000000000000), (-12075483893/203864000), (-152433479792454779756906442259/966072124765000000000000000)]
    bernstein := [(23539906487655399207811258229/150948769494531250000000000000), (436670717454308807758513881031/2415180311912500000000000000000), (5460791547175122508131226468963/28982163742950000000000000000000), (55354406741046175232815529986163/309143079924800000000000000000000), (22246396522301484968543841346173/145479096435200000000000000000000)]
    reserve := (7645908267/50000000000) }

theorem tilt_007_006_valid : tilt_007_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_006]
  · intro i; fin_cases i <;> norm_num [tilt_007_006]
  · norm_num [tilt_007_006]
  · norm_num [tilt_007_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_006]

def tilt_007_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4516651/12500000), 0, (46621887/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 1 true false)
    polynomial := [(-15612101441821926867703389277/2898216374295000000000000000), (-18113225887/305796000), (-236458605935651949367703389277/1449108187147500000000000000), (-18113225887/305796000), (-152435036809827323955901129759/966072124765000000000000000)]
    bernstein := [(69830456425636319983127212187/452846308483593750000000000000), (1297444654559546413385179455593/7245540935737500000000000000000), (16232260503393542721253708469389/86946491228850000000000000000000), (164469080929455850704709494020989/927429239774400000000000000000000), (21997392429273343331746591658673/145479096435200000000000000000000)]
    reserve := (151206551101/1000000000000) }

theorem tilt_007_007_valid : tilt_007_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_007]
  · intro i; fin_cases i <;> norm_num [tilt_007_007]
  · norm_num [tilt_007_007]
  · norm_num [tilt_007_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_007]

def tilt_007_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36319623/100000000), 0, (93171321/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 1 true true)
    polynomial := [(-5202477063520885381906442259/966072124765000000000000000), (-12075483893/203864000), (-78817978427987832569406442259/483036062382500000000000000), (-12075483893/203864000), (-152433479792454779756906442259/966072124765000000000000000)]
    bernstein := [(23539906487655399207811258229/150948769494531250000000000000), (436670717454308807758513881031/2415180311912500000000000000000), (5460791547175122508131226468963/28982163742950000000000000000000), (55354406741046175232815529986163/309143079924800000000000000000000), (22246396522301484968543841346173/145479096435200000000000000000000)]
    reserve := (7645908267/50000000000) }

theorem tilt_007_008_valid : tilt_007_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_008]
  · intro i; fin_cases i <;> norm_num [tilt_007_008]
  · norm_num [tilt_007_008]
  · norm_num [tilt_007_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_008]

def tilt_007_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4516651/12500000), 0, (46621887/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 2 false false)
    polynomial := [(-15612101441821926867703389277/2898216374295000000000000000), (-18113225887/305796000), (-236458605935651949367703389277/1449108187147500000000000000), (-18113225887/305796000), (-152435036809827323955901129759/966072124765000000000000000)]
    bernstein := [(69830456425636319983127212187/452846308483593750000000000000), (1297444654559546413385179455593/7245540935737500000000000000000), (16232260503393542721253708469389/86946491228850000000000000000000), (164469080929455850704709494020989/927429239774400000000000000000000), (21997392429273343331746591658673/145479096435200000000000000000000)]
    reserve := (151206551101/1000000000000) }

theorem tilt_007_009_valid : tilt_007_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_009]
  · intro i; fin_cases i <;> norm_num [tilt_007_009]
  · norm_num [tilt_007_009]
  · norm_num [tilt_007_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_009]

def tilt_007_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36319623/100000000), 0, (93171321/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 2 false true)
    polynomial := [(-5202477063520885381906442259/966072124765000000000000000), (-12075483893/203864000), (-78817978427987832569406442259/483036062382500000000000000), (-12075483893/203864000), (-152433479792454779756906442259/966072124765000000000000000)]
    bernstein := [(23539906487655399207811258229/150948769494531250000000000000), (436670717454308807758513881031/2415180311912500000000000000000), (5460791547175122508131226468963/28982163742950000000000000000000), (55354406741046175232815529986163/309143079924800000000000000000000), (22246396522301484968543841346173/145479096435200000000000000000000)]
    reserve := (7645908267/50000000000) }

theorem tilt_007_010_valid : tilt_007_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_010]
  · intro i; fin_cases i <;> norm_num [tilt_007_010]
  · norm_num [tilt_007_010]
  · norm_num [tilt_007_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_010]

def tilt_007_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4516651/12500000), 0, (46621887/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 2 true false)
    polynomial := [(-15612101441821926867703389277/2898216374295000000000000000), (-18113225887/305796000), (-236458605935651949367703389277/1449108187147500000000000000), (-18113225887/305796000), (-152435036809827323955901129759/966072124765000000000000000)]
    bernstein := [(69830456425636319983127212187/452846308483593750000000000000), (1297444654559546413385179455593/7245540935737500000000000000000), (16232260503393542721253708469389/86946491228850000000000000000000), (164469080929455850704709494020989/927429239774400000000000000000000), (21997392429273343331746591658673/145479096435200000000000000000000)]
    reserve := (151206551101/1000000000000) }

theorem tilt_007_011_valid : tilt_007_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_011]
  · intro i; fin_cases i <;> norm_num [tilt_007_011]
  · norm_num [tilt_007_011]
  · norm_num [tilt_007_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_011]

def tilt_007_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36319623/100000000), 0, (93171321/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 2 true true)
    polynomial := [(-5202477063520885381906442259/966072124765000000000000000), (-12075483893/203864000), (-78817978427987832569406442259/483036062382500000000000000), (-12075483893/203864000), (-152433479792454779756906442259/966072124765000000000000000)]
    bernstein := [(23539906487655399207811258229/150948769494531250000000000000), (436670717454308807758513881031/2415180311912500000000000000000), (5460791547175122508131226468963/28982163742950000000000000000000), (55354406741046175232815529986163/309143079924800000000000000000000), (22246396522301484968543841346173/145479096435200000000000000000000)]
    reserve := (7645908267/50000000000) }

theorem tilt_007_012_valid : tilt_007_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_012]
  · intro i; fin_cases i <;> norm_num [tilt_007_012]
  · norm_num [tilt_007_012]
  · norm_num [tilt_007_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_012]

def tilt_007_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4516651/12500000), 0, (46621887/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 3 false false)
    polynomial := [(-15612101441821926867703389277/2898216374295000000000000000), (-18113225887/305796000), (-236458605935651949367703389277/1449108187147500000000000000), (-18113225887/305796000), (-152435036809827323955901129759/966072124765000000000000000)]
    bernstein := [(69830456425636319983127212187/452846308483593750000000000000), (1297444654559546413385179455593/7245540935737500000000000000000), (16232260503393542721253708469389/86946491228850000000000000000000), (164469080929455850704709494020989/927429239774400000000000000000000), (21997392429273343331746591658673/145479096435200000000000000000000)]
    reserve := (151206551101/1000000000000) }

theorem tilt_007_013_valid : tilt_007_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_013]
  · intro i; fin_cases i <;> norm_num [tilt_007_013]
  · norm_num [tilt_007_013]
  · norm_num [tilt_007_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_013]

def tilt_007_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36319623/100000000), 0, (93171321/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 3 false true)
    polynomial := [(-5202477063520885381906442259/966072124765000000000000000), (-12075483893/203864000), (-78817978427987832569406442259/483036062382500000000000000), (-12075483893/203864000), (-152433479792454779756906442259/966072124765000000000000000)]
    bernstein := [(23539906487655399207811258229/150948769494531250000000000000), (436670717454308807758513881031/2415180311912500000000000000000), (5460791547175122508131226468963/28982163742950000000000000000000), (55354406741046175232815529986163/309143079924800000000000000000000), (22246396522301484968543841346173/145479096435200000000000000000000)]
    reserve := (7645908267/50000000000) }

theorem tilt_007_014_valid : tilt_007_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_014]
  · intro i; fin_cases i <;> norm_num [tilt_007_014]
  · norm_num [tilt_007_014]
  · norm_num [tilt_007_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_014]

def tilt_007_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4516651/12500000), 0, (46621887/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 3 true false)
    polynomial := [(-15612101441821926867703389277/2898216374295000000000000000), (-18113225887/305796000), (-236458605935651949367703389277/1449108187147500000000000000), (-18113225887/305796000), (-152435036809827323955901129759/966072124765000000000000000)]
    bernstein := [(69830456425636319983127212187/452846308483593750000000000000), (1297444654559546413385179455593/7245540935737500000000000000000), (16232260503393542721253708469389/86946491228850000000000000000000), (164469080929455850704709494020989/927429239774400000000000000000000), (21997392429273343331746591658673/145479096435200000000000000000000)]
    reserve := (151206551101/1000000000000) }

theorem tilt_007_015_valid : tilt_007_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_015]
  · intro i; fin_cases i <;> norm_num [tilt_007_015]
  · norm_num [tilt_007_015]
  · norm_num [tilt_007_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_015]

def tilt_007_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36319623/100000000), 0, (93171321/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 3 true true)
    polynomial := [(-5202477063520885381906442259/966072124765000000000000000), (-12075483893/203864000), (-78817978427987832569406442259/483036062382500000000000000), (-12075483893/203864000), (-152433479792454779756906442259/966072124765000000000000000)]
    bernstein := [(23539906487655399207811258229/150948769494531250000000000000), (436670717454308807758513881031/2415180311912500000000000000000), (5460791547175122508131226468963/28982163742950000000000000000000), (55354406741046175232815529986163/309143079924800000000000000000000), (22246396522301484968543841346173/145479096435200000000000000000000)]
    reserve := (7645908267/50000000000) }

theorem tilt_007_016_valid : tilt_007_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_016]
  · intro i; fin_cases i <;> norm_num [tilt_007_016]
  · norm_num [tilt_007_016]
  · norm_num [tilt_007_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_016]

def tilt_007_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4516651/12500000), 0, (46621887/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 4 false false)
    polynomial := [(-15612101441821926867703389277/2898216374295000000000000000), (-18113225887/305796000), (-236458605935651949367703389277/1449108187147500000000000000), (-18113225887/305796000), (-152435036809827323955901129759/966072124765000000000000000)]
    bernstein := [(69830456425636319983127212187/452846308483593750000000000000), (1297444654559546413385179455593/7245540935737500000000000000000), (16232260503393542721253708469389/86946491228850000000000000000000), (164469080929455850704709494020989/927429239774400000000000000000000), (21997392429273343331746591658673/145479096435200000000000000000000)]
    reserve := (151206551101/1000000000000) }

theorem tilt_007_017_valid : tilt_007_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_017]
  · intro i; fin_cases i <;> norm_num [tilt_007_017]
  · norm_num [tilt_007_017]
  · norm_num [tilt_007_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_017]

def tilt_007_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36319623/100000000), 0, (93171321/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 4 false true)
    polynomial := [(-5202477063520885381906442259/966072124765000000000000000), (-12075483893/203864000), (-78817978427987832569406442259/483036062382500000000000000), (-12075483893/203864000), (-152433479792454779756906442259/966072124765000000000000000)]
    bernstein := [(23539906487655399207811258229/150948769494531250000000000000), (436670717454308807758513881031/2415180311912500000000000000000), (5460791547175122508131226468963/28982163742950000000000000000000), (55354406741046175232815529986163/309143079924800000000000000000000), (22246396522301484968543841346173/145479096435200000000000000000000)]
    reserve := (7645908267/50000000000) }

theorem tilt_007_018_valid : tilt_007_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_018]
  · intro i; fin_cases i <;> norm_num [tilt_007_018]
  · norm_num [tilt_007_018]
  · norm_num [tilt_007_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_018]

def tilt_007_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4516651/12500000), 0, (46621887/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 4 true false)
    polynomial := [(-15612101441821926867703389277/2898216374295000000000000000), (-18113225887/305796000), (-236458605935651949367703389277/1449108187147500000000000000), (-18113225887/305796000), (-152435036809827323955901129759/966072124765000000000000000)]
    bernstein := [(69830456425636319983127212187/452846308483593750000000000000), (1297444654559546413385179455593/7245540935737500000000000000000), (16232260503393542721253708469389/86946491228850000000000000000000), (164469080929455850704709494020989/927429239774400000000000000000000), (21997392429273343331746591658673/145479096435200000000000000000000)]
    reserve := (151206551101/1000000000000) }

theorem tilt_007_019_valid : tilt_007_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_019]
  · intro i; fin_cases i <;> norm_num [tilt_007_019]
  · norm_num [tilt_007_019]
  · norm_num [tilt_007_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_019]

def tilt_007_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(36319623/100000000), 0, (93171321/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (76449/12500000)]
    alternative := (.spike 4 true true)
    polynomial := [(-5202477063520885381906442259/966072124765000000000000000), (-12075483893/203864000), (-78817978427987832569406442259/483036062382500000000000000), (-12075483893/203864000), (-152433479792454779756906442259/966072124765000000000000000)]
    bernstein := [(23539906487655399207811258229/150948769494531250000000000000), (436670717454308807758513881031/2415180311912500000000000000000), (5460791547175122508131226468963/28982163742950000000000000000000), (55354406741046175232815529986163/309143079924800000000000000000000), (22246396522301484968543841346173/145479096435200000000000000000000)]
    reserve := (7645908267/50000000000) }

theorem tilt_007_020_valid : tilt_007_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_007_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_007_020]
  · intro i; fin_cases i <;> norm_num [tilt_007_020]
  · norm_num [tilt_007_020]
  · norm_num [tilt_007_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_007_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_007_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_007_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_007_020]

def tiltBundle007_row : Alternative → Row
  | .zero => tilt_007_000
  | (.spike 0 false false) => tilt_007_001
  | (.spike 0 false true) => tilt_007_002
  | (.spike 0 true false) => tilt_007_003
  | (.spike 0 true true) => tilt_007_004
  | (.spike 1 false false) => tilt_007_005
  | (.spike 1 false true) => tilt_007_006
  | (.spike 1 true false) => tilt_007_007
  | (.spike 1 true true) => tilt_007_008
  | (.spike 2 false false) => tilt_007_009
  | (.spike 2 false true) => tilt_007_010
  | (.spike 2 true false) => tilt_007_011
  | (.spike 2 true true) => tilt_007_012
  | (.spike 3 false false) => tilt_007_013
  | (.spike 3 false true) => tilt_007_014
  | (.spike 3 true false) => tilt_007_015
  | (.spike 3 true true) => tilt_007_016
  | (.spike 4 false false) => tilt_007_017
  | (.spike 4 false true) => tilt_007_018
  | (.spike 4 true false) => tilt_007_019
  | (.spike 4 true true) => tilt_007_020

def tiltBundle007 : TiltBundle where
  interval := ⟨(-1/5), (-7/40)⟩
  lambda := ![0, 0, 0, 0, 0, 0, 1]
  row := tiltBundle007_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_007_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_007_001_valid | exact tilt_007_002_valid | exact tilt_007_003_valid | exact tilt_007_004_valid | exact tilt_007_005_valid | exact tilt_007_006_valid | exact tilt_007_007_valid | exact tilt_007_008_valid | exact tilt_007_009_valid | exact tilt_007_010_valid | exact tilt_007_011_valid | exact tilt_007_012_valid | exact tilt_007_013_valid | exact tilt_007_014_valid | exact tilt_007_015_valid | exact tilt_007_016_valid | exact tilt_007_017_valid | exact tilt_007_018_valid | exact tilt_007_019_valid | exact tilt_007_020_valid
  same_interval := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_lambda := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_mode := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_owners := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_alternative := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_sign := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl

end SquaresInCircles.Eight.Generated.Owner
