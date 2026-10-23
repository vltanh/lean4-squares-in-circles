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

def tilt_058_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_000_valid : tilt_058_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_000]
  · intro i; fin_cases i <;> norm_num [tilt_058_000]
  · norm_num [tilt_058_000]
  · norm_num [tilt_058_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_000]

def tilt_058_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_001_valid : tilt_058_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_001]
  · intro i; fin_cases i <;> norm_num [tilt_058_001]
  · norm_num [tilt_058_001]
  · norm_num [tilt_058_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_001]

def tilt_058_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_002_valid : tilt_058_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_002]
  · intro i; fin_cases i <;> norm_num [tilt_058_002]
  · norm_num [tilt_058_002]
  · norm_num [tilt_058_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_002]

def tilt_058_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_003_valid : tilt_058_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_003]
  · intro i; fin_cases i <;> norm_num [tilt_058_003]
  · norm_num [tilt_058_003]
  · norm_num [tilt_058_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_003]

def tilt_058_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_004_valid : tilt_058_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_004]
  · intro i; fin_cases i <;> norm_num [tilt_058_004]
  · norm_num [tilt_058_004]
  · norm_num [tilt_058_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_004]

def tilt_058_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_005_valid : tilt_058_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_005]
  · intro i; fin_cases i <;> norm_num [tilt_058_005]
  · norm_num [tilt_058_005]
  · norm_num [tilt_058_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_005]

def tilt_058_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_006_valid : tilt_058_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_006]
  · intro i; fin_cases i <;> norm_num [tilt_058_006]
  · norm_num [tilt_058_006]
  · norm_num [tilt_058_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_006]

def tilt_058_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_007_valid : tilt_058_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_007]
  · intro i; fin_cases i <;> norm_num [tilt_058_007]
  · norm_num [tilt_058_007]
  · norm_num [tilt_058_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_007]

def tilt_058_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_008_valid : tilt_058_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_008]
  · intro i; fin_cases i <;> norm_num [tilt_058_008]
  · norm_num [tilt_058_008]
  · norm_num [tilt_058_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_008]

def tilt_058_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_009_valid : tilt_058_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_009]
  · intro i; fin_cases i <;> norm_num [tilt_058_009]
  · norm_num [tilt_058_009]
  · norm_num [tilt_058_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_009]

def tilt_058_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_010_valid : tilt_058_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_010]
  · intro i; fin_cases i <;> norm_num [tilt_058_010]
  · norm_num [tilt_058_010]
  · norm_num [tilt_058_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_010]

def tilt_058_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_011_valid : tilt_058_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_011]
  · intro i; fin_cases i <;> norm_num [tilt_058_011]
  · norm_num [tilt_058_011]
  · norm_num [tilt_058_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_011]

def tilt_058_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_012_valid : tilt_058_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_012]
  · intro i; fin_cases i <;> norm_num [tilt_058_012]
  · norm_num [tilt_058_012]
  · norm_num [tilt_058_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_012]

def tilt_058_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_013_valid : tilt_058_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_013]
  · intro i; fin_cases i <;> norm_num [tilt_058_013]
  · norm_num [tilt_058_013]
  · norm_num [tilt_058_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_013]

def tilt_058_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_014_valid : tilt_058_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_014]
  · intro i; fin_cases i <;> norm_num [tilt_058_014]
  · norm_num [tilt_058_014]
  · norm_num [tilt_058_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_014]

def tilt_058_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_015_valid : tilt_058_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_015]
  · intro i; fin_cases i <;> norm_num [tilt_058_015]
  · norm_num [tilt_058_015]
  · norm_num [tilt_058_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_015]

def tilt_058_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_016_valid : tilt_058_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_016]
  · intro i; fin_cases i <;> norm_num [tilt_058_016]
  · norm_num [tilt_058_016]
  · norm_num [tilt_058_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_016]

def tilt_058_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_017_valid : tilt_058_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_017]
  · intro i; fin_cases i <;> norm_num [tilt_058_017]
  · norm_num [tilt_058_017]
  · norm_num [tilt_058_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_017]

def tilt_058_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_018_valid : tilt_058_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_018]
  · intro i; fin_cases i <;> norm_num [tilt_058_018]
  · norm_num [tilt_058_018]
  · norm_num [tilt_058_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_018]

def tilt_058_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_019_valid : tilt_058_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_019]
  · intro i; fin_cases i <;> norm_num [tilt_058_019]
  · norm_num [tilt_058_019]
  · norm_num [tilt_058_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_019]

def tilt_058_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 1, 0, 0, 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1/20), 0, 1, 0, 0], ![0, 0, (4206443/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (20504619/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-7670593914258062497307/8201847600000000000000), (84128860/20504619), (-15872441514258062497307/4100923800000000000000), (84128860/20504619), (-24074289114258062497307/8201847600000000000000)]
    bernstein := [(208038954036460342480411493/1312295616000000000000000000), (91082912701361518906357417/524918246400000000000000000), (118627449631146714577219207/629901895680000000000000000), (5681890905236073407694203/27995639808000000000000000), (7303682372518784951850997/33594767769600000000000000)]
    reserve := (158530556301/1000000000000) }

theorem tilt_058_020_valid : tilt_058_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_058_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_058_020]
  · intro i; fin_cases i <;> norm_num [tilt_058_020]
  · norm_num [tilt_058_020]
  · norm_num [tilt_058_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_058_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_058_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_058_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_058_020]

def tiltBundle058_row : Alternative → Row
  | .zero => tilt_058_000
  | (.spike 0 false false) => tilt_058_001
  | (.spike 0 false true) => tilt_058_002
  | (.spike 0 true false) => tilt_058_003
  | (.spike 0 true true) => tilt_058_004
  | (.spike 1 false false) => tilt_058_005
  | (.spike 1 false true) => tilt_058_006
  | (.spike 1 true false) => tilt_058_007
  | (.spike 1 true true) => tilt_058_008
  | (.spike 2 false false) => tilt_058_009
  | (.spike 2 false true) => tilt_058_010
  | (.spike 2 true false) => tilt_058_011
  | (.spike 2 true true) => tilt_058_012
  | (.spike 3 false false) => tilt_058_013
  | (.spike 3 false true) => tilt_058_014
  | (.spike 3 true false) => tilt_058_015
  | (.spike 3 true true) => tilt_058_016
  | (.spike 4 false false) => tilt_058_017
  | (.spike 4 false true) => tilt_058_018
  | (.spike 4 true false) => tilt_058_019
  | (.spike 4 true true) => tilt_058_020

def tiltBundle058 : TiltBundle where
  interval := ⟨(7/20), (3/8)⟩
  lambda := ![0, 1, 0, 0, 0, 0, 0]
  row := tiltBundle058_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_058_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_058_001_valid | exact tilt_058_002_valid | exact tilt_058_003_valid | exact tilt_058_004_valid | exact tilt_058_005_valid | exact tilt_058_006_valid | exact tilt_058_007_valid | exact tilt_058_008_valid | exact tilt_058_009_valid | exact tilt_058_010_valid | exact tilt_058_011_valid | exact tilt_058_012_valid | exact tilt_058_013_valid | exact tilt_058_014_valid | exact tilt_058_015_valid | exact tilt_058_016_valid | exact tilt_058_017_valid | exact tilt_058_018_valid | exact tilt_058_019_valid | exact tilt_058_020_valid
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
