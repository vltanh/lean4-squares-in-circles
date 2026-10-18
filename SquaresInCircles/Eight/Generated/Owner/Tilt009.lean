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

def tilt_009_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13494863/50000000), 0, (96288913/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := .zero
    polynomial := [(-45572467037466689752554998423/15694549265450000000000000000), (-26989726/620985), (-3787073904397815069257664995269/23541823898175000000000000000), (-26989726/620985), (-7437430407683230069257664995269/47083647796350000000000000000)]
    bernstein := [(158051375683125061502847308802137/2511127882472000000000000000000000), (264914866867243312799247760401577/3013353458966400000000000000000000), (346943080296515308571173582169513/3616024150759680000000000000000000), (2804040203988994414335958341663/32142436895641600000000000000000), (477725583109958295454615799539/7714184854953984000000000000000)]
    reserve := (30964100037/500000000000) }

theorem tilt_009_000_valid : tilt_009_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_000]
  · intro i; fin_cases i <;> norm_num [tilt_009_000]
  · norm_num [tilt_009_000]
  · norm_num [tilt_009_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_000]

def tilt_009_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26893437/100000000), 0, (48157951/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-136759188107810264107390620269/47083647796350000000000000000), (-13494876451/310492500), (-3787119314230036429107390620269/23541823898175000000000000000), (-13494876451/310492500), (-2479159813450754198035796873423/15694549265450000000000000000)]
    bernstein := [(467187340420883505921589650781411/7533383647416000000000000000000000), (87379481461840984407529839508859/1004451152988800000000000000000000), (343622951752507189376497580294513/3616024150759680000000000000000000), (8323872236885733130439275649989/96427310686924800000000000000000), (156895722867976787950328391513/2571394951651328000000000000000)]
    reserve := (61015801079/1000000000000) }

theorem tilt_009_001_valid : tilt_009_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_001]
  · intro i; fin_cases i <;> norm_num [tilt_009_001]
  · norm_num [tilt_009_001]
  · norm_num [tilt_009_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_001]

def tilt_009_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13543007/50000000), 0, (96261923/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-45558629133476050328914998423/15694549265450000000000000000), (-26989752077/620985000), (-1262345343540089840328914998423/7847274632725000000000000000), (-26989752077/620985000), (-2479132057946703630328914998423/15694549265450000000000000000)]
    bernstein := [(160373435049198075548770148802137/2511127882472000000000000000000000), (267691219280508634616671400401577/3013353458966400000000000000000000), (38918134519116996715969860241057/401780461195520000000000000000000), (8500368109853827105087355024989/96427310686924800000000000000000), (484763598157092815240095799539/7714184854953984000000000000000)]
    reserve := (31420273643/500000000000) }

theorem tilt_009_002_valid : tilt_009_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_002]
  · intro i; fin_cases i <;> norm_num [tilt_009_002]
  · norm_num [tilt_009_002]
  · norm_num [tilt_009_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_002]

def tilt_009_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26893437/100000000), 0, (48157951/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-136759188107810264107390620269/47083647796350000000000000000), (-13494876451/310492500), (-3787119314230036429107390620269/23541823898175000000000000000), (-13494876451/310492500), (-2479159813450754198035796873423/15694549265450000000000000000)]
    bernstein := [(467187340420883505921589650781411/7533383647416000000000000000000000), (87379481461840984407529839508859/1004451152988800000000000000000000), (343622951752507189376497580294513/3616024150759680000000000000000000), (8323872236885733130439275649989/96427310686924800000000000000000), (156895722867976787950328391513/2571394951651328000000000000000)]
    reserve := (61015801079/1000000000000) }

theorem tilt_009_003_valid : tilt_009_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_003]
  · intro i; fin_cases i <;> norm_num [tilt_009_003]
  · norm_num [tilt_009_003]
  · norm_num [tilt_009_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_003]

def tilt_009_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13543007/50000000), 0, (96261923/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-45558629133476050328914998423/15694549265450000000000000000), (-26989752077/620985000), (-1262345343540089840328914998423/7847274632725000000000000000), (-26989752077/620985000), (-2479132057946703630328914998423/15694549265450000000000000000)]
    bernstein := [(160373435049198075548770148802137/2511127882472000000000000000000000), (267691219280508634616671400401577/3013353458966400000000000000000000), (38918134519116996715969860241057/401780461195520000000000000000000), (8500368109853827105087355024989/96427310686924800000000000000000), (484763598157092815240095799539/7714184854953984000000000000000)]
    reserve := (31420273643/500000000000) }

theorem tilt_009_004_valid : tilt_009_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_004]
  · intro i; fin_cases i <;> norm_num [tilt_009_004]
  · norm_num [tilt_009_004]
  · norm_num [tilt_009_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_004]

def tilt_009_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26893437/100000000), 0, (48157951/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-136759188107810264107390620269/47083647796350000000000000000), (-13494876451/310492500), (-3787119314230036429107390620269/23541823898175000000000000000), (-13494876451/310492500), (-2479159813450754198035796873423/15694549265450000000000000000)]
    bernstein := [(467187340420883505921589650781411/7533383647416000000000000000000000), (87379481461840984407529839508859/1004451152988800000000000000000000), (343622951752507189376497580294513/3616024150759680000000000000000000), (8323872236885733130439275649989/96427310686924800000000000000000), (156895722867976787950328391513/2571394951651328000000000000000)]
    reserve := (61015801079/1000000000000) }

theorem tilt_009_005_valid : tilt_009_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_005]
  · intro i; fin_cases i <;> norm_num [tilt_009_005]
  · norm_num [tilt_009_005]
  · norm_num [tilt_009_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_005]

def tilt_009_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13543007/50000000), 0, (96261923/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-45558629133476050328914998423/15694549265450000000000000000), (-26989752077/620985000), (-1262345343540089840328914998423/7847274632725000000000000000), (-26989752077/620985000), (-2479132057946703630328914998423/15694549265450000000000000000)]
    bernstein := [(160373435049198075548770148802137/2511127882472000000000000000000000), (267691219280508634616671400401577/3013353458966400000000000000000000), (38918134519116996715969860241057/401780461195520000000000000000000), (8500368109853827105087355024989/96427310686924800000000000000000), (484763598157092815240095799539/7714184854953984000000000000000)]
    reserve := (31420273643/500000000000) }

theorem tilt_009_006_valid : tilt_009_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_006]
  · intro i; fin_cases i <;> norm_num [tilt_009_006]
  · norm_num [tilt_009_006]
  · norm_num [tilt_009_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_006]

def tilt_009_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26893437/100000000), 0, (48157951/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-136759188107810264107390620269/47083647796350000000000000000), (-13494876451/310492500), (-3787119314230036429107390620269/23541823898175000000000000000), (-13494876451/310492500), (-2479159813450754198035796873423/15694549265450000000000000000)]
    bernstein := [(467187340420883505921589650781411/7533383647416000000000000000000000), (87379481461840984407529839508859/1004451152988800000000000000000000), (343622951752507189376497580294513/3616024150759680000000000000000000), (8323872236885733130439275649989/96427310686924800000000000000000), (156895722867976787950328391513/2571394951651328000000000000000)]
    reserve := (61015801079/1000000000000) }

theorem tilt_009_007_valid : tilt_009_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_007]
  · intro i; fin_cases i <;> norm_num [tilt_009_007]
  · norm_num [tilt_009_007]
  · norm_num [tilt_009_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_007]

def tilt_009_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13543007/50000000), 0, (96261923/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-45558629133476050328914998423/15694549265450000000000000000), (-26989752077/620985000), (-1262345343540089840328914998423/7847274632725000000000000000), (-26989752077/620985000), (-2479132057946703630328914998423/15694549265450000000000000000)]
    bernstein := [(160373435049198075548770148802137/2511127882472000000000000000000000), (267691219280508634616671400401577/3013353458966400000000000000000000), (38918134519116996715969860241057/401780461195520000000000000000000), (8500368109853827105087355024989/96427310686924800000000000000000), (484763598157092815240095799539/7714184854953984000000000000000)]
    reserve := (31420273643/500000000000) }

theorem tilt_009_008_valid : tilt_009_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_008]
  · intro i; fin_cases i <;> norm_num [tilt_009_008]
  · norm_num [tilt_009_008]
  · norm_num [tilt_009_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_008]

def tilt_009_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26893437/100000000), 0, (48157951/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-136759188107810264107390620269/47083647796350000000000000000), (-13494876451/310492500), (-3787119314230036429107390620269/23541823898175000000000000000), (-13494876451/310492500), (-2479159813450754198035796873423/15694549265450000000000000000)]
    bernstein := [(467187340420883505921589650781411/7533383647416000000000000000000000), (87379481461840984407529839508859/1004451152988800000000000000000000), (343622951752507189376497580294513/3616024150759680000000000000000000), (8323872236885733130439275649989/96427310686924800000000000000000), (156895722867976787950328391513/2571394951651328000000000000000)]
    reserve := (61015801079/1000000000000) }

theorem tilt_009_009_valid : tilt_009_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_009]
  · intro i; fin_cases i <;> norm_num [tilt_009_009]
  · norm_num [tilt_009_009]
  · norm_num [tilt_009_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_009]

def tilt_009_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13543007/50000000), 0, (96261923/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-45558629133476050328914998423/15694549265450000000000000000), (-26989752077/620985000), (-1262345343540089840328914998423/7847274632725000000000000000), (-26989752077/620985000), (-2479132057946703630328914998423/15694549265450000000000000000)]
    bernstein := [(160373435049198075548770148802137/2511127882472000000000000000000000), (267691219280508634616671400401577/3013353458966400000000000000000000), (38918134519116996715969860241057/401780461195520000000000000000000), (8500368109853827105087355024989/96427310686924800000000000000000), (484763598157092815240095799539/7714184854953984000000000000000)]
    reserve := (31420273643/500000000000) }

theorem tilt_009_010_valid : tilt_009_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_010]
  · intro i; fin_cases i <;> norm_num [tilt_009_010]
  · norm_num [tilt_009_010]
  · norm_num [tilt_009_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_010]

def tilt_009_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26893437/100000000), 0, (48157951/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-136759188107810264107390620269/47083647796350000000000000000), (-13494876451/310492500), (-3787119314230036429107390620269/23541823898175000000000000000), (-13494876451/310492500), (-2479159813450754198035796873423/15694549265450000000000000000)]
    bernstein := [(467187340420883505921589650781411/7533383647416000000000000000000000), (87379481461840984407529839508859/1004451152988800000000000000000000), (343622951752507189376497580294513/3616024150759680000000000000000000), (8323872236885733130439275649989/96427310686924800000000000000000), (156895722867976787950328391513/2571394951651328000000000000000)]
    reserve := (61015801079/1000000000000) }

theorem tilt_009_011_valid : tilt_009_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_011]
  · intro i; fin_cases i <;> norm_num [tilt_009_011]
  · norm_num [tilt_009_011]
  · norm_num [tilt_009_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_011]

def tilt_009_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13543007/50000000), 0, (96261923/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-45558629133476050328914998423/15694549265450000000000000000), (-26989752077/620985000), (-1262345343540089840328914998423/7847274632725000000000000000), (-26989752077/620985000), (-2479132057946703630328914998423/15694549265450000000000000000)]
    bernstein := [(160373435049198075548770148802137/2511127882472000000000000000000000), (267691219280508634616671400401577/3013353458966400000000000000000000), (38918134519116996715969860241057/401780461195520000000000000000000), (8500368109853827105087355024989/96427310686924800000000000000000), (484763598157092815240095799539/7714184854953984000000000000000)]
    reserve := (31420273643/500000000000) }

theorem tilt_009_012_valid : tilt_009_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_012]
  · intro i; fin_cases i <;> norm_num [tilt_009_012]
  · norm_num [tilt_009_012]
  · norm_num [tilt_009_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_012]

def tilt_009_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26893437/100000000), 0, (48157951/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-136759188107810264107390620269/47083647796350000000000000000), (-13494876451/310492500), (-3787119314230036429107390620269/23541823898175000000000000000), (-13494876451/310492500), (-2479159813450754198035796873423/15694549265450000000000000000)]
    bernstein := [(467187340420883505921589650781411/7533383647416000000000000000000000), (87379481461840984407529839508859/1004451152988800000000000000000000), (343622951752507189376497580294513/3616024150759680000000000000000000), (8323872236885733130439275649989/96427310686924800000000000000000), (156895722867976787950328391513/2571394951651328000000000000000)]
    reserve := (61015801079/1000000000000) }

theorem tilt_009_013_valid : tilt_009_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_013]
  · intro i; fin_cases i <;> norm_num [tilt_009_013]
  · norm_num [tilt_009_013]
  · norm_num [tilt_009_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_013]

def tilt_009_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13543007/50000000), 0, (96261923/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-45558629133476050328914998423/15694549265450000000000000000), (-26989752077/620985000), (-1262345343540089840328914998423/7847274632725000000000000000), (-26989752077/620985000), (-2479132057946703630328914998423/15694549265450000000000000000)]
    bernstein := [(160373435049198075548770148802137/2511127882472000000000000000000000), (267691219280508634616671400401577/3013353458966400000000000000000000), (38918134519116996715969860241057/401780461195520000000000000000000), (8500368109853827105087355024989/96427310686924800000000000000000), (484763598157092815240095799539/7714184854953984000000000000000)]
    reserve := (31420273643/500000000000) }

theorem tilt_009_014_valid : tilt_009_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_014]
  · intro i; fin_cases i <;> norm_num [tilt_009_014]
  · norm_num [tilt_009_014]
  · norm_num [tilt_009_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_014]

def tilt_009_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26893437/100000000), 0, (48157951/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-136759188107810264107390620269/47083647796350000000000000000), (-13494876451/310492500), (-3787119314230036429107390620269/23541823898175000000000000000), (-13494876451/310492500), (-2479159813450754198035796873423/15694549265450000000000000000)]
    bernstein := [(467187340420883505921589650781411/7533383647416000000000000000000000), (87379481461840984407529839508859/1004451152988800000000000000000000), (343622951752507189376497580294513/3616024150759680000000000000000000), (8323872236885733130439275649989/96427310686924800000000000000000), (156895722867976787950328391513/2571394951651328000000000000000)]
    reserve := (61015801079/1000000000000) }

theorem tilt_009_015_valid : tilt_009_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_015]
  · intro i; fin_cases i <;> norm_num [tilt_009_015]
  · norm_num [tilt_009_015]
  · norm_num [tilt_009_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_015]

def tilt_009_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13543007/50000000), 0, (96261923/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-45558629133476050328914998423/15694549265450000000000000000), (-26989752077/620985000), (-1262345343540089840328914998423/7847274632725000000000000000), (-26989752077/620985000), (-2479132057946703630328914998423/15694549265450000000000000000)]
    bernstein := [(160373435049198075548770148802137/2511127882472000000000000000000000), (267691219280508634616671400401577/3013353458966400000000000000000000), (38918134519116996715969860241057/401780461195520000000000000000000), (8500368109853827105087355024989/96427310686924800000000000000000), (484763598157092815240095799539/7714184854953984000000000000000)]
    reserve := (31420273643/500000000000) }

theorem tilt_009_016_valid : tilt_009_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_016]
  · intro i; fin_cases i <;> norm_num [tilt_009_016]
  · norm_num [tilt_009_016]
  · norm_num [tilt_009_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_016]

def tilt_009_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26893437/100000000), 0, (48157951/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-136759188107810264107390620269/47083647796350000000000000000), (-13494876451/310492500), (-3787119314230036429107390620269/23541823898175000000000000000), (-13494876451/310492500), (-2479159813450754198035796873423/15694549265450000000000000000)]
    bernstein := [(467187340420883505921589650781411/7533383647416000000000000000000000), (87379481461840984407529839508859/1004451152988800000000000000000000), (343622951752507189376497580294513/3616024150759680000000000000000000), (8323872236885733130439275649989/96427310686924800000000000000000), (156895722867976787950328391513/2571394951651328000000000000000)]
    reserve := (61015801079/1000000000000) }

theorem tilt_009_017_valid : tilt_009_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_017]
  · intro i; fin_cases i <;> norm_num [tilt_009_017]
  · norm_num [tilt_009_017]
  · norm_num [tilt_009_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_017]

def tilt_009_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13543007/50000000), 0, (96261923/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-45558629133476050328914998423/15694549265450000000000000000), (-26989752077/620985000), (-1262345343540089840328914998423/7847274632725000000000000000), (-26989752077/620985000), (-2479132057946703630328914998423/15694549265450000000000000000)]
    bernstein := [(160373435049198075548770148802137/2511127882472000000000000000000000), (267691219280508634616671400401577/3013353458966400000000000000000000), (38918134519116996715969860241057/401780461195520000000000000000000), (8500368109853827105087355024989/96427310686924800000000000000000), (484763598157092815240095799539/7714184854953984000000000000000)]
    reserve := (31420273643/500000000000) }

theorem tilt_009_018_valid : tilt_009_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_018]
  · intro i; fin_cases i <;> norm_num [tilt_009_018]
  · norm_num [tilt_009_018]
  · norm_num [tilt_009_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_018]

def tilt_009_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26893437/100000000), 0, (48157951/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-136759188107810264107390620269/47083647796350000000000000000), (-13494876451/310492500), (-3787119314230036429107390620269/23541823898175000000000000000), (-13494876451/310492500), (-2479159813450754198035796873423/15694549265450000000000000000)]
    bernstein := [(467187340420883505921589650781411/7533383647416000000000000000000000), (87379481461840984407529839508859/1004451152988800000000000000000000), (343622951752507189376497580294513/3616024150759680000000000000000000), (8323872236885733130439275649989/96427310686924800000000000000000), (156895722867976787950328391513/2571394951651328000000000000000)]
    reserve := (61015801079/1000000000000) }

theorem tilt_009_019_valid : tilt_009_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_019]
  · intro i; fin_cases i <;> norm_num [tilt_009_019]
  · norm_num [tilt_009_019]
  · norm_num [tilt_009_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_019]

def tilt_009_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(13543007/50000000), 0, (96261923/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (124197/20000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-45558629133476050328914998423/15694549265450000000000000000), (-26989752077/620985000), (-1262345343540089840328914998423/7847274632725000000000000000), (-26989752077/620985000), (-2479132057946703630328914998423/15694549265450000000000000000)]
    bernstein := [(160373435049198075548770148802137/2511127882472000000000000000000000), (267691219280508634616671400401577/3013353458966400000000000000000000), (38918134519116996715969860241057/401780461195520000000000000000000), (8500368109853827105087355024989/96427310686924800000000000000000), (484763598157092815240095799539/7714184854953984000000000000000)]
    reserve := (31420273643/500000000000) }

theorem tilt_009_020_valid : tilt_009_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_009_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_009_020]
  · intro i; fin_cases i <;> norm_num [tilt_009_020]
  · norm_num [tilt_009_020]
  · norm_num [tilt_009_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_009_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_009_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_009_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_009_020]

def tiltBundle009_row : Alternative → Row
  | .zero => tilt_009_000
  | (.spike 0 false false) => tilt_009_001
  | (.spike 0 false true) => tilt_009_002
  | (.spike 0 true false) => tilt_009_003
  | (.spike 0 true true) => tilt_009_004
  | (.spike 1 false false) => tilt_009_005
  | (.spike 1 false true) => tilt_009_006
  | (.spike 1 true false) => tilt_009_007
  | (.spike 1 true true) => tilt_009_008
  | (.spike 2 false false) => tilt_009_009
  | (.spike 2 false true) => tilt_009_010
  | (.spike 2 true false) => tilt_009_011
  | (.spike 2 true true) => tilt_009_012
  | (.spike 3 false false) => tilt_009_013
  | (.spike 3 false true) => tilt_009_014
  | (.spike 3 true false) => tilt_009_015
  | (.spike 3 true true) => tilt_009_016
  | (.spike 4 false false) => tilt_009_017
  | (.spike 4 false true) => tilt_009_018
  | (.spike 4 true false) => tilt_009_019
  | (.spike 4 true true) => tilt_009_020

def tiltBundle009 : TiltBundle where
  interval := ⟨(-3/20), (-1/8)⟩
  lambda := ![0, 0, 0, 0, 0, 0, 1]
  row := tiltBundle009_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_009_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_009_001_valid | exact tilt_009_002_valid | exact tilt_009_003_valid | exact tilt_009_004_valid | exact tilt_009_005_valid | exact tilt_009_006_valid | exact tilt_009_007_valid | exact tilt_009_008_valid | exact tilt_009_009_valid | exact tilt_009_010_valid | exact tilt_009_011_valid | exact tilt_009_012_valid | exact tilt_009_013_valid | exact tilt_009_014_valid | exact tilt_009_015_valid | exact tilt_009_016_valid | exact tilt_009_017_valid | exact tilt_009_018_valid | exact tilt_009_019_valid | exact tilt_009_020_valid
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
