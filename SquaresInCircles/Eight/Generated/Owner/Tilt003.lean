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

def tilt_003_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(53110117/100000000), 0, (84730841/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := .zero
    polynomial := [(-212004570327801066486235747211/16644073476607500000000000000), (-53110117/585382), (-202367692270542384498033678173/1188862391186250000000000000), (-53110117/585382), (-2621143121459792316486235747211/16644073476607500000000000000)]
    bernstein := [(55742669430770950327033087386109/166440734766075000000000000000000), (239265986446635616924131438882433/665762939064300000000000000000000), (417465787402543115719687771249909/1141307895538800000000000000000000), (3775893791952843010047524828593277/10652207025028800000000000000000000), (13881312306015725096091028244824549/42608828100115200000000000000000000)]
    reserve := (162892444183/500000000000) }

theorem tilt_003_000_valid : tilt_003_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_000]
  · intro i; fin_cases i <;> norm_num [tilt_003_000]
  · norm_num [tilt_003_000]
  · norm_num [tilt_003_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_000]

def tilt_003_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26512693/50000000), 0, (5298997/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-212015295595643208460352965961/16644073476607500000000000000), (-474197946/5226625), (-1416585788286274222210352965961/8322036738303750000000000000), (-474197946/5226625), (-2621156280976905235960352965961/16644073476607500000000000000)]
    bernstein := [(55617777757902103705046411417359/166440734766075000000000000000000), (238769879759545904754221065538683/665762939064300000000000000000000), (2916347269830054998067112998218113/7989155268771600000000000000000000), (3768060913633167576596692236624527/10652207025028800000000000000000000), (13850178939708757450752210945105799/42608828100115200000000000000000000)]
    reserve := (325054209591/1000000000000) }

theorem tilt_003_001_valid : tilt_003_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_001]
  · intro i; fin_cases i <;> norm_num [tilt_003_001]
  · norm_num [tilt_003_001]
  · norm_num [tilt_003_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_001]

def tilt_003_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662339/3125000), 0, (84677731/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-211994276956669982701659153461/16644073476607500000000000000), (-53110170269/585382000), (-1416564758757522797701659153461/8322036738303750000000000000), (-53110170269/585382000), (-2621135240558375612701659153461/16644073476607500000000000000)]
    bernstein := [(55867551046486736229087597729859/166440734766075000000000000000000), (239762093102264317960417934101183/665762939064300000000000000000000), (2928173943653004476571965014905613/7989155268771600000000000000000000), (3783726795800109522696885454937027/10652207025028800000000000000000000), (13912444166944111660455151253918299/42608828100115200000000000000000000)]
    reserve := (32651553181/100000000000) }

theorem tilt_003_002_valid : tilt_003_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_002]
  · intro i; fin_cases i <;> norm_num [tilt_003_002]
  · norm_num [tilt_003_002]
  · norm_num [tilt_003_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_002]

def tilt_003_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26512693/50000000), 0, (5298997/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-212015295595643208460352965961/16644073476607500000000000000), (-474197946/5226625), (-1416585788286274222210352965961/8322036738303750000000000000), (-474197946/5226625), (-2621156280976905235960352965961/16644073476607500000000000000)]
    bernstein := [(55617777757902103705046411417359/166440734766075000000000000000000), (238769879759545904754221065538683/665762939064300000000000000000000), (2916347269830054998067112998218113/7989155268771600000000000000000000), (3768060913633167576596692236624527/10652207025028800000000000000000000), (13850178939708757450752210945105799/42608828100115200000000000000000000)]
    reserve := (325054209591/1000000000000) }

theorem tilt_003_003_valid : tilt_003_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_003]
  · intro i; fin_cases i <;> norm_num [tilt_003_003]
  · norm_num [tilt_003_003]
  · norm_num [tilt_003_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_003]

def tilt_003_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662339/3125000), 0, (84677731/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-211994276956669982701659153461/16644073476607500000000000000), (-53110170269/585382000), (-1416564758757522797701659153461/8322036738303750000000000000), (-53110170269/585382000), (-2621135240558375612701659153461/16644073476607500000000000000)]
    bernstein := [(55867551046486736229087597729859/166440734766075000000000000000000), (239762093102264317960417934101183/665762939064300000000000000000000), (2928173943653004476571965014905613/7989155268771600000000000000000000), (3783726795800109522696885454937027/10652207025028800000000000000000000), (13912444166944111660455151253918299/42608828100115200000000000000000000)]
    reserve := (32651553181/100000000000) }

theorem tilt_003_004_valid : tilt_003_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_004]
  · intro i; fin_cases i <;> norm_num [tilt_003_004]
  · norm_num [tilt_003_004]
  · norm_num [tilt_003_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_004]

def tilt_003_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26512693/50000000), 0, (5298997/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-212015295595643208460352965961/16644073476607500000000000000), (-474197946/5226625), (-1416585788286274222210352965961/8322036738303750000000000000), (-474197946/5226625), (-2621156280976905235960352965961/16644073476607500000000000000)]
    bernstein := [(55617777757902103705046411417359/166440734766075000000000000000000), (238769879759545904754221065538683/665762939064300000000000000000000), (2916347269830054998067112998218113/7989155268771600000000000000000000), (3768060913633167576596692236624527/10652207025028800000000000000000000), (13850178939708757450752210945105799/42608828100115200000000000000000000)]
    reserve := (325054209591/1000000000000) }

theorem tilt_003_005_valid : tilt_003_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_005]
  · intro i; fin_cases i <;> norm_num [tilt_003_005]
  · norm_num [tilt_003_005]
  · norm_num [tilt_003_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_005]

def tilt_003_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662339/3125000), 0, (84677731/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-211994276956669982701659153461/16644073476607500000000000000), (-53110170269/585382000), (-1416564758757522797701659153461/8322036738303750000000000000), (-53110170269/585382000), (-2621135240558375612701659153461/16644073476607500000000000000)]
    bernstein := [(55867551046486736229087597729859/166440734766075000000000000000000), (239762093102264317960417934101183/665762939064300000000000000000000), (2928173943653004476571965014905613/7989155268771600000000000000000000), (3783726795800109522696885454937027/10652207025028800000000000000000000), (13912444166944111660455151253918299/42608828100115200000000000000000000)]
    reserve := (32651553181/100000000000) }

theorem tilt_003_006_valid : tilt_003_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_006]
  · intro i; fin_cases i <;> norm_num [tilt_003_006]
  · norm_num [tilt_003_006]
  · norm_num [tilt_003_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_006]

def tilt_003_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26512693/50000000), 0, (5298997/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-212015295595643208460352965961/16644073476607500000000000000), (-474197946/5226625), (-1416585788286274222210352965961/8322036738303750000000000000), (-474197946/5226625), (-2621156280976905235960352965961/16644073476607500000000000000)]
    bernstein := [(55617777757902103705046411417359/166440734766075000000000000000000), (238769879759545904754221065538683/665762939064300000000000000000000), (2916347269830054998067112998218113/7989155268771600000000000000000000), (3768060913633167576596692236624527/10652207025028800000000000000000000), (13850178939708757450752210945105799/42608828100115200000000000000000000)]
    reserve := (325054209591/1000000000000) }

theorem tilt_003_007_valid : tilt_003_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_007]
  · intro i; fin_cases i <;> norm_num [tilt_003_007]
  · norm_num [tilt_003_007]
  · norm_num [tilt_003_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_007]

def tilt_003_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662339/3125000), 0, (84677731/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-211994276956669982701659153461/16644073476607500000000000000), (-53110170269/585382000), (-1416564758757522797701659153461/8322036738303750000000000000), (-53110170269/585382000), (-2621135240558375612701659153461/16644073476607500000000000000)]
    bernstein := [(55867551046486736229087597729859/166440734766075000000000000000000), (239762093102264317960417934101183/665762939064300000000000000000000), (2928173943653004476571965014905613/7989155268771600000000000000000000), (3783726795800109522696885454937027/10652207025028800000000000000000000), (13912444166944111660455151253918299/42608828100115200000000000000000000)]
    reserve := (32651553181/100000000000) }

theorem tilt_003_008_valid : tilt_003_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_008]
  · intro i; fin_cases i <;> norm_num [tilt_003_008]
  · norm_num [tilt_003_008]
  · norm_num [tilt_003_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_008]

def tilt_003_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26512693/50000000), 0, (5298997/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-212015295595643208460352965961/16644073476607500000000000000), (-474197946/5226625), (-1416585788286274222210352965961/8322036738303750000000000000), (-474197946/5226625), (-2621156280976905235960352965961/16644073476607500000000000000)]
    bernstein := [(55617777757902103705046411417359/166440734766075000000000000000000), (238769879759545904754221065538683/665762939064300000000000000000000), (2916347269830054998067112998218113/7989155268771600000000000000000000), (3768060913633167576596692236624527/10652207025028800000000000000000000), (13850178939708757450752210945105799/42608828100115200000000000000000000)]
    reserve := (325054209591/1000000000000) }

theorem tilt_003_009_valid : tilt_003_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_009]
  · intro i; fin_cases i <;> norm_num [tilt_003_009]
  · norm_num [tilt_003_009]
  · norm_num [tilt_003_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_009]

def tilt_003_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662339/3125000), 0, (84677731/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-211994276956669982701659153461/16644073476607500000000000000), (-53110170269/585382000), (-1416564758757522797701659153461/8322036738303750000000000000), (-53110170269/585382000), (-2621135240558375612701659153461/16644073476607500000000000000)]
    bernstein := [(55867551046486736229087597729859/166440734766075000000000000000000), (239762093102264317960417934101183/665762939064300000000000000000000), (2928173943653004476571965014905613/7989155268771600000000000000000000), (3783726795800109522696885454937027/10652207025028800000000000000000000), (13912444166944111660455151253918299/42608828100115200000000000000000000)]
    reserve := (32651553181/100000000000) }

theorem tilt_003_010_valid : tilt_003_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_010]
  · intro i; fin_cases i <;> norm_num [tilt_003_010]
  · norm_num [tilt_003_010]
  · norm_num [tilt_003_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_010]

def tilt_003_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26512693/50000000), 0, (5298997/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-212015295595643208460352965961/16644073476607500000000000000), (-474197946/5226625), (-1416585788286274222210352965961/8322036738303750000000000000), (-474197946/5226625), (-2621156280976905235960352965961/16644073476607500000000000000)]
    bernstein := [(55617777757902103705046411417359/166440734766075000000000000000000), (238769879759545904754221065538683/665762939064300000000000000000000), (2916347269830054998067112998218113/7989155268771600000000000000000000), (3768060913633167576596692236624527/10652207025028800000000000000000000), (13850178939708757450752210945105799/42608828100115200000000000000000000)]
    reserve := (325054209591/1000000000000) }

theorem tilt_003_011_valid : tilt_003_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_011]
  · intro i; fin_cases i <;> norm_num [tilt_003_011]
  · norm_num [tilt_003_011]
  · norm_num [tilt_003_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_011]

def tilt_003_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662339/3125000), 0, (84677731/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-211994276956669982701659153461/16644073476607500000000000000), (-53110170269/585382000), (-1416564758757522797701659153461/8322036738303750000000000000), (-53110170269/585382000), (-2621135240558375612701659153461/16644073476607500000000000000)]
    bernstein := [(55867551046486736229087597729859/166440734766075000000000000000000), (239762093102264317960417934101183/665762939064300000000000000000000), (2928173943653004476571965014905613/7989155268771600000000000000000000), (3783726795800109522696885454937027/10652207025028800000000000000000000), (13912444166944111660455151253918299/42608828100115200000000000000000000)]
    reserve := (32651553181/100000000000) }

theorem tilt_003_012_valid : tilt_003_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_012]
  · intro i; fin_cases i <;> norm_num [tilt_003_012]
  · norm_num [tilt_003_012]
  · norm_num [tilt_003_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_012]

def tilt_003_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26512693/50000000), 0, (5298997/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-212015295595643208460352965961/16644073476607500000000000000), (-474197946/5226625), (-1416585788286274222210352965961/8322036738303750000000000000), (-474197946/5226625), (-2621156280976905235960352965961/16644073476607500000000000000)]
    bernstein := [(55617777757902103705046411417359/166440734766075000000000000000000), (238769879759545904754221065538683/665762939064300000000000000000000), (2916347269830054998067112998218113/7989155268771600000000000000000000), (3768060913633167576596692236624527/10652207025028800000000000000000000), (13850178939708757450752210945105799/42608828100115200000000000000000000)]
    reserve := (325054209591/1000000000000) }

theorem tilt_003_013_valid : tilt_003_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_013]
  · intro i; fin_cases i <;> norm_num [tilt_003_013]
  · norm_num [tilt_003_013]
  · norm_num [tilt_003_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_013]

def tilt_003_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662339/3125000), 0, (84677731/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-211994276956669982701659153461/16644073476607500000000000000), (-53110170269/585382000), (-1416564758757522797701659153461/8322036738303750000000000000), (-53110170269/585382000), (-2621135240558375612701659153461/16644073476607500000000000000)]
    bernstein := [(55867551046486736229087597729859/166440734766075000000000000000000), (239762093102264317960417934101183/665762939064300000000000000000000), (2928173943653004476571965014905613/7989155268771600000000000000000000), (3783726795800109522696885454937027/10652207025028800000000000000000000), (13912444166944111660455151253918299/42608828100115200000000000000000000)]
    reserve := (32651553181/100000000000) }

theorem tilt_003_014_valid : tilt_003_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_014]
  · intro i; fin_cases i <;> norm_num [tilt_003_014]
  · norm_num [tilt_003_014]
  · norm_num [tilt_003_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_014]

def tilt_003_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26512693/50000000), 0, (5298997/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-212015295595643208460352965961/16644073476607500000000000000), (-474197946/5226625), (-1416585788286274222210352965961/8322036738303750000000000000), (-474197946/5226625), (-2621156280976905235960352965961/16644073476607500000000000000)]
    bernstein := [(55617777757902103705046411417359/166440734766075000000000000000000), (238769879759545904754221065538683/665762939064300000000000000000000), (2916347269830054998067112998218113/7989155268771600000000000000000000), (3768060913633167576596692236624527/10652207025028800000000000000000000), (13850178939708757450752210945105799/42608828100115200000000000000000000)]
    reserve := (325054209591/1000000000000) }

theorem tilt_003_015_valid : tilt_003_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_015]
  · intro i; fin_cases i <;> norm_num [tilt_003_015]
  · norm_num [tilt_003_015]
  · norm_num [tilt_003_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_015]

def tilt_003_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662339/3125000), 0, (84677731/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-211994276956669982701659153461/16644073476607500000000000000), (-53110170269/585382000), (-1416564758757522797701659153461/8322036738303750000000000000), (-53110170269/585382000), (-2621135240558375612701659153461/16644073476607500000000000000)]
    bernstein := [(55867551046486736229087597729859/166440734766075000000000000000000), (239762093102264317960417934101183/665762939064300000000000000000000), (2928173943653004476571965014905613/7989155268771600000000000000000000), (3783726795800109522696885454937027/10652207025028800000000000000000000), (13912444166944111660455151253918299/42608828100115200000000000000000000)]
    reserve := (32651553181/100000000000) }

theorem tilt_003_016_valid : tilt_003_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_016]
  · intro i; fin_cases i <;> norm_num [tilt_003_016]
  · norm_num [tilt_003_016]
  · norm_num [tilt_003_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_016]

def tilt_003_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26512693/50000000), 0, (5298997/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-212015295595643208460352965961/16644073476607500000000000000), (-474197946/5226625), (-1416585788286274222210352965961/8322036738303750000000000000), (-474197946/5226625), (-2621156280976905235960352965961/16644073476607500000000000000)]
    bernstein := [(55617777757902103705046411417359/166440734766075000000000000000000), (238769879759545904754221065538683/665762939064300000000000000000000), (2916347269830054998067112998218113/7989155268771600000000000000000000), (3768060913633167576596692236624527/10652207025028800000000000000000000), (13850178939708757450752210945105799/42608828100115200000000000000000000)]
    reserve := (325054209591/1000000000000) }

theorem tilt_003_017_valid : tilt_003_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_017]
  · intro i; fin_cases i <;> norm_num [tilt_003_017]
  · norm_num [tilt_003_017]
  · norm_num [tilt_003_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_017]

def tilt_003_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662339/3125000), 0, (84677731/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-211994276956669982701659153461/16644073476607500000000000000), (-53110170269/585382000), (-1416564758757522797701659153461/8322036738303750000000000000), (-53110170269/585382000), (-2621135240558375612701659153461/16644073476607500000000000000)]
    bernstein := [(55867551046486736229087597729859/166440734766075000000000000000000), (239762093102264317960417934101183/665762939064300000000000000000000), (2928173943653004476571965014905613/7989155268771600000000000000000000), (3783726795800109522696885454937027/10652207025028800000000000000000000), (13912444166944111660455151253918299/42608828100115200000000000000000000)]
    reserve := (32651553181/100000000000) }

theorem tilt_003_018_valid : tilt_003_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_018]
  · intro i; fin_cases i <;> norm_num [tilt_003_018]
  · norm_num [tilt_003_018]
  · norm_num [tilt_003_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_018]

def tilt_003_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(26512693/50000000), 0, (5298997/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-212015295595643208460352965961/16644073476607500000000000000), (-474197946/5226625), (-1416585788286274222210352965961/8322036738303750000000000000), (-474197946/5226625), (-2621156280976905235960352965961/16644073476607500000000000000)]
    bernstein := [(55617777757902103705046411417359/166440734766075000000000000000000), (238769879759545904754221065538683/665762939064300000000000000000000), (2916347269830054998067112998218113/7989155268771600000000000000000000), (3768060913633167576596692236624527/10652207025028800000000000000000000), (13850178939708757450752210945105799/42608828100115200000000000000000000)]
    reserve := (325054209591/1000000000000) }

theorem tilt_003_019_valid : tilt_003_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_019]
  · intro i; fin_cases i <;> norm_num [tilt_003_019]
  · norm_num [tilt_003_019]
  · norm_num [tilt_003_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_019]

def tilt_003_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1662339/3125000), 0, (84677731/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (292691/50000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-211994276956669982701659153461/16644073476607500000000000000), (-53110170269/585382000), (-1416564758757522797701659153461/8322036738303750000000000000), (-53110170269/585382000), (-2621135240558375612701659153461/16644073476607500000000000000)]
    bernstein := [(55867551046486736229087597729859/166440734766075000000000000000000), (239762093102264317960417934101183/665762939064300000000000000000000), (2928173943653004476571965014905613/7989155268771600000000000000000000), (3783726795800109522696885454937027/10652207025028800000000000000000000), (13912444166944111660455151253918299/42608828100115200000000000000000000)]
    reserve := (32651553181/100000000000) }

theorem tilt_003_020_valid : tilt_003_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_003_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_003_020]
  · intro i; fin_cases i <;> norm_num [tilt_003_020]
  · norm_num [tilt_003_020]
  · norm_num [tilt_003_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_003_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_003_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_003_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_003_020]

def tiltBundle003_row : Alternative → Row
  | .zero => tilt_003_000
  | (.spike 0 false false) => tilt_003_001
  | (.spike 0 false true) => tilt_003_002
  | (.spike 0 true false) => tilt_003_003
  | (.spike 0 true true) => tilt_003_004
  | (.spike 1 false false) => tilt_003_005
  | (.spike 1 false true) => tilt_003_006
  | (.spike 1 true false) => tilt_003_007
  | (.spike 1 true true) => tilt_003_008
  | (.spike 2 false false) => tilt_003_009
  | (.spike 2 false true) => tilt_003_010
  | (.spike 2 true false) => tilt_003_011
  | (.spike 2 true true) => tilt_003_012
  | (.spike 3 false false) => tilt_003_013
  | (.spike 3 false true) => tilt_003_014
  | (.spike 3 true false) => tilt_003_015
  | (.spike 3 true true) => tilt_003_016
  | (.spike 4 false false) => tilt_003_017
  | (.spike 4 false true) => tilt_003_018
  | (.spike 4 true false) => tilt_003_019
  | (.spike 4 true true) => tilt_003_020

def tiltBundle003 : TiltBundle where
  interval := ⟨(-3/10), (-11/40)⟩
  lambda := ![0, 0, 0, 0, 0, 0, 1]
  row := tiltBundle003_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_003_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_003_001_valid | exact tilt_003_002_valid | exact tilt_003_003_valid | exact tilt_003_004_valid | exact tilt_003_005_valid | exact tilt_003_006_valid | exact tilt_003_007_valid | exact tilt_003_008_valid | exact tilt_003_009_valid | exact tilt_003_010_valid | exact tilt_003_011_valid | exact tilt_003_012_valid | exact tilt_003_013_valid | exact tilt_003_014_valid | exact tilt_003_015_valid | exact tilt_003_016_valid | exact tilt_003_017_valid | exact tilt_003_018_valid | exact tilt_003_019_valid | exact tilt_003_020_valid
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
