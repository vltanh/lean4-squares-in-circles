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

def tilt_005_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(44963763/100000000), 0, (44660553/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := .zero
    polynomial := [(-656501497452440959532788647599/75772763722150000000000000000), (-14987921/199873), (-6300174446724490959532788647599/37886381861075000000000000000), (-14987921/199873), (-11943847395996540959532788647599/75772763722150000000000000000)]
    bernstein := [(4761442098552262695024080843889/19397827512870400000000000000000), (52403267652440573262298215448073/193978275128704000000000000000000), (1613221030522017408999545689413299/5819348253861120000000000000000000), (5178933966390120797289605892247689/19397827512870400000000000000000000), (46499858328045019649667618372002161/193978275128704000000000000000000000)]
    reserve := (239716835801/1000000000000) }

theorem tilt_005_000_valid : tilt_005_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_000]
  · intro i; fin_cases i <;> norm_num [tilt_005_000]
  · norm_num [tilt_005_000]
  · norm_num [tilt_005_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_000]

def tilt_005_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22437221/50000000), 0, (8936607/10000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (29981/5000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-147725272861124692146116859053/17048900270325000000000000000), (-4496380807/59962000), (-1417552959641534275896116859053/8524450135162500000000000000), (-4496380807/59962000), (-2687380646421943859646116859053/17048900270325000000000000000)]
    bernstein := [(1067774338386002472272227733683/4364518469203200000000000000000), (11755443864400718134206263940731/43645184692032000000000000000000), (361922033955810639702431296016953/1309355540760960000000000000000000), (1161770450453465594006807628492283/4364518469203200000000000000000000), (10427755920072921690029178245535667/43645184692032000000000000000000000)]
    reserve := (29865138599/125000000000) }

theorem tilt_005_001_valid : tilt_005_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_001]
  · intro i; fin_cases i <;> norm_num [tilt_005_001]
  · norm_num [tilt_005_001]
  · norm_num [tilt_005_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_001]

def tilt_005_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11263271/25000000), 0, (89276143/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-656447541613405594926950522599/75772763722150000000000000000), (-44963807857/599619000), (-6300126182761169294926950522599/37886381861075000000000000000), (-44963807857/599619000), (-11943804823908932994926950522599/75772763722150000000000000000)]
    bernstein := [(14331681810288007598333896906667/58193482538611200000000000000000), (157680590612768463474613445719219/581934825386112000000000000000000), (539300722039497300218422387929433/1939782751287040000000000000000000), (15583355040340037925242658956118067/58193482538611200000000000000000000), (46654204958742809244225364310127161/193978275128704000000000000000000000)]
    reserve := (120256263047/500000000000) }

theorem tilt_005_002_valid : tilt_005_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_002]
  · intro i; fin_cases i <;> norm_num [tilt_005_002]
  · norm_num [tilt_005_002]
  · norm_num [tilt_005_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_002]

def tilt_005_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22437221/50000000), 0, (8936607/10000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (29981/5000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-147725272861124692146116859053/17048900270325000000000000000), (-4496380807/59962000), (-1417552959641534275896116859053/8524450135162500000000000000), (-4496380807/59962000), (-2687380646421943859646116859053/17048900270325000000000000000)]
    bernstein := [(1067774338386002472272227733683/4364518469203200000000000000000), (11755443864400718134206263940731/43645184692032000000000000000000), (361922033955810639702431296016953/1309355540760960000000000000000000), (1161770450453465594006807628492283/4364518469203200000000000000000000), (10427755920072921690029178245535667/43645184692032000000000000000000000)]
    reserve := (29865138599/125000000000) }

theorem tilt_005_003_valid : tilt_005_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_003]
  · intro i; fin_cases i <;> norm_num [tilt_005_003]
  · norm_num [tilt_005_003]
  · norm_num [tilt_005_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_003]

def tilt_005_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11263271/25000000), 0, (89276143/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-656447541613405594926950522599/75772763722150000000000000000), (-44963807857/599619000), (-6300126182761169294926950522599/37886381861075000000000000000), (-44963807857/599619000), (-11943804823908932994926950522599/75772763722150000000000000000)]
    bernstein := [(14331681810288007598333896906667/58193482538611200000000000000000), (157680590612768463474613445719219/581934825386112000000000000000000), (539300722039497300218422387929433/1939782751287040000000000000000000), (15583355040340037925242658956118067/58193482538611200000000000000000000), (46654204958742809244225364310127161/193978275128704000000000000000000000)]
    reserve := (120256263047/500000000000) }

theorem tilt_005_004_valid : tilt_005_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_004]
  · intro i; fin_cases i <;> norm_num [tilt_005_004]
  · norm_num [tilt_005_004]
  · norm_num [tilt_005_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_004]

def tilt_005_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22437221/50000000), 0, (8936607/10000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (29981/5000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-147725272861124692146116859053/17048900270325000000000000000), (-4496380807/59962000), (-1417552959641534275896116859053/8524450135162500000000000000), (-4496380807/59962000), (-2687380646421943859646116859053/17048900270325000000000000000)]
    bernstein := [(1067774338386002472272227733683/4364518469203200000000000000000), (11755443864400718134206263940731/43645184692032000000000000000000), (361922033955810639702431296016953/1309355540760960000000000000000000), (1161770450453465594006807628492283/4364518469203200000000000000000000), (10427755920072921690029178245535667/43645184692032000000000000000000000)]
    reserve := (29865138599/125000000000) }

theorem tilt_005_005_valid : tilt_005_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_005]
  · intro i; fin_cases i <;> norm_num [tilt_005_005]
  · norm_num [tilt_005_005]
  · norm_num [tilt_005_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_005]

def tilt_005_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11263271/25000000), 0, (89276143/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-656447541613405594926950522599/75772763722150000000000000000), (-44963807857/599619000), (-6300126182761169294926950522599/37886381861075000000000000000), (-44963807857/599619000), (-11943804823908932994926950522599/75772763722150000000000000000)]
    bernstein := [(14331681810288007598333896906667/58193482538611200000000000000000), (157680590612768463474613445719219/581934825386112000000000000000000), (539300722039497300218422387929433/1939782751287040000000000000000000), (15583355040340037925242658956118067/58193482538611200000000000000000000), (46654204958742809244225364310127161/193978275128704000000000000000000000)]
    reserve := (120256263047/500000000000) }

theorem tilt_005_006_valid : tilt_005_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_006]
  · intro i; fin_cases i <;> norm_num [tilt_005_006]
  · norm_num [tilt_005_006]
  · norm_num [tilt_005_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_006]

def tilt_005_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22437221/50000000), 0, (8936607/10000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (29981/5000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-147725272861124692146116859053/17048900270325000000000000000), (-4496380807/59962000), (-1417552959641534275896116859053/8524450135162500000000000000), (-4496380807/59962000), (-2687380646421943859646116859053/17048900270325000000000000000)]
    bernstein := [(1067774338386002472272227733683/4364518469203200000000000000000), (11755443864400718134206263940731/43645184692032000000000000000000), (361922033955810639702431296016953/1309355540760960000000000000000000), (1161770450453465594006807628492283/4364518469203200000000000000000000), (10427755920072921690029178245535667/43645184692032000000000000000000000)]
    reserve := (29865138599/125000000000) }

theorem tilt_005_007_valid : tilt_005_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_007]
  · intro i; fin_cases i <;> norm_num [tilt_005_007]
  · norm_num [tilt_005_007]
  · norm_num [tilt_005_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_007]

def tilt_005_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11263271/25000000), 0, (89276143/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-656447541613405594926950522599/75772763722150000000000000000), (-44963807857/599619000), (-6300126182761169294926950522599/37886381861075000000000000000), (-44963807857/599619000), (-11943804823908932994926950522599/75772763722150000000000000000)]
    bernstein := [(14331681810288007598333896906667/58193482538611200000000000000000), (157680590612768463474613445719219/581934825386112000000000000000000), (539300722039497300218422387929433/1939782751287040000000000000000000), (15583355040340037925242658956118067/58193482538611200000000000000000000), (46654204958742809244225364310127161/193978275128704000000000000000000000)]
    reserve := (120256263047/500000000000) }

theorem tilt_005_008_valid : tilt_005_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_008]
  · intro i; fin_cases i <;> norm_num [tilt_005_008]
  · norm_num [tilt_005_008]
  · norm_num [tilt_005_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_008]

def tilt_005_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22437221/50000000), 0, (8936607/10000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (29981/5000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-147725272861124692146116859053/17048900270325000000000000000), (-4496380807/59962000), (-1417552959641534275896116859053/8524450135162500000000000000), (-4496380807/59962000), (-2687380646421943859646116859053/17048900270325000000000000000)]
    bernstein := [(1067774338386002472272227733683/4364518469203200000000000000000), (11755443864400718134206263940731/43645184692032000000000000000000), (361922033955810639702431296016953/1309355540760960000000000000000000), (1161770450453465594006807628492283/4364518469203200000000000000000000), (10427755920072921690029178245535667/43645184692032000000000000000000000)]
    reserve := (29865138599/125000000000) }

theorem tilt_005_009_valid : tilt_005_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_009]
  · intro i; fin_cases i <;> norm_num [tilt_005_009]
  · norm_num [tilt_005_009]
  · norm_num [tilt_005_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_009]

def tilt_005_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11263271/25000000), 0, (89276143/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-656447541613405594926950522599/75772763722150000000000000000), (-44963807857/599619000), (-6300126182761169294926950522599/37886381861075000000000000000), (-44963807857/599619000), (-11943804823908932994926950522599/75772763722150000000000000000)]
    bernstein := [(14331681810288007598333896906667/58193482538611200000000000000000), (157680590612768463474613445719219/581934825386112000000000000000000), (539300722039497300218422387929433/1939782751287040000000000000000000), (15583355040340037925242658956118067/58193482538611200000000000000000000), (46654204958742809244225364310127161/193978275128704000000000000000000000)]
    reserve := (120256263047/500000000000) }

theorem tilt_005_010_valid : tilt_005_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_010]
  · intro i; fin_cases i <;> norm_num [tilt_005_010]
  · norm_num [tilt_005_010]
  · norm_num [tilt_005_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_010]

def tilt_005_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22437221/50000000), 0, (8936607/10000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (29981/5000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-147725272861124692146116859053/17048900270325000000000000000), (-4496380807/59962000), (-1417552959641534275896116859053/8524450135162500000000000000), (-4496380807/59962000), (-2687380646421943859646116859053/17048900270325000000000000000)]
    bernstein := [(1067774338386002472272227733683/4364518469203200000000000000000), (11755443864400718134206263940731/43645184692032000000000000000000), (361922033955810639702431296016953/1309355540760960000000000000000000), (1161770450453465594006807628492283/4364518469203200000000000000000000), (10427755920072921690029178245535667/43645184692032000000000000000000000)]
    reserve := (29865138599/125000000000) }

theorem tilt_005_011_valid : tilt_005_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_011]
  · intro i; fin_cases i <;> norm_num [tilt_005_011]
  · norm_num [tilt_005_011]
  · norm_num [tilt_005_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_011]

def tilt_005_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11263271/25000000), 0, (89276143/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-656447541613405594926950522599/75772763722150000000000000000), (-44963807857/599619000), (-6300126182761169294926950522599/37886381861075000000000000000), (-44963807857/599619000), (-11943804823908932994926950522599/75772763722150000000000000000)]
    bernstein := [(14331681810288007598333896906667/58193482538611200000000000000000), (157680590612768463474613445719219/581934825386112000000000000000000), (539300722039497300218422387929433/1939782751287040000000000000000000), (15583355040340037925242658956118067/58193482538611200000000000000000000), (46654204958742809244225364310127161/193978275128704000000000000000000000)]
    reserve := (120256263047/500000000000) }

theorem tilt_005_012_valid : tilt_005_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_012]
  · intro i; fin_cases i <;> norm_num [tilt_005_012]
  · norm_num [tilt_005_012]
  · norm_num [tilt_005_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_012]

def tilt_005_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22437221/50000000), 0, (8936607/10000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (29981/5000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-147725272861124692146116859053/17048900270325000000000000000), (-4496380807/59962000), (-1417552959641534275896116859053/8524450135162500000000000000), (-4496380807/59962000), (-2687380646421943859646116859053/17048900270325000000000000000)]
    bernstein := [(1067774338386002472272227733683/4364518469203200000000000000000), (11755443864400718134206263940731/43645184692032000000000000000000), (361922033955810639702431296016953/1309355540760960000000000000000000), (1161770450453465594006807628492283/4364518469203200000000000000000000), (10427755920072921690029178245535667/43645184692032000000000000000000000)]
    reserve := (29865138599/125000000000) }

theorem tilt_005_013_valid : tilt_005_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_013]
  · intro i; fin_cases i <;> norm_num [tilt_005_013]
  · norm_num [tilt_005_013]
  · norm_num [tilt_005_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_013]

def tilt_005_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11263271/25000000), 0, (89276143/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-656447541613405594926950522599/75772763722150000000000000000), (-44963807857/599619000), (-6300126182761169294926950522599/37886381861075000000000000000), (-44963807857/599619000), (-11943804823908932994926950522599/75772763722150000000000000000)]
    bernstein := [(14331681810288007598333896906667/58193482538611200000000000000000), (157680590612768463474613445719219/581934825386112000000000000000000), (539300722039497300218422387929433/1939782751287040000000000000000000), (15583355040340037925242658956118067/58193482538611200000000000000000000), (46654204958742809244225364310127161/193978275128704000000000000000000000)]
    reserve := (120256263047/500000000000) }

theorem tilt_005_014_valid : tilt_005_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_014]
  · intro i; fin_cases i <;> norm_num [tilt_005_014]
  · norm_num [tilt_005_014]
  · norm_num [tilt_005_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_014]

def tilt_005_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22437221/50000000), 0, (8936607/10000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (29981/5000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-147725272861124692146116859053/17048900270325000000000000000), (-4496380807/59962000), (-1417552959641534275896116859053/8524450135162500000000000000), (-4496380807/59962000), (-2687380646421943859646116859053/17048900270325000000000000000)]
    bernstein := [(1067774338386002472272227733683/4364518469203200000000000000000), (11755443864400718134206263940731/43645184692032000000000000000000), (361922033955810639702431296016953/1309355540760960000000000000000000), (1161770450453465594006807628492283/4364518469203200000000000000000000), (10427755920072921690029178245535667/43645184692032000000000000000000000)]
    reserve := (29865138599/125000000000) }

theorem tilt_005_015_valid : tilt_005_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_015]
  · intro i; fin_cases i <;> norm_num [tilt_005_015]
  · norm_num [tilt_005_015]
  · norm_num [tilt_005_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_015]

def tilt_005_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11263271/25000000), 0, (89276143/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-656447541613405594926950522599/75772763722150000000000000000), (-44963807857/599619000), (-6300126182761169294926950522599/37886381861075000000000000000), (-44963807857/599619000), (-11943804823908932994926950522599/75772763722150000000000000000)]
    bernstein := [(14331681810288007598333896906667/58193482538611200000000000000000), (157680590612768463474613445719219/581934825386112000000000000000000), (539300722039497300218422387929433/1939782751287040000000000000000000), (15583355040340037925242658956118067/58193482538611200000000000000000000), (46654204958742809244225364310127161/193978275128704000000000000000000000)]
    reserve := (120256263047/500000000000) }

theorem tilt_005_016_valid : tilt_005_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_016]
  · intro i; fin_cases i <;> norm_num [tilt_005_016]
  · norm_num [tilt_005_016]
  · norm_num [tilt_005_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_016]

def tilt_005_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22437221/50000000), 0, (8936607/10000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (29981/5000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-147725272861124692146116859053/17048900270325000000000000000), (-4496380807/59962000), (-1417552959641534275896116859053/8524450135162500000000000000), (-4496380807/59962000), (-2687380646421943859646116859053/17048900270325000000000000000)]
    bernstein := [(1067774338386002472272227733683/4364518469203200000000000000000), (11755443864400718134206263940731/43645184692032000000000000000000), (361922033955810639702431296016953/1309355540760960000000000000000000), (1161770450453465594006807628492283/4364518469203200000000000000000000), (10427755920072921690029178245535667/43645184692032000000000000000000000)]
    reserve := (29865138599/125000000000) }

theorem tilt_005_017_valid : tilt_005_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_017]
  · intro i; fin_cases i <;> norm_num [tilt_005_017]
  · norm_num [tilt_005_017]
  · norm_num [tilt_005_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_017]

def tilt_005_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11263271/25000000), 0, (89276143/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-656447541613405594926950522599/75772763722150000000000000000), (-44963807857/599619000), (-6300126182761169294926950522599/37886381861075000000000000000), (-44963807857/599619000), (-11943804823908932994926950522599/75772763722150000000000000000)]
    bernstein := [(14331681810288007598333896906667/58193482538611200000000000000000), (157680590612768463474613445719219/581934825386112000000000000000000), (539300722039497300218422387929433/1939782751287040000000000000000000), (15583355040340037925242658956118067/58193482538611200000000000000000000), (46654204958742809244225364310127161/193978275128704000000000000000000000)]
    reserve := (120256263047/500000000000) }

theorem tilt_005_018_valid : tilt_005_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_018]
  · intro i; fin_cases i <;> norm_num [tilt_005_018]
  · norm_num [tilt_005_018]
  · norm_num [tilt_005_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_018]

def tilt_005_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(22437221/50000000), 0, (8936607/10000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (29981/5000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-147725272861124692146116859053/17048900270325000000000000000), (-4496380807/59962000), (-1417552959641534275896116859053/8524450135162500000000000000), (-4496380807/59962000), (-2687380646421943859646116859053/17048900270325000000000000000)]
    bernstein := [(1067774338386002472272227733683/4364518469203200000000000000000), (11755443864400718134206263940731/43645184692032000000000000000000), (361922033955810639702431296016953/1309355540760960000000000000000000), (1161770450453465594006807628492283/4364518469203200000000000000000000), (10427755920072921690029178245535667/43645184692032000000000000000000000)]
    reserve := (29865138599/125000000000) }

theorem tilt_005_019_valid : tilt_005_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_019]
  · intro i; fin_cases i <;> norm_num [tilt_005_019]
  · norm_num [tilt_005_019]
  · norm_num [tilt_005_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_019]

def tilt_005_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11263271/25000000), 0, (89276143/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (599619/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-656447541613405594926950522599/75772763722150000000000000000), (-44963807857/599619000), (-6300126182761169294926950522599/37886381861075000000000000000), (-44963807857/599619000), (-11943804823908932994926950522599/75772763722150000000000000000)]
    bernstein := [(14331681810288007598333896906667/58193482538611200000000000000000), (157680590612768463474613445719219/581934825386112000000000000000000), (539300722039497300218422387929433/1939782751287040000000000000000000), (15583355040340037925242658956118067/58193482538611200000000000000000000), (46654204958742809244225364310127161/193978275128704000000000000000000000)]
    reserve := (120256263047/500000000000) }

theorem tilt_005_020_valid : tilt_005_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_005_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_005_020]
  · intro i; fin_cases i <;> norm_num [tilt_005_020]
  · norm_num [tilt_005_020]
  · norm_num [tilt_005_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_005_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_005_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_005_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_005_020]

def tiltBundle005_row : Alternative → Row
  | .zero => tilt_005_000
  | (.spike 0 false false) => tilt_005_001
  | (.spike 0 false true) => tilt_005_002
  | (.spike 0 true false) => tilt_005_003
  | (.spike 0 true true) => tilt_005_004
  | (.spike 1 false false) => tilt_005_005
  | (.spike 1 false true) => tilt_005_006
  | (.spike 1 true false) => tilt_005_007
  | (.spike 1 true true) => tilt_005_008
  | (.spike 2 false false) => tilt_005_009
  | (.spike 2 false true) => tilt_005_010
  | (.spike 2 true false) => tilt_005_011
  | (.spike 2 true true) => tilt_005_012
  | (.spike 3 false false) => tilt_005_013
  | (.spike 3 false true) => tilt_005_014
  | (.spike 3 true false) => tilt_005_015
  | (.spike 3 true true) => tilt_005_016
  | (.spike 4 false false) => tilt_005_017
  | (.spike 4 false true) => tilt_005_018
  | (.spike 4 true false) => tilt_005_019
  | (.spike 4 true true) => tilt_005_020

def tiltBundle005 : TiltBundle where
  interval := ⟨(-1/4), (-9/40)⟩
  lambda := ![0, 0, 0, 0, 0, 0, 1]
  row := tiltBundle005_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_005_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_005_001_valid | exact tilt_005_002_valid | exact tilt_005_003_valid | exact tilt_005_004_valid | exact tilt_005_005_valid | exact tilt_005_006_valid | exact tilt_005_007_valid | exact tilt_005_008_valid | exact tilt_005_009_valid | exact tilt_005_010_valid | exact tilt_005_011_valid | exact tilt_005_012_valid | exact tilt_005_013_valid | exact tilt_005_014_valid | exact tilt_005_015_valid | exact tilt_005_016_valid | exact tilt_005_017_valid | exact tilt_005_018_valid | exact tilt_005_019_valid | exact tilt_005_020_valid
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
