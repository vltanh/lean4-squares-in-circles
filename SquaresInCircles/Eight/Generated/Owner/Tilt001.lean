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

def tilt_001_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60597559/100000000), 0, (19887081/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (142307/25000000)]
    alternative := .zero
    polynomial := [(-129521549643744726346788970057/7356713345025000000000000000), (-5508869/51748), (-643563565097282226346788970057/3678356672512500000000000000), (-5508869/51748), (-1157605580550819726346788970057/7356713345025000000000000000)]
    bernstein := [(2669185225874859485352924318389/6294514092000000000000000000000), (351786153909562126226650475988879/784716090136000000000000000000000), (6411520885132417031215761398513549/14124889622448000000000000000000000), (1385342915516547296731502654842599/3138864360544000000000000000000000), (7740173865257632589686121873456423/18833186163264000000000000000000000)]
    reserve := (205492947347/500000000000) }

theorem tilt_001_000_valid : tilt_001_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_000]
  · intro i; fin_cases i <;> norm_num [tilt_001_000]
  · norm_num [tilt_001_000]
  · norm_num [tilt_001_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_000]

def tilt_001_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60518011/100000000), 0, (79608921/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1266472987283000795082395557579/71932434630650000000000000000), (-60597619921/569229000), (-18877999721030752360247186672737/107898651945975000000000000000), (-60597619921/569229000), (-33956580480212502335247186672737/215797303891950000000000000000)]
    bernstein := [(4872645597787506234943973196516021/11509189540904000000000000000000000), (2810061861448415628645067899228047/6277739749584000000000000000000000), (187794401992393665251285716513538309/414330823472544000000000000000000000), (11066087683336545088515868850188007/25110958998336000000000000000000000), (226681330150028435282528666617068943/552441097963392000000000000000000000)]
    reserve := (82065339087/200000000000) }

theorem tilt_001_001_valid : tilt_001_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_001]
  · intro i; fin_cases i <;> norm_num [tilt_001_001]
  · norm_num [tilt_001_001]
  · norm_num [tilt_001_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_001]

def tilt_001_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15169277/25000000), 0, (39743863/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-1266395422684679899061603682579/71932434630650000000000000000), (-10099603379/94871500), (-18877767049792510397184811047737/107898651945975000000000000000), (-10099603379/94871500), (-33956347831530981097184811047737/215797303891950000000000000000)]
    bernstein := [(14664855514750706828444907965173063/34527568622712000000000000000000000), (2818526024975975050985607004853047/6277739749584000000000000000000000), (188348774217327752215601137415413309/414330823472544000000000000000000000), (11099435229347994632985609780813007/25110958998336000000000000000000000), (227409622651701887688642514842693943/552441097963392000000000000000000000)]
    reserve := (205822506227/500000000000) }

theorem tilt_001_002_valid : tilt_001_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_002]
  · intro i; fin_cases i <;> norm_num [tilt_001_002]
  · norm_num [tilt_001_002]
  · norm_num [tilt_001_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_002]

def tilt_001_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60518011/100000000), 0, (79608921/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-1266472987283000795082395557579/71932434630650000000000000000), (-60597619921/569229000), (-18877999721030752360247186672737/107898651945975000000000000000), (-60597619921/569229000), (-33956580480212502335247186672737/215797303891950000000000000000)]
    bernstein := [(4872645597787506234943973196516021/11509189540904000000000000000000000), (2810061861448415628645067899228047/6277739749584000000000000000000000), (187794401992393665251285716513538309/414330823472544000000000000000000000), (11066087683336545088515868850188007/25110958998336000000000000000000000), (226681330150028435282528666617068943/552441097963392000000000000000000000)]
    reserve := (82065339087/200000000000) }

theorem tilt_001_003_valid : tilt_001_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_003]
  · intro i; fin_cases i <;> norm_num [tilt_001_003]
  · norm_num [tilt_001_003]
  · norm_num [tilt_001_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_003]

def tilt_001_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15169277/25000000), 0, (39743863/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-1266395422684679899061603682579/71932434630650000000000000000), (-10099603379/94871500), (-18877767049792510397184811047737/107898651945975000000000000000), (-10099603379/94871500), (-33956347831530981097184811047737/215797303891950000000000000000)]
    bernstein := [(14664855514750706828444907965173063/34527568622712000000000000000000000), (2818526024975975050985607004853047/6277739749584000000000000000000000), (188348774217327752215601137415413309/414330823472544000000000000000000000), (11099435229347994632985609780813007/25110958998336000000000000000000000), (227409622651701887688642514842693943/552441097963392000000000000000000000)]
    reserve := (205822506227/500000000000) }

theorem tilt_001_004_valid : tilt_001_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_004]
  · intro i; fin_cases i <;> norm_num [tilt_001_004]
  · norm_num [tilt_001_004]
  · norm_num [tilt_001_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_004]

def tilt_001_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60518011/100000000), 0, (79608921/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-1266472987283000795082395557579/71932434630650000000000000000), (-60597619921/569229000), (-18877999721030752360247186672737/107898651945975000000000000000), (-60597619921/569229000), (-33956580480212502335247186672737/215797303891950000000000000000)]
    bernstein := [(4872645597787506234943973196516021/11509189540904000000000000000000000), (2810061861448415628645067899228047/6277739749584000000000000000000000), (187794401992393665251285716513538309/414330823472544000000000000000000000), (11066087683336545088515868850188007/25110958998336000000000000000000000), (226681330150028435282528666617068943/552441097963392000000000000000000000)]
    reserve := (82065339087/200000000000) }

theorem tilt_001_005_valid : tilt_001_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_005]
  · intro i; fin_cases i <;> norm_num [tilt_001_005]
  · norm_num [tilt_001_005]
  · norm_num [tilt_001_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_005]

def tilt_001_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15169277/25000000), 0, (39743863/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-1266395422684679899061603682579/71932434630650000000000000000), (-10099603379/94871500), (-18877767049792510397184811047737/107898651945975000000000000000), (-10099603379/94871500), (-33956347831530981097184811047737/215797303891950000000000000000)]
    bernstein := [(14664855514750706828444907965173063/34527568622712000000000000000000000), (2818526024975975050985607004853047/6277739749584000000000000000000000), (188348774217327752215601137415413309/414330823472544000000000000000000000), (11099435229347994632985609780813007/25110958998336000000000000000000000), (227409622651701887688642514842693943/552441097963392000000000000000000000)]
    reserve := (205822506227/500000000000) }

theorem tilt_001_006_valid : tilt_001_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_006]
  · intro i; fin_cases i <;> norm_num [tilt_001_006]
  · norm_num [tilt_001_006]
  · norm_num [tilt_001_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_006]

def tilt_001_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60518011/100000000), 0, (79608921/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-1266472987283000795082395557579/71932434630650000000000000000), (-60597619921/569229000), (-18877999721030752360247186672737/107898651945975000000000000000), (-60597619921/569229000), (-33956580480212502335247186672737/215797303891950000000000000000)]
    bernstein := [(4872645597787506234943973196516021/11509189540904000000000000000000000), (2810061861448415628645067899228047/6277739749584000000000000000000000), (187794401992393665251285716513538309/414330823472544000000000000000000000), (11066087683336545088515868850188007/25110958998336000000000000000000000), (226681330150028435282528666617068943/552441097963392000000000000000000000)]
    reserve := (82065339087/200000000000) }

theorem tilt_001_007_valid : tilt_001_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_007]
  · intro i; fin_cases i <;> norm_num [tilt_001_007]
  · norm_num [tilt_001_007]
  · norm_num [tilt_001_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_007]

def tilt_001_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15169277/25000000), 0, (39743863/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-1266395422684679899061603682579/71932434630650000000000000000), (-10099603379/94871500), (-18877767049792510397184811047737/107898651945975000000000000000), (-10099603379/94871500), (-33956347831530981097184811047737/215797303891950000000000000000)]
    bernstein := [(14664855514750706828444907965173063/34527568622712000000000000000000000), (2818526024975975050985607004853047/6277739749584000000000000000000000), (188348774217327752215601137415413309/414330823472544000000000000000000000), (11099435229347994632985609780813007/25110958998336000000000000000000000), (227409622651701887688642514842693943/552441097963392000000000000000000000)]
    reserve := (205822506227/500000000000) }

theorem tilt_001_008_valid : tilt_001_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_008]
  · intro i; fin_cases i <;> norm_num [tilt_001_008]
  · norm_num [tilt_001_008]
  · norm_num [tilt_001_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_008]

def tilt_001_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60518011/100000000), 0, (79608921/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-1266472987283000795082395557579/71932434630650000000000000000), (-60597619921/569229000), (-18877999721030752360247186672737/107898651945975000000000000000), (-60597619921/569229000), (-33956580480212502335247186672737/215797303891950000000000000000)]
    bernstein := [(4872645597787506234943973196516021/11509189540904000000000000000000000), (2810061861448415628645067899228047/6277739749584000000000000000000000), (187794401992393665251285716513538309/414330823472544000000000000000000000), (11066087683336545088515868850188007/25110958998336000000000000000000000), (226681330150028435282528666617068943/552441097963392000000000000000000000)]
    reserve := (82065339087/200000000000) }

theorem tilt_001_009_valid : tilt_001_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_009]
  · intro i; fin_cases i <;> norm_num [tilt_001_009]
  · norm_num [tilt_001_009]
  · norm_num [tilt_001_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_009]

def tilt_001_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15169277/25000000), 0, (39743863/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-1266395422684679899061603682579/71932434630650000000000000000), (-10099603379/94871500), (-18877767049792510397184811047737/107898651945975000000000000000), (-10099603379/94871500), (-33956347831530981097184811047737/215797303891950000000000000000)]
    bernstein := [(14664855514750706828444907965173063/34527568622712000000000000000000000), (2818526024975975050985607004853047/6277739749584000000000000000000000), (188348774217327752215601137415413309/414330823472544000000000000000000000), (11099435229347994632985609780813007/25110958998336000000000000000000000), (227409622651701887688642514842693943/552441097963392000000000000000000000)]
    reserve := (205822506227/500000000000) }

theorem tilt_001_010_valid : tilt_001_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_010]
  · intro i; fin_cases i <;> norm_num [tilt_001_010]
  · norm_num [tilt_001_010]
  · norm_num [tilt_001_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_010]

def tilt_001_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60518011/100000000), 0, (79608921/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1266472987283000795082395557579/71932434630650000000000000000), (-60597619921/569229000), (-18877999721030752360247186672737/107898651945975000000000000000), (-60597619921/569229000), (-33956580480212502335247186672737/215797303891950000000000000000)]
    bernstein := [(4872645597787506234943973196516021/11509189540904000000000000000000000), (2810061861448415628645067899228047/6277739749584000000000000000000000), (187794401992393665251285716513538309/414330823472544000000000000000000000), (11066087683336545088515868850188007/25110958998336000000000000000000000), (226681330150028435282528666617068943/552441097963392000000000000000000000)]
    reserve := (82065339087/200000000000) }

theorem tilt_001_011_valid : tilt_001_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_011]
  · intro i; fin_cases i <;> norm_num [tilt_001_011]
  · norm_num [tilt_001_011]
  · norm_num [tilt_001_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_011]

def tilt_001_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15169277/25000000), 0, (39743863/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-1266395422684679899061603682579/71932434630650000000000000000), (-10099603379/94871500), (-18877767049792510397184811047737/107898651945975000000000000000), (-10099603379/94871500), (-33956347831530981097184811047737/215797303891950000000000000000)]
    bernstein := [(14664855514750706828444907965173063/34527568622712000000000000000000000), (2818526024975975050985607004853047/6277739749584000000000000000000000), (188348774217327752215601137415413309/414330823472544000000000000000000000), (11099435229347994632985609780813007/25110958998336000000000000000000000), (227409622651701887688642514842693943/552441097963392000000000000000000000)]
    reserve := (205822506227/500000000000) }

theorem tilt_001_012_valid : tilt_001_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_012]
  · intro i; fin_cases i <;> norm_num [tilt_001_012]
  · norm_num [tilt_001_012]
  · norm_num [tilt_001_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_012]

def tilt_001_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60518011/100000000), 0, (79608921/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-1266472987283000795082395557579/71932434630650000000000000000), (-60597619921/569229000), (-18877999721030752360247186672737/107898651945975000000000000000), (-60597619921/569229000), (-33956580480212502335247186672737/215797303891950000000000000000)]
    bernstein := [(4872645597787506234943973196516021/11509189540904000000000000000000000), (2810061861448415628645067899228047/6277739749584000000000000000000000), (187794401992393665251285716513538309/414330823472544000000000000000000000), (11066087683336545088515868850188007/25110958998336000000000000000000000), (226681330150028435282528666617068943/552441097963392000000000000000000000)]
    reserve := (82065339087/200000000000) }

theorem tilt_001_013_valid : tilt_001_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_013]
  · intro i; fin_cases i <;> norm_num [tilt_001_013]
  · norm_num [tilt_001_013]
  · norm_num [tilt_001_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_013]

def tilt_001_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15169277/25000000), 0, (39743863/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-1266395422684679899061603682579/71932434630650000000000000000), (-10099603379/94871500), (-18877767049792510397184811047737/107898651945975000000000000000), (-10099603379/94871500), (-33956347831530981097184811047737/215797303891950000000000000000)]
    bernstein := [(14664855514750706828444907965173063/34527568622712000000000000000000000), (2818526024975975050985607004853047/6277739749584000000000000000000000), (188348774217327752215601137415413309/414330823472544000000000000000000000), (11099435229347994632985609780813007/25110958998336000000000000000000000), (227409622651701887688642514842693943/552441097963392000000000000000000000)]
    reserve := (205822506227/500000000000) }

theorem tilt_001_014_valid : tilt_001_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_014]
  · intro i; fin_cases i <;> norm_num [tilt_001_014]
  · norm_num [tilt_001_014]
  · norm_num [tilt_001_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_014]

def tilt_001_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60518011/100000000), 0, (79608921/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1266472987283000795082395557579/71932434630650000000000000000), (-60597619921/569229000), (-18877999721030752360247186672737/107898651945975000000000000000), (-60597619921/569229000), (-33956580480212502335247186672737/215797303891950000000000000000)]
    bernstein := [(4872645597787506234943973196516021/11509189540904000000000000000000000), (2810061861448415628645067899228047/6277739749584000000000000000000000), (187794401992393665251285716513538309/414330823472544000000000000000000000), (11066087683336545088515868850188007/25110958998336000000000000000000000), (226681330150028435282528666617068943/552441097963392000000000000000000000)]
    reserve := (82065339087/200000000000) }

theorem tilt_001_015_valid : tilt_001_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_015]
  · intro i; fin_cases i <;> norm_num [tilt_001_015]
  · norm_num [tilt_001_015]
  · norm_num [tilt_001_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_015]

def tilt_001_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15169277/25000000), 0, (39743863/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-1266395422684679899061603682579/71932434630650000000000000000), (-10099603379/94871500), (-18877767049792510397184811047737/107898651945975000000000000000), (-10099603379/94871500), (-33956347831530981097184811047737/215797303891950000000000000000)]
    bernstein := [(14664855514750706828444907965173063/34527568622712000000000000000000000), (2818526024975975050985607004853047/6277739749584000000000000000000000), (188348774217327752215601137415413309/414330823472544000000000000000000000), (11099435229347994632985609780813007/25110958998336000000000000000000000), (227409622651701887688642514842693943/552441097963392000000000000000000000)]
    reserve := (205822506227/500000000000) }

theorem tilt_001_016_valid : tilt_001_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_016]
  · intro i; fin_cases i <;> norm_num [tilt_001_016]
  · norm_num [tilt_001_016]
  · norm_num [tilt_001_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_016]

def tilt_001_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60518011/100000000), 0, (79608921/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1266472987283000795082395557579/71932434630650000000000000000), (-60597619921/569229000), (-18877999721030752360247186672737/107898651945975000000000000000), (-60597619921/569229000), (-33956580480212502335247186672737/215797303891950000000000000000)]
    bernstein := [(4872645597787506234943973196516021/11509189540904000000000000000000000), (2810061861448415628645067899228047/6277739749584000000000000000000000), (187794401992393665251285716513538309/414330823472544000000000000000000000), (11066087683336545088515868850188007/25110958998336000000000000000000000), (226681330150028435282528666617068943/552441097963392000000000000000000000)]
    reserve := (82065339087/200000000000) }

theorem tilt_001_017_valid : tilt_001_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_017]
  · intro i; fin_cases i <;> norm_num [tilt_001_017]
  · norm_num [tilt_001_017]
  · norm_num [tilt_001_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_017]

def tilt_001_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15169277/25000000), 0, (39743863/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1266395422684679899061603682579/71932434630650000000000000000), (-10099603379/94871500), (-18877767049792510397184811047737/107898651945975000000000000000), (-10099603379/94871500), (-33956347831530981097184811047737/215797303891950000000000000000)]
    bernstein := [(14664855514750706828444907965173063/34527568622712000000000000000000000), (2818526024975975050985607004853047/6277739749584000000000000000000000), (188348774217327752215601137415413309/414330823472544000000000000000000000), (11099435229347994632985609780813007/25110958998336000000000000000000000), (227409622651701887688642514842693943/552441097963392000000000000000000000)]
    reserve := (205822506227/500000000000) }

theorem tilt_001_018_valid : tilt_001_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_018]
  · intro i; fin_cases i <;> norm_num [tilt_001_018]
  · norm_num [tilt_001_018]
  · norm_num [tilt_001_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_018]

def tilt_001_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(60518011/100000000), 0, (79608921/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-1266472987283000795082395557579/71932434630650000000000000000), (-60597619921/569229000), (-18877999721030752360247186672737/107898651945975000000000000000), (-60597619921/569229000), (-33956580480212502335247186672737/215797303891950000000000000000)]
    bernstein := [(4872645597787506234943973196516021/11509189540904000000000000000000000), (2810061861448415628645067899228047/6277739749584000000000000000000000), (187794401992393665251285716513538309/414330823472544000000000000000000000), (11066087683336545088515868850188007/25110958998336000000000000000000000), (226681330150028435282528666617068943/552441097963392000000000000000000000)]
    reserve := (82065339087/200000000000) }

theorem tilt_001_019_valid : tilt_001_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_019]
  · intro i; fin_cases i <;> norm_num [tilt_001_019]
  · norm_num [tilt_001_019]
  · norm_num [tilt_001_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_019]

def tilt_001_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15169277/25000000), 0, (39743863/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (569229/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-1266395422684679899061603682579/71932434630650000000000000000), (-10099603379/94871500), (-18877767049792510397184811047737/107898651945975000000000000000), (-10099603379/94871500), (-33956347831530981097184811047737/215797303891950000000000000000)]
    bernstein := [(14664855514750706828444907965173063/34527568622712000000000000000000000), (2818526024975975050985607004853047/6277739749584000000000000000000000), (188348774217327752215601137415413309/414330823472544000000000000000000000), (11099435229347994632985609780813007/25110958998336000000000000000000000), (227409622651701887688642514842693943/552441097963392000000000000000000000)]
    reserve := (205822506227/500000000000) }

theorem tilt_001_020_valid : tilt_001_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_001_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_001_020]
  · intro i; fin_cases i <;> norm_num [tilt_001_020]
  · norm_num [tilt_001_020]
  · norm_num [tilt_001_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_001_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_001_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_001_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_001_020]

def tiltBundle001_row : Alternative → Row
  | .zero => tilt_001_000
  | (.spike 0 false false) => tilt_001_001
  | (.spike 0 false true) => tilt_001_002
  | (.spike 0 true false) => tilt_001_003
  | (.spike 0 true true) => tilt_001_004
  | (.spike 1 false false) => tilt_001_005
  | (.spike 1 false true) => tilt_001_006
  | (.spike 1 true false) => tilt_001_007
  | (.spike 1 true true) => tilt_001_008
  | (.spike 2 false false) => tilt_001_009
  | (.spike 2 false true) => tilt_001_010
  | (.spike 2 true false) => tilt_001_011
  | (.spike 2 true true) => tilt_001_012
  | (.spike 3 false false) => tilt_001_013
  | (.spike 3 false true) => tilt_001_014
  | (.spike 3 true false) => tilt_001_015
  | (.spike 3 true true) => tilt_001_016
  | (.spike 4 false false) => tilt_001_017
  | (.spike 4 false true) => tilt_001_018
  | (.spike 4 true false) => tilt_001_019
  | (.spike 4 true true) => tilt_001_020

def tiltBundle001 : TiltBundle where
  interval := ⟨(-7/20), (-13/40)⟩
  lambda := ![0, 0, 0, 0, 0, 0, 1]
  row := tiltBundle001_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_001_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_001_001_valid | exact tilt_001_002_valid | exact tilt_001_003_valid | exact tilt_001_004_valid | exact tilt_001_005_valid | exact tilt_001_006_valid | exact tilt_001_007_valid | exact tilt_001_008_valid | exact tilt_001_009_valid | exact tilt_001_010_valid | exact tilt_001_011_valid | exact tilt_001_012_valid | exact tilt_001_013_valid | exact tilt_001_014_valid | exact tilt_001_015_valid | exact tilt_001_016_valid | exact tilt_001_017_valid | exact tilt_001_018_valid | exact tilt_001_019_valid | exact tilt_001_020_valid
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
