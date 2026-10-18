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

def tilt_002_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(28469751/50000000), 0, (41103203/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := .zero
    polynomial := [(-2249977462230083738891040853/149278103130750000000000000), (-28469751/288761), (-12874348787371208738891040853/74639051565375000000000000), (-28469751/288761), (-23498720112512333738891040853/149278103130750000000000000)]
    bernstein := [(145021121019048388530193505215067/382151944014720000000000000000000), (38582850350192937505867692927877/95537986003680000000000000000000), (29368254773592548897650043221661/71653489502760000000000000000000), (2376207798709122635324804143097/5971124125230000000000000000000), (550023553041015348235543625507/1492781031307500000000000000000)]
    reserve := (18422780753/50000000000) }

theorem tilt_002_000_valid : tilt_002_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_000]
  · intro i; fin_cases i <;> norm_num [tilt_002_000]
  · norm_num [tilt_002_000]
  · norm_num [tilt_002_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_000]

def tilt_002_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11371459/20000000), 0, (16452669/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-562516789401714681481562557/37319525782687500000000000), (-11387911669/115504400), (-3218612260579375853356562557/18659762891343750000000000), (-11387911669/115504400), (-534064339250639729566505687/3392684162062500000000000)]
    bernstein := [(36186878802265976303082165063923/95537986003680000000000000000000), (9628738593004047009879977296813/23884496500920000000000000000000), (7329424767192164135552191101509/17913372375690000000000000000000), (593006074465961013847625084993/1492781031307500000000000000000), (137246197231264789161305260283/373195257826875000000000000000)]
    reserve := (36775975673/100000000000) }

theorem tilt_002_001_valid : tilt_002_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_001]
  · intro i; fin_cases i <;> norm_num [tilt_002_001]
  · norm_num [tilt_002_001]
  · norm_num [tilt_002_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_001]

def tilt_002_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14255427/25000000), 0, (41074733/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-2249892317878266475022022103/149278103130750000000000000), (-28469779267/288761000), (-12874274202976631725022022103/74639051565375000000000000), (-28469779267/288761000), (-23498656088074996975022022103/149278103130750000000000000)]
    bernstein := [(145294696543849696018109889733817/382151944014720000000000000000000), (38650744253513008771297833009127/95537986003680000000000000000000), (29418810417266540564090432652911/71653489502760000000000000000000), (2380391205041893547596220349347/5971124125230000000000000000000), (551062218728382107263355394257/1492781031307500000000000000000)]
    reserve := (184575703727/500000000000) }

theorem tilt_002_002_valid : tilt_002_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_002]
  · intro i; fin_cases i <;> norm_num [tilt_002_002]
  · norm_num [tilt_002_002]
  · norm_num [tilt_002_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_002]

def tilt_002_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11371459/20000000), 0, (16452669/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-562516789401714681481562557/37319525782687500000000000), (-11387911669/115504400), (-3218612260579375853356562557/18659762891343750000000000), (-11387911669/115504400), (-534064339250639729566505687/3392684162062500000000000)]
    bernstein := [(36186878802265976303082165063923/95537986003680000000000000000000), (9628738593004047009879977296813/23884496500920000000000000000000), (7329424767192164135552191101509/17913372375690000000000000000000), (593006074465961013847625084993/1492781031307500000000000000000), (137246197231264789161305260283/373195257826875000000000000000)]
    reserve := (36775975673/100000000000) }

theorem tilt_002_003_valid : tilt_002_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_003]
  · intro i; fin_cases i <;> norm_num [tilt_002_003]
  · norm_num [tilt_002_003]
  · norm_num [tilt_002_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_003]

def tilt_002_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14255427/25000000), 0, (41074733/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-2249892317878266475022022103/149278103130750000000000000), (-28469779267/288761000), (-12874274202976631725022022103/74639051565375000000000000), (-28469779267/288761000), (-23498656088074996975022022103/149278103130750000000000000)]
    bernstein := [(145294696543849696018109889733817/382151944014720000000000000000000), (38650744253513008771297833009127/95537986003680000000000000000000), (29418810417266540564090432652911/71653489502760000000000000000000), (2380391205041893547596220349347/5971124125230000000000000000000), (551062218728382107263355394257/1492781031307500000000000000000)]
    reserve := (184575703727/500000000000) }

theorem tilt_002_004_valid : tilt_002_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_004]
  · intro i; fin_cases i <;> norm_num [tilt_002_004]
  · norm_num [tilt_002_004]
  · norm_num [tilt_002_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_004]

def tilt_002_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11371459/20000000), 0, (16452669/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-562516789401714681481562557/37319525782687500000000000), (-11387911669/115504400), (-3218612260579375853356562557/18659762891343750000000000), (-11387911669/115504400), (-534064339250639729566505687/3392684162062500000000000)]
    bernstein := [(36186878802265976303082165063923/95537986003680000000000000000000), (9628738593004047009879977296813/23884496500920000000000000000000), (7329424767192164135552191101509/17913372375690000000000000000000), (593006074465961013847625084993/1492781031307500000000000000000), (137246197231264789161305260283/373195257826875000000000000000)]
    reserve := (36775975673/100000000000) }

theorem tilt_002_005_valid : tilt_002_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_005]
  · intro i; fin_cases i <;> norm_num [tilt_002_005]
  · norm_num [tilt_002_005]
  · norm_num [tilt_002_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_005]

def tilt_002_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14255427/25000000), 0, (41074733/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-2249892317878266475022022103/149278103130750000000000000), (-28469779267/288761000), (-12874274202976631725022022103/74639051565375000000000000), (-28469779267/288761000), (-23498656088074996975022022103/149278103130750000000000000)]
    bernstein := [(145294696543849696018109889733817/382151944014720000000000000000000), (38650744253513008771297833009127/95537986003680000000000000000000), (29418810417266540564090432652911/71653489502760000000000000000000), (2380391205041893547596220349347/5971124125230000000000000000000), (551062218728382107263355394257/1492781031307500000000000000000)]
    reserve := (184575703727/500000000000) }

theorem tilt_002_006_valid : tilt_002_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_006]
  · intro i; fin_cases i <;> norm_num [tilt_002_006]
  · norm_num [tilt_002_006]
  · norm_num [tilt_002_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_006]

def tilt_002_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11371459/20000000), 0, (16452669/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-562516789401714681481562557/37319525782687500000000000), (-11387911669/115504400), (-3218612260579375853356562557/18659762891343750000000000), (-11387911669/115504400), (-534064339250639729566505687/3392684162062500000000000)]
    bernstein := [(36186878802265976303082165063923/95537986003680000000000000000000), (9628738593004047009879977296813/23884496500920000000000000000000), (7329424767192164135552191101509/17913372375690000000000000000000), (593006074465961013847625084993/1492781031307500000000000000000), (137246197231264789161305260283/373195257826875000000000000000)]
    reserve := (36775975673/100000000000) }

theorem tilt_002_007_valid : tilt_002_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_007]
  · intro i; fin_cases i <;> norm_num [tilt_002_007]
  · norm_num [tilt_002_007]
  · norm_num [tilt_002_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_007]

def tilt_002_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14255427/25000000), 0, (41074733/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-2249892317878266475022022103/149278103130750000000000000), (-28469779267/288761000), (-12874274202976631725022022103/74639051565375000000000000), (-28469779267/288761000), (-23498656088074996975022022103/149278103130750000000000000)]
    bernstein := [(145294696543849696018109889733817/382151944014720000000000000000000), (38650744253513008771297833009127/95537986003680000000000000000000), (29418810417266540564090432652911/71653489502760000000000000000000), (2380391205041893547596220349347/5971124125230000000000000000000), (551062218728382107263355394257/1492781031307500000000000000000)]
    reserve := (184575703727/500000000000) }

theorem tilt_002_008_valid : tilt_002_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_008]
  · intro i; fin_cases i <;> norm_num [tilt_002_008]
  · norm_num [tilt_002_008]
  · norm_num [tilt_002_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_008]

def tilt_002_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11371459/20000000), 0, (16452669/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-562516789401714681481562557/37319525782687500000000000), (-11387911669/115504400), (-3218612260579375853356562557/18659762891343750000000000), (-11387911669/115504400), (-534064339250639729566505687/3392684162062500000000000)]
    bernstein := [(36186878802265976303082165063923/95537986003680000000000000000000), (9628738593004047009879977296813/23884496500920000000000000000000), (7329424767192164135552191101509/17913372375690000000000000000000), (593006074465961013847625084993/1492781031307500000000000000000), (137246197231264789161305260283/373195257826875000000000000000)]
    reserve := (36775975673/100000000000) }

theorem tilt_002_009_valid : tilt_002_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_009]
  · intro i; fin_cases i <;> norm_num [tilt_002_009]
  · norm_num [tilt_002_009]
  · norm_num [tilt_002_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_009]

def tilt_002_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14255427/25000000), 0, (41074733/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-2249892317878266475022022103/149278103130750000000000000), (-28469779267/288761000), (-12874274202976631725022022103/74639051565375000000000000), (-28469779267/288761000), (-23498656088074996975022022103/149278103130750000000000000)]
    bernstein := [(145294696543849696018109889733817/382151944014720000000000000000000), (38650744253513008771297833009127/95537986003680000000000000000000), (29418810417266540564090432652911/71653489502760000000000000000000), (2380391205041893547596220349347/5971124125230000000000000000000), (551062218728382107263355394257/1492781031307500000000000000000)]
    reserve := (184575703727/500000000000) }

theorem tilt_002_010_valid : tilt_002_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_010]
  · intro i; fin_cases i <;> norm_num [tilt_002_010]
  · norm_num [tilt_002_010]
  · norm_num [tilt_002_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_010]

def tilt_002_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11371459/20000000), 0, (16452669/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-562516789401714681481562557/37319525782687500000000000), (-11387911669/115504400), (-3218612260579375853356562557/18659762891343750000000000), (-11387911669/115504400), (-534064339250639729566505687/3392684162062500000000000)]
    bernstein := [(36186878802265976303082165063923/95537986003680000000000000000000), (9628738593004047009879977296813/23884496500920000000000000000000), (7329424767192164135552191101509/17913372375690000000000000000000), (593006074465961013847625084993/1492781031307500000000000000000), (137246197231264789161305260283/373195257826875000000000000000)]
    reserve := (36775975673/100000000000) }

theorem tilt_002_011_valid : tilt_002_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_011]
  · intro i; fin_cases i <;> norm_num [tilt_002_011]
  · norm_num [tilt_002_011]
  · norm_num [tilt_002_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_011]

def tilt_002_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14255427/25000000), 0, (41074733/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-2249892317878266475022022103/149278103130750000000000000), (-28469779267/288761000), (-12874274202976631725022022103/74639051565375000000000000), (-28469779267/288761000), (-23498656088074996975022022103/149278103130750000000000000)]
    bernstein := [(145294696543849696018109889733817/382151944014720000000000000000000), (38650744253513008771297833009127/95537986003680000000000000000000), (29418810417266540564090432652911/71653489502760000000000000000000), (2380391205041893547596220349347/5971124125230000000000000000000), (551062218728382107263355394257/1492781031307500000000000000000)]
    reserve := (184575703727/500000000000) }

theorem tilt_002_012_valid : tilt_002_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_012]
  · intro i; fin_cases i <;> norm_num [tilt_002_012]
  · norm_num [tilt_002_012]
  · norm_num [tilt_002_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_012]

def tilt_002_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11371459/20000000), 0, (16452669/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-562516789401714681481562557/37319525782687500000000000), (-11387911669/115504400), (-3218612260579375853356562557/18659762891343750000000000), (-11387911669/115504400), (-534064339250639729566505687/3392684162062500000000000)]
    bernstein := [(36186878802265976303082165063923/95537986003680000000000000000000), (9628738593004047009879977296813/23884496500920000000000000000000), (7329424767192164135552191101509/17913372375690000000000000000000), (593006074465961013847625084993/1492781031307500000000000000000), (137246197231264789161305260283/373195257826875000000000000000)]
    reserve := (36775975673/100000000000) }

theorem tilt_002_013_valid : tilt_002_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_013]
  · intro i; fin_cases i <;> norm_num [tilt_002_013]
  · norm_num [tilt_002_013]
  · norm_num [tilt_002_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_013]

def tilt_002_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14255427/25000000), 0, (41074733/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-2249892317878266475022022103/149278103130750000000000000), (-28469779267/288761000), (-12874274202976631725022022103/74639051565375000000000000), (-28469779267/288761000), (-23498656088074996975022022103/149278103130750000000000000)]
    bernstein := [(145294696543849696018109889733817/382151944014720000000000000000000), (38650744253513008771297833009127/95537986003680000000000000000000), (29418810417266540564090432652911/71653489502760000000000000000000), (2380391205041893547596220349347/5971124125230000000000000000000), (551062218728382107263355394257/1492781031307500000000000000000)]
    reserve := (184575703727/500000000000) }

theorem tilt_002_014_valid : tilt_002_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_014]
  · intro i; fin_cases i <;> norm_num [tilt_002_014]
  · norm_num [tilt_002_014]
  · norm_num [tilt_002_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_014]

def tilt_002_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11371459/20000000), 0, (16452669/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-562516789401714681481562557/37319525782687500000000000), (-11387911669/115504400), (-3218612260579375853356562557/18659762891343750000000000), (-11387911669/115504400), (-534064339250639729566505687/3392684162062500000000000)]
    bernstein := [(36186878802265976303082165063923/95537986003680000000000000000000), (9628738593004047009879977296813/23884496500920000000000000000000), (7329424767192164135552191101509/17913372375690000000000000000000), (593006074465961013847625084993/1492781031307500000000000000000), (137246197231264789161305260283/373195257826875000000000000000)]
    reserve := (36775975673/100000000000) }

theorem tilt_002_015_valid : tilt_002_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_015]
  · intro i; fin_cases i <;> norm_num [tilt_002_015]
  · norm_num [tilt_002_015]
  · norm_num [tilt_002_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_015]

def tilt_002_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14255427/25000000), 0, (41074733/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-2249892317878266475022022103/149278103130750000000000000), (-28469779267/288761000), (-12874274202976631725022022103/74639051565375000000000000), (-28469779267/288761000), (-23498656088074996975022022103/149278103130750000000000000)]
    bernstein := [(145294696543849696018109889733817/382151944014720000000000000000000), (38650744253513008771297833009127/95537986003680000000000000000000), (29418810417266540564090432652911/71653489502760000000000000000000), (2380391205041893547596220349347/5971124125230000000000000000000), (551062218728382107263355394257/1492781031307500000000000000000)]
    reserve := (184575703727/500000000000) }

theorem tilt_002_016_valid : tilt_002_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_016]
  · intro i; fin_cases i <;> norm_num [tilt_002_016]
  · norm_num [tilt_002_016]
  · norm_num [tilt_002_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_016]

def tilt_002_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11371459/20000000), 0, (16452669/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-562516789401714681481562557/37319525782687500000000000), (-11387911669/115504400), (-3218612260579375853356562557/18659762891343750000000000), (-11387911669/115504400), (-534064339250639729566505687/3392684162062500000000000)]
    bernstein := [(36186878802265976303082165063923/95537986003680000000000000000000), (9628738593004047009879977296813/23884496500920000000000000000000), (7329424767192164135552191101509/17913372375690000000000000000000), (593006074465961013847625084993/1492781031307500000000000000000), (137246197231264789161305260283/373195257826875000000000000000)]
    reserve := (36775975673/100000000000) }

theorem tilt_002_017_valid : tilt_002_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_017]
  · intro i; fin_cases i <;> norm_num [tilt_002_017]
  · norm_num [tilt_002_017]
  · norm_num [tilt_002_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_017]

def tilt_002_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14255427/25000000), 0, (41074733/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-2249892317878266475022022103/149278103130750000000000000), (-28469779267/288761000), (-12874274202976631725022022103/74639051565375000000000000), (-28469779267/288761000), (-23498656088074996975022022103/149278103130750000000000000)]
    bernstein := [(145294696543849696018109889733817/382151944014720000000000000000000), (38650744253513008771297833009127/95537986003680000000000000000000), (29418810417266540564090432652911/71653489502760000000000000000000), (2380391205041893547596220349347/5971124125230000000000000000000), (551062218728382107263355394257/1492781031307500000000000000000)]
    reserve := (184575703727/500000000000) }

theorem tilt_002_018_valid : tilt_002_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_018]
  · intro i; fin_cases i <;> norm_num [tilt_002_018]
  · norm_num [tilt_002_018]
  · norm_num [tilt_002_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_018]

def tilt_002_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(11371459/20000000), 0, (16452669/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-562516789401714681481562557/37319525782687500000000000), (-11387911669/115504400), (-3218612260579375853356562557/18659762891343750000000000), (-11387911669/115504400), (-534064339250639729566505687/3392684162062500000000000)]
    bernstein := [(36186878802265976303082165063923/95537986003680000000000000000000), (9628738593004047009879977296813/23884496500920000000000000000000), (7329424767192164135552191101509/17913372375690000000000000000000), (593006074465961013847625084993/1492781031307500000000000000000), (137246197231264789161305260283/373195257826875000000000000000)]
    reserve := (36775975673/100000000000) }

theorem tilt_002_019_valid : tilt_002_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_019]
  · intro i; fin_cases i <;> norm_num [tilt_002_019]
  · norm_num [tilt_002_019]
  · norm_num [tilt_002_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_019]

def tilt_002_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14255427/25000000), 0, (41074733/50000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (288761/50000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-2249892317878266475022022103/149278103130750000000000000), (-28469779267/288761000), (-12874274202976631725022022103/74639051565375000000000000), (-28469779267/288761000), (-23498656088074996975022022103/149278103130750000000000000)]
    bernstein := [(145294696543849696018109889733817/382151944014720000000000000000000), (38650744253513008771297833009127/95537986003680000000000000000000), (29418810417266540564090432652911/71653489502760000000000000000000), (2380391205041893547596220349347/5971124125230000000000000000000), (551062218728382107263355394257/1492781031307500000000000000000)]
    reserve := (184575703727/500000000000) }

theorem tilt_002_020_valid : tilt_002_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_002_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_002_020]
  · intro i; fin_cases i <;> norm_num [tilt_002_020]
  · norm_num [tilt_002_020]
  · norm_num [tilt_002_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_002_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_002_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_002_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_002_020]

def tiltBundle002_row : Alternative → Row
  | .zero => tilt_002_000
  | (.spike 0 false false) => tilt_002_001
  | (.spike 0 false true) => tilt_002_002
  | (.spike 0 true false) => tilt_002_003
  | (.spike 0 true true) => tilt_002_004
  | (.spike 1 false false) => tilt_002_005
  | (.spike 1 false true) => tilt_002_006
  | (.spike 1 true false) => tilt_002_007
  | (.spike 1 true true) => tilt_002_008
  | (.spike 2 false false) => tilt_002_009
  | (.spike 2 false true) => tilt_002_010
  | (.spike 2 true false) => tilt_002_011
  | (.spike 2 true true) => tilt_002_012
  | (.spike 3 false false) => tilt_002_013
  | (.spike 3 false true) => tilt_002_014
  | (.spike 3 true false) => tilt_002_015
  | (.spike 3 true true) => tilt_002_016
  | (.spike 4 false false) => tilt_002_017
  | (.spike 4 false true) => tilt_002_018
  | (.spike 4 true false) => tilt_002_019
  | (.spike 4 true true) => tilt_002_020

def tiltBundle002 : TiltBundle where
  interval := ⟨(-13/40), (-3/10)⟩
  lambda := ![0, 0, 0, 0, 0, 0, 1]
  row := tiltBundle002_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_002_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_002_001_valid | exact tilt_002_002_valid | exact tilt_002_003_valid | exact tilt_002_004_valid | exact tilt_002_005_valid | exact tilt_002_006_valid | exact tilt_002_007_valid | exact tilt_002_008_valid | exact tilt_002_009_valid | exact tilt_002_010_valid | exact tilt_002_011_valid | exact tilt_002_012_valid | exact tilt_002_013_valid | exact tilt_002_014_valid | exact tilt_002_015_valid | exact tilt_002_016_valid | exact tilt_002_017_valid | exact tilt_002_018_valid | exact tilt_002_019_valid | exact tilt_002_020_valid
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
