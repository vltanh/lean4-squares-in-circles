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

def tilt_056_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_000_valid : tilt_056_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_000]
  · intro i; fin_cases i <;> norm_num [tilt_056_000]
  · norm_num [tilt_056_000]
  · norm_num [tilt_056_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_000]

def tilt_056_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_001_valid : tilt_056_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_001]
  · intro i; fin_cases i <;> norm_num [tilt_056_001]
  · norm_num [tilt_056_001]
  · norm_num [tilt_056_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_001]

def tilt_056_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_002_valid : tilt_056_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_002]
  · intro i; fin_cases i <;> norm_num [tilt_056_002]
  · norm_num [tilt_056_002]
  · norm_num [tilt_056_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_002]

def tilt_056_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_003_valid : tilt_056_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_003]
  · intro i; fin_cases i <;> norm_num [tilt_056_003]
  · norm_num [tilt_056_003]
  · norm_num [tilt_056_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_003]

def tilt_056_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_004_valid : tilt_056_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_004]
  · intro i; fin_cases i <;> norm_num [tilt_056_004]
  · norm_num [tilt_056_004]
  · norm_num [tilt_056_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_004]

def tilt_056_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (5559341/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-132599294731017579025761742397/578375491814700000000000000000), (1145370724492751/832293600000000), (-350992023854919573838761742397/289187745907350000000000000000), (1145370724492751/832293600000000), (-569384752978821568651761742397/578375491814700000000000000000)]
    bernstein := [(598819497561218594432764988581243/5783754918147000000000000000000000), (842439135384612645690960975687051/7711673224196000000000000000000000), (31897626497700104250697633931283589/277620236071056000000000000000000000), (44604000030834272181919750147671373/370160314761408000000000000000000000), (186634847781902591782693257050781683/1480641259045632000000000000000000000)]
    reserve := (20706945783/200000000000) }

theorem tilt_056_005_valid : tilt_056_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_005]
  · intro i; fin_cases i <;> norm_num [tilt_056_005]
  · norm_num [tilt_056_005]
  · norm_num [tilt_056_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_005]

def tilt_056_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (173903/1562500), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-133059884031550993446282032467/578953415683200000000000000000), (1145370724492751/832293600000000), (-351670835353062970374282032467/289476707841600000000000000000), (1145370724492751/832293600000000), (-570281786674574947302282032467/578953415683200000000000000000)]
    bernstein := [(595519770055470581293227172259573/5789534156832000000000000000000000), (838047715284869254822590821473861/7719378875776000000000000000000000), (31739774858990741942424585059535179/277897639527936000000000000000000000), (44393774707182903181941424124420003/370530186037248000000000000000000000), (185794613750015153071212356597036413/1482120744148992000000000000000000000)]
    reserve := (102861431321/1000000000000) }

theorem tilt_056_006_valid : tilt_056_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_006]
  · intro i; fin_cases i <;> norm_num [tilt_056_006]
  · norm_num [tilt_056_006]
  · norm_num [tilt_056_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_006]

def tilt_056_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8315601/100000000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-21215255660429592757374557681/92504699690235000000000000000), (1145370724492751/831560100000000), (-18736146729627737064208994227/15417449948372500000000000000), (1145370724492751/831560100000000), (-5364801453960989978110553393/5441452922955000000000000000)]
    bernstein := [(95927819868658115079527122342039/925046996902350000000000000000000), (134946721049157779819302508518823/1233395995869800000000000000000000), (1703092963951044711905827182887299/14800751950437600000000000000000000), (2381404379127106014646409761534843/19734335933916800000000000000000000), (29891954336552776464104014339978159/236812031207001600000000000000000000)]
    reserve := (103700482451/1000000000000) }

theorem tilt_056_007_valid : tilt_056_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_007]
  · intro i; fin_cases i <;> norm_num [tilt_056_007]
  · norm_num [tilt_056_007]
  · norm_num [tilt_056_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_007]

def tilt_056_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (260321/3125000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-12523666213194177531149188883/54510531377600000000000000000), (1145370724492751/833027200000000), (-562176285348624781501511961011/463339516709600000000000000000), (1145370724492751/833027200000000), (-911450245072948544973487711011/926679033419200000000000000000)]
    bernstein := [(951660964429037440857658855478309/9266790334192000000000000000000000), (4017920411463332087241296415412639/37067161336768000000000000000000000), (50726872976330540124401236042646107/444805936041216000000000000000000000), (70954064871080742083758083768256499/593074581388288000000000000000000000), (296966609685248945884956028782906029/2372298325553152000000000000000000000)]
    reserve := (51347927929/500000000000) }

theorem tilt_056_008_valid : tilt_056_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_008]
  · intro i; fin_cases i <;> norm_num [tilt_056_008]
  · norm_num [tilt_056_008]
  · norm_num [tilt_056_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_008]

def tilt_056_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (5559341/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-66299653735494332407604326261/289187745907350000000000000000), (1145370724492751/832293600000000), (-175496018297445329814104326261/144593872953675000000000000000), (1145370724492751/832293600000000), (-284692382859396327220604326261/289187745907350000000000000000)]
    bernstein := [(299409673098811062084173124693059/2891877459073500000000000000000000), (421219466088913585160343138444963/3855836612098000000000000000000000), (15948809565323102134417347670835357/138810118035528000000000000000000000), (22301995068543693348803692383393749/185080157380704000000000000000000000), (93317403956966967392771942467550779/740320629522816000000000000000000000)]
    reserve := (12941837843/125000000000) }

theorem tilt_056_009_valid : tilt_056_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_009]
  · intro i; fin_cases i <;> norm_num [tilt_056_009]
  · norm_num [tilt_056_009]
  · norm_num [tilt_056_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_009]

def tilt_056_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (173903/1562500), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-259864812779650988933345591/1130768390006250000000000000), (1145370724492751/832293600000000), (-686839327079479068870845591/565384195003125000000000000), (1145370724492751/832293600000000), (-1113813841379307148808345591/1130768390006250000000000000)]
    bernstein := [(1163335714510138347413592908329/11307683900062500000000000000000), (1637095432690745874012799364603/15076911866750000000000000000000), (62002025366677856095913286324067/542768827203000000000000000000000), (86720393747249622785652952420969/723691769604000000000000000000000), (362935723800358604498023395502649/2894767078416000000000000000000000)]
    reserve := (102880105669/1000000000000) }

theorem tilt_056_010_valid : tilt_056_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_010]
  · intro i; fin_cases i <;> norm_num [tilt_056_010]
  · norm_num [tilt_056_010]
  · norm_num [tilt_056_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_010]

def tilt_056_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(325453/20000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1327171696571524599610753489/5786643497122500000000000000), (1145370724492751/832293600000000), (-3512189705959354836385753489/2893321748561250000000000000), (1145370724492751/832293600000000), (-5697207715347185073160753489/5786643497122500000000000000)]
    bernstein := [(5985049014555299932463306547191/57866434971225000000000000000000), (25261080762923640338058401985361/231465739884900000000000000000000), (318836893151078907378562658315393/2777588878618800000000000000000000), (148620549895948316645960077512167/1234483946052800000000000000000000), (621888081515191319846449975303157/4937935784211200000000000000000000)]
    reserve := (12928585063/125000000000) }

theorem tilt_056_011_valid : tilt_056_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_011]
  · intro i; fin_cases i <;> norm_num [tilt_056_011]
  · norm_num [tilt_056_011]
  · norm_num [tilt_056_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_011]

def tilt_056_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(31269/2000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-1329325820875614328564433489/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514343830263444565339433489/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699361839651274802114433489/5786643497122500000000000000)]
    bernstein := [(5959455863698409862764634467191/57866434971225000000000000000000), (8386001253616214239298620101787/77155246628300000000000000000000), (317591242768623068444620800475393/2777588878618800000000000000000000), (444188776140407603240012927656501/3703451838158400000000000000000000), (1858923211959203421251132927429471/14813807352633600000000000000000000)]
    reserve := (5149320039/50000000000) }

theorem tilt_056_012_valid : tilt_056_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_012]
  · intro i; fin_cases i <;> norm_num [tilt_056_012]
  · norm_num [tilt_056_012]
  · norm_num [tilt_056_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_012]

def tilt_056_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_013_valid : tilt_056_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_013]
  · intro i; fin_cases i <;> norm_num [tilt_056_013]
  · norm_num [tilt_056_013]
  · norm_num [tilt_056_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_013]

def tilt_056_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_014_valid : tilt_056_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_014]
  · intro i; fin_cases i <;> norm_num [tilt_056_014]
  · norm_num [tilt_056_014]
  · norm_num [tilt_056_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_014]

def tilt_056_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_015_valid : tilt_056_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_015]
  · intro i; fin_cases i <;> norm_num [tilt_056_015]
  · norm_num [tilt_056_015]
  · norm_num [tilt_056_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_015]

def tilt_056_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_016_valid : tilt_056_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_016]
  · intro i; fin_cases i <;> norm_num [tilt_056_016]
  · norm_num [tilt_056_016]
  · norm_num [tilt_056_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_016]

def tilt_056_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_017_valid : tilt_056_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_017]
  · intro i; fin_cases i <;> norm_num [tilt_056_017]
  · norm_num [tilt_056_017]
  · norm_num [tilt_056_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_017]

def tilt_056_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_018_valid : tilt_056_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_018]
  · intro i; fin_cases i <;> norm_num [tilt_056_018]
  · norm_num [tilt_056_018]
  · norm_num [tilt_056_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_018]

def tilt_056_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_019_valid : tilt_056_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_019]
  · intro i; fin_cases i <;> norm_num [tilt_056_019]
  · norm_num [tilt_056_019]
  · norm_num [tilt_056_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_019]

def tilt_056_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(117999/6250000), 0, (37759679/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(797679/50000000), 0, (1994197/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1040367/12500000), (2224847/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-1329171904365440143423447889/5786643497122500000000000000), (1145370724492751/832293600000000), (-3514189913753270380198447889/2893321748561250000000000000), (1145370724492751/832293600000000), (-5699207923141100616973447889/5786643497122500000000000000)]
    bernstein := [(5961284545755789356424684380791/57866434971225000000000000000000), (8388456273258995883692387416987/77155246628300000000000000000000), (317680246991545923266802556488193/2777588878618800000000000000000000), (444308306316960283852836075746101/3703451838158400000000000000000000), (1859404872283398619438112765631071/14813807352633600000000000000000000)]
    reserve := (20603600511/200000000000) }

theorem tilt_056_020_valid : tilt_056_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_056_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_056_020]
  · intro i; fin_cases i <;> norm_num [tilt_056_020]
  · norm_num [tilt_056_020]
  · norm_num [tilt_056_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_056_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_056_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_056_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_056_020]

def tiltBundle056_row : Alternative → Row
  | .zero => tilt_056_000
  | (.spike 0 false false) => tilt_056_001
  | (.spike 0 false true) => tilt_056_002
  | (.spike 0 true false) => tilt_056_003
  | (.spike 0 true true) => tilt_056_004
  | (.spike 1 false false) => tilt_056_005
  | (.spike 1 false true) => tilt_056_006
  | (.spike 1 true false) => tilt_056_007
  | (.spike 1 true true) => tilt_056_008
  | (.spike 2 false false) => tilt_056_009
  | (.spike 2 false true) => tilt_056_010
  | (.spike 2 true false) => tilt_056_011
  | (.spike 2 true true) => tilt_056_012
  | (.spike 3 false false) => tilt_056_013
  | (.spike 3 false true) => tilt_056_014
  | (.spike 3 true false) => tilt_056_015
  | (.spike 3 true true) => tilt_056_016
  | (.spike 4 false false) => tilt_056_017
  | (.spike 4 false true) => tilt_056_018
  | (.spike 4 true false) => tilt_056_019
  | (.spike 4 true true) => tilt_056_020

def tiltBundle056 : TiltBundle where
  interval := ⟨(3/10), (13/40)⟩
  lambda := ![0, (37759679/100000000), (30333169/100000000), (1994197/6250000), 0, 0, 0]
  row := tiltBundle056_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_056_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_056_001_valid | exact tilt_056_002_valid | exact tilt_056_003_valid | exact tilt_056_004_valid | exact tilt_056_005_valid | exact tilt_056_006_valid | exact tilt_056_007_valid | exact tilt_056_008_valid | exact tilt_056_009_valid | exact tilt_056_010_valid | exact tilt_056_011_valid | exact tilt_056_012_valid | exact tilt_056_013_valid | exact tilt_056_014_valid | exact tilt_056_015_valid | exact tilt_056_016_valid | exact tilt_056_017_valid | exact tilt_056_018_valid | exact tilt_056_019_valid | exact tilt_056_020_valid
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
