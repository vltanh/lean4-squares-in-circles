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

def tilt_000_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(64079547/100000000), 0, (19192791/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := .zero
    polynomial := [(-1620727449770030967505577765797/79689861485025000000000000000), (-64079547/560548), (-7077783246244318467505577765797/39844930742512500000000000000), (-64079547/560548), (-12534839042718605967505577765797/79689861485025000000000000000)]
    bernstein := [(152973127681015649162776086067787/326409672642662400000000000000000), (9351788505401607444158162337773/18977306548992000000000000000000), (3047791107911764812669211199920697/6120181362049920000000000000000000), (2472226517472226383039200551443607/5100151135041600000000000000000000), (5781511706612179969908016837559003/12750377837604000000000000000000000)]
    reserve := (14169951913/31250000000) }

theorem tilt_000_000_valid : tilt_000_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_000]
  · intro i; fin_cases i <;> norm_num [tilt_000_000]
  · norm_num [tilt_000_000]
  · norm_num [tilt_000_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_000]

def tilt_000_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8000347/12500000), 0, (19208811/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1620768341258972300701323703297/79689861485025000000000000000), (-16019902811/140137000), (-7077829626977591525701323703297/39844930742512500000000000000), (-16019902811/140137000), (-12534890912696210750701323703297/79689861485025000000000000000)]
    bernstein := [(152764005431005999312645985130287/326409672642662400000000000000000), (401608421781385638058409908336739/816024181606656000000000000000000), (3043933880820887712460581289608197/6120181362049920000000000000000000), (2469037505835640427079123956756107/5100151135041600000000000000000000), (5773600516601194882362440091621503/12750377837604000000000000000000000)]
    reserve := (3537640579/7812500000) }

theorem tilt_000_001_valid : tilt_000_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_001]
  · intro i; fin_cases i <;> norm_num [tilt_000_001]
  · norm_num [tilt_000_001]
  · norm_num [tilt_000_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_001]

def tilt_000_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32078159/50000000), 0, (15341417/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-1620689843681237165092878703297/79689861485025000000000000000), (-12815922183/112109600), (-7077751136081574083842878703297/39844930742512500000000000000), (-12815922183/112109600), (-12534812428481911002592878703297/79689861485025000000000000000)]
    bernstein := [(153182228298393691232549390130287/326409672642662400000000000000000), (402645388543198317759043693336739/816024181606656000000000000000000), (3051648488686393272135116344608197/6120181362049920000000000000000000), (2475415601598461911685590661756107/5100151135041600000000000000000000), (5789422472671814391898060536621503/12750377837604000000000000000000000)]
    reserve := (45405889507/100000000000) }

theorem tilt_000_002_valid : tilt_000_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_002]
  · intro i; fin_cases i <;> norm_num [tilt_000_002]
  · norm_num [tilt_000_002]
  · norm_num [tilt_000_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_002]

def tilt_000_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8000347/12500000), 0, (19208811/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-1620768341258972300701323703297/79689861485025000000000000000), (-16019902811/140137000), (-7077829626977591525701323703297/39844930742512500000000000000), (-16019902811/140137000), (-12534890912696210750701323703297/79689861485025000000000000000)]
    bernstein := [(152764005431005999312645985130287/326409672642662400000000000000000), (401608421781385638058409908336739/816024181606656000000000000000000), (3043933880820887712460581289608197/6120181362049920000000000000000000), (2469037505835640427079123956756107/5100151135041600000000000000000000), (5773600516601194882362440091621503/12750377837604000000000000000000000)]
    reserve := (3537640579/7812500000) }

theorem tilt_000_003_valid : tilt_000_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_003]
  · intro i; fin_cases i <;> norm_num [tilt_000_003]
  · norm_num [tilt_000_003]
  · norm_num [tilt_000_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_003]

def tilt_000_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32078159/50000000), 0, (15341417/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-1620689843681237165092878703297/79689861485025000000000000000), (-12815922183/112109600), (-7077751136081574083842878703297/39844930742512500000000000000), (-12815922183/112109600), (-12534812428481911002592878703297/79689861485025000000000000000)]
    bernstein := [(153182228298393691232549390130287/326409672642662400000000000000000), (402645388543198317759043693336739/816024181606656000000000000000000), (3051648488686393272135116344608197/6120181362049920000000000000000000), (2475415601598461911685590661756107/5100151135041600000000000000000000), (5789422472671814391898060536621503/12750377837604000000000000000000000)]
    reserve := (45405889507/100000000000) }

theorem tilt_000_004_valid : tilt_000_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_004]
  · intro i; fin_cases i <;> norm_num [tilt_000_004]
  · norm_num [tilt_000_004]
  · norm_num [tilt_000_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_004]

def tilt_000_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8000347/12500000), 0, (19208811/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-1620768341258972300701323703297/79689861485025000000000000000), (-16019902811/140137000), (-7077829626977591525701323703297/39844930742512500000000000000), (-16019902811/140137000), (-12534890912696210750701323703297/79689861485025000000000000000)]
    bernstein := [(152764005431005999312645985130287/326409672642662400000000000000000), (401608421781385638058409908336739/816024181606656000000000000000000), (3043933880820887712460581289608197/6120181362049920000000000000000000), (2469037505835640427079123956756107/5100151135041600000000000000000000), (5773600516601194882362440091621503/12750377837604000000000000000000000)]
    reserve := (3537640579/7812500000) }

theorem tilt_000_005_valid : tilt_000_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_005]
  · intro i; fin_cases i <;> norm_num [tilt_000_005]
  · norm_num [tilt_000_005]
  · norm_num [tilt_000_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_005]

def tilt_000_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32078159/50000000), 0, (15341417/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-1620689843681237165092878703297/79689861485025000000000000000), (-12815922183/112109600), (-7077751136081574083842878703297/39844930742512500000000000000), (-12815922183/112109600), (-12534812428481911002592878703297/79689861485025000000000000000)]
    bernstein := [(153182228298393691232549390130287/326409672642662400000000000000000), (402645388543198317759043693336739/816024181606656000000000000000000), (3051648488686393272135116344608197/6120181362049920000000000000000000), (2475415601598461911685590661756107/5100151135041600000000000000000000), (5789422472671814391898060536621503/12750377837604000000000000000000000)]
    reserve := (45405889507/100000000000) }

theorem tilt_000_006_valid : tilt_000_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_006]
  · intro i; fin_cases i <;> norm_num [tilt_000_006]
  · norm_num [tilt_000_006]
  · norm_num [tilt_000_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_006]

def tilt_000_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8000347/12500000), 0, (19208811/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-1620768341258972300701323703297/79689861485025000000000000000), (-16019902811/140137000), (-7077829626977591525701323703297/39844930742512500000000000000), (-16019902811/140137000), (-12534890912696210750701323703297/79689861485025000000000000000)]
    bernstein := [(152764005431005999312645985130287/326409672642662400000000000000000), (401608421781385638058409908336739/816024181606656000000000000000000), (3043933880820887712460581289608197/6120181362049920000000000000000000), (2469037505835640427079123956756107/5100151135041600000000000000000000), (5773600516601194882362440091621503/12750377837604000000000000000000000)]
    reserve := (3537640579/7812500000) }

theorem tilt_000_007_valid : tilt_000_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_007]
  · intro i; fin_cases i <;> norm_num [tilt_000_007]
  · norm_num [tilt_000_007]
  · norm_num [tilt_000_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_007]

def tilt_000_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32078159/50000000), 0, (15341417/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-1620689843681237165092878703297/79689861485025000000000000000), (-12815922183/112109600), (-7077751136081574083842878703297/39844930742512500000000000000), (-12815922183/112109600), (-12534812428481911002592878703297/79689861485025000000000000000)]
    bernstein := [(153182228298393691232549390130287/326409672642662400000000000000000), (402645388543198317759043693336739/816024181606656000000000000000000), (3051648488686393272135116344608197/6120181362049920000000000000000000), (2475415601598461911685590661756107/5100151135041600000000000000000000), (5789422472671814391898060536621503/12750377837604000000000000000000000)]
    reserve := (45405889507/100000000000) }

theorem tilt_000_008_valid : tilt_000_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_008]
  · intro i; fin_cases i <;> norm_num [tilt_000_008]
  · norm_num [tilt_000_008]
  · norm_num [tilt_000_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_008]

def tilt_000_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8000347/12500000), 0, (19208811/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-1620768341258972300701323703297/79689861485025000000000000000), (-16019902811/140137000), (-7077829626977591525701323703297/39844930742512500000000000000), (-16019902811/140137000), (-12534890912696210750701323703297/79689861485025000000000000000)]
    bernstein := [(152764005431005999312645985130287/326409672642662400000000000000000), (401608421781385638058409908336739/816024181606656000000000000000000), (3043933880820887712460581289608197/6120181362049920000000000000000000), (2469037505835640427079123956756107/5100151135041600000000000000000000), (5773600516601194882362440091621503/12750377837604000000000000000000000)]
    reserve := (3537640579/7812500000) }

theorem tilt_000_009_valid : tilt_000_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_009]
  · intro i; fin_cases i <;> norm_num [tilt_000_009]
  · norm_num [tilt_000_009]
  · norm_num [tilt_000_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_009]

def tilt_000_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32078159/50000000), 0, (15341417/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-1620689843681237165092878703297/79689861485025000000000000000), (-12815922183/112109600), (-7077751136081574083842878703297/39844930742512500000000000000), (-12815922183/112109600), (-12534812428481911002592878703297/79689861485025000000000000000)]
    bernstein := [(153182228298393691232549390130287/326409672642662400000000000000000), (402645388543198317759043693336739/816024181606656000000000000000000), (3051648488686393272135116344608197/6120181362049920000000000000000000), (2475415601598461911685590661756107/5100151135041600000000000000000000), (5789422472671814391898060536621503/12750377837604000000000000000000000)]
    reserve := (45405889507/100000000000) }

theorem tilt_000_010_valid : tilt_000_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_010]
  · intro i; fin_cases i <;> norm_num [tilt_000_010]
  · norm_num [tilt_000_010]
  · norm_num [tilt_000_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_010]

def tilt_000_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8000347/12500000), 0, (19208811/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-1620768341258972300701323703297/79689861485025000000000000000), (-16019902811/140137000), (-7077829626977591525701323703297/39844930742512500000000000000), (-16019902811/140137000), (-12534890912696210750701323703297/79689861485025000000000000000)]
    bernstein := [(152764005431005999312645985130287/326409672642662400000000000000000), (401608421781385638058409908336739/816024181606656000000000000000000), (3043933880820887712460581289608197/6120181362049920000000000000000000), (2469037505835640427079123956756107/5100151135041600000000000000000000), (5773600516601194882362440091621503/12750377837604000000000000000000000)]
    reserve := (3537640579/7812500000) }

theorem tilt_000_011_valid : tilt_000_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_011]
  · intro i; fin_cases i <;> norm_num [tilt_000_011]
  · norm_num [tilt_000_011]
  · norm_num [tilt_000_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_011]

def tilt_000_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32078159/50000000), 0, (15341417/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-1620689843681237165092878703297/79689861485025000000000000000), (-12815922183/112109600), (-7077751136081574083842878703297/39844930742512500000000000000), (-12815922183/112109600), (-12534812428481911002592878703297/79689861485025000000000000000)]
    bernstein := [(153182228298393691232549390130287/326409672642662400000000000000000), (402645388543198317759043693336739/816024181606656000000000000000000), (3051648488686393272135116344608197/6120181362049920000000000000000000), (2475415601598461911685590661756107/5100151135041600000000000000000000), (5789422472671814391898060536621503/12750377837604000000000000000000000)]
    reserve := (45405889507/100000000000) }

theorem tilt_000_012_valid : tilt_000_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_012]
  · intro i; fin_cases i <;> norm_num [tilt_000_012]
  · norm_num [tilt_000_012]
  · norm_num [tilt_000_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_012]

def tilt_000_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8000347/12500000), 0, (19208811/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-1620768341258972300701323703297/79689861485025000000000000000), (-16019902811/140137000), (-7077829626977591525701323703297/39844930742512500000000000000), (-16019902811/140137000), (-12534890912696210750701323703297/79689861485025000000000000000)]
    bernstein := [(152764005431005999312645985130287/326409672642662400000000000000000), (401608421781385638058409908336739/816024181606656000000000000000000), (3043933880820887712460581289608197/6120181362049920000000000000000000), (2469037505835640427079123956756107/5100151135041600000000000000000000), (5773600516601194882362440091621503/12750377837604000000000000000000000)]
    reserve := (3537640579/7812500000) }

theorem tilt_000_013_valid : tilt_000_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_013]
  · intro i; fin_cases i <;> norm_num [tilt_000_013]
  · norm_num [tilt_000_013]
  · norm_num [tilt_000_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_013]

def tilt_000_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32078159/50000000), 0, (15341417/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-1620689843681237165092878703297/79689861485025000000000000000), (-12815922183/112109600), (-7077751136081574083842878703297/39844930742512500000000000000), (-12815922183/112109600), (-12534812428481911002592878703297/79689861485025000000000000000)]
    bernstein := [(153182228298393691232549390130287/326409672642662400000000000000000), (402645388543198317759043693336739/816024181606656000000000000000000), (3051648488686393272135116344608197/6120181362049920000000000000000000), (2475415601598461911685590661756107/5100151135041600000000000000000000), (5789422472671814391898060536621503/12750377837604000000000000000000000)]
    reserve := (45405889507/100000000000) }

theorem tilt_000_014_valid : tilt_000_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_014]
  · intro i; fin_cases i <;> norm_num [tilt_000_014]
  · norm_num [tilt_000_014]
  · norm_num [tilt_000_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_014]

def tilt_000_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8000347/12500000), 0, (19208811/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1620768341258972300701323703297/79689861485025000000000000000), (-16019902811/140137000), (-7077829626977591525701323703297/39844930742512500000000000000), (-16019902811/140137000), (-12534890912696210750701323703297/79689861485025000000000000000)]
    bernstein := [(152764005431005999312645985130287/326409672642662400000000000000000), (401608421781385638058409908336739/816024181606656000000000000000000), (3043933880820887712460581289608197/6120181362049920000000000000000000), (2469037505835640427079123956756107/5100151135041600000000000000000000), (5773600516601194882362440091621503/12750377837604000000000000000000000)]
    reserve := (3537640579/7812500000) }

theorem tilt_000_015_valid : tilt_000_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_015]
  · intro i; fin_cases i <;> norm_num [tilt_000_015]
  · norm_num [tilt_000_015]
  · norm_num [tilt_000_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_015]

def tilt_000_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32078159/50000000), 0, (15341417/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-1620689843681237165092878703297/79689861485025000000000000000), (-12815922183/112109600), (-7077751136081574083842878703297/39844930742512500000000000000), (-12815922183/112109600), (-12534812428481911002592878703297/79689861485025000000000000000)]
    bernstein := [(153182228298393691232549390130287/326409672642662400000000000000000), (402645388543198317759043693336739/816024181606656000000000000000000), (3051648488686393272135116344608197/6120181362049920000000000000000000), (2475415601598461911685590661756107/5100151135041600000000000000000000), (5789422472671814391898060536621503/12750377837604000000000000000000000)]
    reserve := (45405889507/100000000000) }

theorem tilt_000_016_valid : tilt_000_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_016]
  · intro i; fin_cases i <;> norm_num [tilt_000_016]
  · norm_num [tilt_000_016]
  · norm_num [tilt_000_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_016]

def tilt_000_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8000347/12500000), 0, (19208811/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1620768341258972300701323703297/79689861485025000000000000000), (-16019902811/140137000), (-7077829626977591525701323703297/39844930742512500000000000000), (-16019902811/140137000), (-12534890912696210750701323703297/79689861485025000000000000000)]
    bernstein := [(152764005431005999312645985130287/326409672642662400000000000000000), (401608421781385638058409908336739/816024181606656000000000000000000), (3043933880820887712460581289608197/6120181362049920000000000000000000), (2469037505835640427079123956756107/5100151135041600000000000000000000), (5773600516601194882362440091621503/12750377837604000000000000000000000)]
    reserve := (3537640579/7812500000) }

theorem tilt_000_017_valid : tilt_000_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_017]
  · intro i; fin_cases i <;> norm_num [tilt_000_017]
  · norm_num [tilt_000_017]
  · norm_num [tilt_000_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_017]

def tilt_000_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32078159/50000000), 0, (15341417/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1620689843681237165092878703297/79689861485025000000000000000), (-12815922183/112109600), (-7077751136081574083842878703297/39844930742512500000000000000), (-12815922183/112109600), (-12534812428481911002592878703297/79689861485025000000000000000)]
    bernstein := [(153182228298393691232549390130287/326409672642662400000000000000000), (402645388543198317759043693336739/816024181606656000000000000000000), (3051648488686393272135116344608197/6120181362049920000000000000000000), (2475415601598461911685590661756107/5100151135041600000000000000000000), (5789422472671814391898060536621503/12750377837604000000000000000000000)]
    reserve := (45405889507/100000000000) }

theorem tilt_000_018_valid : tilt_000_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_018]
  · intro i; fin_cases i <;> norm_num [tilt_000_018]
  · norm_num [tilt_000_018]
  · norm_num [tilt_000_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_018]

def tilt_000_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8000347/12500000), 0, (19208811/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-1620768341258972300701323703297/79689861485025000000000000000), (-16019902811/140137000), (-7077829626977591525701323703297/39844930742512500000000000000), (-16019902811/140137000), (-12534890912696210750701323703297/79689861485025000000000000000)]
    bernstein := [(152764005431005999312645985130287/326409672642662400000000000000000), (401608421781385638058409908336739/816024181606656000000000000000000), (3043933880820887712460581289608197/6120181362049920000000000000000000), (2469037505835640427079123956756107/5100151135041600000000000000000000), (5773600516601194882362440091621503/12750377837604000000000000000000000)]
    reserve := (3537640579/7812500000) }

theorem tilt_000_019_valid : tilt_000_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_019]
  · intro i; fin_cases i <;> norm_num [tilt_000_019]
  · norm_num [tilt_000_019]
  · norm_num [tilt_000_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_019]

def tilt_000_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(32078159/50000000), 0, (15341417/20000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (140137/25000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-1620689843681237165092878703297/79689861485025000000000000000), (-12815922183/112109600), (-7077751136081574083842878703297/39844930742512500000000000000), (-12815922183/112109600), (-12534812428481911002592878703297/79689861485025000000000000000)]
    bernstein := [(153182228298393691232549390130287/326409672642662400000000000000000), (402645388543198317759043693336739/816024181606656000000000000000000), (3051648488686393272135116344608197/6120181362049920000000000000000000), (2475415601598461911685590661756107/5100151135041600000000000000000000), (5789422472671814391898060536621503/12750377837604000000000000000000000)]
    reserve := (45405889507/100000000000) }

theorem tilt_000_020_valid : tilt_000_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_000_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_000_020]
  · intro i; fin_cases i <;> norm_num [tilt_000_020]
  · norm_num [tilt_000_020]
  · norm_num [tilt_000_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_000_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_000_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_000_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_000_020]

def tiltBundle000_row : Alternative → Row
  | .zero => tilt_000_000
  | (.spike 0 false false) => tilt_000_001
  | (.spike 0 false true) => tilt_000_002
  | (.spike 0 true false) => tilt_000_003
  | (.spike 0 true true) => tilt_000_004
  | (.spike 1 false false) => tilt_000_005
  | (.spike 1 false true) => tilt_000_006
  | (.spike 1 true false) => tilt_000_007
  | (.spike 1 true true) => tilt_000_008
  | (.spike 2 false false) => tilt_000_009
  | (.spike 2 false true) => tilt_000_010
  | (.spike 2 true false) => tilt_000_011
  | (.spike 2 true true) => tilt_000_012
  | (.spike 3 false false) => tilt_000_013
  | (.spike 3 false true) => tilt_000_014
  | (.spike 3 true false) => tilt_000_015
  | (.spike 3 true true) => tilt_000_016
  | (.spike 4 false false) => tilt_000_017
  | (.spike 4 false true) => tilt_000_018
  | (.spike 4 true false) => tilt_000_019
  | (.spike 4 true true) => tilt_000_020

def tiltBundle000 : TiltBundle where
  interval := ⟨(-3/8), (-7/20)⟩
  lambda := ![0, 0, 0, 0, 0, 0, 1]
  row := tiltBundle000_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_000_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_000_001_valid | exact tilt_000_002_valid | exact tilt_000_003_valid | exact tilt_000_004_valid | exact tilt_000_005_valid | exact tilt_000_006_valid | exact tilt_000_007_valid | exact tilt_000_008_valid | exact tilt_000_009_valid | exact tilt_000_010_valid | exact tilt_000_011_valid | exact tilt_000_012_valid | exact tilt_000_013_valid | exact tilt_000_014_valid | exact tilt_000_015_valid | exact tilt_000_016_valid | exact tilt_000_017_valid | exact tilt_000_018_valid | exact tilt_000_019_valid | exact tilt_000_020_valid
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
