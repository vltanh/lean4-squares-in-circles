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

def tilt_004_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24557813/50000000), 0, (21776787/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (296381/50000000)]
    alternative := .zero
    polynomial := [(-5583609220191214020983092717/526684620157265625000000000), (-24557813/296381), (-44282104701820198395983092717/263342310078632812500000000), (-24557813/296381), (-82980600183449182770983092717/526684620157265625000000000)]
    bernstein := [(391361567361536549283665683988003/1348312627602600000000000000000000), (14150342835909063261746553740451/44943754253420000000000000000000), (13008064294266600512964428103137/40449378828078000000000000000000), (139704507636450410542383157227/449437542534200000000000000000), (38143782513145241685886204787/134831262760260000000000000000)]
    reserve := (70725033891/250000000000) }

theorem tilt_004_000_valid : tilt_004_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_000]
  · intro i; fin_cases i <;> norm_num [tilt_004_000]
  · norm_num [tilt_004_000]
  · norm_num [tilt_004_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_000]

def tilt_004_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(49028519/100000000), 0, (10894533/12500000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-7147483041473400140261456520871/674157451114950000000000000000), (-6139459408/74095375), (-56681607004626207965261456520871/337078725557475000000000000000), (-6139459408/74095375), (-106215730967779015790261456520871/674157451114950000000000000000)]
    bernstein := [(499592472618103914660217356766916489/1725843074854272000000000000000000000), (18067716966961078589921899672117513/57528102495142400000000000000000000), (16610323070684082921050066315299331/51775292245628160000000000000000000), (178380008807197852436648631276001/575281024951424000000000000000000), (48692283923581538214439065468281/172584307485427200000000000000000)]
    reserve := (56427243743/200000000000) }

theorem tilt_004_001_valid : tilt_004_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_001]
  · intro i; fin_cases i <;> norm_num [tilt_004_001]
  · norm_num [tilt_004_001]
  · norm_num [tilt_004_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_001]

def tilt_004_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24601367/50000000), 0, (5441127/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-7146570927737541469662459645871/674157451114950000000000000000), (-6139459496/74095375), (-56680694466103701019662459645871/337078725557475000000000000000), (-6139459496/74095375), (-106214818004469860569662459645871/674157451114950000000000000000)]
    bernstein := [(502294791692075523818370860013791489/1725843074854272000000000000000000000), (18157217884450487552221696118992513/57528102495142400000000000000000000), (16690373069903457266385453130924331/51775292245628160000000000000000000), (179264084264284235197076603151001/575281024951424000000000000000000), (48955953681469788167549162343281/172584307485427200000000000000000)]
    reserve := (17728999523/62500000000) }

theorem tilt_004_002_valid : tilt_004_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_002]
  · intro i; fin_cases i <;> norm_num [tilt_004_002]
  · norm_num [tilt_004_002]
  · norm_num [tilt_004_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_002]

def tilt_004_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(49028519/100000000), 0, (10894533/12500000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-7147483041473400140261456520871/674157451114950000000000000000), (-6139459408/74095375), (-56681607004626207965261456520871/337078725557475000000000000000), (-6139459408/74095375), (-106215730967779015790261456520871/674157451114950000000000000000)]
    bernstein := [(499592472618103914660217356766916489/1725843074854272000000000000000000000), (18067716966961078589921899672117513/57528102495142400000000000000000000), (16610323070684082921050066315299331/51775292245628160000000000000000000), (178380008807197852436648631276001/575281024951424000000000000000000), (48692283923581538214439065468281/172584307485427200000000000000000)]
    reserve := (56427243743/200000000000) }

theorem tilt_004_003_valid : tilt_004_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_003]
  · intro i; fin_cases i <;> norm_num [tilt_004_003]
  · norm_num [tilt_004_003]
  · norm_num [tilt_004_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_003]

def tilt_004_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24601367/50000000), 0, (5441127/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-7146570927737541469662459645871/674157451114950000000000000000), (-6139459496/74095375), (-56680694466103701019662459645871/337078725557475000000000000000), (-6139459496/74095375), (-106214818004469860569662459645871/674157451114950000000000000000)]
    bernstein := [(502294791692075523818370860013791489/1725843074854272000000000000000000000), (18157217884450487552221696118992513/57528102495142400000000000000000000), (16690373069903457266385453130924331/51775292245628160000000000000000000), (179264084264284235197076603151001/575281024951424000000000000000000), (48955953681469788167549162343281/172584307485427200000000000000000)]
    reserve := (17728999523/62500000000) }

theorem tilt_004_004_valid : tilt_004_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_004]
  · intro i; fin_cases i <;> norm_num [tilt_004_004]
  · norm_num [tilt_004_004]
  · norm_num [tilt_004_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_004]

def tilt_004_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(49028519/100000000), 0, (10894533/12500000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-7147483041473400140261456520871/674157451114950000000000000000), (-6139459408/74095375), (-56681607004626207965261456520871/337078725557475000000000000000), (-6139459408/74095375), (-106215730967779015790261456520871/674157451114950000000000000000)]
    bernstein := [(499592472618103914660217356766916489/1725843074854272000000000000000000000), (18067716966961078589921899672117513/57528102495142400000000000000000000), (16610323070684082921050066315299331/51775292245628160000000000000000000), (178380008807197852436648631276001/575281024951424000000000000000000), (48692283923581538214439065468281/172584307485427200000000000000000)]
    reserve := (56427243743/200000000000) }

theorem tilt_004_005_valid : tilt_004_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_005]
  · intro i; fin_cases i <;> norm_num [tilt_004_005]
  · norm_num [tilt_004_005]
  · norm_num [tilt_004_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_005]

def tilt_004_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24601367/50000000), 0, (5441127/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-7146570927737541469662459645871/674157451114950000000000000000), (-6139459496/74095375), (-56680694466103701019662459645871/337078725557475000000000000000), (-6139459496/74095375), (-106214818004469860569662459645871/674157451114950000000000000000)]
    bernstein := [(502294791692075523818370860013791489/1725843074854272000000000000000000000), (18157217884450487552221696118992513/57528102495142400000000000000000000), (16690373069903457266385453130924331/51775292245628160000000000000000000), (179264084264284235197076603151001/575281024951424000000000000000000), (48955953681469788167549162343281/172584307485427200000000000000000)]
    reserve := (17728999523/62500000000) }

theorem tilt_004_006_valid : tilt_004_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_006]
  · intro i; fin_cases i <;> norm_num [tilt_004_006]
  · norm_num [tilt_004_006]
  · norm_num [tilt_004_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_006]

def tilt_004_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(49028519/100000000), 0, (10894533/12500000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-7147483041473400140261456520871/674157451114950000000000000000), (-6139459408/74095375), (-56681607004626207965261456520871/337078725557475000000000000000), (-6139459408/74095375), (-106215730967779015790261456520871/674157451114950000000000000000)]
    bernstein := [(499592472618103914660217356766916489/1725843074854272000000000000000000000), (18067716966961078589921899672117513/57528102495142400000000000000000000), (16610323070684082921050066315299331/51775292245628160000000000000000000), (178380008807197852436648631276001/575281024951424000000000000000000), (48692283923581538214439065468281/172584307485427200000000000000000)]
    reserve := (56427243743/200000000000) }

theorem tilt_004_007_valid : tilt_004_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_007]
  · intro i; fin_cases i <;> norm_num [tilt_004_007]
  · norm_num [tilt_004_007]
  · norm_num [tilt_004_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_007]

def tilt_004_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24601367/50000000), 0, (5441127/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-7146570927737541469662459645871/674157451114950000000000000000), (-6139459496/74095375), (-56680694466103701019662459645871/337078725557475000000000000000), (-6139459496/74095375), (-106214818004469860569662459645871/674157451114950000000000000000)]
    bernstein := [(502294791692075523818370860013791489/1725843074854272000000000000000000000), (18157217884450487552221696118992513/57528102495142400000000000000000000), (16690373069903457266385453130924331/51775292245628160000000000000000000), (179264084264284235197076603151001/575281024951424000000000000000000), (48955953681469788167549162343281/172584307485427200000000000000000)]
    reserve := (17728999523/62500000000) }

theorem tilt_004_008_valid : tilt_004_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_008]
  · intro i; fin_cases i <;> norm_num [tilt_004_008]
  · norm_num [tilt_004_008]
  · norm_num [tilt_004_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_008]

def tilt_004_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(49028519/100000000), 0, (10894533/12500000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-7147483041473400140261456520871/674157451114950000000000000000), (-6139459408/74095375), (-56681607004626207965261456520871/337078725557475000000000000000), (-6139459408/74095375), (-106215730967779015790261456520871/674157451114950000000000000000)]
    bernstein := [(499592472618103914660217356766916489/1725843074854272000000000000000000000), (18067716966961078589921899672117513/57528102495142400000000000000000000), (16610323070684082921050066315299331/51775292245628160000000000000000000), (178380008807197852436648631276001/575281024951424000000000000000000), (48692283923581538214439065468281/172584307485427200000000000000000)]
    reserve := (56427243743/200000000000) }

theorem tilt_004_009_valid : tilt_004_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_009]
  · intro i; fin_cases i <;> norm_num [tilt_004_009]
  · norm_num [tilt_004_009]
  · norm_num [tilt_004_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_009]

def tilt_004_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24601367/50000000), 0, (5441127/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-7146570927737541469662459645871/674157451114950000000000000000), (-6139459496/74095375), (-56680694466103701019662459645871/337078725557475000000000000000), (-6139459496/74095375), (-106214818004469860569662459645871/674157451114950000000000000000)]
    bernstein := [(502294791692075523818370860013791489/1725843074854272000000000000000000000), (18157217884450487552221696118992513/57528102495142400000000000000000000), (16690373069903457266385453130924331/51775292245628160000000000000000000), (179264084264284235197076603151001/575281024951424000000000000000000), (48955953681469788167549162343281/172584307485427200000000000000000)]
    reserve := (17728999523/62500000000) }

theorem tilt_004_010_valid : tilt_004_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_010]
  · intro i; fin_cases i <;> norm_num [tilt_004_010]
  · norm_num [tilt_004_010]
  · norm_num [tilt_004_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_010]

def tilt_004_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(49028519/100000000), 0, (10894533/12500000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-7147483041473400140261456520871/674157451114950000000000000000), (-6139459408/74095375), (-56681607004626207965261456520871/337078725557475000000000000000), (-6139459408/74095375), (-106215730967779015790261456520871/674157451114950000000000000000)]
    bernstein := [(499592472618103914660217356766916489/1725843074854272000000000000000000000), (18067716966961078589921899672117513/57528102495142400000000000000000000), (16610323070684082921050066315299331/51775292245628160000000000000000000), (178380008807197852436648631276001/575281024951424000000000000000000), (48692283923581538214439065468281/172584307485427200000000000000000)]
    reserve := (56427243743/200000000000) }

theorem tilt_004_011_valid : tilt_004_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_011]
  · intro i; fin_cases i <;> norm_num [tilt_004_011]
  · norm_num [tilt_004_011]
  · norm_num [tilt_004_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_011]

def tilt_004_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24601367/50000000), 0, (5441127/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-7146570927737541469662459645871/674157451114950000000000000000), (-6139459496/74095375), (-56680694466103701019662459645871/337078725557475000000000000000), (-6139459496/74095375), (-106214818004469860569662459645871/674157451114950000000000000000)]
    bernstein := [(502294791692075523818370860013791489/1725843074854272000000000000000000000), (18157217884450487552221696118992513/57528102495142400000000000000000000), (16690373069903457266385453130924331/51775292245628160000000000000000000), (179264084264284235197076603151001/575281024951424000000000000000000), (48955953681469788167549162343281/172584307485427200000000000000000)]
    reserve := (17728999523/62500000000) }

theorem tilt_004_012_valid : tilt_004_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_012]
  · intro i; fin_cases i <;> norm_num [tilt_004_012]
  · norm_num [tilt_004_012]
  · norm_num [tilt_004_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_012]

def tilt_004_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(49028519/100000000), 0, (10894533/12500000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-7147483041473400140261456520871/674157451114950000000000000000), (-6139459408/74095375), (-56681607004626207965261456520871/337078725557475000000000000000), (-6139459408/74095375), (-106215730967779015790261456520871/674157451114950000000000000000)]
    bernstein := [(499592472618103914660217356766916489/1725843074854272000000000000000000000), (18067716966961078589921899672117513/57528102495142400000000000000000000), (16610323070684082921050066315299331/51775292245628160000000000000000000), (178380008807197852436648631276001/575281024951424000000000000000000), (48692283923581538214439065468281/172584307485427200000000000000000)]
    reserve := (56427243743/200000000000) }

theorem tilt_004_013_valid : tilt_004_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_013]
  · intro i; fin_cases i <;> norm_num [tilt_004_013]
  · norm_num [tilt_004_013]
  · norm_num [tilt_004_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_013]

def tilt_004_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24601367/50000000), 0, (5441127/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-7146570927737541469662459645871/674157451114950000000000000000), (-6139459496/74095375), (-56680694466103701019662459645871/337078725557475000000000000000), (-6139459496/74095375), (-106214818004469860569662459645871/674157451114950000000000000000)]
    bernstein := [(502294791692075523818370860013791489/1725843074854272000000000000000000000), (18157217884450487552221696118992513/57528102495142400000000000000000000), (16690373069903457266385453130924331/51775292245628160000000000000000000), (179264084264284235197076603151001/575281024951424000000000000000000), (48955953681469788167549162343281/172584307485427200000000000000000)]
    reserve := (17728999523/62500000000) }

theorem tilt_004_014_valid : tilt_004_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_014]
  · intro i; fin_cases i <;> norm_num [tilt_004_014]
  · norm_num [tilt_004_014]
  · norm_num [tilt_004_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_014]

def tilt_004_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(49028519/100000000), 0, (10894533/12500000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-7147483041473400140261456520871/674157451114950000000000000000), (-6139459408/74095375), (-56681607004626207965261456520871/337078725557475000000000000000), (-6139459408/74095375), (-106215730967779015790261456520871/674157451114950000000000000000)]
    bernstein := [(499592472618103914660217356766916489/1725843074854272000000000000000000000), (18067716966961078589921899672117513/57528102495142400000000000000000000), (16610323070684082921050066315299331/51775292245628160000000000000000000), (178380008807197852436648631276001/575281024951424000000000000000000), (48692283923581538214439065468281/172584307485427200000000000000000)]
    reserve := (56427243743/200000000000) }

theorem tilt_004_015_valid : tilt_004_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_015]
  · intro i; fin_cases i <;> norm_num [tilt_004_015]
  · norm_num [tilt_004_015]
  · norm_num [tilt_004_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_015]

def tilt_004_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24601367/50000000), 0, (5441127/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-7146570927737541469662459645871/674157451114950000000000000000), (-6139459496/74095375), (-56680694466103701019662459645871/337078725557475000000000000000), (-6139459496/74095375), (-106214818004469860569662459645871/674157451114950000000000000000)]
    bernstein := [(502294791692075523818370860013791489/1725843074854272000000000000000000000), (18157217884450487552221696118992513/57528102495142400000000000000000000), (16690373069903457266385453130924331/51775292245628160000000000000000000), (179264084264284235197076603151001/575281024951424000000000000000000), (48955953681469788167549162343281/172584307485427200000000000000000)]
    reserve := (17728999523/62500000000) }

theorem tilt_004_016_valid : tilt_004_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_016]
  · intro i; fin_cases i <;> norm_num [tilt_004_016]
  · norm_num [tilt_004_016]
  · norm_num [tilt_004_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_016]

def tilt_004_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(49028519/100000000), 0, (10894533/12500000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-7147483041473400140261456520871/674157451114950000000000000000), (-6139459408/74095375), (-56681607004626207965261456520871/337078725557475000000000000000), (-6139459408/74095375), (-106215730967779015790261456520871/674157451114950000000000000000)]
    bernstein := [(499592472618103914660217356766916489/1725843074854272000000000000000000000), (18067716966961078589921899672117513/57528102495142400000000000000000000), (16610323070684082921050066315299331/51775292245628160000000000000000000), (178380008807197852436648631276001/575281024951424000000000000000000), (48692283923581538214439065468281/172584307485427200000000000000000)]
    reserve := (56427243743/200000000000) }

theorem tilt_004_017_valid : tilt_004_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_017]
  · intro i; fin_cases i <;> norm_num [tilt_004_017]
  · norm_num [tilt_004_017]
  · norm_num [tilt_004_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_017]

def tilt_004_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24601367/50000000), 0, (5441127/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-7146570927737541469662459645871/674157451114950000000000000000), (-6139459496/74095375), (-56680694466103701019662459645871/337078725557475000000000000000), (-6139459496/74095375), (-106214818004469860569662459645871/674157451114950000000000000000)]
    bernstein := [(502294791692075523818370860013791489/1725843074854272000000000000000000000), (18157217884450487552221696118992513/57528102495142400000000000000000000), (16690373069903457266385453130924331/51775292245628160000000000000000000), (179264084264284235197076603151001/575281024951424000000000000000000), (48955953681469788167549162343281/172584307485427200000000000000000)]
    reserve := (17728999523/62500000000) }

theorem tilt_004_018_valid : tilt_004_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_018]
  · intro i; fin_cases i <;> norm_num [tilt_004_018]
  · norm_num [tilt_004_018]
  · norm_num [tilt_004_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_018]

def tilt_004_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(49028519/100000000), 0, (10894533/12500000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-7147483041473400140261456520871/674157451114950000000000000000), (-6139459408/74095375), (-56681607004626207965261456520871/337078725557475000000000000000), (-6139459408/74095375), (-106215730967779015790261456520871/674157451114950000000000000000)]
    bernstein := [(499592472618103914660217356766916489/1725843074854272000000000000000000000), (18067716966961078589921899672117513/57528102495142400000000000000000000), (16610323070684082921050066315299331/51775292245628160000000000000000000), (178380008807197852436648631276001/575281024951424000000000000000000), (48692283923581538214439065468281/172584307485427200000000000000000)]
    reserve := (56427243743/200000000000) }

theorem tilt_004_019_valid : tilt_004_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_019]
  · intro i; fin_cases i <;> norm_num [tilt_004_019]
  · norm_num [tilt_004_019]
  · norm_num [tilt_004_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_019]

def tilt_004_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(24601367/50000000), 0, (5441127/6250000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (592763/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-7146570927737541469662459645871/674157451114950000000000000000), (-6139459496/74095375), (-56680694466103701019662459645871/337078725557475000000000000000), (-6139459496/74095375), (-106214818004469860569662459645871/674157451114950000000000000000)]
    bernstein := [(502294791692075523818370860013791489/1725843074854272000000000000000000000), (18157217884450487552221696118992513/57528102495142400000000000000000000), (16690373069903457266385453130924331/51775292245628160000000000000000000), (179264084264284235197076603151001/575281024951424000000000000000000), (48955953681469788167549162343281/172584307485427200000000000000000)]
    reserve := (17728999523/62500000000) }

theorem tilt_004_020_valid : tilt_004_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_004_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_004_020]
  · intro i; fin_cases i <;> norm_num [tilt_004_020]
  · norm_num [tilt_004_020]
  · norm_num [tilt_004_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_004_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_004_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_004_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_004_020]

def tiltBundle004_row : Alternative → Row
  | .zero => tilt_004_000
  | (.spike 0 false false) => tilt_004_001
  | (.spike 0 false true) => tilt_004_002
  | (.spike 0 true false) => tilt_004_003
  | (.spike 0 true true) => tilt_004_004
  | (.spike 1 false false) => tilt_004_005
  | (.spike 1 false true) => tilt_004_006
  | (.spike 1 true false) => tilt_004_007
  | (.spike 1 true true) => tilt_004_008
  | (.spike 2 false false) => tilt_004_009
  | (.spike 2 false true) => tilt_004_010
  | (.spike 2 true false) => tilt_004_011
  | (.spike 2 true true) => tilt_004_012
  | (.spike 3 false false) => tilt_004_013
  | (.spike 3 false true) => tilt_004_014
  | (.spike 3 true false) => tilt_004_015
  | (.spike 3 true true) => tilt_004_016
  | (.spike 4 false false) => tilt_004_017
  | (.spike 4 false true) => tilt_004_018
  | (.spike 4 true false) => tilt_004_019
  | (.spike 4 true true) => tilt_004_020

def tiltBundle004 : TiltBundle where
  interval := ⟨(-11/40), (-1/4)⟩
  lambda := ![0, 0, 0, 0, 0, 0, 1]
  row := tiltBundle004_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_004_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_004_001_valid | exact tilt_004_002_valid | exact tilt_004_003_valid | exact tilt_004_004_valid | exact tilt_004_005_valid | exact tilt_004_006_valid | exact tilt_004_007_valid | exact tilt_004_008_valid | exact tilt_004_009_valid | exact tilt_004_010_valid | exact tilt_004_011_valid | exact tilt_004_012_valid | exact tilt_004_013_valid | exact tilt_004_014_valid | exact tilt_004_015_valid | exact tilt_004_016_valid | exact tilt_004_017_valid | exact tilt_004_018_valid | exact tilt_004_019_valid | exact tilt_004_020_valid
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
