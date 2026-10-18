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

def tilt_006_000 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1270743/3125000), 0, (22839737/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := .zero
    polynomial := [(-4772480137531614013351331725771/689108576357850000000000000000), (-40663776/605909), (-56724369442551714013351331725771/344554288178925000000000000000), (-40663776/605909), (-108676258747571814013351331725771/689108576357850000000000000000)]
    bernstein := [(353586790299851965818327511253613269/1764117955476096000000000000000000000), (4514794054274046227571816010600031/20046794948592000000000000000000000), (4808035938383916849516913341661643/20673257290735500000000000000000000), (34894706307835688702221063734563/156615585535875000000000000000000), (21118989715523931743624938344701/107673215055914062500000000000000)]
    reserve := (98069838931/500000000000) }

theorem tilt_006_000_valid : tilt_006_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_000]
  · intro i; fin_cases i <;> norm_num [tilt_006_000]
  · norm_num [tilt_006_000]
  · norm_num [tilt_006_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_000]

def tilt_006_001 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(40572417/100000000), 0, (91399611/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-4773011520652623329651994850771/689108576357850000000000000000), (-40663816611/605909000), (-56724952336313902304651994850771/344554288178925000000000000000), (-40663816611/605909000), (-108676893151975181279651994850771/689108576357850000000000000000)]
    bernstein := [(352099151913616851523299378490488269/1764117955476096000000000000000000000), (4497980037571156839757436461225031/20046794948592000000000000000000000), (4790786143424972835018084724786643/20673257290735500000000000000000000), (34764674326443927363457271859563/156615585535875000000000000000000), (21030017421688835488812870219701/107673215055914062500000000000000)]
    reserve := (97656680033/500000000000) }

theorem tilt_006_001_valid : tilt_006_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_001]
  · intro i; fin_cases i <;> norm_num [tilt_006_001]
  · norm_num [tilt_006_001]
  · norm_num [tilt_006_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_001]

def tilt_006_002 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8151027/20000000), 0, (22829571/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-4771958634448049216885293600771/689108576357850000000000000000), (-10165954179/151477250), (-56723899764007895591885293600771/344554288178925000000000000000), (-10165954179/151477250), (-108675840893567741966885293600771/689108576357850000000000000000)]
    bernstein := [(355074343473411215056245869391738269/1764117955476096000000000000000000000), (4531608051449978814900607684975031/20046794948592000000000000000000000), (4825285973610922892538334583536643/20673257290735500000000000000000000), (35024736733392500741832480609563/156615585535875000000000000000000), (21207954990663314971385381469701/107673215055914062500000000000000)]
    reserve := (98482965237/500000000000) }

theorem tilt_006_002_valid : tilt_006_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_002]
  · intro i; fin_cases i <;> norm_num [tilt_006_002]
  · norm_num [tilt_006_002]
  · norm_num [tilt_006_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_002]

def tilt_006_003 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(40572417/100000000), 0, (91399611/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-4773011520652623329651994850771/689108576357850000000000000000), (-40663816611/605909000), (-56724952336313902304651994850771/344554288178925000000000000000), (-40663816611/605909000), (-108676893151975181279651994850771/689108576357850000000000000000)]
    bernstein := [(352099151913616851523299378490488269/1764117955476096000000000000000000000), (4497980037571156839757436461225031/20046794948592000000000000000000000), (4790786143424972835018084724786643/20673257290735500000000000000000000), (34764674326443927363457271859563/156615585535875000000000000000000), (21030017421688835488812870219701/107673215055914062500000000000000)]
    reserve := (97656680033/500000000000) }

theorem tilt_006_003_valid : tilt_006_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_003]
  · intro i; fin_cases i <;> norm_num [tilt_006_003]
  · norm_num [tilt_006_003]
  · norm_num [tilt_006_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_003]

def tilt_006_004 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8151027/20000000), 0, (22829571/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-4771958634448049216885293600771/689108576357850000000000000000), (-10165954179/151477250), (-56723899764007895591885293600771/344554288178925000000000000000), (-10165954179/151477250), (-108675840893567741966885293600771/689108576357850000000000000000)]
    bernstein := [(355074343473411215056245869391738269/1764117955476096000000000000000000000), (4531608051449978814900607684975031/20046794948592000000000000000000000), (4825285973610922892538334583536643/20673257290735500000000000000000000), (35024736733392500741832480609563/156615585535875000000000000000000), (21207954990663314971385381469701/107673215055914062500000000000000)]
    reserve := (98482965237/500000000000) }

theorem tilt_006_004_valid : tilt_006_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_004]
  · intro i; fin_cases i <;> norm_num [tilt_006_004]
  · norm_num [tilt_006_004]
  · norm_num [tilt_006_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_004]

def tilt_006_005 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(40572417/100000000), 0, (91399611/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-4773011520652623329651994850771/689108576357850000000000000000), (-40663816611/605909000), (-56724952336313902304651994850771/344554288178925000000000000000), (-40663816611/605909000), (-108676893151975181279651994850771/689108576357850000000000000000)]
    bernstein := [(352099151913616851523299378490488269/1764117955476096000000000000000000000), (4497980037571156839757436461225031/20046794948592000000000000000000000), (4790786143424972835018084724786643/20673257290735500000000000000000000), (34764674326443927363457271859563/156615585535875000000000000000000), (21030017421688835488812870219701/107673215055914062500000000000000)]
    reserve := (97656680033/500000000000) }

theorem tilt_006_005_valid : tilt_006_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_005]
  · intro i; fin_cases i <;> norm_num [tilt_006_005]
  · norm_num [tilt_006_005]
  · norm_num [tilt_006_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_005]

def tilt_006_006 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8151027/20000000), 0, (22829571/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-4771958634448049216885293600771/689108576357850000000000000000), (-10165954179/151477250), (-56723899764007895591885293600771/344554288178925000000000000000), (-10165954179/151477250), (-108675840893567741966885293600771/689108576357850000000000000000)]
    bernstein := [(355074343473411215056245869391738269/1764117955476096000000000000000000000), (4531608051449978814900607684975031/20046794948592000000000000000000000), (4825285973610922892538334583536643/20673257290735500000000000000000000), (35024736733392500741832480609563/156615585535875000000000000000000), (21207954990663314971385381469701/107673215055914062500000000000000)]
    reserve := (98482965237/500000000000) }

theorem tilt_006_006_valid : tilt_006_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_006]
  · intro i; fin_cases i <;> norm_num [tilt_006_006]
  · norm_num [tilt_006_006]
  · norm_num [tilt_006_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_006]

def tilt_006_007 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(40572417/100000000), 0, (91399611/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-4773011520652623329651994850771/689108576357850000000000000000), (-40663816611/605909000), (-56724952336313902304651994850771/344554288178925000000000000000), (-40663816611/605909000), (-108676893151975181279651994850771/689108576357850000000000000000)]
    bernstein := [(352099151913616851523299378490488269/1764117955476096000000000000000000000), (4497980037571156839757436461225031/20046794948592000000000000000000000), (4790786143424972835018084724786643/20673257290735500000000000000000000), (34764674326443927363457271859563/156615585535875000000000000000000), (21030017421688835488812870219701/107673215055914062500000000000000)]
    reserve := (97656680033/500000000000) }

theorem tilt_006_007_valid : tilt_006_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_007]
  · intro i; fin_cases i <;> norm_num [tilt_006_007]
  · norm_num [tilt_006_007]
  · norm_num [tilt_006_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_007]

def tilt_006_008 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8151027/20000000), 0, (22829571/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-4771958634448049216885293600771/689108576357850000000000000000), (-10165954179/151477250), (-56723899764007895591885293600771/344554288178925000000000000000), (-10165954179/151477250), (-108675840893567741966885293600771/689108576357850000000000000000)]
    bernstein := [(355074343473411215056245869391738269/1764117955476096000000000000000000000), (4531608051449978814900607684975031/20046794948592000000000000000000000), (4825285973610922892538334583536643/20673257290735500000000000000000000), (35024736733392500741832480609563/156615585535875000000000000000000), (21207954990663314971385381469701/107673215055914062500000000000000)]
    reserve := (98482965237/500000000000) }

theorem tilt_006_008_valid : tilt_006_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_008]
  · intro i; fin_cases i <;> norm_num [tilt_006_008]
  · norm_num [tilt_006_008]
  · norm_num [tilt_006_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_008]

def tilt_006_009 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(40572417/100000000), 0, (91399611/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-4773011520652623329651994850771/689108576357850000000000000000), (-40663816611/605909000), (-56724952336313902304651994850771/344554288178925000000000000000), (-40663816611/605909000), (-108676893151975181279651994850771/689108576357850000000000000000)]
    bernstein := [(352099151913616851523299378490488269/1764117955476096000000000000000000000), (4497980037571156839757436461225031/20046794948592000000000000000000000), (4790786143424972835018084724786643/20673257290735500000000000000000000), (34764674326443927363457271859563/156615585535875000000000000000000), (21030017421688835488812870219701/107673215055914062500000000000000)]
    reserve := (97656680033/500000000000) }

theorem tilt_006_009_valid : tilt_006_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_009]
  · intro i; fin_cases i <;> norm_num [tilt_006_009]
  · norm_num [tilt_006_009]
  · norm_num [tilt_006_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_009]

def tilt_006_010 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8151027/20000000), 0, (22829571/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-4771958634448049216885293600771/689108576357850000000000000000), (-10165954179/151477250), (-56723899764007895591885293600771/344554288178925000000000000000), (-10165954179/151477250), (-108675840893567741966885293600771/689108576357850000000000000000)]
    bernstein := [(355074343473411215056245869391738269/1764117955476096000000000000000000000), (4531608051449978814900607684975031/20046794948592000000000000000000000), (4825285973610922892538334583536643/20673257290735500000000000000000000), (35024736733392500741832480609563/156615585535875000000000000000000), (21207954990663314971385381469701/107673215055914062500000000000000)]
    reserve := (98482965237/500000000000) }

theorem tilt_006_010_valid : tilt_006_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_010]
  · intro i; fin_cases i <;> norm_num [tilt_006_010]
  · norm_num [tilt_006_010]
  · norm_num [tilt_006_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_010]

def tilt_006_011 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(40572417/100000000), 0, (91399611/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-4773011520652623329651994850771/689108576357850000000000000000), (-40663816611/605909000), (-56724952336313902304651994850771/344554288178925000000000000000), (-40663816611/605909000), (-108676893151975181279651994850771/689108576357850000000000000000)]
    bernstein := [(352099151913616851523299378490488269/1764117955476096000000000000000000000), (4497980037571156839757436461225031/20046794948592000000000000000000000), (4790786143424972835018084724786643/20673257290735500000000000000000000), (34764674326443927363457271859563/156615585535875000000000000000000), (21030017421688835488812870219701/107673215055914062500000000000000)]
    reserve := (97656680033/500000000000) }

theorem tilt_006_011_valid : tilt_006_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_011]
  · intro i; fin_cases i <;> norm_num [tilt_006_011]
  · norm_num [tilt_006_011]
  · norm_num [tilt_006_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_011]

def tilt_006_012 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8151027/20000000), 0, (22829571/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-4771958634448049216885293600771/689108576357850000000000000000), (-10165954179/151477250), (-56723899764007895591885293600771/344554288178925000000000000000), (-10165954179/151477250), (-108675840893567741966885293600771/689108576357850000000000000000)]
    bernstein := [(355074343473411215056245869391738269/1764117955476096000000000000000000000), (4531608051449978814900607684975031/20046794948592000000000000000000000), (4825285973610922892538334583536643/20673257290735500000000000000000000), (35024736733392500741832480609563/156615585535875000000000000000000), (21207954990663314971385381469701/107673215055914062500000000000000)]
    reserve := (98482965237/500000000000) }

theorem tilt_006_012_valid : tilt_006_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_012]
  · intro i; fin_cases i <;> norm_num [tilt_006_012]
  · norm_num [tilt_006_012]
  · norm_num [tilt_006_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_012]

def tilt_006_013 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(40572417/100000000), 0, (91399611/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-4773011520652623329651994850771/689108576357850000000000000000), (-40663816611/605909000), (-56724952336313902304651994850771/344554288178925000000000000000), (-40663816611/605909000), (-108676893151975181279651994850771/689108576357850000000000000000)]
    bernstein := [(352099151913616851523299378490488269/1764117955476096000000000000000000000), (4497980037571156839757436461225031/20046794948592000000000000000000000), (4790786143424972835018084724786643/20673257290735500000000000000000000), (34764674326443927363457271859563/156615585535875000000000000000000), (21030017421688835488812870219701/107673215055914062500000000000000)]
    reserve := (97656680033/500000000000) }

theorem tilt_006_013_valid : tilt_006_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_013]
  · intro i; fin_cases i <;> norm_num [tilt_006_013]
  · norm_num [tilt_006_013]
  · norm_num [tilt_006_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_013]

def tilt_006_014 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8151027/20000000), 0, (22829571/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-4771958634448049216885293600771/689108576357850000000000000000), (-10165954179/151477250), (-56723899764007895591885293600771/344554288178925000000000000000), (-10165954179/151477250), (-108675840893567741966885293600771/689108576357850000000000000000)]
    bernstein := [(355074343473411215056245869391738269/1764117955476096000000000000000000000), (4531608051449978814900607684975031/20046794948592000000000000000000000), (4825285973610922892538334583536643/20673257290735500000000000000000000), (35024736733392500741832480609563/156615585535875000000000000000000), (21207954990663314971385381469701/107673215055914062500000000000000)]
    reserve := (98482965237/500000000000) }

theorem tilt_006_014_valid : tilt_006_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_014]
  · intro i; fin_cases i <;> norm_num [tilt_006_014]
  · norm_num [tilt_006_014]
  · norm_num [tilt_006_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_014]

def tilt_006_015 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(40572417/100000000), 0, (91399611/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-4773011520652623329651994850771/689108576357850000000000000000), (-40663816611/605909000), (-56724952336313902304651994850771/344554288178925000000000000000), (-40663816611/605909000), (-108676893151975181279651994850771/689108576357850000000000000000)]
    bernstein := [(352099151913616851523299378490488269/1764117955476096000000000000000000000), (4497980037571156839757436461225031/20046794948592000000000000000000000), (4790786143424972835018084724786643/20673257290735500000000000000000000), (34764674326443927363457271859563/156615585535875000000000000000000), (21030017421688835488812870219701/107673215055914062500000000000000)]
    reserve := (97656680033/500000000000) }

theorem tilt_006_015_valid : tilt_006_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_015]
  · intro i; fin_cases i <;> norm_num [tilt_006_015]
  · norm_num [tilt_006_015]
  · norm_num [tilt_006_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_015]

def tilt_006_016 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8151027/20000000), 0, (22829571/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-4771958634448049216885293600771/689108576357850000000000000000), (-10165954179/151477250), (-56723899764007895591885293600771/344554288178925000000000000000), (-10165954179/151477250), (-108675840893567741966885293600771/689108576357850000000000000000)]
    bernstein := [(355074343473411215056245869391738269/1764117955476096000000000000000000000), (4531608051449978814900607684975031/20046794948592000000000000000000000), (4825285973610922892538334583536643/20673257290735500000000000000000000), (35024736733392500741832480609563/156615585535875000000000000000000), (21207954990663314971385381469701/107673215055914062500000000000000)]
    reserve := (98482965237/500000000000) }

theorem tilt_006_016_valid : tilt_006_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_016]
  · intro i; fin_cases i <;> norm_num [tilt_006_016]
  · norm_num [tilt_006_016]
  · norm_num [tilt_006_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_016]

def tilt_006_017 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(40572417/100000000), 0, (91399611/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-4773011520652623329651994850771/689108576357850000000000000000), (-40663816611/605909000), (-56724952336313902304651994850771/344554288178925000000000000000), (-40663816611/605909000), (-108676893151975181279651994850771/689108576357850000000000000000)]
    bernstein := [(352099151913616851523299378490488269/1764117955476096000000000000000000000), (4497980037571156839757436461225031/20046794948592000000000000000000000), (4790786143424972835018084724786643/20673257290735500000000000000000000), (34764674326443927363457271859563/156615585535875000000000000000000), (21030017421688835488812870219701/107673215055914062500000000000000)]
    reserve := (97656680033/500000000000) }

theorem tilt_006_017_valid : tilt_006_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_017]
  · intro i; fin_cases i <;> norm_num [tilt_006_017]
  · norm_num [tilt_006_017]
  · norm_num [tilt_006_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_017]

def tilt_006_018 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8151027/20000000), 0, (22829571/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-4771958634448049216885293600771/689108576357850000000000000000), (-10165954179/151477250), (-56723899764007895591885293600771/344554288178925000000000000000), (-10165954179/151477250), (-108675840893567741966885293600771/689108576357850000000000000000)]
    bernstein := [(355074343473411215056245869391738269/1764117955476096000000000000000000000), (4531608051449978814900607684975031/20046794948592000000000000000000000), (4825285973610922892538334583536643/20673257290735500000000000000000000), (35024736733392500741832480609563/156615585535875000000000000000000), (21207954990663314971385381469701/107673215055914062500000000000000)]
    reserve := (98482965237/500000000000) }

theorem tilt_006_018_valid : tilt_006_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_018]
  · intro i; fin_cases i <;> norm_num [tilt_006_018]
  · norm_num [tilt_006_018]
  · norm_num [tilt_006_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_018]

def tilt_006_019 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(40572417/100000000), 0, (91399611/100000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-4773011520652623329651994850771/689108576357850000000000000000), (-40663816611/605909000), (-56724952336313902304651994850771/344554288178925000000000000000), (-40663816611/605909000), (-108676893151975181279651994850771/689108576357850000000000000000)]
    bernstein := [(352099151913616851523299378490488269/1764117955476096000000000000000000000), (4497980037571156839757436461225031/20046794948592000000000000000000000), (4790786143424972835018084724786643/20673257290735500000000000000000000), (34764674326443927363457271859563/156615585535875000000000000000000), (21030017421688835488812870219701/107673215055914062500000000000000)]
    reserve := (97656680033/500000000000) }

theorem tilt_006_019_valid : tilt_006_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_019]
  · intro i; fin_cases i <;> norm_num [tilt_006_019]
  · norm_num [tilt_006_019]
  · norm_num [tilt_006_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_019]

def tilt_006_020 : Row :=
  { mode := .tilt
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![0, 0, (49098509/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(8151027/20000000), 0, (22829571/25000000), 0, 0]] i.1) i.2
    mu := ![(22746273/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (605909/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-4771958634448049216885293600771/689108576357850000000000000000), (-10165954179/151477250), (-56723899764007895591885293600771/344554288178925000000000000000), (-10165954179/151477250), (-108675840893567741966885293600771/689108576357850000000000000000)]
    bernstein := [(355074343473411215056245869391738269/1764117955476096000000000000000000000), (4531608051449978814900607684975031/20046794948592000000000000000000000), (4825285973610922892538334583536643/20673257290735500000000000000000000), (35024736733392500741832480609563/156615585535875000000000000000000), (21207954990663314971385381469701/107673215055914062500000000000000)]
    reserve := (98482965237/500000000000) }

theorem tilt_006_020_valid : tilt_006_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_006_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_006_020]
  · intro i; fin_cases i <;> norm_num [tilt_006_020]
  · norm_num [tilt_006_020]
  · norm_num [tilt_006_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_006_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_006_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_006_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_006_020]

def tiltBundle006_row : Alternative → Row
  | .zero => tilt_006_000
  | (.spike 0 false false) => tilt_006_001
  | (.spike 0 false true) => tilt_006_002
  | (.spike 0 true false) => tilt_006_003
  | (.spike 0 true true) => tilt_006_004
  | (.spike 1 false false) => tilt_006_005
  | (.spike 1 false true) => tilt_006_006
  | (.spike 1 true false) => tilt_006_007
  | (.spike 1 true true) => tilt_006_008
  | (.spike 2 false false) => tilt_006_009
  | (.spike 2 false true) => tilt_006_010
  | (.spike 2 true false) => tilt_006_011
  | (.spike 2 true true) => tilt_006_012
  | (.spike 3 false false) => tilt_006_013
  | (.spike 3 false true) => tilt_006_014
  | (.spike 3 true false) => tilt_006_015
  | (.spike 3 true true) => tilt_006_016
  | (.spike 4 false false) => tilt_006_017
  | (.spike 4 false true) => tilt_006_018
  | (.spike 4 true false) => tilt_006_019
  | (.spike 4 true true) => tilt_006_020

def tiltBundle006 : TiltBundle where
  interval := ⟨(-9/40), (-1/5)⟩
  lambda := ![0, 0, 0, 0, 0, 0, 1]
  row := tiltBundle006_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_006_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_006_001_valid | exact tilt_006_002_valid | exact tilt_006_003_valid | exact tilt_006_004_valid | exact tilt_006_005_valid | exact tilt_006_006_valid | exact tilt_006_007_valid | exact tilt_006_008_valid | exact tilt_006_009_valid | exact tilt_006_010_valid | exact tilt_006_011_valid | exact tilt_006_012_valid | exact tilt_006_013_valid | exact tilt_006_014_valid | exact tilt_006_015_valid | exact tilt_006_016_valid | exact tilt_006_017_valid | exact tilt_006_018_valid | exact tilt_006_019_valid | exact tilt_006_020_valid
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
