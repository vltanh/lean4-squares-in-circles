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

def tilt_055_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_000_valid : tilt_055_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_000]
  · intro i; fin_cases i <;> norm_num [tilt_055_000]
  · norm_num [tilt_055_000]
  · norm_num [tilt_055_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_000]

def tilt_055_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_001_valid : tilt_055_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_001]
  · intro i; fin_cases i <;> norm_num [tilt_055_001]
  · norm_num [tilt_055_001]
  · norm_num [tilt_055_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_001]

def tilt_055_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_002_valid : tilt_055_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_002]
  · intro i; fin_cases i <;> norm_num [tilt_055_002]
  · norm_num [tilt_055_002]
  · norm_num [tilt_055_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_002]

def tilt_055_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_003_valid : tilt_055_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_003]
  · intro i; fin_cases i <;> norm_num [tilt_055_003]
  · norm_num [tilt_055_003]
  · norm_num [tilt_055_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_003]

def tilt_055_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_004_valid : tilt_055_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_004]
  · intro i; fin_cases i <;> norm_num [tilt_055_004]
  · norm_num [tilt_055_004]
  · norm_num [tilt_055_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_004]

def tilt_055_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (1110037/10000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-6336615103633180087857191233/29990258141950000000000000000), (566188730817133/432277600000000), (-17698807976112573128357191233/14995129070975000000000000000), (566188730817133/432277600000000), (-29061000848591966168857191233/29990258141950000000000000000)]
    bernstein := [(6244686081018999237828575361260047/76775060843392000000000000000000000), (1666396519329529821399204187257031/19193765210848000000000000000000000), (442635754488327893463692687374963/4798441302712000000000000000000000), (117101831250315070966132301626099/1199610325678000000000000000000000), (30869787251772694169562085960727/299902581419500000000000000000000)]
    reserve := (81337429269/1000000000000) }

theorem tilt_055_005_valid : tilt_055_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_005]
  · intro i; fin_cases i <;> norm_num [tilt_055_005]
  · norm_num [tilt_055_005]
  · norm_num [tilt_055_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_005]

def tilt_055_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (2777861/25000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-1987499719422030424669344897/9381305361043750000000000000), (566188730817133/432277600000000), (-5541727242349022861731844897/4690652680521875000000000000), (566188730817133/432277600000000), (-9095954765276015298794344897/9381305361043750000000000000)]
    bernstein := [(1937618658688483551157884653424623/24016141724272000000000000000000000), (517295046501696166251767442388629/6004035431068000000000000000000000), (412385391361040286266081344641901/4503026573301000000000000000000000), (36379174710029461053199885927541/375252214441750000000000000000000), (9593082779680244929529935153743/93813053610437500000000000000000)]
    reserve := (10084980973/125000000000) }

theorem tilt_055_006_valid : tilt_055_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_006]
  · intro i; fin_cases i <;> norm_num [tilt_055_006]
  · norm_num [tilt_055_006]
  · norm_num [tilt_055_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_006]

def tilt_055_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4319183/50000000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-253448775476489090145675439003/1199211009869950000000000000000), (566188730817133/431918300000000), (-708571209327375182092112689003/599605504934975000000000000000), (566188730817133/431918300000000), (-1163693643178261274038549939003/1199211009869950000000000000000)]
    bernstein := [(250163353426915046254052813313415477/3069980185267072000000000000000000000), (66750543606538452092345688754537421/767495046316768000000000000000000000), (53187773622158004712359492889899299/575621284737576000000000000000000000), (4690064493280680025396261803875409/47968440394798000000000000000000000), (1236296620917402127609935224705357/11992110098699500000000000000000000)]
    reserve := (81486960283/1000000000000) }

theorem tilt_055_007_valid : tilt_055_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_007]
  · intro i; fin_cases i <;> norm_num [tilt_055_007]
  · norm_num [tilt_055_007]
  · norm_num [tilt_055_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_007]

def tilt_055_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8652739/100000000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-127208024970845643006273038707/600603162353337500000000000000), (566188730817133/432636950000000), (-354361212316434405174929413707/300301581176668750000000000000), (566188730817133/432636950000000), (-581514399662023167343585788707/600603162353337500000000000000)]
    bernstein := [(123819157104289926450254102390270413/1537544095624544000000000000000000000), (33059419840701485905347312381064549/384386023906136000000000000000000000), (8785610425001171030380545130656377/96096505976534000000000000000000000), (2455399993500204853606307965043/25368665780500000000000000000000), (613202770533841524082373719372133/6006031623533375000000000000000000)]
    reserve := (80530475487/1000000000000) }

theorem tilt_055_008_valid : tilt_055_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_008]
  · intro i; fin_cases i <;> norm_num [tilt_055_008]
  · norm_num [tilt_055_008]
  · norm_num [tilt_055_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_008]

def tilt_055_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (1110037/10000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-6336616083677583179234759683/29990258141950000000000000000), (566188730817133/432277600000000), (-17698808956156976219734759683/14995129070975000000000000000), (566188730817133/432277600000000), (-29061001828636369260234759683/29990258141950000000000000000)]
    bernstein := [(6244683178283304341259746645743597/76775060843392000000000000000000000), (1666395789007300948526279821296181/19193765210848000000000000000000000), (442635570708114655494691170637913/4798441302712000000000000000000000), (117101784995159378262385203491449/1199610325678000000000000000000000), (30869775607865141040905195206277/299902581419500000000000000000000)]
    reserve := (81337391461/1000000000000) }

theorem tilt_055_009_valid : tilt_055_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_009]
  · intro i; fin_cases i <;> norm_num [tilt_055_009]
  · norm_num [tilt_055_009]
  · norm_num [tilt_055_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_009]

def tilt_055_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (2222289/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-3179649689486755807746515519/15010089928537500000000000000), (566188730817133/432277600000000), (-8866414237963373677371515519/7505044964268750000000000000), (566188730817133/432277600000000), (-14553178786439991546996515519/15010089928537500000000000000)]
    bernstein := [(3101227214960803584025997853689521/38425830217056000000000000000000000), (827933076565499650686021665537333/9606457554264000000000000000000000), (660013667145464462812171332147727/7204843165698000000000000000000000), (58223210699258262346969714862257/600403597141500000000000000000000), (15353093934623659132006117868761/150100899285375000000000000000000)]
    reserve := (3228273479/40000000000) }

theorem tilt_055_010_valid : tilt_055_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_010]
  · intro i; fin_cases i <;> norm_num [tilt_055_010]
  · norm_num [tilt_055_010]
  · norm_num [tilt_055_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_010]

def tilt_055_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(410867/25000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-95134629674210897027182639813/450078224203650000000000000000), (566188730817133/432277600000000), (-265652521414251264210682639813/225039112101825000000000000000), (566188730817133/432277600000000), (-436170413154291631394182639813/450078224203650000000000000000)]
    bernstein := [(93604456796452421900136288413624267/1152200253961344000000000000000000000), (24980096511394949785525944996081091/288050063490336000000000000000000000), (19907165274502448229457473305820029/216037547617752000000000000000000000), (1755610003337559276103026792495839/18003128968146000000000000000000000), (462826262835118952017121681381747/4500782242036500000000000000000000)]
    reserve := (40619873357/500000000000) }

theorem tilt_055_011_valid : tilt_055_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_011]
  · intro i; fin_cases i <;> norm_num [tilt_055_011]
  · norm_num [tilt_055_011]
  · norm_num [tilt_055_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_011]

def tilt_055_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1579019/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-95303836217136741191318839813/450078224203650000000000000000), (566188730817133/432277600000000), (-265821727957177108374818839813/225039112101825000000000000000), (566188730817133/432277600000000), (-436339619697217475558318839813/450078224203650000000000000000)]
    bernstein := [(93103293920146396695186961669424267/1152200253961344000000000000000000000), (24854004980052411195320797709481091/288050063490336000000000000000000000), (19811975257268284855571863680420029/216037547617752000000000000000000000), (1747623962131088209088290561095839/18003128968146000000000000000000000), (460815919898616997503019489181747/4500782242036500000000000000000000)]
    reserve := (16160957021/200000000000) }

theorem tilt_055_012_valid : tilt_055_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_012]
  · intro i; fin_cases i <;> norm_num [tilt_055_012]
  · norm_num [tilt_055_012]
  · norm_num [tilt_055_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_012]

def tilt_055_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_013_valid : tilt_055_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_013]
  · intro i; fin_cases i <;> norm_num [tilt_055_013]
  · norm_num [tilt_055_013]
  · norm_num [tilt_055_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_013]

def tilt_055_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_014_valid : tilt_055_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_014]
  · intro i; fin_cases i <;> norm_num [tilt_055_014]
  · norm_num [tilt_055_014]
  · norm_num [tilt_055_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_014]

def tilt_055_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_015_valid : tilt_055_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_015]
  · intro i; fin_cases i <;> norm_num [tilt_055_015]
  · norm_num [tilt_055_015]
  · norm_num [tilt_055_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_015]

def tilt_055_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_016_valid : tilt_055_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_016]
  · intro i; fin_cases i <;> norm_num [tilt_055_016]
  · norm_num [tilt_055_016]
  · norm_num [tilt_055_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_016]

def tilt_055_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_017_valid : tilt_055_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_017]
  · intro i; fin_cases i <;> norm_num [tilt_055_017]
  · norm_num [tilt_055_017]
  · norm_num [tilt_055_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_017]

def tilt_055_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_018_valid : tilt_055_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_018]
  · intro i; fin_cases i <;> norm_num [tilt_055_018]
  · norm_num [tilt_055_018]
  · norm_num [tilt_055_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_018]

def tilt_055_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_019_valid : tilt_055_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_019]
  · intro i; fin_cases i <;> norm_num [tilt_055_019]
  · norm_num [tilt_055_019]
  · norm_num [tilt_055_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_019]

def tilt_055_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(947157/50000000), 0, (37886279/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1611243/100000000), 0, (8056217/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (540347/6250000), (5552953/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-31763917985607189722503415271/150026074734550000000000000000), (566188730817133/432277600000000), (-88603215232287312117003415271/75013037367275000000000000000), (566188730817133/432277600000000), (-145442512478967434511503415271/150026074734550000000000000000)]
    bernstein := [(31046359884706848705785410510326089/384066751320448000000000000000000000), (8287669531954485060419598432707697/96016687830112000000000000000000000), (6606257446069003411829930993739343/72012515872584000000000000000000000), (582731402857061127698661590704613/6001042989382000000000000000000000), (153653156411140518772629798165249/1500260747345500000000000000000000)]
    reserve := (80835843711/1000000000000) }

theorem tilt_055_020_valid : tilt_055_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_055_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_055_020]
  · intro i; fin_cases i <;> norm_num [tilt_055_020]
  · norm_num [tilt_055_020]
  · norm_num [tilt_055_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_055_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_055_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_055_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_055_020]

def tiltBundle055_row : Alternative → Row
  | .zero => tilt_055_000
  | (.spike 0 false false) => tilt_055_001
  | (.spike 0 false true) => tilt_055_002
  | (.spike 0 true false) => tilt_055_003
  | (.spike 0 true true) => tilt_055_004
  | (.spike 1 false false) => tilt_055_005
  | (.spike 1 false true) => tilt_055_006
  | (.spike 1 true false) => tilt_055_007
  | (.spike 1 true true) => tilt_055_008
  | (.spike 2 false false) => tilt_055_009
  | (.spike 2 false true) => tilt_055_010
  | (.spike 2 true false) => tilt_055_011
  | (.spike 2 true true) => tilt_055_012
  | (.spike 3 false false) => tilt_055_013
  | (.spike 3 false true) => tilt_055_014
  | (.spike 3 true false) => tilt_055_015
  | (.spike 3 true true) => tilt_055_016
  | (.spike 4 false false) => tilt_055_017
  | (.spike 4 false true) => tilt_055_018
  | (.spike 4 true false) => tilt_055_019
  | (.spike 4 true true) => tilt_055_020

def tiltBundle055 : TiltBundle where
  interval := ⟨(11/40), (3/10)⟩
  lambda := ![0, (37886279/100000000), (14944427/50000000), (8056217/25000000), 0, 0, 0]
  row := tiltBundle055_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_055_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_055_001_valid | exact tilt_055_002_valid | exact tilt_055_003_valid | exact tilt_055_004_valid | exact tilt_055_005_valid | exact tilt_055_006_valid | exact tilt_055_007_valid | exact tilt_055_008_valid | exact tilt_055_009_valid | exact tilt_055_010_valid | exact tilt_055_011_valid | exact tilt_055_012_valid | exact tilt_055_013_valid | exact tilt_055_014_valid | exact tilt_055_015_valid | exact tilt_055_016_valid | exact tilt_055_017_valid | exact tilt_055_018_valid | exact tilt_055_019_valid | exact tilt_055_020_valid
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
