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

def tilt_057_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_000_valid : tilt_057_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_000]
  · intro i; fin_cases i <;> norm_num [tilt_057_000]
  · norm_num [tilt_057_000]
  · norm_num [tilt_057_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_000]

def tilt_057_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_001_valid : tilt_057_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_001]
  · intro i; fin_cases i <;> norm_num [tilt_057_001]
  · norm_num [tilt_057_001]
  · norm_num [tilt_057_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_001]

def tilt_057_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_002_valid : tilt_057_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_002]
  · intro i; fin_cases i <;> norm_num [tilt_057_002]
  · norm_num [tilt_057_002]
  · norm_num [tilt_057_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_002]

def tilt_057_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_003_valid : tilt_057_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_003]
  · intro i; fin_cases i <;> norm_num [tilt_057_003]
  · norm_num [tilt_057_003]
  · norm_num [tilt_057_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_003]

def tilt_057_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_004_valid : tilt_057_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_004]
  · intro i; fin_cases i <;> norm_num [tilt_057_004]
  · norm_num [tilt_057_004]
  · norm_num [tilt_057_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_004]

def tilt_057_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5569003/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-20880553519836846081133883057/83500795631550000000000000000), (289470511461541/199918000000000), (-52307849842653990072133883057/41750397815775000000000000000), (289470511461541/199918000000000), (-83735146165471134063133883057/83500795631550000000000000000)]
    bernstein := [(27083917850476786175374481582863423/213762036816768000000000000000000000), (22615159222497034395466616765711/170464144192000000000000000000000), (22218215948841882026194725551254549/160321527612576000000000000000000000), (116964670986819603794793060699989/809704684912000000000000000000000), (2007662627860538642430979541825743/13360127301048000000000000000000000)]
    reserve := (15837656591/125000000000) }

theorem tilt_057_005_valid : tilt_057_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_005]
  · intro i; fin_cases i <;> norm_num [tilt_057_005]
  · norm_num [tilt_057_005]
  · norm_num [tilt_057_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_005]

def tilt_057_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (2229829/20000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-2094863640689219095673630801/8358430387912500000000000000), (289470511461541/199918000000000), (-5240736283072919973923630801/4179215193956250000000000000), (289470511461541/199918000000000), (-8386608925456620852173630801/8358430387912500000000000000)]
    bernstein := [(2696329687517963184814324292951839/21397581793056000000000000000000000), (24771034058024902056485069016853/187698085904000000000000000000000), (2212800259830158438717471528393557/16048186344792000000000000000000000), (128160378277271086807925218044247/891565908044000000000000000000000), (200015480769326470008941481887599/1337348862066000000000000000000000)]
    reserve := (7875684603/62500000000) }

theorem tilt_057_006_valid : tilt_057_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_006]
  · intro i; fin_cases i <;> norm_num [tilt_057_006]
  · norm_num [tilt_057_006]
  · norm_num [tilt_057_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_006]

def tilt_057_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3994621/50000000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-64248211816085852472379194109/256813584896850000000000000000), (289470511461541/199731050000000), (-161091554233899718645967694109/128406792448425000000000000000), (289470511461541/199731050000000), (-257934896651713584819556194109/256813584896850000000000000000)]
    bernstein := [(83419012607688402849797349646865651/657442777335936000000000000000000000), (14557314325580881617525341108490163/109573796222656000000000000000000000), (68427018666086482267515306916015313/493082083001952000000000000000000000), (3962324927544760319922148046982523/27393449055664000000000000000000000), (6182707311685077301851860911431491/41090173583496000000000000000000000)]
    reserve := (63442032891/500000000000) }

theorem tilt_057_007_valid : tilt_057_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_007]
  · intro i; fin_cases i <;> norm_num [tilt_057_007]
  · norm_num [tilt_057_007]
  · norm_num [tilt_057_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_007]

def tilt_057_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8004199/100000000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-6294634597361475688417859/25126403958991699218750000), (289470511461541/200104975000000), (-1006932228230600376089439851/804044926687734375000000000), (289470511461541/200104975000000), (-805503921115033154060068363/804044926687734375000000000)]
    bernstein := [(258999392935348185243548467493957/2058355012320600000000000000000000), (45210778358783897951416069433341/343059168720100000000000000000000), (212570786026987162200930507019391/1543766259240450000000000000000000), (12312070262252624128565218588861/85764792180025000000000000000000), (19215683695743679330756254200837/128647188270037500000000000000000)]
    reserve := (125828339321/1000000000000) }

theorem tilt_057_008_valid : tilt_057_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_008]
  · intro i; fin_cases i <;> norm_num [tilt_057_008]
  · norm_num [tilt_057_008]
  · norm_num [tilt_057_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_008]

def tilt_057_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5569003/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-20880554494816517989569440807/83500795631550000000000000000), (289470511461541/199918000000000), (-52307850817633661980569440807/41750397815775000000000000000), (289470511461541/199918000000000), (-83735147140450805971569440807/83500795631550000000000000000)]
    bernstein := [(27083914799413425112320676146765673/213762036816768000000000000000000000), (22615156771552083376382009143961/170464144192000000000000000000000), (22218213626398379414409164261771299/160321527612576000000000000000000000), (116964659167141041248828794096739/809704684912000000000000000000000), (2007662431303661806018462663867993/13360127301048000000000000000000000)]
    reserve := (25340247691/200000000000) }

theorem tilt_057_009_valid : tilt_057_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_009]
  · intro i; fin_cases i <;> norm_num [tilt_057_009]
  · norm_num [tilt_057_009]
  · norm_num [tilt_057_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_009]

def tilt_057_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5574573/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-6982647346313672814079796999/27861437125350000000000000000), (289470511461541/199918000000000), (-17468890428134945241079796999/13930718562675000000000000000), (289470511461541/199918000000000), (-27955133509956217668079796999/27861437125350000000000000000)]
    bernstein := [(8988492700494321516609759383412361/71325279040896000000000000000000000), (27525512844504206837849681408849/208553447488000000000000000000000), (7376554357691538314534046867111043/53493959280672000000000000000000000), (142410749370665299340718568597451/990628875568000000000000000000000), (666765117054576448450344345204601/4457829940056000000000000000000000)]
    reserve := (126021136143/1000000000000) }

theorem tilt_057_010_valid : tilt_057_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_010]
  · intro i; fin_cases i <;> norm_num [tilt_057_010]
  · norm_num [tilt_057_010]
  · norm_num [tilt_057_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_010]

def tilt_057_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(402881/25000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-535867303027277150740277049/2142116372050000000000000000), (289470511461541/199918000000000), (-1342098255357709551740277049/1071058186025000000000000000), (289470511461541/199918000000000), (-2148329207688141952740277049/2142116372050000000000000000)]
    bernstein := [(694178087000529685535356873664311/5483817912448000000000000000000000), (19128808843022287988534657167591/144310997696000000000000000000000), (569504224284897382310664487368893/4112863434336000000000000000000000), (98939233056101739311555379054109/685477239056000000000000000000000), (51463773270357937504025906644551/342738619528000000000000000000000)]
    reserve := (126586640563/1000000000000) }

theorem tilt_057_011_valid : tilt_057_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_011]
  · intro i; fin_cases i <;> norm_num [tilt_057_011]
  · norm_num [tilt_057_011]
  · norm_num [tilt_057_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_011]

def tilt_057_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(1548327/100000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-1609970975991528603436631147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028663832982825806436631147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447356689974123009436631147/6426349116150000000000000000)]
    bernstein := [(2075120595407992269780243517192933/16451453737344000000000000000000000), (19063298781396681916496614567591/144310997696000000000000000000000), (1702869453605916415758455582706679/12338590303008000000000000000000000), (98623310876492895105474801654109/685477239056000000000000000000000), (153913713553011957129821224133653/1028215858584000000000000000000000)]
    reserve := (31534000407/250000000000) }

theorem tilt_057_012_valid : tilt_057_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_012]
  · intro i; fin_cases i <;> norm_num [tilt_057_012]
  · norm_num [tilt_057_012]
  · norm_num [tilt_057_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_012]

def tilt_057_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_013_valid : tilt_057_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_013]
  · intro i; fin_cases i <;> norm_num [tilt_057_013]
  · norm_num [tilt_057_013]
  · norm_num [tilt_057_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_013]

def tilt_057_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_014_valid : tilt_057_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_014]
  · intro i; fin_cases i <;> norm_num [tilt_057_014]
  · norm_num [tilt_057_014]
  · norm_num [tilt_057_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_014]

def tilt_057_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_015_valid : tilt_057_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_015]
  · intro i; fin_cases i <;> norm_num [tilt_057_015]
  · norm_num [tilt_057_015]
  · norm_num [tilt_057_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_015]

def tilt_057_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_016_valid : tilt_057_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_016]
  · intro i; fin_cases i <;> norm_num [tilt_057_016]
  · norm_num [tilt_057_016]
  · norm_num [tilt_057_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_016]

def tilt_057_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_017_valid : tilt_057_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_017]
  · intro i; fin_cases i <;> norm_num [tilt_057_017]
  · norm_num [tilt_057_017]
  · norm_num [tilt_057_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_017]

def tilt_057_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_018_valid : tilt_057_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_018]
  · intro i; fin_cases i <;> norm_num [tilt_057_018]
  · norm_num [tilt_057_018]
  · norm_num [tilt_057_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_018]

def tilt_057_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_019_valid : tilt_057_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_019]
  · intro i; fin_cases i <;> norm_num [tilt_057_019]
  · norm_num [tilt_057_019]
  · norm_num [tilt_057_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_019]

def tilt_057_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(7351/390625), 0, (18818561/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(789963/50000000), 0, (7899629/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (99959/1250000), (5571787/50000000), (1/100000000), (1/100000000), (1/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-1609801722396723737230145147/6426349116150000000000000000), (289470511461541/199918000000000), (-4028494579388020940230145147/3213174558075000000000000000), (289470511461541/199918000000000), (-6447187436379318143230145147/6426349116150000000000000000)]
    bernstein := [(2075650251006684420697038752638933/16451453737344000000000000000000000), (19067979026340645762329472409591/144310997696000000000000000000000), (1703272622946646183671552113604679/12338590303008000000000000000000000), (98645881351120908428708329212109/685477239056000000000000000000000), (153947835246978212961915008219653/1028215858584000000000000000000000)]
    reserve := (31542049173/250000000000) }

theorem tilt_057_020_valid : tilt_057_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_057_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_057_020]
  · intro i; fin_cases i <;> norm_num [tilt_057_020]
  · norm_num [tilt_057_020]
  · norm_num [tilt_057_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_057_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_057_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_057_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_057_020]

def tiltBundle057_row : Alternative → Row
  | .zero => tilt_057_000
  | (.spike 0 false false) => tilt_057_001
  | (.spike 0 false true) => tilt_057_002
  | (.spike 0 true false) => tilt_057_003
  | (.spike 0 true true) => tilt_057_004
  | (.spike 1 false false) => tilt_057_005
  | (.spike 1 false true) => tilt_057_006
  | (.spike 1 true false) => tilt_057_007
  | (.spike 1 true true) => tilt_057_008
  | (.spike 2 false false) => tilt_057_009
  | (.spike 2 false true) => tilt_057_010
  | (.spike 2 true false) => tilt_057_011
  | (.spike 2 true true) => tilt_057_012
  | (.spike 3 false false) => tilt_057_013
  | (.spike 3 false true) => tilt_057_014
  | (.spike 3 true false) => tilt_057_015
  | (.spike 3 true true) => tilt_057_016
  | (.spike 4 false false) => tilt_057_017
  | (.spike 4 false true) => tilt_057_018
  | (.spike 4 true false) => tilt_057_019
  | (.spike 4 true true) => tilt_057_020

def tiltBundle057 : TiltBundle where
  interval := ⟨(13/40), (7/20)⟩
  lambda := ![0, (18818561/50000000), (15382181/50000000), (7899629/25000000), 0, 0, 0]
  row := tiltBundle057_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_057_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_057_001_valid | exact tilt_057_002_valid | exact tilt_057_003_valid | exact tilt_057_004_valid | exact tilt_057_005_valid | exact tilt_057_006_valid | exact tilt_057_007_valid | exact tilt_057_008_valid | exact tilt_057_009_valid | exact tilt_057_010_valid | exact tilt_057_011_valid | exact tilt_057_012_valid | exact tilt_057_013_valid | exact tilt_057_014_valid | exact tilt_057_015_valid | exact tilt_057_016_valid | exact tilt_057_017_valid | exact tilt_057_018_valid | exact tilt_057_019_valid | exact tilt_057_020_valid
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
