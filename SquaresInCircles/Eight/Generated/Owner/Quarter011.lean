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

def quarter_011_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_011_000_valid : quarter_011_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_000]
  · intro i; fin_cases i <;> norm_num [quarter_011_000]
  · norm_num [quarter_011_000]
  · norm_num [quarter_011_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_000]

def quarter_011_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_011_001_valid : quarter_011_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_001]
  · intro i; fin_cases i <;> norm_num [quarter_011_001]
  · norm_num [quarter_011_001]
  · norm_num [quarter_011_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_001]

def quarter_011_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(1243607/4000000), (1243607/4000000), 0, 0, 0, 0, (756393/2000000)]
    cone := fun i => (![![(269179/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9876771/100000000), 0, 0]] i.1) i.2
    mu := ![(43683/20000000), (1/100000000), (1571173/20000000), (1/100000000), (1/100000000), (1/100000000), (9876771/100000000)]
    alternative := .zero
    polynomial := [(-85164097015208738094367388111/15063952396387924200000000000), (-1104002088711/29122000000), (-495325370133122935105348988111/7531976198193962100000000000), (-1104002088711/29122000000), (-905486643251037132116330588111/15063952396387924200000000000)]
    bernstein := [(13560145988169784209541094486372929/38563718134753085952000000000000000), (3454967606524006263315975811040399/9640929533688271488000000000000000), (2589538444618496992879879634668807/7230697150266203616000000000000000), (211550163635565640610824975550539/602558095855516968000000000000000), (50820476142515489025771279653209/150639523963879242000000000000000)]
    reserve := (5271325339/15625000000) }

theorem quarter_011_002_valid : quarter_011_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_002]
  · intro i; fin_cases i <;> norm_num [quarter_011_002]
  · norm_num [quarter_011_002]
  · norm_num [quarter_011_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_002]

def quarter_011_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(15722243/50000000), (15722243/50000000), 0, 0, 0, 0, (9277757/25000000)]
    cone := fun i => (![![(1970971/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9691711/100000000), 0, 0]] i.1) i.2
    mu := ![(5431/2500000), (1/100000000), (7945393/100000000), (1/100000000), (1/100000000), (1/100000000), (9691711/100000000)]
    alternative := .zero
    polynomial := [(-1955721723182496371722023882269/418211182816944313000000000000), (-18627739998979/543100000000), (-13319646141900841152250698335269/209105591408472156500000000000), (-18627739998979/543100000000), (-24683570560619185932779372788269/418211182816944313000000000000)]
    bernstein := [(1373549323797071574418854503876011/4182111828169443130000000000000000), (5602267458063742645849756284893007/16728447312677772520000000000000000), (67171118947903957858377812755223477/200741367752133270240000000000000000), (87720984766141713194133598434534083/267655157002844360320000000000000000), (336587108727047934738425643352956771/1070620628011377441280000000000000000)]
    reserve := (15719251989/50000000000) }

theorem quarter_011_003_valid : quarter_011_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_003]
  · intro i; fin_cases i <;> norm_num [quarter_011_003]
  · norm_num [quarter_011_003]
  · norm_num [quarter_011_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_003]

def quarter_011_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(15883043/50000000), (15883043/50000000), 0, 0, 0, 0, (36467829/100000000)]
    cone := fun i => (![![(17911403/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9523737/100000000), 0, 0]] i.1) i.2
    mu := ![(108083/50000000), (1/100000000), (1605331/20000000), (1/100000000), (1/100000000), (1/100000000), (9523737/100000000)]
    alternative := .zero
    polynomial := [(-155535914376581364302739934399/40801333145687842000000000000), (-666923477246639/21616600000000), (-1261774849687475053197339944399/20400666572843921000000000000), (-666923477246639/21616600000000), (-2368013784998368742091939954399/40801333145687842000000000000)]
    bernstein := [(31826152911368799562523300268111441/104451412852960875520000000000000000), (3247461764001337482718584633293891/10445141285296087552000000000000000), (973216382774473456864357496526139/3133542385588826265600000000000000), (31737398239578762469785951192107/104451412852960875520000000000000), (104745744959724344426725167541/360177285699865088000000000000)]
    reserve := (290817186753/1000000000000) }

theorem quarter_011_004_valid : quarter_011_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_004]
  · intro i; fin_cases i <;> norm_num [quarter_011_004]
  · norm_num [quarter_011_004]
  · norm_num [quarter_011_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_004]

def quarter_011_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(16027921/50000000), (16027921/50000000), 0, 0, 0, 0, (35888317/100000000)]
    cone := fun i => (![![(8068369/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4686197/50000000), 0, 0]] i.1) i.2
    mu := ![(26899/12500000), (1/100000000), (809987/10000000), (1/100000000), (1/100000000), (1/100000000), (1874479/20000000)]
    alternative := .zero
    polynomial := [(-249308976320555688379439728539/81681698244143854000000000000), (-296458345096637/10759600000000), (-2458870693338814998521867311039/40840849122071927000000000000), (-296458345096637/10759600000000), (-4668432410357074308664294893539/81681698244143854000000000000)]
    bernstein := [(158467360725862147553343161817/565149047310833152000000000000), (59882477961166992865434788647453/209105147505008266240000000000000), (1794117158660409086765103783051239/6273154425150247987200000000000000), (142491180698193274939976856863269/510012554890264064000000000000000), (1359864013576677398566702660198581/5100125548902640640000000000000000)]
    reserve := (266633438831/1000000000000) }

theorem quarter_011_005_valid : quarter_011_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_005]
  · intro i; fin_cases i <;> norm_num [quarter_011_005]
  · norm_num [quarter_011_005]
  · norm_num [quarter_011_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_005]

def quarter_011_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(16157263/50000000), (16157263/50000000), 0, 0, 0, 0, (8842737/25000000)]
    cone := fun i => (![![(14383163/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9237281/100000000), 0, 0]] i.1) i.2
    mu := ![(107157/50000000), (1/100000000), (4082617/50000000), (1/100000000), (1/100000000), (1/100000000), (4618641/50000000)]
    alternative := .zero
    polynomial := [(-1073004969427794379636910407923/449015030339899562000000000000), (-43549751766571/1785950000000), (-13191704394396328459248495447923/224507515169949781000000000000), (-43549751766571/1785950000000), (-25310403819364862538860080487923/449015030339899562000000000000)]
    bernstein := [(293695664243716199757997968079815597/1149478477670142878720000000000000000), (3412683134902555606997989567577303/13062255428069805440000000000000000), (501933619199321518189450188857437/1924350130028140980000000000000000), (25952651381423405379335118983019/102048870531795355000000000000000), (16963870743970253944280343241013/70158598490609306562500000000000)]
    reserve := (30224147697/125000000000) }

theorem quarter_011_006_valid : quarter_011_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_006]
  · intro i; fin_cases i <;> norm_num [quarter_011_006]
  · norm_num [quarter_011_006]
  · norm_num [quarter_011_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_006]

def quarter_011_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(32542819/100000000), (32542819/100000000), 0, 0, 0, 0, (34914361/100000000)]
    cone := fun i => (![![(12648221/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4559021/50000000), 0, 0]] i.1) i.2
    mu := ![(53383/25000000), (1/100000000), (205573/2500000), (1/100000000), (1/100000000), (1/100000000), (4559021/50000000)]
    alternative := .zero
    polynomial := [(-90960215053305765088035569457/50031168125753639000000000000), (-455502420455197/21353200000000), (-1438330319051835225363089913207/25015584062876819500000000000), (-455502420455197/21353200000000), (-2785700423050364685638144256957/50031168125753639000000000000)]
    bernstein := [(1797713066104871049698429249267/7817370019649006093750000000000), (1841151163513955647035376460193/7817370019649006093750000000000), (29396950181331901304214493790877/125077920314384097500000000000000), (914891027886863081241285855959031/4002493450060291120000000000000000), (27696355731980612426956468442568643/128079790401929315840000000000000000)]
    reserve := (216242981387/1000000000000) }

theorem quarter_011_007_valid : quarter_011_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_007]
  · intro i; fin_cases i <;> norm_num [quarter_011_007]
  · norm_num [quarter_011_007]
  · norm_num [quarter_011_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_007]

def quarter_011_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(32741317/100000000), (32741317/100000000), 0, 0, 0, 0, (17258683/50000000)]
    cone := fun i => (![![(85387/781250), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1802873/20000000), 0, 0]] i.1) i.2
    mu := ![(106421/50000000), (1/100000000), (2068269/25000000), (1/100000000), (1/100000000), (1/100000000), (1802873/20000000)]
    alternative := .zero
    polynomial := [(-28555029835041646918436593/21440751436812750000000000), (-97799062277001/5321050000000), (-604803293141885804213655343/10720375718406375000000000), (-97799062277001/5321050000000), (-1181051556448729961508874093/21440751436812750000000000)]
    bernstein := [(11181929900565376569242244040307/54888323678240640000000000000000), (5738180746281912511740349922903/27444161839120320000000000000000), (1226306797223665934564407107623/5880891822668640000000000000000), (198102899462980494166795430089/980148637111440000000000000000), (651512740832238322029651548867/3430520229890040000000000000000)]
    reserve := (9495830037/50000000000) }

theorem quarter_011_008_valid : quarter_011_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_008]
  · intro i; fin_cases i <;> norm_num [quarter_011_008]
  · norm_num [quarter_011_008]
  · norm_num [quarter_011_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_008]

def quarter_011_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(3291053/10000000), (3291053/10000000), 0, 0, 0, 0, (1708947/5000000)]
    cone := fun i => (![![(4612401/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8925983/100000000), 0, 0]] i.1) i.2
    mu := ![(42449/20000000), (1/100000000), (8315833/100000000), (1/100000000), (1/100000000), (1/100000000), (278937/3125000)]
    alternative := .zero
    polynomial := [(-42912039027279480265267946641/46336199946191496000000000000), (-16463207247479/1061225000000), (-21862248940550329851817762292897/393857699542627716000000000000), (-16463207247479/1061225000000), (-42994993217636908539125969492897/787715399085255432000000000000)]
    bernstein := [(22270790395143174526003724413896943/126034463853640869120000000000000000), (9169427559918624265709926489355701/50413785541456347648000000000000000), (10964408695288199711510884800012469/60496542649747617177600000000000000), (282062381747531830984019564423257/1613241137326603124736000000000000), (21002428028895402611642264564407/129059290986128249978880000000000)]
    reserve := (81367361731/500000000000) }

theorem quarter_011_009_valid : quarter_011_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_009]
  · intro i; fin_cases i <;> norm_num [quarter_011_009]
  · norm_num [quarter_011_009]
  · norm_num [quarter_011_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_009]

def quarter_011_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(7327363/25000000), (7327363/25000000), (59389/2500000), (2981559/100000000), (2981559/100000000), (2981559/100000000), (15030429/50000000)]
    cone := fun i => (![![(166979/2500000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (345167/4000000), 0, 0]] i.1) i.2
    mu := ![(23471/12500000), (1/100000000), (7576039/100000000), (963271/100000000), (1/100000000), (1/100000000), (345167/4000000)]
    alternative := .zero
    polynomial := [(-29540851616803571954611532386527063/59122331028579768530833000000000000), (-4324567412526967751/386559155150000000), (-1433973343955902398756936768360292063/29561165514289884265416500000000000), (-4324567412526967751/386559155150000000), (-2838405836295001225559262004334057063/59122331028579768530833000000000000)]
    bernstein := [(1462112695940072508051882010144324353/9686602715722509276091678720000000000), (1348187973448226081927477653123441523/8648752424752240425081856000000000000), (176785983071116032554909726780799000719/1135148755748731555791993600000000000000), (71211291598246292478318150980874457597/472978648228638148246664000000000000000), (82994045509134086420729187027389100337/591223310285797685308330000000000000000)]
    reserve := (28075363087/200000000000) }

theorem quarter_011_010_valid : quarter_011_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_010]
  · intro i; fin_cases i <;> norm_num [quarter_011_010]
  · norm_num [quarter_011_010]
  · norm_num [quarter_011_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_010]

def quarter_011_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(25110881/100000000), (25110881/100000000), (4709449/100000000), (6523477/100000000), (6523477/100000000), (6523477/100000000), (12749179/50000000)]
    cone := fun i => (![![(1107077/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1672529/20000000), 0, 0]] i.1) i.2
    mu := ![(160011/100000000), (1/100000000), (208851/3125000), (2033009/100000000), (1/100000000), (1/100000000), (4181323/50000000)]
    alternative := .zero
    polynomial := [(-76354278992209870560142734772896391/378772249868297283355236000000000000), (-263139462494730543871/35646354518400000000), (-2583259785460088255859873070863098797/63128708311382880559206000000000000), (-263139462494730543871/35646354518400000000), (-15423204433768319664599095690405696391/378772249868297283355236000000000000)]
    bernstein := [(495115174360034116683235571200029827909/3787722498682972833552360000000000000000), (3715348181391021660576791821915097351/27447264483209948069220000000000000000), (2741788659222842474525191631789294436877/20201186659642521778945920000000000000000), (1775462805037151197796138300420027326801/13467457773095014519297280000000000000000), (119956528362646463010887341181219267521529/969656959662841045389404160000000000000000)]
    reserve := (61855137101/500000000000) }

theorem quarter_011_011_valid : quarter_011_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_011]
  · intro i; fin_cases i <;> norm_num [quarter_011_011]
  · norm_num [quarter_011_011]
  · norm_num [quarter_011_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_011]

def quarter_011_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(21672851/100000000), (21672851/100000000), (6289913/100000000), (594199/6250000), (594199/6250000), (594199/6250000), (10921417/50000000)]
    cone := fun i => (![![(271973/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8187197/100000000), 0, 0]] i.1) i.2
    mu := ![(137541/100000000), (1/100000000), (5925563/100000000), (2880437/100000000), (1/100000000), (1/100000000), (4093599/50000000)]
    alternative := .zero
    polynomial := [(-4393964291851366683641359546933841/152540416118552750991283000000000000), (-52656438080479937849/11642969436900000000), (-7987696499209752777066216718806421523/228810624177829126486924500000000000), (-52656438080479937849/11642969436900000000), (-15962211105543951454081509358972041523/457621248355658252973849000000000000)]
    bernstein := [(44840337467568180046962171020238179698079/390503465263495042537684480000000000000000), (69809981420113754685629328731258929612879/585755197895242563806526720000000000000000), (829366102670190802036588920301053328177/6918368479077668076455040000000000000000), (5708595596459559029923190526463794806477/48812933157936880317210560000000000000000), (8083255855893985337259123924665752860077/73219399736905320475815840000000000000000)]
    reserve := (110397734547/1000000000000) }

theorem quarter_011_012_valid : quarter_011_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_012]
  · intro i; fin_cases i <;> norm_num [quarter_011_012]
  · norm_num [quarter_011_012]
  · norm_num [quarter_011_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_012]

def quarter_011_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(2358567/12500000), (2358567/12500000), (3670879/50000000), (1199983/10000000), (1199983/10000000), (1199983/10000000), (18921679/100000000)]
    cone := fun i => (![![(1417133/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (807529/10000000), 0, 0]] i.1) i.2
    mu := ![(119407/100000000), (1/100000000), (2642771/50000000), (3554601/100000000), (1/100000000), (1/100000000), (8075291/100000000)]
    alternative := .zero
    polynomial := [(1076411820086113360110633086837727869/18116252099899874437834254000000000000), (-74502570097274819473/31556535679700000000), (-273177895267655747735949290024705552131/9058126049949937218917127000000000000), (-74502570097274819473/31556535679700000000), (-547432202355397608832009213136248832131/18116252099899874437834254000000000000)]
    bernstein := [(296160262824021601648049855637506425703069/2898600335983979910053480640000000000000000), (205318458359309586302625877585902922730223/1932400223989319940035653760000000000000000), (532558717850187317657200570111689544043201/4969029147401108417234538240000000000000000), (811324409441859971010760947095407036157823/7729600895957279760142615040000000000000000), (4619957992101168776529485352868595923388669/46377605375743678560855690240000000000000000)]
    reserve := (99616139183/1000000000000) }

theorem quarter_011_013_valid : quarter_011_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_013]
  · intro i; fin_cases i <;> norm_num [quarter_011_013]
  · norm_num [quarter_011_013]
  · norm_num [quarter_011_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_013]

def quarter_011_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(16572213/100000000), (16572213/100000000), (4012883/50000000), (7042069/50000000), (7042069/50000000), (7042069/50000000), (16577393/100000000)]
    cone := fun i => (![![(41437/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2001849/25000000), 0, 0]] i.1) i.2
    mu := ![(13089/12500000), (1/100000000), (4743009/100000000), (819207/20000000), (1/100000000), (1/100000000), (2001849/25000000)]
    alternative := .zero
    polynomial := [(7604940272666392569176370242999/83793264143266037860200000000000), (-216756450442552321/306574048400000000), (-552744118599261265097151905984063/20948316035816509465050000000000), (-216756450442552321/306574048400000000), (-2218581414669711452957783994179251/83793264143266037860200000000000)]
    bernstein := [(19722863946099855132865486541467277549/214510756206761056922112000000000000000), (102720896880723185289154241091824717/1072553781033805284610560000000000000), (19476438170648846655383682914728537/201103833943838490864480000000000000), (63801731572745750144173539006517/670346113146128302881600000000000), (7604940272666392569176370242999/83793264143266037860200000000000)]
    reserve := (90758372411/1000000000000) }

theorem quarter_011_014_valid : quarter_011_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_014]
  · intro i; fin_cases i <;> norm_num [quarter_011_014]
  · norm_num [quarter_011_014]
  · norm_num [quarter_011_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_014]

def quarter_011_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(951377/6250000), (951377/6250000), (261539/3125000), (3010557/20000000), (3010557/20000000), (3010557/20000000), (4007083/25000000)]
    cone := fun i => (![![0, 0, (801291/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8116973/100000000), 0, 0]] i.1) i.2
    mu := ![(25311/25000000), (1/100000000), (2194663/50000000), (43519/1000000), (1/100000000), (1/100000000), (8116973/100000000)]
    alternative := .zero
    polynomial := [(372240953175902611098078579122183/4617014350399692533292000000000000), (4610897955199206613/3703274346200000000), (-58890802788202492122106719751057817/2308507175199846266646000000000000), (4610897955199206613/3703274346200000000), (-3029585808450791970649013284134303/118384983343581859828000000000000)]
    bernstein := [(372240953175902611098078579122183/4617014350399692533292000000000000), (25510600026898254992531997920363/288563396899980783330750000000000), (2072780786099036941460030981030220583/22161668881918524159801600000000000000), (14774753286707283442901702098529971/153900478346656417776400000000000000), (1132507408589729093665809810573105427783/11819556737023212885227520000000000000000)]
    reserve := (80623737533/1000000000000) }

theorem quarter_011_015_valid : quarter_011_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_015]
  · intro i; fin_cases i <;> norm_num [quarter_011_015]
  · norm_num [quarter_011_015]
  · norm_num [quarter_011_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_015]

def quarter_011_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(2988879/20000000), (2988879/20000000), (4411823/50000000), (15670849/100000000), (15670849/100000000), (15670849/100000000), (14275017/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7820497/100000000), 0, 0]] i.1) i.2
    mu := ![(81111/20000000), (1/100000000), (4288223/100000000), (4544253/100000000), (1/100000000), (1/100000000), (7820497/100000000)]
    alternative := .zero
    polynomial := [(10665344729865883400966268783865207/128760525633873825249187218750000000), (31786620451719/53602787500000), (-1388929998481411003321831242442209797/257521051267747650498374437500000000), (31786620451719/53602787500000), (-1410260687941142770123763780009940211/257521051267747650498374437500000000)]
    bernstein := [(62162465618416571478718756146180038824589/659253891245433985275838560000000000000000), (3527659182757927195702413660350715249821/36625216180301888070879920000000000000000), (6906913669608355322371465028367317133881/70634345490582212708125560000000000000000), (903646796468248942880047090987776059621/9156304045075472017719980000000000000000), (4080668572765877685358526515700074680989/41203368202839624079739910000000000000000)]
    reserve := (18858429641/200000000000) }

theorem quarter_011_016_valid : quarter_011_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_016]
  · intro i; fin_cases i <;> norm_num [quarter_011_016]
  · norm_num [quarter_011_016]
  · norm_num [quarter_011_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_016]

def quarter_011_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(1823257/12500000), (1823257/12500000), (9166899/100000000), (802369/5000000), (802369/5000000), (802369/5000000), (13518849/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7721353/100000000), 0, 0]] i.1) i.2
    mu := ![(595319/100000000), (1/100000000), (2076401/50000000), (23349/500000), (1/100000000), (1/100000000), (7721353/100000000)]
    alternative := .zero
    polynomial := [(34157519367151060291068833003548643/445710290851739863864086000000000000), (12299555424507/20764010000000), (-769014047586250986549993949438291357/222855145425869931932043000000000000), (12299555424507/20764010000000), (-1572185614539653033391056731880131357/445710290851739863864086000000000000)]
    bernstein := [(6965830915632414717495932633492473663043/71313646536278378218253760000000000000000), (93738258280796996495143902081207640079/944551609752031499579520000000000000000), (4524176385908520726363969304932421522619/45040197812386344137844480000000000000000), (57791373880985213392128491123233084209361/570509172290227025746030080000000000000000), (116144577566864468661271616299920460358483/1141018344580454051492060160000000000000000)]
    reserve := (19535758593/200000000000) }

theorem quarter_011_017_valid : quarter_011_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_017]
  · intro i; fin_cases i <;> norm_num [quarter_011_017]
  · norm_num [quarter_011_017]
  · norm_num [quarter_011_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_017]

def quarter_011_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(14272503/100000000), (14272503/100000000), (1898103/20000000), (1023483/6250000), (1023483/6250000), (1023483/6250000), (2567459/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (953639/12500000), 0, 0]] i.1) i.2
    mu := ![(192809/25000000), (1/100000000), (502753/12500000), (956499/20000000), (1/100000000), (1/100000000), (953639/12500000)]
    alternative := .zero
    polynomial := [(829242409570877865249818924701393/11789332962948884481119600000000000), (47743444195841/80440480000000), (-14857181110778715278762124217254107/5894666481474442240559800000000000), (47743444195841/80440480000000), (-30543604631128308422774067359209607/11789332962948884481119600000000000)]
    bernstein := [(3043531659062650975375585963899129920233/30180692385149144271666176000000000000000), (771309503748648425775350218219879018061/7545173096287286067916544000000000000000), (584843528336800910811705048078578612011/5658879822215464550937408000000000000000), (49145193895381710645555722208270460029/471573318517955379244784000000000000000), (122353286964386660272636838658504693/1167260689400879651596000000000000000)]
    reserve := (25210916471/250000000000) }

theorem quarter_011_018_valid : quarter_011_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_018]
  · intro i; fin_cases i <;> norm_num [quarter_011_018]
  · norm_num [quarter_011_018]
  · norm_num [quarter_011_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_018]

def quarter_011_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(3499631/25000000), (3499631/25000000), (9796629/100000000), (8331227/50000000), (8331227/50000000), (8331227/50000000), (152737/1250000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (754251/10000000), 0, 0]] i.1) i.2
    mu := ![(935013/100000000), (1/100000000), (486881/12500000), (4884059/100000000), (1/100000000), (1/100000000), (7542511/100000000)]
    alternative := .zero
    polynomial := [(714462791682680666199303119242180683/11180109855965036502132998000000000000), (563896159213/945400000000), (-33230407440493969133507696830379617951/16770164783947554753199497000000000000), (563896159213/945400000000), (-68604203256035980265613303018485777951/33540329567895109506398994000000000000)]
    bernstein := [(34924820708051986291915982935414825421849/335403295678951095063989940000000000000000), (28291814276405957306111052488153299967869/268322636543160876051191952000000000000000), (68615901973323562222082264704857961328663/643974327703586102522860684800000000000000), (3690759529639112628892915231170737324597/34345297477524592134552569856000000000000), (594404690308309589527982751224832918281/5495247596403934741528411176960000000000)]
    reserve := (650799/6250000) }

theorem quarter_011_019_valid : quarter_011_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_019]
  · intro i; fin_cases i <;> norm_num [quarter_011_019]
  · norm_num [quarter_011_019]
  · norm_num [quarter_011_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_019]

def quarter_011_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(6879909/50000000), (6879909/50000000), (10086981/100000000), (16913017/100000000), (16913017/100000000), (16913017/100000000), (11654333/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7460491/100000000), 0, 0]] i.1) i.2
    mu := ![(272057/25000000), (1/100000000), (3771201/100000000), (4975919/100000000), (1/100000000), (1/100000000), (1865123/25000000)]
    alternative := .zero
    polynomial := [(6992450563628672654790324517655351/122074727129491893012665500000000000), (18891390604777/31426675000000), (-99749593690641566373634823955448399/61037363564745946506332750000000000), (18891390604777/31426675000000), (-206491637944911805402059972428552149/122074727129491893012665500000000000)]
    bernstein := [(23659528904534024987603384661690009/219788168053801667595550720000000000), (299307585062174692290335794213531959/2747352100672520844944384000000000000), (1032016772855378085449328315494454245273/9375339043544977383372710400000000000000), (867588947722680030765371775928476362617/7812782536287481152810592000000000000000), (2184670569691900695852665174438093763131/19531956340718702882026480000000000000000)]
    reserve := (107646963501/1000000000000) }

theorem quarter_011_020_valid : quarter_011_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_020]
  · intro i; fin_cases i <;> norm_num [quarter_011_020]
  · norm_num [quarter_011_020]
  · norm_num [quarter_011_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_020]

def quarter_011_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(1355281/10000000), (1355281/10000000), (10363017/100000000), (3426397/20000000), (3426397/20000000), (3426397/20000000), (11135409/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1845539/25000000), 0, 0]] i.1) i.2
    mu := ![(154029/12500000), (1/100000000), (912487/25000000), (79051/1562500), (1/100000000), (1/100000000), (7382157/100000000)]
    alternative := .zero
    polynomial := [(3674596168856121183285010425853557/72906677118035870275432000000000000), (110867664022617/182497400000000), (-50852080517883342643470950979796443/36453338559017935137716000000000000), (110867664022617/182497400000000), (-105378757204622806470226912385446443/72906677118035870275432000000000000)]
    bernstein := [(1300165954058034244189341504111255968517/11665068338885739244069120000000000000000), (2631025477541148710465499356523219751473/23330136677771478488138240000000000000000), (5317038137820492681360139694261246721437/46660273355542956976276480000000000000000), (10731156047639375125536756648378762519753/93320546711085913952552960000000000000000), (21630387711054182856710745640810729947957/186641093422171827905105920000000000000000)]
    reserve := (27864516441/250000000000) }

theorem quarter_011_021_valid : quarter_011_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_021]
  · intro i; fin_cases i <;> norm_num [quarter_011_021]
  · norm_num [quarter_011_021]
  · norm_num [quarter_011_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_021]

def quarter_011_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![(3343629/25000000), (3343629/25000000), (2656491/25000000), (3464641/20000000), (3464641/20000000), (3464641/20000000), (10655387/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1461347/20000000), 0, 0]] i.1) i.2
    mu := ![(1368173/100000000), (1/100000000), (1765431/50000000), (5135093/100000000), (1/100000000), (1/100000000), (1461347/20000000)]
    alternative := .zero
    polynomial := [(87004310403445655816165793730717813/2013960369125865524524397000000000000), (6037847990017/9807950000000), (-1231236539291030859721498230450742187/1006980184562932762262198500000000000), (6037847990017/9807950000000), (-2549477388985507375259162254632202187/2013960369125865524524397000000000000)]
    bernstein := [(595996550286559883263492835515890087307413/5155738544962215742782456320000000000000000), (75373962111240457056068782658550121607859/644467318120276967847807040000000000000000), (7141158198052900183118705311256893540759/60418811073775965735731910000000000000000), (600734873113799341778521262960828214783/5034900922814663811310992500000000000000), (37860396158861265087364436286589480397/314681307675916488206937031250000000000)]
    reserve := (115598676133/1000000000000) }

theorem quarter_011_022_valid : quarter_011_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_022]
  · intro i; fin_cases i <;> norm_num [quarter_011_022]
  · norm_num [quarter_011_022]
  · norm_num [quarter_011_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_022]

def quarter_011_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![0, (17710741/100000000), (718451/5000000), (283001/1250000), (283001/1250000), (283001/1250000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(885537/100000000), 0, (17710741/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2956279/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4550911/100000000), (1693901/25000000), (1/100000000), (1/100000000), (5912559/100000000)]
    alternative := .zero
    polynomial := [(3152886573912270340799369129747/182314766483705889396000000000000), (12724299582191/22754555000000), (-29136409522771686931872655230253/91157383241852944698000000000000), (12724299582191/22754555000000), (-61425705619455644204544679590253/182314766483705889396000000000000)]
    bernstein := [(3426453159706812525719149660247243/28486682263079045218125000000000000), (5110223474341593402199341472707509/41435174200842247590000000000000000), (691182975041700692136225770225929949/5469442994511176681880000000000000000), (686337575330433713661629351989909433/5303702297707807691520000000000000000), (61812302160554709287612714360911092467/466725802198287076853760000000000000000)]
    reserve := (120282633409/1000000000000) }

theorem quarter_011_023_valid : quarter_011_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_023]
  · intro i; fin_cases i <;> norm_num [quarter_011_023]
  · norm_num [quarter_011_023]
  · norm_num [quarter_011_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_023]

def quarter_011_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![0, (18288719/100000000), (7461833/50000000), (11131269/50000000), (11131269/50000000), (11131269/50000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(228609/25000000), 0, (18288719/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5813961/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (567993/12500000), (6772279/100000000), (1/100000000), (1/100000000), (2906981/50000000)]
    alternative := .zero
    polynomial := [(411057043506989487542402845423/44728054621857496428000000000000), (136467366961927/227197200000000), (-7769131180451040614609554474577/22364027310928748214000000000000), (136467366961927/227197200000000), (-15949319404409070716761511794577/44728054621857496428000000000000)]
    bernstein := [(15192238497762004323623176274195101903/114503819831955190855680000000000000000), (518795985633288027538962121289561549/3816793994398506361856000000000000000), (478047633609605861051460577628645677/3435114594958655725670400000000000000), (16305488269606819883221932139390279/114503819831955190855680000000000000), (1667569018541926189457717455087247/11450381983195519085568000000000000)]
    reserve := (207310749/1562500000) }

theorem quarter_011_024_valid : quarter_011_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_024]
  · intro i; fin_cases i <;> norm_num [quarter_011_024]
  · norm_num [quarter_011_024]
  · norm_num [quarter_011_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_024]

def quarter_011_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![0, (9408677/50000000), (15465897/100000000), (21905583/100000000), (21905583/100000000), (21905583/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(235217/25000000), 0, (9408677/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5720741/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (564461/12500000), (1355127/20000000), (1/100000000), (1/100000000), (5720741/100000000)]
    alternative := .zero
    polynomial := [(-2307621423309990874109662057/8751776553315852654000000000000), (145513629388269/225784400000000), (-1649160396749752722895684822057/4375888276657926327000000000000), (145513629388269/225784400000000), (-3296013172076195454917259982057/8751776553315852654000000000000)]
    bernstein := [(326883821528707768582343918445527/2240454797648858279424000000000000), (1115440754329892623286221538901767/7468182658829527598080000000000000), (102711756807711276699429768305050877/672136439294657483827200000000000000), (116702351681515430569670441384459471/746818265882952759808000000000000000), (3578378380898058045890263670230913063/22404547976488582794240000000000000000)]
    reserve := (145900654577/1000000000000) }

theorem quarter_011_025_valid : quarter_011_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_025]
  · intro i; fin_cases i <;> norm_num [quarter_011_025]
  · norm_num [quarter_011_025]
  · norm_num [quarter_011_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_025]

def quarter_011_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![0, (3860579/20000000), (7998389/50000000), (2695847/12500000), (2695847/12500000), (2695847/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(193029/20000000), 0, (3860579/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (281613/5000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (893669/20000000), (678493/10000000), (1/100000000), (1/100000000), (5632261/100000000)]
    alternative := .zero
    polynomial := [(-30688519622984753259636512289/2732088878873053789600000000000), (4411201801033/6383350000000), (-558060767218527509559645432289/1366044439436526894800000000000), (4411201801033/6383350000000), (-1085433014814070265859654352289/2732088878873053789600000000000)]
    bernstein := [(1119137183916955628365291941339915951/6994147529915017701376000000000000000), (286233034279966618088764751561943223/1748536882478754425344000000000000000), (219508777794906875050700021275914137/1311402661859065819008000000000000000), (18695127461884592847450832827616067/109283555154922151584000000000000000), (4774461015370825055897229480614391/27320888788730537896000000000000000)]
    reserve := (160010520099/1000000000000) }

theorem quarter_011_026_valid : quarter_011_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_026]
  · intro i; fin_cases i <;> norm_num [quarter_011_026]
  · norm_num [quarter_011_026]
  · norm_num [quarter_011_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_026]

def quarter_011_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![0, (3950243/20000000), (2064651/12500000), (21243859/100000000), (21243859/100000000), (21243859/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(987561/100000000), 0, (3950243/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5547929/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (2201983/50000000), (3399743/50000000), (1/100000000), (1/100000000), (5547929/100000000)]
    alternative := .zero
    polynomial := [(-794310798909964032513080722673/33226219632360476640800000000000), (8155873160193/11009915000000), (-7356892874869691348862266442673/16613109816180238320400000000000), (8155873160193/11009915000000), (-13919474950829418665211452162673/33226219632360476640800000000000)]
    bernstein := [(8310292927834416022929667745497441/47466028046229252344000000000000000), (33988569651050692182911426602790611/189864112184917009376000000000000000), (2917817354849640706280750325360223001/15948585423533028787584000000000000000), (3974141022798087673164304475998012257/21264780564710705050112000000000000000), (16231558978109516218913507865258258047/85059122258842820200448000000000000000)]
    reserve := (7003150059/40000000000) }

theorem quarter_011_027_valid : quarter_011_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_027]
  · intro i; fin_cases i <;> norm_num [quarter_011_027]
  · norm_num [quarter_011_027]
  · norm_num [quarter_011_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_027]

def quarter_011_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![0, (20167713/100000000), (17027943/100000000), (20934781/100000000), (20934781/100000000), (20934781/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(504193/50000000), 0, (20167713/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1366803/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4324437/100000000), (681869/10000000), (1/100000000), (1/100000000), (1366803/25000000)]
    alternative := .zero
    polynomial := [(-68965333188182650916084497607/1791240607762399404000000000000), (38157185267151/48049300000000), (-430217598101159084628515017607/895620303881199702000000000000), (38157185267151/48049300000000), (-791469863014135518340945537607/1791240607762399404000000000000)]
    bernstein := [(876683831746738474135613989391020873/4585575955871742474240000000000000000), (49775994142256787924033572064348483/254754219770652359680000000000000000), (686443943885029147268585454724808899/3439181966903806855680000000000000000), (564347741062353808976374274436141/2769067606202743040000000000000000), (59617177546417855923131525897691193/286598497241983904640000000000000000)]
    reserve := (191182926677/1000000000000) }

theorem quarter_011_028_valid : quarter_011_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_028]
  · intro i; fin_cases i <;> norm_num [quarter_011_028]
  · norm_num [quarter_011_028]
  · norm_num [quarter_011_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_028]

def quarter_011_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 2, 0, 0, 3]
    lambda := ![0, (20557271/100000000), (8764813/50000000), (20637701/100000000), (20637701/100000000), (20637701/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(128483/12500000), 0, (20557271/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1347407/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (264467/6250000), (1710499/25000000), (1/100000000), (1/100000000), (1347407/25000000)]
    alternative := .zero
    polynomial := [(-577498433198115406966802171/10449038243774355960000000000), (25740090872189/30224800000000), (-2725535541864450390168653771/5224519121887177980000000000), (25740090872189/30224800000000), (-4873572650530785373370505371/10449038243774355960000000000)]
    bernstein := [(348425445690203422960212164954029/1671846119003896953600000000000000), (142377099761428925528062200894251/668738447601558781440000000000000), (174463308779454141758385402683371/802486137121870537728000000000000), (23743627175444063298862574818327/106998151616249405030400000000000), (9690383002825532373642685463941/42799260646499762012160000000000)]
    reserve := (208407605059/1000000000000) }

theorem quarter_011_029_valid : quarter_011_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_011_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_011_029]
  · intro i; fin_cases i <;> norm_num [quarter_011_029]
  · norm_num [quarter_011_029]
  · norm_num [quarter_011_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_011_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_011_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_011_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_011_029]

def quarterTable011 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 2, 0, 0, 3]
  rows := [quarter_011_000, quarter_011_001, quarter_011_002, quarter_011_003, quarter_011_004, quarter_011_005, quarter_011_006, quarter_011_007, quarter_011_008, quarter_011_009, quarter_011_010, quarter_011_011, quarter_011_012, quarter_011_013, quarter_011_014, quarter_011_015, quarter_011_016, quarter_011_017, quarter_011_018, quarter_011_019, quarter_011_020, quarter_011_021, quarter_011_022, quarter_011_023, quarter_011_024, quarter_011_025, quarter_011_026, quarter_011_027, quarter_011_028, quarter_011_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_011_000_valid
    · exact quarter_011_001_valid
    · exact quarter_011_002_valid
    · exact quarter_011_003_valid
    · exact quarter_011_004_valid
    · exact quarter_011_005_valid
    · exact quarter_011_006_valid
    · exact quarter_011_007_valid
    · exact quarter_011_008_valid
    · exact quarter_011_009_valid
    · exact quarter_011_010_valid
    · exact quarter_011_011_valid
    · exact quarter_011_012_valid
    · exact quarter_011_013_valid
    · exact quarter_011_014_valid
    · exact quarter_011_015_valid
    · exact quarter_011_016_valid
    · exact quarter_011_017_valid
    · exact quarter_011_018_valid
    · exact quarter_011_019_valid
    · exact quarter_011_020_valid
    · exact quarter_011_021_valid
    · exact quarter_011_022_valid
    · exact quarter_011_023_valid
    · exact quarter_011_024_valid
    · exact quarter_011_025_valid
    · exact quarter_011_026_valid
    · exact quarter_011_027_valid
    · exact quarter_011_028_valid
    · exact quarter_011_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
