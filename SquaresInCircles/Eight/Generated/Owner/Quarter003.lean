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

def quarter_003_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_003_000_valid : quarter_003_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_000]
  · intro i; fin_cases i <;> norm_num [quarter_003_000]
  · norm_num [quarter_003_000]
  · norm_num [quarter_003_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_000]

def quarter_003_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_003_001_valid : quarter_003_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_001]
  · intro i; fin_cases i <;> norm_num [quarter_003_001]
  · norm_num [quarter_003_001]
  · norm_num [quarter_003_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_001]

def quarter_003_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(1243607/4000000), (1243607/4000000), 0, 0, 0, 0, (756393/2000000)]
    cone := fun i => (![![(269179/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9876771/100000000), 0, 0]] i.1) i.2
    mu := ![(43683/20000000), (1/100000000), (1571173/20000000), (1/100000000), (1/100000000), (1/100000000), (9876771/100000000)]
    alternative := .zero
    polynomial := [(-85164097015208738094367388111/15063952396387924200000000000), (-1104002088711/29122000000), (-495325370133122935105348988111/7531976198193962100000000000), (-1104002088711/29122000000), (-905486643251037132116330588111/15063952396387924200000000000)]
    bernstein := [(13560145988169784209541094486372929/38563718134753085952000000000000000), (3454967606524006263315975811040399/9640929533688271488000000000000000), (2589538444618496992879879634668807/7230697150266203616000000000000000), (211550163635565640610824975550539/602558095855516968000000000000000), (50820476142515489025771279653209/150639523963879242000000000000000)]
    reserve := (5271325339/15625000000) }

theorem quarter_003_002_valid : quarter_003_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_002]
  · intro i; fin_cases i <;> norm_num [quarter_003_002]
  · norm_num [quarter_003_002]
  · norm_num [quarter_003_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_002]

def quarter_003_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(15722243/50000000), (15722243/50000000), 0, 0, 0, 0, (9277757/25000000)]
    cone := fun i => (![![(1970971/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9691711/100000000), 0, 0]] i.1) i.2
    mu := ![(5431/2500000), (1/100000000), (7945393/100000000), (1/100000000), (1/100000000), (1/100000000), (9691711/100000000)]
    alternative := .zero
    polynomial := [(-1955721723182496371722023882269/418211182816944313000000000000), (-18627739998979/543100000000), (-13319646141900841152250698335269/209105591408472156500000000000), (-18627739998979/543100000000), (-24683570560619185932779372788269/418211182816944313000000000000)]
    bernstein := [(1373549323797071574418854503876011/4182111828169443130000000000000000), (5602267458063742645849756284893007/16728447312677772520000000000000000), (67171118947903957858377812755223477/200741367752133270240000000000000000), (87720984766141713194133598434534083/267655157002844360320000000000000000), (336587108727047934738425643352956771/1070620628011377441280000000000000000)]
    reserve := (15719251989/50000000000) }

theorem quarter_003_003_valid : quarter_003_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_003]
  · intro i; fin_cases i <;> norm_num [quarter_003_003]
  · norm_num [quarter_003_003]
  · norm_num [quarter_003_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_003]

def quarter_003_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(15883043/50000000), (15883043/50000000), 0, 0, 0, 0, (36467829/100000000)]
    cone := fun i => (![![(17911403/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9523737/100000000), 0, 0]] i.1) i.2
    mu := ![(108083/50000000), (1/100000000), (1605331/20000000), (1/100000000), (1/100000000), (1/100000000), (9523737/100000000)]
    alternative := .zero
    polynomial := [(-155535914376581364302739934399/40801333145687842000000000000), (-666923477246639/21616600000000), (-1261774849687475053197339944399/20400666572843921000000000000), (-666923477246639/21616600000000), (-2368013784998368742091939954399/40801333145687842000000000000)]
    bernstein := [(31826152911368799562523300268111441/104451412852960875520000000000000000), (3247461764001337482718584633293891/10445141285296087552000000000000000), (973216382774473456864357496526139/3133542385588826265600000000000000), (31737398239578762469785951192107/104451412852960875520000000000000), (104745744959724344426725167541/360177285699865088000000000000)]
    reserve := (290817186753/1000000000000) }

theorem quarter_003_004_valid : quarter_003_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_004]
  · intro i; fin_cases i <;> norm_num [quarter_003_004]
  · norm_num [quarter_003_004]
  · norm_num [quarter_003_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_004]

def quarter_003_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(16027921/50000000), (16027921/50000000), 0, 0, 0, 0, (35888317/100000000)]
    cone := fun i => (![![(8068369/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4686197/50000000), 0, 0]] i.1) i.2
    mu := ![(26899/12500000), (1/100000000), (809987/10000000), (1/100000000), (1/100000000), (1/100000000), (1874479/20000000)]
    alternative := .zero
    polynomial := [(-249308976320555688379439728539/81681698244143854000000000000), (-296458345096637/10759600000000), (-2458870693338814998521867311039/40840849122071927000000000000), (-296458345096637/10759600000000), (-4668432410357074308664294893539/81681698244143854000000000000)]
    bernstein := [(158467360725862147553343161817/565149047310833152000000000000), (59882477961166992865434788647453/209105147505008266240000000000000), (1794117158660409086765103783051239/6273154425150247987200000000000000), (142491180698193274939976856863269/510012554890264064000000000000000), (1359864013576677398566702660198581/5100125548902640640000000000000000)]
    reserve := (266633438831/1000000000000) }

theorem quarter_003_005_valid : quarter_003_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_005]
  · intro i; fin_cases i <;> norm_num [quarter_003_005]
  · norm_num [quarter_003_005]
  · norm_num [quarter_003_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_005]

def quarter_003_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(16157263/50000000), (16157263/50000000), 0, 0, 0, 0, (8842737/25000000)]
    cone := fun i => (![![(14383163/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9237281/100000000), 0, 0]] i.1) i.2
    mu := ![(107157/50000000), (1/100000000), (4082617/50000000), (1/100000000), (1/100000000), (1/100000000), (4618641/50000000)]
    alternative := .zero
    polynomial := [(-1073004969427794379636910407923/449015030339899562000000000000), (-43549751766571/1785950000000), (-13191704394396328459248495447923/224507515169949781000000000000), (-43549751766571/1785950000000), (-25310403819364862538860080487923/449015030339899562000000000000)]
    bernstein := [(293695664243716199757997968079815597/1149478477670142878720000000000000000), (3412683134902555606997989567577303/13062255428069805440000000000000000), (501933619199321518189450188857437/1924350130028140980000000000000000), (25952651381423405379335118983019/102048870531795355000000000000000), (16963870743970253944280343241013/70158598490609306562500000000000)]
    reserve := (30224147697/125000000000) }

theorem quarter_003_006_valid : quarter_003_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_006]
  · intro i; fin_cases i <;> norm_num [quarter_003_006]
  · norm_num [quarter_003_006]
  · norm_num [quarter_003_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_006]

def quarter_003_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(32542819/100000000), (32542819/100000000), 0, 0, 0, 0, (34914361/100000000)]
    cone := fun i => (![![(12648221/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4559021/50000000), 0, 0]] i.1) i.2
    mu := ![(53383/25000000), (1/100000000), (205573/2500000), (1/100000000), (1/100000000), (1/100000000), (4559021/50000000)]
    alternative := .zero
    polynomial := [(-90960215053305765088035569457/50031168125753639000000000000), (-455502420455197/21353200000000), (-1438330319051835225363089913207/25015584062876819500000000000), (-455502420455197/21353200000000), (-2785700423050364685638144256957/50031168125753639000000000000)]
    bernstein := [(1797713066104871049698429249267/7817370019649006093750000000000), (1841151163513955647035376460193/7817370019649006093750000000000), (29396950181331901304214493790877/125077920314384097500000000000000), (914891027886863081241285855959031/4002493450060291120000000000000000), (27696355731980612426956468442568643/128079790401929315840000000000000000)]
    reserve := (216242981387/1000000000000) }

theorem quarter_003_007_valid : quarter_003_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_007]
  · intro i; fin_cases i <;> norm_num [quarter_003_007]
  · norm_num [quarter_003_007]
  · norm_num [quarter_003_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_007]

def quarter_003_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(1280139/4000000), (1280139/4000000), (421173/50000000), (421173/50000000), (71107/25000000), (71107/25000000), (33739501/100000000)]
    cone := fun i => (![![(5341617/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8885501/100000000), 0, 0]] i.1) i.2
    mu := ![(104023/50000000), (1/100000000), (255043/3125000), (1/100000000), (224651/100000000), (1/100000000), (4442751/50000000)]
    alternative := .zero
    polynomial := [(-273641560617084086985996183999207991/211832747557460268272712000000000000), (-761203731885499109271/42448540782400000000), (-5838609934983220405831273385629707991/105916373778730134136356000000000000), (-761203731885499109271/42448540782400000000), (-670798724079373924980973563956482823/12460749856321192251336000000000000)]
    bernstein := [(6501422227887072382173631445432973015577/31899519632182252163420160000000000000000), (56732660586472863436288130942694567627461/271145916873549143389071360000000000000000), (84949182929084153874990811646085365868707/406718875310323715083607040000000000000000), (13745848056014714889760883177240132735101/67786479218387285847267840000000000000000), (223274520687911579976401734744849267501/1168732400317022169780480000000000000000)]
    reserve := (23879987479/125000000000) }

theorem quarter_003_008_valid : quarter_003_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_008]
  · intro i; fin_cases i <;> norm_num [quarter_003_008]
  · norm_num [quarter_003_008]
  · norm_num [quarter_003_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_008]

def quarter_003_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(14971581/50000000), (14971581/50000000), (827597/25000000), (827597/25000000), (149731/12500000), (149731/12500000), (15548603/50000000)]
    cone := fun i => (![![(8393051/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4216999/50000000), 0, 0]] i.1) i.2
    mu := ![(48277/25000000), (1/100000000), (7852281/100000000), (1/100000000), (444773/50000000), (1/100000000), (4216999/50000000)]
    alternative := .zero
    polynomial := [(-1145976665978563398912924299652938743/1422027570146701856209998000000000000), (-70703838388039632583/5054460931160000000), (-35856195005498531844571629524549108743/711013785073350928104999000000000000), (-70703838388039632583/5054460931160000000), (-70566413345018500290230334749445278743/1422027570146701856209998000000000000)]
    bernstein := [(40910359916897160146854011051010371592217/227524411223472296993599680000000000000000), (16856850118664864253009019539316898190419/91009764489388918797439872000000000000000), (413085051044213187979184552692288465139/2228810558923810256263833600000000000000), (524867979259646233128273314892481441583/2912312463660445401518075904000000000000), (39588229757927719876918187341937188433/232984997092835632121446072320000000000)]
    reserve := (339835013/2000000000) }

theorem quarter_003_009_valid : quarter_003_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_009]
  · intro i; fin_cases i <;> norm_num [quarter_003_009]
  · norm_num [quarter_003_009]
  · norm_num [quarter_003_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_009]

def quarter_003_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(7015737/25000000), (7015737/25000000), (218047/4000000), (218047/4000000), (1047339/50000000), (1047339/50000000), (28782397/100000000)]
    cone := fun i => (![![(6395101/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4031843/50000000), 0, 0]] i.1) i.2
    mu := ![(89891/50000000), (1/100000000), (943623/12500000), (1/100000000), (295119/20000000), (1/100000000), (8063687/100000000)]
    alternative := .zero
    polynomial := [(-631436024316965104198806599699921/1401790363359962635861312500000000), (-29962165600569549227/2827440503100000000), (-4064302227006484919660657757250537/87611897709997664741332031250000), (-29962165600569549227/2827440503100000000), (-64397399607786793610371717516308671/1401790363359962635861312500000000)]
    bernstein := [(36472790927658793640736690426231601/229669333132896278259517440000000000), (17458867417559460866156291799660037/106328394968933462157184000000000000), (2216702628322899378641785448691349199/13457187488255641304268600000000000000), (133266799825471825607031233724463499/830690585694792673103000000000000000), (2121568130444394219389145446012853379/14017903633599626358613125000000000000)]
    reserve := (1182398699/7812500000) }

theorem quarter_003_010_valid : quarter_003_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_010]
  · intro i; fin_cases i <;> norm_num [quarter_003_010]
  · norm_num [quarter_003_010]
  · norm_num [quarter_003_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_010]

def quarter_003_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(26357953/100000000), (26357953/100000000), (3650953/50000000), (3650953/50000000), (739451/25000000), (739451/25000000), (26764673/100000000)]
    cone := fun i => (![![(464823/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3881079/50000000), 0, 0]] i.1) i.2
    mu := ![(83979/50000000), (1/100000000), (1813631/25000000), (1/100000000), (199067/10000000), (1/100000000), (3881079/50000000)]
    alternative := .zero
    polynomial := [(-291456900604465479720559813341641/1452734883248220961697000000000000), (-25956378649836280563/3384598172200000000), (-6526770908482647265159245067610983/152030394758534751805500000000000), (-25956378649836280563/3384598172200000000), (-558679186024067475486210037494469769/13074613949233988655273000000000000)]
    bernstein := [(18351467841340538632173065707296336431/130746139492339886552730000000000000000), (10887206705028362851890448874579975699/74712079709908506601560000000000000000), (31722177577338716056133646613337864053/216407403297666019121760000000000000000), (398824365029695936596889818046993636379/2789250975836584246458240000000000000000), (501858744277411192203842284580012951279/3719001301115445661944320000000000000000)]
    reserve := (134944492793/1000000000000) }

theorem quarter_003_011_valid : quarter_003_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_011]
  · intro i; fin_cases i <;> norm_num [quarter_003_011]
  · norm_num [quarter_003_011]
  · norm_num [quarter_003_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_011]

def quarter_003_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(4963533/20000000), (4963533/20000000), (8898991/100000000), (8898991/100000000), (944297/25000000), (944297/25000000), (25012313/100000000)]
    cone := fun i => (![![(1557187/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7518507/100000000), 0, 0]] i.1) i.2
    mu := ![(157499/100000000), (1/100000000), (6970459/100000000), (1/100000000), (1221383/50000000), (1/100000000), (7518507/100000000)]
    alternative := .zero
    polynomial := [(-91595560019869597345211534819358571/2520360506615521902581105250000000000), (-562690374705393323503/109784032204100000000), (-50384286164619483515387225441477339821/1260180253307760951290552625000000000), (-562690374705393323503/109784032204100000000), (-100676976769219097433429239348135321071/2520360506615521902581105250000000000)]
    bernstein := [(800487286217157355468958699029725766488449/6452122896935736070607629440000000000000000), (417437697074563225627153835905341288636583/3226061448467868035303814720000000000000000), (1281329917677900072438571708063355140031/9815602784384994022222560000000000000000), (102852069130851322515724813947257475087287/806515362116967008825953680000000000000000), (48538414391761479078519111792751433612129/403257681058483504412976840000000000000000)]
    reserve := (1880714889/15625000000) }

theorem quarter_003_012_valid : quarter_003_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_012]
  · intro i; fin_cases i <;> norm_num [quarter_003_012]
  · norm_num [quarter_003_012]
  · norm_num [quarter_003_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_012]

def quarter_003_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(4685747/20000000), (4685747/20000000), (5138007/50000000), (5138007/50000000), (4547891/100000000), (4547891/100000000), (23494721/100000000)]
    cone := fun i => (![![(175963/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3661727/50000000), 0, 0]] i.1) i.2
    mu := ![(74133/50000000), (1/100000000), (837171/12500000), (1/100000000), (1419737/50000000), (1/100000000), (3661727/50000000)]
    alternative := .zero
    polynomial := [(835442005295784449568470973293377/14339601953913589991629200000000000), (-1598423065071689627/551662202160000000), (-268709809182593527112836534508561623/7169800976956794995814600000000000), (-1598423065071689627/551662202160000000), (-179418353456827612891747179996805541/4779867317971196663876400000000000)]
    bernstein := [(27931531634617705627043479820413100553/254926256958463822073408000000000000000), (5922128891507081759131343294355032593/51558119384857851655296000000000000000), (3200376006470881849463091972230210000531/27532035751514092783928064000000000000000), (23453024122951487661358833474357354193/206232477539431406621184000000000000000), (3939089396341253176055883022544412109777/36709381002018790378570752000000000000000)]
    reserve := (107304707647/1000000000000) }

theorem quarter_003_013_valid : quarter_003_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_013]
  · intro i; fin_cases i <;> norm_num [quarter_003_013]
  · norm_num [quarter_003_013]
  · norm_num [quarter_003_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_013]

def quarter_003_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(4435357/20000000), (4435357/20000000), (2865713/25000000), (2865713/25000000), (1053701/20000000), (1053701/20000000), (22183717/100000000)]
    cone := fun i => (![![(277253/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (716927/10000000), 0, 0]] i.1) i.2
    mu := ![(35031/25000000), (1/100000000), (6435219/100000000), (1/100000000), (1593859/50000000), (1/100000000), (7169271/100000000)]
    alternative := .zero
    polynomial := [(2733088119525842602947230732679941/28621886347725747937116900000000000), (-4640762725223706271/5009603484200000000), (-84343241171707843976838761512313239/2385157195643812328093075000000000), (-4640762725223706271/5009603484200000000), (-1014851982180019970325012368880438809/28621886347725747937116900000000000)]
    bernstein := [(2358097433727074694471500658245679570797/24424009683392638239673088000000000000000), (37299870139941974585866003769219834803/366360145250889573595096320000000000000), (789090918965501636205850384833578187/7632503026060199449897840000000000000), (23190432468444434174760872510785003/228975090781805983496935200000000000), (2733088119525842602947230732679941/28621886347725747937116900000000000)]
    reserve := (95489447701/1000000000000) }

theorem quarter_003_014_valid : quarter_003_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_014]
  · intro i; fin_cases i <;> norm_num [quarter_003_014]
  · norm_num [quarter_003_014]
  · norm_num [quarter_003_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_014]

def quarter_003_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(21088977/100000000), (21088977/100000000), (12152307/100000000), (12152307/100000000), (1131139/20000000), (1131139/20000000), (5551511/25000000)]
    cone := fun i => (![![0, 0, (1110129/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3638109/50000000), 0, 0]] i.1) i.2
    mu := ![(28053/20000000), (1/100000000), (6150169/100000000), (1/100000000), (1693453/50000000), (1/100000000), (3638109/50000000)]
    alternative := .zero
    polynomial := [(194010403417852685979517267386979/2394044649833430420474750000000000), (50021662597403949179/28755115159500000000), (-42379619823074783108679921208698521/1197022324916715210237375000000000), (50021662597403949179/28755115159500000000), (-84953250049567418903339359684784021/2394044649833430420474750000000000)]
    bernstein := [(194010403417852685979517267386979/2394044649833430420474750000000000), (1760314168260343882700420375744807/19152357198667443363798000000000000), (1138747445683644983430141646227570679/11491414319200466018278800000000000000), (3144012952508941133411800671035472007/30643771517867909382076800000000000000), (627669085192976686083057805983153368779/6128754303573581876415360000000000000000)]
    reserve := (81038757331/1000000000000) }

theorem quarter_003_015_valid : quarter_003_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_015]
  · intro i; fin_cases i <;> norm_num [quarter_003_015]
  · norm_num [quarter_003_015]
  · norm_num [quarter_003_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_015]

def quarter_003_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(1312471/6250000), (1312471/6250000), (6492223/50000000), (6492223/50000000), (1198247/20000000), (1198247/20000000), (626549/3125000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (212521/3125000), 0, 0]] i.1) i.2
    mu := ![(285379/50000000), (1/100000000), (3048767/50000000), (1/100000000), (3613331/100000000), (1/100000000), (6800673/100000000)]
    alternative := .zero
    polynomial := [(897436593837598234377151923441483827/10689955346524594724991379500000000000), (3232332414673/3810958750000), (-40775754715485589762246704770891396173/5344977673262297362495689750000000000), (3232332414673/3810958750000), (-82448946024808777758870561465224276173/10689955346524594724991379500000000000)]
    bernstein := [(2747515534233767362368330052568436441090227/27366285687102962495977931520000000000000000), (27720920536938063182626213471344243479777/268296918501009436235077760000000000000000), (2164428056015567695223811503940083170911881/20524714265327221871983448640000000000000000), (121776428908486983151382223066226244985409/1140261903629290103999080480000000000000000), (183603145186321651756725472250975239105427/1710392855443935155998620720000000000000000)]
    reserve := (10039782401/100000000000) }

theorem quarter_003_016_valid : quarter_003_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_016]
  · intro i; fin_cases i <;> norm_num [quarter_003_016]
  · norm_num [quarter_003_016]
  · norm_num [quarter_003_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_016]

def quarter_003_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(10322187/50000000), (10322187/50000000), (6793811/50000000), (6793811/50000000), (194049/3125000), (194049/3125000), (19116871/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6614113/100000000), 0, 0]] i.1) i.2
    mu := ![(168849/20000000), (1/100000000), (371997/6250000), (1/100000000), (3774859/100000000), (1/100000000), (6614113/100000000)]
    alternative := .zero
    polynomial := [(99050435541346898138055379107161/1320060495684906876045750000000000), (42339445625251/49599600000000), (-3258884800036922749115222424827339/660030247842453438022875000000000), (42339445625251/49599600000000), (-2205606678538397465456166742920613/440020165228302292015250000000000)]
    bernstein := [(22271572125646428422068056724678464461/211209679309585100167320000000000000000), (258542890051039466151950820467313833/2400109992154376138265000000000000000), (277494118988815958659466516048640526897/2534516151715021202007840000000000000000), (8505329479838891089614880043890239851/76803519748940036424480000000000000000), (376746822478192965918788504112385312841/3379354868953361602677120000000000000000)]
    reserve := (5272384343/50000000000) }

theorem quarter_003_017_valid : quarter_003_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_017]
  · intro i; fin_cases i <;> norm_num [quarter_003_017]
  · norm_num [quarter_003_017]
  · norm_num [quarter_003_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_017]

def quarter_003_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(20322107/100000000), (20322107/100000000), (14149107/100000000), (14149107/100000000), (6402357/100000000), (6402357/100000000), (2281607/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6438819/100000000), 0, 0]] i.1) i.2
    mu := ![(220121/20000000), (1/100000000), (5802877/100000000), (1/100000000), (1962087/50000000), (1/100000000), (321941/5000000)]
    alternative := .zero
    polynomial := [(17717301997901440682368527058517363/268954079854205214215813000000000000), (499377822941873/580287700000000), (-490167300035180921490854798552568637/134477039927102607107906500000000000), (499377822941873/580287700000000), (-998051902068263283664078124163654637/268954079854205214215813000000000000)]
    bernstein := [(75847702298168325683046499388779176108803/688522444426765348392481280000000000000000), (19308425662081027075092722201172769469001/172130611106691337098120320000000000000000), (14693097223124349137651432471623556064701/129097958330018502823590240000000000000000), (112550383954434258643740930226072503199/978014835833473506239320000000000000000), (311909688745834918715164110064559947963/2689540798542052142158130000000000000000)]
    reserve := (22032020281/200000000000) }

theorem quarter_003_018_valid : quarter_003_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_018]
  · intro i; fin_cases i <;> norm_num [quarter_003_018]
  · norm_num [quarter_003_018]
  · norm_num [quarter_003_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_018]

def quarter_003_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(4006223/20000000), (4006223/20000000), (917017/6250000), (917017/6250000), (3285971/50000000), (3285971/50000000), (17449343/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3136633/50000000), 0, 0]] i.1) i.2
    mu := ![(1341231/100000000), (1/100000000), (5650799/100000000), (1/100000000), (2031153/50000000), (1/100000000), (6273267/100000000)]
    alternative := .zero
    polynomial := [(2622436577253150682553347947963129/46451031647890562353661000000000000), (245553713846697/282539950000000), (-201626347978072684662515847815985613/69676547471835843530491500000000000), (245553713846697/282539950000000), (-411120005687904821372691739475860613/139353094943671687060983000000000000)]
    bernstein := [(14568975016797780184693845815491880617/126684631766974260964530000000000000000), (1692590142453639522924875217729144611/14478243630511344110232000000000000000), (317101391048531993134278480980294871869/2675579422918496391570873600000000000000), (1315387488172412537576519554540308347/10976736094024600580803584000000000000), (212255016844359433117938295420180031/1756277775043936092928573440000000000)]
    reserve := (184003061/1600000000) }

theorem quarter_003_019_valid : quarter_003_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_019]
  · intro i; fin_cases i <;> norm_num [quarter_003_019]
  · norm_num [quarter_003_019]
  · norm_num [quarter_003_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_019]

def quarter_003_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(1235617/6250000), (1235617/6250000), (15160159/100000000), (15160159/100000000), (6720471/100000000), (6720471/100000000), (3339799/20000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3058049/50000000), 0, 0]] i.1) i.2
    mu := ![(156761/10000000), (1/100000000), (2748081/50000000), (1/100000000), (4190187/100000000), (1/100000000), (6116099/100000000)]
    alternative := .zero
    polynomial := [(1953923828787447684482959336247773/41818797409872113292325125000000000), (17259827373001/19629150000000), (-50348569502878854573363204572607227/20909398704936056646162562500000000), (17259827373001/19629150000000), (-102651062834545156831209368481462227/41818797409872113292325125000000000)]
    bernstein := [(274359605230612649546590967437023879/2283863922544482347271516160000000000), (3482907279806215737598485532067345829/28548299031806029340893952000000000000), (5156671311156810026011271984510857427/41710177156859458452604800000000000000), (334603078721240704351144811947769620091/2676403034231815250708808000000000000000), (844165903401816991683348845200446655213/6691007585579538126772020000000000000000)]
    reserve := (120129576251/1000000000000) }

theorem quarter_003_020_valid : quarter_003_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_020]
  · intro i; fin_cases i <;> norm_num [quarter_003_020]
  · norm_num [quarter_003_020]
  · norm_num [quarter_003_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_020]

def quarter_003_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![(4884239/25000000), (4884239/25000000), (7807761/50000000), (7807761/50000000), (6849909/100000000), (6849909/100000000), (1999403/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5966109/100000000), 0, 0]] i.1) i.2
    mu := ![(1781123/100000000), (1/100000000), (533937/10000000), (1/100000000), (4308663/100000000), (1/100000000), (5966109/100000000)]
    alternative := .zero
    polynomial := [(49717249345350437413011456766020473/1358141858660207681412556500000000000), (19828691857033/22247375000000), (-1407052110131363700814615266116279527/679070929330103840706278250000000000), (19828691857033/22247375000000), (-2863821469608077839042241988998579527/1358141858660207681412556500000000000)]
    bernstein := [(27297386209859195871384178849174696303913/217302697385633229026009040000000000000000), (55413378198690777685676106074354259068197/434605394771266458052018080000000000000000), (336860703745840858772051734184072850073379/2607632368627598748312108480000000000000000), (227137419760945674752575865883440031041117/1738421579085065832208072320000000000000000), (458680787299726671765842544145489598482073/3476843158170131664416144640000000000000000)]
    reserve := (6280958897/50000000000) }

theorem quarter_003_021_valid : quarter_003_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_021]
  · intro i; fin_cases i <;> norm_num [quarter_003_021]
  · norm_num [quarter_003_021]
  · norm_num [quarter_003_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_021]

def quarter_003_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![0, (29739637/100000000), (196393/800000), (196393/800000), (165329/1562500), (165329/1562500), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(743491/50000000), 0, (29739637/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (276329/10000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1591069/20000000), (1/100000000), (6754729/100000000), (1/100000000), (2763291/100000000)]
    alternative := .zero
    polynomial := [(-693813447920694318220290107357/39597001777056020788000000000000), (5840656529341/6364276000000), (-12469818039300704187216029667357/19798500888528010394000000000000), (5840656529341/6364276000000), (-24245822630680714056211769227357/39597001777056020788000000000000)]
    bernstein := [(764051527550954973660109768480565779/5962842620544906659840000000000000000), (99086345093659596594132361827648797/745355327568113332480000000000000000), (54530698302843476127298832652562983/395970017770560207880000000000000000), (14102946423482668421730137309182313/98992504442640051970000000000000000), (910680387828331655160383180076667/6187031527665003248125000000000000)]
    reserve := (128135450853/1000000000000) }

theorem quarter_003_022_valid : quarter_003_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_022]
  · intro i; fin_cases i <;> norm_num [quarter_003_022]
  · norm_num [quarter_003_022]
  · norm_num [quarter_003_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_022]

def quarter_003_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![0, (3732323/12500000), (24858847/100000000), (24858847/100000000), (10211861/100000000), (10211861/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1492929/100000000), 0, (3732323/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2666873/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3870493/50000000), (1/100000000), (271627/4000000), (1/100000000), (1333437/50000000)]
    alternative := .zero
    polynomial := [(-17513741817570612647708274119/700941428699842753500000000000), (92781246411581/96762325000000), (-226804927096713269069418714119/350470714349921376750000000000), (92781246411581/96762325000000), (-436096112375855925491129154119/700941428699842753500000000000)]
    bernstein := [(16162729814832018789541338303889/109522098234350430234375000000000), (267312364556601006654502261008677/1752353571749606883750000000000000), (473109744940763685266697373106461/3004034694427897515000000000000000), (36430309570028747965884224076200849/224301257183949681120000000000000000), (300245424214740438465522268416340441/1794410057471597448960000000000000000)]
    reserve := (36893764079/250000000000) }

theorem quarter_003_023_valid : quarter_003_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_023]
  · intro i; fin_cases i <;> norm_num [quarter_003_023]
  · norm_num [quarter_003_023]
  · norm_num [quarter_003_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_023]

def quarter_003_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![0, (29953703/100000000), (25171881/100000000), (25171881/100000000), (9851267/100000000), (9851267/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(299537/20000000), 0, (29953703/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2572703/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7516771/100000000), (1/100000000), (273207/4000000), (1/100000000), (2572703/100000000)]
    alternative := .zero
    polynomial := [(-14084687125850369313817804177/414383648803534564000000000000), (753991047425343/751677100000000), (-138207934569024166116722724177/207191824401767282000000000000), (753991047425343/751677100000000), (-262331182012197962919627644177/414383648803534564000000000000)]
    bernstein := [(177938918688241401901710897165956303/1060822140937048483840000000000000000), (1078929914764748853306389237981191/6240130240806167552000000000000000), (1888771112778063434803200688371759/10608221409370484838400000000000000), (194317791603790014940382465679479/1060822140937048483840000000000000), (1174950939817222382519295968991/6240130240806167552000000000000)]
    reserve := (83868403487/500000000000) }

theorem quarter_003_024_valid : quarter_003_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_024]
  · intro i; fin_cases i <;> norm_num [quarter_003_024]
  · norm_num [quarter_003_024]
  · norm_num [quarter_003_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_024]

def quarter_003_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![0, (15015269/50000000), (25486643/100000000), (25486643/100000000), (9498089/100000000), (9498089/100000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1501527/100000000), 0, (15015269/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (620117/25000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7284229/100000000), (1/100000000), (687263/10000000), (1/100000000), (2480469/100000000)]
    alternative := .zero
    polynomial := [(-555262639442624994516519953971/12417676965487241463000000000000), (382688800551967/364211450000000), (-4284357839280517927214490893971/6208838482743620731500000000000), (382688800551967/364211450000000), (-8013453039118410859912461833971/12417676965487241463000000000000)]
    bernstein := [(599980504385136028529676907982381/3178925303164733814528000000000000), (108265742797133013719910692847479/557706193537672599040000000000000), (190260384905282832168334270449738431/953677590949420144358400000000000000), (11425354137025961287937658059947727/55770619353767259904000000000000000), (6682506751804553027263015263672699389/31789253031647338145280000000000000000)]
    reserve := (188736899161/1000000000000) }

theorem quarter_003_025_valid : quarter_003_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_025]
  · intro i; fin_cases i <;> norm_num [quarter_003_025]
  · norm_num [quarter_003_025]
  · norm_num [quarter_003_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_025]

def quarter_003_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![0, (6018769/20000000), (25801747/100000000), (25801747/100000000), (915133/10000000), (915133/10000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(376173/25000000), 0, (6018769/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2389911/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (880593/12500000), (1/100000000), (3458757/50000000), (1/100000000), (2389911/100000000)]
    alternative := .zero
    polynomial := [(-185594548897684243768286516783/3235150507796591916000000000000), (155294754989443/140894880000000), (-1159175728230703530251856716783/1617575253898295958000000000000), (155294754989443/140894880000000), (-2132756907563722816735426916783/3235150507796591916000000000000)]
    bernstein := [(581660042222744045279862603102507499/2760661766653091768320000000000000000), (149311370087734301286761537122721127/690165441663272942080000000000000000), (344700176089700084829463336182763039/1552872243742364119680000000000000000), (29452903414749209814012769972655249/129406020311863676640000000000000000), (7544926344107428750181998407451177/32351505077965919160000000000000000)]
    reserve := (210695873449/1000000000000) }

theorem quarter_003_026_valid : quarter_003_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_026]
  · intro i; fin_cases i <;> norm_num [quarter_003_026]
  · norm_num [quarter_003_026]
  · norm_num [quarter_003_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_026]

def quarter_003_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![0, (15073833/50000000), (13058001/50000000), (13058001/50000000), (1762033/20000000), (1762033/20000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1507383/100000000), 0, (15073833/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1150407/50000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (6799557/100000000), (1/100000000), (696437/10000000), (1/100000000), (1150407/50000000)]
    alternative := .zero
    polynomial := [(-1541939612754997933748030947/21363568131934362600000000000), (65611375462611/56662975000000), (-7982556778853008909624946947/10681784065967181300000000000), (65611375462611/56662975000000), (-14423173944951019885501862947/21363568131934362600000000000)]
    bernstein := [(49934930947319711472292168646693/213635681319343626000000000000000), (204809646661957858730705610583103/854542725277374504000000000000000), (359782904968604270743174366411277/1464930386189784864000000000000000), (56375613998090372665756079561743/224142354171114624000000000000000), (230805595884299472499030019835953/896569416684458496000000000000000)]
    reserve := (233738721167/1000000000000) }

theorem quarter_003_027_valid : quarter_003_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_027]
  · intro i; fin_cases i <;> norm_num [quarter_003_027]
  · norm_num [quarter_003_027]
  · norm_num [quarter_003_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_027]

def quarter_003_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![0, (30195401/100000000), (6607097/25000000), (6607097/25000000), (1059239/12500000), (1059239/12500000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(150977/10000000), 0, (30195401/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2213/100000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (3274889/50000000), (1/100000000), (7012801/100000000), (1/100000000), (2213001/100000000)]
    alternative := .zero
    polynomial := [(-18174190912367543131803592456249/203296406112975244356000000000000), (199503943360897/163744450000000), (-79560355956768931195827660016249/101648203056487622178000000000000), (199503943360897/163744450000000), (-140946521001170319259851727576249/203296406112975244356000000000000)]
    bernstein := [(134270547016186968505767755009538653111/520438799649216625551360000000000000000), (848919345627624874485994064507770709/3212585183019855713280000000000000000), (105583101842481753648088152322310703293/390329099736912469163520000000000000000), (222266662100678749578300958392506189/803146295754963928320000000000000000), (9204963839318639919568000282166225351/32527424978076039096960000000000000000)]
    reserve := (1289974413/5000000000) }

theorem quarter_003_028_valid : quarter_003_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_028]
  · intro i; fin_cases i <;> norm_num [quarter_003_028]
  · norm_num [quarter_003_028]
  · norm_num [quarter_003_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_028]

def quarter_003_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 0, 0, 0, 3]
    lambda := ![0, (7559971/25000000), (5347609/20000000), (5347609/20000000), (2035503/25000000), (2035503/25000000), 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(755997/50000000), 0, (7559971/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2126323/100000000), 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (15741/250000), (1/100000000), (110351/1562500), (1/100000000), (2126323/100000000)]
    alternative := .zero
    polynomial := [(-6460682003404520594859143923/59095962652806288000000000000), (40427768959339/31482000000000), (-24331232558296464830765063923/29547981326403144000000000000), (40427768959339/31482000000000), (-42201783113188409066670983923/59095962652806288000000000000)]
    bernstein := [(99315686655200965124614642277751/350198297201815040000000000000000), (3695622310549625261077540240329/12734483534611456000000000000000), (1347108300080161062675308375817023/4538569931735522918400000000000000), (183613582215573400729987237769401/605142657564736389120000000000000), (75045560896047120766540292306333/242057063025894555648000000000000)]
    reserve := (283598428229/1000000000000) }

theorem quarter_003_029_valid : quarter_003_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_003_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_003_029]
  · intro i; fin_cases i <;> norm_num [quarter_003_029]
  · norm_num [quarter_003_029]
  · norm_num [quarter_003_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_003_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_003_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_003_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_003_029]

def quarterTable003 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 0, 0, 0, 3]
  rows := [quarter_003_000, quarter_003_001, quarter_003_002, quarter_003_003, quarter_003_004, quarter_003_005, quarter_003_006, quarter_003_007, quarter_003_008, quarter_003_009, quarter_003_010, quarter_003_011, quarter_003_012, quarter_003_013, quarter_003_014, quarter_003_015, quarter_003_016, quarter_003_017, quarter_003_018, quarter_003_019, quarter_003_020, quarter_003_021, quarter_003_022, quarter_003_023, quarter_003_024, quarter_003_025, quarter_003_026, quarter_003_027, quarter_003_028, quarter_003_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_003_000_valid
    · exact quarter_003_001_valid
    · exact quarter_003_002_valid
    · exact quarter_003_003_valid
    · exact quarter_003_004_valid
    · exact quarter_003_005_valid
    · exact quarter_003_006_valid
    · exact quarter_003_007_valid
    · exact quarter_003_008_valid
    · exact quarter_003_009_valid
    · exact quarter_003_010_valid
    · exact quarter_003_011_valid
    · exact quarter_003_012_valid
    · exact quarter_003_013_valid
    · exact quarter_003_014_valid
    · exact quarter_003_015_valid
    · exact quarter_003_016_valid
    · exact quarter_003_017_valid
    · exact quarter_003_018_valid
    · exact quarter_003_019_valid
    · exact quarter_003_020_valid
    · exact quarter_003_021_valid
    · exact quarter_003_022_valid
    · exact quarter_003_023_valid
    · exact quarter_003_024_valid
    · exact quarter_003_025_valid
    · exact quarter_003_026_valid
    · exact quarter_003_027_valid
    · exact quarter_003_028_valid
    · exact quarter_003_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
