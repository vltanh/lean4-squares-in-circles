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

def quarter_007_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_007_000_valid : quarter_007_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_000]
  · intro i; fin_cases i <;> norm_num [quarter_007_000]
  · norm_num [quarter_007_000]
  · norm_num [quarter_007_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_000]

def quarter_007_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_007_001_valid : quarter_007_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_001]
  · intro i; fin_cases i <;> norm_num [quarter_007_001]
  · norm_num [quarter_007_001]
  · norm_num [quarter_007_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_001]

def quarter_007_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(1243607/4000000), (1243607/4000000), 0, 0, 0, 0, (756393/2000000)]
    cone := fun i => (![![(269179/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9876771/100000000), 0, 0]] i.1) i.2
    mu := ![(43683/20000000), (1/100000000), (1571173/20000000), (1/100000000), (1/100000000), (1/100000000), (9876771/100000000)]
    alternative := .zero
    polynomial := [(-85164097015208738094367388111/15063952396387924200000000000), (-1104002088711/29122000000), (-495325370133122935105348988111/7531976198193962100000000000), (-1104002088711/29122000000), (-905486643251037132116330588111/15063952396387924200000000000)]
    bernstein := [(13560145988169784209541094486372929/38563718134753085952000000000000000), (3454967606524006263315975811040399/9640929533688271488000000000000000), (2589538444618496992879879634668807/7230697150266203616000000000000000), (211550163635565640610824975550539/602558095855516968000000000000000), (50820476142515489025771279653209/150639523963879242000000000000000)]
    reserve := (5271325339/15625000000) }

theorem quarter_007_002_valid : quarter_007_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_002]
  · intro i; fin_cases i <;> norm_num [quarter_007_002]
  · norm_num [quarter_007_002]
  · norm_num [quarter_007_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_002]

def quarter_007_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(15722243/50000000), (15722243/50000000), 0, 0, 0, 0, (9277757/25000000)]
    cone := fun i => (![![(1970971/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9691711/100000000), 0, 0]] i.1) i.2
    mu := ![(5431/2500000), (1/100000000), (7945393/100000000), (1/100000000), (1/100000000), (1/100000000), (9691711/100000000)]
    alternative := .zero
    polynomial := [(-1955721723182496371722023882269/418211182816944313000000000000), (-18627739998979/543100000000), (-13319646141900841152250698335269/209105591408472156500000000000), (-18627739998979/543100000000), (-24683570560619185932779372788269/418211182816944313000000000000)]
    bernstein := [(1373549323797071574418854503876011/4182111828169443130000000000000000), (5602267458063742645849756284893007/16728447312677772520000000000000000), (67171118947903957858377812755223477/200741367752133270240000000000000000), (87720984766141713194133598434534083/267655157002844360320000000000000000), (336587108727047934738425643352956771/1070620628011377441280000000000000000)]
    reserve := (15719251989/50000000000) }

theorem quarter_007_003_valid : quarter_007_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_003]
  · intro i; fin_cases i <;> norm_num [quarter_007_003]
  · norm_num [quarter_007_003]
  · norm_num [quarter_007_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_003]

def quarter_007_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(15883043/50000000), (15883043/50000000), 0, 0, 0, 0, (36467829/100000000)]
    cone := fun i => (![![(17911403/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9523737/100000000), 0, 0]] i.1) i.2
    mu := ![(108083/50000000), (1/100000000), (1605331/20000000), (1/100000000), (1/100000000), (1/100000000), (9523737/100000000)]
    alternative := .zero
    polynomial := [(-155535914376581364302739934399/40801333145687842000000000000), (-666923477246639/21616600000000), (-1261774849687475053197339944399/20400666572843921000000000000), (-666923477246639/21616600000000), (-2368013784998368742091939954399/40801333145687842000000000000)]
    bernstein := [(31826152911368799562523300268111441/104451412852960875520000000000000000), (3247461764001337482718584633293891/10445141285296087552000000000000000), (973216382774473456864357496526139/3133542385588826265600000000000000), (31737398239578762469785951192107/104451412852960875520000000000000), (104745744959724344426725167541/360177285699865088000000000000)]
    reserve := (290817186753/1000000000000) }

theorem quarter_007_004_valid : quarter_007_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_004]
  · intro i; fin_cases i <;> norm_num [quarter_007_004]
  · norm_num [quarter_007_004]
  · norm_num [quarter_007_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_004]

def quarter_007_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(16027921/50000000), (16027921/50000000), 0, 0, 0, 0, (35888317/100000000)]
    cone := fun i => (![![(8068369/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4686197/50000000), 0, 0]] i.1) i.2
    mu := ![(26899/12500000), (1/100000000), (809987/10000000), (1/100000000), (1/100000000), (1/100000000), (1874479/20000000)]
    alternative := .zero
    polynomial := [(-249308976320555688379439728539/81681698244143854000000000000), (-296458345096637/10759600000000), (-2458870693338814998521867311039/40840849122071927000000000000), (-296458345096637/10759600000000), (-4668432410357074308664294893539/81681698244143854000000000000)]
    bernstein := [(158467360725862147553343161817/565149047310833152000000000000), (59882477961166992865434788647453/209105147505008266240000000000000), (1794117158660409086765103783051239/6273154425150247987200000000000000), (142491180698193274939976856863269/510012554890264064000000000000000), (1359864013576677398566702660198581/5100125548902640640000000000000000)]
    reserve := (266633438831/1000000000000) }

theorem quarter_007_005_valid : quarter_007_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_005]
  · intro i; fin_cases i <;> norm_num [quarter_007_005]
  · norm_num [quarter_007_005]
  · norm_num [quarter_007_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_005]

def quarter_007_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(16157263/50000000), (16157263/50000000), 0, 0, 0, 0, (8842737/25000000)]
    cone := fun i => (![![(14383163/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9237281/100000000), 0, 0]] i.1) i.2
    mu := ![(107157/50000000), (1/100000000), (4082617/50000000), (1/100000000), (1/100000000), (1/100000000), (4618641/50000000)]
    alternative := .zero
    polynomial := [(-1073004969427794379636910407923/449015030339899562000000000000), (-43549751766571/1785950000000), (-13191704394396328459248495447923/224507515169949781000000000000), (-43549751766571/1785950000000), (-25310403819364862538860080487923/449015030339899562000000000000)]
    bernstein := [(293695664243716199757997968079815597/1149478477670142878720000000000000000), (3412683134902555606997989567577303/13062255428069805440000000000000000), (501933619199321518189450188857437/1924350130028140980000000000000000), (25952651381423405379335118983019/102048870531795355000000000000000), (16963870743970253944280343241013/70158598490609306562500000000000)]
    reserve := (30224147697/125000000000) }

theorem quarter_007_006_valid : quarter_007_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_006]
  · intro i; fin_cases i <;> norm_num [quarter_007_006]
  · norm_num [quarter_007_006]
  · norm_num [quarter_007_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_006]

def quarter_007_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(32542819/100000000), (32542819/100000000), 0, 0, 0, 0, (34914361/100000000)]
    cone := fun i => (![![(12648221/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4559021/50000000), 0, 0]] i.1) i.2
    mu := ![(53383/25000000), (1/100000000), (205573/2500000), (1/100000000), (1/100000000), (1/100000000), (4559021/50000000)]
    alternative := .zero
    polynomial := [(-90960215053305765088035569457/50031168125753639000000000000), (-455502420455197/21353200000000), (-1438330319051835225363089913207/25015584062876819500000000000), (-455502420455197/21353200000000), (-2785700423050364685638144256957/50031168125753639000000000000)]
    bernstein := [(1797713066104871049698429249267/7817370019649006093750000000000), (1841151163513955647035376460193/7817370019649006093750000000000), (29396950181331901304214493790877/125077920314384097500000000000000), (914891027886863081241285855959031/4002493450060291120000000000000000), (27696355731980612426956468442568643/128079790401929315840000000000000000)]
    reserve := (216242981387/1000000000000) }

theorem quarter_007_007_valid : quarter_007_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_007]
  · intro i; fin_cases i <;> norm_num [quarter_007_007]
  · norm_num [quarter_007_007]
  · norm_num [quarter_007_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_007]

def quarter_007_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(32424929/100000000), (32424929/100000000), (483163/100000000), (483163/100000000), 0, 0, (4272977/12500000)]
    cone := fun i => (![![(10823921/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (143117/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1115907/12500000), 0, 0]] i.1) i.2
    mu := ![(105393/50000000), (1/100000000), (64339/781250), (1/100000000), (125597/100000000), (1/100000000), (8927257/100000000)]
    alternative := .zero
    polynomial := [(-31966400179632284103328760440304161/24329509604425881076425600000000000), (-1578195024744470418293/86795266905600000000), (-226510956848001548420447749452933387/4054918267404313512737600000000000), (-1578195024744470418293/86795266905600000000), (-1327099340908377006419357736277296161/24329509604425881076425600000000000)]
    bernstein := [(12685764303608488613243932075557389222639/62283544587330255555649536000000000000000), (2170550746274833346635285047662671576927/10380590764555042592608256000000000000000), (3248833202309679127179374650240198291099/15570886146832563888912384000000000000000), (27646305193685061659298555813369407153/136586720586250560429056000000000000000), (741311895343491046453253994276968186759/3892721536708140972228096000000000000000)]
    reserve := (190435377499/1000000000000) }

theorem quarter_007_008_valid : quarter_007_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_008]
  · intro i; fin_cases i <;> norm_num [quarter_007_008]
  · norm_num [quarter_007_008]
  · norm_num [quarter_007_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_008]

def quarter_007_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(31044647/100000000), (31044647/100000000), (2834781/100000000), (2834781/100000000), 0, 0, (4030143/12500000)]
    cone := fun i => (![![(2175449/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (167937/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8419919/100000000), 0, 0]] i.1) i.2
    mu := ![(200211/100000000), (1/100000000), (8083577/100000000), (1/100000000), (73689/10000000), (1/100000000), (8419919/100000000)]
    alternative := .zero
    polynomial := [(-8240789709118168469861033563302889/9737290556064131720278080000000000), (-783587325144452228963/53947367824900000000), (-254661900528336886233697223024675689/4868645278032065860139040000000000), (-783587325144452228963/53947367824900000000), (-501083011347555603997533412486048489/9737290556064131720278080000000000)]
    bernstein := [(278122171179139269788401058160133655591/1557966488970261075244492800000000000000), (114681053498761781134937677010230430237/623186595588104430097797120000000000000), (19661327181141368320248403118140619579/106831987815103616588193792000000000000), (3562199599332915294468305132288102369/19941971058819341763129507840000000000), (267753771583422075735384009837176879/1595357684705547341050360627200000000)]
    reserve := (33566613199/200000000000) }

theorem quarter_007_009_valid : quarter_007_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_009]
  · intro i; fin_cases i <;> norm_num [quarter_007_009]
  · norm_num [quarter_007_009]
  · norm_num [quarter_007_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_009]

def quarter_007_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(14877703/50000000), (14877703/50000000), (38949/781250), (38949/781250), 0, 0, (7629561/25000000)]
    cone := fun i => (![![(3390393/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1476737/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (996247/12500000), 0, 0]] i.1) i.2
    mu := ![(61/32000), (1/100000000), (7923323/100000000), (1/100000000), (647977/50000000), (1/100000000), (996247/12500000)]
    alternative := .zero
    polynomial := [(-1231080111182930072976306009313513/2496052984753110146056000000000000), (-22384737122291595457/1987346640625000000), (-307130938990901592444426333123231117/6240132461882775365140000000000000), (-22384737122291595457/1987346640625000000), (-608106477425888534523971136199894669/12480264923765550730280000000000000)]
    bernstein := [(1592923438868509668691009229590253719/10223833025548739158245376000000000000), (10312694766759057410749888679112114979/63898956409679619739033600000000000000), (12924651248657042023593885997100140951/79873695512099524673792000000000000000), (15687687175764234745578544544299120399/99842119390124405842240000000000000000), (18390516674913733734457266282347746171/124802649237655507302800000000000000000)]
    reserve := (1151224853/7812500000) }

theorem quarter_007_010_valid : quarter_007_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_010]
  · intro i; fin_cases i <;> norm_num [quarter_007_010]
  · norm_num [quarter_007_010]
  · norm_num [quarter_007_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_010]

def quarter_007_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(28555393/100000000), (28555393/100000000), (6946597/100000000), (6946597/100000000), 0, 0, (28996021/100000000)]
    cone := fun i => (![![(5035749/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1028819/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (189311/2500000), 0, 0]] i.1) i.2
    mu := ![(4549/2500000), (1/100000000), (3878093/50000000), (1/100000000), (90287/5000000), (1/100000000), (7572441/100000000)]
    alternative := .zero
    polynomial := [(-2286698364360617625069298838073313/9649065722023439365855200000000000), (-588519902675185085297/70565780228000000000), (-224578098232494990272896358235003613/4824532861011719682927600000000000), (-588519902675185085297/70565780228000000000), (-446869498100629362920723417631933913/9649065722023439365855200000000000)]
    bernstein := [(13048646341159801994495208356160811487/96490657220234393658552000000000000000), (54377367977264936904684054656970492661/385962628880937574634208000000000000000), (656130489540285597004100774770446906449/4631551546571250895610496000000000000000), (849767347121561874578264988729916147649/6175402062095001194147328000000000000000), (3179807758000664796766438956614003802647/24701608248380004776589312000000000000000)]
    reserve := (257457549/2000000000) }

theorem quarter_007_011_valid : quarter_007_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_011]
  · intro i; fin_cases i <;> norm_num [quarter_007_011]
  · norm_num [quarter_007_011]
  · norm_num [quarter_007_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_011]

def quarter_007_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(27441261/100000000), (27441261/100000000), (68207/781250), (68207/781250), 0, 0, (13828243/50000000)]
    cone := fun i => (![![(3443609/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (646511/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1444523/20000000), 0, 0]] i.1) i.2
    mu := ![(174149/100000000), (1/100000000), (7583411/100000000), (1/100000000), (2269457/100000000), (1/100000000), (902827/12500000)]
    alternative := .zero
    polynomial := [(-171008251909697613289475764284012361/2705902078731257626168421000000000000), (-94123523913109936141/16508043027987500000), (-59874177756771360029357612394942492361/1352951039365628813084210500000000000), (-94123523913109936141/16508043027987500000), (-119577347261633022445425749025600972361/2705902078731257626168421000000000000)]
    bernstein := [(807029547913049531262984817477034010681959/6927109321552019522991157760000000000000000), (423318860449436886845605624484544930934253/3463554660776009761495578880000000000000000), (640621870261545313152932294541100917683453/5195331991164014642243368320000000000000000), (103726039564584118345313073998790572440917/865888665194002440373894720000000000000000), (48353753894344575769123422767674425778839/432944332597001220186947360000000000000000)]
    reserve := (13960730703/125000000000) }

theorem quarter_007_012_valid : quarter_007_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_012]
  · intro i; fin_cases i <;> norm_num [quarter_007_012]
  · norm_num [quarter_007_012]
  · norm_num [quarter_007_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_012]

def quarter_007_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(26408683/100000000), (26408683/100000000), (2069957/20000000), (2069957/20000000), 0, 0, (13241531/50000000)]
    cone := fun i => (![![(24793/1250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (306569/10000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (691617/10000000), 0, 0]] i.1) i.2
    mu := ![(41781/25000000), (1/100000000), (7406003/100000000), (1/100000000), (538077/20000000), (1/100000000), (6916171/100000000)]
    alternative := .zero
    polynomial := [(268194507522218237294779586235899/6734056481467150763411000000000000), (-102178355747118473443/30943021134300000000), (-427242111256901676200937113581154803/10101084722200726145116500000000000), (-102178355747118473443/30943021134300000000), (-855288806036370007113758565921017303/20202169444401452290233000000000000)]
    bernstein := [(107034202485238303122636129585364420099/1077449037034744122145760000000000000000), (679535687791540468841127147328609509097/6464694222208464732874560000000000000000), (217354503586981063394617655615293153289/2041482385960567810381440000000000000000), (2674385478751283215965521601560726165497/25858776888833858931498240000000000000000), (4963844286020964174764709894813341133097/51717553777667717862996480000000000000000)]
    reserve := (95979873823/1000000000000) }

theorem quarter_007_013_valid : quarter_007_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_013]
  · intro i; fin_cases i <;> norm_num [quarter_007_013]
  · norm_num [quarter_007_013]
  · norm_num [quarter_007_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_013]

def quarter_007_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(25452763/100000000), (25452763/100000000), (5908439/50000000), (5908439/50000000), 0, 0, (12730359/50000000)]
    cone := fun i => (![![(636419/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (700051/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (332459/5000000), 0, 0]] i.1) i.2
    mu := ![(160823/100000000), (1/100000000), (7224793/100000000), (1/100000000), (12287/400000), (1/100000000), (6649181/100000000)]
    alternative := .zero
    polynomial := [(1123614919756828905052334652256051/13807494492978975753764800000000000), (-63922483767428511799/58095644231950000000), (-280581279766569548559515604317759949/6903747246489487876882400000000000), (-63922483767428511799/58095644231950000000), (-562286174452895926024083543287775949/13807494492978975753764800000000000)]
    bernstein := [(2950949887252071107141976340966056387251/35347185902026177929637888000000000000000), (1973068034708583350824090817068686251/22091991188766361206023680000000000000), (2008103772141182128792235545694481617/22091991188766361206023680000000000000), (1218567105314884862415357142940651/13807494492978975753764800000000000), (1123614919756828905052334652256051/13807494492978975753764800000000000)]
    reserve := (10172147093/125000000000) }

theorem quarter_007_014_valid : quarter_007_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_014]
  · intro i; fin_cases i <;> norm_num [quarter_007_014]
  · norm_num [quarter_007_014]
  · norm_num [quarter_007_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_014]

def quarter_007_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(12202813/50000000), (12202813/50000000), (3186297/25000000), (3186297/25000000), 0, 0, (25698373/100000000)]
    cone := fun i => (![![0, 0, (642359/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (943807/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1342249/20000000), 0, 0]] i.1) i.2
    mu := ![(40581/25000000), (1/100000000), (6957077/100000000), (1/100000000), (165653/5000000), (1/100000000), (3355623/50000000)]
    alternative := .zero
    polynomial := [(45137853514420479394256244233401/697492439825026719442680000000000), (223378464597533183959/112930056694800000000), (-14309207063637986476296141169752599/348746219912513359721340000000000), (223378464597533183959/112930056694800000000), (-28663551980790393431986538583738599/697492439825026719442680000000000)]
    bernstein := [(45137853514420479394256244233401/697492439825026719442680000000000), (143361899648522865329130723882851/1859979839533404585180480000000000), (285131934801826027616144492488186201/3347963711160128253324864000000000000), (794477631331291301196986784397749353/8927903229760342008866304000000000000), (158088039800620337807061059490061180601/1785580645952068401773260800000000000000)]
    reserve := (64714469917/1000000000000) }

theorem quarter_007_015_valid : quarter_007_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_015]
  · intro i; fin_cases i <;> norm_num [quarter_007_015]
  · norm_num [quarter_007_015]
  · norm_num [quarter_007_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_015]

def quarter_007_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(3055439/12500000), (3055439/12500000), (2775561/20000000), (2775561/20000000), 0, 0, (11678683/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2055359/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (6099881/100000000), 0, 0]] i.1) i.2
    mu := ![(26501/4000000), (1/100000000), (434273/6250000), (1/100000000), (3607479/100000000), (1/100000000), (6099881/100000000)]
    alternative := .zero
    polynomial := [(68430493015459472342638498883919137/1013001892138183435444908000000000000), (82976680251067/86854600000000), (-4543993923957765355057539767699428063/506500946069091717722454000000000000), (82976680251067/86854600000000), (-9156418340930990182457718034282775263/1013001892138183435444908000000000000)]
    bernstein := [(222608306067804992018809061676829524543137/2593284843873749594738964480000000000000000), (12824564447850925985312487011232265370393/144071380215208310818831360000000000000000), (177497062252314753608234208970946568186611/1944963632905312196054223360000000000000000), (3334313836173073229496272471990387098793/36017845053802077704707840000000000000000), (15066066534902988072660021598719889894337/162080302742109349671185280000000000000000)]
    reserve := (85840283451/1000000000000) }

theorem quarter_007_016_valid : quarter_007_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_016]
  · intro i; fin_cases i <;> norm_num [quarter_007_016]
  · norm_num [quarter_007_016]
  · norm_num [quarter_007_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_016]

def quarter_007_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(2410241/10000000), (2410241/10000000), (14722309/100000000), (14722309/100000000), 0, 0, (22350563/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4360867/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5836949/100000000), 0, 0]] i.1) i.2
    mu := ![(982597/100000000), (1/100000000), (6812437/100000000), (1/100000000), (765401/20000000), (1/100000000), (116739/2000000)]
    alternative := .zero
    polynomial := [(2774848321162390744803284772486913/48825515610339482330316000000000000), (41210420773047/42577731250000), (-142834639147373909738966744119313087/24412757805169741165158000000000000), (41210420773047/42577731250000), (-41206303802272887174676681858730441/6975073658619926047188000000000000)]
    bernstein := [(708425273737067604859414591875671697313/7812082497654317172850560000000000000000), (1454652247820506674420994138120837446739/15624164995308634345701120000000000000000), (8898142228011582263867408943086251219051/93744989971851806074206720000000000000000), (6007807515788527817290433776306652342651/62496659981234537382804480000000000000000), (12091101408552080420895154878846249014353/124993319962469074765608960000000000000000)]
    reserve := (4534164059/50000000000) }

theorem quarter_007_017_valid : quarter_007_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_017]
  · intro i; fin_cases i <;> norm_num [quarter_007_017]
  · norm_num [quarter_007_017]
  · norm_num [quarter_007_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_017]

def quarter_007_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(1486663/6250000), (1486663/6250000), (7754959/50000000), (7754959/50000000), 0, 0, (5351737/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4594163/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (139763/2500000), 0, 0]] i.1) i.2
    mu := ![(642089/50000000), (1/100000000), (6667597/100000000), (1/100000000), (201587/5000000), (1/100000000), (5590521/100000000)]
    alternative := .zero
    polynomial := [(3529539197053971775326021346863817111/77196810989564131137407856000000000000), (81799268013257/83344962500000), (-167882285050253300336137043865864502889/38598405494782065568703928000000000000), (81799268013257/83344962500000), (-339294109297560572447600109078592822889/77196810989564131137407856000000000000)]
    bernstein := [(18801860664890739219287953725384875372702791/197623836133284175711764111360000000000000000), (4804890890008325185657245490550868352554397/49405959033321043927941027840000000000000000), (3665479030839784050299052223653547803172297/37054469274990782945955770880000000000000000), (309227722613829167954254965762840947549033/3087872439582565245496314240000000000000000), (77902430794532592099121588287865986509311/771968109895641311374078560000000000000000)]
    reserve := (95139640201/1000000000000) }

theorem quarter_007_018_valid : quarter_007_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_018]
  · intro i; fin_cases i <;> norm_num [quarter_007_018]
  · norm_num [quarter_007_018]
  · norm_num [quarter_007_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_018]

def quarter_007_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(23496137/100000000), (23496137/100000000), (16243937/100000000), (16243937/100000000), 0, 0, (5129963/25000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2405793/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5358851/100000000), 0, 0]] i.1) i.2
    mu := ![(784207/50000000), (1/100000000), (162873/2500000), (1/100000000), (2111273/50000000), (1/100000000), (1339713/25000000)]
    alternative := .zero
    polynomial := [(549559111857154811683301253552011/16056595166165544477308400000000000), (649040157555049/651492000000000), (-27902454829345294973697553103927989/8028297583082772238654200000000000), (649040157555049/651492000000000), (-56354468770547744759078407461407989/16056595166165544477308400000000000)]
    bernstein := [(16014874703183413993401886548575827211/160565951661655444773084000000000000000), (483940088537558626457138770328925883/4757509678863865030313600000000000000), (31861301389193072334593861530967750657/308286627190378453964321280000000000000), (63711643386622800929967268737513599/608961238894574723880140800000000000), (277645298202111998958025420933073699/2630712552024562807162208256000000000)]
    reserve := (99740166189/1000000000000) }

theorem quarter_007_019_valid : quarter_007_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_019]
  · intro i; fin_cases i <;> norm_num [quarter_007_019]
  · norm_num [quarter_007_019]
  · norm_num [quarter_007_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_019]

def quarter_007_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(23230849/100000000), (23230849/100000000), (16927601/100000000), (16927601/100000000), 0, 0, (19683099/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5014093/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5140329/100000000), 0, 0]] i.1) i.2
    mu := ![(918327/50000000), (1/100000000), (635539/10000000), (1/100000000), (4400261/100000000), (1/100000000), (514033/10000000)]
    alternative := .zero
    polynomial := [(117779171975242882963938619108190207/5280426343534595210560356000000000000), (643430083870469/635539000000000), (-7682008148760412646722848510321819793/2640213171767297605280178000000000000), (643430083870469/635539000000000), (-15481795469496068176409635639751829793/5280426343534595210560356000000000000)]
    bernstein := [(6964798374054355580896759836848990291/66549619394208313792169902080000000000), (88669459280244741482370658678440208541/831870242427603922402123776000000000000), (43892497199487612083831089663986107980661/405536743183456912171035340800000000000000), (37032857517242256213081891280260109154069/337947285986214093475862784000000000000000), (93470779034492893765196670915463657437167/844868214965535233689656960000000000000000)]
    reserve := (10465572061/100000000000) }

theorem quarter_007_020_valid : quarter_007_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_020]
  · intro i; fin_cases i <;> norm_num [quarter_007_020]
  · norm_num [quarter_007_020]
  · norm_num [quarter_007_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_020]

def quarter_007_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(22990469/100000000), (22990469/100000000), (8782023/50000000), (8782023/50000000), 0, 0, (18890969/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (5202613/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4933461/100000000), 0, 0]] i.1) i.2
    mu := ![(2090203/100000000), (1/100000000), (3094957/50000000), (1/100000000), (2282851/50000000), (1/100000000), (2466731/50000000)]
    alternative := .zero
    polynomial := [(2882857682409118350134258982062491043/291428775342879149914703608000000000000), (318836301025453/309495700000000), (-366890211468839613826202474583352508957/145714387671439574957351804000000000000), (318836301025453/309495700000000), (-736663280620088346002539208148767508957/291428775342879149914703608000000000000)]
    bernstein := [(5127477772010418666403700622486184946964083/46628604054860663986352577280000000000000000), (10435775867992177164183521808050046533637927/93257208109721327972705154560000000000000000), (63559951328999944153631846546325999802561489/559543248658327967836230927360000000000000000), (42909705548912091426094503306539419946253647/373028832438885311890820618240000000000000000), (86702480519599528682768739440321742307016643/746057664877770623781641236480000000000000000)]
    reserve := (109964213511/1000000000000) }

theorem quarter_007_021_valid : quarter_007_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_021]
  · intro i; fin_cases i <;> norm_num [quarter_007_021]
  · norm_num [quarter_007_021]
  · norm_num [quarter_007_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_021]

def quarter_007_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(182197/800000), (182197/800000), (1815629/10000000), (1815629/10000000), 0, 0, (1813817/10000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (134451/2500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (148027/3125000), 0, 0]] i.1) i.2
    mu := ![(2330267/100000000), (1/100000000), (6019321/100000000), (1/100000000), (2359827/50000000), (1/100000000), (947373/20000000)]
    alternative := .zero
    polynomial := [(-4688813776647098194471495502717/1515998714026934354956200000000000), (63186163130639/60193210000000), (-1693668970033620961321028593502717/757999357013467177478100000000000), (63186163130639/60193210000000), (-3382649126290594824447585691502717/1515998714026934354956200000000000)]
    bernstein := [(449078589759588287969067735929718030883/3880956707908951948687872000000000000000), (6343758610500495791628573203501177341/53902176498735443731776000000000000000), (776076567738482925062364874235068567/6497137345829718664098000000000000000), (7278462526562717864477998921748231/60158679128052950593500000000000000), (28970629070749610931057120092390827/236874799066708492961906250000000000)]
    reserve := (28928343161/250000000000) }

theorem quarter_007_022_valid : quarter_007_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_022]
  · intro i; fin_cases i <;> norm_num [quarter_007_022]
  · norm_num [quarter_007_022]
  · norm_num [quarter_007_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_022]

def quarter_007_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![(3/100000000), (9487147/25000000), (31025703/100000000), (31025703/100000000), 0, 0, (1/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1897429/100000000), 0, (7589717/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1838013/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (19553/200000), (1/100000000), (1613001/20000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-85437012590659881031/970431032400000000000), (294345414915841/244412500000000), (-453701916013213365031/485215516200000000000), (294345414915841/244412500000000), (-821966819435766849031/970431032400000000000)]
    bernstein := [(18756057016058600721041/151629848812500000000000), (314466692683101731153173/2426077581000000000000000), (3944776854984321568793483/29112930972000000000000000), (43890693031097664460566241/310537930368000000000000000), (365531940355213760338868249/2484303442944000000000000000)]
    reserve := (12369633791/100000000000) }

theorem quarter_007_023_valid : quarter_007_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_023]
  · intro i; fin_cases i <;> norm_num [quarter_007_023]
  · norm_num [quarter_007_023]
  · norm_num [quarter_007_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_023]

def quarter_007_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![0, (37623949/100000000), (1247521/4000000), (1247521/4000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1881197/100000000), 0, (37623949/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4619073/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (9397071/100000000), (1/100000000), (5067/62500), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-10992466565673409051661/112865087424000000000000), (46936666480429/37588284000000), (-53456769496884582811661/56432543712000000000000), (46936666480429/37588284000000), (-95921072428095756571661/112865087424000000000000)]
    bernstein := [(42662276558871550727138640979/288934623805440000000000000000), (13326002306016362546608994513/86680387141632000000000000000), (1385004817804155829471783961/8668038714163200000000000000), (143709844023331523083573841/866803871416320000000000000), (14888946021165516004689913/86680387141632000000000000)]
    reserve := (147653735633/1000000000000) }

theorem quarter_007_024_valid : quarter_007_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_024]
  · intro i; fin_cases i <;> norm_num [quarter_007_024]
  · norm_num [quarter_007_024]
  · norm_num [quarter_007_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_024]

def quarter_007_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![0, (9326257/25000000), (15673743/50000000), (15673743/50000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1865251/100000000), 0, (9326257/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9285379/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (4508941/50000000), (1/100000000), (8148651/100000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-5319720875589001917391239/48989048784788000000000000), (146177355369951/112723525000000), (-23595099241687825058031239/24494524392394000000000000), (146177355369951/112723525000000), (-41870477607786648198671239/48989048784788000000000000)]
    bernstein := [(2161135466766834344685131929/12541196488905728000000000000), (22398992831913094271639828227/125411964889057280000000000000), (695476964305009053854877921379/3762358946671718400000000000000), (2396228917672216159445022723451/12541196488905728000000000000000), (24738338635393261459885119609001/125411964889057280000000000000000)]
    reserve := (34464581887/200000000000) }

theorem quarter_007_025_valid : quarter_007_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_025]
  · intro i; fin_cases i <;> norm_num [quarter_007_025]
  · norm_num [quarter_007_025]
  · norm_num [quarter_007_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_025]

def quarter_007_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![0, (18497209/50000000), (31502791/100000000), (31502791/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1849721/100000000), 0, (18497209/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4665691/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (8639939/100000000), (1/100000000), (4094511/50000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8620129557683961896953993/70752650549658000000000000), (582713709210319/431996950000000), (-34794660848103739987393993/35376325274829000000000000), (582713709210319/431996950000000), (-60969192138523518077833993/70752650549658000000000000)]
    bernstein := [(35836121135881466594900262738887/181126785407124480000000000000000), (9254003883535920909843599554351/45281696351781120000000000000000), (7160807188386803798463834659969/33961272263835840000000000000000), (615019894650041213663799532379/2830106021986320000000000000000), (158309152474742025727223529167/707526505496580000000000000000)]
    reserve := (39570206091/200000000000) }

theorem quarter_007_026_valid : quarter_007_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_026]
  · intro i; fin_cases i <;> norm_num [quarter_007_026]
  · norm_num [quarter_007_026]
  · norm_num [quarter_007_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_026]

def quarter_007_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![0, (18347079/50000000), (31652921/100000000), (31652921/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(458677/25000000), 0, (18347079/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9375851/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (1652827/20000000), (1/100000000), (514253/6250000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-22416600006866766580804681/163194478700352000000000000), (15695638977507/11167750000000), (-82299439868450276016964681/81597239350176000000000000), (15695638977507/11167750000000), (-142182279730033785453124681/163194478700352000000000000)]
    bernstein := [(366187341137210436331360385039/1631944787003520000000000000000), (1509042595285333601704661449469/6527779148014080000000000000000), (18638282272836485630623218590897/78333349776168960000000000000000), (25555221205042992801932361897529/104444466368225280000000000000000), (105029309429560144952754414821159/417777865472901120000000000000000)]
    reserve := (56096772399/250000000000) }

theorem quarter_007_027_valid : quarter_007_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_027]
  · intro i; fin_cases i <;> norm_num [quarter_007_027]
  · norm_num [quarter_007_027]
  · norm_num [quarter_007_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_027]

def quarter_007_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![0, (36405811/100000000), (6359419/20000000), (6359419/20000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1820291/100000000), 0, (36405811/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9418557/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7891253/100000000), (1/100000000), (330621/4000000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-270347461424974101335953/1739342638742000000000000), (231519806183809/157825060000000), (-903569255127799398955953/869671319371000000000000), (231519806183809/157825060000000), (-1536791048830624696575953/1739342638742000000000000)]
    bernstein := [(1122451276963051263800119143967/4452717155179520000000000000000), (577020514566640413942499476413/2226358577589760000000000000000), (296388138174701441262521396007/1113179288794880000000000000000), (152123923059908922026598318773/556589644397440000000000000000), (78022595281454633229113299247/278294822198720000000000000000)]
    reserve := (63020580347/250000000000) }

theorem quarter_007_028_valid : quarter_007_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_028]
  · intro i; fin_cases i <;> norm_num [quarter_007_028]
  · norm_num [quarter_007_028]
  · norm_num [quarter_007_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_028]

def quarter_007_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 0, 0, 0, 0, 2, 3]
    lambda := ![0, (18065267/50000000), (31934733/100000000), (31934733/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(1806527/100000000), 0, (18065267/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4729663/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1/100000000), (7521979/100000000), (1/100000000), (1037663/12500000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-33033068582385389662375369/187326703081848000000000000), (576909478218711/376098950000000), (-100715206730451529130695369/93663351540924000000000000), (576909478218711/376098950000000), (-168397344878517668599015369/187326703081848000000000000)]
    bernstein := [(8424924075555363969161956994231/29972272493095680000000000000000), (3459195350074546588027607016739/11988908997238272000000000000000), (4257917371100188346554632722669/14386690796685926400000000000000), (581950384830825093161923369403/1918225439558123520000000000000), (238462740826374681457846458599/767290175823249408000000000000)]
    reserve := (28109060057/100000000000) }

theorem quarter_007_029_valid : quarter_007_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_007_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_007_029]
  · intro i; fin_cases i <;> norm_num [quarter_007_029]
  · norm_num [quarter_007_029]
  · norm_num [quarter_007_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_007_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_007_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_007_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_007_029]

def quarterTable007 : OwnerTable where
  mode := .quarter
  owners := ![0, 0, 0, 0, 0, 2, 3]
  rows := [quarter_007_000, quarter_007_001, quarter_007_002, quarter_007_003, quarter_007_004, quarter_007_005, quarter_007_006, quarter_007_007, quarter_007_008, quarter_007_009, quarter_007_010, quarter_007_011, quarter_007_012, quarter_007_013, quarter_007_014, quarter_007_015, quarter_007_016, quarter_007_017, quarter_007_018, quarter_007_019, quarter_007_020, quarter_007_021, quarter_007_022, quarter_007_023, quarter_007_024, quarter_007_025, quarter_007_026, quarter_007_027, quarter_007_028, quarter_007_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_007_000_valid
    · exact quarter_007_001_valid
    · exact quarter_007_002_valid
    · exact quarter_007_003_valid
    · exact quarter_007_004_valid
    · exact quarter_007_005_valid
    · exact quarter_007_006_valid
    · exact quarter_007_007_valid
    · exact quarter_007_008_valid
    · exact quarter_007_009_valid
    · exact quarter_007_010_valid
    · exact quarter_007_011_valid
    · exact quarter_007_012_valid
    · exact quarter_007_013_valid
    · exact quarter_007_014_valid
    · exact quarter_007_015_valid
    · exact quarter_007_016_valid
    · exact quarter_007_017_valid
    · exact quarter_007_018_valid
    · exact quarter_007_019_valid
    · exact quarter_007_020_valid
    · exact quarter_007_021_valid
    · exact quarter_007_022_valid
    · exact quarter_007_023_valid
    · exact quarter_007_024_valid
    · exact quarter_007_025_valid
    · exact quarter_007_026_valid
    · exact quarter_007_027_valid
    · exact quarter_007_028_valid
    · exact quarter_007_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
