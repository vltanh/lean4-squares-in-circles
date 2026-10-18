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

def quarter_031_000 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/8), (-7/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(102465129/100000000), 0, (19192791/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(560543/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9336687063886503438164777/457463486508250000000000), (-64079547/560543), (-40663458022347003438164777/228731743254125000000000), (-64079547/560543), (-71990228980807503438164777/457463486508250000000000)]
    bernstein := [(703685342559292178019903367/1873770440737792000000000000), (1875854259774222321528801499/4684426101844480000000000000), (14277826683957307031840585677/35133195763833600000000000000), (11531305198752544833786737987/29277663136528000000000000000), (26588901590914354362542792023/73194157841320000000000000000)]
    reserve := (36326535307/100000000000) }

theorem quarter_031_000_valid : quarter_031_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_000]
  · intro i; fin_cases i <;> norm_num [quarter_031_000]
  · norm_num [quarter_031_000]
  · norm_num [quarter_031_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_000]

def quarter_031_001 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/20), (-13/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(100371721/100000000), 0, (19887081/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(71153/12500000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8208487042318949692827207/464548117886000000000000), (-60597559/569224), (-40668488900274449692827207/232274058943000000000000), (-60597559/569224), (-73128490758229949692827207/464548117886000000000000)]
    bernstein := [(25542887225243746976342241593/74327698861760000000000000000), (54783549554092372087240394787/148655397723520000000000000000), (111418677708706730449600452033/297310795447040000000000000000), (215717198152734591859305697947/594621590894080000000000000000), (396003581849212929304558675273/1189243181788160000000000000000)]
    reserve := (83246973351/250000000000) }

theorem quarter_031_001_valid : quarter_031_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_001]
  · intro i; fin_cases i <;> norm_num [quarter_031_001]
  · norm_num [quarter_031_001]
  · norm_num [quarter_031_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_001]

def quarter_031_002 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-13/40), (-3/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(19608541/20000000), 0, (41103203/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(577517/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1426099006298046362438957/94263219891350000000000), (-56939502/577517), (-8135027509922696362438957/47131609945675000000000), (-56939502/577517), (-14843956013547346362438957/94263219891350000000000)]
    bernstein := [(74943659209813187891663083523/241313842921856000000000000000), (20236252696962981297167944413/60328460730464000000000000000), (15471642832850517916961408309/45246345547848000000000000000), (1246171032223673960933468593/3770528795654000000000000000), (284174818686034867862751883/942632198913500000000000000)]
    reserve := (301469458621/1000000000000) }

theorem quarter_031_002_valid : quarter_031_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_002]
  · intro i; fin_cases i <;> norm_num [quarter_031_002]
  · norm_num [quarter_031_002]
  · norm_num [quarter_031_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_002]

def quarter_031_003 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/10), (-11/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(47737769/50000000), 0, (84730841/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(585377/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-9773973405635598256572169/764369130194800000000000), (-106220235/1170754), (-65093570208929798256572169/382184565097400000000000), (-106220235/1170754), (-120413167012223998256572169/764369130194800000000000)]
    bernstein := [(2111975726260626713666060111/7643691301948000000000000000), (9208591601509896784563339707/30574765207792000000000000000), (37663862899051992598321534059/122299060831168000000000000000), (145308269583885004690215666383/489196243324672000000000000000), (525814725929969699756030396871/1956784973298688000000000000000)]
    reserve := (16794599723/62500000000) }

theorem quarter_031_003_valid : quarter_031_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_003]
  · intro i; fin_cases i <;> norm_num [quarter_031_003]
  · norm_num [quarter_031_003]
  · norm_num [quarter_031_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_003]

def quarter_031_004 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-11/40), (-1/4)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(231673/250000), 0, (21776787/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(592757/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-8238678976211038309129793/774005730506800000000000), (-49115626/592757), (-65109733826768638309129793/387002865253400000000000), (-49115626/592757), (-121980788677326238309129793/774005730506800000000000)]
    bernstein := [(477272706590133896248704771087/1981454670097408000000000000000), (52661339155095844167884088237/198145467009740800000000000000), (16217359561567344995261091973/59443640102922240000000000000), (519868938481048435359691749/1981454670097408000000000000), (46506272043574728661489823/198145467009740800000000000)]
    reserve := (9388309053/40000000000) }

theorem quarter_031_004_valid : quarter_031_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_004]
  · intro i; fin_cases i <;> norm_num [quarter_031_004]
  · norm_num [quarter_031_004]
  · norm_num [quarter_031_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_004]

def quarter_031_005 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/4), (-9/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(22406079/25000000), 0, (44660553/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(299807/50000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-17030661182269892909521343/1957398529634000000000000), (-44963763/599614), (-162821954872612892909521343/978699264817000000000000), (-44963763/599614), (-308613248562955892909521343/1957398529634000000000000)]
    bernstein := [(102349856194342949148331873/501094023586304000000000000), (1148422154004984670945181561/5010940235863040000000000000), (826745766726247431323963401/3496004815718400000000000000), (113485721831883046226991188473/501094023586304000000000000000), (999296720257540176098060282977/5010940235863040000000000000000)]
    reserve := (99711498563/500000000000) }

theorem quarter_031_005_valid : quarter_031_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_005]
  · intro i; fin_cases i <;> norm_num [quarter_031_005]
  · norm_num [quarter_031_005]
  · norm_num [quarter_031_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_005]

def quarter_031_006 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-9/40), (-1/5)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(345373/400000), 0, (22839737/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(37869/6250000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-1719924153567237495332851/247241475078000000000000), (-847162/12623), (-20359610527228987495332851/123620737539000000000000), (-847162/12623), (-12999765633630245831777617/82413825026000000000000)]
    bernstein := [(8102730097404880342365201953/48687552015360000000000000000), (15141896346211681502204791021/79117272024960000000000000000), (113495363872629455994497791/570557250180000000000000000), (39006384597562700060214611/206034562565000000000000000), (483828052294162560672937/2971652344687500000000000)]
    reserve := (40703621771/250000000000) }

theorem quarter_031_006_valid : quarter_031_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_006]
  · intro i; fin_cases i <;> norm_num [quarter_031_006]
  · norm_num [quarter_031_006]
  · norm_num [quarter_031_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_006]

def quarter_031_007 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/5), (-7/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, 0, 0, 0, 0, 0, 1]
    cone := fun i => (![![(82830189/100000000), 0, (93207547/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (26115447/100000000), 0, 0]] i.1) i.2
    mu := ![(611587/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (1/100000000), (3264431/12500000)]
    alternative := .zero
    polynomial := [(-2160864767049455192679741/399296712399400000000000), (-72452831/1223174), (-32587825353125155192679741/199648356199700000000000), (-72452831/1223174), (-63014785939200855192679741/399296712399400000000000)]
    bernstein := [(7944486300681222437123771/62390111312406250000000000), (152061772474782676498816969/998241780998500000000000000), (1917553159418961854195085037/11978901371982000000000000000), (19273738542380305840119167837/127774947967808000000000000000), (127591957454070811210055593059/1022199583742464000000000000000)]
    reserve := (15602622947/125000000000) }

theorem quarter_031_007_valid : quarter_031_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_007]
  · intro i; fin_cases i <;> norm_num [quarter_031_007]
  · norm_num [quarter_031_007]
  · norm_num [quarter_031_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_007]

def quarter_031_008 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-7/40), (-3/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(7920889/100000000), (13954759/50000000), (13954759/50000000), (13954759/50000000), 0, 0, (8350557/100000000)]
    cone := fun i => (![![(264411/10000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (330681/4000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (436157/20000000), 0, 0]] i.1) i.2
    mu := ![(12873/25000000), (397887/5000000), (1/100000000), (1/100000000), (3627483/50000000), (1/100000000), (1090393/50000000)]
    alternative := .zero
    polynomial := [(-632199600481181443875058666756913/2572630399960883052504000000000000), (-79589455789392823/17421766500000000), (-17873516908509101909877195726106913/1286315199980441526252000000000000), (-79589455789392823/17421766500000000), (-35114834216537022375879332785456913/2572630399960883052504000000000000)]
    bernstein := [(921186148068183067392154397214139273487/6585933823899860614410240000000000000000), (464046397103329171021443873726494930123/3292966911949930307205120000000000000000), (694043745627294811047635173120157068501/4939450367924895460807680000000000000000), (38050459331659428545826498945888986881/274413909329160858933760000000000000000), (55727752796573775985955201694320056447/411620863993741288400640000000000000000)]
    reserve := (27077224539/200000000000) }

theorem quarter_031_008_valid : quarter_031_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_008]
  · intro i; fin_cases i <;> norm_num [quarter_031_008]
  · norm_num [quarter_031_008]
  · norm_num [quarter_031_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_008]

def quarter_031_009 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/20), (-1/8)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(1738323/20000000), (13713631/50000000), (13713631/50000000), (13713631/50000000), 0, 0, (45133/500000)]
    cone := fun i => (![![(1218127/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (8124177/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2357337/100000000), 0, 0]] i.1) i.2
    mu := ![(28027/50000000), (7860273/100000000), (1/100000000), (1/100000000), (1425921/20000000), (1/100000000), (2357337/100000000)]
    alternative := .zero
    polynomial := [(-54490180723046715272363366854889599/329115899400967485635052000000000000), (-15305192226787770249/3671664522850000000), (-2447985689676027481274395727441129599/164557949700483742817526000000000000), (-15305192226787770249/3671664522850000000), (-4841481198629008247276428088027369599/329115899400967485635052000000000000)]
    bernstein := [(6930510883419188441713471702857005309681/52658543904154797701608320000000000000000), (2800060646426271450927919020893360463467/21063417561661919080643328000000000000000), (20832562867703175942205952341984812043/156994416608660266439577600000000000000), (88240390840952309106500542658702907719/674029361973181410580586496000000000000), (6880647531329092369041617123247433769/53922348957854512846446919680000000000)]
    reserve := (127602889419/1000000000000) }

theorem quarter_031_009_valid : quarter_031_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_009]
  · intro i; fin_cases i <;> norm_num [quarter_031_009]
  · norm_num [quarter_031_009]
  · norm_num [quarter_031_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_009]

def quarter_031_010 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/8), (-1/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(470561/5000000), (13489381/50000000), (13489381/50000000), (13489381/50000000), 0, 0, (1930499/20000000)]
    cone := fun i => (![![(536167/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (249729/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (315099/12500000), 0, 0]] i.1) i.2
    mu := ![(15073/25000000), (1938221/25000000), (1/100000000), (1/100000000), (7013019/100000000), (1/100000000), (2520793/100000000)]
    alternative := .zero
    polynomial := [(-3533037048284160540509720202290837/39728470105080439698147000000000000), (-626503470354696631/171851794900000000), (-313545049119134143064544415307555837/19864235052540219849073500000000000), (-626503470354696631/171851794900000000), (-623557061189984125588579110412820837/39728470105080439698147000000000000)]
    bernstein := [(803406502655760437651983731596814547/6509112542016379240144404480000000000), (1695141077566375731479507495209393213/13560651129200790083634176000000000000), (95291700232042711476017498523259351981/762786626017544442204422400000000000000), (13053022806728344135578464236947422501/105942586946881172528392000000000000000), (47619646711470693053729274696256941763/397284701050804396981470000000000000000)]
    reserve := (23972554989/200000000000) }

theorem quarter_031_010_valid : quarter_031_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_010]
  · intro i; fin_cases i <;> norm_num [quarter_031_010]
  · norm_num [quarter_031_010]
  · norm_num [quarter_031_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_010]

def quarter_031_011 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/10), (-3/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(10080943/100000000), (26560853/100000000), (26560853/100000000), (26560853/100000000), 0, 0, (10236499/100000000)]
    cone := fun i => (![![(111111/6250000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (393377/5000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (2673307/100000000), 0, 0]] i.1) i.2
    mu := ![(32119/50000000), (7635567/100000000), (1/100000000), (1/100000000), (3452193/50000000), (1/100000000), (668327/25000000)]
    alternative := .zero
    polynomial := [(-3971193006194984530545642421157887/188610613322830957110501000000000000), (-73904589923593418341/24524677647300000000), (-1569012299325563705596757572207945387/94305306661415478555250500000000000), (-73904589923593418341/24524677647300000000), (-3134053405644932426662969501994732887/188610613322830957110501000000000000)]
    bernstein := [(217409333721900820392539045406569019713/1886106133228309571105010000000000000000), (883316303778713844600720093455851575439/7544424532913238284420040000000000000000), (10606165492438717689170060377206688676951/90533094394958859413040480000000000000000), (13941389864892184325822452735216900656251/120710792526611812550720640000000000000000), (54133992361374472424584997023970712370553/482843170106447250202882560000000000000000)]
    reserve := (56057531423/500000000000) }

theorem quarter_031_011_valid : quarter_031_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_011]
  · intro i; fin_cases i <;> norm_num [quarter_031_011]
  · norm_num [quarter_031_011]
  · norm_num [quarter_031_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_011]

def quarter_031_012 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-3/40), (-1/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(2140373/20000000), (13085389/50000000), (13085389/50000000), (13085389/50000000), 0, 0, (5392901/50000000)]
    cone := fun i => (![![(1342979/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1937999/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (70419/2500000), 0, 0]] i.1) i.2
    mu := ![(67917/100000000), (3754217/50000000), (1/100000000), (1/100000000), (6802987/100000000), (1/100000000), (2816761/100000000)]
    alternative := .zero
    polynomial := [(328331791103472402677342252104141073/9771865976024943217151646000000000000), (-2328602426829543337/1019900623956000000), (-28422604877739777292599737408700146309/1628644329337490536191941000000000000), (-2328602426829543337/1019900623956000000), (-170863961057542136158275766704305018927/9771865976024943217151646000000000000)]
    bernstein := [(2678744089690775317478787996184235659249313/25015976898623854635908213760000000000000000), (454941056455148928380669165340064006101657/4169329483103975772651368960000000000000000), (683718322961405314610578110301883801176457/6253994224655963658977053440000000000000000), (112279768041529688138376920214232990983073/1042332370775993943162842240000000000000000), (163080523886553995759463961845734505519473/1563498556163990914744263360000000000000000)]
    reserve := (104304876549/1000000000000) }

theorem quarter_031_012_valid : quarter_031_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_012]
  · intro i; fin_cases i <;> norm_num [quarter_031_012]
  · norm_num [quarter_031_012]
  · norm_num [quarter_031_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_012]

def quarter_031_013 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/20), (-1/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(2818743/25000000), (258061/1000000), (258061/1000000), (258061/1000000), 0, 0, (11306727/100000000)]
    cone := fun i => (![![(423407/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (955497/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1476401/50000000), 0, 0]] i.1) i.2
    mu := ![(71353/100000000), (1842927/25000000), (1/100000000), (1/100000000), (6708191/100000000), (1/100000000), (2952803/100000000)]
    alternative := .zero
    polynomial := [(3783454813943514061698741911307299/53157455379036316034187000000000000), (-3207018646932678751/2191639503850000000), (-484803968038992496437014582672072701/26578727689518158017093500000000000), (-3207018646932678751/2191639503850000000), (-973391390891928506935727907255452701/53157455379036316034187000000000000)]
    bernstein := [(840372899085715415823595122687086626499/8505192860645810565469920000000000000000), (572967917289488183516842074310871162033/5670128573763873710313280000000000000000), (10347862025725453138456519078216535476697/102062314327749726785639040000000000000000), (2264148895828608069254753458434063161633/22680514295055494841253120000000000000000), (13114657577111495590394311819628222144099/136083085770332969047518720000000000000000)]
    reserve := (3011638419/31250000000) }

theorem quarter_031_013_valid : quarter_031_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_013]
  · intro i; fin_cases i <;> norm_num [quarter_031_013]
  · norm_num [quarter_031_013]
  · norm_num [quarter_031_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_013]

def quarter_031_014 : Row :=
  { mode := .quarter
    positive := false
    interval := ⟨(-1/40), 0⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(11801199/100000000), (12732319/50000000), (12732319/50000000), (12732319/50000000), 0, 0, (11804887/100000000)]
    cone := fun i => (![![(73769/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (471427/6250000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3082899/100000000), 0, 0]] i.1) i.2
    mu := ![(37283/50000000), (3612857/50000000), (1/100000000), (1/100000000), (6619429/100000000), (1/100000000), (30829/1000000)]
    alternative := .zero
    polynomial := [(17707061618172511153335129398049/200641618244497476083000000000000), (-302018549436712359/538792590124000000), (-1907681468081717370889303215924451/100320809122248738041500000000000), (-302018549436712359/538792590124000000), (-3833069997781607252931941561246951/200641618244497476083000000000000)]
    bernstein := [(46424181905824797311705599785355949849/513642542705913538772480000000000000000), (59596783076215432425633315374054773/642053178382391923465600000000000000), (89834357270254186839634968199710749/963079767573587885198400000000000000), (36819986355325824530527685942973/401283236488994952166000000000000), (17707061618172511153335129398049/200641618244497476083000000000000)]
    reserve := (5515761689/62500000000) }

theorem quarter_031_014_valid : quarter_031_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_014]
  · intro i; fin_cases i <;> norm_num [quarter_031_014]
  · norm_num [quarter_031_014]
  · norm_num [quarter_031_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_014]

def quarter_031_015 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨0, (1/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(3037653/25000000), (25018389/100000000), (25018389/100000000), (25018389/100000000), 0, 0, (12794221/100000000)]
    cone := fun i => (![![0, 0, (639611/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7410649/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (835317/25000000), 0, 0]] i.1) i.2
    mu := ![(16163/20000000), (7027763/100000000), (1/100000000), (1/100000000), (1625857/25000000), (1/100000000), (3341269/100000000)]
    alternative := .zero
    polynomial := [(787089331903611839197727658093365699/9873084393644084917338832000000000000), (19387143964857846639/16227104767000000000), (-101642213310548677525058235182765626301/4936542196822042458669416000000000000), (19387143964857846639/16227104767000000000), (-204071515953000966889314198023624618301/9873084393644084917338832000000000000)]
    bernstein := [(787089331903611839197727658093365699/9873084393644084917338832000000000000), (860812783832182662917616470375976599/9873084393644084917338832000000000000), (4384131718341068058334967121578454368899/47390805089491607603226393600000000000000), (1511647010444298789870492205535434422999/15796935029830535867742131200000000000000), (2444889513404445627462575864108686886418499/25275096047728857388387409920000000000000000)]
    reserve := (79720713459/1000000000000) }

theorem quarter_031_015_valid : quarter_031_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_015]
  · intro i; fin_cases i <;> norm_num [quarter_031_015]
  · norm_num [quarter_031_015]
  · norm_num [quarter_031_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_015]

def quarter_031_016 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/40), (1/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(1577423/12500000), (25109501/100000000), (25109501/100000000), (25109501/100000000), 0, 0, (6026057/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (7437637/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3147463/100000000), 0, 0]] i.1) i.2
    mu := ![(6853/2000000), (1739263/25000000), (1/100000000), (1/100000000), (6527113/100000000), (1/100000000), (393433/12500000)]
    alternative := .zero
    polynomial := [(901556662887146197024111035392297/11130257502919708722884000000000000), (12114020069581/17392630000000), (-292543239445032161926880940050625533/61216416266058397975862000000000000), (12114020069581/17392630000000), (-595003602181822932021027101490566333/122432832532116795951724000000000000)]
    bernstein := [(29912103194925886617586283063017143248067/313428051282218997636413440000000000000000), (15405197369765864575665703265889107914467/156714025641109498818206720000000000000000), (23665330287266686184191740539959480169401/235071038461664248227310080000000000000000), (4017812233778004147374551507210814234067/39178506410277374704551680000000000000000), (2036014371397593212953690371754027727267/19589253205138687352275840000000000000000)]
    reserve := (47717654933/500000000000) }

theorem quarter_031_016_valid : quarter_031_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_016]
  · intro i; fin_cases i <;> norm_num [quarter_031_016]
  · norm_num [quarter_031_016]
  · norm_num [quarter_031_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_016]

def quarter_031_017 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/20), (3/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(1625663/12500000), (2498299/10000000), (2498299/10000000), (2498299/10000000), 0, 0, (6022863/50000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1850041/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (629159/20000000), 0, 0]] i.1) i.2
    mu := ![(531583/100000000), (1704967/25000000), (1/100000000), (1/100000000), (6494227/100000000), (1/100000000), (786449/25000000)]
    alternative := .zero
    polynomial := [(347482961190248971953763351456160089/4628977723706729145727403000000000000), (664690084711/926612500000), (-7629808390618229737368898463887859911/2314488861853364572863701500000000000), (664690084711/926612500000), (-15607099742426708446691560279231879911/4628977723706729145727403000000000000)]
    bernstein := [(76108392600818623036983014094932537631289/740636435793076663316384480000000000000000), (155840103104072818370295744414800391818267/1481272871586153326632768960000000000000000), (953781396991889796161595015139328155439603/8887637229516919959796613760000000000000000), (646349693043098000164080166061450469030403/5925091486344613306531075840000000000000000), (1309679779027155424569170111571391212930409/11850182972689226613062151680000000000000000)]
    reserve := (102760799931/1000000000000) }

theorem quarter_031_017_valid : quarter_031_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_017]
  · intro i; fin_cases i <;> norm_num [quarter_031_017]
  · norm_num [quarter_031_017]
  · norm_num [quarter_031_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_017]

def quarter_031_018 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/40), (1/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(6696323/50000000), (2485947/10000000), (2485947/10000000), (2485947/10000000), 0, 0, (12028943/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (920447/12500000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (785353/25000000), 0, 0]] i.1) i.2
    mu := ![(362661/50000000), (6675893/100000000), (1/100000000), (1/100000000), (3231059/50000000), (1/100000000), (3141413/100000000)]
    alternative := .zero
    polynomial := [(952355903532368682152275393859297/13899458666392806828696375000000000), (246770977099909/333794650000000), (-8969419097137083492249105069295039/3474864666598201707174093750000000), (246770977099909/333794650000000), (-12276677430693567550382898557013151/4633152888797602276232125000000000)]
    bernstein := [(3902446882432715315959463761827803977907/35582614185965585481462720000000000000000), (142233290752958166932320787974635770117/1270807649498770910052240000000000000000), (760000329889827059558599134208551287869/6671740159868547277774260000000000000000), (21431500023976759196431587998215858597/185326115551904091049285000000000000000), (16277446538304658034148830588249489947/138994586663928068286963750000000000000)]
    reserve := (21934570979/200000000000) }

theorem quarter_031_018_valid : quarter_031_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_018]
  · intro i; fin_cases i <;> norm_num [quarter_031_018]
  · norm_num [quarter_031_018]
  · norm_num [quarter_031_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_018]

def quarter_031_019 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/10), (1/8)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(1722503/12500000), (24740013/100000000), (24740013/100000000), (24740013/100000000), 0, 0, (11999937/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (114503/1562500), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (3133837/100000000), 0, 0]] i.1) i.2
    mu := ![(18461/2000000), (1631377/25000000), (1/100000000), (1/100000000), (3215533/50000000), (1/100000000), (1566919/50000000)]
    alternative := .zero
    polynomial := [(1861004952197448648965008754314663/30348628591919239590623800000000000), (15547791958947/20392212500000), (-32831213833629759732847677745542377/15174314295959619795311900000000000), (15547791958947/20392212500000), (-67523432619456968114660364245399417/30348628591919239590623800000000000)]
    bernstein := [(35346611835161794564493863851202195183/303486285919192395906238000000000000000), (28798815869680904434563413937758844723/242789028735353916724990400000000000000), (70243277147181633560034104276334548881/582693668964849400139976960000000000000), (3799656619776455977075381173388389771/31076995678125301340798771200000000000), (615400232958513390943305878200036639/4972319308500048214527803392000000000)]
    reserve := (116468563737/1000000000000) }

theorem quarter_031_019_valid : quarter_031_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_019]
  · intro i; fin_cases i <;> norm_num [quarter_031_019]
  · norm_num [quarter_031_019]
  · norm_num [quarter_031_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_019]

def quarter_031_020 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/8), (3/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![(3541583/25000000), (24625513/100000000), (24625513/100000000), (24625513/100000000), 0, 0, (1494641/12500000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1823569/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (1561329/50000000), 0, 0]] i.1) i.2
    mu := ![(562037/50000000), (6369129/100000000), (1/100000000), (1/100000000), (3200651/50000000), (1/100000000), (1561329/50000000)]
    alternative := .zero
    polynomial := [(583431006961793582372022770156311/10921035080612779491946500000000000), (25058308711567/31845645000000), (-10334477735521073257427541979068689/5460517540306389745973250000000000), (25058308711567/31845645000000), (-3036055211143420013889586675470527/1560147868658968498849500000000000)]
    bernstein := [(220569632461428813643961375077566559/1789302387607597791960514560000000000), (5207440080155210053355857507356092731/41537376855176377313369088000000000000), (1387788205103277891851299007580062414089/10903561424483799044759385600000000000000), (1172161518452402350716204088399994560681/9086301187069832537299488000000000000000), (2965320116400575486821059195026982335083/22715752967674581343248720000000000000000)]
    reserve := (24654260117/200000000000) }

theorem quarter_031_020_valid : quarter_031_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_020]
  · intro i; fin_cases i <;> norm_num [quarter_031_020]
  · norm_num [quarter_031_020]
  · norm_num [quarter_031_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_020]

def quarter_031_021 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/20), (7/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4940969/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2049999/25000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(101436319681669357494871/4736790009369600000000000), (1168077766097/1453900000000), (-1572633276507981179868329/2368395004684800000000000), (1168077766097/1453900000000), (-3246702872697631717231529/4736790009369600000000000)]
    bernstein := [(98032908678325882668079957351/757886401499136000000000000000), (202215919043560450421982748619/1515772802998272000000000000000), (1249821912686529486565463632333/9094636817989632000000000000000), (857325354090093686630341285459/6063091211993088000000000000000), (1762407155066361193701472631671/12126182423986176000000000000000)]
    reserve := (64675199663/500000000000) }

theorem quarter_031_021_valid : quarter_031_021.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_021]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_021]
  · intro i; fin_cases i <;> norm_num [quarter_031_021]
  · norm_num [quarter_031_021]
  · norm_num [quarter_031_021, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_021, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_021, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_021, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_021]

def quarter_031_022 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/40), (1/5)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5274893/25000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (2011119/25000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(45349196563992031633783/4646952699417600000000000), (5328174694193/6094300000000), (-1605204421090898293428617/2323476349708800000000000), (5328174694193/6094300000000), (-3255758038745788618491017/4646952699417600000000000)]
    bernstein := [(1732445749747919635624903122583/11896198910509056000000000000000), (74346976331178249565528954723/495674954604544000000000000000), (21512839003361566058568320569/139408580982528000000000000000), (47244793575154686759879827/297881583296000000000000000), (9095925938230271731616779/55852796868000000000000000)]
    reserve := (145630193541/1000000000000) }

theorem quarter_031_022_valid : quarter_031_022.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_022]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_022]
  · intro i; fin_cases i <;> norm_num [quarter_031_022]
  · norm_num [quarter_031_022]
  · norm_num [quarter_031_022, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_022, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_022, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_022, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_022]

def quarter_031_023 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/5), (9/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (22374263/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7871407/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-351539038227236775500109/90939561524864000000000000), (745808759208579/787140700000000), (-32818836399567059915372109/45469780762432000000000000), (745808759208579/787140700000000), (-65286133760906883055244109/90939561524864000000000000)]
    bernstein := [(178373744093408921053826583/1093023576020000000000000000), (2935902891708917972665581219/17488377216320000000000000000), (156896104304976514450418026799/909395615248640000000000000000), (5155063760000460926358710429139/29100659687956480000000000000000), (42308335497210173836153826508051/232805277503651840000000000000000)]
    reserve := (163192952107/1000000000000) }

theorem quarter_031_023_valid : quarter_031_023.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_023]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_023]
  · intro i; fin_cases i <;> norm_num [quarter_031_023]
  · norm_num [quarter_031_023]
  · norm_num [quarter_031_023, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_023, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_023, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_023, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_023]

def quarter_031_024 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(9/40), (1/4)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4717031/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (7681887/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1738650352648571444836189/88750008157824000000000000), (52411455031441/51212580000000), (-33592676758870970863876189/44375004078912000000000000), (52411455031441/51212580000000), (-65446703165093370282916189/88750008157824000000000000)]
    bernstein := [(41377683598646380186429202855171/227200020884029440000000000000000), (327078396565262875158427721783/1747692468338688000000000000000), (1309674936113106624367396558889/6816000626520883200000000000000), (3444993985033524198079042231/17476924683386880000000000000), (4590771716770908322921381379/22720002088402944000000000000)]
    reserve := (182120069521/1000000000000) }

theorem quarter_031_024_valid : quarter_031_024.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_024]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_024]
  · intro i; fin_cases i <;> norm_num [quarter_031_024]
  · norm_num [quarter_031_024]
  · norm_num [quarter_031_024, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_024, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_024, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_024, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_024]

def quarter_031_025 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(1/4), (11/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (772813/3125000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (3738543/50000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-324565868615193799479241/8638391107507200000000000), (8586811025243/7788631250000), (-3442120901450736492701641/4319195553753600000000000), (8586811025243/7788631250000), (-6559675934286279185924041/8638391107507200000000000)]
    bernstein := [(447812089681361374011145751/2211428123521843200000000000), (1532478906464409420969857071/7371427078406144000000000000), (141484965223149880082168685101/663428437056552960000000000000), (161144563357774173623168390023/737142707840614400000000000000), (4951973979386289843594111200519/22114281235218432000000000000000)]
    reserve := (25312380997/125000000000) }

theorem quarter_031_025_valid : quarter_031_025.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_025]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_025]
  · intro i; fin_cases i <;> norm_num [quarter_031_025]
  · norm_num [quarter_031_025]
  · norm_num [quarter_031_025, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_025, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_025, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_025, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_025]

def quarter_031_026 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(11/40), (3/10)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (5161433/20000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (907279/12500000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-607935026077572796343673/10481932193408000000000000), (172047764946189/145164640000000), (-4412489573266026944003673/5240966096704000000000000), (172047764946189/145164640000000), (-8217044120454481091663673/10481932193408000000000000)]
    bernstein := [(6022123309852760320111119098007/26833746415124480000000000000000), (1544347953192846047296538526111/6708436603781120000000000000000), (395752862800068091199062823803/1677109150945280000000000000000), (101345611395785646178113625419/419277287736320000000000000000), (25936083643372049408747901087/104819321934080000000000000000)]
    reserve := (28052937599/125000000000) }

theorem quarter_031_026_valid : quarter_031_026.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_026]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_026]
  · intro i; fin_cases i <;> norm_num [quarter_031_026]
  · norm_num [quarter_031_026]
  · norm_num [quarter_031_026, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_026, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_026, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_026, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_026]

def quarter_031_027 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(3/10), (13/40)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (26815469/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (1405319/20000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-1316551873099029153020757/16235864015488000000000000), (893848957728177/702659500000000), (-7244845134492575946255957/8117932007744000000000000), (893848957728177/702659500000000), (-13173138395886122739491157/16235864015488000000000000)]
    bernstein := [(40263830410692127132565083683/162358640154880000000000000000), (165083694140515564695496326393/649434560619520000000000000000), (676398016655881345246982439903/2597738242478080000000000000000), (2769656141859305891713732014213/10390952969912320000000000000000), (11334160612480689253697056639323/41563811879649280000000000000000)]
    reserve := (247993148823/1000000000000) }

theorem quarter_031_027_valid : quarter_031_027.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_027]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_027]
  · intro i; fin_cases i <;> norm_num [quarter_031_027]
  · norm_num [quarter_031_027]
  · norm_num [quarter_031_027, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_027, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_027, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_027, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_027]

def quarter_031_028 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(13/40), (7/20)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (13877157/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6783467/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-8393981810590607474775969/78370425337984000000000000), (462571895374281/339173350000000), (-37189538371110772323351969/39185212668992000000000000), (462571895374281/339173350000000), (-65985094931630937171927969/78370425337984000000000000)]
    bernstein := [(54834484819889220019157231002191/200628288865239040000000000000000), (28084001816314697118210510549549/100314144432619520000000000000000), (14374581548409025918218067513111/50157072216309760000000000000000), (7353207941169859319923060649829/25078536108154880000000000000000), (3759385042572018843493375121631/12539268054077440000000000000000)]
    reserve := (273313823937/1000000000000) }

theorem quarter_031_028_valid : quarter_031_028.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_028]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_028]
  · intro i; fin_cases i <;> norm_num [quarter_031_028]
  · norm_num [quarter_031_028]
  · norm_num [quarter_031_028, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_028, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_028, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_028, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_028]

def quarter_031_029 : Row :=
  { mode := .quarter
    positive := true
    interval := ⟨(7/20), (3/8)⟩
    owners := ![0, 2, 0, 0, 0, 2, 3]
    lambda := ![0, (33333333/100000000), (33333333/100000000), (33333333/100000000), 0, 0, 0]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (28623581/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (9873603/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1/100000000), (6530147/100000000), (1/100000000), (1/100000000), (270777/3125000), (1/100000000), (1/100000000)]
    alternative := .zero
    polynomial := [(-791352488847721368036173/5803367759488000000000000), (954119357125473/653014700000000), (-2937790811621204592324173/2901683879744000000000000), (954119357125473/653014700000000), (-5084229134394687816612173/5803367759488000000000000)]
    bernstein := [(279023570419861849652590111027/928538841518080000000000000000), (114253662594494344577861152463/371415536607232000000000000000), (140271802598845565369771974273/445698643928678400000000000000), (19124525956096234960326270151/59426485857157120000000000000), (7818190784798868847520642083/23770594342862848000000000000)]
    reserve := (300497467573/1000000000000) }

theorem quarter_031_029_valid : quarter_031_029.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [quarter_031_029]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [quarter_031_029]
  · intro i; fin_cases i <;> norm_num [quarter_031_029]
  · norm_num [quarter_031_029]
  · norm_num [quarter_031_029, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [quarter_031_029, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [quarter_031_029, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [quarter_031_029, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [quarter_031_029]

def quarterTable031 : OwnerTable where
  mode := .quarter
  owners := ![0, 2, 0, 0, 0, 2, 3]
  rows := [quarter_031_000, quarter_031_001, quarter_031_002, quarter_031_003, quarter_031_004, quarter_031_005, quarter_031_006, quarter_031_007, quarter_031_008, quarter_031_009, quarter_031_010, quarter_031_011, quarter_031_012, quarter_031_013, quarter_031_014, quarter_031_015, quarter_031_016, quarter_031_017, quarter_031_018, quarter_031_019, quarter_031_020, quarter_031_021, quarter_031_022, quarter_031_023, quarter_031_024, quarter_031_025, quarter_031_026, quarter_031_027, quarter_031_028, quarter_031_029]
  valid := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quarter_031_000_valid
    · exact quarter_031_001_valid
    · exact quarter_031_002_valid
    · exact quarter_031_003_valid
    · exact quarter_031_004_valid
    · exact quarter_031_005_valid
    · exact quarter_031_006_valid
    · exact quarter_031_007_valid
    · exact quarter_031_008_valid
    · exact quarter_031_009_valid
    · exact quarter_031_010_valid
    · exact quarter_031_011_valid
    · exact quarter_031_012_valid
    · exact quarter_031_013_valid
    · exact quarter_031_014_valid
    · exact quarter_031_015_valid
    · exact quarter_031_016_valid
    · exact quarter_031_017_valid
    · exact quarter_031_018_valid
    · exact quarter_031_019_valid
    · exact quarter_031_020_valid
    · exact quarter_031_021_valid
    · exact quarter_031_022_valid
    · exact quarter_031_023_valid
    · exact quarter_031_024_valid
    · exact quarter_031_025_valid
    · exact quarter_031_026_valid
    · exact quarter_031_027_valid
    · exact quarter_031_028_valid
    · exact quarter_031_029_valid

  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  cover := by decide

end SquaresInCircles.Eight.Generated.Owner
