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

def tilt_032_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (2765739/50000000), (156997/50000000)]
    alternative := .zero
    polynomial := [(-5066949389499534122315196264894771609727711/434847370990220673345673652700000000000000000), (67270228326593/105677250000000), (-1878555560661277322428684205709804248109727711/217423685495110336672836826350000000000000000), (67270228326593/105677250000000), (-3752044171933055110735053215154713724609727711/434847370990220673345673652700000000000000000)]
    bernstein := [(154839743240362858138191813868854387309877620474449/4559705168834416327741130960535552000000000000000000000), (77372096121049546374533298824127277550122194805177/1139926292208604081935282740133888000000000000000000000), (3947850462712898923742731330014850352498941990577/44997090481918582181655897636864000000000000000000000), (952013398631027994707775821311997734615283350319/10177913323291107874422167322624000000000000000000000), (216978220797777662767848133597119321924991026887/2544478330822776968605541830656000000000000000000000)]
    reserve := (33958279/1000000000000) }

theorem tilt_032_000_valid : tilt_032_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_000]
  · intro i; fin_cases i <;> norm_num [tilt_032_000]
  · norm_num [tilt_032_000]
  · norm_num [tilt_032_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_000]

def tilt_032_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![(587/4000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (2765739/50000000), (12719/4000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-57791853975484103197639248050752249072667/5032692809985101393460314700000000000000000), (603259088217536840003/960077816250000000000), (-21479143429419733597614282774518361352072667/2516346404992550696730157350000000000000000), (603259088217536840003/960077816250000000000), (-42900495004863983092030926300985970455072667/5032692809985101393460314700000000000000000)]
    bernstein := [(2287939865309242958126353944854595933311911968853/52771608959229376787490429468672000000000000000000000), (1008453807252807874909955439507500272310447135069/13192902239807344196872607367168000000000000000000000), (946295709692675565874141364433850497582203478511/9894676679855508147654455525376000000000000000000000), (83234478263750132551090819498058251159208390701/824556389987959012304537960448000000000000000000000), (19038444826543335943580340570151577389889155573/206139097496989753076134490112000000000000000000000)]
    reserve := (43355507/1000000000000) }

theorem tilt_032_001_valid : tilt_032_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_001]
  · intro i; fin_cases i <;> norm_num [tilt_032_001]
  · norm_num [tilt_032_001]
  · norm_num [tilt_032_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_001]

def tilt_032_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, (4347/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (763/20000000), (422709/10000000), (271807/6250000), (1/100000000), (2765739/50000000), (62003/20000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-220845727185259385055388425090864783049654361/18719088442723269314892937955700000000000000000), (4226192519840669733979/6552306531750000000000), (-81866691131516385923361464266158649740376654361/9359544221361634657446468977850000000000000000), (4226192519840669733979/6552306531750000000000), (-163512536535847512461667540107226434697703654361/18719088442723269314892937955700000000000000000)]
    bernstein := [(1460844361233527958322982900474134860708893080010257/28040552689881421207333110442622976000000000000000000000), (4262966201224767472391052653998300076815587386971727/49070967207292487112832943274590208000000000000000000000), (564774125596030382478444863161683286664261131625059/5257603629352766476374958207991808000000000000000000000), (348815397459777580915880837371084607174978902597183/3066935450455780444552058954661888000000000000000000000), (81127823416473840006942755905837317193955291049559/766733862613945111138014738665472000000000000000000000)]
    reserve := (52097559/1000000000000) }

theorem tilt_032_002_valid : tilt_032_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_002]
  · intro i; fin_cases i <;> norm_num [tilt_032_002]
  · norm_num [tilt_032_002]
  · norm_num [tilt_032_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_002]

def tilt_032_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2744267/50000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (2765739/50000000), (12719/4000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-201199720232793451434431693360865591849757/17605651734973407735095494700000000000000000), (603259088217536840003/960077816250000000000), (-75138588066574531507075113940604772894849757/8802825867486703867547747350000000000000000), (603259088217536840003/960077816250000000000), (-150075976412916269562715796187848680197849757/17605651734973407735095494700000000000000000)]
    bernstein := [(7804204141869633688436164377542311101598275280927/79117988029934897096723543359488000000000000000000000), (18238818782911640275003409826688272630477896308097/138456479052386069919266200879104000000000000000000000), (248782326696223208936306391966077820692794112261/1648291417290310356181740486656000000000000000000000), (1352092052779120093772654626206638899841645152913/8653529940774129369954137554944000000000000000000000), (106486479423747818518748198622544651918237043283/721127495064510780829511462912000000000000000000000)]
    reserve := (98640073/1000000000000) }

theorem tilt_032_003_valid : tilt_032_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_003]
  · intro i; fin_cases i <;> norm_num [tilt_032_003]
  · norm_num [tilt_032_003]
  · norm_num [tilt_032_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_003]

def tilt_032_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1373501/25000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (2765739/50000000), (62003/20000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-3528263144443780269128664678945153855740599/300685509509902997273503931900000000000000000), (4226192519840669733979/6552306531750000000000), (-1315008931654847047143265522071411393764740599/150342754754951498636751965950000000000000000), (4226192519840669733979/6552306531750000000000), (-2626489600165250314017402379463877633673740599/300685509509902997273503931900000000000000000)]
    bernstein := [(1097905488822946477364035697713931178751688625852523/9458748264595681358071849766879232000000000000000000000), (356726798234231459030551391171102032290072942874979/2364687066148920339517962441719808000000000000000000000), (101332660646594291691883604651717156926234735498267/591171766537230084879490610429952000000000000000000000), (26267367070484722420827804622100727054299091091091/147792941634307521219872652607488000000000000000000000), (2091440040920564204016844330090497405258606966681/12316078469525626768322721050624000000000000000000000)]
    reserve := (116073021/1000000000000) }

theorem tilt_032_004_valid : tilt_032_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_004]
  · intro i; fin_cases i <;> norm_num [tilt_032_004]
  · norm_num [tilt_032_004]
  · norm_num [tilt_032_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_004]

def tilt_032_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (54337/1250000), (1/100000000), (2765739/50000000), (12719/4000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-2311870562038908402715984166148918493249/201217355856295426104885540000000000000000), (603259088217536840003/960077816250000000000), (-858781336436658903309482299454328013093249/100608677928147713052442770000000000000000), (603259088217536840003/960077816250000000000), (-1715250802311278898216248614742507107693249/201217355856295426104885540000000000000000)]
    bernstein := [(78506564225700011178033848662293233205657522191/2109916901343708327233564599910400000000000000000000), (37077210465543920967167294252636167357182853543/527479225335927081808391149977600000000000000000000), (35402442723985509376967419404087510464373470717/395609419001945311356293362483200000000000000000000), (3125162018137263776430808602733405161931386647/32967451583495442613024446873600000000000000000000), (710509365030482967660446189453992533580642031/8241862895873860653256111718400000000000000000000)]
    reserve := (37208367/1000000000000) }

theorem tilt_032_005_valid : tilt_032_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_005]
  · intro i; fin_cases i <;> norm_num [tilt_032_005]
  · norm_num [tilt_032_005]
  · norm_num [tilt_032_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_005]

def tilt_032_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271929/6250000), (1/100000000), (2765739/50000000), (62003/20000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-95956462348246645600183714642120814033987/8181516149489355839764901100000000000000000), (4226192519840669733979/6552306531750000000000), (-35780749808891520674211397630357570535033987/4090758074744677919882450550000000000000000), (4226192519840669733979/6552306531750000000000), (-71465543155434794702822611546073020256033987/8181516149489355839764901100000000000000000)]
    bernstein := [(10441063119210861411477342894364127342042552226733/85789414779669507890373209358336000000000000000000000), (3356277653771657980463091630807042360867360008309/21447353694917376972593302339584000000000000000000000), (2847840389608637402900214379268980477311789182071/16085515271188032729444976754688000000000000000000000), (245793961694271044064783576244858589613599166661/1340459605932336060787081396224000000000000000000000), (58795584382224614175449827179739953226246424653/335114901483084015196770349056000000000000000000000)]
    reserve := (121705727/1000000000000) }

theorem tilt_032_006_valid : tilt_032_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_006]
  · intro i; fin_cases i <;> norm_num [tilt_032_006]
  · norm_num [tilt_032_006]
  · norm_num [tilt_032_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_006]

def tilt_032_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (4225077/100000000), (271807/6250000), (1/100000000), (2765739/50000000), (12719/4000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-58632962424219557998338468635788314755791/5103199013592622809971607300000000000000000), (262224468654225181333/417226353750000000000), (-21780896572398329807955232596951037015755791/2551599506796311404985803650000000000000000), (262224468654225181333/417226353750000000000), (-14501053394124146685970708908422095238918597/1701066337864207603323869100000000000000000)]
    bernstein := [(2246513188835245812253766158077285237208529491169/53510920088768980555887880962048000000000000000000000), (1005554367097141209759065852182033695569769537737/13377730022192245138971970240512000000000000000000000), (947784031458495934459931485921891125588946267603/10033297516644183854228977680384000000000000000000000), (83502864669445966713956504770593510166312784473/836108126387015321185748140032000000000000000000000), (19101396602598159169946434517499809411530697729/209027031596753830296437035008000000000000000000000)]
    reserve := (41982331/1000000000000) }

theorem tilt_032_007_valid : tilt_032_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_007]
  · intro i; fin_cases i <;> norm_num [tilt_032_007]
  · norm_num [tilt_032_007]
  · norm_num [tilt_032_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_007]

def tilt_032_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (4229103/100000000), (271807/6250000), (1/100000000), (2765739/50000000), (62003/20000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-28211893841662047470584238275847630774915939/2405431544227387978408429804740000000000000000), (42272191171867246164193/65554268327250000000000), (-10519448255192341410587276267939395442115515939/1202715772113693989204214902370000000000000000), (42272191171867246164193/65554268327250000000000), (-21010684616543020773703968297602943253456115939/2405431544227387978408429804740000000000000000)]
    bernstein := [(2949437384572139760704831333191198085028713503125901/25222777869197775768475976909350502400000000000000000000), (956056505348886538095245676552663135763168103980373/6305694467299443942118994227337625600000000000000000000), (8389442999109801776248021480670197023355164330871/48755369592521473779270573922713600000000000000000000), (70266684804222477970689024175798835365925921143717/394105904206215246382437139208601600000000000000000000), (16776898167849835753206473830809862411802064196141/98526476051553811595609284802150400000000000000000000)]
    reserve := (116935469/1000000000000) }

theorem tilt_032_008_valid : tilt_032_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_008]
  · intro i; fin_cases i <;> norm_num [tilt_032_008]
  · norm_num [tilt_032_008]
  · norm_num [tilt_032_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_008]

def tilt_032_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (4346961/100000000), (1/100000000), (2765739/50000000), (12719/4000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-308251493192401956098364074699142013520371/26828986952734411228577192700000000000000000), (603259088217536840003/960077816250000000000), (-114504206546771731193999849516522647336520371/13414493476367205614288596350000000000000000), (603259088217536840003/960077816250000000000), (-228700161600351060431901334958346152659520371/26828986952734411228577192700000000000000000)]
    bernstein := [(10446375950911201358749355080248534577739642811389/281322318229504379884165584125952000000000000000000000), (4938336543052628997813641035621466876583000425797/70330579557376094971041396031488000000000000000000000), (4716356851415268141054313669039838878658397168743/52747934668032071228281047023616000000000000000000000), (416357499713736642184499875257254079528397976213/4395661222336005935690087251968000000000000000000000), (94651877809364305237118750956805380248581550749/1098915305584001483922521812992000000000000000000000)]
    reserve := (37133121/1000000000000) }

theorem tilt_032_009_valid : tilt_032_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_009]
  · intro i; fin_cases i <;> norm_num [tilt_032_009]
  · norm_num [tilt_032_009]
  · norm_num [tilt_032_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_009]

def tilt_032_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (870173/20000000), (1/100000000), (2765739/50000000), (62003/20000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-1283609733193285028502056964702171024958187/109959602322180882526152494940000000000000000), (4226192519840669733979/6552306531750000000000), (-480887342542546909112195096530380756708358187/54979801161090441263076247470000000000000000), (4226192519840669733979/6552306531750000000000), (-960491075351900533195888136096059342391758187/109959602322180882526152494940000000000000000)]
    bernstein := [(203868613016334031596982740286885595211651069254533/1153009999645831410757428785342054400000000000000000000), (60995259545778467790521116049950678146543999517709/288252499911457852689357196335513600000000000000000000), (50191458895635434963905934815886569926663999980671/216189374933593389517017897251635200000000000000000000), (613803458147626109579047591184965631201078051323/2573683034923730827583546395852800000000000000000000), (148361435025255675597927059106739582886604017779/643420758730932706895886598963200000000000000000000)]
    reserve := (88407131/500000000000) }

theorem tilt_032_010_valid : tilt_032_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_010]
  · intro i; fin_cases i <;> norm_num [tilt_032_010]
  · norm_num [tilt_032_010]
  · norm_num [tilt_032_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_010]

def tilt_032_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14607/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (2765739/50000000), (12719/4000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-57795562480148617120237655376773509676417/5032692809985101393460314700000000000000000), (603259088217536840003/960077816250000000000), (-21479147137924398111536881181844382612676417/2516346404992550696730157350000000000000000), (603259088217536840003/960077816250000000000), (-42900498713368647605953524708311991715676417/5032692809985101393460314700000000000000000)]
    bernstein := [(2248961421429662269339410966407574412888404465103/52771608959229376787490429468672000000000000000000000), (998708150733994248475608238772699571644088361319/13192902239807344196872607367168000000000000000000000), (938985659323309952904908123032213236486859027261/9894676679855508147654455525376000000000000000000000), (82625238082430436763713294800588096843793076951/824556389987959012304537960448000000000000000000000), (18886116955358615844438509501369686116628251823/206139097496989753076134490112000000000000000000000)]
    reserve := (42616881/1000000000000) }

theorem tilt_032_011_valid : tilt_032_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_011]
  · intro i; fin_cases i <;> norm_num [tilt_032_011]
  · norm_num [tilt_032_011]
  · norm_num [tilt_032_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_011]

def tilt_032_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4327/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1899/50000000), (2765739/50000000), (62003/20000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-71247793143199509790125273624917570375554501/6039338931826620528199403530050000000000000000), (4226192519840669733979/6552306531750000000000), (-26412644399127706695696213962409783970981054501/3019669465913310264099701765025000000000000000), (4226192519840669733979/6552306531750000000000), (-52754041005112213881602302651194650371586554501/6039338931826620528199403530050000000000000000)]
    bernstein := [(1112540994799703644929311676170916061062567679803353/21109019532596768156590725853085696000000000000000000000), (461657043999245912963532769601365283745098663453569/5277254883149192039147681463271424000000000000000000000), (1282700066507524186797862619497920663024127428890033/11873823487085682088082283292360704000000000000000000000), (16162727224669791979334019742928055296751831690229/141355041512924786762884324909056000000000000000000000), (3760640307974989411095265549912805868824701944317/35338760378231196690721081227264000000000000000000000)]
    reserve := (52704531/1000000000000) }

theorem tilt_032_012_valid : tilt_032_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_012]
  · intro i; fin_cases i <;> norm_num [tilt_032_012]
  · norm_num [tilt_032_012]
  · norm_num [tilt_032_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_012]

def tilt_032_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (552873/10000000), (12719/4000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-5748013207870323111261842061654370872649/503019260301657705717456450000000000000000), (603259088217536840003/960077816250000000000), (-2146818972826725997982718070651685181372649/251509630150828852858728225000000000000000), (603259088217536840003/960077816250000000000), (-4287889932445581672854174299241715991872649/503019260301657705717456450000000000000000)]
    bernstein := [(526140922919348371757468030206110847849901166791/5274539238900710304303876145152000000000000000000000), (175168410367857053587370036056854874536183309343/1318634809725177576075969036288000000000000000000000), (150368572381572437927618595164717014374470730917/988976107293883182056976777216000000000000000000000), (12968676177339326320649778158988830044795864847/82414675607823598504748064768000000000000000000000), (3065375547910084236177061937341655994131710631/20603668901955899626187016192000000000000000000000)]
    reserve := (24937767/250000000000) }

theorem tilt_032_013_valid : tilt_032_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_013]
  · intro i; fin_cases i <;> norm_num [tilt_032_013]
  · norm_num [tilt_032_013]
  · norm_num [tilt_032_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_013]

def tilt_032_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (1383557/25000000), (62003/20000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-123456405630066287942634892261600689190271/10519600107408141265840650600000000000000000), (4226192519840669733979/6552306531750000000000), (-46006120335171250982771950410863559855190271/5259800053704070632920325300000000000000000), (4226192519840669733979/6552306531750000000000), (-91888784264712435677601265929465519021190271/10519600107408141265840650600000000000000000)]
    bernstein := [(88246074593596798299702659100137307202942024798423/772142014155791939517908823048192000000000000000000000), (28775796057910170365611868386651759445537472565679/193035503538947984879477205762048000000000000000000000), (24557561332573199632496001622991576938229790278101/144776627654210988659607904321536000000000000000000000), (2122722303474759514389513911810224714736535231391/12064718971184249054967325360128000000000000000000000), (506800649057312976589378911582485947719625461943/3016179742796062263741831340032000000000000000000000)]
    reserve := (57143681/500000000000) }

theorem tilt_032_014_valid : tilt_032_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_014]
  · intro i; fin_cases i <;> norm_num [tilt_032_014]
  · norm_num [tilt_032_014]
  · norm_num [tilt_032_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_014]

def tilt_032_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(14607/100000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (2765739/50000000), (12719/4000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-57795562480148617120237655376773509676417/5032692809985101393460314700000000000000000), (603259088217536840003/960077816250000000000), (-21479147137924398111536881181844382612676417/2516346404992550696730157350000000000000000), (603259088217536840003/960077816250000000000), (-42900498713368647605953524708311991715676417/5032692809985101393460314700000000000000000)]
    bernstein := [(2248961421429662269339410966407574412888404465103/52771608959229376787490429468672000000000000000000000), (998708150733994248475608238772699571644088361319/13192902239807344196872607367168000000000000000000000), (938985659323309952904908123032213236486859027261/9894676679855508147654455525376000000000000000000000), (82625238082430436763713294800588096843793076951/824556389987959012304537960448000000000000000000000), (18886116955358615844438509501369686116628251823/206139097496989753076134490112000000000000000000000)]
    reserve := (42616881/1000000000000) }

theorem tilt_032_015_valid : tilt_032_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_015]
  · intro i; fin_cases i <;> norm_num [tilt_032_015]
  · norm_num [tilt_032_015]
  · norm_num [tilt_032_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_015]

def tilt_032_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4327/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1899/50000000), (2765739/50000000), (62003/20000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-71247793143199509790125273624917570375554501/6039338931826620528199403530050000000000000000), (4226192519840669733979/6552306531750000000000), (-26412644399127706695696213962409783970981054501/3019669465913310264099701765025000000000000000), (4226192519840669733979/6552306531750000000000), (-52754041005112213881602302651194650371586554501/6039338931826620528199403530050000000000000000)]
    bernstein := [(1112540994799703644929311676170916061062567679803353/21109019532596768156590725853085696000000000000000000000), (461657043999245912963532769601365283745098663453569/5277254883149192039147681463271424000000000000000000000), (1282700066507524186797862619497920663024127428890033/11873823487085682088082283292360704000000000000000000000), (16162727224669791979334019742928055296751831690229/141355041512924786762884324909056000000000000000000000), (3760640307974989411095265549912805868824701944317/35338760378231196690721081227264000000000000000000000)]
    reserve := (52704531/1000000000000) }

theorem tilt_032_016_valid : tilt_032_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_016]
  · intro i; fin_cases i <;> norm_num [tilt_032_016]
  · norm_num [tilt_032_016]
  · norm_num [tilt_032_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_016]

def tilt_032_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (552873/10000000), (12719/4000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-11496050285988014291891551906964554518173/1006038520603315411434912900000000000000000), (603259088217536840003/960077816250000000000), (-4293637969523699364034804009087026175518173/503019260301657705717456450000000000000000), (603259088217536840003/960077816250000000000), (-8575779888761410713777716466267087796518173/1006038520603315411434912900000000000000000)]
    bernstein := [(1052030956280344266090827896340007884481173870707/10549078477801420608607752290304000000000000000000000), (350274091616321504158653957369773807919167728811/2637269619450355152151938072576000000000000000000000), (300690092722935921455321270839754467729637279209/1977952214587766364113953554432000000000000000000000), (25933430905159166948318645973815142684856585819/164829351215647197009496129536000000000000000000000), (6129770618701985512641462290173595059033618387/41207337803911799252374032384000000000000000000000)]
    reserve := (19945457/200000000000) }

theorem tilt_032_017_valid : tilt_032_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_017]
  · intro i; fin_cases i <;> norm_num [tilt_032_017]
  · norm_num [tilt_032_017]
  · norm_num [tilt_032_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_017]

def tilt_032_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (1383557/25000000), (62003/20000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-431473311049113630396035186327578866076261/36818600375928494430442277100000000000000000), (4226192519840669733979/6552306531750000000000), (-161020797064443260062298639501434435947076261/18409300187964247215221138550000000000000000), (4226192519840669733979/6552306531750000000000), (-321610120817837406494201243816541293028076261/36818600375928494430442277100000000000000000)]
    bernstein := [(50682765928138608705009236645441511390550239513899/386071007077895969758954411524096000000000000000000000), (16028006143459855830062229318965431265452360405027/96517751769473992439738602881024000000000000000000000), (13508997728122330788841403650770492139167152148113/72388313827105494329803952160768000000000000000000000), (1163890905698627453552240744204327989649062252883/6032359485592124527483662680064000000000000000000000), (279035762953251209394643171673491364110177995659/1508089871398031131870915670016000000000000000000000)]
    reserve := (8204897/62500000000) }

theorem tilt_032_018_valid : tilt_032_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_018]
  · intro i; fin_cases i <;> norm_num [tilt_032_018]
  · norm_num [tilt_032_018]
  · norm_num [tilt_032_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_018]

def tilt_032_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (2765739/50000000), (156997/50000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-2498624442805403687530983933420193774792043/217423685495110336672836826350000000000000000), (67270228326593/105677250000000), (-939278685299949440111258160078187916985597293/108711842747555168336418413175000000000000000), (67270228326593/105677250000000), (-1876058746157093476534985336222955640196402543/217423685495110336672836826350000000000000000)]
    bernstein := [(442828286842962492367591816440895505735718264313537/2279852584417208163870565480267776000000000000000000000), (130037884828183712864250593182646614512618015423401/569963146104302040967641370066944000000000000000000000), (5579907898392517761751954251179871439099951053601/22498545240959291090827948818432000000000000000000000), (1291643093035550725285259947285197897553368390847/5088956661645553937211083661312000000000000000000000), (312397552927615433556327444371555190264171708631/1272239165411388484302770915328000000000000000000000)]
    reserve := (194235491/1000000000000) }

theorem tilt_032_019_valid : tilt_032_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_019]
  · intro i; fin_cases i <;> norm_num [tilt_032_019]
  · norm_num [tilt_032_019]
  · norm_num [tilt_032_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_019]

def tilt_032_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(11/320), (3/80)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
    cone := fun i => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(5491269/100000000), (1/100000000), (422709/10000000), (271807/6250000), (1/100000000), (2765739/50000000), (156997/50000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-2532874804618814527668449907568821844792043/217423685495110336672836826350000000000000000), (67270228326593/105677250000000), (-939243234894194781269030668781916669252597293/108711842747555168336418413175000000000000000), (67270228326593/105677250000000), (-1875953594983770748010392887656264516660402543/217423685495110336672836826350000000000000000)]
    bernstein := [(84567241887625309193556177706280695014135240313537/2279852584417208163870565480267776000000000000000000000), (40482641412662852138629503185283461665191663423401/569963146104302040967641370066944000000000000000000000), (2045240007553491726630570298662426203811199053601/22498545240959291090827948818432000000000000000000000), (492229785831336746281979791448978936665224390847/5088956661645553937211083661312000000000000000000000), (112568636371996551785540685019632900642459708631/1272239165411388484302770915328000000000000000000000)]
    reserve := (37093293/1000000000000) }

theorem tilt_032_020_valid : tilt_032_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_032_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_032_020]
  · intro i; fin_cases i <;> norm_num [tilt_032_020]
  · norm_num [tilt_032_020]
  · norm_num [tilt_032_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_032_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_032_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_032_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_032_020]

def tiltBundle032_row : Alternative → Row
  | .zero => tilt_032_000
  | (.spike 0 false false) => tilt_032_001
  | (.spike 0 false true) => tilt_032_002
  | (.spike 0 true false) => tilt_032_003
  | (.spike 0 true true) => tilt_032_004
  | (.spike 1 false false) => tilt_032_005
  | (.spike 1 false true) => tilt_032_006
  | (.spike 1 true false) => tilt_032_007
  | (.spike 1 true true) => tilt_032_008
  | (.spike 2 false false) => tilt_032_009
  | (.spike 2 false true) => tilt_032_010
  | (.spike 2 true false) => tilt_032_011
  | (.spike 2 true true) => tilt_032_012
  | (.spike 3 false false) => tilt_032_013
  | (.spike 3 false true) => tilt_032_014
  | (.spike 3 true false) => tilt_032_015
  | (.spike 3 true true) => tilt_032_016
  | (.spike 4 false false) => tilt_032_017
  | (.spike 4 false true) => tilt_032_018
  | (.spike 4 true false) => tilt_032_019
  | (.spike 4 true true) => tilt_032_020

def tiltBundle032 : TiltBundle where
  interval := ⟨(11/320), (3/80)⟩
  lambda := ![(7337479/50000000), (7337479/50000000), (1137743/12500000), (14607297/100000000), (14607297/100000000), (8152379/50000000), (16028789/100000000)]
  row := tiltBundle032_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_032_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_032_001_valid | exact tilt_032_002_valid | exact tilt_032_003_valid | exact tilt_032_004_valid | exact tilt_032_005_valid | exact tilt_032_006_valid | exact tilt_032_007_valid | exact tilt_032_008_valid | exact tilt_032_009_valid | exact tilt_032_010_valid | exact tilt_032_011_valid | exact tilt_032_012_valid | exact tilt_032_013_valid | exact tilt_032_014_valid | exact tilt_032_015_valid | exact tilt_032_016_valid | exact tilt_032_017_valid | exact tilt_032_018_valid | exact tilt_032_019_valid | exact tilt_032_020_valid
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
