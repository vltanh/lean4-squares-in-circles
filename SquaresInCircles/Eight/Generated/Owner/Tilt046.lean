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

def tilt_046_000 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (1048447/20000000), (393039/50000000)]
    alternative := .zero
    polynomial := [(-6505214574706334710612273745345387056137790829/179539008864650020032284886016275000000000000000), (3585733309587/5395866250000), (-272763576500518608853704036744820439291637790829/89769504432325010016142443008137500000000000000), (3585733309587/5395866250000), (-539021938426330882996795799744295491527137790829/179539008864650020032284886016275000000000000000)]
    bernstein := [(358880495761120496722935577825450530567395753371/1795390088646500200322848860162750000000000000000000), (2882982516034825909921439301992578103245805060069/9575413806114667735055193920868000000000000000000000), (527574965410356801499055391400201373247986726255557/1378859588080512153847947924604992000000000000000000000), (1089513830829208735654415602043541023122476209902241/2451305934365354940174129643742208000000000000000000000), (57252498665109938798472716942827502000527663540183891/117662684849537037128358222899625984000000000000000000000)]
    reserve := (199889983/1000000000000) }

theorem tilt_046_000_valid : tilt_046_000.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_000]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_000]
  · intro i; fin_cases i <;> norm_num [tilt_046_000]
  · norm_num [tilt_046_000]
  · norm_num [tilt_046_000, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_000, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_000, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_000, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_000]

def tilt_046_001 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![(3931/25000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (1048447/20000000), (197409/25000000)]
    alternative := (.spike 0 false false)
    polynomial := [(-108378732438321692498462409283390866690409571/3005860843407541050171724015817500000000000000), (94005914026525407217/142025674739500000000), (-4548572696842793274348864250247955775868909571/1502930421703770525085862007908750000000000000), (94005914026525407217/142025674739500000000), (-8988766661247264856199266091212520685047409571/3005860843407541050171724015817500000000000000)]
    bernstein := [(6965642227416972836454846907974964098124966229/30058608434075410501717240158175000000000000000000), (159916110783158094892553886035147744641348592993/480937734945206568027475842530800000000000000000000), (3183451081616210117175054732903210563483844225881/7695003759123305088439613480492800000000000000000000), (58517334534616293803890896004661321883217630188077/123120060145972881415033815687884800000000000000000000), (1018884790141546311112975097131715363563196114487709/1969920962335566102640541051006156800000000000000000000)]
    reserve := (28966919/125000000000) }

theorem tilt_046_001_valid : tilt_046_001.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_001]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_001]
  · intro i; fin_cases i <;> norm_num [tilt_046_001]
  · norm_num [tilt_046_001]
  · norm_num [tilt_046_001, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_001, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_001, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_001, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_001]

def tilt_046_002 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, (2329/50000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (511/12500000), (4316693/100000000), (4540321/100000000), (1/100000000), (1048447/20000000), (782521/100000000)]
    alternative := (.spike 0 false true)
    polynomial := [(-26581681118606080480503824539443473279735716170249/730634322499303345921644623147977900000000000000000), (281715830200460694249/422237865381625000000), (-1114420358525406202269288811236229866735469936170249/365317161249651672960822311573988950000000000000000), (281715830200460694249/422237865381625000000), (-2202259035932206324058073797933016260191204156170249/730634322499303345921644623147977900000000000000000)]
    bernstein := [(1448644418063348487500794239900860706908902907289951/7306343224993033459216446231479779000000000000000000000), (5008478209677381719895069438967659294454984391920581/16700213085698362192494734243382352000000000000000000000), (2654772969161042387221377480710155626063283713118231/6953248570997087604310075224010496000000000000000000000), (1897930527496253805358862980999057730918720675845860609/4275254549938780721278651966305882112000000000000000000000), (865557427132823728948857237673662045020320605435611859/1780031634175254426703379257346686976000000000000000000000)]
    reserve := (39654431/200000000000) }

theorem tilt_046_002_valid : tilt_046_002.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_002]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_002]
  · intro i; fin_cases i <;> norm_num [tilt_046_002]
  · norm_num [tilt_046_002]
  · norm_num [tilt_046_002, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_002, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_002, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_002, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_002]

def tilt_046_003 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (802073/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1066477/20000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (1048447/20000000), (197409/25000000)]
    alternative := (.spike 0 true false)
    polynomial := [(-7788416098549993174632879354649207663368529057/216308033726628852927004396983150000000000000000), (94005914026525407217/142025674739500000000), (-327314061442923140638613675834157143950698529057/108154016863314426463502198491575000000000000000), (94005914026525407217/142025674739500000000), (-646839706787296288102594472313665080238028529057/216308033726628852927004396983150000000000000000)]
    bernstein := [(610863628757147151938202756560293345485975089543/2163080337266288529270043969831500000000000000000000), (4420868699044409199081362640212380902393156665977/11536428465420205489440234505768000000000000000000000), (771542587381720331787744745500061088997189812539481/1661245699020509590479393768830592000000000000000000000), (1553602810519846522772023054514408644739227410153253/2953325687147572605296700033476608000000000000000000000), (80522267561865340404440094814046429982949813678492703/141759632983083485054241601606877184000000000000000000000)]
    reserve := (282404503/1000000000000) }

theorem tilt_046_003_valid : tilt_046_003.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_003]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_003]
  · intro i; fin_cases i <;> norm_num [tilt_046_003]
  · norm_num [tilt_046_003]
  · norm_num [tilt_046_003, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_003, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_003, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_003, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_003]

def tilt_046_004 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (786349/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(1334501/25000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (1048447/20000000), (782521/100000000)]
    alternative := (.spike 0 true true)
    polynomial := [(-486889481599776735892015264758359358729097043/13411554694306710711078721030819375000000000000), (281715830200460694249/422237865381625000000), (-20455302504842993963143822965534240852741472043/6705777347153355355539360515409687500000000000), (281715830200460694249/422237865381625000000), (-40423715528086211190395630666310122346753847043/13411554694306710711078721030819375000000000000)]
    bernstein := [(37251295108616069373650753748857123217131314357/134115546943067107110787210308193750000000000000000), (116316440260327629245750863869065612428294639767/306549821584153387681799337847300000000000000000000), (176665702777110155862269053815883636749535184951/382902379376488989818158280731200000000000000000000), (41087893333517448192348806527448777909522514271563/78476754325543267246540630488908800000000000000000000), (18491899263764511441738222908708777703056117155313/32674336373460393797816173289062400000000000000000000)]
    reserve := (277755233/1000000000000) }

theorem tilt_046_004_valid : tilt_046_004.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_004]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_004]
  · intro i; fin_cases i <;> norm_num [tilt_046_004]
  · norm_num [tilt_046_004]
  · norm_num [tilt_046_004, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_004, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_004, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_004, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_004]

def tilt_046_005 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (453817/10000000), (1/100000000), (1048447/20000000), (197409/25000000)]
    alternative := (.spike 1 false false)
    polynomial := [(-649998560236269318319414168803316566179514617/18026620809929695148415029831850000000000000000), (94005914026525407217/142025674739500000000), (-27278540960795314546979728876873727711849514617/9013310404964847574207514915925000000000000000), (94005914026525407217/142025674739500000000), (-53907083361354359775640043584944138857519514617/18026620809929695148415029831850000000000000000)]
    bernstein := [(41424817624319220731175584583887872328431391983/180266208099296951484150298318500000000000000000000), (45402422355816458049028803977916045055984823591/137345682361369105892685941576000000000000000000000), (57006423816826422821864874906327141982249085310961/138444447820260058739827429108608000000000000000000000), (16643070880570887463427909223890959953286778197499/35160494684510491108527601043456000000000000000000000), (6087466559793032284035241705394399063393323337727943/11813926213995525012465273950601216000000000000000000000)]
    reserve := (229798019/1000000000000) }

theorem tilt_046_005_valid : tilt_046_005.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_005]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_005]
  · intro i; fin_cases i <;> norm_num [tilt_046_005]
  · norm_num [tilt_046_005]
  · norm_num [tilt_046_005, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_005, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_005, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_005, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_005]

def tilt_046_006 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4542473/100000000), (1/100000000), (1048447/20000000), (782521/100000000)]
    alternative := (.spike 1 false true)
    polynomial := [(-25966711317363225788240085224250122592818454841/715245230058905485272770257137850000000000000000), (281715830200460694249/422237865381625000000), (-1090892627235505857044732114670560622761948454841/357622615029452742636385128568925000000000000000), (281715830200460694249/422237865381625000000), (-2155818543153648488301224144116871122931078454841/715245230058905485272770257137850000000000000000)]
    bernstein := [(1980097562043276333175196405298118478818682166959/7152452300589054852727702571378500000000000000000000), (43317915708094193260852569892856662827515990732403/114439236809424877643643241142056000000000000000000000), (9402997783928122865344880311558125690329684480437/20420384263391799728233738196352000000000000000000000), (15311860017446718309104203404733108645537553198724567/29296444623212768676772669732366336000000000000000000000), (984586853712049876397025556265588745366968502543331/1742539457142766910142612326088704000000000000000000000)]
    reserve := (276841771/1000000000000) }

theorem tilt_046_006_valid : tilt_046_006.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_006]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_006]
  · intro i; fin_cases i <;> norm_num [tilt_046_006]
  · norm_num [tilt_046_006]
  · norm_num [tilt_046_006, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_006, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_006, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_006, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_006]

def tilt_046_007 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4314303/100000000), (4540321/100000000), (1/100000000), (1048447/20000000), (197409/25000000)]
    alternative := (.spike 1 true false)
    polynomial := [(-4814217255120184745969653459358492251331893/133519849099460418482173166013000000000000000), (3480884826029963641/5257297783500000000), (-202072414173800650348833385002230686824131893/66759924549730209241086583006500000000000000), (3480884826029963641/5257297783500000000), (-399330611092481115951697116545102881396931893/133519849099460418482173166013000000000000000)]
    bernstein := [(332258306781540540965761266107044572437759507/1335198490994604184821731660130000000000000000000), (16947036207247689365205852150490363707888959/48442575636992442079700014880000000000000000000), (442216175045372919247442280412844149879353681869/1025432441083856013943089914979840000000000000000000), (6114405229563404606055476228230750598365814451/12401299363070065172403203809280000000000000000000), (46831178229940312441525144061933328422498500542347/87503568305822379856477006078279680000000000000000000)]
    reserve := (248845627/1000000000000) }

theorem tilt_046_007_valid : tilt_046_007.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_007]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_007]
  · intro i; fin_cases i <;> norm_num [tilt_046_007]
  · norm_num [tilt_046_007]
  · norm_num [tilt_046_007, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_007, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_007, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_007, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_007]

def tilt_046_008 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (2159541/50000000), (4540321/100000000), (1/100000000), (1048447/20000000), (782521/100000000)]
    alternative := (.spike 1 true true)
    polynomial := [(-721385080333405673319336913731107398271296391/19869500967163251781215328166925000000000000000), (2609097387887087497/3911773571437500000), (-30301218708280078438446381954739448926068796391/9934750483581625890607664083462500000000000000), (2609097387887087497/3911773571437500000), (-59881052336226751203573426995747790453866296391/19869500967163251781215328166925000000000000000)]
    bernstein := [(51225960627073792156668535732648883951410515409/198695009671632517812153281669250000000000000000000), (380725403468854481368189217054277778436940770351/1059706718248706761664817502236000000000000000000000), (250172503835496477810475030037124090501431923787/567277945828303991374474796736000000000000000000000), (136448637426306259469426667511747272252086023303139/271284919871668930986193280572416000000000000000000000), (26388811792522059929098211489786014480006393364381/48407718044015273930621849321472000000000000000000000)]
    reserve := (128906007/500000000000) }

theorem tilt_046_008_valid : tilt_046_008.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_008]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_008]
  · intro i; fin_cases i <;> norm_num [tilt_046_008]
  · norm_num [tilt_046_008]
  · norm_num [tilt_046_008, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_008, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_008, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_008, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_008]

def tilt_046_009 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4538171/100000000), (1/100000000), (1048447/20000000), (197409/25000000)]
    alternative := (.spike 2 false false)
    polynomial := [(-649999727606268902540616523444247676948247141/18026624782152157050392070889155000000000000000), (94005914026525407217/142025674739500000000), (-27278547995848190832392210681230008417369247141/9013312391076078525196035444577500000000000000), (94005914026525407217/142025674739500000000), (-53907096264090112762243804839015769157790247141/18026624782152157050392070889155000000000000000)]
    bernstein := [(41414379492339755354833600495422577907188914659/180266247821521570503920708891550000000000000000000), (28887388483900903136005559320140808820341899191/87401817125586216001900949765600000000000000000000), (56998402847083080547263122848864012927248704723453/138444478326928566147011104428710400000000000000000000), (10589748254539419827949309053360136298777121565899/22374865184150071296486643139993600000000000000000000), (6086781480742144239733482504944551549283148746827739/11813928817231237644544947577916620800000000000000000000)]
    reserve := (45948013/200000000000) }

theorem tilt_046_009_valid : tilt_046_009.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_009]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_009]
  · intro i; fin_cases i <;> norm_num [tilt_046_009]
  · norm_num [tilt_046_009]
  · norm_num [tilt_046_009, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_009, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_009, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_009, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_009]

def tilt_046_010 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (2271237/50000000), (1/100000000), (1048447/20000000), (782521/100000000)]
    alternative := (.spike 2 false true)
    polynomial := [(-1080722584735735299401414173711812318981501763/29801891146505774821601781315137500000000000000), (281715830200460694249/422237865381625000000), (-45452645516219945834556699035128892131979001763/14900945573252887410800890657568750000000000000), (281715830200460694249/422237865381625000000), (-89824568447704156369711983896545971944976501763/29801891146505774821601781315137500000000000000)]
    bernstein := [(94989682262256279406121523065294244607205515637/298018911465057748216017813151375000000000000000000), (2004806755866659570920670031793419779994661572129/4768302583440923971456285010422000000000000000000000), (427482863595013701654782616524033184653588643991/850849531617711340631604760224000000000000000000000), (689232279714804653841750232987331971448930001889581/1220685461360876536692808962668032000000000000000000000), (44074075506859204174759935523715885619497520110833/72605826698044701067230272872448000000000000000000000)]
    reserve := (63747419/200000000000) }

theorem tilt_046_010_valid : tilt_046_010.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_010]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_010]
  · intro i; fin_cases i <;> norm_num [tilt_046_010]
  · norm_num [tilt_046_010]
  · norm_num [tilt_046_010, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_010, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_010, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_010, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_010]

def tilt_046_011 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7297/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (1048447/20000000), (197409/25000000)]
    alternative := (.spike 2 true false)
    polynomial := [(-325246591385108278279025098753498583516550713/9017582530222623150515172047452500000000000000), (94005914026525407217/142025674739500000000), (-13645828484598523023830230621647193311052050713/4508791265111311575257586023726250000000000000), (94005914026525407217/142025674739500000000), (-26966410377811937769381436144540888038587550713/9017582530222623150515172047452500000000000000)]
    bernstein := [(19770796772720127315474619639096535168645176687/90175825302226231505151720474525000000000000000000), (153906367998632387432091831928984531861464234993/480937734945206568027475842530800000000000000000000), (27785110212532910193189165705999025487013461258929/69255033832109745795956521324435200000000000000000000), (56976876802452075581674043343726080144025292126077/123120060145972881415033815687884800000000000000000000), (2982663813415363524146027149393378978656285115101127/5909762887006698307921623153018470400000000000000000000)]
    reserve := (43849439/200000000000) }

theorem tilt_046_011_valid : tilt_046_011.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_011]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_011]
  · intro i; fin_cases i <;> norm_num [tilt_046_011]
  · norm_num [tilt_046_011]
  · norm_num [tilt_046_011, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_011, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_011, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_011, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_011]

def tilt_046_012 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4323/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1897/50000000), (1048447/20000000), (782521/100000000)]
    alternative := (.spike 2 true true)
    polynomial := [(-24663128665521146794458808253284096864629924865393/678088703415449338167005797510623325000000000000000), (281715830200460694249/422237865381625000000), (-1034266832697174684481995559605438592160876409865393/339044351707724669083502898755311662500000000000000), (281715830200460694249/422237865381625000000), (-2043870536728828222169532310957593087457122894865393/678088703415449338167005797510623325000000000000000)]
    bernstein := [(1414401267023019057025709225348144571158724478126007/6780887034154493381670057975106233250000000000000000000), (4808241629090350529760913606067173099454815895515917/15499170363781699158102989657385676000000000000000000000), (7591472817321433510771734892375007017606043642805901/19359558521303535007890723140823744000000000000000000000), (1802438110542191150420018592676481651974922581193183913/3967787613128114984474365352290733056000000000000000000000), (820391360556922143584979318178229746415049957032505163/1652015660484568320673341708016959488000000000000000000000)]
    reserve := (104293233/500000000000) }

theorem tilt_046_012_valid : tilt_046_012.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_012]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_012]
  · intro i; fin_cases i <;> norm_num [tilt_046_012]
  · norm_num [tilt_046_012]
  · norm_num [tilt_046_012, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_012, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_012, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_012, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_012]

def tilt_046_013 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (2619807/50000000), (197409/25000000)]
    alternative := (.spike 3 false false)
    polynomial := [(-5410991101220197447637655398851132928537416907/150217899017975727834162981604350000000000000000), (94005914026525407217/142025674739500000000), (-227309689448482109235887432369396213433707416907/75108949508987863917081490802175000000000000000), (94005914026525407217/142025674739500000000), (-449208387795744021024137209339941293938877416907/150217899017975727834162981604350000000000000000)]
    bernstein := [(401522187519924211636627379146743959646470131693/1502178990179757278341629816043500000000000000000000), (2948988006512938082248911385105583452086550999827/8011621280958705484488692352232000000000000000000000), (518352336199870327162455122678336513965651752868531/1153673464458053589766371698721408000000000000000000000), (1047867751542403317591150558994035938309139191430903/2050975047925428604029105242171392000000000000000000000), (54428263368238213211183340859285890761214176601492853/98446802300420572993397051624226816000000000000000000000)]
    reserve := (66823293/250000000000) }

theorem tilt_046_013_valid : tilt_046_013.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_013]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_013]
  · intro i; fin_cases i <;> norm_num [tilt_046_013]
  · norm_num [tilt_046_013]
  · norm_num [tilt_046_013, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_013, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_013, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_013, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_013]

def tilt_046_014 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (655607/12500000), (782521/100000000)]
    alternative := (.spike 3 false true)
    polynomial := [(-32455378481254903017666684297881414984011497507/894079774075390624224014971430900000000000000000), (281715830200460694249/422237865381625000000), (-1363647370118454476579806507950838309113631497507/447039887037695312112007485715450000000000000000), (281715830200460694249/422237865381625000000), (-2694839361755654050141946331603795203243251497507/894079774075390624224014971430900000000000000000)]
    bernstein := [(2514503566542177863858805678024140873091473931093/8940797740753906242240149714309000000000000000000000), (54778267774606885234615264879116459580439181649281/143052763852062499875842395428944000000000000000000000), (3955481563925591175438804732244164680345948643133/8508714578561338282577986345216000000000000000000000), (19301671390025349624281519259936873313224425343744909/36621507546127999968215653229809664000000000000000000000), (1240368821916283253775263223295573704364655208838737/2178230932111702600339964504375296000000000000000000000)]
    reserve := (56247857/200000000000) }

theorem tilt_046_014_valid : tilt_046_014.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_014]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_014]
  · intro i; fin_cases i <;> norm_num [tilt_046_014]
  · norm_num [tilt_046_014]
  · norm_num [tilt_046_014, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_014, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_014, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_014, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_014]

def tilt_046_015 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(7297/50000000), 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (1048447/20000000), (197409/25000000)]
    alternative := (.spike 3 true false)
    polynomial := [(-325246591385108278279025098753498583516550713/9017582530222623150515172047452500000000000000), (94005914026525407217/142025674739500000000), (-13645828484598523023830230621647193311052050713/4508791265111311575257586023726250000000000000), (94005914026525407217/142025674739500000000), (-26966410377811937769381436144540888038587550713/9017582530222623150515172047452500000000000000)]
    bernstein := [(19770796772720127315474619639096535168645176687/90175825302226231505151720474525000000000000000000), (153906367998632387432091831928984531861464234993/480937734945206568027475842530800000000000000000000), (27785110212532910193189165705999025487013461258929/69255033832109745795956521324435200000000000000000000), (56976876802452075581674043343726080144025292126077/123120060145972881415033815687884800000000000000000000), (2982663813415363524146027149393378978656285115101127/5909762887006698307921623153018470400000000000000000000)]
    reserve := (43849439/200000000000) }

theorem tilt_046_015_valid : tilt_046_015.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_015]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_015]
  · intro i; fin_cases i <;> norm_num [tilt_046_015]
  · norm_num [tilt_046_015]
  · norm_num [tilt_046_015, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_015, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_015, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_015, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_015]

def tilt_046_016 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (4323/100000000), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1897/50000000), (1048447/20000000), (782521/100000000)]
    alternative := (.spike 3 true true)
    polynomial := [(-24663128665521146794458808253284096864629924865393/678088703415449338167005797510623325000000000000000), (281715830200460694249/422237865381625000000), (-1034266832697174684481995559605438592160876409865393/339044351707724669083502898755311662500000000000000), (281715830200460694249/422237865381625000000), (-2043870536728828222169532310957593087457122894865393/678088703415449338167005797510623325000000000000000)]
    bernstein := [(1414401267023019057025709225348144571158724478126007/6780887034154493381670057975106233250000000000000000000), (4808241629090350529760913606067173099454815895515917/15499170363781699158102989657385676000000000000000000000), (7591472817321433510771734892375007017606043642805901/19359558521303535007890723140823744000000000000000000000), (1802438110542191150420018592676481651974922581193183913/3967787613128114984474365352290733056000000000000000000000), (820391360556922143584979318178229746415049957032505163/1652015660484568320673341708016959488000000000000000000000)]
    reserve := (104293233/500000000000) }

theorem tilt_046_016_valid : tilt_046_016.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_016]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_016]
  · intro i; fin_cases i <;> norm_num [tilt_046_016]
  · norm_num [tilt_046_016]
  · norm_num [tilt_046_016, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_016, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_016, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_016, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_016]

def tilt_046_017 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (2619807/50000000), (197409/25000000)]
    alternative := (.spike 4 false false)
    polynomial := [(-1803663805860339800872395279599779553171442219/50072633005991909278054327201450000000000000000), (94005914026525407217/142025674739500000000), (-75769896588280977063622320936448139721561442219/25036316502995954639027163600725000000000000000), (94005914026525407217/142025674739500000000), (-149736129370701614326372246593296499889951442219/50072633005991909278054327201450000000000000000)]
    bernstein := [(133839653441059816296812453745032432650337923981/500726330059919092780543272014500000000000000000000), (2948970784146151675118253764765211663434561119577/8011621280958705484488692352232000000000000000000000), (172783284870916885012178923380379803275232843313427/384557821486017863255457232907136000000000000000000000), (1047863336989396057252481300251542025077343488363653/2050975047925428604029105242171392000000000000000000000), (18142683776819784760618436786376419419070180724487701/32815600766806857664465683874742272000000000000000000000)]
    reserve := (267291023/1000000000000) }

theorem tilt_046_017_valid : tilt_046_017.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_017]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_017]
  · intro i; fin_cases i <;> norm_num [tilt_046_017]
  · norm_num [tilt_046_017]
  · norm_num [tilt_046_017, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_017, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_017, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_017, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_017]

def tilt_046_018 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (655607/12500000), (782521/100000000)]
    alternative := (.spike 4 false true)
    polynomial := [(-8113508822705685404158523968414317841627067283/223519943518847656056003742857725000000000000000), (281715830200460694249/422237865381625000000), (-340911506732005578794693479881653541374032067283/111759971759423828028001871428862500000000000000), (281715830200460694249/422237865381625000000), (-673709504641305472185228435794892764906437067283/223519943518847656056003742857725000000000000000)]
    bernstein := [(632051363035164078948060048383657478810476646117/2235199435188476560560037428577250000000000000000000), (13749408401604047191763627139532730690053482542289/35763190963015624968960598857236000000000000000000000), (992134396577022391336032051053924679280863372877/2127178644640334570644496586304000000000000000000000), (4839475179238295473276616398167400103705087683537821/9155376886531999992053913307452416000000000000000000000), (310928878700647008752265431207605502434532765589153/544557733027925650084991126093824000000000000000000000)]
    reserve := (282771797/1000000000000) }

theorem tilt_046_018_valid : tilt_046_018.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_018]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_018]
  · intro i; fin_cases i <;> norm_num [tilt_046_018]
  · norm_num [tilt_046_018]
  · norm_num [tilt_046_018, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_018, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_018, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_018, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_018]

def tilt_046_019 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (1048447/20000000), (786079/100000000)]
    alternative := (.spike 4 true false)
    polynomial := [(-25919401916402563810629852836535889825784398297/718156949052461578097636473300550000000000000000), (3585733309587/5395866250000), (-1091055462757851637275647647733344691771041798297/359078474526230789048818236650275000000000000000), (3585733309587/5395866250000), (-308027360514185815820095063232879070530899885471/102593849864637368299662353328650000000000000000)]
    bernstein := [(2450363870988099392687563966898164473831358172303/7181569490524615780976364733005500000000000000000000), (50833197285803558180042617002228493865181251728851/114905111848393852495621835728088000000000000000000000), (2889691954787195958597654200287220504426064012216401/5515445368722904919789848114948224000000000000000000000), (17230903083327574762486825165815013036832249642259639/29415708633188826238879189946390528000000000000000000000), (295517417971926270119093164229534842467743225696066663/470651338131021219822067039142248448000000000000000000000)]
    reserve := (341201721/1000000000000) }

theorem tilt_046_019_valid : tilt_046_019.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_019]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_019]
  · intro i; fin_cases i <;> norm_num [tilt_046_019]
  · norm_num [tilt_046_019]
  · norm_num [tilt_046_019, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_019, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_019, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_019, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_019]

def tilt_046_020 : Row :=
  { mode := .tilt
    positive := true
    interval := ⟨(1/10), (17/160)⟩
    owners := ![0, 0, 0, 2, 0, 2, 1]
    lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
    cone := fun i => (![![0, 0, 0, (794211/100000000), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] i.1) i.2
    mu := ![(2667597/50000000), (1/100000000), (4316693/100000000), (4540321/100000000), (1/100000000), (1048447/20000000), (786079/100000000)]
    alternative := (.spike 4 true true)
    polynomial := [(-26016544996061432941406701448897129982744398297/718156949052461578097636473300550000000000000000), (3585733309587/5395866250000), (-1090949571090239411057926413713465704313981798297/359078474526230789048818236650275000000000000000), (3585733309587/5395866250000), (-307983228169202484167778017996862039806459885471/102593849864637368299662353328650000000000000000)]
    bernstein := [(1500420334336736650029543963913679610714438172303/7181569490524615780976364733005500000000000000000000), (35644998792557860240852639673116754016087611728851/114905111848393852495621835728088000000000000000000000), (2161193051529861415383246520336522110177788372216401/5515445368722904919789848114948224000000000000000000000), (13348488656825351177748521162453857052851921682259639/29415708633188826238879189946390528000000000000000000000), (233446388957111855372087416723919543769014706376066663/470651338131021219822067039142248448000000000000000000000)]
    reserve := (208926521/1000000000000) }

theorem tilt_046_020_valid : tilt_046_020.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [tilt_046_020]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [tilt_046_020]
  · intro i; fin_cases i <;> norm_num [tilt_046_020]
  · norm_num [tilt_046_020]
  · norm_num [tilt_046_020, Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · constructor
    · norm_num [tilt_046_020, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [tilt_046_020, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [tilt_046_020, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [tilt_046_020]

def tiltBundle046_row : Alternative → Row
  | .zero => tilt_046_000
  | (.spike 0 false false) => tilt_046_001
  | (.spike 0 false true) => tilt_046_002
  | (.spike 0 true false) => tilt_046_003
  | (.spike 0 true true) => tilt_046_004
  | (.spike 1 false false) => tilt_046_005
  | (.spike 1 false true) => tilt_046_006
  | (.spike 1 true false) => tilt_046_007
  | (.spike 1 true true) => tilt_046_008
  | (.spike 2 false false) => tilt_046_009
  | (.spike 2 false true) => tilt_046_010
  | (.spike 2 true false) => tilt_046_011
  | (.spike 2 true true) => tilt_046_012
  | (.spike 3 false false) => tilt_046_013
  | (.spike 3 false true) => tilt_046_014
  | (.spike 3 true false) => tilt_046_015
  | (.spike 3 true true) => tilt_046_016
  | (.spike 4 false false) => tilt_046_017
  | (.spike 4 false true) => tilt_046_018
  | (.spike 4 true false) => tilt_046_019
  | (.spike 4 true true) => tilt_046_020

def tiltBundle046 : TiltBundle where
  interval := ⟨(1/10), (17/160)⟩
  lambda := ![(7862121/50000000), (7862121/50000000), (524091/5000000), (7297239/50000000), (7297239/50000000), (368623/2500000), (706791/5000000)]
  row := tiltBundle046_row
  valid := by
    intro a
    cases a with
    | zero => exact tilt_046_000_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact tilt_046_001_valid | exact tilt_046_002_valid | exact tilt_046_003_valid | exact tilt_046_004_valid | exact tilt_046_005_valid | exact tilt_046_006_valid | exact tilt_046_007_valid | exact tilt_046_008_valid | exact tilt_046_009_valid | exact tilt_046_010_valid | exact tilt_046_011_valid | exact tilt_046_012_valid | exact tilt_046_013_valid | exact tilt_046_014_valid | exact tilt_046_015_valid | exact tilt_046_016_valid | exact tilt_046_017_valid | exact tilt_046_018_valid | exact tilt_046_019_valid | exact tilt_046_020_valid
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
