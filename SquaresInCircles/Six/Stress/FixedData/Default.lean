module
public import SquaresInCircles.Six.Stress.FixedRow

@[expose] public section

/-!
# Default fixed-stress data, excluding the separately listed hard table

Weights and domains are the audited check_A2_direct_stresses.py data
(SHA-256 e6b6a55c5ff9f8b9fade76ded788f4f232227beca24f6d5733ba91ea150a9234).
The arithmetic uses the larger R0 radius and only strict positivity. Absent
zero-weight squares receive their full normalized domain, not a dummy zero.
-/

namespace SquaresInCircles.Six.Stress.FixedData

private def q (r : ℚ) : PiBound := ⟨r,0⟩
private def p (r : ℚ) : PiBound := ⟨0,r⟩
private def b (r s : ℚ) : PiBound := ⟨r,s⟩
private def mk (key : String) (wc sc : Bool) (wd ds : Fin 8) (weight : Fin 5 → ℚ)
    (w s d : PiBound × PiBound) (ordered : Bool) : FixedRow :=
  ⟨key,⟨weight,wc,sc,wd,ds⟩,![w,s,d],ordered⟩

def defaultRows : Fin 59 → FixedRow :=
  ![
  mk "P9a" false false 6 2 ![1/3,0,0,1/3,1/3] (q (-2/5),q (2/5)) (q (1/6),q (1/2)) (b (-1/3) (1/4),b (-1/6) (1/4)) true,
  mk "P9b" false true 6 6 ![9/40,13/40,0,9/40,9/40] (q (-2/5),q (2/5)) (q (1/6),q (1/2)) (b (-1/3) (1/4),b (-1/6) (1/4)) true,
  mk "P10DW-Wp-" true false 0 0 ![11/20,0,1/20,2/5,0] (q (-2/5),q (2/5)) (p (-1/4),p (1/4)) (q (0),p (1/4)) false,
  mk "P10DW-Wp+" true false 1 0 ![1/20,0,13/20,3/10,0] (q (-2/5),q (2/5)) (p (-1/4),p (1/4)) (q (0),p (1/4)) false,
  mk "P10DW-Dp-" true false 4 0 ![11/20,0,1/20,2/5,0] (q (-2/5),q (2/5)) (p (-1/4),p (1/4)) (q (0),p (1/4)) false,
  mk "P10DW-Dp+" true false 5 0 ![1/20,0,1/2,9/20,0] (q (-2/5),q (2/5)) (p (-1/4),p (1/4)) (q (0),p (1/4)) false,
  mk "P10DW-Ws-" true false 2 0 ![2/5,0,7/20,1/4,0] (q (-2/5),q (2/5)) (p (-1/4),p (1/4)) (q (0),q (1/2)) false,
  mk "P10DW-Ws+" true false 3 0 ![2/5,0,7/20,1/4,0] (q (-2/5),q (2/5)) (p (-1/4),p (1/4)) (q (0),q (1/2)) false,
  mk "P10DW-Ds-" true false 6 0 ![3/10,0,43/100,27/100,0] (q (-2/5),q (2/5)) (p (-1/4),p (1/4)) (q (0),q (1/2)) false,
  mk "P10DW-Ds+" true false 7 0 ![2/5,0,7/20,1/4,0] (q (-2/5),q (2/5)) (p (-1/4),p (1/4)) (q (0),q (1/2)) false,
  mk "P10E-WsSp" true true 2 4 ![523/1000,1/100,0,27/100,197/1000] (q (-2/5),q (2/5)) (q (1/6),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P10E-WsDs" true true 2 2 ![379/1000,7/500,21/500,279/1000,143/500] (q (-2/5),q (2/5)) (q (-2/5),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P10E-DsSp" true true 6 4 ![119/500,21/500,167/1000,149/500,51/200] (q (-2/5),q (2/5)) (q (1/6),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P10E-DsSs" true true 6 6 ![43/250,351/1000,0,233/1000,61/250] (q (-2/5),q (2/5)) (q (-2/5),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P10E-DsDs" true true 6 2 ![263/1000,1/1000,0,46/125,46/125] (q (-2/5),q (2/5)) (q (-2/5),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P10C5-sneg" true true 2 6 ![37/125,9/25,0,27/125,16/125] (q (-2/5),q (2/5)) (q (-2/5),q (-3/10)) (q (1/2),p (1/4)) true,
  mk "P10C5-spos" true true 2 6 ![79/250,139/500,0,28/125,91/500] (q (-2/5),q (2/5)) (q (3/10),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P10C5-wneg" true true 2 6 ![469/1000,13/100,0,31/100,91/1000] (q (-2/5),q (-1/6)) (q (-3/10),q (3/10)) (q (1/2),p (1/4)) true,
  mk "P14-WsSp" false true 2 4 ![47/125,233/1000,0,43/200,22/125] (q (-2/3),p (1/4)) (q (1/6),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P14-WsDs" false true 2 2 ![407/1000,41/500,0,33/125,247/1000] (q (-1/5),p (1/4)) (q (-2/5),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P14-DsSs" false true 6 6 ![153/1000,17/100,29/100,263/1000,31/250] (q (-1/5),q (0)) (q (-2/5),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P14-4" false true 2 6 ![381/1000,53/250,0,63/250,31/200] (q (2/25),p (1/4)) (q (-2/5),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P14-5a-1" false true 2 6 ![491/1000,39/200,3/50,83/500,11/125] (q (-2/3),q (-21/50)) (q (-2/5),q (-3/20)) (q (1/2),p (1/4)) true,
  mk "P14-5a-2" false true 2 6 ![12/25,24/125,27/500,4/25,57/500] (q (-2/3),q (-21/50)) (q (-3/20),q (1/10)) (q (1/2),p (1/4)) true,
  mk "P14-5a-3" false true 2 6 ![109/250,227/1000,47/1000,153/1000,137/1000] (q (-2/3),q (-21/50)) (q (1/10),q (2/5)) (q (1/2),p (1/4)) true,
  mk "P17+eW" false false 0 0 ![1/2,0,1/20,9/20,0] (q (0),p (1/4)) (p (-1/4),p (1/4)) (q (0),p (1/4)) true,
  mk "P17-eW" false false 1 0 ![1/20,0,11/20,2/5,0] (q (0),p (1/4)) (p (-1/4),p (1/4)) (q (0),p (1/4)) true,
  mk "P17+eD" false false 4 0 ![11/20,0,1/20,2/5,0] (q (0),p (1/4)) (p (-1/4),p (1/4)) (q (0),p (1/4)) true,
  mk "P17-eD" false false 5 0 ![1/20,0,1/2,9/20,0] (q (0),p (1/4)) (p (-1/4),p (1/4)) (q (0),p (1/4)) true,
  mk "P18-low-Ws" false false 2 0 ![19/50,0,7/20,27/100,0] (q (0),b (-1/4) (1/4)) (p (-1/4),p (1/4)) (q (0),b (-1/4) (1/4)) true,
  mk "P18-low-Ds" false false 6 0 ![8/25,0,41/100,27/100,0] (q (0),b (-1/4) (1/4)) (p (-1/4),p (1/4)) (q (0),b (-1/4) (1/4)) true,
  mk "P18-near-Ds" false false 6 0 ![1/8,0,5/8,1/4,0] (q (0),p (1/4)) (p (-1/4),p (1/4)) (b (-1/4) (1/4),p (1/4)) true,
  mk "A22-Dp" false true 0 1 ![0,31/50,0,0,19/50] (q (-2/3),p (1/4)) (q (-2/5),q (1/6)) (b (-1/4) (1/4),p (1/4)) true,
  mk "SD-Ws" false false 2 0 ![11/25,0,31/100,1/4,0] (q (-2/3),q (0)) (p (-1/4),p (1/4)) (q (0),q (1/2)) true,
  mk "SD-Ds" false false 6 0 ![37/100,0,21/50,21/100,0] (q (-2/3),q (0)) (p (-1/4),p (1/4)) (q (0),q (1/2)) true,
  mk "WP" false false 1 0 ![43/100,0,19/50,19/100,0] (q (-2/3),q (0)) (p (-1/4),p (1/4)) (q (0),p (1/4)) true,
  mk "DWp+eD" false false 4 0 ![10/13,0,0,3/13,0] (q (-2/3),q (0)) (p (-1/4),p (1/4)) (p (1/12),p (1/4)) true,
  mk "DWm-eD" false false 5 0 ![1/20,0,1/2,9/20,0] (q (-2/3),q (0)) (p (-1/4),p (1/4)) (q (0),p (1/12)) true,
  mk "SP+eS" false false 0 4 ![0,0,2/3,0,1/3] (q (-2/3),p (1/4)) (p (-1/12),q (1/6)) (q (1/2),p (1/4)) true,
  mk "SP-eS" false true 0 5 ![0,7/12,0,0,5/12] (q (-2/3),p (1/4)) (q (-2/5),p (-1/12)) (q (1/2),p (1/4)) true,
  mk "DP" false true 0 1 ![0,3/5,0,0,2/5] (q (-2/3),p (1/4)) (q (-2/5),q (2/5)) (q (1/2),p (1/4)) true,
  mk "R22d-far-1" false true 2 6 ![491/1000,39/200,3/50,83/500,11/125] (q (-2/3),q (-1/2)) (q (-2/5),q (-3/20)) (q (1/2),p (1/4)) true,
  mk "R22d-far-2" false true 2 6 ![12/25,24/125,27/500,4/25,57/500] (q (-2/3),q (-1/2)) (q (-3/20),q (1/10)) (q (1/2),p (1/4)) true,
  mk "R22d-far-3" false true 2 6 ![233/500,227/1000,17/1000,153/1000,137/1000] (q (-2/3),q (-1/2)) (q (1/10),q (2/5)) (q (1/2),p (1/4)) true,
  mk "R22d-DsDs" false true 6 2 ![3/100,0,0,97/200,97/200] (q (-2/3),q (0)) (q (-2/5),q (2/5)) (q (1/2),p (1/4)) true,
  mk "R22d-DsSp" false true 6 4 ![179/1000,139/1000,4/25,279/1000,243/1000] (q (-2/3),q (0)) (q (1/6),q (2/5)) (q (1/2),p (1/4)) true,
  mk "R22d-WsDs" false true 2 2 ![201/500,11/200,17/100,177/1000,49/250] (q (-2/3),q (-1/5)) (q (-2/5),q (2/5)) (q (1/2),p (1/4)) true,
  mk "R22d-DsSs-00" false true 6 6 ![389/1000,36/125,0,4/25,163/1000] (q (-2/3),q (-1/2)) (q (-2/5),q (-3/20)) (q (1/2),p (1/4)) true,
  mk "R22d-DsSs-01" false true 6 6 ![247/500,67/500,19/125,67/500,43/500] (q (-2/3),q (-1/2)) (q (-3/20),q (1/10)) (q (1/2),p (1/4)) true,
  mk "R22d-DsSs-02" false true 6 6 ![501/1000,111/1000,189/1000,31/250,3/40] (q (-2/3),q (-1/2)) (q (1/10),q (2/5)) (q (1/2),p (1/4)) true,
  mk "R22d-DsSs-10" false true 6 6 ![121/500,53/250,237/1000,189/1000,3/25] (q (-1/2),q (-7/20)) (q (-2/5),q (-3/20)) (q (1/2),p (1/4)) true,
  mk "R22d-DsSs-11" false true 6 6 ![329/1000,209/1000,16/125,191/1000,143/1000] (q (-1/2),q (-7/20)) (q (-3/20),q (1/10)) (q (1/2),p (1/4)) true,
  mk "R22d-DsSs-12" false true 6 6 ![69/200,109/500,111/1000,9/50,73/500] (q (-1/2),q (-7/20)) (q (1/10),q (2/5)) (q (1/2),p (1/4)) true,
  mk "R22d-DsSs-20" false true 6 6 ![79/500,77/200,0,229/1000,57/250] (q (-7/20),q (-1/5)) (q (-2/5),q (-3/20)) (q (1/2),p (1/4)) true,
  mk "R22d-DsSs-21" false true 6 6 ![21/125,121/500,177/1000,61/250,169/1000] (q (-7/20),q (-1/5)) (q (-3/20),q (1/10)) (q (1/2),p (1/4)) true,
  mk "R22d-DsSs-22" false true 6 6 ![171/1000,61/250,181/1000,237/1000,167/1000] (q (-7/20),q (-1/5)) (q (1/10),q (2/5)) (q (1/2),p (1/4)) true,
  mk "A23-WsDs-1" false false 2 2 ![2/5,59/1000,31/200,183/1000,203/1000] (q (-2/3),p (1/4)) (q (-1/5),q (1/5)) (q (1/2),p (1/4)) true,
  mk "A23-DsDp-1" false false 6 1 ![11/200,481/1000,1/250,129/1000,331/1000] (q (-2/3),p (1/4)) (p (-1/4),q (-1/5)) (q (1/2),p (1/4)) true,
  mk "A23-DsDs-1" false false 6 2 ![139/1000,261/1000,9/500,71/250,149/500] (q (-2/3),p (1/4)) (p (-1/4),q (-1/5)) (q (1/2),p (1/4)) true
  ]

theorem defaultRows_valid (i : Fin 59) : (defaultRows i).spec.valid := by
  fin_cases i <;> decide

end SquaresInCircles.Six.Stress.FixedData
