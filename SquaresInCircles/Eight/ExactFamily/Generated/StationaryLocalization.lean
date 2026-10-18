module

public import SquaresInCircles.Eight.ExactFamily.Generated.StationaryFormula
public import SquaresInCircles.Eight.ExactFamily.MeanValueCover

/-!
# Stationary localization

Every simultaneous zero of `F`, `F_y` and `F_z` in `initialBox` lies in `localBox`. Closed cuts
split `initialBox` into a tree of 613 boxes of depth at most 29. Each of its 307 leaves lies in
`localBox` (21 leaves), or one target has a fixed-point enclosure on it that excludes
zero: a direct one (95 leaves) or a mean-value enclosure (191 leaves) built from enclosures
of the partial derivatives.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ExactFamily.Generated
open Arithmetic MeanValueCover

set_option maxRecDepth 1000000
set_option linter.all false

noncomputable def coverFormula259 : Formula 3 := .mul formula60 formula92
noncomputable def coverFormula260 : Formula 3 := .mul formula4 formula59
noncomputable def coverFormula261 : Formula 3 := .mul coverFormula260 formula143
noncomputable def coverFormula262 : Formula 3 := .neg coverFormula261
noncomputable def coverFormula263 : Formula 3 := .mul formula89 coverFormula262
noncomputable def coverFormula264 : Formula 3 := .mul formula34 coverFormula263
noncomputable def coverFormula265 : Formula 3 := .mul formula42 coverFormula264
noncomputable def coverFormula266 : Formula 3 := .add coverFormula259 coverFormula265
noncomputable def coverFormula267 : Formula 3 := .mul formula4 coverFormula266
noncomputable def coverFormula268 : Formula 3 := .mul formula83 formula110
noncomputable def coverFormula269 : Formula 3 := .mul formula71 formula101
noncomputable def coverFormula270 : Formula 3 := .mul formula64 formula97
noncomputable def coverFormula271 : Formula 3 := .mul formula4 formula64
noncomputable def coverFormula272 : Formula 3 := .mul coverFormula271 formula158
noncomputable def coverFormula273 : Formula 3 := .neg coverFormula272
noncomputable def coverFormula274 : Formula 3 := .mul formula96 coverFormula273
noncomputable def coverFormula275 : Formula 3 := .mul formula17 coverFormula274
noncomputable def coverFormula276 : Formula 3 := .add coverFormula270 coverFormula275
noncomputable def coverFormula277 : Formula 3 := .mul formula4 coverFormula276
noncomputable def coverFormula278 : Formula 3 := .neg coverFormula277
noncomputable def coverFormula279 : Formula 3 := .mul coverFormula278 formula70
noncomputable def coverFormula280 : Formula 3 := .mul formula4 formula71
noncomputable def coverFormula281 : Formula 3 := .mul coverFormula280 formula170
noncomputable def coverFormula282 : Formula 3 := .neg coverFormula281
noncomputable def coverFormula283 : Formula 3 := .mul formula100 coverFormula282
noncomputable def coverFormula284 : Formula 3 := .add coverFormula279 coverFormula283
noncomputable def coverFormula285 : Formula 3 := .mul formula23 coverFormula284
noncomputable def coverFormula286 : Formula 3 := .add coverFormula269 coverFormula285
noncomputable def coverFormula287 : Formula 3 := .mul formula4 coverFormula286
noncomputable def coverFormula288 : Formula 3 := .neg coverFormula287
noncomputable def coverFormula289 : Formula 3 := .mul coverFormula288 formula77
noncomputable def coverFormula290 : Formula 3 := .mul formula4 formula78
noncomputable def coverFormula291 : Formula 3 := .mul coverFormula290 formula182
noncomputable def coverFormula292 : Formula 3 := .neg coverFormula291
noncomputable def coverFormula293 : Formula 3 := .mul formula104 coverFormula292
noncomputable def coverFormula294 : Formula 3 := .add coverFormula289 coverFormula293
noncomputable def coverFormula295 : Formula 3 := .neg coverFormula294
noncomputable def coverFormula296 : Formula 3 := .mul formula36 coverFormula295
noncomputable def coverFormula297 : Formula 3 := .neg coverFormula296
noncomputable def coverFormula298 : Formula 3 := .mul formula34 coverFormula284
noncomputable def coverFormula299 : Formula 3 := .add coverFormula297 coverFormula298
noncomputable def coverFormula300 : Formula 3 := .mul formula50 coverFormula299
noncomputable def coverFormula301 : Formula 3 := .add coverFormula268 coverFormula300
noncomputable def coverFormula302 : Formula 3 := .mul formula4 coverFormula301
noncomputable def coverFormula303 : Formula 3 := .add coverFormula267 coverFormula302
noncomputable def coverFormula304 : Formula 3 := .mul formula60 formula127
noncomputable def coverFormula305 : Formula 3 := .mul formula119 formula59
noncomputable def coverFormula306 : Formula 3 := .mul formula42 coverFormula305
noncomputable def coverFormula307 : Formula 3 := .add coverFormula304 coverFormula306
noncomputable def coverFormula308 : Formula 3 := .mul formula4 coverFormula307
noncomputable def coverFormula309 : Formula 3 := .mul formula83 formula135
noncomputable def coverFormula310 : Formula 3 := .mul formula123 formula79
noncomputable def coverFormula311 : Formula 3 := .neg coverFormula310
noncomputable def coverFormula312 : Formula 3 := .mul formula119 formula71
noncomputable def coverFormula313 : Formula 3 := .add coverFormula311 coverFormula312
noncomputable def coverFormula314 : Formula 3 := .mul formula50 coverFormula313
noncomputable def coverFormula315 : Formula 3 := .add coverFormula309 coverFormula314
noncomputable def coverFormula316 : Formula 3 := .mul formula4 coverFormula315
noncomputable def coverFormula317 : Formula 3 := .add coverFormula308 coverFormula316
noncomputable def coverFyq : Formula 3 := coverFormula303
noncomputable def coverFzq : Formula 3 := coverFormula317

theorem coverFyq_diff : FyFormula.diff 0 = coverFyq := by decide +kernel
theorem coverFzq_diff : FzFormula.diff 0 = coverFzq := by decide +kernel

/-- The partial derivatives of the three targets. -/
noncomputable def coverPartial : Fin 3 → Fin 3 → Formula 3 :=
  ![![FqFormula, FyFormula, FzFormula], ![coverFyq, FyyFormula, FyzFormula],
    ![coverFzq, FyzFormula, FzzFormula]]

theorem coverPartial_eval (j k : Fin 3) (x : Fin 3 → ℝ) :
    ((stationaryTargets j).diff k).eval x = (coverPartial j k).eval x := by
  fin_cases j <;> fin_cases k
  · show (FFormula.diff 0).eval x = FqFormula.eval x; rw [Fq_diff]
  · show (FFormula.diff 1).eval x = FyFormula.eval x; rw [Fy_diff]
  · show (FFormula.diff 2).eval x = FzFormula.eval x; rw [Fz_diff]
  · show (FyFormula.diff 0).eval x = coverFyq.eval x; rw [coverFyq_diff]
  · show (FyFormula.diff 1).eval x = FyyFormula.eval x; rw [Fyy_diff]
  · show (FyFormula.diff 2).eval x = FyzFormula.eval x; rw [Fyz_diff]
  · show (FzFormula.diff 0).eval x = coverFzq.eval x; rw [coverFzq_diff]
  · exact mixed_partials x
  · show (FzFormula.diff 2).eval x = FzzFormula.eval x; rw [Fzz_diff]

/-- The radicands and denominators of the three targets are positive on `initialBox`. -/
theorem coverRegular (j : Fin 3) :
    ∀ x, initialBox.Mem x → (stationaryTargets j).RegularAt x := by
  intro x hx
  fin_cases j <;> exact FixedEval.regular_sound (p := 40) (by decide +kernel) hx

noncomputable def coverBox0 : QBox 3 := initialBox
noncomputable def coverBox1 : QBox 3 := coverBox0.left 1 (-3/4)
noncomputable def coverBox2 : QBox 3 := coverBox1.left 1 (-7/8)
noncomputable def coverBox3 : QBox 3 := coverBox2.left 2 (1/20)
noncomputable def coverBox4 : QBox 3 := coverBox3.left 1 (-15/16)
noncomputable def coverBox5 : QBox 3 := coverBox4.left 0 (312649/80000)
noncomputable def coverBox6 : QBox 3 := coverBox5.left 2 (1/40)
noncomputable def coverBox7 : QBox 3 := coverBox6.left 1 (-31/32)
noncomputable def coverBox8 : QBox 3 := coverBox6.right 1 (-31/32)
noncomputable def coverBox9 : QBox 3 := coverBox5.right 2 (1/40)
noncomputable def coverBox10 : QBox 3 := coverBox9.left 1 (-31/32)
noncomputable def coverBox11 : QBox 3 := coverBox9.right 1 (-31/32)
noncomputable def coverBox12 : QBox 3 := coverBox4.right 0 (312649/80000)
noncomputable def coverBox13 : QBox 3 := coverBox12.left 2 (1/40)
noncomputable def coverBox14 : QBox 3 := coverBox13.left 1 (-31/32)
noncomputable def coverBox15 : QBox 3 := coverBox14.left 0 (625897/160000)
noncomputable def coverBox16 : QBox 3 := coverBox15.left 2 (1/80)
noncomputable def coverBox17 : QBox 3 := coverBox15.right 2 (1/80)
noncomputable def coverBox18 : QBox 3 := coverBox14.right 0 (625897/160000)
noncomputable def coverBox19 : QBox 3 := coverBox18.left 2 (1/80)
noncomputable def coverBox20 : QBox 3 := coverBox18.right 2 (1/80)
noncomputable def coverBox21 : QBox 3 := coverBox20.left 1 (-63/64)
noncomputable def coverBox22 : QBox 3 := coverBox21.left 0 (1252393/320000)
noncomputable def coverBox23 : QBox 3 := coverBox21.right 0 (1252393/320000)
noncomputable def coverBox24 : QBox 3 := coverBox23.left 2 (3/160)
noncomputable def coverBox25 : QBox 3 := coverBox23.right 2 (3/160)
noncomputable def coverBox26 : QBox 3 := coverBox20.right 1 (-63/64)
noncomputable def coverBox27 : QBox 3 := coverBox13.right 1 (-31/32)
noncomputable def coverBox28 : QBox 3 := coverBox12.right 2 (1/40)
noncomputable def coverBox29 : QBox 3 := coverBox28.left 1 (-31/32)
noncomputable def coverBox30 : QBox 3 := coverBox29.left 0 (625897/160000)
noncomputable def coverBox31 : QBox 3 := coverBox30.left 2 (3/80)
noncomputable def coverBox32 : QBox 3 := coverBox30.right 2 (3/80)
noncomputable def coverBox33 : QBox 3 := coverBox29.right 0 (625897/160000)
noncomputable def coverBox34 : QBox 3 := coverBox33.left 2 (3/80)
noncomputable def coverBox35 : QBox 3 := coverBox34.left 1 (-63/64)
noncomputable def coverBox36 : QBox 3 := coverBox34.right 1 (-63/64)
noncomputable def coverBox37 : QBox 3 := coverBox36.left 0 (1252393/320000)
noncomputable def coverBox38 : QBox 3 := coverBox36.right 0 (1252393/320000)
noncomputable def coverBox39 : QBox 3 := coverBox38.left 2 (1/32)
noncomputable def coverBox40 : QBox 3 := coverBox38.right 2 (1/32)
noncomputable def coverBox41 : QBox 3 := coverBox33.right 2 (3/80)
noncomputable def coverBox42 : QBox 3 := coverBox28.right 1 (-31/32)
noncomputable def coverBox43 : QBox 3 := coverBox42.left 0 (625897/160000)
noncomputable def coverBox44 : QBox 3 := coverBox43.left 2 (3/80)
noncomputable def coverBox45 : QBox 3 := coverBox43.right 2 (3/80)
noncomputable def coverBox46 : QBox 3 := coverBox42.right 0 (625897/160000)
noncomputable def coverBox47 : QBox 3 := coverBox46.left 2 (3/80)
noncomputable def coverBox48 : QBox 3 := coverBox47.left 1 (-61/64)
noncomputable def coverBox49 : QBox 3 := coverBox48.left 0 (1252393/320000)
noncomputable def coverBox50 : QBox 3 := coverBox48.right 0 (1252393/320000)
noncomputable def coverBox51 : QBox 3 := coverBox50.left 2 (1/32)
noncomputable def coverBox52 : QBox 3 := coverBox50.right 2 (1/32)
noncomputable def coverBox53 : QBox 3 := coverBox52.left 1 (-123/128)
noncomputable def coverBox54 : QBox 3 := coverBox52.right 1 (-123/128)
noncomputable def coverBox55 : QBox 3 := coverBox47.right 1 (-61/64)
noncomputable def coverBox56 : QBox 3 := coverBox46.right 2 (3/80)
noncomputable def coverBox57 : QBox 3 := coverBox56.left 1 (-61/64)
noncomputable def coverBox58 : QBox 3 := coverBox57.left 0 (1252393/320000)
noncomputable def coverBox59 : QBox 3 := coverBox57.right 0 (1252393/320000)
noncomputable def coverBox60 : QBox 3 := coverBox56.right 1 (-61/64)
noncomputable def coverBox61 : QBox 3 := coverBox60.left 0 (1252393/320000)
noncomputable def coverBox62 : QBox 3 := coverBox60.right 0 (1252393/320000)
noncomputable def coverBox63 : QBox 3 := coverBox62.left 2 (7/160)
noncomputable def coverBox64 : QBox 3 := coverBox62.right 2 (7/160)
noncomputable def coverBox65 : QBox 3 := coverBox64.left 1 (-121/128)
noncomputable def coverBox66 : QBox 3 := coverBox64.right 1 (-121/128)
noncomputable def coverBox67 : QBox 3 := coverBox66.left 0 (501077/128000)
noncomputable def coverBox68 : QBox 3 := coverBox66.right 0 (501077/128000)
noncomputable def coverBox69 : QBox 3 := coverBox68.left 2 (3/64)
noncomputable def coverBox70 : QBox 3 := coverBox68.right 2 (3/64)
noncomputable def coverBox71 : QBox 3 := coverBox70.left 1 (-241/256)
noncomputable def coverBox72 : QBox 3 := coverBox70.right 1 (-241/256)
noncomputable def coverBox73 : QBox 3 := coverBox3.right 1 (-15/16)
noncomputable def coverBox74 : QBox 3 := coverBox73.left 0 (312649/80000)
noncomputable def coverBox75 : QBox 3 := coverBox74.left 2 (1/40)
noncomputable def coverBox76 : QBox 3 := coverBox74.right 2 (1/40)
noncomputable def coverBox77 : QBox 3 := coverBox76.left 1 (-29/32)
noncomputable def coverBox78 : QBox 3 := coverBox76.right 1 (-29/32)
noncomputable def coverBox79 : QBox 3 := coverBox73.right 0 (312649/80000)
noncomputable def coverBox80 : QBox 3 := coverBox79.left 2 (1/40)
noncomputable def coverBox81 : QBox 3 := coverBox79.right 2 (1/40)
noncomputable def coverBox82 : QBox 3 := coverBox81.left 1 (-29/32)
noncomputable def coverBox83 : QBox 3 := coverBox82.left 0 (625897/160000)
noncomputable def coverBox84 : QBox 3 := coverBox83.left 2 (3/80)
noncomputable def coverBox85 : QBox 3 := coverBox83.right 2 (3/80)
noncomputable def coverBox86 : QBox 3 := coverBox82.right 0 (625897/160000)
noncomputable def coverBox87 : QBox 3 := coverBox86.left 2 (3/80)
noncomputable def coverBox88 : QBox 3 := coverBox86.right 2 (3/80)
noncomputable def coverBox89 : QBox 3 := coverBox81.right 1 (-29/32)
noncomputable def coverBox90 : QBox 3 := coverBox2.right 2 (1/20)
noncomputable def coverBox91 : QBox 3 := coverBox90.left 1 (-15/16)
noncomputable def coverBox92 : QBox 3 := coverBox91.left 0 (312649/80000)
noncomputable def coverBox93 : QBox 3 := coverBox92.left 2 (3/40)
noncomputable def coverBox94 : QBox 3 := coverBox93.left 1 (-31/32)
noncomputable def coverBox95 : QBox 3 := coverBox93.right 1 (-31/32)
noncomputable def coverBox96 : QBox 3 := coverBox92.right 2 (3/40)
noncomputable def coverBox97 : QBox 3 := coverBox91.right 0 (312649/80000)
noncomputable def coverBox98 : QBox 3 := coverBox97.left 2 (3/40)
noncomputable def coverBox99 : QBox 3 := coverBox98.left 1 (-31/32)
noncomputable def coverBox100 : QBox 3 := coverBox98.right 1 (-31/32)
noncomputable def coverBox101 : QBox 3 := coverBox100.left 0 (625897/160000)
noncomputable def coverBox102 : QBox 3 := coverBox101.left 2 (1/16)
noncomputable def coverBox103 : QBox 3 := coverBox101.right 2 (1/16)
noncomputable def coverBox104 : QBox 3 := coverBox100.right 0 (625897/160000)
noncomputable def coverBox105 : QBox 3 := coverBox104.left 2 (1/16)
noncomputable def coverBox106 : QBox 3 := coverBox105.left 1 (-61/64)
noncomputable def coverBox107 : QBox 3 := coverBox105.right 1 (-61/64)
noncomputable def coverBox108 : QBox 3 := coverBox104.right 2 (1/16)
noncomputable def coverBox109 : QBox 3 := coverBox97.right 2 (3/40)
noncomputable def coverBox110 : QBox 3 := coverBox90.right 1 (-15/16)
noncomputable def coverBox111 : QBox 3 := coverBox110.left 0 (312649/80000)
noncomputable def coverBox112 : QBox 3 := coverBox111.left 2 (3/40)
noncomputable def coverBox113 : QBox 3 := coverBox112.left 1 (-29/32)
noncomputable def coverBox114 : QBox 3 := coverBox112.right 1 (-29/32)
noncomputable def coverBox115 : QBox 3 := coverBox111.right 2 (3/40)
noncomputable def coverBox116 : QBox 3 := coverBox115.left 1 (-29/32)
noncomputable def coverBox117 : QBox 3 := coverBox115.right 1 (-29/32)
noncomputable def coverBox118 : QBox 3 := coverBox110.right 0 (312649/80000)
noncomputable def coverBox119 : QBox 3 := coverBox118.left 2 (3/40)
noncomputable def coverBox120 : QBox 3 := coverBox119.left 1 (-29/32)
noncomputable def coverBox121 : QBox 3 := coverBox120.left 0 (625897/160000)
noncomputable def coverBox122 : QBox 3 := coverBox121.left 2 (1/16)
noncomputable def coverBox123 : QBox 3 := coverBox121.right 2 (1/16)
noncomputable def coverBox124 : QBox 3 := coverBox120.right 0 (625897/160000)
noncomputable def coverBox125 : QBox 3 := coverBox124.left 2 (1/16)
noncomputable def coverBox126 : QBox 3 := coverBox125.left 1 (-59/64)
noncomputable def coverBox127 : QBox 3 := coverBox126.left 0 (1252393/320000)
noncomputable def coverBox128 : QBox 3 := coverBox126.right 0 (1252393/320000)
noncomputable def coverBox129 : QBox 3 := coverBox128.left 2 (9/160)
noncomputable def coverBox130 : QBox 3 := coverBox129.left 1 (-119/128)
noncomputable def coverBox131 : QBox 3 := coverBox130.left 0 (501077/128000)
noncomputable def coverBox132 : QBox 3 := coverBox130.right 0 (501077/128000)
noncomputable def coverBox133 : QBox 3 := coverBox132.left 2 (17/320)
noncomputable def coverBox134 : QBox 3 := coverBox133.left 1 (-239/256)
noncomputable def coverBox135 : QBox 3 := coverBox134.left 0 (5011369/1280000)
noncomputable def coverBox136 : QBox 3 := coverBox134.right 0 (5011369/1280000)
noncomputable def coverBox137 : QBox 3 := coverBox136.left 2 (33/640)
noncomputable def coverBox138 : QBox 3 := coverBox136.right 2 (33/640)
noncomputable def coverBox139 : QBox 3 := coverBox138.left 1 (-479/512)
noncomputable def coverBox140 : QBox 3 := coverBox138.right 1 (-479/512)
noncomputable def coverBox141 : QBox 3 := coverBox133.right 1 (-239/256)
noncomputable def coverBox142 : QBox 3 := coverBox132.right 2 (17/320)
noncomputable def coverBox143 : QBox 3 := coverBox142.left 1 (-239/256)
noncomputable def coverBox144 : QBox 3 := coverBox142.right 1 (-239/256)
noncomputable def coverBox145 : QBox 3 := coverBox144.left 0 (5011369/1280000)
noncomputable def coverBox146 : QBox 3 := coverBox144.right 0 (5011369/1280000)
noncomputable def coverBox147 : QBox 3 := coverBox146.left 2 (7/128)
noncomputable def coverBox148 : QBox 3 := coverBox146.right 2 (7/128)
noncomputable def coverBox149 : QBox 3 := coverBox148.left 1 (-477/512)
noncomputable def coverBox150 : QBox 3 := coverBox148.right 1 (-477/512)
noncomputable def coverBox151 : QBox 3 := coverBox150.left 0 (10023337/2560000)
noncomputable def coverBox152 : QBox 3 := coverBox150.right 0 (10023337/2560000)
noncomputable def coverBox153 : QBox 3 := coverBox152.left 2 (71/1280)
noncomputable def coverBox154 : QBox 3 := coverBox152.right 2 (71/1280)
noncomputable def coverBox155 : QBox 3 := coverBox129.right 1 (-119/128)
noncomputable def coverBox156 : QBox 3 := coverBox128.right 2 (9/160)
noncomputable def coverBox157 : QBox 3 := coverBox156.left 1 (-119/128)
noncomputable def coverBox158 : QBox 3 := coverBox156.right 1 (-119/128)
noncomputable def coverBox159 : QBox 3 := coverBox158.left 0 (501077/128000)
noncomputable def coverBox160 : QBox 3 := coverBox158.right 0 (501077/128000)
noncomputable def coverBox161 : QBox 3 := coverBox160.left 2 (19/320)
noncomputable def coverBox162 : QBox 3 := coverBox161.left 1 (-237/256)
noncomputable def coverBox163 : QBox 3 := coverBox162.left 0 (5011369/1280000)
noncomputable def coverBox164 : QBox 3 := coverBox162.right 0 (5011369/1280000)
noncomputable def coverBox165 : QBox 3 := coverBox164.left 2 (37/640)
noncomputable def coverBox166 : QBox 3 := coverBox165.left 1 (-475/512)
noncomputable def coverBox167 : QBox 3 := coverBox166.left 0 (10023337/2560000)
noncomputable def coverBox168 : QBox 3 := coverBox166.right 0 (10023337/2560000)
noncomputable def coverBox169 : QBox 3 := coverBox168.left 2 (73/1280)
noncomputable def coverBox170 : QBox 3 := coverBox169.left 1 (-951/1024)
noncomputable def coverBox171 : QBox 3 := coverBox169.right 1 (-951/1024)
noncomputable def coverBox172 : QBox 3 := coverBox168.right 2 (73/1280)
noncomputable def coverBox173 : QBox 3 := coverBox165.right 1 (-475/512)
noncomputable def coverBox174 : QBox 3 := coverBox164.right 2 (37/640)
noncomputable def coverBox175 : QBox 3 := coverBox174.left 1 (-475/512)
noncomputable def coverBox176 : QBox 3 := coverBox174.right 1 (-475/512)
noncomputable def coverBox177 : QBox 3 := coverBox176.left 0 (10023337/2560000)
noncomputable def coverBox178 : QBox 3 := coverBox176.right 0 (10023337/2560000)
noncomputable def coverBox179 : QBox 3 := coverBox178.left 2 (15/256)
noncomputable def coverBox180 : QBox 3 := coverBox179.left 1 (-949/1024)
noncomputable def coverBox181 : QBox 3 := coverBox179.right 1 (-949/1024)
noncomputable def coverBox182 : QBox 3 := coverBox181.left 0 (20047273/5120000)
noncomputable def coverBox183 : QBox 3 := coverBox181.right 0 (20047273/5120000)
noncomputable def coverBox184 : QBox 3 := coverBox183.left 2 (149/2560)
noncomputable def coverBox185 : QBox 3 := coverBox183.right 2 (149/2560)
noncomputable def coverBox186 : QBox 3 := coverBox178.right 2 (15/256)
noncomputable def coverBox187 : QBox 3 := coverBox161.right 1 (-237/256)
noncomputable def coverBox188 : QBox 3 := coverBox187.left 0 (5011369/1280000)
noncomputable def coverBox189 : QBox 3 := coverBox187.right 0 (5011369/1280000)
noncomputable def coverBox190 : QBox 3 := coverBox189.left 2 (37/640)
noncomputable def coverBox191 : QBox 3 := coverBox189.right 2 (37/640)
noncomputable def coverBox192 : QBox 3 := coverBox191.left 1 (-473/512)
noncomputable def coverBox193 : QBox 3 := coverBox192.left 0 (10023337/2560000)
noncomputable def coverBox194 : QBox 3 := coverBox192.right 0 (10023337/2560000)
noncomputable def coverBox195 : QBox 3 := coverBox194.left 2 (15/256)
noncomputable def coverBox196 : QBox 3 := coverBox194.right 2 (15/256)
noncomputable def coverBox197 : QBox 3 := coverBox196.left 1 (-947/1024)
noncomputable def coverBox198 : QBox 3 := coverBox197.left 0 (20047273/5120000)
noncomputable def coverBox199 : QBox 3 := coverBox197.right 0 (20047273/5120000)
noncomputable def coverBox200 : QBox 3 := coverBox199.left 2 (151/2560)
noncomputable def coverBox201 : QBox 3 := coverBox199.right 2 (151/2560)
noncomputable def coverBox202 : QBox 3 := coverBox196.right 1 (-947/1024)
noncomputable def coverBox203 : QBox 3 := coverBox191.right 1 (-473/512)
noncomputable def coverBox204 : QBox 3 := coverBox160.right 2 (19/320)
noncomputable def coverBox205 : QBox 3 := coverBox204.left 1 (-237/256)
noncomputable def coverBox206 : QBox 3 := coverBox204.right 1 (-237/256)
noncomputable def coverBox207 : QBox 3 := coverBox206.left 0 (5011369/1280000)
noncomputable def coverBox208 : QBox 3 := coverBox206.right 0 (5011369/1280000)
noncomputable def coverBox209 : QBox 3 := coverBox208.left 2 (39/640)
noncomputable def coverBox210 : QBox 3 := coverBox209.left 1 (-473/512)
noncomputable def coverBox211 : QBox 3 := coverBox210.left 0 (10023337/2560000)
noncomputable def coverBox212 : QBox 3 := coverBox210.right 0 (10023337/2560000)
noncomputable def coverBox213 : QBox 3 := coverBox212.left 2 (77/1280)
noncomputable def coverBox214 : QBox 3 := coverBox213.left 1 (-947/1024)
noncomputable def coverBox215 : QBox 3 := coverBox213.right 1 (-947/1024)
noncomputable def coverBox216 : QBox 3 := coverBox215.left 0 (20047273/5120000)
noncomputable def coverBox217 : QBox 3 := coverBox215.right 0 (20047273/5120000)
noncomputable def coverBox218 : QBox 3 := coverBox217.left 2 (153/2560)
noncomputable def coverBox219 : QBox 3 := coverBox218.left 1 (-1893/2048)
noncomputable def coverBox220 : QBox 3 := coverBox218.right 1 (-1893/2048)
noncomputable def coverBox221 : QBox 3 := coverBox217.right 2 (153/2560)
noncomputable def coverBox222 : QBox 3 := coverBox212.right 2 (77/1280)
noncomputable def coverBox223 : QBox 3 := coverBox209.right 1 (-473/512)
noncomputable def coverBox224 : QBox 3 := coverBox223.left 0 (10023337/2560000)
noncomputable def coverBox225 : QBox 3 := coverBox223.right 0 (10023337/2560000)
noncomputable def coverBox226 : QBox 3 := coverBox225.left 2 (77/1280)
noncomputable def coverBox227 : QBox 3 := coverBox225.right 2 (77/1280)
noncomputable def coverBox228 : QBox 3 := coverBox227.left 1 (-945/1024)
noncomputable def coverBox229 : QBox 3 := coverBox228.left 0 (20047273/5120000)
noncomputable def coverBox230 : QBox 3 := coverBox228.right 0 (20047273/5120000)
noncomputable def coverBox231 : QBox 3 := coverBox230.left 2 (31/512)
noncomputable def coverBox232 : QBox 3 := coverBox231.left 1 (-1891/2048)
noncomputable def coverBox233 : QBox 3 := coverBox231.right 1 (-1891/2048)
noncomputable def coverBox234 : QBox 3 := coverBox230.right 2 (31/512)
noncomputable def coverBox235 : QBox 3 := coverBox227.right 1 (-945/1024)
noncomputable def coverBox236 : QBox 3 := coverBox235.left 0 (20047273/5120000)
noncomputable def coverBox237 : QBox 3 := coverBox235.right 0 (20047273/5120000)
noncomputable def coverBox238 : QBox 3 := coverBox237.left 2 (31/512)
noncomputable def coverBox239 : QBox 3 := coverBox237.right 2 (31/512)
noncomputable def coverBox240 : QBox 3 := coverBox239.left 1 (-1889/2048)
noncomputable def coverBox241 : QBox 3 := coverBox239.right 1 (-1889/2048)
noncomputable def coverBox242 : QBox 3 := coverBox208.right 2 (39/640)
noncomputable def coverBox243 : QBox 3 := coverBox242.left 1 (-473/512)
noncomputable def coverBox244 : QBox 3 := coverBox242.right 1 (-473/512)
noncomputable def coverBox245 : QBox 3 := coverBox244.left 0 (10023337/2560000)
noncomputable def coverBox246 : QBox 3 := coverBox244.right 0 (10023337/2560000)
noncomputable def coverBox247 : QBox 3 := coverBox246.left 2 (79/1280)
noncomputable def coverBox248 : QBox 3 := coverBox247.left 1 (-945/1024)
noncomputable def coverBox249 : QBox 3 := coverBox247.right 1 (-945/1024)
noncomputable def coverBox250 : QBox 3 := coverBox249.left 0 (20047273/5120000)
noncomputable def coverBox251 : QBox 3 := coverBox249.right 0 (20047273/5120000)
noncomputable def coverBox252 : QBox 3 := coverBox246.right 2 (79/1280)
noncomputable def coverBox253 : QBox 3 := coverBox125.right 1 (-59/64)
noncomputable def coverBox254 : QBox 3 := coverBox253.left 0 (1252393/320000)
noncomputable def coverBox255 : QBox 3 := coverBox253.right 0 (1252393/320000)
noncomputable def coverBox256 : QBox 3 := coverBox255.left 2 (9/160)
noncomputable def coverBox257 : QBox 3 := coverBox255.right 2 (9/160)
noncomputable def coverBox258 : QBox 3 := coverBox257.left 1 (-117/128)
noncomputable def coverBox259 : QBox 3 := coverBox258.left 0 (501077/128000)
noncomputable def coverBox260 : QBox 3 := coverBox258.right 0 (501077/128000)
noncomputable def coverBox261 : QBox 3 := coverBox260.left 2 (19/320)
noncomputable def coverBox262 : QBox 3 := coverBox260.right 2 (19/320)
noncomputable def coverBox263 : QBox 3 := coverBox262.left 1 (-235/256)
noncomputable def coverBox264 : QBox 3 := coverBox263.left 0 (5011369/1280000)
noncomputable def coverBox265 : QBox 3 := coverBox263.right 0 (5011369/1280000)
noncomputable def coverBox266 : QBox 3 := coverBox265.left 2 (39/640)
noncomputable def coverBox267 : QBox 3 := coverBox265.right 2 (39/640)
noncomputable def coverBox268 : QBox 3 := coverBox267.left 1 (-471/512)
noncomputable def coverBox269 : QBox 3 := coverBox268.left 0 (10023337/2560000)
noncomputable def coverBox270 : QBox 3 := coverBox268.right 0 (10023337/2560000)
noncomputable def coverBox271 : QBox 3 := coverBox270.left 2 (79/1280)
noncomputable def coverBox272 : QBox 3 := coverBox271.left 1 (-943/1024)
noncomputable def coverBox273 : QBox 3 := coverBox272.left 0 (20047273/5120000)
noncomputable def coverBox274 : QBox 3 := coverBox272.right 0 (20047273/5120000)
noncomputable def coverBox275 : QBox 3 := coverBox274.left 2 (157/2560)
noncomputable def coverBox276 : QBox 3 := coverBox275.left 1 (-1887/2048)
noncomputable def coverBox277 : QBox 3 := coverBox276.left 0 (8019029/2048000)
noncomputable def coverBox278 : QBox 3 := coverBox277.left 2 (313/5120)
noncomputable def coverBox279 : QBox 3 := coverBox277.right 2 (313/5120)
noncomputable def coverBox280 : QBox 3 := coverBox279.left 1 (-3775/4096)
noncomputable def coverBox281 : QBox 3 := coverBox279.right 1 (-3775/4096)
noncomputable def coverBox282 : QBox 3 := coverBox276.right 0 (8019029/2048000)
noncomputable def coverBox283 : QBox 3 := coverBox275.right 1 (-1887/2048)
noncomputable def coverBox284 : QBox 3 := coverBox274.right 2 (157/2560)
noncomputable def coverBox285 : QBox 3 := coverBox284.left 1 (-1887/2048)
noncomputable def coverBox286 : QBox 3 := coverBox284.right 1 (-1887/2048)
noncomputable def coverBox287 : QBox 3 := coverBox286.left 0 (8019029/2048000)
noncomputable def coverBox288 : QBox 3 := coverBox287.left 2 (63/1024)
noncomputable def coverBox289 : QBox 3 := coverBox288.left 1 (-3773/4096)
noncomputable def coverBox290 : QBox 3 := coverBox289.left 0 (80189691/20480000)
noncomputable def coverBox291 : QBox 3 := coverBox289.right 0 (80189691/20480000)
noncomputable def coverBox292 : QBox 3 := coverBox288.right 1 (-3773/4096)
noncomputable def coverBox293 : QBox 3 := coverBox287.right 2 (63/1024)
noncomputable def coverBox294 : QBox 3 := coverBox293.left 1 (-3773/4096)
noncomputable def coverBox295 : QBox 3 := coverBox293.right 1 (-3773/4096)
noncomputable def coverBox296 : QBox 3 := coverBox295.left 0 (80189691/20480000)
noncomputable def coverBox297 : QBox 3 := coverBox295.right 0 (80189691/20480000)
noncomputable def coverBox298 : QBox 3 := coverBox286.right 0 (8019029/2048000)
noncomputable def coverBox299 : QBox 3 := coverBox271.right 1 (-943/1024)
noncomputable def coverBox300 : QBox 3 := coverBox270.right 2 (79/1280)
noncomputable def coverBox301 : QBox 3 := coverBox300.left 1 (-943/1024)
noncomputable def coverBox302 : QBox 3 := coverBox301.left 0 (20047273/5120000)
noncomputable def coverBox303 : QBox 3 := coverBox301.right 0 (20047273/5120000)
noncomputable def coverBox304 : QBox 3 := coverBox300.right 1 (-943/1024)
noncomputable def coverBox305 : QBox 3 := coverBox304.left 0 (20047273/5120000)
noncomputable def coverBox306 : QBox 3 := coverBox304.right 0 (20047273/5120000)
noncomputable def coverBox307 : QBox 3 := coverBox306.left 2 (159/2560)
noncomputable def coverBox308 : QBox 3 := coverBox307.left 1 (-1885/2048)
noncomputable def coverBox309 : QBox 3 := coverBox308.left 0 (8019029/2048000)
noncomputable def coverBox310 : QBox 3 := coverBox309.left 2 (317/5120)
noncomputable def coverBox311 : QBox 3 := coverBox310.left 1 (-3771/4096)
noncomputable def coverBox312 : QBox 3 := coverBox311.left 0 (80189691/20480000)
noncomputable def coverBox313 : QBox 3 := coverBox311.right 0 (80189691/20480000)
noncomputable def coverBox314 : QBox 3 := coverBox310.right 1 (-3771/4096)
noncomputable def coverBox315 : QBox 3 := coverBox314.left 0 (80189691/20480000)
noncomputable def coverBox316 : QBox 3 := coverBox314.right 0 (80189691/20480000)
noncomputable def coverBox317 : QBox 3 := coverBox309.right 2 (317/5120)
noncomputable def coverBox318 : QBox 3 := coverBox317.left 1 (-3771/4096)
noncomputable def coverBox319 : QBox 3 := coverBox317.right 1 (-3771/4096)
noncomputable def coverBox320 : QBox 3 := coverBox319.left 0 (80189691/20480000)
noncomputable def coverBox321 : QBox 3 := coverBox319.right 0 (80189691/20480000)
noncomputable def coverBox322 : QBox 3 := coverBox308.right 0 (8019029/2048000)
noncomputable def coverBox323 : QBox 3 := coverBox307.right 1 (-1885/2048)
noncomputable def coverBox324 : QBox 3 := coverBox323.left 0 (8019029/2048000)
noncomputable def coverBox325 : QBox 3 := coverBox324.left 2 (317/5120)
noncomputable def coverBox326 : QBox 3 := coverBox324.right 2 (317/5120)
noncomputable def coverBox327 : QBox 3 := coverBox326.left 1 (-3769/4096)
noncomputable def coverBox328 : QBox 3 := coverBox327.left 0 (80189691/20480000)
noncomputable def coverBox329 : QBox 3 := coverBox327.right 0 (80189691/20480000)
noncomputable def coverBox330 : QBox 3 := coverBox326.right 1 (-3769/4096)
noncomputable def coverBox331 : QBox 3 := coverBox323.right 0 (8019029/2048000)
noncomputable def coverBox332 : QBox 3 := coverBox306.right 2 (159/2560)
noncomputable def coverBox333 : QBox 3 := coverBox332.left 1 (-1885/2048)
noncomputable def coverBox334 : QBox 3 := coverBox332.right 1 (-1885/2048)
noncomputable def coverBox335 : QBox 3 := coverBox334.left 0 (8019029/2048000)
noncomputable def coverBox336 : QBox 3 := coverBox335.left 2 (319/5120)
noncomputable def coverBox337 : QBox 3 := coverBox336.left 1 (-3769/4096)
noncomputable def coverBox338 : QBox 3 := coverBox337.left 0 (80189691/20480000)
noncomputable def coverBox339 : QBox 3 := coverBox337.right 0 (80189691/20480000)
noncomputable def coverBox340 : QBox 3 := coverBox336.right 1 (-3769/4096)
noncomputable def coverBox341 : QBox 3 := coverBox340.left 0 (80189691/20480000)
noncomputable def coverBox342 : QBox 3 := coverBox340.right 0 (80189691/20480000)
noncomputable def coverBox343 : QBox 3 := coverBox335.right 2 (319/5120)
noncomputable def coverBox344 : QBox 3 := coverBox334.right 0 (8019029/2048000)
noncomputable def coverBox345 : QBox 3 := coverBox267.right 1 (-471/512)
noncomputable def coverBox346 : QBox 3 := coverBox345.left 0 (10023337/2560000)
noncomputable def coverBox347 : QBox 3 := coverBox345.right 0 (10023337/2560000)
noncomputable def coverBox348 : QBox 3 := coverBox347.left 2 (79/1280)
noncomputable def coverBox349 : QBox 3 := coverBox347.right 2 (79/1280)
noncomputable def coverBox350 : QBox 3 := coverBox349.left 1 (-941/1024)
noncomputable def coverBox351 : QBox 3 := coverBox350.left 0 (20047273/5120000)
noncomputable def coverBox352 : QBox 3 := coverBox350.right 0 (20047273/5120000)
noncomputable def coverBox353 : QBox 3 := coverBox352.left 2 (159/2560)
noncomputable def coverBox354 : QBox 3 := coverBox352.right 2 (159/2560)
noncomputable def coverBox355 : QBox 3 := coverBox354.left 1 (-1883/2048)
noncomputable def coverBox356 : QBox 3 := coverBox355.left 0 (8019029/2048000)
noncomputable def coverBox357 : QBox 3 := coverBox356.left 2 (319/5120)
noncomputable def coverBox358 : QBox 3 := coverBox356.right 2 (319/5120)
noncomputable def coverBox359 : QBox 3 := coverBox358.left 1 (-3767/4096)
noncomputable def coverBox360 : QBox 3 := coverBox359.left 0 (80189691/20480000)
noncomputable def coverBox361 : QBox 3 := coverBox359.right 0 (80189691/20480000)
noncomputable def coverBox362 : QBox 3 := coverBox358.right 1 (-3767/4096)
noncomputable def coverBox363 : QBox 3 := coverBox355.right 0 (8019029/2048000)
noncomputable def coverBox364 : QBox 3 := coverBox354.right 1 (-1883/2048)
noncomputable def coverBox365 : QBox 3 := coverBox349.right 1 (-941/1024)
noncomputable def coverBox366 : QBox 3 := coverBox262.right 1 (-235/256)
noncomputable def coverBox367 : QBox 3 := coverBox257.right 1 (-117/128)
noncomputable def coverBox368 : QBox 3 := coverBox124.right 2 (1/16)
noncomputable def coverBox369 : QBox 3 := coverBox368.left 1 (-59/64)
noncomputable def coverBox370 : QBox 3 := coverBox368.right 1 (-59/64)
noncomputable def coverBox371 : QBox 3 := coverBox370.left 0 (1252393/320000)
noncomputable def coverBox372 : QBox 3 := coverBox370.right 0 (1252393/320000)
noncomputable def coverBox373 : QBox 3 := coverBox372.left 2 (11/160)
noncomputable def coverBox374 : QBox 3 := coverBox373.left 1 (-117/128)
noncomputable def coverBox375 : QBox 3 := coverBox374.left 0 (501077/128000)
noncomputable def coverBox376 : QBox 3 := coverBox374.right 0 (501077/128000)
noncomputable def coverBox377 : QBox 3 := coverBox376.left 2 (21/320)
noncomputable def coverBox378 : QBox 3 := coverBox377.left 1 (-235/256)
noncomputable def coverBox379 : QBox 3 := coverBox378.left 0 (5011369/1280000)
noncomputable def coverBox380 : QBox 3 := coverBox378.right 0 (5011369/1280000)
noncomputable def coverBox381 : QBox 3 := coverBox380.left 2 (41/640)
noncomputable def coverBox382 : QBox 3 := coverBox381.left 1 (-471/512)
noncomputable def coverBox383 : QBox 3 := coverBox381.right 1 (-471/512)
noncomputable def coverBox384 : QBox 3 := coverBox383.left 0 (10023337/2560000)
noncomputable def coverBox385 : QBox 3 := coverBox383.right 0 (10023337/2560000)
noncomputable def coverBox386 : QBox 3 := coverBox385.left 2 (81/1280)
noncomputable def coverBox387 : QBox 3 := coverBox386.left 1 (-941/1024)
noncomputable def coverBox388 : QBox 3 := coverBox387.left 0 (20047273/5120000)
noncomputable def coverBox389 : QBox 3 := coverBox387.right 0 (20047273/5120000)
noncomputable def coverBox390 : QBox 3 := coverBox389.left 2 (161/2560)
noncomputable def coverBox391 : QBox 3 := coverBox390.left 1 (-1883/2048)
noncomputable def coverBox392 : QBox 3 := coverBox391.left 0 (8019029/2048000)
noncomputable def coverBox393 : QBox 3 := coverBox392.left 2 (321/5120)
noncomputable def coverBox394 : QBox 3 := coverBox393.left 1 (-3767/4096)
noncomputable def coverBox395 : QBox 3 := coverBox393.right 1 (-3767/4096)
noncomputable def coverBox396 : QBox 3 := coverBox395.left 0 (80189691/20480000)
noncomputable def coverBox397 : QBox 3 := coverBox395.right 0 (80189691/20480000)
noncomputable def coverBox398 : QBox 3 := coverBox392.right 2 (321/5120)
noncomputable def coverBox399 : QBox 3 := coverBox391.right 0 (8019029/2048000)
noncomputable def coverBox400 : QBox 3 := coverBox390.right 1 (-1883/2048)
noncomputable def coverBox401 : QBox 3 := coverBox400.left 0 (8019029/2048000)
noncomputable def coverBox402 : QBox 3 := coverBox401.left 2 (321/5120)
noncomputable def coverBox403 : QBox 3 := coverBox401.right 2 (321/5120)
noncomputable def coverBox404 : QBox 3 := coverBox403.left 1 (-3765/4096)
noncomputable def coverBox405 : QBox 3 := coverBox404.left 0 (80189691/20480000)
noncomputable def coverBox406 : QBox 3 := coverBox404.right 0 (80189691/20480000)
noncomputable def coverBox407 : QBox 3 := coverBox403.right 1 (-3765/4096)
noncomputable def coverBox408 : QBox 3 := coverBox400.right 0 (8019029/2048000)
noncomputable def coverBox409 : QBox 3 := coverBox389.right 2 (161/2560)
noncomputable def coverBox410 : QBox 3 := coverBox386.right 1 (-941/1024)
noncomputable def coverBox411 : QBox 3 := coverBox410.left 0 (20047273/5120000)
noncomputable def coverBox412 : QBox 3 := coverBox410.right 0 (20047273/5120000)
noncomputable def coverBox413 : QBox 3 := coverBox412.left 2 (161/2560)
noncomputable def coverBox414 : QBox 3 := coverBox412.right 2 (161/2560)
noncomputable def coverBox415 : QBox 3 := coverBox414.left 1 (-1881/2048)
noncomputable def coverBox416 : QBox 3 := coverBox415.left 0 (8019029/2048000)
noncomputable def coverBox417 : QBox 3 := coverBox416.left 2 (323/5120)
noncomputable def coverBox418 : QBox 3 := coverBox416.right 2 (323/5120)
noncomputable def coverBox419 : QBox 3 := coverBox418.left 1 (-3763/4096)
noncomputable def coverBox420 : QBox 3 := coverBox418.right 1 (-3763/4096)
noncomputable def coverBox421 : QBox 3 := coverBox415.right 0 (8019029/2048000)
noncomputable def coverBox422 : QBox 3 := coverBox414.right 1 (-1881/2048)
noncomputable def coverBox423 : QBox 3 := coverBox385.right 2 (81/1280)
noncomputable def coverBox424 : QBox 3 := coverBox423.left 1 (-941/1024)
noncomputable def coverBox425 : QBox 3 := coverBox423.right 1 (-941/1024)
noncomputable def coverBox426 : QBox 3 := coverBox425.left 0 (20047273/5120000)
noncomputable def coverBox427 : QBox 3 := coverBox425.right 0 (20047273/5120000)
noncomputable def coverBox428 : QBox 3 := coverBox427.left 2 (163/2560)
noncomputable def coverBox429 : QBox 3 := coverBox428.left 1 (-1881/2048)
noncomputable def coverBox430 : QBox 3 := coverBox428.right 1 (-1881/2048)
noncomputable def coverBox431 : QBox 3 := coverBox430.left 0 (8019029/2048000)
noncomputable def coverBox432 : QBox 3 := coverBox431.left 2 (65/1024)
noncomputable def coverBox433 : QBox 3 := coverBox431.right 2 (65/1024)
noncomputable def coverBox434 : QBox 3 := coverBox430.right 0 (8019029/2048000)
noncomputable def coverBox435 : QBox 3 := coverBox427.right 2 (163/2560)
noncomputable def coverBox436 : QBox 3 := coverBox380.right 2 (41/640)
noncomputable def coverBox437 : QBox 3 := coverBox377.right 1 (-235/256)
noncomputable def coverBox438 : QBox 3 := coverBox437.left 0 (5011369/1280000)
noncomputable def coverBox439 : QBox 3 := coverBox437.right 0 (5011369/1280000)
noncomputable def coverBox440 : QBox 3 := coverBox439.left 2 (41/640)
noncomputable def coverBox441 : QBox 3 := coverBox440.left 1 (-469/512)
noncomputable def coverBox442 : QBox 3 := coverBox441.left 0 (10023337/2560000)
noncomputable def coverBox443 : QBox 3 := coverBox441.right 0 (10023337/2560000)
noncomputable def coverBox444 : QBox 3 := coverBox443.left 2 (81/1280)
noncomputable def coverBox445 : QBox 3 := coverBox443.right 2 (81/1280)
noncomputable def coverBox446 : QBox 3 := coverBox445.left 1 (-939/1024)
noncomputable def coverBox447 : QBox 3 := coverBox446.left 0 (20047273/5120000)
noncomputable def coverBox448 : QBox 3 := coverBox446.right 0 (20047273/5120000)
noncomputable def coverBox449 : QBox 3 := coverBox448.left 2 (163/2560)
noncomputable def coverBox450 : QBox 3 := coverBox448.right 2 (163/2560)
noncomputable def coverBox451 : QBox 3 := coverBox450.left 1 (-1879/2048)
noncomputable def coverBox452 : QBox 3 := coverBox450.right 1 (-1879/2048)
noncomputable def coverBox453 : QBox 3 := coverBox445.right 1 (-939/1024)
noncomputable def coverBox454 : QBox 3 := coverBox440.right 1 (-469/512)
noncomputable def coverBox455 : QBox 3 := coverBox439.right 2 (41/640)
noncomputable def coverBox456 : QBox 3 := coverBox455.left 1 (-469/512)
noncomputable def coverBox457 : QBox 3 := coverBox456.left 0 (10023337/2560000)
noncomputable def coverBox458 : QBox 3 := coverBox456.right 0 (10023337/2560000)
noncomputable def coverBox459 : QBox 3 := coverBox458.left 2 (83/1280)
noncomputable def coverBox460 : QBox 3 := coverBox459.left 1 (-939/1024)
noncomputable def coverBox461 : QBox 3 := coverBox459.right 1 (-939/1024)
noncomputable def coverBox462 : QBox 3 := coverBox461.left 0 (20047273/5120000)
noncomputable def coverBox463 : QBox 3 := coverBox461.right 0 (20047273/5120000)
noncomputable def coverBox464 : QBox 3 := coverBox463.left 2 (33/512)
noncomputable def coverBox465 : QBox 3 := coverBox463.right 2 (33/512)
noncomputable def coverBox466 : QBox 3 := coverBox458.right 2 (83/1280)
noncomputable def coverBox467 : QBox 3 := coverBox455.right 1 (-469/512)
noncomputable def coverBox468 : QBox 3 := coverBox467.left 0 (10023337/2560000)
noncomputable def coverBox469 : QBox 3 := coverBox467.right 0 (10023337/2560000)
noncomputable def coverBox470 : QBox 3 := coverBox469.left 2 (83/1280)
noncomputable def coverBox471 : QBox 3 := coverBox469.right 2 (83/1280)
noncomputable def coverBox472 : QBox 3 := coverBox471.left 1 (-937/1024)
noncomputable def coverBox473 : QBox 3 := coverBox472.left 0 (20047273/5120000)
noncomputable def coverBox474 : QBox 3 := coverBox472.right 0 (20047273/5120000)
noncomputable def coverBox475 : QBox 3 := coverBox474.left 2 (167/2560)
noncomputable def coverBox476 : QBox 3 := coverBox474.right 2 (167/2560)
noncomputable def coverBox477 : QBox 3 := coverBox471.right 1 (-937/1024)
noncomputable def coverBox478 : QBox 3 := coverBox376.right 2 (21/320)
noncomputable def coverBox479 : QBox 3 := coverBox373.right 1 (-117/128)
noncomputable def coverBox480 : QBox 3 := coverBox479.left 0 (501077/128000)
noncomputable def coverBox481 : QBox 3 := coverBox479.right 0 (501077/128000)
noncomputable def coverBox482 : QBox 3 := coverBox481.left 2 (21/320)
noncomputable def coverBox483 : QBox 3 := coverBox481.right 2 (21/320)
noncomputable def coverBox484 : QBox 3 := coverBox483.left 1 (-233/256)
noncomputable def coverBox485 : QBox 3 := coverBox484.left 0 (5011369/1280000)
noncomputable def coverBox486 : QBox 3 := coverBox484.right 0 (5011369/1280000)
noncomputable def coverBox487 : QBox 3 := coverBox486.left 2 (43/640)
noncomputable def coverBox488 : QBox 3 := coverBox487.left 1 (-467/512)
noncomputable def coverBox489 : QBox 3 := coverBox488.left 0 (10023337/2560000)
noncomputable def coverBox490 : QBox 3 := coverBox488.right 0 (10023337/2560000)
noncomputable def coverBox491 : QBox 3 := coverBox490.left 2 (17/256)
noncomputable def coverBox492 : QBox 3 := coverBox490.right 2 (17/256)
noncomputable def coverBox493 : QBox 3 := coverBox492.left 1 (-935/1024)
noncomputable def coverBox494 : QBox 3 := coverBox492.right 1 (-935/1024)
noncomputable def coverBox495 : QBox 3 := coverBox487.right 1 (-467/512)
noncomputable def coverBox496 : QBox 3 := coverBox486.right 2 (43/640)
noncomputable def coverBox497 : QBox 3 := coverBox496.left 1 (-467/512)
noncomputable def coverBox498 : QBox 3 := coverBox496.right 1 (-467/512)
noncomputable def coverBox499 : QBox 3 := coverBox498.left 0 (10023337/2560000)
noncomputable def coverBox500 : QBox 3 := coverBox498.right 0 (10023337/2560000)
noncomputable def coverBox501 : QBox 3 := coverBox500.left 2 (87/1280)
noncomputable def coverBox502 : QBox 3 := coverBox500.right 2 (87/1280)
noncomputable def coverBox503 : QBox 3 := coverBox483.right 1 (-233/256)
noncomputable def coverBox504 : QBox 3 := coverBox372.right 2 (11/160)
noncomputable def coverBox505 : QBox 3 := coverBox504.left 1 (-117/128)
noncomputable def coverBox506 : QBox 3 := coverBox504.right 1 (-117/128)
noncomputable def coverBox507 : QBox 3 := coverBox506.left 0 (501077/128000)
noncomputable def coverBox508 : QBox 3 := coverBox506.right 0 (501077/128000)
noncomputable def coverBox509 : QBox 3 := coverBox508.left 2 (23/320)
noncomputable def coverBox510 : QBox 3 := coverBox509.left 1 (-233/256)
noncomputable def coverBox511 : QBox 3 := coverBox509.right 1 (-233/256)
noncomputable def coverBox512 : QBox 3 := coverBox511.left 0 (5011369/1280000)
noncomputable def coverBox513 : QBox 3 := coverBox511.right 0 (5011369/1280000)
noncomputable def coverBox514 : QBox 3 := coverBox513.left 2 (9/128)
noncomputable def coverBox515 : QBox 3 := coverBox514.left 1 (-465/512)
noncomputable def coverBox516 : QBox 3 := coverBox514.right 1 (-465/512)
noncomputable def coverBox517 : QBox 3 := coverBox513.right 2 (9/128)
noncomputable def coverBox518 : QBox 3 := coverBox508.right 2 (23/320)
noncomputable def coverBox519 : QBox 3 := coverBox119.right 1 (-29/32)
noncomputable def coverBox520 : QBox 3 := coverBox519.left 0 (625897/160000)
noncomputable def coverBox521 : QBox 3 := coverBox520.left 2 (1/16)
noncomputable def coverBox522 : QBox 3 := coverBox520.right 2 (1/16)
noncomputable def coverBox523 : QBox 3 := coverBox519.right 0 (625897/160000)
noncomputable def coverBox524 : QBox 3 := coverBox523.left 2 (1/16)
noncomputable def coverBox525 : QBox 3 := coverBox523.right 2 (1/16)
noncomputable def coverBox526 : QBox 3 := coverBox525.left 1 (-57/64)
noncomputable def coverBox527 : QBox 3 := coverBox526.left 0 (1252393/320000)
noncomputable def coverBox528 : QBox 3 := coverBox526.right 0 (1252393/320000)
noncomputable def coverBox529 : QBox 3 := coverBox528.left 2 (11/160)
noncomputable def coverBox530 : QBox 3 := coverBox528.right 2 (11/160)
noncomputable def coverBox531 : QBox 3 := coverBox530.left 1 (-115/128)
noncomputable def coverBox532 : QBox 3 := coverBox531.left 0 (501077/128000)
noncomputable def coverBox533 : QBox 3 := coverBox531.right 0 (501077/128000)
noncomputable def coverBox534 : QBox 3 := coverBox533.left 2 (23/320)
noncomputable def coverBox535 : QBox 3 := coverBox533.right 2 (23/320)
noncomputable def coverBox536 : QBox 3 := coverBox535.left 1 (-231/256)
noncomputable def coverBox537 : QBox 3 := coverBox536.left 0 (5011369/1280000)
noncomputable def coverBox538 : QBox 3 := coverBox536.right 0 (5011369/1280000)
noncomputable def coverBox539 : QBox 3 := coverBox538.left 2 (47/640)
noncomputable def coverBox540 : QBox 3 := coverBox538.right 2 (47/640)
noncomputable def coverBox541 : QBox 3 := coverBox535.right 1 (-231/256)
noncomputable def coverBox542 : QBox 3 := coverBox530.right 1 (-115/128)
noncomputable def coverBox543 : QBox 3 := coverBox525.right 1 (-57/64)
noncomputable def coverBox544 : QBox 3 := coverBox118.right 2 (3/40)
noncomputable def coverBox545 : QBox 3 := coverBox544.left 1 (-29/32)
noncomputable def coverBox546 : QBox 3 := coverBox544.right 1 (-29/32)
noncomputable def coverBox547 : QBox 3 := coverBox546.left 0 (625897/160000)
noncomputable def coverBox548 : QBox 3 := coverBox547.left 2 (7/80)
noncomputable def coverBox549 : QBox 3 := coverBox547.right 2 (7/80)
noncomputable def coverBox550 : QBox 3 := coverBox546.right 0 (625897/160000)
noncomputable def coverBox551 : QBox 3 := coverBox550.left 2 (7/80)
noncomputable def coverBox552 : QBox 3 := coverBox551.left 1 (-57/64)
noncomputable def coverBox553 : QBox 3 := coverBox552.left 0 (1252393/320000)
noncomputable def coverBox554 : QBox 3 := coverBox552.right 0 (1252393/320000)
noncomputable def coverBox555 : QBox 3 := coverBox554.left 2 (13/160)
noncomputable def coverBox556 : QBox 3 := coverBox555.left 1 (-115/128)
noncomputable def coverBox557 : QBox 3 := coverBox555.right 1 (-115/128)
noncomputable def coverBox558 : QBox 3 := coverBox557.left 0 (501077/128000)
noncomputable def coverBox559 : QBox 3 := coverBox557.right 0 (501077/128000)
noncomputable def coverBox560 : QBox 3 := coverBox559.left 2 (5/64)
noncomputable def coverBox561 : QBox 3 := coverBox559.right 2 (5/64)
noncomputable def coverBox562 : QBox 3 := coverBox561.left 1 (-229/256)
noncomputable def coverBox563 : QBox 3 := coverBox561.right 1 (-229/256)
noncomputable def coverBox564 : QBox 3 := coverBox554.right 2 (13/160)
noncomputable def coverBox565 : QBox 3 := coverBox551.right 1 (-57/64)
noncomputable def coverBox566 : QBox 3 := coverBox565.left 0 (1252393/320000)
noncomputable def coverBox567 : QBox 3 := coverBox565.right 0 (1252393/320000)
noncomputable def coverBox568 : QBox 3 := coverBox567.left 2 (13/160)
noncomputable def coverBox569 : QBox 3 := coverBox567.right 2 (13/160)
noncomputable def coverBox570 : QBox 3 := coverBox569.left 1 (-113/128)
noncomputable def coverBox571 : QBox 3 := coverBox570.left 0 (501077/128000)
noncomputable def coverBox572 : QBox 3 := coverBox570.right 0 (501077/128000)
noncomputable def coverBox573 : QBox 3 := coverBox572.left 2 (27/320)
noncomputable def coverBox574 : QBox 3 := coverBox572.right 2 (27/320)
noncomputable def coverBox575 : QBox 3 := coverBox569.right 1 (-113/128)
noncomputable def coverBox576 : QBox 3 := coverBox550.right 2 (7/80)
noncomputable def coverBox577 : QBox 3 := coverBox576.left 1 (-57/64)
noncomputable def coverBox578 : QBox 3 := coverBox576.right 1 (-57/64)
noncomputable def coverBox579 : QBox 3 := coverBox578.left 0 (1252393/320000)
noncomputable def coverBox580 : QBox 3 := coverBox578.right 0 (1252393/320000)
noncomputable def coverBox581 : QBox 3 := coverBox580.left 2 (3/32)
noncomputable def coverBox582 : QBox 3 := coverBox581.left 1 (-113/128)
noncomputable def coverBox583 : QBox 3 := coverBox581.right 1 (-113/128)
noncomputable def coverBox584 : QBox 3 := coverBox580.right 2 (3/32)
noncomputable def coverBox585 : QBox 3 := coverBox1.right 1 (-7/8)
noncomputable def coverBox586 : QBox 3 := coverBox585.left 2 (1/20)
noncomputable def coverBox587 : QBox 3 := coverBox585.right 2 (1/20)
noncomputable def coverBox588 : QBox 3 := coverBox587.left 1 (-13/16)
noncomputable def coverBox589 : QBox 3 := coverBox588.left 0 (312649/80000)
noncomputable def coverBox590 : QBox 3 := coverBox589.left 2 (3/40)
noncomputable def coverBox591 : QBox 3 := coverBox589.right 2 (3/40)
noncomputable def coverBox592 : QBox 3 := coverBox591.left 1 (-27/32)
noncomputable def coverBox593 : QBox 3 := coverBox591.right 1 (-27/32)
noncomputable def coverBox594 : QBox 3 := coverBox588.right 0 (312649/80000)
noncomputable def coverBox595 : QBox 3 := coverBox594.left 2 (3/40)
noncomputable def coverBox596 : QBox 3 := coverBox594.right 2 (3/40)
noncomputable def coverBox597 : QBox 3 := coverBox596.left 1 (-27/32)
noncomputable def coverBox598 : QBox 3 := coverBox597.left 0 (625897/160000)
noncomputable def coverBox599 : QBox 3 := coverBox598.left 2 (7/80)
noncomputable def coverBox600 : QBox 3 := coverBox598.right 2 (7/80)
noncomputable def coverBox601 : QBox 3 := coverBox597.right 0 (625897/160000)
noncomputable def coverBox602 : QBox 3 := coverBox601.left 2 (7/80)
noncomputable def coverBox603 : QBox 3 := coverBox601.right 2 (7/80)
noncomputable def coverBox604 : QBox 3 := coverBox603.left 1 (-55/64)
noncomputable def coverBox605 : QBox 3 := coverBox604.left 0 (1252393/320000)
noncomputable def coverBox606 : QBox 3 := coverBox604.right 0 (1252393/320000)
noncomputable def coverBox607 : QBox 3 := coverBox606.left 2 (3/32)
noncomputable def coverBox608 : QBox 3 := coverBox606.right 2 (3/32)
noncomputable def coverBox609 : QBox 3 := coverBox603.right 1 (-55/64)
noncomputable def coverBox610 : QBox 3 := coverBox596.right 1 (-27/32)
noncomputable def coverBox611 : QBox 3 := coverBox587.right 1 (-13/16)
noncomputable def coverBox612 : QBox 3 := coverBox0.right 1 (-3/4)

theorem cover7 : Covered stationaryTargets localBox coverBox7 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover8 : Covered stationaryTargets localBox coverBox8 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover10 : Covered stationaryTargets localBox coverBox10 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover11 : Covered stationaryTargets localBox coverBox11 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover16 : Covered stationaryTargets localBox coverBox16 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover17 : Covered stationaryTargets localBox coverBox17 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover19 : Covered stationaryTargets localBox coverBox19 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover22 : Covered stationaryTargets localBox coverBox22 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover24 : Covered stationaryTargets localBox coverBox24 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover25 : Covered stationaryTargets localBox coverBox25 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover26 : Covered stationaryTargets localBox coverBox26 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover27 : Covered stationaryTargets localBox coverBox27 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover31 : Covered stationaryTargets localBox coverBox31 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover32 : Covered stationaryTargets localBox coverBox32 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover35 : Covered stationaryTargets localBox coverBox35 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover37 : Covered stationaryTargets localBox coverBox37 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover39 : Covered stationaryTargets localBox coverBox39 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover40 : Covered stationaryTargets localBox coverBox40 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover41 : Covered stationaryTargets localBox coverBox41 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover44 : Covered stationaryTargets localBox coverBox44 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover45 : Covered stationaryTargets localBox coverBox45 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover49 : Covered stationaryTargets localBox coverBox49 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover51 : Covered stationaryTargets localBox coverBox51 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover53 : Covered stationaryTargets localBox coverBox53 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover54 : Covered stationaryTargets localBox coverBox54 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover55 : Covered stationaryTargets localBox coverBox55 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover58 : Covered stationaryTargets localBox coverBox58 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover59 : Covered stationaryTargets localBox coverBox59 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover61 : Covered stationaryTargets localBox coverBox61 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover63 : Covered stationaryTargets localBox coverBox63 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover65 : Covered stationaryTargets localBox coverBox65 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover67 : Covered stationaryTargets localBox coverBox67 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover69 : Covered stationaryTargets localBox coverBox69 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover71 : Covered stationaryTargets localBox coverBox71 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover72 : Covered stationaryTargets localBox coverBox72 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover75 : Covered stationaryTargets localBox coverBox75 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover77 : Covered stationaryTargets localBox coverBox77 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover78 : Covered stationaryTargets localBox coverBox78 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover80 : Covered stationaryTargets localBox coverBox80 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover84 : Covered stationaryTargets localBox coverBox84 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover85 : Covered stationaryTargets localBox coverBox85 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover87 : Covered stationaryTargets localBox coverBox87 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover88 : Covered stationaryTargets localBox coverBox88 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover89 : Covered stationaryTargets localBox coverBox89 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover94 : Covered stationaryTargets localBox coverBox94 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover95 : Covered stationaryTargets localBox coverBox95 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover96 : Covered stationaryTargets localBox coverBox96 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover99 : Covered stationaryTargets localBox coverBox99 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover102 : Covered stationaryTargets localBox coverBox102 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover103 : Covered stationaryTargets localBox coverBox103 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover106 : Covered stationaryTargets localBox coverBox106 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover107 : Covered stationaryTargets localBox coverBox107 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover108 : Covered stationaryTargets localBox coverBox108 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover109 : Covered stationaryTargets localBox coverBox109 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover113 : Covered stationaryTargets localBox coverBox113 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover114 : Covered stationaryTargets localBox coverBox114 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover116 : Covered stationaryTargets localBox coverBox116 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover117 : Covered stationaryTargets localBox coverBox117 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover122 : Covered stationaryTargets localBox coverBox122 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover123 : Covered stationaryTargets localBox coverBox123 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover127 : Covered stationaryTargets localBox coverBox127 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover131 : Covered stationaryTargets localBox coverBox131 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover135 : Covered stationaryTargets localBox coverBox135 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover137 : Covered stationaryTargets localBox coverBox137 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover139 : Covered stationaryTargets localBox coverBox139 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover140 : Covered stationaryTargets localBox coverBox140 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover141 : Covered stationaryTargets localBox coverBox141 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover143 : Covered stationaryTargets localBox coverBox143 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover145 : Covered stationaryTargets localBox coverBox145 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover147 : Covered stationaryTargets localBox coverBox147 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover149 : Covered stationaryTargets localBox coverBox149 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover151 : Covered stationaryTargets localBox coverBox151 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover153 : Covered stationaryTargets localBox coverBox153 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover154 : Covered stationaryTargets localBox coverBox154 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover155 : Covered stationaryTargets localBox coverBox155 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover157 : Covered stationaryTargets localBox coverBox157 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover159 : Covered stationaryTargets localBox coverBox159 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover163 : Covered stationaryTargets localBox coverBox163 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover167 : Covered stationaryTargets localBox coverBox167 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover170 : Covered stationaryTargets localBox coverBox170 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover171 : Covered stationaryTargets localBox coverBox171 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover172 : Covered stationaryTargets localBox coverBox172 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover173 : Covered stationaryTargets localBox coverBox173 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover175 : Covered stationaryTargets localBox coverBox175 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover177 : Covered stationaryTargets localBox coverBox177 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover180 : Covered stationaryTargets localBox coverBox180 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover182 : Covered stationaryTargets localBox coverBox182 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover184 : Covered stationaryTargets localBox coverBox184 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover185 : Covered stationaryTargets localBox coverBox185 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover186 : Covered stationaryTargets localBox coverBox186 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover188 : Covered stationaryTargets localBox coverBox188 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover190 : Covered stationaryTargets localBox coverBox190 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover193 : Covered stationaryTargets localBox coverBox193 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover195 : Covered stationaryTargets localBox coverBox195 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover198 : Covered stationaryTargets localBox coverBox198 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover200 : Covered stationaryTargets localBox coverBox200 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover201 : Covered stationaryTargets localBox coverBox201 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover202 : Covered stationaryTargets localBox coverBox202 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover203 : Covered stationaryTargets localBox coverBox203 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover205 : Covered stationaryTargets localBox coverBox205 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover207 : Covered stationaryTargets localBox coverBox207 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover211 : Covered stationaryTargets localBox coverBox211 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover214 : Covered stationaryTargets localBox coverBox214 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover216 : Covered stationaryTargets localBox coverBox216 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover219 : Covered stationaryTargets localBox coverBox219 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover220 : Covered stationaryTargets localBox coverBox220 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover221 : Covered stationaryTargets localBox coverBox221 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover222 : Covered stationaryTargets localBox coverBox222 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover224 : Covered stationaryTargets localBox coverBox224 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover226 : Covered stationaryTargets localBox coverBox226 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover229 : Covered stationaryTargets localBox coverBox229 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover232 : Covered stationaryTargets localBox coverBox232 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover233 : Covered stationaryTargets localBox coverBox233 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover234 : Covered stationaryTargets localBox coverBox234 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover236 : Covered stationaryTargets localBox coverBox236 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover238 : Covered stationaryTargets localBox coverBox238 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover240 : Covered stationaryTargets localBox coverBox240 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover241 : Covered stationaryTargets localBox coverBox241 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover243 : Covered stationaryTargets localBox coverBox243 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover245 : Covered stationaryTargets localBox coverBox245 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover248 : Covered stationaryTargets localBox coverBox248 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover250 : Covered stationaryTargets localBox coverBox250 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover251 : Covered stationaryTargets localBox coverBox251 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover252 : Covered stationaryTargets localBox coverBox252 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover254 : Covered stationaryTargets localBox coverBox254 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover256 : Covered stationaryTargets localBox coverBox256 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover259 : Covered stationaryTargets localBox coverBox259 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover261 : Covered stationaryTargets localBox coverBox261 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover264 : Covered stationaryTargets localBox coverBox264 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover266 : Covered stationaryTargets localBox coverBox266 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover269 : Covered stationaryTargets localBox coverBox269 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover273 : Covered stationaryTargets localBox coverBox273 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover278 : Covered stationaryTargets localBox coverBox278 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover280 : Covered stationaryTargets localBox coverBox280 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover281 : Covered stationaryTargets localBox coverBox281 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover282 : Covered stationaryTargets localBox coverBox282 :=
  covered_inside (by decide +kernel)
theorem cover283 : Covered stationaryTargets localBox coverBox283 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover285 : Covered stationaryTargets localBox coverBox285 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover290 : Covered stationaryTargets localBox coverBox290 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover291 : Covered stationaryTargets localBox coverBox291 :=
  covered_inside (by decide +kernel)
theorem cover292 : Covered stationaryTargets localBox coverBox292 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover294 : Covered stationaryTargets localBox coverBox294 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover296 : Covered stationaryTargets localBox coverBox296 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover297 : Covered stationaryTargets localBox coverBox297 :=
  covered_inside (by decide +kernel)
theorem cover298 : Covered stationaryTargets localBox coverBox298 :=
  covered_inside (by decide +kernel)
theorem cover299 : Covered stationaryTargets localBox coverBox299 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover302 : Covered stationaryTargets localBox coverBox302 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover303 : Covered stationaryTargets localBox coverBox303 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover305 : Covered stationaryTargets localBox coverBox305 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover312 : Covered stationaryTargets localBox coverBox312 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover313 : Covered stationaryTargets localBox coverBox313 :=
  covered_inside (by decide +kernel)
theorem cover315 : Covered stationaryTargets localBox coverBox315 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover316 : Covered stationaryTargets localBox coverBox316 :=
  covered_inside (by decide +kernel)
theorem cover318 : Covered stationaryTargets localBox coverBox318 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover320 : Covered stationaryTargets localBox coverBox320 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover321 : Covered stationaryTargets localBox coverBox321 :=
  covered_inside (by decide +kernel)
theorem cover322 : Covered stationaryTargets localBox coverBox322 :=
  covered_inside (by decide +kernel)
theorem cover325 : Covered stationaryTargets localBox coverBox325 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover328 : Covered stationaryTargets localBox coverBox328 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover329 : Covered stationaryTargets localBox coverBox329 :=
  covered_inside (by decide +kernel)
theorem cover330 : Covered stationaryTargets localBox coverBox330 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover331 : Covered stationaryTargets localBox coverBox331 :=
  covered_inside (by decide +kernel)
theorem cover333 : Covered stationaryTargets localBox coverBox333 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover338 : Covered stationaryTargets localBox coverBox338 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover339 : Covered stationaryTargets localBox coverBox339 :=
  covered_inside (by decide +kernel)
theorem cover341 : Covered stationaryTargets localBox coverBox341 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover342 : Covered stationaryTargets localBox coverBox342 :=
  covered_inside (by decide +kernel)
theorem cover343 : Covered stationaryTargets localBox coverBox343 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover344 : Covered stationaryTargets localBox coverBox344 :=
  covered_inside (by decide +kernel)
theorem cover346 : Covered stationaryTargets localBox coverBox346 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover348 : Covered stationaryTargets localBox coverBox348 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover351 : Covered stationaryTargets localBox coverBox351 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover353 : Covered stationaryTargets localBox coverBox353 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover357 : Covered stationaryTargets localBox coverBox357 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover360 : Covered stationaryTargets localBox coverBox360 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover361 : Covered stationaryTargets localBox coverBox361 :=
  covered_inside (by decide +kernel)
theorem cover362 : Covered stationaryTargets localBox coverBox362 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover363 : Covered stationaryTargets localBox coverBox363 :=
  covered_inside (by decide +kernel)
theorem cover364 : Covered stationaryTargets localBox coverBox364 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover365 : Covered stationaryTargets localBox coverBox365 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover366 : Covered stationaryTargets localBox coverBox366 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover367 : Covered stationaryTargets localBox coverBox367 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover369 : Covered stationaryTargets localBox coverBox369 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover371 : Covered stationaryTargets localBox coverBox371 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover375 : Covered stationaryTargets localBox coverBox375 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover379 : Covered stationaryTargets localBox coverBox379 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover382 : Covered stationaryTargets localBox coverBox382 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover384 : Covered stationaryTargets localBox coverBox384 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover388 : Covered stationaryTargets localBox coverBox388 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover394 : Covered stationaryTargets localBox coverBox394 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover396 : Covered stationaryTargets localBox coverBox396 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover397 : Covered stationaryTargets localBox coverBox397 :=
  covered_inside (by decide +kernel)
theorem cover398 : Covered stationaryTargets localBox coverBox398 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover399 : Covered stationaryTargets localBox coverBox399 :=
  covered_inside (by decide +kernel)
theorem cover402 : Covered stationaryTargets localBox coverBox402 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover405 : Covered stationaryTargets localBox coverBox405 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover406 : Covered stationaryTargets localBox coverBox406 :=
  covered_inside (by decide +kernel)
theorem cover407 : Covered stationaryTargets localBox coverBox407 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover408 : Covered stationaryTargets localBox coverBox408 :=
  covered_inside (by decide +kernel)
theorem cover409 : Covered stationaryTargets localBox coverBox409 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover411 : Covered stationaryTargets localBox coverBox411 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover413 : Covered stationaryTargets localBox coverBox413 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover417 : Covered stationaryTargets localBox coverBox417 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover419 : Covered stationaryTargets localBox coverBox419 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover420 : Covered stationaryTargets localBox coverBox420 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover421 : Covered stationaryTargets localBox coverBox421 :=
  covered_inside (by decide +kernel)
theorem cover422 : Covered stationaryTargets localBox coverBox422 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover424 : Covered stationaryTargets localBox coverBox424 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover426 : Covered stationaryTargets localBox coverBox426 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover429 : Covered stationaryTargets localBox coverBox429 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover432 : Covered stationaryTargets localBox coverBox432 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover433 : Covered stationaryTargets localBox coverBox433 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover434 : Covered stationaryTargets localBox coverBox434 :=
  covered_inside (by decide +kernel)
theorem cover435 : Covered stationaryTargets localBox coverBox435 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover436 : Covered stationaryTargets localBox coverBox436 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover438 : Covered stationaryTargets localBox coverBox438 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover442 : Covered stationaryTargets localBox coverBox442 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover444 : Covered stationaryTargets localBox coverBox444 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover447 : Covered stationaryTargets localBox coverBox447 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover449 : Covered stationaryTargets localBox coverBox449 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover451 : Covered stationaryTargets localBox coverBox451 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover452 : Covered stationaryTargets localBox coverBox452 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover453 : Covered stationaryTargets localBox coverBox453 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover454 : Covered stationaryTargets localBox coverBox454 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover457 : Covered stationaryTargets localBox coverBox457 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover460 : Covered stationaryTargets localBox coverBox460 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover462 : Covered stationaryTargets localBox coverBox462 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover464 : Covered stationaryTargets localBox coverBox464 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover465 : Covered stationaryTargets localBox coverBox465 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover466 : Covered stationaryTargets localBox coverBox466 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover468 : Covered stationaryTargets localBox coverBox468 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover470 : Covered stationaryTargets localBox coverBox470 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover473 : Covered stationaryTargets localBox coverBox473 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover475 : Covered stationaryTargets localBox coverBox475 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover476 : Covered stationaryTargets localBox coverBox476 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover477 : Covered stationaryTargets localBox coverBox477 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover478 : Covered stationaryTargets localBox coverBox478 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover480 : Covered stationaryTargets localBox coverBox480 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover482 : Covered stationaryTargets localBox coverBox482 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover485 : Covered stationaryTargets localBox coverBox485 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover489 : Covered stationaryTargets localBox coverBox489 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover491 : Covered stationaryTargets localBox coverBox491 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover493 : Covered stationaryTargets localBox coverBox493 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover494 : Covered stationaryTargets localBox coverBox494 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover495 : Covered stationaryTargets localBox coverBox495 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover497 : Covered stationaryTargets localBox coverBox497 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover499 : Covered stationaryTargets localBox coverBox499 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover501 : Covered stationaryTargets localBox coverBox501 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover502 : Covered stationaryTargets localBox coverBox502 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover503 : Covered stationaryTargets localBox coverBox503 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover505 : Covered stationaryTargets localBox coverBox505 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover507 : Covered stationaryTargets localBox coverBox507 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover510 : Covered stationaryTargets localBox coverBox510 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover512 : Covered stationaryTargets localBox coverBox512 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover515 : Covered stationaryTargets localBox coverBox515 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover516 : Covered stationaryTargets localBox coverBox516 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover517 : Covered stationaryTargets localBox coverBox517 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover518 : Covered stationaryTargets localBox coverBox518 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover521 : Covered stationaryTargets localBox coverBox521 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover522 : Covered stationaryTargets localBox coverBox522 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover524 : Covered stationaryTargets localBox coverBox524 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover527 : Covered stationaryTargets localBox coverBox527 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover529 : Covered stationaryTargets localBox coverBox529 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover532 : Covered stationaryTargets localBox coverBox532 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover534 : Covered stationaryTargets localBox coverBox534 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover537 : Covered stationaryTargets localBox coverBox537 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover539 : Covered stationaryTargets localBox coverBox539 :=
  covered_meanValue (p := 40) 1 (coverPartial 1) (coverPartial_eval 1)
    (regular_of_inside (by decide +kernel) (coverRegular 1)) (by decide +kernel)
theorem cover540 : Covered stationaryTargets localBox coverBox540 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover541 : Covered stationaryTargets localBox coverBox541 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover542 : Covered stationaryTargets localBox coverBox542 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover543 : Covered stationaryTargets localBox coverBox543 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover545 : Covered stationaryTargets localBox coverBox545 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover548 : Covered stationaryTargets localBox coverBox548 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover549 : Covered stationaryTargets localBox coverBox549 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover553 : Covered stationaryTargets localBox coverBox553 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover556 : Covered stationaryTargets localBox coverBox556 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover558 : Covered stationaryTargets localBox coverBox558 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover560 : Covered stationaryTargets localBox coverBox560 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover562 : Covered stationaryTargets localBox coverBox562 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover563 : Covered stationaryTargets localBox coverBox563 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover564 : Covered stationaryTargets localBox coverBox564 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover566 : Covered stationaryTargets localBox coverBox566 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover568 : Covered stationaryTargets localBox coverBox568 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover571 : Covered stationaryTargets localBox coverBox571 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover573 : Covered stationaryTargets localBox coverBox573 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover574 : Covered stationaryTargets localBox coverBox574 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover575 : Covered stationaryTargets localBox coverBox575 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover577 : Covered stationaryTargets localBox coverBox577 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover579 : Covered stationaryTargets localBox coverBox579 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover582 : Covered stationaryTargets localBox coverBox582 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover583 : Covered stationaryTargets localBox coverBox583 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover584 : Covered stationaryTargets localBox coverBox584 :=
  covered_meanValue (p := 40) 2 (coverPartial 2) (coverPartial_eval 2)
    (regular_of_inside (by decide +kernel) (coverRegular 2)) (by decide +kernel)
theorem cover586 : Covered stationaryTargets localBox coverBox586 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover590 : Covered stationaryTargets localBox coverBox590 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover592 : Covered stationaryTargets localBox coverBox592 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover593 : Covered stationaryTargets localBox coverBox593 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover595 : Covered stationaryTargets localBox coverBox595 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover599 : Covered stationaryTargets localBox coverBox599 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover600 : Covered stationaryTargets localBox coverBox600 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover602 : Covered stationaryTargets localBox coverBox602 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover605 : Covered stationaryTargets localBox coverBox605 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover607 : Covered stationaryTargets localBox coverBox607 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover608 : Covered stationaryTargets localBox coverBox608 :=
  covered_meanValue (p := 40) 0 (coverPartial 0) (coverPartial_eval 0)
    (regular_of_inside (by decide +kernel) (coverRegular 0)) (by decide +kernel)
theorem cover609 : Covered stationaryTargets localBox coverBox609 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover610 : Covered stationaryTargets localBox coverBox610 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover611 : Covered stationaryTargets localBox coverBox611 :=
  covered_exclude (p := 40) 1 (by decide +kernel)
theorem cover612 : Covered stationaryTargets localBox coverBox612 :=
  covered_exclude (p := 40) 1 (by decide +kernel)

theorem cover606 : Covered stationaryTargets localBox coverBox606 :=
  covered_split coverBox606 2 (3/32) cover607 cover608
theorem cover604 : Covered stationaryTargets localBox coverBox604 :=
  covered_split coverBox604 0 (1252393/320000) cover605 cover606
theorem cover603 : Covered stationaryTargets localBox coverBox603 :=
  covered_split coverBox603 1 (-55/64) cover604 cover609
theorem cover601 : Covered stationaryTargets localBox coverBox601 :=
  covered_split coverBox601 2 (7/80) cover602 cover603
theorem cover598 : Covered stationaryTargets localBox coverBox598 :=
  covered_split coverBox598 2 (7/80) cover599 cover600
theorem cover597 : Covered stationaryTargets localBox coverBox597 :=
  covered_split coverBox597 0 (625897/160000) cover598 cover601
theorem cover596 : Covered stationaryTargets localBox coverBox596 :=
  covered_split coverBox596 1 (-27/32) cover597 cover610
theorem cover594 : Covered stationaryTargets localBox coverBox594 :=
  covered_split coverBox594 2 (3/40) cover595 cover596
theorem cover591 : Covered stationaryTargets localBox coverBox591 :=
  covered_split coverBox591 1 (-27/32) cover592 cover593
theorem cover589 : Covered stationaryTargets localBox coverBox589 :=
  covered_split coverBox589 2 (3/40) cover590 cover591
theorem cover588 : Covered stationaryTargets localBox coverBox588 :=
  covered_split coverBox588 0 (312649/80000) cover589 cover594
theorem cover587 : Covered stationaryTargets localBox coverBox587 :=
  covered_split coverBox587 1 (-13/16) cover588 cover611
theorem cover585 : Covered stationaryTargets localBox coverBox585 :=
  covered_split coverBox585 2 (1/20) cover586 cover587
theorem cover581 : Covered stationaryTargets localBox coverBox581 :=
  covered_split coverBox581 1 (-113/128) cover582 cover583
theorem cover580 : Covered stationaryTargets localBox coverBox580 :=
  covered_split coverBox580 2 (3/32) cover581 cover584
theorem cover578 : Covered stationaryTargets localBox coverBox578 :=
  covered_split coverBox578 0 (1252393/320000) cover579 cover580
theorem cover576 : Covered stationaryTargets localBox coverBox576 :=
  covered_split coverBox576 1 (-57/64) cover577 cover578
theorem cover572 : Covered stationaryTargets localBox coverBox572 :=
  covered_split coverBox572 2 (27/320) cover573 cover574
theorem cover570 : Covered stationaryTargets localBox coverBox570 :=
  covered_split coverBox570 0 (501077/128000) cover571 cover572
theorem cover569 : Covered stationaryTargets localBox coverBox569 :=
  covered_split coverBox569 1 (-113/128) cover570 cover575
theorem cover567 : Covered stationaryTargets localBox coverBox567 :=
  covered_split coverBox567 2 (13/160) cover568 cover569
theorem cover565 : Covered stationaryTargets localBox coverBox565 :=
  covered_split coverBox565 0 (1252393/320000) cover566 cover567
theorem cover561 : Covered stationaryTargets localBox coverBox561 :=
  covered_split coverBox561 1 (-229/256) cover562 cover563
theorem cover559 : Covered stationaryTargets localBox coverBox559 :=
  covered_split coverBox559 2 (5/64) cover560 cover561
theorem cover557 : Covered stationaryTargets localBox coverBox557 :=
  covered_split coverBox557 0 (501077/128000) cover558 cover559
theorem cover555 : Covered stationaryTargets localBox coverBox555 :=
  covered_split coverBox555 1 (-115/128) cover556 cover557
theorem cover554 : Covered stationaryTargets localBox coverBox554 :=
  covered_split coverBox554 2 (13/160) cover555 cover564
theorem cover552 : Covered stationaryTargets localBox coverBox552 :=
  covered_split coverBox552 0 (1252393/320000) cover553 cover554
theorem cover551 : Covered stationaryTargets localBox coverBox551 :=
  covered_split coverBox551 1 (-57/64) cover552 cover565
theorem cover550 : Covered stationaryTargets localBox coverBox550 :=
  covered_split coverBox550 2 (7/80) cover551 cover576
theorem cover547 : Covered stationaryTargets localBox coverBox547 :=
  covered_split coverBox547 2 (7/80) cover548 cover549
theorem cover546 : Covered stationaryTargets localBox coverBox546 :=
  covered_split coverBox546 0 (625897/160000) cover547 cover550
theorem cover544 : Covered stationaryTargets localBox coverBox544 :=
  covered_split coverBox544 1 (-29/32) cover545 cover546
theorem cover538 : Covered stationaryTargets localBox coverBox538 :=
  covered_split coverBox538 2 (47/640) cover539 cover540
theorem cover536 : Covered stationaryTargets localBox coverBox536 :=
  covered_split coverBox536 0 (5011369/1280000) cover537 cover538
theorem cover535 : Covered stationaryTargets localBox coverBox535 :=
  covered_split coverBox535 1 (-231/256) cover536 cover541
theorem cover533 : Covered stationaryTargets localBox coverBox533 :=
  covered_split coverBox533 2 (23/320) cover534 cover535
theorem cover531 : Covered stationaryTargets localBox coverBox531 :=
  covered_split coverBox531 0 (501077/128000) cover532 cover533
theorem cover530 : Covered stationaryTargets localBox coverBox530 :=
  covered_split coverBox530 1 (-115/128) cover531 cover542
theorem cover528 : Covered stationaryTargets localBox coverBox528 :=
  covered_split coverBox528 2 (11/160) cover529 cover530
theorem cover526 : Covered stationaryTargets localBox coverBox526 :=
  covered_split coverBox526 0 (1252393/320000) cover527 cover528
theorem cover525 : Covered stationaryTargets localBox coverBox525 :=
  covered_split coverBox525 1 (-57/64) cover526 cover543
theorem cover523 : Covered stationaryTargets localBox coverBox523 :=
  covered_split coverBox523 2 (1/16) cover524 cover525
theorem cover520 : Covered stationaryTargets localBox coverBox520 :=
  covered_split coverBox520 2 (1/16) cover521 cover522
theorem cover519 : Covered stationaryTargets localBox coverBox519 :=
  covered_split coverBox519 0 (625897/160000) cover520 cover523
theorem cover514 : Covered stationaryTargets localBox coverBox514 :=
  covered_split coverBox514 1 (-465/512) cover515 cover516
theorem cover513 : Covered stationaryTargets localBox coverBox513 :=
  covered_split coverBox513 2 (9/128) cover514 cover517
theorem cover511 : Covered stationaryTargets localBox coverBox511 :=
  covered_split coverBox511 0 (5011369/1280000) cover512 cover513
theorem cover509 : Covered stationaryTargets localBox coverBox509 :=
  covered_split coverBox509 1 (-233/256) cover510 cover511
theorem cover508 : Covered stationaryTargets localBox coverBox508 :=
  covered_split coverBox508 2 (23/320) cover509 cover518
theorem cover506 : Covered stationaryTargets localBox coverBox506 :=
  covered_split coverBox506 0 (501077/128000) cover507 cover508
theorem cover504 : Covered stationaryTargets localBox coverBox504 :=
  covered_split coverBox504 1 (-117/128) cover505 cover506
theorem cover500 : Covered stationaryTargets localBox coverBox500 :=
  covered_split coverBox500 2 (87/1280) cover501 cover502
theorem cover498 : Covered stationaryTargets localBox coverBox498 :=
  covered_split coverBox498 0 (10023337/2560000) cover499 cover500
theorem cover496 : Covered stationaryTargets localBox coverBox496 :=
  covered_split coverBox496 1 (-467/512) cover497 cover498
theorem cover492 : Covered stationaryTargets localBox coverBox492 :=
  covered_split coverBox492 1 (-935/1024) cover493 cover494
theorem cover490 : Covered stationaryTargets localBox coverBox490 :=
  covered_split coverBox490 2 (17/256) cover491 cover492
theorem cover488 : Covered stationaryTargets localBox coverBox488 :=
  covered_split coverBox488 0 (10023337/2560000) cover489 cover490
theorem cover487 : Covered stationaryTargets localBox coverBox487 :=
  covered_split coverBox487 1 (-467/512) cover488 cover495
theorem cover486 : Covered stationaryTargets localBox coverBox486 :=
  covered_split coverBox486 2 (43/640) cover487 cover496
theorem cover484 : Covered stationaryTargets localBox coverBox484 :=
  covered_split coverBox484 0 (5011369/1280000) cover485 cover486
theorem cover483 : Covered stationaryTargets localBox coverBox483 :=
  covered_split coverBox483 1 (-233/256) cover484 cover503
theorem cover481 : Covered stationaryTargets localBox coverBox481 :=
  covered_split coverBox481 2 (21/320) cover482 cover483
theorem cover479 : Covered stationaryTargets localBox coverBox479 :=
  covered_split coverBox479 0 (501077/128000) cover480 cover481
theorem cover474 : Covered stationaryTargets localBox coverBox474 :=
  covered_split coverBox474 2 (167/2560) cover475 cover476
theorem cover472 : Covered stationaryTargets localBox coverBox472 :=
  covered_split coverBox472 0 (20047273/5120000) cover473 cover474
theorem cover471 : Covered stationaryTargets localBox coverBox471 :=
  covered_split coverBox471 1 (-937/1024) cover472 cover477
theorem cover469 : Covered stationaryTargets localBox coverBox469 :=
  covered_split coverBox469 2 (83/1280) cover470 cover471
theorem cover467 : Covered stationaryTargets localBox coverBox467 :=
  covered_split coverBox467 0 (10023337/2560000) cover468 cover469
theorem cover463 : Covered stationaryTargets localBox coverBox463 :=
  covered_split coverBox463 2 (33/512) cover464 cover465
theorem cover461 : Covered stationaryTargets localBox coverBox461 :=
  covered_split coverBox461 0 (20047273/5120000) cover462 cover463
theorem cover459 : Covered stationaryTargets localBox coverBox459 :=
  covered_split coverBox459 1 (-939/1024) cover460 cover461
theorem cover458 : Covered stationaryTargets localBox coverBox458 :=
  covered_split coverBox458 2 (83/1280) cover459 cover466
theorem cover456 : Covered stationaryTargets localBox coverBox456 :=
  covered_split coverBox456 0 (10023337/2560000) cover457 cover458
theorem cover455 : Covered stationaryTargets localBox coverBox455 :=
  covered_split coverBox455 1 (-469/512) cover456 cover467
theorem cover450 : Covered stationaryTargets localBox coverBox450 :=
  covered_split coverBox450 1 (-1879/2048) cover451 cover452
theorem cover448 : Covered stationaryTargets localBox coverBox448 :=
  covered_split coverBox448 2 (163/2560) cover449 cover450
theorem cover446 : Covered stationaryTargets localBox coverBox446 :=
  covered_split coverBox446 0 (20047273/5120000) cover447 cover448
theorem cover445 : Covered stationaryTargets localBox coverBox445 :=
  covered_split coverBox445 1 (-939/1024) cover446 cover453
theorem cover443 : Covered stationaryTargets localBox coverBox443 :=
  covered_split coverBox443 2 (81/1280) cover444 cover445
theorem cover441 : Covered stationaryTargets localBox coverBox441 :=
  covered_split coverBox441 0 (10023337/2560000) cover442 cover443
theorem cover440 : Covered stationaryTargets localBox coverBox440 :=
  covered_split coverBox440 1 (-469/512) cover441 cover454
theorem cover439 : Covered stationaryTargets localBox coverBox439 :=
  covered_split coverBox439 2 (41/640) cover440 cover455
theorem cover437 : Covered stationaryTargets localBox coverBox437 :=
  covered_split coverBox437 0 (5011369/1280000) cover438 cover439
theorem cover431 : Covered stationaryTargets localBox coverBox431 :=
  covered_split coverBox431 2 (65/1024) cover432 cover433
theorem cover430 : Covered stationaryTargets localBox coverBox430 :=
  covered_split coverBox430 0 (8019029/2048000) cover431 cover434
theorem cover428 : Covered stationaryTargets localBox coverBox428 :=
  covered_split coverBox428 1 (-1881/2048) cover429 cover430
theorem cover427 : Covered stationaryTargets localBox coverBox427 :=
  covered_split coverBox427 2 (163/2560) cover428 cover435
theorem cover425 : Covered stationaryTargets localBox coverBox425 :=
  covered_split coverBox425 0 (20047273/5120000) cover426 cover427
theorem cover423 : Covered stationaryTargets localBox coverBox423 :=
  covered_split coverBox423 1 (-941/1024) cover424 cover425
theorem cover418 : Covered stationaryTargets localBox coverBox418 :=
  covered_split coverBox418 1 (-3763/4096) cover419 cover420
theorem cover416 : Covered stationaryTargets localBox coverBox416 :=
  covered_split coverBox416 2 (323/5120) cover417 cover418
theorem cover415 : Covered stationaryTargets localBox coverBox415 :=
  covered_split coverBox415 0 (8019029/2048000) cover416 cover421
theorem cover414 : Covered stationaryTargets localBox coverBox414 :=
  covered_split coverBox414 1 (-1881/2048) cover415 cover422
theorem cover412 : Covered stationaryTargets localBox coverBox412 :=
  covered_split coverBox412 2 (161/2560) cover413 cover414
theorem cover410 : Covered stationaryTargets localBox coverBox410 :=
  covered_split coverBox410 0 (20047273/5120000) cover411 cover412
theorem cover404 : Covered stationaryTargets localBox coverBox404 :=
  covered_split coverBox404 0 (80189691/20480000) cover405 cover406
theorem cover403 : Covered stationaryTargets localBox coverBox403 :=
  covered_split coverBox403 1 (-3765/4096) cover404 cover407
theorem cover401 : Covered stationaryTargets localBox coverBox401 :=
  covered_split coverBox401 2 (321/5120) cover402 cover403
theorem cover400 : Covered stationaryTargets localBox coverBox400 :=
  covered_split coverBox400 0 (8019029/2048000) cover401 cover408
theorem cover395 : Covered stationaryTargets localBox coverBox395 :=
  covered_split coverBox395 0 (80189691/20480000) cover396 cover397
theorem cover393 : Covered stationaryTargets localBox coverBox393 :=
  covered_split coverBox393 1 (-3767/4096) cover394 cover395
theorem cover392 : Covered stationaryTargets localBox coverBox392 :=
  covered_split coverBox392 2 (321/5120) cover393 cover398
theorem cover391 : Covered stationaryTargets localBox coverBox391 :=
  covered_split coverBox391 0 (8019029/2048000) cover392 cover399
theorem cover390 : Covered stationaryTargets localBox coverBox390 :=
  covered_split coverBox390 1 (-1883/2048) cover391 cover400
theorem cover389 : Covered stationaryTargets localBox coverBox389 :=
  covered_split coverBox389 2 (161/2560) cover390 cover409
theorem cover387 : Covered stationaryTargets localBox coverBox387 :=
  covered_split coverBox387 0 (20047273/5120000) cover388 cover389
theorem cover386 : Covered stationaryTargets localBox coverBox386 :=
  covered_split coverBox386 1 (-941/1024) cover387 cover410
theorem cover385 : Covered stationaryTargets localBox coverBox385 :=
  covered_split coverBox385 2 (81/1280) cover386 cover423
theorem cover383 : Covered stationaryTargets localBox coverBox383 :=
  covered_split coverBox383 0 (10023337/2560000) cover384 cover385
theorem cover381 : Covered stationaryTargets localBox coverBox381 :=
  covered_split coverBox381 1 (-471/512) cover382 cover383
theorem cover380 : Covered stationaryTargets localBox coverBox380 :=
  covered_split coverBox380 2 (41/640) cover381 cover436
theorem cover378 : Covered stationaryTargets localBox coverBox378 :=
  covered_split coverBox378 0 (5011369/1280000) cover379 cover380
theorem cover377 : Covered stationaryTargets localBox coverBox377 :=
  covered_split coverBox377 1 (-235/256) cover378 cover437
theorem cover376 : Covered stationaryTargets localBox coverBox376 :=
  covered_split coverBox376 2 (21/320) cover377 cover478
theorem cover374 : Covered stationaryTargets localBox coverBox374 :=
  covered_split coverBox374 0 (501077/128000) cover375 cover376
theorem cover373 : Covered stationaryTargets localBox coverBox373 :=
  covered_split coverBox373 1 (-117/128) cover374 cover479
theorem cover372 : Covered stationaryTargets localBox coverBox372 :=
  covered_split coverBox372 2 (11/160) cover373 cover504
theorem cover370 : Covered stationaryTargets localBox coverBox370 :=
  covered_split coverBox370 0 (1252393/320000) cover371 cover372
theorem cover368 : Covered stationaryTargets localBox coverBox368 :=
  covered_split coverBox368 1 (-59/64) cover369 cover370
theorem cover359 : Covered stationaryTargets localBox coverBox359 :=
  covered_split coverBox359 0 (80189691/20480000) cover360 cover361
theorem cover358 : Covered stationaryTargets localBox coverBox358 :=
  covered_split coverBox358 1 (-3767/4096) cover359 cover362
theorem cover356 : Covered stationaryTargets localBox coverBox356 :=
  covered_split coverBox356 2 (319/5120) cover357 cover358
theorem cover355 : Covered stationaryTargets localBox coverBox355 :=
  covered_split coverBox355 0 (8019029/2048000) cover356 cover363
theorem cover354 : Covered stationaryTargets localBox coverBox354 :=
  covered_split coverBox354 1 (-1883/2048) cover355 cover364
theorem cover352 : Covered stationaryTargets localBox coverBox352 :=
  covered_split coverBox352 2 (159/2560) cover353 cover354
theorem cover350 : Covered stationaryTargets localBox coverBox350 :=
  covered_split coverBox350 0 (20047273/5120000) cover351 cover352
theorem cover349 : Covered stationaryTargets localBox coverBox349 :=
  covered_split coverBox349 1 (-941/1024) cover350 cover365
theorem cover347 : Covered stationaryTargets localBox coverBox347 :=
  covered_split coverBox347 2 (79/1280) cover348 cover349
theorem cover345 : Covered stationaryTargets localBox coverBox345 :=
  covered_split coverBox345 0 (10023337/2560000) cover346 cover347
theorem cover340 : Covered stationaryTargets localBox coverBox340 :=
  covered_split coverBox340 0 (80189691/20480000) cover341 cover342
theorem cover337 : Covered stationaryTargets localBox coverBox337 :=
  covered_split coverBox337 0 (80189691/20480000) cover338 cover339
theorem cover336 : Covered stationaryTargets localBox coverBox336 :=
  covered_split coverBox336 1 (-3769/4096) cover337 cover340
theorem cover335 : Covered stationaryTargets localBox coverBox335 :=
  covered_split coverBox335 2 (319/5120) cover336 cover343
theorem cover334 : Covered stationaryTargets localBox coverBox334 :=
  covered_split coverBox334 0 (8019029/2048000) cover335 cover344
theorem cover332 : Covered stationaryTargets localBox coverBox332 :=
  covered_split coverBox332 1 (-1885/2048) cover333 cover334
theorem cover327 : Covered stationaryTargets localBox coverBox327 :=
  covered_split coverBox327 0 (80189691/20480000) cover328 cover329
theorem cover326 : Covered stationaryTargets localBox coverBox326 :=
  covered_split coverBox326 1 (-3769/4096) cover327 cover330
theorem cover324 : Covered stationaryTargets localBox coverBox324 :=
  covered_split coverBox324 2 (317/5120) cover325 cover326
theorem cover323 : Covered stationaryTargets localBox coverBox323 :=
  covered_split coverBox323 0 (8019029/2048000) cover324 cover331
theorem cover319 : Covered stationaryTargets localBox coverBox319 :=
  covered_split coverBox319 0 (80189691/20480000) cover320 cover321
theorem cover317 : Covered stationaryTargets localBox coverBox317 :=
  covered_split coverBox317 1 (-3771/4096) cover318 cover319
theorem cover314 : Covered stationaryTargets localBox coverBox314 :=
  covered_split coverBox314 0 (80189691/20480000) cover315 cover316
theorem cover311 : Covered stationaryTargets localBox coverBox311 :=
  covered_split coverBox311 0 (80189691/20480000) cover312 cover313
theorem cover310 : Covered stationaryTargets localBox coverBox310 :=
  covered_split coverBox310 1 (-3771/4096) cover311 cover314
theorem cover309 : Covered stationaryTargets localBox coverBox309 :=
  covered_split coverBox309 2 (317/5120) cover310 cover317
theorem cover308 : Covered stationaryTargets localBox coverBox308 :=
  covered_split coverBox308 0 (8019029/2048000) cover309 cover322
theorem cover307 : Covered stationaryTargets localBox coverBox307 :=
  covered_split coverBox307 1 (-1885/2048) cover308 cover323
theorem cover306 : Covered stationaryTargets localBox coverBox306 :=
  covered_split coverBox306 2 (159/2560) cover307 cover332
theorem cover304 : Covered stationaryTargets localBox coverBox304 :=
  covered_split coverBox304 0 (20047273/5120000) cover305 cover306
theorem cover301 : Covered stationaryTargets localBox coverBox301 :=
  covered_split coverBox301 0 (20047273/5120000) cover302 cover303
theorem cover300 : Covered stationaryTargets localBox coverBox300 :=
  covered_split coverBox300 1 (-943/1024) cover301 cover304
theorem cover295 : Covered stationaryTargets localBox coverBox295 :=
  covered_split coverBox295 0 (80189691/20480000) cover296 cover297
theorem cover293 : Covered stationaryTargets localBox coverBox293 :=
  covered_split coverBox293 1 (-3773/4096) cover294 cover295
theorem cover289 : Covered stationaryTargets localBox coverBox289 :=
  covered_split coverBox289 0 (80189691/20480000) cover290 cover291
theorem cover288 : Covered stationaryTargets localBox coverBox288 :=
  covered_split coverBox288 1 (-3773/4096) cover289 cover292
theorem cover287 : Covered stationaryTargets localBox coverBox287 :=
  covered_split coverBox287 2 (63/1024) cover288 cover293
theorem cover286 : Covered stationaryTargets localBox coverBox286 :=
  covered_split coverBox286 0 (8019029/2048000) cover287 cover298
theorem cover284 : Covered stationaryTargets localBox coverBox284 :=
  covered_split coverBox284 1 (-1887/2048) cover285 cover286
theorem cover279 : Covered stationaryTargets localBox coverBox279 :=
  covered_split coverBox279 1 (-3775/4096) cover280 cover281
theorem cover277 : Covered stationaryTargets localBox coverBox277 :=
  covered_split coverBox277 2 (313/5120) cover278 cover279
theorem cover276 : Covered stationaryTargets localBox coverBox276 :=
  covered_split coverBox276 0 (8019029/2048000) cover277 cover282
theorem cover275 : Covered stationaryTargets localBox coverBox275 :=
  covered_split coverBox275 1 (-1887/2048) cover276 cover283
theorem cover274 : Covered stationaryTargets localBox coverBox274 :=
  covered_split coverBox274 2 (157/2560) cover275 cover284
theorem cover272 : Covered stationaryTargets localBox coverBox272 :=
  covered_split coverBox272 0 (20047273/5120000) cover273 cover274
theorem cover271 : Covered stationaryTargets localBox coverBox271 :=
  covered_split coverBox271 1 (-943/1024) cover272 cover299
theorem cover270 : Covered stationaryTargets localBox coverBox270 :=
  covered_split coverBox270 2 (79/1280) cover271 cover300
theorem cover268 : Covered stationaryTargets localBox coverBox268 :=
  covered_split coverBox268 0 (10023337/2560000) cover269 cover270
theorem cover267 : Covered stationaryTargets localBox coverBox267 :=
  covered_split coverBox267 1 (-471/512) cover268 cover345
theorem cover265 : Covered stationaryTargets localBox coverBox265 :=
  covered_split coverBox265 2 (39/640) cover266 cover267
theorem cover263 : Covered stationaryTargets localBox coverBox263 :=
  covered_split coverBox263 0 (5011369/1280000) cover264 cover265
theorem cover262 : Covered stationaryTargets localBox coverBox262 :=
  covered_split coverBox262 1 (-235/256) cover263 cover366
theorem cover260 : Covered stationaryTargets localBox coverBox260 :=
  covered_split coverBox260 2 (19/320) cover261 cover262
theorem cover258 : Covered stationaryTargets localBox coverBox258 :=
  covered_split coverBox258 0 (501077/128000) cover259 cover260
theorem cover257 : Covered stationaryTargets localBox coverBox257 :=
  covered_split coverBox257 1 (-117/128) cover258 cover367
theorem cover255 : Covered stationaryTargets localBox coverBox255 :=
  covered_split coverBox255 2 (9/160) cover256 cover257
theorem cover253 : Covered stationaryTargets localBox coverBox253 :=
  covered_split coverBox253 0 (1252393/320000) cover254 cover255
theorem cover249 : Covered stationaryTargets localBox coverBox249 :=
  covered_split coverBox249 0 (20047273/5120000) cover250 cover251
theorem cover247 : Covered stationaryTargets localBox coverBox247 :=
  covered_split coverBox247 1 (-945/1024) cover248 cover249
theorem cover246 : Covered stationaryTargets localBox coverBox246 :=
  covered_split coverBox246 2 (79/1280) cover247 cover252
theorem cover244 : Covered stationaryTargets localBox coverBox244 :=
  covered_split coverBox244 0 (10023337/2560000) cover245 cover246
theorem cover242 : Covered stationaryTargets localBox coverBox242 :=
  covered_split coverBox242 1 (-473/512) cover243 cover244
theorem cover239 : Covered stationaryTargets localBox coverBox239 :=
  covered_split coverBox239 1 (-1889/2048) cover240 cover241
theorem cover237 : Covered stationaryTargets localBox coverBox237 :=
  covered_split coverBox237 2 (31/512) cover238 cover239
theorem cover235 : Covered stationaryTargets localBox coverBox235 :=
  covered_split coverBox235 0 (20047273/5120000) cover236 cover237
theorem cover231 : Covered stationaryTargets localBox coverBox231 :=
  covered_split coverBox231 1 (-1891/2048) cover232 cover233
theorem cover230 : Covered stationaryTargets localBox coverBox230 :=
  covered_split coverBox230 2 (31/512) cover231 cover234
theorem cover228 : Covered stationaryTargets localBox coverBox228 :=
  covered_split coverBox228 0 (20047273/5120000) cover229 cover230
theorem cover227 : Covered stationaryTargets localBox coverBox227 :=
  covered_split coverBox227 1 (-945/1024) cover228 cover235
theorem cover225 : Covered stationaryTargets localBox coverBox225 :=
  covered_split coverBox225 2 (77/1280) cover226 cover227
theorem cover223 : Covered stationaryTargets localBox coverBox223 :=
  covered_split coverBox223 0 (10023337/2560000) cover224 cover225
theorem cover218 : Covered stationaryTargets localBox coverBox218 :=
  covered_split coverBox218 1 (-1893/2048) cover219 cover220
theorem cover217 : Covered stationaryTargets localBox coverBox217 :=
  covered_split coverBox217 2 (153/2560) cover218 cover221
theorem cover215 : Covered stationaryTargets localBox coverBox215 :=
  covered_split coverBox215 0 (20047273/5120000) cover216 cover217
theorem cover213 : Covered stationaryTargets localBox coverBox213 :=
  covered_split coverBox213 1 (-947/1024) cover214 cover215
theorem cover212 : Covered stationaryTargets localBox coverBox212 :=
  covered_split coverBox212 2 (77/1280) cover213 cover222
theorem cover210 : Covered stationaryTargets localBox coverBox210 :=
  covered_split coverBox210 0 (10023337/2560000) cover211 cover212
theorem cover209 : Covered stationaryTargets localBox coverBox209 :=
  covered_split coverBox209 1 (-473/512) cover210 cover223
theorem cover208 : Covered stationaryTargets localBox coverBox208 :=
  covered_split coverBox208 2 (39/640) cover209 cover242
theorem cover206 : Covered stationaryTargets localBox coverBox206 :=
  covered_split coverBox206 0 (5011369/1280000) cover207 cover208
theorem cover204 : Covered stationaryTargets localBox coverBox204 :=
  covered_split coverBox204 1 (-237/256) cover205 cover206
theorem cover199 : Covered stationaryTargets localBox coverBox199 :=
  covered_split coverBox199 2 (151/2560) cover200 cover201
theorem cover197 : Covered stationaryTargets localBox coverBox197 :=
  covered_split coverBox197 0 (20047273/5120000) cover198 cover199
theorem cover196 : Covered stationaryTargets localBox coverBox196 :=
  covered_split coverBox196 1 (-947/1024) cover197 cover202
theorem cover194 : Covered stationaryTargets localBox coverBox194 :=
  covered_split coverBox194 2 (15/256) cover195 cover196
theorem cover192 : Covered stationaryTargets localBox coverBox192 :=
  covered_split coverBox192 0 (10023337/2560000) cover193 cover194
theorem cover191 : Covered stationaryTargets localBox coverBox191 :=
  covered_split coverBox191 1 (-473/512) cover192 cover203
theorem cover189 : Covered stationaryTargets localBox coverBox189 :=
  covered_split coverBox189 2 (37/640) cover190 cover191
theorem cover187 : Covered stationaryTargets localBox coverBox187 :=
  covered_split coverBox187 0 (5011369/1280000) cover188 cover189
theorem cover183 : Covered stationaryTargets localBox coverBox183 :=
  covered_split coverBox183 2 (149/2560) cover184 cover185
theorem cover181 : Covered stationaryTargets localBox coverBox181 :=
  covered_split coverBox181 0 (20047273/5120000) cover182 cover183
theorem cover179 : Covered stationaryTargets localBox coverBox179 :=
  covered_split coverBox179 1 (-949/1024) cover180 cover181
theorem cover178 : Covered stationaryTargets localBox coverBox178 :=
  covered_split coverBox178 2 (15/256) cover179 cover186
theorem cover176 : Covered stationaryTargets localBox coverBox176 :=
  covered_split coverBox176 0 (10023337/2560000) cover177 cover178
theorem cover174 : Covered stationaryTargets localBox coverBox174 :=
  covered_split coverBox174 1 (-475/512) cover175 cover176
theorem cover169 : Covered stationaryTargets localBox coverBox169 :=
  covered_split coverBox169 1 (-951/1024) cover170 cover171
theorem cover168 : Covered stationaryTargets localBox coverBox168 :=
  covered_split coverBox168 2 (73/1280) cover169 cover172
theorem cover166 : Covered stationaryTargets localBox coverBox166 :=
  covered_split coverBox166 0 (10023337/2560000) cover167 cover168
theorem cover165 : Covered stationaryTargets localBox coverBox165 :=
  covered_split coverBox165 1 (-475/512) cover166 cover173
theorem cover164 : Covered stationaryTargets localBox coverBox164 :=
  covered_split coverBox164 2 (37/640) cover165 cover174
theorem cover162 : Covered stationaryTargets localBox coverBox162 :=
  covered_split coverBox162 0 (5011369/1280000) cover163 cover164
theorem cover161 : Covered stationaryTargets localBox coverBox161 :=
  covered_split coverBox161 1 (-237/256) cover162 cover187
theorem cover160 : Covered stationaryTargets localBox coverBox160 :=
  covered_split coverBox160 2 (19/320) cover161 cover204
theorem cover158 : Covered stationaryTargets localBox coverBox158 :=
  covered_split coverBox158 0 (501077/128000) cover159 cover160
theorem cover156 : Covered stationaryTargets localBox coverBox156 :=
  covered_split coverBox156 1 (-119/128) cover157 cover158
theorem cover152 : Covered stationaryTargets localBox coverBox152 :=
  covered_split coverBox152 2 (71/1280) cover153 cover154
theorem cover150 : Covered stationaryTargets localBox coverBox150 :=
  covered_split coverBox150 0 (10023337/2560000) cover151 cover152
theorem cover148 : Covered stationaryTargets localBox coverBox148 :=
  covered_split coverBox148 1 (-477/512) cover149 cover150
theorem cover146 : Covered stationaryTargets localBox coverBox146 :=
  covered_split coverBox146 2 (7/128) cover147 cover148
theorem cover144 : Covered stationaryTargets localBox coverBox144 :=
  covered_split coverBox144 0 (5011369/1280000) cover145 cover146
theorem cover142 : Covered stationaryTargets localBox coverBox142 :=
  covered_split coverBox142 1 (-239/256) cover143 cover144
theorem cover138 : Covered stationaryTargets localBox coverBox138 :=
  covered_split coverBox138 1 (-479/512) cover139 cover140
theorem cover136 : Covered stationaryTargets localBox coverBox136 :=
  covered_split coverBox136 2 (33/640) cover137 cover138
theorem cover134 : Covered stationaryTargets localBox coverBox134 :=
  covered_split coverBox134 0 (5011369/1280000) cover135 cover136
theorem cover133 : Covered stationaryTargets localBox coverBox133 :=
  covered_split coverBox133 1 (-239/256) cover134 cover141
theorem cover132 : Covered stationaryTargets localBox coverBox132 :=
  covered_split coverBox132 2 (17/320) cover133 cover142
theorem cover130 : Covered stationaryTargets localBox coverBox130 :=
  covered_split coverBox130 0 (501077/128000) cover131 cover132
theorem cover129 : Covered stationaryTargets localBox coverBox129 :=
  covered_split coverBox129 1 (-119/128) cover130 cover155
theorem cover128 : Covered stationaryTargets localBox coverBox128 :=
  covered_split coverBox128 2 (9/160) cover129 cover156
theorem cover126 : Covered stationaryTargets localBox coverBox126 :=
  covered_split coverBox126 0 (1252393/320000) cover127 cover128
theorem cover125 : Covered stationaryTargets localBox coverBox125 :=
  covered_split coverBox125 1 (-59/64) cover126 cover253
theorem cover124 : Covered stationaryTargets localBox coverBox124 :=
  covered_split coverBox124 2 (1/16) cover125 cover368
theorem cover121 : Covered stationaryTargets localBox coverBox121 :=
  covered_split coverBox121 2 (1/16) cover122 cover123
theorem cover120 : Covered stationaryTargets localBox coverBox120 :=
  covered_split coverBox120 0 (625897/160000) cover121 cover124
theorem cover119 : Covered stationaryTargets localBox coverBox119 :=
  covered_split coverBox119 1 (-29/32) cover120 cover519
theorem cover118 : Covered stationaryTargets localBox coverBox118 :=
  covered_split coverBox118 2 (3/40) cover119 cover544
theorem cover115 : Covered stationaryTargets localBox coverBox115 :=
  covered_split coverBox115 1 (-29/32) cover116 cover117
theorem cover112 : Covered stationaryTargets localBox coverBox112 :=
  covered_split coverBox112 1 (-29/32) cover113 cover114
theorem cover111 : Covered stationaryTargets localBox coverBox111 :=
  covered_split coverBox111 2 (3/40) cover112 cover115
theorem cover110 : Covered stationaryTargets localBox coverBox110 :=
  covered_split coverBox110 0 (312649/80000) cover111 cover118
theorem cover105 : Covered stationaryTargets localBox coverBox105 :=
  covered_split coverBox105 1 (-61/64) cover106 cover107
theorem cover104 : Covered stationaryTargets localBox coverBox104 :=
  covered_split coverBox104 2 (1/16) cover105 cover108
theorem cover101 : Covered stationaryTargets localBox coverBox101 :=
  covered_split coverBox101 2 (1/16) cover102 cover103
theorem cover100 : Covered stationaryTargets localBox coverBox100 :=
  covered_split coverBox100 0 (625897/160000) cover101 cover104
theorem cover98 : Covered stationaryTargets localBox coverBox98 :=
  covered_split coverBox98 1 (-31/32) cover99 cover100
theorem cover97 : Covered stationaryTargets localBox coverBox97 :=
  covered_split coverBox97 2 (3/40) cover98 cover109
theorem cover93 : Covered stationaryTargets localBox coverBox93 :=
  covered_split coverBox93 1 (-31/32) cover94 cover95
theorem cover92 : Covered stationaryTargets localBox coverBox92 :=
  covered_split coverBox92 2 (3/40) cover93 cover96
theorem cover91 : Covered stationaryTargets localBox coverBox91 :=
  covered_split coverBox91 0 (312649/80000) cover92 cover97
theorem cover90 : Covered stationaryTargets localBox coverBox90 :=
  covered_split coverBox90 1 (-15/16) cover91 cover110
theorem cover86 : Covered stationaryTargets localBox coverBox86 :=
  covered_split coverBox86 2 (3/80) cover87 cover88
theorem cover83 : Covered stationaryTargets localBox coverBox83 :=
  covered_split coverBox83 2 (3/80) cover84 cover85
theorem cover82 : Covered stationaryTargets localBox coverBox82 :=
  covered_split coverBox82 0 (625897/160000) cover83 cover86
theorem cover81 : Covered stationaryTargets localBox coverBox81 :=
  covered_split coverBox81 1 (-29/32) cover82 cover89
theorem cover79 : Covered stationaryTargets localBox coverBox79 :=
  covered_split coverBox79 2 (1/40) cover80 cover81
theorem cover76 : Covered stationaryTargets localBox coverBox76 :=
  covered_split coverBox76 1 (-29/32) cover77 cover78
theorem cover74 : Covered stationaryTargets localBox coverBox74 :=
  covered_split coverBox74 2 (1/40) cover75 cover76
theorem cover73 : Covered stationaryTargets localBox coverBox73 :=
  covered_split coverBox73 0 (312649/80000) cover74 cover79
theorem cover70 : Covered stationaryTargets localBox coverBox70 :=
  covered_split coverBox70 1 (-241/256) cover71 cover72
theorem cover68 : Covered stationaryTargets localBox coverBox68 :=
  covered_split coverBox68 2 (3/64) cover69 cover70
theorem cover66 : Covered stationaryTargets localBox coverBox66 :=
  covered_split coverBox66 0 (501077/128000) cover67 cover68
theorem cover64 : Covered stationaryTargets localBox coverBox64 :=
  covered_split coverBox64 1 (-121/128) cover65 cover66
theorem cover62 : Covered stationaryTargets localBox coverBox62 :=
  covered_split coverBox62 2 (7/160) cover63 cover64
theorem cover60 : Covered stationaryTargets localBox coverBox60 :=
  covered_split coverBox60 0 (1252393/320000) cover61 cover62
theorem cover57 : Covered stationaryTargets localBox coverBox57 :=
  covered_split coverBox57 0 (1252393/320000) cover58 cover59
theorem cover56 : Covered stationaryTargets localBox coverBox56 :=
  covered_split coverBox56 1 (-61/64) cover57 cover60
theorem cover52 : Covered stationaryTargets localBox coverBox52 :=
  covered_split coverBox52 1 (-123/128) cover53 cover54
theorem cover50 : Covered stationaryTargets localBox coverBox50 :=
  covered_split coverBox50 2 (1/32) cover51 cover52
theorem cover48 : Covered stationaryTargets localBox coverBox48 :=
  covered_split coverBox48 0 (1252393/320000) cover49 cover50
theorem cover47 : Covered stationaryTargets localBox coverBox47 :=
  covered_split coverBox47 1 (-61/64) cover48 cover55
theorem cover46 : Covered stationaryTargets localBox coverBox46 :=
  covered_split coverBox46 2 (3/80) cover47 cover56
theorem cover43 : Covered stationaryTargets localBox coverBox43 :=
  covered_split coverBox43 2 (3/80) cover44 cover45
theorem cover42 : Covered stationaryTargets localBox coverBox42 :=
  covered_split coverBox42 0 (625897/160000) cover43 cover46
theorem cover38 : Covered stationaryTargets localBox coverBox38 :=
  covered_split coverBox38 2 (1/32) cover39 cover40
theorem cover36 : Covered stationaryTargets localBox coverBox36 :=
  covered_split coverBox36 0 (1252393/320000) cover37 cover38
theorem cover34 : Covered stationaryTargets localBox coverBox34 :=
  covered_split coverBox34 1 (-63/64) cover35 cover36
theorem cover33 : Covered stationaryTargets localBox coverBox33 :=
  covered_split coverBox33 2 (3/80) cover34 cover41
theorem cover30 : Covered stationaryTargets localBox coverBox30 :=
  covered_split coverBox30 2 (3/80) cover31 cover32
theorem cover29 : Covered stationaryTargets localBox coverBox29 :=
  covered_split coverBox29 0 (625897/160000) cover30 cover33
theorem cover28 : Covered stationaryTargets localBox coverBox28 :=
  covered_split coverBox28 1 (-31/32) cover29 cover42
theorem cover23 : Covered stationaryTargets localBox coverBox23 :=
  covered_split coverBox23 2 (3/160) cover24 cover25
theorem cover21 : Covered stationaryTargets localBox coverBox21 :=
  covered_split coverBox21 0 (1252393/320000) cover22 cover23
theorem cover20 : Covered stationaryTargets localBox coverBox20 :=
  covered_split coverBox20 1 (-63/64) cover21 cover26
theorem cover18 : Covered stationaryTargets localBox coverBox18 :=
  covered_split coverBox18 2 (1/80) cover19 cover20
theorem cover15 : Covered stationaryTargets localBox coverBox15 :=
  covered_split coverBox15 2 (1/80) cover16 cover17
theorem cover14 : Covered stationaryTargets localBox coverBox14 :=
  covered_split coverBox14 0 (625897/160000) cover15 cover18
theorem cover13 : Covered stationaryTargets localBox coverBox13 :=
  covered_split coverBox13 1 (-31/32) cover14 cover27
theorem cover12 : Covered stationaryTargets localBox coverBox12 :=
  covered_split coverBox12 2 (1/40) cover13 cover28
theorem cover9 : Covered stationaryTargets localBox coverBox9 :=
  covered_split coverBox9 1 (-31/32) cover10 cover11
theorem cover6 : Covered stationaryTargets localBox coverBox6 :=
  covered_split coverBox6 1 (-31/32) cover7 cover8
theorem cover5 : Covered stationaryTargets localBox coverBox5 :=
  covered_split coverBox5 2 (1/40) cover6 cover9
theorem cover4 : Covered stationaryTargets localBox coverBox4 :=
  covered_split coverBox4 0 (312649/80000) cover5 cover12
theorem cover3 : Covered stationaryTargets localBox coverBox3 :=
  covered_split coverBox3 1 (-15/16) cover4 cover73
theorem cover2 : Covered stationaryTargets localBox coverBox2 :=
  covered_split coverBox2 2 (1/20) cover3 cover90
theorem cover1 : Covered stationaryTargets localBox coverBox1 :=
  covered_split coverBox1 1 (-7/8) cover2 cover585
theorem cover0 : Covered stationaryTargets localBox coverBox0 :=
  covered_split coverBox0 1 (-3/4) cover1 cover612

theorem stationary_localization (env : Fin 3 → ℝ)
    (he : initialBox.Mem env) (hz : SimultaneousZeros stationaryTargets env) :
    localBox.Mem env :=
  cover0 env he hz

end SquaresInCircles.Eight.ExactFamily.Generated
