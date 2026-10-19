module

public import SquaresInCircles.Eight.ExactFamily.Expression

/-!
# Eight squares: the formulas of the stationary point

The chain of `ExactFamily/Coordinates.lean` as formulas (`Formula`) in the variables `(q, y, z)`:
the coordinates `x₁, x₂, y₃, x₄` (`xOneFormula`, ...), the cosine and sine of the tilt, the fifth
corner `(h₁, h₂)`, the defect `F = h₁² + h₂² - q` (`FFormula`), its first partial derivatives,
its second derivatives in `y` and `z`, and the determinant `(F_yy - 1/4)(F_zz - 1/4) - F_yz²` of
the shifted Hessian (`determinantFormula`, `determinant_eval`). Each derivative is the symbolic
derivative `Formula.diff` of `F`, `F_y` or `F_z`, an identity of formulas decided by the kernel
(`Fq_diff`, ...), and the two mixed partials agree in value (`mixed_partials`). `scalarF` and its
companions write `F`, `F_y`, `F_z` and the coordinates as explicit real expressions (`F_eval`,
...). The module also fixes the box `localBox`, the trial point `(trialY, trialZ)` and the
bracket `[sharpLower, sharpUpper]` of `qStar`. Written by `scripts/eight/generate_stationary.py`.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 100000

namespace SquaresInCircles.Eight.ExactFamily.Generated
open Arithmetic


noncomputable def formula0 : Formula 3 := .var 0
noncomputable def formula1 : Formula 3 := .var 1
noncomputable def formula2 : Formula 3 := .var 2
noncomputable def formula3 : Formula 3 := .const 1
noncomputable def formula4 : Formula 3 := .const 2
noncomputable def formula6 : Formula 3 := .pow formula1 2
noncomputable def formula7 : Formula 3 := .neg formula6
noncomputable def formula9 : Formula 3 := .add formula0 formula7
noncomputable def formula10 : Formula 3 := .sqrt formula9
noncomputable def formula11 : Formula 3 := .add formula1 formula4
noncomputable def formula12 : Formula 3 := .pow formula11 2
noncomputable def formula13 : Formula 3 := .neg formula12
noncomputable def formula14 : Formula 3 := .add formula0 formula13
noncomputable def formula15 : Formula 3 := .sqrt formula14
noncomputable def formula16 : Formula 3 := .const (-3)
noncomputable def formula17 : Formula 3 := .add formula15 formula16
noncomputable def formula18 : Formula 3 := .pow formula17 2
noncomputable def formula19 : Formula 3 := .neg formula18
noncomputable def formula20 : Formula 3 := .add formula0 formula19
noncomputable def formula21 : Formula 3 := .sqrt formula20
noncomputable def formula22 : Formula 3 := .const (-2)
noncomputable def formula23 : Formula 3 := .add formula21 formula22
noncomputable def formula24 : Formula 3 := .pow formula23 2
noncomputable def formula25 : Formula 3 := .neg formula24
noncomputable def formula26 : Formula 3 := .add formula0 formula25
noncomputable def formula27 : Formula 3 := .sqrt formula26
noncomputable def formula28 : Formula 3 := .neg formula27
noncomputable def formula29 : Formula 3 := .pow formula2 2
noncomputable def formula30 : Formula 3 := .add formula3 formula29
noncomputable def formula31 : Formula 3 := .neg formula29
noncomputable def formula32 : Formula 3 := .add formula3 formula31
noncomputable def formula33 : Formula 3 := .inv formula30
noncomputable def formula34 : Formula 3 := .mul formula32 formula33
noncomputable def formula35 : Formula 3 := .mul formula4 formula2
noncomputable def formula36 : Formula 3 := .mul formula35 formula33
noncomputable def formula37 : Formula 3 := .mul formula34 formula10
noncomputable def formula38 : Formula 3 := .mul formula36 formula1
noncomputable def formula39 : Formula 3 := .add formula37 formula38
noncomputable def formula40 : Formula 3 := .add formula39 formula22
noncomputable def formula41 : Formula 3 := .neg formula34
noncomputable def formula42 : Formula 3 := .add formula40 formula41
noncomputable def formula43 : Formula 3 := .mul formula36 formula28
noncomputable def formula44 : Formula 3 := .neg formula43
noncomputable def formula45 : Formula 3 := .mul formula34 formula23
noncomputable def formula46 : Formula 3 := .add formula44 formula45
noncomputable def formula47 : Formula 3 := .const (-1)
noncomputable def formula48 : Formula 3 := .add formula46 formula47
noncomputable def formula49 : Formula 3 := .neg formula36
noncomputable def formula50 : Formula 3 := .add formula48 formula49
noncomputable def formula51 : Formula 3 := .pow formula42 2
noncomputable def formula52 : Formula 3 := .pow formula50 2
noncomputable def formula53 : Formula 3 := .add formula51 formula52
noncomputable def formula54 : Formula 3 := .neg formula0
noncomputable def formula55 : Formula 3 := .add formula53 formula54
noncomputable def formula56 : Formula 3 := .pow formula30 2
noncomputable def formula57 : Formula 3 := .inv formula56
noncomputable def formula58 : Formula 3 := .mul formula4 formula10
noncomputable def formula59 : Formula 3 := .inv formula58
noncomputable def formula60 : Formula 3 := .mul formula34 formula59
noncomputable def formula61 : Formula 3 := .mul formula42 formula60
noncomputable def formula62 : Formula 3 := .mul formula4 formula61
noncomputable def formula63 : Formula 3 := .mul formula4 formula15
noncomputable def formula64 : Formula 3 := .inv formula63
noncomputable def formula65 : Formula 3 := .mul formula17 formula64
noncomputable def formula66 : Formula 3 := .mul formula4 formula65
noncomputable def formula67 : Formula 3 := .neg formula66
noncomputable def formula68 : Formula 3 := .add formula3 formula67
noncomputable def formula69 : Formula 3 := .mul formula4 formula21
noncomputable def formula70 : Formula 3 := .inv formula69
noncomputable def formula71 : Formula 3 := .mul formula68 formula70
noncomputable def formula72 : Formula 3 := .mul formula23 formula71
noncomputable def formula73 : Formula 3 := .mul formula4 formula72
noncomputable def formula74 : Formula 3 := .neg formula73
noncomputable def formula75 : Formula 3 := .add formula3 formula74
noncomputable def formula76 : Formula 3 := .mul formula4 formula27
noncomputable def formula77 : Formula 3 := .inv formula76
noncomputable def formula78 : Formula 3 := .mul formula75 formula77
noncomputable def formula79 : Formula 3 := .neg formula78
noncomputable def formula80 : Formula 3 := .mul formula36 formula79
noncomputable def formula81 : Formula 3 := .neg formula80
noncomputable def formula82 : Formula 3 := .mul formula34 formula71
noncomputable def formula83 : Formula 3 := .add formula81 formula82
noncomputable def formula84 : Formula 3 := .mul formula50 formula83
noncomputable def formula85 : Formula 3 := .mul formula4 formula84
noncomputable def formula86 : Formula 3 := .add formula62 formula85
noncomputable def formula87 : Formula 3 := .add formula86 formula47
noncomputable def formula88 : Formula 3 := .mul formula4 formula1
noncomputable def formula89 : Formula 3 := .neg formula88
noncomputable def formula90 : Formula 3 := .mul formula89 formula59
noncomputable def formula91 : Formula 3 := .mul formula34 formula90
noncomputable def formula92 : Formula 3 := .add formula91 formula36
noncomputable def formula93 : Formula 3 := .mul formula42 formula92
noncomputable def formula94 : Formula 3 := .mul formula4 formula93
noncomputable def formula95 : Formula 3 := .mul formula4 formula11
noncomputable def formula96 : Formula 3 := .neg formula95
noncomputable def formula97 : Formula 3 := .mul formula96 formula64
noncomputable def formula98 : Formula 3 := .mul formula17 formula97
noncomputable def formula99 : Formula 3 := .mul formula4 formula98
noncomputable def formula100 : Formula 3 := .neg formula99
noncomputable def formula101 : Formula 3 := .mul formula100 formula70
noncomputable def formula102 : Formula 3 := .mul formula23 formula101
noncomputable def formula103 : Formula 3 := .mul formula4 formula102
noncomputable def formula104 : Formula 3 := .neg formula103
noncomputable def formula105 : Formula 3 := .mul formula104 formula77
noncomputable def formula106 : Formula 3 := .neg formula105
noncomputable def formula107 : Formula 3 := .mul formula36 formula106
noncomputable def formula108 : Formula 3 := .neg formula107
noncomputable def formula109 : Formula 3 := .mul formula34 formula101
noncomputable def formula110 : Formula 3 := .add formula108 formula109
noncomputable def formula111 : Formula 3 := .mul formula50 formula110
noncomputable def formula112 : Formula 3 := .mul formula4 formula111
noncomputable def formula113 : Formula 3 := .add formula94 formula112
noncomputable def formula114 : Formula 3 := .neg formula35
noncomputable def formula115 : Formula 3 := .mul formula114 formula33
noncomputable def formula116 : Formula 3 := .mul formula35 formula57
noncomputable def formula117 : Formula 3 := .neg formula116
noncomputable def formula118 : Formula 3 := .mul formula32 formula117
noncomputable def formula119 : Formula 3 := .add formula115 formula118
noncomputable def formula120 : Formula 3 := .mul formula119 formula10
noncomputable def formula121 : Formula 3 := .mul formula4 formula33
noncomputable def formula122 : Formula 3 := .mul formula35 formula117
noncomputable def formula123 : Formula 3 := .add formula121 formula122
noncomputable def formula124 : Formula 3 := .mul formula123 formula1
noncomputable def formula125 : Formula 3 := .add formula120 formula124
noncomputable def formula126 : Formula 3 := .neg formula119
noncomputable def formula127 : Formula 3 := .add formula125 formula126
noncomputable def formula128 : Formula 3 := .mul formula42 formula127
noncomputable def formula129 : Formula 3 := .mul formula4 formula128
noncomputable def formula130 : Formula 3 := .mul formula123 formula28
noncomputable def formula131 : Formula 3 := .neg formula130
noncomputable def formula132 : Formula 3 := .mul formula119 formula23
noncomputable def formula133 : Formula 3 := .add formula131 formula132
noncomputable def formula134 : Formula 3 := .neg formula123
noncomputable def formula135 : Formula 3 := .add formula133 formula134
noncomputable def formula136 : Formula 3 := .mul formula50 formula135
noncomputable def formula137 : Formula 3 := .mul formula4 formula136
noncomputable def formula138 : Formula 3 := .add formula129 formula137
noncomputable def formula139 : Formula 3 := .mul formula92 formula92
noncomputable def formula140 : Formula 3 := .mul formula22 formula59
noncomputable def formula141 : Formula 3 := .mul formula4 formula90
noncomputable def formula142 : Formula 3 := .pow formula58 2
noncomputable def formula143 : Formula 3 := .inv formula142
noncomputable def formula144 : Formula 3 := .mul formula141 formula143
noncomputable def formula145 : Formula 3 := .neg formula144
noncomputable def formula146 : Formula 3 := .mul formula89 formula145
noncomputable def formula147 : Formula 3 := .add formula140 formula146
noncomputable def formula148 : Formula 3 := .mul formula34 formula147
noncomputable def formula149 : Formula 3 := .mul formula42 formula148
noncomputable def formula150 : Formula 3 := .add formula139 formula149
noncomputable def formula151 : Formula 3 := .mul formula4 formula150
noncomputable def formula152 : Formula 3 := .mul formula110 formula110
noncomputable def formula153 : Formula 3 := .mul formula101 formula101
noncomputable def formula154 : Formula 3 := .mul formula97 formula97
noncomputable def formula155 : Formula 3 := .mul formula22 formula64
noncomputable def formula156 : Formula 3 := .mul formula4 formula97
noncomputable def formula157 : Formula 3 := .pow formula63 2
noncomputable def formula158 : Formula 3 := .inv formula157
noncomputable def formula159 : Formula 3 := .mul formula156 formula158
noncomputable def formula160 : Formula 3 := .neg formula159
noncomputable def formula161 : Formula 3 := .mul formula96 formula160
noncomputable def formula162 : Formula 3 := .add formula155 formula161
noncomputable def formula163 : Formula 3 := .mul formula17 formula162
noncomputable def formula164 : Formula 3 := .add formula154 formula163
noncomputable def formula165 : Formula 3 := .mul formula4 formula164
noncomputable def formula166 : Formula 3 := .neg formula165
noncomputable def formula167 : Formula 3 := .mul formula166 formula70
noncomputable def formula168 : Formula 3 := .mul formula4 formula101
noncomputable def formula169 : Formula 3 := .pow formula69 2
noncomputable def formula170 : Formula 3 := .inv formula169
noncomputable def formula171 : Formula 3 := .mul formula168 formula170
noncomputable def formula172 : Formula 3 := .neg formula171
noncomputable def formula173 : Formula 3 := .mul formula100 formula172
noncomputable def formula174 : Formula 3 := .add formula167 formula173
noncomputable def formula175 : Formula 3 := .mul formula23 formula174
noncomputable def formula176 : Formula 3 := .add formula153 formula175
noncomputable def formula177 : Formula 3 := .mul formula4 formula176
noncomputable def formula178 : Formula 3 := .neg formula177
noncomputable def formula179 : Formula 3 := .mul formula178 formula77
noncomputable def formula180 : Formula 3 := .mul formula4 formula105
noncomputable def formula181 : Formula 3 := .pow formula76 2
noncomputable def formula182 : Formula 3 := .inv formula181
noncomputable def formula183 : Formula 3 := .mul formula180 formula182
noncomputable def formula184 : Formula 3 := .neg formula183
noncomputable def formula185 : Formula 3 := .mul formula104 formula184
noncomputable def formula186 : Formula 3 := .add formula179 formula185
noncomputable def formula187 : Formula 3 := .neg formula186
noncomputable def formula188 : Formula 3 := .mul formula36 formula187
noncomputable def formula189 : Formula 3 := .neg formula188
noncomputable def formula190 : Formula 3 := .mul formula34 formula174
noncomputable def formula191 : Formula 3 := .add formula189 formula190
noncomputable def formula192 : Formula 3 := .mul formula50 formula191
noncomputable def formula193 : Formula 3 := .add formula152 formula192
noncomputable def formula194 : Formula 3 := .mul formula4 formula193
noncomputable def formula195 : Formula 3 := .add formula151 formula194
noncomputable def formula196 : Formula 3 := .mul formula127 formula92
noncomputable def formula197 : Formula 3 := .mul formula119 formula90
noncomputable def formula198 : Formula 3 := .add formula197 formula123
noncomputable def formula199 : Formula 3 := .mul formula42 formula198
noncomputable def formula200 : Formula 3 := .add formula196 formula199
noncomputable def formula201 : Formula 3 := .mul formula4 formula200
noncomputable def formula202 : Formula 3 := .mul formula135 formula110
noncomputable def formula203 : Formula 3 := .mul formula123 formula106
noncomputable def formula204 : Formula 3 := .neg formula203
noncomputable def formula205 : Formula 3 := .mul formula119 formula101
noncomputable def formula206 : Formula 3 := .add formula204 formula205
noncomputable def formula207 : Formula 3 := .mul formula50 formula206
noncomputable def formula208 : Formula 3 := .add formula202 formula207
noncomputable def formula209 : Formula 3 := .mul formula4 formula208
noncomputable def formula210 : Formula 3 := .add formula201 formula209
noncomputable def formula211 : Formula 3 := .mul formula127 formula127
noncomputable def formula212 : Formula 3 := .mul formula22 formula33
noncomputable def formula213 : Formula 3 := .mul formula114 formula117
noncomputable def formula214 : Formula 3 := .add formula212 formula213
noncomputable def formula215 : Formula 3 := .mul formula4 formula57
noncomputable def formula216 : Formula 3 := .mul formula30 formula35
noncomputable def formula217 : Formula 3 := .mul formula4 formula216
noncomputable def formula218 : Formula 3 := .pow formula56 2
noncomputable def formula219 : Formula 3 := .inv formula218
noncomputable def formula220 : Formula 3 := .mul formula217 formula219
noncomputable def formula221 : Formula 3 := .neg formula220
noncomputable def formula222 : Formula 3 := .mul formula35 formula221
noncomputable def formula223 : Formula 3 := .add formula215 formula222
noncomputable def formula224 : Formula 3 := .neg formula223
noncomputable def formula225 : Formula 3 := .mul formula32 formula224
noncomputable def formula226 : Formula 3 := .add formula213 formula225
noncomputable def formula227 : Formula 3 := .add formula214 formula226
noncomputable def formula228 : Formula 3 := .mul formula227 formula10
noncomputable def formula229 : Formula 3 := .mul formula4 formula117
noncomputable def formula230 : Formula 3 := .mul formula35 formula224
noncomputable def formula231 : Formula 3 := .add formula229 formula230
noncomputable def formula232 : Formula 3 := .add formula229 formula231
noncomputable def formula233 : Formula 3 := .mul formula232 formula1
noncomputable def formula234 : Formula 3 := .add formula228 formula233
noncomputable def formula235 : Formula 3 := .neg formula227
noncomputable def formula236 : Formula 3 := .add formula234 formula235
noncomputable def formula237 : Formula 3 := .mul formula42 formula236
noncomputable def formula238 : Formula 3 := .add formula211 formula237
noncomputable def formula239 : Formula 3 := .mul formula4 formula238
noncomputable def formula240 : Formula 3 := .mul formula135 formula135
noncomputable def formula241 : Formula 3 := .mul formula232 formula28
noncomputable def formula242 : Formula 3 := .neg formula241
noncomputable def formula243 : Formula 3 := .mul formula227 formula23
noncomputable def formula244 : Formula 3 := .add formula242 formula243
noncomputable def formula245 : Formula 3 := .neg formula232
noncomputable def formula246 : Formula 3 := .add formula244 formula245
noncomputable def formula247 : Formula 3 := .mul formula50 formula246
noncomputable def formula248 : Formula 3 := .add formula240 formula247
noncomputable def formula249 : Formula 3 := .mul formula4 formula248
noncomputable def formula250 : Formula 3 := .add formula239 formula249
noncomputable def formula252 : Formula 3 := .const (-1/4)
noncomputable def formula253 : Formula 3 := .add formula195 formula252
noncomputable def formula254 : Formula 3 := .add formula250 formula252
noncomputable def formula255 : Formula 3 := .mul formula253 formula254
noncomputable def formula256 : Formula 3 := .pow formula210 2
noncomputable def formula257 : Formula 3 := .neg formula256
noncomputable def formula258 : Formula 3 := .add formula255 formula257

noncomputable def FFormula : Formula 3 := formula55
noncomputable def FqFormula : Formula 3 := formula87
noncomputable def FyFormula : Formula 3 := formula113
noncomputable def FzFormula : Formula 3 := formula138
noncomputable def FyyFormula : Formula 3 := formula195
noncomputable def FyzFormula : Formula 3 := formula210
noncomputable def FzzFormula : Formula 3 := formula250
noncomputable def xOneFormula : Formula 3 := formula10
noncomputable def xTwoFormula : Formula 3 := formula15
noncomputable def yThreeFormula : Formula 3 := formula21
noncomputable def xFourFormula : Formula 3 := formula28
noncomputable def cosineFormula : Formula 3 := formula34
noncomputable def sineFormula : Formula 3 := formula36
noncomputable def hOneFormula : Formula 3 := formula42
noncomputable def hTwoFormula : Formula 3 := formula50
noncomputable def determinantFormula : Formula 3 := formula258
/-- The box of `(q, y, z)`: `q` in `[qMinus, Q0]` and `(y, z)` in the rectangle `poseBox`
of `ExactFamily/Analysis.lean`. -/
noncomputable def localBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
/-- The position `y` of the trial point, near the stationary pose (`sharpPose_close`). -/
noncomputable def trialY : ℝ := (-3682626712030424527/4000000000000000000)
/-- The half-angle tangent `z` of the trial point. -/
noncomputable def trialZ : ℝ := (618974110076603597/10000000000000000000)
/-- The lower end of the bracket of `qStar` (`qStar_bracket`). -/
noncomputable def sharpLower : ℝ := (97888353437936878163/25000000000000000000)
/-- The upper end of the bracket of `qStar`. -/
noncomputable def sharpUpper : ℝ := (97888353437936885663/25000000000000000000)

theorem Fq_diff : FFormula.diff 0 = FqFormula := by decide +kernel
theorem Fy_diff : FFormula.diff 1 = FyFormula := by decide +kernel
theorem Fz_diff : FFormula.diff 2 = FzFormula := by decide +kernel
theorem Fyy_diff : FyFormula.diff 1 = FyyFormula := by decide +kernel
theorem Fyz_diff : FyFormula.diff 2 = FyzFormula := by decide +kernel
theorem Fzz_diff : FzFormula.diff 2 = FzzFormula := by decide +kernel

noncomputable def scalarF (q y z : ℝ) : ℝ := by
  let n0 : ℝ := q
  let n1 : ℝ := y
  let n2 : ℝ := z
  let n3 : ℝ := ((1:ℚ):ℝ)
  let n4 : ℝ := ((2:ℚ):ℝ)
  let n6 : ℝ := n1^2
  let n7 : ℝ := -n6
  let n9 : ℝ := n0+n7
  let n10 : ℝ := Real.sqrt n9
  let n11 : ℝ := n1+n4
  let n12 : ℝ := n11^2
  let n13 : ℝ := -n12
  let n14 : ℝ := n0+n13
  let n15 : ℝ := Real.sqrt n14
  let n16 : ℝ := ((-3:ℚ):ℝ)
  let n17 : ℝ := n15+n16
  let n18 : ℝ := n17^2
  let n19 : ℝ := -n18
  let n20 : ℝ := n0+n19
  let n21 : ℝ := Real.sqrt n20
  let n22 : ℝ := ((-2:ℚ):ℝ)
  let n23 : ℝ := n21+n22
  let n24 : ℝ := n23^2
  let n25 : ℝ := -n24
  let n26 : ℝ := n0+n25
  let n27 : ℝ := Real.sqrt n26
  let n28 : ℝ := -n27
  let n29 : ℝ := n2^2
  let n30 : ℝ := n3+n29
  let n31 : ℝ := -n29
  let n32 : ℝ := n3+n31
  let n33 : ℝ := (n30)⁻¹
  let n34 : ℝ := n32*n33
  let n35 : ℝ := n4*n2
  let n36 : ℝ := n35*n33
  let n37 : ℝ := n34*n10
  let n38 : ℝ := n36*n1
  let n39 : ℝ := n37+n38
  let n40 : ℝ := n39+n22
  let n41 : ℝ := -n34
  let n42 : ℝ := n40+n41
  let n43 : ℝ := n36*n28
  let n44 : ℝ := -n43
  let n45 : ℝ := n34*n23
  let n46 : ℝ := n44+n45
  let n47 : ℝ := ((-1:ℚ):ℝ)
  let n48 : ℝ := n46+n47
  let n49 : ℝ := -n36
  let n50 : ℝ := n48+n49
  let n51 : ℝ := n42^2
  let n52 : ℝ := n50^2
  let n53 : ℝ := n51+n52
  let n54 : ℝ := -n0
  let n55 : ℝ := n53+n54
  exact n55
theorem F_eval (q y z : ℝ) : FFormula.eval ![q,y,z] = scalarF q y z := by
  rfl

noncomputable def scalarFy (q y z : ℝ) : ℝ := by
  let n0 : ℝ := q
  let n1 : ℝ := y
  let n2 : ℝ := z
  let n3 : ℝ := ((1:ℚ):ℝ)
  let n4 : ℝ := ((2:ℚ):ℝ)
  let n6 : ℝ := n1^2
  let n7 : ℝ := -n6
  let n9 : ℝ := n0+n7
  let n10 : ℝ := Real.sqrt n9
  let n11 : ℝ := n1+n4
  let n12 : ℝ := n11^2
  let n13 : ℝ := -n12
  let n14 : ℝ := n0+n13
  let n15 : ℝ := Real.sqrt n14
  let n16 : ℝ := ((-3:ℚ):ℝ)
  let n17 : ℝ := n15+n16
  let n18 : ℝ := n17^2
  let n19 : ℝ := -n18
  let n20 : ℝ := n0+n19
  let n21 : ℝ := Real.sqrt n20
  let n22 : ℝ := ((-2:ℚ):ℝ)
  let n23 : ℝ := n21+n22
  let n24 : ℝ := n23^2
  let n25 : ℝ := -n24
  let n26 : ℝ := n0+n25
  let n27 : ℝ := Real.sqrt n26
  let n28 : ℝ := -n27
  let n29 : ℝ := n2^2
  let n30 : ℝ := n3+n29
  let n31 : ℝ := -n29
  let n32 : ℝ := n3+n31
  let n33 : ℝ := (n30)⁻¹
  let n34 : ℝ := n32*n33
  let n35 : ℝ := n4*n2
  let n36 : ℝ := n35*n33
  let n37 : ℝ := n34*n10
  let n38 : ℝ := n36*n1
  let n39 : ℝ := n37+n38
  let n40 : ℝ := n39+n22
  let n41 : ℝ := -n34
  let n42 : ℝ := n40+n41
  let n43 : ℝ := n36*n28
  let n44 : ℝ := -n43
  let n45 : ℝ := n34*n23
  let n46 : ℝ := n44+n45
  let n47 : ℝ := ((-1:ℚ):ℝ)
  let n48 : ℝ := n46+n47
  let n49 : ℝ := -n36
  let n50 : ℝ := n48+n49
  let n58 : ℝ := n4*n10
  let n59 : ℝ := (n58)⁻¹
  let n63 : ℝ := n4*n15
  let n64 : ℝ := (n63)⁻¹
  let n69 : ℝ := n4*n21
  let n70 : ℝ := (n69)⁻¹
  let n76 : ℝ := n4*n27
  let n77 : ℝ := (n76)⁻¹
  let n88 : ℝ := n4*n1
  let n89 : ℝ := -n88
  let n90 : ℝ := n89*n59
  let n91 : ℝ := n34*n90
  let n92 : ℝ := n91+n36
  let n93 : ℝ := n42*n92
  let n94 : ℝ := n4*n93
  let n95 : ℝ := n4*n11
  let n96 : ℝ := -n95
  let n97 : ℝ := n96*n64
  let n98 : ℝ := n17*n97
  let n99 : ℝ := n4*n98
  let n100 : ℝ := -n99
  let n101 : ℝ := n100*n70
  let n102 : ℝ := n23*n101
  let n103 : ℝ := n4*n102
  let n104 : ℝ := -n103
  let n105 : ℝ := n104*n77
  let n106 : ℝ := -n105
  let n107 : ℝ := n36*n106
  let n108 : ℝ := -n107
  let n109 : ℝ := n34*n101
  let n110 : ℝ := n108+n109
  let n111 : ℝ := n50*n110
  let n112 : ℝ := n4*n111
  let n113 : ℝ := n94+n112
  exact n113
theorem Fy_eval (q y z : ℝ) : FyFormula.eval ![q,y,z] = scalarFy q y z := by
  rfl

noncomputable def scalarFz (q y z : ℝ) : ℝ := by
  let n0 : ℝ := q
  let n1 : ℝ := y
  let n2 : ℝ := z
  let n3 : ℝ := ((1:ℚ):ℝ)
  let n4 : ℝ := ((2:ℚ):ℝ)
  let n6 : ℝ := n1^2
  let n7 : ℝ := -n6
  let n9 : ℝ := n0+n7
  let n10 : ℝ := Real.sqrt n9
  let n11 : ℝ := n1+n4
  let n12 : ℝ := n11^2
  let n13 : ℝ := -n12
  let n14 : ℝ := n0+n13
  let n15 : ℝ := Real.sqrt n14
  let n16 : ℝ := ((-3:ℚ):ℝ)
  let n17 : ℝ := n15+n16
  let n18 : ℝ := n17^2
  let n19 : ℝ := -n18
  let n20 : ℝ := n0+n19
  let n21 : ℝ := Real.sqrt n20
  let n22 : ℝ := ((-2:ℚ):ℝ)
  let n23 : ℝ := n21+n22
  let n24 : ℝ := n23^2
  let n25 : ℝ := -n24
  let n26 : ℝ := n0+n25
  let n27 : ℝ := Real.sqrt n26
  let n28 : ℝ := -n27
  let n29 : ℝ := n2^2
  let n30 : ℝ := n3+n29
  let n31 : ℝ := -n29
  let n32 : ℝ := n3+n31
  let n33 : ℝ := (n30)⁻¹
  let n34 : ℝ := n32*n33
  let n35 : ℝ := n4*n2
  let n36 : ℝ := n35*n33
  let n37 : ℝ := n34*n10
  let n38 : ℝ := n36*n1
  let n39 : ℝ := n37+n38
  let n40 : ℝ := n39+n22
  let n41 : ℝ := -n34
  let n42 : ℝ := n40+n41
  let n43 : ℝ := n36*n28
  let n44 : ℝ := -n43
  let n45 : ℝ := n34*n23
  let n46 : ℝ := n44+n45
  let n47 : ℝ := ((-1:ℚ):ℝ)
  let n48 : ℝ := n46+n47
  let n49 : ℝ := -n36
  let n50 : ℝ := n48+n49
  let n56 : ℝ := n30^2
  let n57 : ℝ := (n56)⁻¹
  let n114 : ℝ := -n35
  let n115 : ℝ := n114*n33
  let n116 : ℝ := n35*n57
  let n117 : ℝ := -n116
  let n118 : ℝ := n32*n117
  let n119 : ℝ := n115+n118
  let n120 : ℝ := n119*n10
  let n121 : ℝ := n4*n33
  let n122 : ℝ := n35*n117
  let n123 : ℝ := n121+n122
  let n124 : ℝ := n123*n1
  let n125 : ℝ := n120+n124
  let n126 : ℝ := -n119
  let n127 : ℝ := n125+n126
  let n128 : ℝ := n42*n127
  let n129 : ℝ := n4*n128
  let n130 : ℝ := n123*n28
  let n131 : ℝ := -n130
  let n132 : ℝ := n119*n23
  let n133 : ℝ := n131+n132
  let n134 : ℝ := -n123
  let n135 : ℝ := n133+n134
  let n136 : ℝ := n50*n135
  let n137 : ℝ := n4*n136
  let n138 : ℝ := n129+n137
  exact n138
theorem Fz_eval (q y z : ℝ) : FzFormula.eval ![q,y,z] = scalarFz q y z := by
  rfl

noncomputable def scalarxOne (q y _z : ℝ) : ℝ := by
  let n0 : ℝ := q
  let n1 : ℝ := y
  let n6 : ℝ := n1^2
  let n7 : ℝ := -n6
  let n9 : ℝ := n0+n7
  let n10 : ℝ := Real.sqrt n9
  exact n10
theorem xOne_eval (q y z : ℝ) : xOneFormula.eval ![q,y,z] = scalarxOne q y z := by
  rfl

noncomputable def scalarxTwo (q y _z : ℝ) : ℝ := by
  let n0 : ℝ := q
  let n1 : ℝ := y
  let n4 : ℝ := ((2:ℚ):ℝ)
  let n11 : ℝ := n1+n4
  let n12 : ℝ := n11^2
  let n13 : ℝ := -n12
  let n14 : ℝ := n0+n13
  let n15 : ℝ := Real.sqrt n14
  exact n15
theorem xTwo_eval (q y z : ℝ) : xTwoFormula.eval ![q,y,z] = scalarxTwo q y z := by
  rfl

noncomputable def scalaryThree (q y _z : ℝ) : ℝ := by
  let n0 : ℝ := q
  let n1 : ℝ := y
  let n4 : ℝ := ((2:ℚ):ℝ)
  let n11 : ℝ := n1+n4
  let n12 : ℝ := n11^2
  let n13 : ℝ := -n12
  let n14 : ℝ := n0+n13
  let n15 : ℝ := Real.sqrt n14
  let n16 : ℝ := ((-3:ℚ):ℝ)
  let n17 : ℝ := n15+n16
  let n18 : ℝ := n17^2
  let n19 : ℝ := -n18
  let n20 : ℝ := n0+n19
  let n21 : ℝ := Real.sqrt n20
  exact n21
theorem yThree_eval (q y z : ℝ) : yThreeFormula.eval ![q,y,z] = scalaryThree q y z := by
  rfl

noncomputable def scalarxFour (q y _z : ℝ) : ℝ := by
  let n0 : ℝ := q
  let n1 : ℝ := y
  let n4 : ℝ := ((2:ℚ):ℝ)
  let n11 : ℝ := n1+n4
  let n12 : ℝ := n11^2
  let n13 : ℝ := -n12
  let n14 : ℝ := n0+n13
  let n15 : ℝ := Real.sqrt n14
  let n16 : ℝ := ((-3:ℚ):ℝ)
  let n17 : ℝ := n15+n16
  let n18 : ℝ := n17^2
  let n19 : ℝ := -n18
  let n20 : ℝ := n0+n19
  let n21 : ℝ := Real.sqrt n20
  let n22 : ℝ := ((-2:ℚ):ℝ)
  let n23 : ℝ := n21+n22
  let n24 : ℝ := n23^2
  let n25 : ℝ := -n24
  let n26 : ℝ := n0+n25
  let n27 : ℝ := Real.sqrt n26
  let n28 : ℝ := -n27
  exact n28
theorem xFour_eval (q y z : ℝ) : xFourFormula.eval ![q,y,z] = scalarxFour q y z := by
  rfl

noncomputable def scalarcosine (_q _y z : ℝ) : ℝ := by
  let n2 : ℝ := z
  let n3 : ℝ := ((1:ℚ):ℝ)
  let n29 : ℝ := n2^2
  let n30 : ℝ := n3+n29
  let n31 : ℝ := -n29
  let n32 : ℝ := n3+n31
  let n33 : ℝ := (n30)⁻¹
  let n34 : ℝ := n32*n33
  exact n34
theorem cosine_eval (q y z : ℝ) : cosineFormula.eval ![q,y,z] = scalarcosine q y z := by
  rfl

noncomputable def scalarsine (_q _y z : ℝ) : ℝ := by
  let n2 : ℝ := z
  let n3 : ℝ := ((1:ℚ):ℝ)
  let n4 : ℝ := ((2:ℚ):ℝ)
  let n29 : ℝ := n2^2
  let n30 : ℝ := n3+n29
  let n33 : ℝ := (n30)⁻¹
  let n35 : ℝ := n4*n2
  let n36 : ℝ := n35*n33
  exact n36
theorem sine_eval (q y z : ℝ) : sineFormula.eval ![q,y,z] = scalarsine q y z := by
  rfl

noncomputable def scalarhOne (q y z : ℝ) : ℝ := by
  let n0 : ℝ := q
  let n1 : ℝ := y
  let n2 : ℝ := z
  let n3 : ℝ := ((1:ℚ):ℝ)
  let n4 : ℝ := ((2:ℚ):ℝ)
  let n6 : ℝ := n1^2
  let n7 : ℝ := -n6
  let n9 : ℝ := n0+n7
  let n10 : ℝ := Real.sqrt n9
  let n22 : ℝ := ((-2:ℚ):ℝ)
  let n29 : ℝ := n2^2
  let n30 : ℝ := n3+n29
  let n31 : ℝ := -n29
  let n32 : ℝ := n3+n31
  let n33 : ℝ := (n30)⁻¹
  let n34 : ℝ := n32*n33
  let n35 : ℝ := n4*n2
  let n36 : ℝ := n35*n33
  let n37 : ℝ := n34*n10
  let n38 : ℝ := n36*n1
  let n39 : ℝ := n37+n38
  let n40 : ℝ := n39+n22
  let n41 : ℝ := -n34
  let n42 : ℝ := n40+n41
  exact n42
theorem hOne_eval (q y z : ℝ) : hOneFormula.eval ![q,y,z] = scalarhOne q y z := by
  rfl

noncomputable def scalarhTwo (q y z : ℝ) : ℝ := by
  let n0 : ℝ := q
  let n1 : ℝ := y
  let n2 : ℝ := z
  let n3 : ℝ := ((1:ℚ):ℝ)
  let n4 : ℝ := ((2:ℚ):ℝ)
  let n11 : ℝ := n1+n4
  let n12 : ℝ := n11^2
  let n13 : ℝ := -n12
  let n14 : ℝ := n0+n13
  let n15 : ℝ := Real.sqrt n14
  let n16 : ℝ := ((-3:ℚ):ℝ)
  let n17 : ℝ := n15+n16
  let n18 : ℝ := n17^2
  let n19 : ℝ := -n18
  let n20 : ℝ := n0+n19
  let n21 : ℝ := Real.sqrt n20
  let n22 : ℝ := ((-2:ℚ):ℝ)
  let n23 : ℝ := n21+n22
  let n24 : ℝ := n23^2
  let n25 : ℝ := -n24
  let n26 : ℝ := n0+n25
  let n27 : ℝ := Real.sqrt n26
  let n28 : ℝ := -n27
  let n29 : ℝ := n2^2
  let n30 : ℝ := n3+n29
  let n31 : ℝ := -n29
  let n32 : ℝ := n3+n31
  let n33 : ℝ := (n30)⁻¹
  let n34 : ℝ := n32*n33
  let n35 : ℝ := n4*n2
  let n36 : ℝ := n35*n33
  let n43 : ℝ := n36*n28
  let n44 : ℝ := -n43
  let n45 : ℝ := n34*n23
  let n46 : ℝ := n44+n45
  let n47 : ℝ := ((-1:ℚ):ℝ)
  let n48 : ℝ := n46+n47
  let n49 : ℝ := -n36
  let n50 : ℝ := n48+n49
  exact n50
theorem hTwo_eval (q y z : ℝ) : hTwoFormula.eval ![q,y,z] = scalarhTwo q y z := by
  rfl

/-- `determinantFormula` is `(F_yy - 1/4)(F_zz - 1/4) - F_yz²`. -/
theorem determinant_eval (env : Fin 3 → ℝ) :
    determinantFormula.eval env =
      (FyyFormula.eval env-1/4)*(FzzFormula.eval env-1/4)-(FyzFormula.eval env)^2 := by
  simp only [determinantFormula,formula258,formula257,formula256,formula255,formula254,
    formula253,formula252,Formula.eval,FyyFormula,FzzFormula,FyzFormula]
  push_cast
  ring

/-- The derivative of `F_z` in `y` has the value of `F_yz`. -/
theorem mixed_partials (env : Fin 3 → ℝ) :
    (FzFormula.diff 1).eval env = FyzFormula.eval env := by
  norm_num [FzFormula,FyzFormula,Formula.diff,Formula.plus,Formula.minus,Formula.times,
    Formula.power,Formula.reciprocal,Formula.quotient,Formula.eval,formula0, formula1, formula2, formula3, formula4, formula6, formula7, formula9, formula10, formula11, formula12, formula13, formula14, formula15, formula16, formula17, formula18, formula19, formula20, formula21, formula22, formula23, formula24, formula25, formula26, formula27, formula28, formula29, formula30, formula31, formula32, formula33, formula34, formula35, formula36, formula37, formula38, formula39, formula40, formula41, formula42, formula43, formula44, formula45, formula46, formula47, formula48, formula49, formula50, formula51, formula52, formula53, formula54, formula55, formula56, formula57, formula58, formula59, formula60, formula61, formula62, formula63, formula64, formula65, formula66, formula67, formula68, formula69, formula70, formula71, formula72, formula73, formula74, formula75, formula76, formula77, formula78, formula79, formula80, formula81, formula82, formula83, formula84, formula85, formula86, formula87, formula88, formula89, formula90, formula91, formula92, formula93, formula94, formula95, formula96, formula97, formula98, formula99, formula100, formula101, formula102, formula103, formula104, formula105, formula106, formula107, formula108, formula109, formula110, formula111, formula112, formula113, formula114, formula115, formula116, formula117, formula118, formula119, formula120, formula121, formula122, formula123, formula124, formula125, formula126, formula127, formula128, formula129, formula130, formula131, formula132, formula133, formula134, formula135, formula136, formula137, formula138, formula139, formula140, formula141, formula142, formula143, formula144, formula145, formula146, formula147, formula148, formula149, formula150, formula151, formula152, formula153, formula154, formula155, formula156, formula157, formula158, formula159, formula160, formula161, formula162, formula163, formula164, formula165, formula166, formula167, formula168, formula169, formula170, formula171, formula172, formula173, formula174, formula175, formula176, formula177, formula178, formula179, formula180, formula181, formula182, formula183, formula184, formula185, formula186, formula187, formula188, formula189, formula190, formula191, formula192, formula193, formula194, formula195, formula196, formula197, formula198, formula199, formula200, formula201, formula202, formula203, formula204, formula205, formula206, formula207, formula208, formula209, formula210, formula211, formula212, formula213, formula214, formula215, formula216, formula217, formula218, formula219, formula220, formula221, formula222, formula223, formula224, formula225, formula226, formula227, formula228, formula229, formula230, formula231, formula232, formula233, formula234, formula235, formula236, formula237, formula238, formula239, formula240, formula241, formula242, formula243, formula244, formula245, formula246, formula247, formula248, formula249, formula250, formula252, formula253, formula254, formula255, formula256, formula257, formula258]
  ring

end SquaresInCircles.Eight.ExactFamily.Generated
