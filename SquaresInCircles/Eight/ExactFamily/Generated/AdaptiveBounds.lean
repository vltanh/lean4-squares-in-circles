module

public import SquaresInCircles.Eight.ExactFamily.Generated.AdaptiveFormula
public import SquaresInCircles.Eight.ExactFamily.FixedEval
public import SquaresInCircles.Eight.ExactFamily.CompactRootCover

/-!
# Uniform estimates along the stationary curve

There are 256 closed boxes but only seven kinds of bound. The strict signs of the derivative at
both ends of the position interval of each box, from which `Adaptive.lean` obtains the adaptive
stationary point, are checked box by box. The other five kinds of estimate are uniform on 32
hulls of 8 consecutive graph boxes each, so they are checked once per hull. Every enclosure is a
fixed-point interval evaluation in the kernel (`FixedEval`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated
open Arithmetic Generated CompactRootCover

set_option maxRecDepth 1000000
set_option linter.all false

/-- Boxes containing 8 consecutive graph boxes each. -/
noncomputable def graphHull : Fin 32 → QBox 3 := ![![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-93576669/100000000),(-93429287/100000000)⟩, ⟨(1/20),(1631/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-46726977/50000000),(-46653339/50000000)⟩, ⟨(1631/32000),(831/16000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-583321/625000),(-9318419/10000000)⟩, ⟨(831/16000),(1693/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-11651111/12500000),(-3722473/4000000)⟩, ⟨(1693/32000),(431/8000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-46543269/50000000),(-92939583/100000000)⟩, ⟨(431/8000),(351/6400)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-92964311/100000000),(-11602183/12500000)⟩, ⟨(351/6400),(893/16000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-2901319/3125000),(-23173867/25000000)⟩, ⟨(893/16000),(1817/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-92720227/100000000),(-23143399/25000000)⟩, ⟨(1817/32000),(231/4000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-92598371/100000000),(-11556481/12500000)⟩, ⟨(231/4000),(1879/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-46238319/50000000),(-3693209/4000000)⟩, ⟨(1879/32000),(191/3200)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-92355031/100000000),(-92208727/100000000)⟩, ⟨(191/3200),(1941/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-23058387/25000000),(-46043677/50000000)⟩, ⟨(1941/32000),(493/8000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-1439253/1562500),(-22991527/25000000)⟩, ⟨(493/8000),(2003/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-91990961/100000000),(-91844987/100000000)⟩, ⟨(2003/32000),(1017/16000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-2870933/3125000),(-91723993/100000000)⟩, ⟨(1017/16000),(413/6400)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-45874439/50000000),(-91603127/100000000)⟩, ⟨(413/6400),(131/2000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-91628027/100000000),(-91482387/100000000)⟩, ⟨(131/2000),(2127/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-11438413/12500000),(-5710111/6250000)⟩, ⟨(2127/32000),(1079/16000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-91386709/100000000),(-91241293/100000000)⟩, ⟨(1079/16000),(2189/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-91266241/100000000),(-45560469/50000000)⟩, ⟨(2189/32000),(111/1600)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-91145903/100000000),(-91000713/100000000)⟩, ⟨(111/1600),(2251/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-45512847/50000000),(-90880617/100000000)⟩, ⟨(2251/32000),(1141/16000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-45452807/50000000),(-1815213/2000000)⟩, ⟨(1141/16000),(2313/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-709263/781250),(-45320407/50000000)⟩, ⟨(2313/32000),(293/4000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-22666461/25000000),(-22630277/25000000)⟩, ⟨(293/4000),(19/256)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-45273077/50000000),(-45200767/50000000)⟩, ⟨(19/256),(1203/16000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-22606649/25000000),(-9028209/10000000)⟩, ⟨(1203/16000),(2437/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-90307169/100000000),(-45081389/50000000)⟩, ⟨(2437/32000),(617/8000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-45093937/50000000),(-90043599/100000000)⟩, ⟨(617/8000),(2499/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-90068711/100000000),(-89924551/100000000)⟩, ⟨(2499/32000),(253/3200)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-1124371/1250000),(-89805637/100000000)⟩, ⟨(253/3200),(2561/32000)⟩],
  ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-44915391/50000000),(-17937371/20000000)⟩, ⟨(2561/32000),(81/1000)⟩]]

/-- The hull of the graph box `i`. -/
noncomputable def hullOf (i : Fin 256) : Fin 32 := ⟨i.val / 8, by omega⟩

/-- The five kinds of graph estimate on a hull. -/
noncomputable def hullCheck (m : Fin 32) : Bool :=
  (List.finRange 9).all (fun j =>
    FixedEval.bounded 100 (graphHull m) (reserveFormula j) (56793/5000000) 2) &&
    (List.finRange 7).all (fun j =>
      FixedEval.bounded 100 (graphHull m) (lambdaFormula j) (1/100) (4209/5000)) &&
    FixedEval.bounded 100 (graphHull m) hTwoFormula (-29/20) (-7/5) &&
    FixedEval.bounded 100 (graphHull m) quadraticFormula 0 (232/25) &&
    FixedEval.bounded 100 (graphHull m) cubicFormula 0 (3/2)

/-- The derivative signs at both ends of the position interval of box `i`, and its hull. -/
noncomputable def cellCheck (i : Fin 256) : Bool :=
  FixedEval.bounded 100 (lowerBoxes i) FyFormula (-1) (-1/1000000) &&
    FixedEval.bounded 100 (upperBoxes i) FyFormula (1/1000000) 1 &&
    inside (graphBoxes i) (graphHull (hullOf i))

theorem hullCheck_0 : hullCheck 0 = true := by decide +kernel
theorem hullCheck_1 : hullCheck 1 = true := by decide +kernel
theorem hullCheck_2 : hullCheck 2 = true := by decide +kernel
theorem hullCheck_3 : hullCheck 3 = true := by decide +kernel
theorem hullCheck_4 : hullCheck 4 = true := by decide +kernel
theorem hullCheck_5 : hullCheck 5 = true := by decide +kernel
theorem hullCheck_6 : hullCheck 6 = true := by decide +kernel
theorem hullCheck_7 : hullCheck 7 = true := by decide +kernel
theorem hullCheck_8 : hullCheck 8 = true := by decide +kernel
theorem hullCheck_9 : hullCheck 9 = true := by decide +kernel
theorem hullCheck_10 : hullCheck 10 = true := by decide +kernel
theorem hullCheck_11 : hullCheck 11 = true := by decide +kernel
theorem hullCheck_12 : hullCheck 12 = true := by decide +kernel
theorem hullCheck_13 : hullCheck 13 = true := by decide +kernel
theorem hullCheck_14 : hullCheck 14 = true := by decide +kernel
theorem hullCheck_15 : hullCheck 15 = true := by decide +kernel
theorem hullCheck_16 : hullCheck 16 = true := by decide +kernel
theorem hullCheck_17 : hullCheck 17 = true := by decide +kernel
theorem hullCheck_18 : hullCheck 18 = true := by decide +kernel
theorem hullCheck_19 : hullCheck 19 = true := by decide +kernel
theorem hullCheck_20 : hullCheck 20 = true := by decide +kernel
theorem hullCheck_21 : hullCheck 21 = true := by decide +kernel
theorem hullCheck_22 : hullCheck 22 = true := by decide +kernel
theorem hullCheck_23 : hullCheck 23 = true := by decide +kernel
theorem hullCheck_24 : hullCheck 24 = true := by decide +kernel
theorem hullCheck_25 : hullCheck 25 = true := by decide +kernel
theorem hullCheck_26 : hullCheck 26 = true := by decide +kernel
theorem hullCheck_27 : hullCheck 27 = true := by decide +kernel
theorem hullCheck_28 : hullCheck 28 = true := by decide +kernel
theorem hullCheck_29 : hullCheck 29 = true := by decide +kernel
theorem hullCheck_30 : hullCheck 30 = true := by decide +kernel
theorem hullCheck_31 : hullCheck 31 = true := by decide +kernel

theorem cellCheck_0 : cellCheck 0 = true := by decide +kernel
theorem cellCheck_1 : cellCheck 1 = true := by decide +kernel
theorem cellCheck_2 : cellCheck 2 = true := by decide +kernel
theorem cellCheck_3 : cellCheck 3 = true := by decide +kernel
theorem cellCheck_4 : cellCheck 4 = true := by decide +kernel
theorem cellCheck_5 : cellCheck 5 = true := by decide +kernel
theorem cellCheck_6 : cellCheck 6 = true := by decide +kernel
theorem cellCheck_7 : cellCheck 7 = true := by decide +kernel
theorem cellCheck_8 : cellCheck 8 = true := by decide +kernel
theorem cellCheck_9 : cellCheck 9 = true := by decide +kernel
theorem cellCheck_10 : cellCheck 10 = true := by decide +kernel
theorem cellCheck_11 : cellCheck 11 = true := by decide +kernel
theorem cellCheck_12 : cellCheck 12 = true := by decide +kernel
theorem cellCheck_13 : cellCheck 13 = true := by decide +kernel
theorem cellCheck_14 : cellCheck 14 = true := by decide +kernel
theorem cellCheck_15 : cellCheck 15 = true := by decide +kernel
theorem cellCheck_16 : cellCheck 16 = true := by decide +kernel
theorem cellCheck_17 : cellCheck 17 = true := by decide +kernel
theorem cellCheck_18 : cellCheck 18 = true := by decide +kernel
theorem cellCheck_19 : cellCheck 19 = true := by decide +kernel
theorem cellCheck_20 : cellCheck 20 = true := by decide +kernel
theorem cellCheck_21 : cellCheck 21 = true := by decide +kernel
theorem cellCheck_22 : cellCheck 22 = true := by decide +kernel
theorem cellCheck_23 : cellCheck 23 = true := by decide +kernel
theorem cellCheck_24 : cellCheck 24 = true := by decide +kernel
theorem cellCheck_25 : cellCheck 25 = true := by decide +kernel
theorem cellCheck_26 : cellCheck 26 = true := by decide +kernel
theorem cellCheck_27 : cellCheck 27 = true := by decide +kernel
theorem cellCheck_28 : cellCheck 28 = true := by decide +kernel
theorem cellCheck_29 : cellCheck 29 = true := by decide +kernel
theorem cellCheck_30 : cellCheck 30 = true := by decide +kernel
theorem cellCheck_31 : cellCheck 31 = true := by decide +kernel
theorem cellCheck_32 : cellCheck 32 = true := by decide +kernel
theorem cellCheck_33 : cellCheck 33 = true := by decide +kernel
theorem cellCheck_34 : cellCheck 34 = true := by decide +kernel
theorem cellCheck_35 : cellCheck 35 = true := by decide +kernel
theorem cellCheck_36 : cellCheck 36 = true := by decide +kernel
theorem cellCheck_37 : cellCheck 37 = true := by decide +kernel
theorem cellCheck_38 : cellCheck 38 = true := by decide +kernel
theorem cellCheck_39 : cellCheck 39 = true := by decide +kernel
theorem cellCheck_40 : cellCheck 40 = true := by decide +kernel
theorem cellCheck_41 : cellCheck 41 = true := by decide +kernel
theorem cellCheck_42 : cellCheck 42 = true := by decide +kernel
theorem cellCheck_43 : cellCheck 43 = true := by decide +kernel
theorem cellCheck_44 : cellCheck 44 = true := by decide +kernel
theorem cellCheck_45 : cellCheck 45 = true := by decide +kernel
theorem cellCheck_46 : cellCheck 46 = true := by decide +kernel
theorem cellCheck_47 : cellCheck 47 = true := by decide +kernel
theorem cellCheck_48 : cellCheck 48 = true := by decide +kernel
theorem cellCheck_49 : cellCheck 49 = true := by decide +kernel
theorem cellCheck_50 : cellCheck 50 = true := by decide +kernel
theorem cellCheck_51 : cellCheck 51 = true := by decide +kernel
theorem cellCheck_52 : cellCheck 52 = true := by decide +kernel
theorem cellCheck_53 : cellCheck 53 = true := by decide +kernel
theorem cellCheck_54 : cellCheck 54 = true := by decide +kernel
theorem cellCheck_55 : cellCheck 55 = true := by decide +kernel
theorem cellCheck_56 : cellCheck 56 = true := by decide +kernel
theorem cellCheck_57 : cellCheck 57 = true := by decide +kernel
theorem cellCheck_58 : cellCheck 58 = true := by decide +kernel
theorem cellCheck_59 : cellCheck 59 = true := by decide +kernel
theorem cellCheck_60 : cellCheck 60 = true := by decide +kernel
theorem cellCheck_61 : cellCheck 61 = true := by decide +kernel
theorem cellCheck_62 : cellCheck 62 = true := by decide +kernel
theorem cellCheck_63 : cellCheck 63 = true := by decide +kernel
theorem cellCheck_64 : cellCheck 64 = true := by decide +kernel
theorem cellCheck_65 : cellCheck 65 = true := by decide +kernel
theorem cellCheck_66 : cellCheck 66 = true := by decide +kernel
theorem cellCheck_67 : cellCheck 67 = true := by decide +kernel
theorem cellCheck_68 : cellCheck 68 = true := by decide +kernel
theorem cellCheck_69 : cellCheck 69 = true := by decide +kernel
theorem cellCheck_70 : cellCheck 70 = true := by decide +kernel
theorem cellCheck_71 : cellCheck 71 = true := by decide +kernel
theorem cellCheck_72 : cellCheck 72 = true := by decide +kernel
theorem cellCheck_73 : cellCheck 73 = true := by decide +kernel
theorem cellCheck_74 : cellCheck 74 = true := by decide +kernel
theorem cellCheck_75 : cellCheck 75 = true := by decide +kernel
theorem cellCheck_76 : cellCheck 76 = true := by decide +kernel
theorem cellCheck_77 : cellCheck 77 = true := by decide +kernel
theorem cellCheck_78 : cellCheck 78 = true := by decide +kernel
theorem cellCheck_79 : cellCheck 79 = true := by decide +kernel
theorem cellCheck_80 : cellCheck 80 = true := by decide +kernel
theorem cellCheck_81 : cellCheck 81 = true := by decide +kernel
theorem cellCheck_82 : cellCheck 82 = true := by decide +kernel
theorem cellCheck_83 : cellCheck 83 = true := by decide +kernel
theorem cellCheck_84 : cellCheck 84 = true := by decide +kernel
theorem cellCheck_85 : cellCheck 85 = true := by decide +kernel
theorem cellCheck_86 : cellCheck 86 = true := by decide +kernel
theorem cellCheck_87 : cellCheck 87 = true := by decide +kernel
theorem cellCheck_88 : cellCheck 88 = true := by decide +kernel
theorem cellCheck_89 : cellCheck 89 = true := by decide +kernel
theorem cellCheck_90 : cellCheck 90 = true := by decide +kernel
theorem cellCheck_91 : cellCheck 91 = true := by decide +kernel
theorem cellCheck_92 : cellCheck 92 = true := by decide +kernel
theorem cellCheck_93 : cellCheck 93 = true := by decide +kernel
theorem cellCheck_94 : cellCheck 94 = true := by decide +kernel
theorem cellCheck_95 : cellCheck 95 = true := by decide +kernel
theorem cellCheck_96 : cellCheck 96 = true := by decide +kernel
theorem cellCheck_97 : cellCheck 97 = true := by decide +kernel
theorem cellCheck_98 : cellCheck 98 = true := by decide +kernel
theorem cellCheck_99 : cellCheck 99 = true := by decide +kernel
theorem cellCheck_100 : cellCheck 100 = true := by decide +kernel
theorem cellCheck_101 : cellCheck 101 = true := by decide +kernel
theorem cellCheck_102 : cellCheck 102 = true := by decide +kernel
theorem cellCheck_103 : cellCheck 103 = true := by decide +kernel
theorem cellCheck_104 : cellCheck 104 = true := by decide +kernel
theorem cellCheck_105 : cellCheck 105 = true := by decide +kernel
theorem cellCheck_106 : cellCheck 106 = true := by decide +kernel
theorem cellCheck_107 : cellCheck 107 = true := by decide +kernel
theorem cellCheck_108 : cellCheck 108 = true := by decide +kernel
theorem cellCheck_109 : cellCheck 109 = true := by decide +kernel
theorem cellCheck_110 : cellCheck 110 = true := by decide +kernel
theorem cellCheck_111 : cellCheck 111 = true := by decide +kernel
theorem cellCheck_112 : cellCheck 112 = true := by decide +kernel
theorem cellCheck_113 : cellCheck 113 = true := by decide +kernel
theorem cellCheck_114 : cellCheck 114 = true := by decide +kernel
theorem cellCheck_115 : cellCheck 115 = true := by decide +kernel
theorem cellCheck_116 : cellCheck 116 = true := by decide +kernel
theorem cellCheck_117 : cellCheck 117 = true := by decide +kernel
theorem cellCheck_118 : cellCheck 118 = true := by decide +kernel
theorem cellCheck_119 : cellCheck 119 = true := by decide +kernel
theorem cellCheck_120 : cellCheck 120 = true := by decide +kernel
theorem cellCheck_121 : cellCheck 121 = true := by decide +kernel
theorem cellCheck_122 : cellCheck 122 = true := by decide +kernel
theorem cellCheck_123 : cellCheck 123 = true := by decide +kernel
theorem cellCheck_124 : cellCheck 124 = true := by decide +kernel
theorem cellCheck_125 : cellCheck 125 = true := by decide +kernel
theorem cellCheck_126 : cellCheck 126 = true := by decide +kernel
theorem cellCheck_127 : cellCheck 127 = true := by decide +kernel
theorem cellCheck_128 : cellCheck 128 = true := by decide +kernel
theorem cellCheck_129 : cellCheck 129 = true := by decide +kernel
theorem cellCheck_130 : cellCheck 130 = true := by decide +kernel
theorem cellCheck_131 : cellCheck 131 = true := by decide +kernel
theorem cellCheck_132 : cellCheck 132 = true := by decide +kernel
theorem cellCheck_133 : cellCheck 133 = true := by decide +kernel
theorem cellCheck_134 : cellCheck 134 = true := by decide +kernel
theorem cellCheck_135 : cellCheck 135 = true := by decide +kernel
theorem cellCheck_136 : cellCheck 136 = true := by decide +kernel
theorem cellCheck_137 : cellCheck 137 = true := by decide +kernel
theorem cellCheck_138 : cellCheck 138 = true := by decide +kernel
theorem cellCheck_139 : cellCheck 139 = true := by decide +kernel
theorem cellCheck_140 : cellCheck 140 = true := by decide +kernel
theorem cellCheck_141 : cellCheck 141 = true := by decide +kernel
theorem cellCheck_142 : cellCheck 142 = true := by decide +kernel
theorem cellCheck_143 : cellCheck 143 = true := by decide +kernel
theorem cellCheck_144 : cellCheck 144 = true := by decide +kernel
theorem cellCheck_145 : cellCheck 145 = true := by decide +kernel
theorem cellCheck_146 : cellCheck 146 = true := by decide +kernel
theorem cellCheck_147 : cellCheck 147 = true := by decide +kernel
theorem cellCheck_148 : cellCheck 148 = true := by decide +kernel
theorem cellCheck_149 : cellCheck 149 = true := by decide +kernel
theorem cellCheck_150 : cellCheck 150 = true := by decide +kernel
theorem cellCheck_151 : cellCheck 151 = true := by decide +kernel
theorem cellCheck_152 : cellCheck 152 = true := by decide +kernel
theorem cellCheck_153 : cellCheck 153 = true := by decide +kernel
theorem cellCheck_154 : cellCheck 154 = true := by decide +kernel
theorem cellCheck_155 : cellCheck 155 = true := by decide +kernel
theorem cellCheck_156 : cellCheck 156 = true := by decide +kernel
theorem cellCheck_157 : cellCheck 157 = true := by decide +kernel
theorem cellCheck_158 : cellCheck 158 = true := by decide +kernel
theorem cellCheck_159 : cellCheck 159 = true := by decide +kernel
theorem cellCheck_160 : cellCheck 160 = true := by decide +kernel
theorem cellCheck_161 : cellCheck 161 = true := by decide +kernel
theorem cellCheck_162 : cellCheck 162 = true := by decide +kernel
theorem cellCheck_163 : cellCheck 163 = true := by decide +kernel
theorem cellCheck_164 : cellCheck 164 = true := by decide +kernel
theorem cellCheck_165 : cellCheck 165 = true := by decide +kernel
theorem cellCheck_166 : cellCheck 166 = true := by decide +kernel
theorem cellCheck_167 : cellCheck 167 = true := by decide +kernel
theorem cellCheck_168 : cellCheck 168 = true := by decide +kernel
theorem cellCheck_169 : cellCheck 169 = true := by decide +kernel
theorem cellCheck_170 : cellCheck 170 = true := by decide +kernel
theorem cellCheck_171 : cellCheck 171 = true := by decide +kernel
theorem cellCheck_172 : cellCheck 172 = true := by decide +kernel
theorem cellCheck_173 : cellCheck 173 = true := by decide +kernel
theorem cellCheck_174 : cellCheck 174 = true := by decide +kernel
theorem cellCheck_175 : cellCheck 175 = true := by decide +kernel
theorem cellCheck_176 : cellCheck 176 = true := by decide +kernel
theorem cellCheck_177 : cellCheck 177 = true := by decide +kernel
theorem cellCheck_178 : cellCheck 178 = true := by decide +kernel
theorem cellCheck_179 : cellCheck 179 = true := by decide +kernel
theorem cellCheck_180 : cellCheck 180 = true := by decide +kernel
theorem cellCheck_181 : cellCheck 181 = true := by decide +kernel
theorem cellCheck_182 : cellCheck 182 = true := by decide +kernel
theorem cellCheck_183 : cellCheck 183 = true := by decide +kernel
theorem cellCheck_184 : cellCheck 184 = true := by decide +kernel
theorem cellCheck_185 : cellCheck 185 = true := by decide +kernel
theorem cellCheck_186 : cellCheck 186 = true := by decide +kernel
theorem cellCheck_187 : cellCheck 187 = true := by decide +kernel
theorem cellCheck_188 : cellCheck 188 = true := by decide +kernel
theorem cellCheck_189 : cellCheck 189 = true := by decide +kernel
theorem cellCheck_190 : cellCheck 190 = true := by decide +kernel
theorem cellCheck_191 : cellCheck 191 = true := by decide +kernel
theorem cellCheck_192 : cellCheck 192 = true := by decide +kernel
theorem cellCheck_193 : cellCheck 193 = true := by decide +kernel
theorem cellCheck_194 : cellCheck 194 = true := by decide +kernel
theorem cellCheck_195 : cellCheck 195 = true := by decide +kernel
theorem cellCheck_196 : cellCheck 196 = true := by decide +kernel
theorem cellCheck_197 : cellCheck 197 = true := by decide +kernel
theorem cellCheck_198 : cellCheck 198 = true := by decide +kernel
theorem cellCheck_199 : cellCheck 199 = true := by decide +kernel
theorem cellCheck_200 : cellCheck 200 = true := by decide +kernel
theorem cellCheck_201 : cellCheck 201 = true := by decide +kernel
theorem cellCheck_202 : cellCheck 202 = true := by decide +kernel
theorem cellCheck_203 : cellCheck 203 = true := by decide +kernel
theorem cellCheck_204 : cellCheck 204 = true := by decide +kernel
theorem cellCheck_205 : cellCheck 205 = true := by decide +kernel
theorem cellCheck_206 : cellCheck 206 = true := by decide +kernel
theorem cellCheck_207 : cellCheck 207 = true := by decide +kernel
theorem cellCheck_208 : cellCheck 208 = true := by decide +kernel
theorem cellCheck_209 : cellCheck 209 = true := by decide +kernel
theorem cellCheck_210 : cellCheck 210 = true := by decide +kernel
theorem cellCheck_211 : cellCheck 211 = true := by decide +kernel
theorem cellCheck_212 : cellCheck 212 = true := by decide +kernel
theorem cellCheck_213 : cellCheck 213 = true := by decide +kernel
theorem cellCheck_214 : cellCheck 214 = true := by decide +kernel
theorem cellCheck_215 : cellCheck 215 = true := by decide +kernel
theorem cellCheck_216 : cellCheck 216 = true := by decide +kernel
theorem cellCheck_217 : cellCheck 217 = true := by decide +kernel
theorem cellCheck_218 : cellCheck 218 = true := by decide +kernel
theorem cellCheck_219 : cellCheck 219 = true := by decide +kernel
theorem cellCheck_220 : cellCheck 220 = true := by decide +kernel
theorem cellCheck_221 : cellCheck 221 = true := by decide +kernel
theorem cellCheck_222 : cellCheck 222 = true := by decide +kernel
theorem cellCheck_223 : cellCheck 223 = true := by decide +kernel
theorem cellCheck_224 : cellCheck 224 = true := by decide +kernel
theorem cellCheck_225 : cellCheck 225 = true := by decide +kernel
theorem cellCheck_226 : cellCheck 226 = true := by decide +kernel
theorem cellCheck_227 : cellCheck 227 = true := by decide +kernel
theorem cellCheck_228 : cellCheck 228 = true := by decide +kernel
theorem cellCheck_229 : cellCheck 229 = true := by decide +kernel
theorem cellCheck_230 : cellCheck 230 = true := by decide +kernel
theorem cellCheck_231 : cellCheck 231 = true := by decide +kernel
theorem cellCheck_232 : cellCheck 232 = true := by decide +kernel
theorem cellCheck_233 : cellCheck 233 = true := by decide +kernel
theorem cellCheck_234 : cellCheck 234 = true := by decide +kernel
theorem cellCheck_235 : cellCheck 235 = true := by decide +kernel
theorem cellCheck_236 : cellCheck 236 = true := by decide +kernel
theorem cellCheck_237 : cellCheck 237 = true := by decide +kernel
theorem cellCheck_238 : cellCheck 238 = true := by decide +kernel
theorem cellCheck_239 : cellCheck 239 = true := by decide +kernel
theorem cellCheck_240 : cellCheck 240 = true := by decide +kernel
theorem cellCheck_241 : cellCheck 241 = true := by decide +kernel
theorem cellCheck_242 : cellCheck 242 = true := by decide +kernel
theorem cellCheck_243 : cellCheck 243 = true := by decide +kernel
theorem cellCheck_244 : cellCheck 244 = true := by decide +kernel
theorem cellCheck_245 : cellCheck 245 = true := by decide +kernel
theorem cellCheck_246 : cellCheck 246 = true := by decide +kernel
theorem cellCheck_247 : cellCheck 247 = true := by decide +kernel
theorem cellCheck_248 : cellCheck 248 = true := by decide +kernel
theorem cellCheck_249 : cellCheck 249 = true := by decide +kernel
theorem cellCheck_250 : cellCheck 250 = true := by decide +kernel
theorem cellCheck_251 : cellCheck 251 = true := by decide +kernel
theorem cellCheck_252 : cellCheck 252 = true := by decide +kernel
theorem cellCheck_253 : cellCheck 253 = true := by decide +kernel
theorem cellCheck_254 : cellCheck 254 = true := by decide +kernel
theorem cellCheck_255 : cellCheck 255 = true := by decide +kernel

theorem hullCheck_all : ∀ m : Fin 32, hullCheck m = true := by
  intro m
  fin_cases m
  exacts [
    hullCheck_0, hullCheck_1, hullCheck_2, hullCheck_3, hullCheck_4, hullCheck_5, hullCheck_6,
    hullCheck_7, hullCheck_8, hullCheck_9, hullCheck_10, hullCheck_11, hullCheck_12, hullCheck_13,
    hullCheck_14, hullCheck_15, hullCheck_16, hullCheck_17, hullCheck_18, hullCheck_19,
    hullCheck_20, hullCheck_21, hullCheck_22, hullCheck_23, hullCheck_24, hullCheck_25,
    hullCheck_26, hullCheck_27, hullCheck_28, hullCheck_29, hullCheck_30, hullCheck_31]

theorem cellCheck_all : ∀ i : Fin 256, cellCheck i = true := by
  intro i
  fin_cases i
  exacts [
    cellCheck_0, cellCheck_1, cellCheck_2, cellCheck_3, cellCheck_4, cellCheck_5, cellCheck_6,
    cellCheck_7, cellCheck_8, cellCheck_9, cellCheck_10, cellCheck_11, cellCheck_12, cellCheck_13,
    cellCheck_14, cellCheck_15, cellCheck_16, cellCheck_17, cellCheck_18, cellCheck_19,
    cellCheck_20, cellCheck_21, cellCheck_22, cellCheck_23, cellCheck_24, cellCheck_25,
    cellCheck_26, cellCheck_27, cellCheck_28, cellCheck_29, cellCheck_30, cellCheck_31,
    cellCheck_32, cellCheck_33, cellCheck_34, cellCheck_35, cellCheck_36, cellCheck_37,
    cellCheck_38, cellCheck_39, cellCheck_40, cellCheck_41, cellCheck_42, cellCheck_43,
    cellCheck_44, cellCheck_45, cellCheck_46, cellCheck_47, cellCheck_48, cellCheck_49,
    cellCheck_50, cellCheck_51, cellCheck_52, cellCheck_53, cellCheck_54, cellCheck_55,
    cellCheck_56, cellCheck_57, cellCheck_58, cellCheck_59, cellCheck_60, cellCheck_61,
    cellCheck_62, cellCheck_63, cellCheck_64, cellCheck_65, cellCheck_66, cellCheck_67,
    cellCheck_68, cellCheck_69, cellCheck_70, cellCheck_71, cellCheck_72, cellCheck_73,
    cellCheck_74, cellCheck_75, cellCheck_76, cellCheck_77, cellCheck_78, cellCheck_79,
    cellCheck_80, cellCheck_81, cellCheck_82, cellCheck_83, cellCheck_84, cellCheck_85,
    cellCheck_86, cellCheck_87, cellCheck_88, cellCheck_89, cellCheck_90, cellCheck_91,
    cellCheck_92, cellCheck_93, cellCheck_94, cellCheck_95, cellCheck_96, cellCheck_97,
    cellCheck_98, cellCheck_99, cellCheck_100, cellCheck_101, cellCheck_102, cellCheck_103,
    cellCheck_104, cellCheck_105, cellCheck_106, cellCheck_107, cellCheck_108, cellCheck_109,
    cellCheck_110, cellCheck_111, cellCheck_112, cellCheck_113, cellCheck_114, cellCheck_115,
    cellCheck_116, cellCheck_117, cellCheck_118, cellCheck_119, cellCheck_120, cellCheck_121,
    cellCheck_122, cellCheck_123, cellCheck_124, cellCheck_125, cellCheck_126, cellCheck_127,
    cellCheck_128, cellCheck_129, cellCheck_130, cellCheck_131, cellCheck_132, cellCheck_133,
    cellCheck_134, cellCheck_135, cellCheck_136, cellCheck_137, cellCheck_138, cellCheck_139,
    cellCheck_140, cellCheck_141, cellCheck_142, cellCheck_143, cellCheck_144, cellCheck_145,
    cellCheck_146, cellCheck_147, cellCheck_148, cellCheck_149, cellCheck_150, cellCheck_151,
    cellCheck_152, cellCheck_153, cellCheck_154, cellCheck_155, cellCheck_156, cellCheck_157,
    cellCheck_158, cellCheck_159, cellCheck_160, cellCheck_161, cellCheck_162, cellCheck_163,
    cellCheck_164, cellCheck_165, cellCheck_166, cellCheck_167, cellCheck_168, cellCheck_169,
    cellCheck_170, cellCheck_171, cellCheck_172, cellCheck_173, cellCheck_174, cellCheck_175,
    cellCheck_176, cellCheck_177, cellCheck_178, cellCheck_179, cellCheck_180, cellCheck_181,
    cellCheck_182, cellCheck_183, cellCheck_184, cellCheck_185, cellCheck_186, cellCheck_187,
    cellCheck_188, cellCheck_189, cellCheck_190, cellCheck_191, cellCheck_192, cellCheck_193,
    cellCheck_194, cellCheck_195, cellCheck_196, cellCheck_197, cellCheck_198, cellCheck_199,
    cellCheck_200, cellCheck_201, cellCheck_202, cellCheck_203, cellCheck_204, cellCheck_205,
    cellCheck_206, cellCheck_207, cellCheck_208, cellCheck_209, cellCheck_210, cellCheck_211,
    cellCheck_212, cellCheck_213, cellCheck_214, cellCheck_215, cellCheck_216, cellCheck_217,
    cellCheck_218, cellCheck_219, cellCheck_220, cellCheck_221, cellCheck_222, cellCheck_223,
    cellCheck_224, cellCheck_225, cellCheck_226, cellCheck_227, cellCheck_228, cellCheck_229,
    cellCheck_230, cellCheck_231, cellCheck_232, cellCheck_233, cellCheck_234, cellCheck_235,
    cellCheck_236, cellCheck_237, cellCheck_238, cellCheck_239, cellCheck_240, cellCheck_241,
    cellCheck_242, cellCheck_243, cellCheck_244, cellCheck_245, cellCheck_246, cellCheck_247,
    cellCheck_248, cellCheck_249, cellCheck_250, cellCheck_251, cellCheck_252, cellCheck_253,
    cellCheck_254, cellCheck_255]

theorem hull_mem (i : Fin 256) {env : Fin 3 → ℝ} (he : (graphBoxes i).Mem env) :
    (graphHull (hullOf i)).Mem env := by
  have h := cellCheck_all i
  simp only [cellCheck, Bool.and_eq_true] at h
  exact box_mem_of_subset (by simpa [inside] using h.2) he

theorem hull_bounds {m : Fin 32} {env : Fin 3 → ℝ} (he : (graphHull m).Mem env) :
    (∀ j : Fin 9, (((56793/5000000 : ℚ)) : ℝ) ≤ (reserveFormula j).eval env) ∧
    (∀ j : Fin 7, (lambdaFormula j).eval env ≤ (((4209/5000 : ℚ)) : ℝ)) ∧
    (((-29/20 : ℚ)) : ℝ) ≤ hTwoFormula.eval env ∧
    hTwoFormula.eval env ≤ (((-7/5 : ℚ)) : ℝ) ∧
    quadraticFormula.eval env ≤ (((232/25 : ℚ)) : ℝ) ∧
    cubicFormula.eval env ≤ (((3/2 : ℚ)) : ℝ) := by
  have h := hullCheck_all m
  simp only [hullCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨fun j => (FixedEval.bounded_sound (h1 j) he).1,
    fun j => (FixedEval.bounded_sound (h2 j) he).2, (FixedEval.bounded_sound h3 he).1,
    (FixedEval.bounded_sound h3 he).2, (FixedEval.bounded_sound h4 he).2,
    (FixedEval.bounded_sound h5 he).2⟩

theorem lower_sign (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (lowerBoxes i).Mem env) : FyFormula.eval env < 0 := by
  have h := cellCheck_all i
  simp only [cellCheck, Bool.and_eq_true] at h
  have hb := (FixedEval.bounded_sound h.1.1 he).2
  push_cast at hb
  linarith

theorem upper_sign (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (upperBoxes i).Mem env) : 0 < FyFormula.eval env := by
  have h := cellCheck_all i
  simp only [cellCheck, Bool.and_eq_true] at h
  have hb := (FixedEval.bounded_sound h.1.2 he).1
  push_cast at hb
  linarith

theorem reserve_bound (i : Fin 256) (j : Fin 9) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) :
    (56793/5000000 : ℝ) ≤ (reserveFormula j).eval env := by
  have h := (hull_bounds (hull_mem i he)).1 j
  push_cast at h
  exact h

theorem weight_bound (i : Fin 256) (j : Fin 7) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) :
    (lambdaFormula j).eval env ≤ 4209/5000 := by
  have h := (hull_bounds (hull_mem i he)).2.1 j
  push_cast at h
  exact h

theorem hTwo_bound (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) :
    -(29/20:ℝ) ≤ hTwoFormula.eval env ∧ hTwoFormula.eval env ≤ -(7/5) := by
  have h := hull_bounds (hull_mem i he)
  have h1 := h.2.2.1
  have h2 := h.2.2.2.1
  push_cast at h1 h2
  constructor <;> linarith

theorem quadratic_bound (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) : quadraticFormula.eval env ≤ 232/25 := by
  have h := (hull_bounds (hull_mem i he)).2.2.2.2.1
  push_cast at h
  exact h

theorem cubic_bound (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) : cubicFormula.eval env ≤ 3/2 := by
  have h := (hull_bounds (hull_mem i he)).2.2.2.2.2
  push_cast at h
  exact h

end SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated
