#!/usr/bin/env python3
"""Emit n=8 closed-domain word proof scripts, schema n8-word-box-script-v1.

The geometric expressions and exact role labels are in WordProblems.lean.
This generator enumerates the retained increment/branch/sign/axis cases
and writes ordinary Lean `by decide` bodies for the depth-96 compiler.
It neither invokes Lean nor evaluates those decisions or a historical checker.
Common core/core cases are proved by CoreWordGeometry and are omitted.
The four geometric CoreSeparatorExcluded classes are also omitted.
"""
from pathlib import Path
root = Path(__file__).resolve().parents[2]
# Separate per-case theorem declarations: later compiler evaluation is deliberately deferred.
g='''module

public import SquaresInCircles.Eight.Arithmetic.WordProblems

/-!
# Whole-domain finite proof scripts for the six excluded words

These are complete rational closed-box decisions, with their continuous
meaning supplied by `RealBox.certify_sound`. They are deliberately left
uncompiled and unevaluated in this draft. No external Boolean report,
opaque arithmetic record, or numerical optimizer is consumed here.

Each statement carries the actual branch/sign/axis expression. A failed
leaf will make its `by decide` proof fail during the later requested audit.
The common core/core block has been removed: WordGeometry supplies its
whole-domain geometric proof before calling the retained dispatcher.
Both dispatchers also omit the four impossible core separator classes;
WordGeometry proves this exclusion for every actual feasible axis.
-/

@[expose] public section
namespace SquaresInCircles.Eight.WordProblems
open Arithmetic.RealBox
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
'''
# Individual source-axis and radial/sign statements keep elaboration names reviewable.
rad=['outer','coreSide','coreCorner']
def core_separator_excluded(k,a,b,si,ti,ax):
 return ((k==0 and ((ax==1 and b!='outer') or (ax==3 and a!='outer'))) or
         (ax==0 and not si and b!='outer') or
         (ax==2 and ti and a!='outer'))
common_count=0
for k in range(3):
 for a in rad:
  for b in rad:
   if a!='outer' and b!='outer':continue
   for si in [False,True]:
    for ti in [False,True]:
     for ax in range(4):
      if core_separator_excluded(k,a,b,si,ti,ax):continue
      common_count+=1
      S=str(si).lower();T=str(ti).lower()
      g+=f'theorem common_{k}_{a}_{b}_{int(si)}{int(ti)}_{ax} :\n    certify 96 (commonProblem {k} .{a} .{b} {S} {T} {ax}) (pairBox .{a} .{b})=true := by decide\n'
g+='''
theorem common_certificates (k : Fin 3) (source target : RadialKind)
    (σ τ : Bool) (axis : Fin 4) (houter : source=.outer ∨ target=.outer)
    (hkeep : ¬ CoreSeparatorExcluded k source target σ τ axis) :
    certify 96 (commonProblem k source target σ τ axis) (pairBox source target)=true := by
  fin_cases k <;> cases source <;> cases target <;> cases σ <;> cases τ <;> fin_cases axis
  all_goals first
  | solve | simp at houter
  | solve | simp [CoreSeparatorExcluded] at hkeep
'''
for k in range(3):
 for a in rad:
  for b in rad:
   if a!='outer' and b!='outer':continue
   for si in [False,True]:
    for ti in [False,True]:
     for ax in range(4):
      if core_separator_excluded(k,a,b,si,ti,ax):continue
      g+=f'  | exact common_{k}_{a}_{b}_{int(si)}{int(ti)}_{ax}\n'
words={'short':[0,0,1,0,1,1,1],'second':[0,0,1,1,0,1,1]}
case_names=[]
for w,word in words.items():
 for i in range(7):
  for si in [False,True]:
   for ti in [False,True]:
    if (i==0 and not si) or (i==2 and si) or ((i+1)%7==0 and not ti) or ((i+1)%7==2 and ti) or (word[i]==0 and not si and ti):continue
    for a in rad:
     for b in rad:
      for ax in range(4):
       if core_separator_excluded(word[i],a,b,si,ti,ax):continue
       name=f'{w}_{i}_{a}_{b}_{int(si)}{int(ti)}_{ax}';case_names.append(name)
       S=str(si).lower();T=str(ti).lower()
       g+=f'theorem {name} :\n    certify 96 (wrongProblem .{w} {i} .{a} .{b} {S} {T} {ax}) (pairBox .{a} .{b})=true := by decide\n'
g+='''
theorem wrong_certificates (w : WrongWord) (i : Vertex) (source target : RadialKind)
    (σ τ : Bool) (axis : Fin 4) (hallowed : allowed w i σ τ)
    (hkeep : ¬ CoreSeparatorExcluded (wrongWord w i) source target σ τ axis) :
    certify 96 (wrongProblem w i source target σ τ axis) (pairBox source target)=true := by
  cases w <;> fin_cases i <;> cases source <;> cases target <;> cases σ <;> cases τ <;> fin_cases axis
  all_goals first
  | contradiction
  | solve | simp [allowed,wrongWord,next] at hallowed
  | solve | simp [CoreSeparatorExcluded,wrongWord] at hkeep
'''
for name in case_names:g+=f'  | exact {name}\n'
g+='\nend SquaresInCircles.Eight.WordProblems\n'
(root/'SquaresInCircles/Eight/Generated/WordCertificates.lean').write_text(g)
print('Wrote WordCertificates.lean:',common_count+len(case_names),
      'finite proof scripts;',1800-common_count-len(case_names),
      'original cases removed by geometry; no decision evaluated.')
