#!/usr/bin/env python3
"""Independent exact A3 adapter for the published relative-support chord family."""
from pathlib import Path
from fractions import Fraction as F
import argparse,json,sys
import verify_conditional_a3_cone_incircle_tree as BASE
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'relative_support_chords_v1'))
import independent_relative_support_chords as RELATIVE

class Checker(BASE.Checker):
    def __init__(self):
        super().__init__()
        self.relative_support_chord_rows_checked=0

class Adapter(BASE.Adapter):
    def rebuild(self,state,printed):
        ordinary=[r for r in printed if not r['name'].startswith(RELATIVE.PREFIX)]
        answer,bounds,physical=super().rebuild(state,ordinary)
        for r in printed:
            if not r['name'].startswith(RELATIVE.PREFIX):continue
            literal=(tuple((i,F(v))for i,v in r['coefficients']),F(r['rhs']),r['name'])
            RELATIVE.verify_literal(literal,physical['scalar'],physical['differences'])
            assert r['index'] not in answer
            answer[r['index']]=literal
            self.checker.relative_support_chord_rows_checked+=1
        return answer,bounds,physical

def replay(tree,output):
    tree=Path(tree).resolve();output=Path(output).resolve()
    manifest=json.loads((tree/'manifest.json').read_text())
    assert manifest['stronger_scope']['relative_support_chords']==dict(signed=True,folded=True,support_upper='121/100',new_case_premise=False)
    BASE.Checker,BASE.Adapter=Checker,Adapter
    result=BASE.replay(tree,output)
    checker=BASE.BASE.BASE._checker
    result['relative_support_chord_rows_checked']=checker.relative_support_chord_rows_checked
    for p in(__file__,RELATIVE.__file__,HERE/'relative_support_chords_v1/INDEPENDENT_REVIEW.md',HERE/'relative_support_chords_v1/OWNER_FREE_RELATIVE_SUPPORT_HAND_PROOF.md'):
        result['checker_dependency_sha256'][str(Path(p).resolve())]=BASE.BASE.BASE.sha(p)
    assert not any(n in sys.modules for n in('physical_relative_support_chords','owner_free_relative_support_snapshot'))
    output.write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('tree',type=Path);ap.add_argument('output',type=Path);a=ap.parse_args()
    replay(a.tree,a.output)
