#!/usr/bin/env python3
"""Exact Cb882 height tree with freshly replayed whole-original bounds."""
from pathlib import Path
from fractions import Fraction as F
import argparse,json,sys
HERE=Path(__file__).resolve().parent
AC=HERE.parents[1]/'ac_work/tree'
sys.path.insert(0,str(AC))
import verify_cb882_height_consequence_four_tree as BASE
import independent_cb882_whole_height_bound_rows as ROWS

_configuration=None
_checker=None

class Checker(BASE.Checker):
    def __init__(self):
        global _checker
        super().__init__();assert _configuration is not None
        self.whole_height_bound_binding=_configuration
        self.whole_height_bound_row_occurrences=0;_checker=self

class Adapter(BASE.Adapter):
    def rebuild(self,state,printed):
        ROWS.assert_caller(state)
        ordinary=[row for row in printed if not row['name'].startswith(ROWS.PREFIX)]
        answer,bounds,physical=super().rebuild(state,ordinary)
        for row in printed:
            if not row['name'].startswith(ROWS.PREFIX):continue
            literal=(tuple((i,F(v))for i,v in row['coefficients']),F(row['rhs']),row['name'])
            ROWS.verify_literal(literal,state,self.checker.whole_height_bound_binding)
            assert row['index']not in answer;answer[row['index']]=literal
            self.checker.whole_height_bound_row_occurrences+=1
        return answer,bounds,physical

def replay(tree,output):
    global _configuration
    tree=Path(tree).resolve();output=Path(output).resolve()
    manifest=json.loads((tree/'manifest.json').read_text())
    assert manifest['whole_original_height_bound_state']==dict(path=str(ROWS.BINDING),sha256=ROWS.BINDING_SHA)
    source,_configuration=ROWS.replay_source(output.with_name(output.stem+'_WHOLE_ROOT_SOURCE'))
    BASE.Checker=Checker;BASE.Adapter=Adapter
    result=BASE.replay(tree,output);assert _checker is not None
    result.update(fresh_whole_original_height_bound_state=source,
        whole_original_height_bound_state_row_occurrences_checked=_checker.whole_height_bound_row_occurrences)
    for path in (__file__,ROWS.__file__,ROWS.BINDING,ROWS.LITERAL.__file__):
        result['checker_dependency_sha256'][str(Path(path).resolve())]=ROWS.sha(path)
    ROWS.verify_binding()
    assert not any(n in sys.modules for n in ('numpy','scipy','highspy',
        'cb882_shared_height_bounds_runtime','cb882_whole_height_bound_rows'))
    output.write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('tree',type=Path)
    parser.add_argument('output',type=Path);args=parser.parse_args();replay(args.tree,args.output)
