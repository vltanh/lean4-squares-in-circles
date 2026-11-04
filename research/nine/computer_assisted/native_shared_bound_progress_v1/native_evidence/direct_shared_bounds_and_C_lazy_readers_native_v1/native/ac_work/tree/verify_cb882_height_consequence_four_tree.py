#!/usr/bin/env python3
"""Cb882 fixed height tree with two freshly proved whole-original consequences."""
from pathlib import Path
from fractions import Fraction as F
import argparse,json,sys
import verify_cb882_height_four_tree as BASE
import independent_c_height_exclusion_consequences as CONSEQUENCE

_checker=None

class Checker(BASE.Checker):
    def __init__(self):
        global _checker
        super().__init__();self.height_consequence_row_occurrences=0;_checker=self

class Adapter(BASE.Adapter):
    def rebuild(self,state,printed):
        CONSEQUENCE.assert_caller(state,'cb882')
        ordinary=[row for row in printed if not row['name'].startswith(CONSEQUENCE.PREFIX)]
        answer,bounds,physical=super().rebuild(state,ordinary)
        for row in printed:
            if not row['name'].startswith(CONSEQUENCE.PREFIX):continue
            literal=(tuple((i,F(v))for i,v in row['coefficients']),F(row['rhs']),row['name'])
            CONSEQUENCE.verify_literal(literal,state)
            assert row['index']not in answer;answer[row['index']]=literal
            self.checker.height_consequence_row_occurrences+=1
        return answer,bounds,physical

def replay(tree,output):
    tree=Path(tree).resolve();output=Path(output).resolve()
    manifest=json.loads((tree/'manifest.json').read_text())
    assert manifest['whole_original_height_exclusion_consequences']==dict(
        path=str(CONSEQUENCE.BINDING),sha256=CONSEQUENCE.BINDING_SHA,key='cb882')
    source=CONSEQUENCE.replay_source_exclusions('cb882',output.with_name(output.stem+'_HEIGHT_SOURCE'))
    BASE.Checker=Checker;BASE.Adapter=Adapter
    result=BASE.replay(tree,output);assert _checker is not None
    result.update(whole_original_height_exclusion_consequence_source=source,
        height_exclusion_consequence_row_occurrences_checked=_checker.height_consequence_row_occurrences)
    for p in (__file__,CONSEQUENCE.__file__,CONSEQUENCE.BINDING,CONSEQUENCE.LOADER):
        result['checker_dependency_sha256'][str(Path(p).resolve())]=CONSEQUENCE.sha(p)
    CONSEQUENCE.verify_binding()
    assert not any(n in sys.modules for n in ('numpy','scipy','highspy',
        'cb882_height_consequence_four_runtime','c_height_exclusion_consequence_rows'))
    output.write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('tree',type=Path)
    parser.add_argument('output',type=Path);args=parser.parse_args();replay(args.tree,args.output)
