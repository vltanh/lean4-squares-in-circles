#!/usr/bin/env python3
"""Conditional-domain and literal controls for A component-3 root transport."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import json
import a_c744_component3_post_a1_bound_rows as PRODUCER
import independent_a_c744_component3_post_a1_bound_rows as CHECK

def reject(action):
    try:action()
    except (AssertionError,KeyError,ValueError):return
    raise AssertionError('Damaged or wrong-component shared bound was accepted')

def main():
    binding=CHECK.verify_binding()
    consumer=dict(component=3,scope=CHECK.SCOPE,parent=binding['component_parent'],
        conditional_parent=binding['conditional_parent'],closed_domain=binding['closed_domain'])
    positive=damaged=wrong_component=0
    for tail in ([],[['proxy',[0,8],[0,1]],['angle_cut',[4,'0'],0]]):
        state=dict(id=CHECK.TARGET,path=deepcopy(CHECK.ORIGINAL_PATH)+tail)
        rows=PRODUCER.rows(state,3,consumer['closed_domain']);assert len(rows)==414
        for literal in rows:
            CHECK.verify_literal(literal,state,consumer,binding);positive+=1
            co,rhs,name=literal
            for bad in ((co,rhs+F(1,1000000),name),(tuple((i,-v)for i,v in co),rhs,name),
                        (co,rhs,name.replace(CHECK.BINDING_SHA,'0'*64))):
                reject(lambda bad=bad:CHECK.verify_literal(bad,state,consumer,binding));damaged+=1
        literal=rows[0]
        for component in (0,1,2,4):
            invalid=deepcopy(consumer);invalid['component']=component
            reject(lambda:CHECK.verify_literal(literal,state,invalid,binding));wrong_component+=1
            reject(lambda:PRODUCER.rows(state,component,consumer['closed_domain']));wrong_component+=1
        invalid=deepcopy(consumer);invalid['scope']='WHOLE_UNCHANGED_ORIGINAL_PARENT'
        reject(lambda:CHECK.verify_literal(literal,state,invalid,binding));damaged+=1
        invalid=deepcopy(consumer);invalid['parent']['sha256']='0'*64
        reject(lambda:CHECK.verify_literal(literal,state,invalid,binding));damaged+=1
        invalid=deepcopy(consumer);invalid['conditional_parent']['sha256']='0'*64
        reject(lambda:CHECK.verify_literal(literal,state,invalid,binding));damaged+=1
        invalid=deepcopy(consumer);invalid['closed_domain']['rhs']='-1/2'
        reject(lambda:CHECK.verify_literal(literal,state,invalid,binding));damaged+=1
        invalid=deepcopy(consumer);invalid['closed_domain']['name']='two_link_actual_AB_escape_1'
        reject(lambda:CHECK.verify_literal(literal,state,invalid,binding));damaged+=1
        invalid=deepcopy(consumer);invalid['closed_domain']['coefficients'][0][0]=1
        reject(lambda:CHECK.verify_literal(literal,state,invalid,binding));damaged+=1
        wrong=deepcopy(state);wrong['id']='negative-887236b78100baf3'
        reject(lambda:CHECK.verify_literal(literal,wrong,consumer,binding));damaged+=1
        wrong=deepcopy(state);wrong['path'][2][2]=[3]
        reject(lambda:CHECK.verify_literal(literal,wrong,consumer,binding));damaged+=1
    files=[__file__,PRODUCER.__file__,PRODUCER.LITERAL.__file__,CHECK.__file__,CHECK.LITERAL.__file__,CHECK.BINDING]
    report=dict(status='PASS_A_C744_COMPONENT3_POST_A1_CONDITIONAL_BOUND_CONTROLS',
        binding_sha256=CHECK.BINDING_SHA,positive_literals=positive,
        damaged_literal_or_domain_rejections=damaged,wrong_component_producer_or_consumer_rejections=wrong_component,
        exact_component_parent_and_closed_domain_required=True,valid_on_whole_original=False,
        forbidden_consumer_components=[0,1,2,4],source_arithmetic_replay_separate=True,
        files={str(Path(p).resolve()):CHECK.sha(p)for p in files},new_original_cells=0,new_masks=0)
    output=Path(__file__).resolve().parent/'A_C744_COMPONENT3_POST_A1_BOUND_EXACT_CONTROLS.json'
    assert not output.exists()
    output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
