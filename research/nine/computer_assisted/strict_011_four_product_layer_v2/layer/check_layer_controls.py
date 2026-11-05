#!/usr/bin/env python3
"""Fresh same-state, literal and residual controls without numerical solves."""
if not __debug__:
    raise RuntimeError('Exact layer controls reject optimized Python.')
import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import strict011_four_product_rows as P
import independent_strict011_four_product as I
import suggest_four_product_parameters as N
import layer_dependencies as D

def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def printed(rows):
    return [dict(index=k,name=name,coefficients=[[j,str(v)]for j,v in co],rhs=str(rhs))
            for k,(co,rhs,name)in enumerate(rows)]
def halfangle_frame(t):
    t=F(t);a=(1-t*t)/(1+t*t);b=2*t/(1+t*t)
    assert a*a+b*b==1 and a>=abs(b)
    return a,b
def frame_point(current,halfangle,side,representative):
    coordinates=[interval[side] if side in (0,1) else sum(interval)/2 for interval in current['positions']]
    frames=[halfangle_frame(abs(halfangle)if representative and i==3 else halfangle)for i in range(9)]
    values=coordinates+[a for a,b in frames]+[b for a,b in frames]
    values += [abs(b)for a,b in frames]+[1/(2*(a+abs(b)))for a,b in frames]
    for value,interval in zip(values,current['positions']+current['scalar']):
        assert interval[0]<=value<=interval[1]
    return values
def residual(row,current,values):
    co,rhs,name=row;fields=name[len('physical_unit_four_corner_'):].split('_')
    i,e,t=map(int,fields[:3]);px,py=map(F,fields[3:5]);bits=tuple(map(int,fields[5:]))
    x,y,a,b=values[2*i],values[2*i+1],values[18+i],values[27+i]
    assert a*a+b*b==1
    corner=(x+(e*a-t*b)/2)**2+(y+(e*b+t*a)/2)**2
    factors=[(a,e*x),(a,t*y),(b,e*y),(b,-t*x)]
    boxes=[(current['scalar'][i],tuple(sorted(e*z for z in current['positions'][2*i]))),
           (current['scalar'][i],tuple(sorted(t*z for z in current['positions'][2*i+1]))),
           (current['scalar'][9+i],tuple(sorted(e*z for z in current['positions'][2*i+1]))),
           (current['scalar'][9+i],tuple(sorted(-t*z for z in current['positions'][2*i])))]
    products=[]
    for (f,g),(fb,gb),side in zip(factors,boxes,bits):
        assert fb[0]<=f<=fb[1] and gb[0]<=g<=gb[1]
        products.append((f-fb[side])*(g-gb[side]))
    assert min(products)>=0
    slack=F(rhs)-sum(value*values[column]for column,value in co)
    total=F(1105,256)-corner+(x-px)**2+(y-py)**2+sum(products)
    assert slack==total
    if corner<=F(1105,256):assert slack>=0
    return corner<=F(1105,256)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--foundation',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    foundation=args.foundation.resolve();assert not args.output.exists()
    family=D.verify_family();base=D.verify_foundation(foundation)
    files=['layer_dependencies.py','strict011_four_product_rows.py','independent_strict011_four_product.py',
           'suggest_four_product_parameters.py','check_layer_controls.py','SAME_STATE_PHYSICAL_ATTACHMENT.md']
    sources={name:digest(HERE/name)for name in files}
    G=D.load('corner_layer_frozen_generic',foundation/'dependencies/workspace/b_work/independent_physical_sat_replay.py')
    assert digest(G.__file__)=='1d069c90f289dce136e41afeb5d564ec7016ac06f58eeb733ca7552801b6fafc'
    old=D.load('corner_layer_accepted_grouped',HERE/'accepted/accepted_grouped/physical_unit_corner_rows.py')
    counts=dict(contexts=0,additional_rows=0,ordinary_rows=0,physical_residuals=0,
        contained_corner_evaluations=0,grouped_rows_reproduced=0,
        mixed_SAT_auxiliary_contexts=0,synthetic_weighted_rounds=0,
        synthetic_positive_corner_weight_uses=0,parameter_rebuilds=0,numeric_suggestions_checked=0)
    rejected=[];examples=[];callers=[]
    def reject(name,callback):
        try:callback()
        except (AssertionError,ValueError,KeyError,TypeError,IndexError):rejected.append(name)
        else:raise AssertionError('Damaged control accepted: '+name)
    for representative,folder in ((False,'strict_011_full_root_v2'),(True,'strict_011_representative_root_v1')):
        document=json.loads((foundation/folder/'snapshots/ROOT_DOCUMENT.json').read_text())
        context=P.Context(foundation,document);adapter=I.Adapter(foundation,document)
        root=adapter.verify_root(document)
        assert root==context.model.fresh_state()
        states=[('root',root)]
        selected=context.model.physical_child(root,'sat',(0,8),(8,1,-1))
        states.append(('selected_sat',selected))
        narrow=deepcopy(selected)
        narrow['angles']=tuple((F(0),F(1,2))if representative and i==3 else(F(-1,2),F(1,2))for i in range(9))
        narrow['positions']=tuple((F(-1,2)+F(i%3,6),F(1,2)+F(i%3,6))for i in range(18))
        states.append(('narrowed',narrow))
        grouped_sample={}
        for label,state in states:
            raw_rows,raw_bounds,raw_current,raw_terminal=context.model.collect(state)
            rows,bounds,current,terminal=context.collect(state,seed_midpoints=True)
            assert terminal is raw_terminal is None and bounds==raw_bounds and current==raw_current
            assert rows[:len(raw_rows)]==raw_rows and len(rows)==len(raw_rows)+576
            # The ordinary adapter and accepted extra decoder each see exactly
            # the same current positions/scalars and the same SAT auxiliaries.
            literals=printed(rows)
            rebuilt,checked_bounds,checked_current=adapter.rebuild(state,literals)
            assert rebuilt==dict(enumerate(rows))and checked_bounds==bounds and checked_current==current
            counts['contexts']+=1;counts['ordinary_rows']+=len(raw_rows);counts['additional_rows']+=576
            if label!='root':assert len(bounds)==60;counts['mixed_SAT_auxiliary_contexts']+=1
            else:assert len(bounds)==54
            extras=rows[len(raw_rows):]
            for halfangle,side in product((F(-1,5),F(0),F(1,5)),(0,1,2)):
                values=frame_point(current,halfangle,side,representative)
                for row in extras:
                    counts['contained_corner_evaluations']+=int(residual(row,current,values))
                    counts['physical_residuals']+=1
            for i,e,t in product(range(9),(-1,1),(-1,1)):
                px=sum(current['positions'][2*i])/2;py=sum(current['positions'][2*i+1])/2
                for a,b in product((0,1),repeat=2):
                    parent=old.row(current['positions'],current['scalar'],i,e,t,px,py,a,b)
                    child=context.row_on_current(current,(i,e,t,px,py,(a,a,b,b)))
                    assert parent[:2]==child[:2];counts['grouped_rows_reproduced']+=1
            params=(4,1,-1,F(2,7),F(-3,11),(0,1,1,0))
            newrow=context.row_on_current(current,params)
            fresh,bb,cc,tt=context.collect(state,[params,params])
            assert fresh==raw_rows+[newrow]and bb==bounds and cc==current and tt is None
            adapter.rebuild(state,[dict(index=999999,name=newrow[2],coefficients=[[k,str(v)]for k,v in newrow[0]],rhs=str(newrow[1]))])
            counts['parameter_rebuilds']+=1

            # One positive, explicitly synthetic corner weight, with all exact
            # residuals paid, exercises the unchanged generic arithmetic core.
            chosen=extras[0]
            row_literal=dict(index=0,name=chosen[2],coefficients=[[k,str(v)]for k,v in chosen[0]],rhs=str(chosen[1]))
            co=[F(0)]*len(bounds)
            for column,value in chosen[0]:co[column]+=value
            co[45]-=1
            correction=sum(b*abs(c)for b,c in zip(bounds,co));proved=chosen[1]+correction
            upper=G.ceiling_grid(proved)
            after=deepcopy(current);scalar=[list(ab)for ab in current['scalar']]
            scalar[27][1]=min(scalar[27][1],upper);after['scalar']=tuple(map(tuple,scalar))
            assert scalar[27][0]<=scalar[27][1]
            proposal=dict(kind='scalar',key=45,sign=1,objective=[[45,1]],weights=[[0,G.DENOMINATOR]],
                summed_rhs=str(chosen[1]),residual_coefficients=[[k,str(v)]for k,v in enumerate(co)if v],
                residual_correction=str(correction),proved_upper=str(proved),upper=str(upper))
            round_record=dict(before=G.state_view(state),printed_rows=[row_literal],propagated=G.state_view(current),
                absolute_variable_bounds=list(map(str,bounds)),proposals=[proposal],
                physical_frame_inferences=[],after=G.state_view(after))
            record=dict(initial=G.state_view(state),rounds=[round_record],status='OPEN',final=G.state_view(after))
            audit,final=G.check_record(record,state,adapter)
            assert final==after and audit['deductions']==audit['printed_rows_checked']==1
            counts['synthetic_weighted_rounds']+=1;counts['synthetic_positive_corner_weight_uses']+=1
            for key,value in (('residual_correction','0'),('upper','-1')):
                bad=deepcopy(record);bad['rounds'][0]['proposals'][0][key]=value
                assert bad!=record
                reject(folder+':'+label+':weighted:'+key,lambda bad=bad:G.check_record(bad,state,adapter))

            for field in ('coefficient','rhs','auxiliary','name','duplicate_index','unknown_prefix'):
                bad=deepcopy(literals)
                index=len(raw_rows)
                if field=='coefficient':bad[index]['coefficients'][0][1]=str(F(bad[index]['coefficients'][0][1])+1)
                elif field=='rhs':bad[index]['rhs']=str(F(bad[index]['rhs'])-F(1,100))
                elif field=='auxiliary':bad[index]['coefficients'].append([54,'1'])
                elif field=='name':bad[index]['name']=bad[index]['name'].rsplit('_',1)[0]+'_2'
                elif field=='duplicate_index':bad[index]['index']=bad[0]['index']
                else:bad[index]['name']='unproved_corner_'+bad[index]['name']
                reject(folder+':'+label+':literal:'+field,lambda bad=bad:adapter.rebuild(state,bad))
            grouped_sample[label]=(state,current,literals[len(raw_rows)])

            # Deliberately infeasible diagnostics can suggest useful valid
            # planes; no feasibility or proof status is attached to the point.
            values=[float(sum(interval)/2)for interval in current['positions']+current['scalar']]
            values[0]=2.0;values[1]=2.0
            suggestions=N.suggest(values,current,context)
            assert suggestions
            for parameters,violation in suggestions:
                row=context.row_on_current(current,parameters)
                assert violation>0
                lit=dict(index=0,name=row[2],coefficients=[[k,str(v)]for k,v in row[0]],rhs=str(row[1]))
                adapter.rebuild(state,[lit]);counts['numeric_suggestions_checked']+=1
            for invalid in (float('nan'),float('inf')):
                bad=list(values);bad[0]=invalid
                reject(folder+':'+label+':nonfinite',lambda bad=bad:N.suggest(bad,current,context))

        for old_label,new_label in (('root','narrowed'),('narrowed','root')):
            _,_,stale=grouped_sample[old_label]
            target,_,fresh=grouped_sample[new_label]
            assert stale!=fresh
            reject(folder+':stale:'+old_label+'->'+new_label,lambda stale=stale,target=target:adapter.rebuild(target,[stale]))
        for field,value in (('mask','001/00'),('radius_mode','closed'),('physical_originals',list(range(8))),
                            ('inherited_original_cells',['old_registered_cell']),('corner_relation','corner_norm_squared <= Q')):
            bad=deepcopy(document);bad[field]=value
            reject(folder+':caller:'+field,lambda bad=bad:I.Adapter(foundation,bad))
        examples.append(dict(root_id=document['original_id'],contexts=[label for label,state in states],
                             root_document_sha256=digest(foundation/folder/'snapshots/ROOT_DOCUMENT.json')))
    assert counts['contexts']==6 and counts['additional_rows']==3456
    assert counts['physical_residuals']==31104 and counts['grouped_rows_reproduced']==864
    assert counts['synthetic_weighted_rounds']==6
    assert not any(name.split('.')[0]in{'numpy','scipy','sympy','z3','highspy'}for name in sys.modules)
    assert sources=={name:digest(HERE/name)for name in files}
    D.verify_family();D.verify_foundation(foundation)
    report=dict(status='PASS_NEW_STRICT011_FOUR_PRODUCT_SAME_STATE_LAYER_CONTROLS',
        source_hashes=sources,foundation_manifest_sha256=D.FOUNDATION,
        accepted_family_manifest_sha256=D.FAMILY,foundation_members_rehashed=len(base['files']),
        accepted_family_members_rehashed=len(family['files']),counts=counts,callers=examples,
        rejections=rejected,rejected_controls=len(rejected),
        exact_continuous_implication_in_hand_proof=True,conditional_boxes_not_certified_tree_ancestors=True,
        numeric_suggestions_are_not_LP_solves=True,synthetic_weighted_controls_not_actual_discovery_use=True,
        actual_weighted_use_gate_passed=False,installed_in_tree_replay=False,
        lost_previous_control_receipts_used=False,numerical_solver_called=False,
        original_cell_credit=0,whole_mask_credit=0)
    with args.output.open('x')as stream:json.dump(report,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps(dict(status=report['status'],counts=counts,rejected_controls=len(rejected),
                         report_sha256=digest(args.output),output=str(args.output.resolve()))))
if __name__=='__main__':main()
