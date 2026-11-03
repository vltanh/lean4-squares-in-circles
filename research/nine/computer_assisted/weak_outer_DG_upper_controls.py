#!/usr/bin/env python3
"""Deliberately damaged controls for the original DG upper-gap exact checker."""
from copy import deepcopy
import gzip, hashlib, json
from pathlib import Path
import weak_outer_DG_upper_verify as v

BASE=Path(__file__).parent

def first_path(data,pred):
    def walk(node,path,box,ch):
        if pred(node,box,ch):return path,box,ch
        if node.get('kind')=='angle':
            k=node['axis'];lo,hi=box[k];mid=(lo+hi)/2
            for side,T in (('0',(lo,mid)),('1',(mid,hi))):
                bb=list(box);bb[k]=T
                hit=walk(node['children'][side],path+['children',side],tuple(bb),ch)
                if hit:return hit
        if node.get('kind')=='sep':
            for key,child in node['children'].items():
                option=tuple(map(int,key.split(',')))
                hit=walk(child,path+['children',key],box,ch+(option,))
                if hit:return hit
        return None
    for i,(_,box) in enumerate(v.ROOTS):
        hit=walk(data['roots'][i],['roots',i],box,())
        if hit:return hit
    raise AssertionError('Requested node absent from complete certificate')

def at(data,path):
    for key in path:data=data[key]
    return data

def reject(name,data,edit):
    changed=deepcopy(data);edit(changed)
    try:v.verify(changed)
    except (AssertionError,KeyError,TypeError,ValueError,IndexError) as e:
        return {'name':name,'status':'REJECTED','reason':str(e)[:300]}
    raise AssertionError('Damaged certificate accepted: '+name)

def main():
    cert=BASE/'weak_outer_DG_upper_certificate.json.gz'
    with gzip.open(cert,'rt') as f:data=json.load(f)
    angle,_,_=first_path(data,lambda n,b,c:n.get('kind')=='angle')
    leaf,_,_=first_path(data,lambda n,b,c:'w' in n)
    sep,box,ch=first_path(data,lambda n,b,c:n.get('kind')=='sep' and any(
        not v.omitted_option_impossible(b,len(c),tuple(map(int,k.split(',')))) for k in n['children']))
    key=next(k for k in at(data,sep)['children'] if not v.omitted_option_impossible(box,len(ch),tuple(map(int,k.split(',')))))
    def false_leaf(d):
        n=at(d,leaf);n.clear();n['w']=[[0,1]]
    def negative_weight(d):at(d,leaf)['w'][0][1]=-1
    def false_empty(d):d['roots'][0]={'empty_interval':['coordinate',0]}
    rows=[
        reject('missing signed orientation root',data,lambda d:d['roots'].pop()),
        reject('missing closed angle child',data,lambda d:at(d,angle)['children'].pop('0')),
        reject('missing possible owned separator child',data,lambda d:at(d,sep)['children'].pop(key)),
        reject('false exact row combination',data,false_leaf),
        reject('negative row multiplier',data,negative_weight),
        reject('false empty-coordinate terminal',data,false_empty),
    ]
    result={'status':'PASS','controls_rejected':len(rows),'controls':rows,
            'certificate_sha256':hashlib.sha256(cert.read_bytes()).hexdigest(),
            'verifier_sha256':hashlib.sha256((BASE/'weak_outer_DG_upper_verify.py').read_bytes()).hexdigest(),
            'exact_helper_sha256':hashlib.sha256((BASE/'weak_outer_hand_right_lower_verify.py').read_bytes()).hexdigest()}
    (BASE/'weak_outer_DG_upper_rejection_controls.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
