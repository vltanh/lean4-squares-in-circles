#!/usr/bin/env python3
"""Exact emitted-text controls in Q(sqrt(3)); finite tests, not global UNSAT."""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import hashlib,json,re
from emit_hex_root import build_root
from verify_hex_cover import sign_sqrt3,require

class K:
    def __init__(self,a=0,b=0):self.a,self.b=F(a),F(b)
    @staticmethod
    def cast(x):return x if isinstance(x,K) else K(x)
    def __add__(self,z):
        z=self.cast(z);return K(self.a+z.a,self.b+z.b)
    __radd__=__add__
    def __neg__(self):return K(-self.a,-self.b)
    def __sub__(self,z):return self+-self.cast(z)
    def __rsub__(self,z):return self.cast(z)+-self
    def __mul__(self,z):
        z=self.cast(z);return K(self.a*z.a+3*self.b*z.b,self.a*z.b+self.b*z.a)
    __rmul__=__mul__
    def sign(self):return sign_sqrt3(self.a,self.b)
    def __eq__(self,z):return (self-self.cast(z)).sign()==0
    def __lt__(self,z):return (self-self.cast(z)).sign()<0
    def __le__(self,z):return (self-self.cast(z)).sign()<=0
    def __gt__(self,z):return (self-self.cast(z)).sign()>0
    def __ge__(self,z):return (self-self.cast(z)).sign()>=0


def parse(text):
    tokens=re.findall(r'\(|\)|[^\s()]+',re.sub(r';[^\n]*','',text))
    stack=[];out=[]
    for token in tokens:
        if token=='(':stack.append([])
        elif token==')':
            require(bool(stack),'parentheses');v=stack.pop();(stack[-1] if stack else out).append(v)
        else:stack[-1].append(token)
    require(not stack,'unclosed syntax')
    defs={};preds={};variables=[]
    for command in out:
        if command[0]=='declare-fun':variables.append(command[1])
        if command[0]=='define-fun':defs[command[1]]=command[4]
        if command[0]=='assert':preds[command[1][3]]=command[1][1]
    return variables,defs,preds


def evaluate(t,env,defs):
    if isinstance(t,str):
        try:return K(F(t))
        except ValueError:pass
        if t not in env:env[t]=evaluate(defs[t],env,defs)
        return env[t]
    name,*args=t
    if name=='and':return all(evaluate(x,env,defs) for x in args)
    if name=='or':return any(evaluate(x,env,defs) for x in args)
    a=[evaluate(x,env,defs) for x in args]
    if name=='+':return sum(a,K())
    if name=='*':
        result=K(1)
        for x in a:result=result*x
        return result
    if name=='-':return -a[0] if len(a)==1 else a[0]-a[1]
    if name=='=':return a[0]==a[1]
    if name=='<':return a[0]<a[1]
    if name=='<=':return a[0]<=a[1]
    if name=='>':return a[0]>a[1]
    if name=='>=':return a[0]>=a[1]
    raise ValueError('unexpected operator '+name)


def main():
    here=Path(__file__).resolve().parent
    manifest=json.loads((here/'hex_root_manifest.json').read_text())
    report=json.loads((here/'hex_verification_report.json').read_text())
    occupied=report['witness_control']['assigned_cells']
    centers=[(F(x,2),F(1,16)) for x in (-3,-1,1,3)]
    centers += [(F(x),-F(15,16)) for x in (-1,0,1)]
    centers += [(F(x,20),F(19,16)) for x in (-11,11)]
    poses=[tuple(map(K,(x,y,F(1) if i<7 else F(99,101),F(0) if i<7 else F(20,101))))
           for i,(x,y) in enumerate(centers)]
    total=0;canonical_checks=0
    def rotate(x,y):return K(F(1,2))*x-K(0,F(1,2))*y,K(0,F(1,2))*x+K(F(1,2))*y
    for symmetry,perm in enumerate(manifest['symmetries']):
        transformed=[]
        for pose in poses:
            x,y,a,b=pose
            if symmetry>=6:y,b=-y,-b
            for _ in range(symmetry%6):x,y=rotate(x,y);a,b=rotate(a,b)
            transformed.append((x,y,a,b))
        cellposes=sorted((perm[c],p) for c,p in zip(occupied,transformed))
        row={'cells':[c for c,p in cellposes]}
        for radius in ('strict','closed'):
            model=build_root(row,manifest['cells'],radius)
            variables,defs,predicates=parse(model.smt2())
            require(len(variables)==37 and len(predicates)==137,'emitted counts')
            require(sum(x.startswith('pair_') for x in predicates)==36,'pairs lost')
            require(sum(x.startswith('hex_') for x in predicates)==54,'hex constraints lost')
            env={'sqrt_three':K(0,1)}
            for i,(c,pose) in enumerate(cellposes):
                env.update({f'{v}_{i}':z for v,z in zip(('x','y','a','b'),pose)})
            failures=[name for name,t in predicates.items() if not evaluate(t,env,defs)]
            if radius=='closed':require(not failures,'closed witness rejected')
            else:require(len(failures)==4 and all(x.startswith('corner_') for x in failures),'strict equality behavior')
            total+=1
        mask=sum(1<<c for c in row['cells'])
        if mask==report['witness_control']['canonical_mask']:canonical_checks+=1
    require(canonical_checks>=1,'canonical witness not tested')
    vertex_checks=0
    for c,(q,r) in enumerate(manifest['cells']):
        row={'cells':[c]+[i for i in range(19) if i!=c][:8]}
        variables,defs,predicates=parse(build_root(row,manifest['cells'],'closed').smt2())
        hex0=[t for name,t in predicates.items() if name.startswith('hex_0_')]
        for X,Y in ((2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1)):
            env={'sqrt_three':K(0,1),'x_0':K(F(49,200)*(3*q+X)),
                 'y_0':K(0,F(49,200)*(q+2*r+Y))}
            require(all(evaluate(t,env,defs) for t in hex0),'closed hex vertex rejected')
            vertex_checks+=1
        env={'sqrt_three':K(0,1),'x_0':K(F(49,200)*(3*q+3)),
             'y_0':K(0,F(49,200)*(q+2*r))}
        require(not all(evaluate(t,env,defs) for t in hex0),'outside-hex point accepted')
    result={'result':'PASS','arithmetic':'Fraction pairs in Q(sqrt(3))',
            'emitted_models_evaluated':total,'canonical_witness_symmetries':canonical_checks,
            'closed_hex_vertices_checked':vertex_checks,'outside_hex_controls_rejected':19,
            'root_real_variables':37,'root_assertions':137,'original_pairs_retained':36,
            'new_hex_inequalities':54,'frame_gauge_used':False,
            'baseline_git_blob_sha':'9139677c644b3d66f9e3db986f12a54b4321ec17',
            'emitter_sha256':hashlib.sha256((here/'emit_hex_root.py').read_bytes()).hexdigest(),
            'global_lower_bound_proved':False}
    (here/'hex_emitter_test_report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
