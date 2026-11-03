#!/usr/bin/env python3
"""Independent exact checker for a complete original-center rectangle cover.

The supplied state needs its own independently accepted bound induction.
This checker binds that state's bytes, rejects a changed center box, and
checks every leaf and the exhaustive closed-child union. No producer is
imported. Only Python's standard library is used.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

RHO = F(91,60)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def intervals(value):
    result=tuple(tuple(F(x) for x in pair) for pair in value)
    assert all(len(pair)==2 and pair[0]<=pair[1] for pair in result)
    return result


def minimum_square(pair):
    a,b=pair
    return F(0) if a<=0<=b else min(a*a,b*b)


def verify(cover_path,state_path):
    cover_path,state_path=Path(cover_path),Path(state_path)
    cover=json.loads(cover_path.read_text())
    state=json.loads(state_path.read_text())
    assert cover['status']=='COMPLETE' and not cover['pending']
    assert cover['original_id']==state['id']
    assert cover['proof_record_sha256']==sha(state_path)
    assert state['scope']=='WHOLE_UNCHANGED_ORIGINAL_PARENT'
    assert cover['completed_rounds']==len(state['rounds'])
    target=cover['target_original']
    assert type(target)is int and 0<=target<9
    positions=intervals(cover['positions'])
    assert len(positions)==18 and positions==intervals(state['final_positions'])
    root=intervals(cover['root_box'])
    assert len(root)==2 and root==(positions[2*target],positions[2*target+1])
    assert all(a<b for a,b in root)

    tree={}
    for leaf in cover['leaves']:
        node=tree
        for step in leaf['path']:
            assert len(step)==2
            axis,side=step
            assert type(axis)is int and axis in(0,1)
            assert type(side)is int and side in(0,1)
            assert 'leaf'not in node,'a terminal is another terminal ancestor'
            node=node.setdefault((axis,side),{})
        assert not node,'duplicate terminal or terminal above existing descendants'
        node['leaf']=leaf

    witnesses=Counter()
    reserves=[]
    maxdepth=0
    def walk(node,rectangle,depth):
        nonlocal maxdepth
        maxdepth=max(maxdepth,depth)
        if 'leaf'in node:
            assert set(node)=={'leaf'}
            leaf=node['leaf']
            assert intervals(leaf['box'])==rectangle
            if leaf['kind']=='incircle':
                other=leaf['original']
                assert type(other)is int and 0<=other<9 and other!=target
                upper=F(0)
                for axis in(0,1):
                    p,q=rectangle[axis]
                    a,b=positions[2*other+axis]
                    # Difference extremes of the entire two rectangles.
                    upper+=max((p-b)**2,(q-a)**2)
                assert upper<1
                assert F(leaf['squared_distance_upper'])==upper
                reserve=1-upper
                assert F(leaf['reserve'])==reserve
                witnesses[str(other)]+=1
            else:
                assert leaf['kind']=='outside_center_disk'
                lower=sum(minimum_square(pair) for pair in rectangle)
                # Every physical original center has norm STRICTLY <91/60.
                assert lower>=RHO*RHO
                assert F(leaf['squared_distance_lower'])==lower
                reserve=lower-RHO*RHO
                assert F(leaf['reserve'])==reserve
                witnesses['outside_center_disk']+=1
            reserves.append(reserve)
            return 1,1,0
        assert len(node)==2,'incomplete closed-child union'
        keys=set(node)
        axes={key[0]for key in keys}
        assert len(axes)==1
        axis=next(iter(axes))
        assert keys=={(axis,0),(axis,1)}
        lo,hi=rectangle[axis]
        middle=(lo+hi)/2
        totals=[1,0,1]
        for side in(0,1):
            child=list(rectangle)
            child[axis]=(lo,middle)if side==0 else(middle,hi)
            got=walk(node[axis,side],tuple(child),depth+1)
            totals=[a+b for a,b in zip(totals,got)]
        return tuple(totals)

    nodes,leaves,splits=walk(tree,root,0)
    assert nodes==cover['nodes'] and leaves==len(cover['leaves'])
    assert maxdepth==cover['depth'] and nodes==2*leaves-1
    return {'status':'PASS_COMPLETE_ORIGINAL_CENTER_COVER',
            'original_id':state['id'],'target_original':target,
            'cover_sha256':sha(cover_path),'state_sha256':sha(state_path),
            'checker_sha256':sha(__file__),
            'requires_separately_verified_bound_induction':True,
            'nodes':nodes,'terminal_rectangles':leaves,'internal_rectangle_splits':splits,
            'maximum_depth':maxdepth,'pending_rectangles':0,
            'witness_counts':dict(witnesses),'least_leaf_reserve':str(min(reserves)),
            'all_shared_faces_covered':True,'whole_mask_closed':False,
            'lean_lake_ci_run':False,'human_or_kernel_verification':False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cover',type=Path)
    parser.add_argument('state',type=Path)
    parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    result=verify(args.cover,args.state)
    text=json.dumps(result,indent=2)+'\n'
    if args.out:
        args.out.parent.mkdir(parents=True,exist_ok=True)
        args.out.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
