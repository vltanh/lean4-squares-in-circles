#!/usr/bin/env python3
"""Damaged-certificate controls for the exact original F-order forest."""
import copy,gzip,json,hashlib
from pathlib import Path
from weak_outer_hand_F_order_verify import verify
HERE=Path(__file__).resolve().parent
CERT=HERE/'weak_outer_hand_F_order_certificate.json.gz'


def find(node,condition):
    if condition(node):return node
    for child in node.get('children',{}).values():
        result=find(child,condition)
        if result is not None:return result
    return None


def any_node(data,condition):
    for root in data['roots']:
        node=find(root,condition)
        if node is not None:return node
    raise AssertionError('No matching genuine node for damage control.')


def missing_root(d):d['roots'].pop()
def missing_angle_child(d):any_node(d,lambda n:n.get('kind')=='angle')['children'].pop('0')
def missing_separator_child(d):
    node=any_node(d,lambda n:n.get('kind')=='sep')
    node['children'].pop(next(iter(node['children'])))
def false_whole_root(d):d['roots'][0]={'w':[]}
def false_empty_interval(d):d['roots'][0]={'empty_interval':['coordinate',0]}
def negative_weight(d):
    node=any_node(d,lambda n:'w'in n)
    node['w'][0][1]=-node['w'][0][1]


def main():
    with gzip.open(CERT,'rt') as stream:data=json.load(stream)
    reports=[]
    controls=[('missing_orientation_root',missing_root),('missing_closed_angle_child',missing_angle_child),('missing_owned_separator_child',missing_separator_child),('false_whole_root_leaf',false_whole_root),('negative_multiplier',negative_weight),('false_empty_interval',false_empty_interval)]
    for name,damage in controls:
        altered=copy.deepcopy(data);damage(altered)
        try:verify(altered)
        except (AssertionError,ValueError,KeyError,TypeError) as exc:
            reports.append({'control':name,'status':'REJECTED','reason':str(exc)[:500]})
            print(name,'REJECTED',flush=True)
        else:raise AssertionError('Damaged certificate accepted: '+name)
    report={'status':'PASS','controls':reports,'certificate_sha256':hashlib.sha256(CERT.read_bytes()).hexdigest(),'verifier_sha256':hashlib.sha256((HERE/'weak_outer_hand_F_order_verify.py').read_bytes()).hexdigest(),'exact_helper_sha256':hashlib.sha256((HERE/'weak_outer_hand_right_lower_verify.py').read_bytes()).hexdigest()}
    (HERE/'weak_outer_hand_F_order_rejection_controls.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
