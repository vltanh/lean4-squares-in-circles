#!/usr/bin/env python3
"""Untrusted index builder from one immutable completed-record context only.

The output chooses candidate proofs; the separate strict assembly checker
replays every chosen component and derives every closed/open conclusion.
"""
from collections import defaultdict
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import importlib.util
import json

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('dc71_assembly_definitions',HERE/'verify_dc71_original_cover_v3.py')
G=importlib.util.module_from_spec(spec);spec.loader.exec_module(G)
digest=lambda p:sha256(Path(p).read_bytes()).hexdigest()

def build(context,output):
    context=Path(context).resolve();output=Path(output).resolve();assert not output.exists()
    raw=(context/'SHA256_MANIFEST.json').read_bytes();manifest=json.loads(raw)['files']
    byhash=defaultdict(list)
    for name,h in manifest.items():byhash[h].append(name)
    for names in byhash.values():names.sort(key=lambda n:(not n.startswith('data'),len(n),n))
    sharp_path=context/'shared_strict_row_terminal.py'
    assert digest(sharp_path)==G.SHARP_PINS['shared_strict_row_terminal.py']
    sp=importlib.util.spec_from_file_location('candidate_sharp_guard_only',sharp_path)
    sharp=importlib.util.module_from_spec(sp);sp.loader.exec_module(sharp)
    loaded={};candidate_guards={}
    def record(h):
        if h not in loaded:
            name=byhash[h][0];p=context/name;assert p.is_relative_to(context)and digest(p)==h
            loaded[h]=json.loads(p.read_text())
        return loaded[h]
    def binding(h):return dict(file=byhash[h][0],sha256=h)
    children=defaultdict(lambda:defaultdict(list));H_records=defaultdict(list)
    considered=[];excluded_unfinished=[]
    for name,h in sorted(manifest.items()):
        if not name.startswith('data')or not name.endswith('.json'):continue
        r=record(h)
        if not isinstance(r,dict)or r.get('id')!=G.ID:continue
        if r.get('schema')not in G.H_SCHEMAS+(G.SLOPE_SCHEMA,):continue
        assert r['path']==G.PATH
        if r['status']=='OPEN'and ('final_test'not in r or r['final_test'].get('proposals')!=[]):
            excluded_unfinished.append(dict(file=name,sha256=h));continue
        assert r['status']in('OPEN','CANDIDATE_CLOSED')
        considered.append(h)
        if r['schema']==G.SLOPE_SCHEMA:
            s=r['slope_restriction'];assert s['kind']=='original_slope_closed_equal_partition'
            key=(s['parent']['sha256'],s['original'],s['parts'])
            if h not in children[key][s['index']]:children[key][s['index']].append(h)
        else:
            tile=tuple(r['prior']['tile']+r['derived_H_cover']['tile'])
            if h not in H_records[tile]:H_records[tile].append(h)
    memo={};active=set()
    def candidate(h):
        if h in memo:return memo[h]
        assert h not in active,'cycle in untrusted index candidates';active.add(h)
        r=record(h)
        if r['status']=='CANDIDATE_CLOSED':answer=(dict(kind='terminal',bound=binding(h)),True,1,0)
        elif sharp.evaluate_any_guard(r['final'])['status']=='PASS_SHARP_PHYSICAL_ROW_GUARD':
            candidate_guards[h]=sharp.evaluate_any_guard(r['final'])
            answer=(dict(kind='accepted_sharp_guard',bound=binding(h)),True,1,0)
        else:
            assert r['status']=='OPEN'and r['final_test']['round']==len(r['rounds'])and r['final_test']['proposals']==[]
            answer=(dict(kind='open',bound=binding(h)),False,0,1)
            choices=[]
            for (parent,original,parts),slots in children.items():
                if parent!=h or set(slots)!=set(range(parts)):continue
                if r['schema']not in(G.H_SCHEMAS[1],G.SLOPE_SCHEMA):continue
                if not r['rounds']:continue
                sub=[]
                for i in range(parts):
                    possibilities=[candidate(c)for c in slots[i]]
                    chosen=max(possibilities,key=lambda a:(a[1],a[2],-a[3],len(record(a[0]['bound']['sha256'])['rounds'])))
                    sub.append(chosen)
                node=dict(kind='slope_cover',bound=binding(h),original=original,parts=parts,
                          children=[dict(index=i,node=a[0])for i,a in enumerate(sub)])
                choices.append((node,all(a[1]for a in sub),sum(a[2]for a in sub),sum(a[3]for a in sub)))
            if choices:answer=max([answer]+choices,key=lambda a:(a[1],a[2],-a[3]))
        active.remove(h);memo[h]=answer;return answer
    I_index=json.loads((context/'DC71_SIX_ROUND_RECORDS.json').read_text())
    I_bound={tuple(e['tile']):e['sha256']for e in I_index['records']}
    I_members=[];predicted_closed=[];frontier=[];normal_roots=0
    for itile in product(range(4),repeat=2):
        if itile in((0,1),(0,2)):
            m=dict(tile=list(itile),kind='initial_I_difference');closed=True
        elif itile not in G.PARENTS:
            h=I_bound[itile];assert record(h)['status']=='CANDIDATE_CLOSED'
            m=dict(tile=list(itile),kind='I_terminal',bound=binding(h));closed=True
        else:
            h=I_bound[itile];assert h==G.PARENTS[itile]and record(h)['status']=='OPEN'
            H_children=[];flags=[]
            for ht in product(range(2),range(4)):
                tile=itile+ht
                if tile in G.DIRECT_H:
                    child=dict(tile=list(ht),kind='initial_H_difference');flag=True
                elif tile==(1,2,0,0):
                    child=dict(tile=list(ht),kind='finished_H_prefix_difference');flag=True
                else:
                    assert H_records[tile],('no completed H state',tile)
                    choices=[candidate(q)for q in H_records[tile]]
                    chosen=max(choices,key=lambda a:(a[1],a[2],-a[3],len(record(a[0]['bound']['sha256'])['rounds'])))
                    # A partial I22/I23 angular tree cannot close its H domain.
                    # Retain the strongest fully completed normal H parent
                    # until a full H subtree is ready; all candidate files
                    # remain frozen in the core for later complete assembly.
                    if not chosen[1]and itile in((2,2),(2,3)):
                        completed=[q for q in H_records[tile]if record(q)['status']=='OPEN'
                                   and record(q)['schema']==G.H_SCHEMAS[1]
                                   and len(record(q)['rounds'])==6]
                        assert completed,('missing completed H6 OPEN parent',tile)
                        q=sorted(completed)[0]
                        chosen=(dict(kind='open',bound=binding(q)),False,0,1)
                    child=dict(tile=list(ht),kind='proof_tree',node=chosen[0]);flag=chosen[1];normal_roots+=1
                    if not flag:frontier.append(dict(HI=list(tile),untrusted_open_leaf_count=chosen[3]))
                H_children.append(child);flags.append(flag)
            m=dict(tile=list(itile),kind='derived_H_cover',parent=binding(h),children=H_children)
            closed=all(flags)
        I_members.append(m)
        if closed:predicted_closed.append(list(itile))
    assert len(I_members)==16 and normal_roots==50
    index=dict(schema='Dc71_full_original_fixed_I_H_recursive_slope_cover_v1',
        original_id=G.ID,original_path=G.PATH,original_prefix=binding(G.PREFIX),
        original_I_parts=[4,4],derived_H_parts=[2,4],
        original_cell_denominator=231,mask_denominator=32,original_count=9,
        original_corner_count=36,original_pair_count=36,original_strict_weak_CD_retained=True,
        core_manifest_sha256=sha256(raw).hexdigest(),finished_H_prefix=binding(G.FINISHED_PREFIX),I_members=I_members)
    output.mkdir()
    index_path=output/'DC71_ORIGINAL_COVER_INDEX.json';index_path.write_text(json.dumps(index,indent=2)+'\n')
    nodes=[]
    def table(node,tile,restriction_path=()):
        r=record(node['bound']['sha256'])
        row=dict(HI=list(tile),restriction_path=list(restriction_path),kind=node['kind'],bound=node['bound'],
                 raw_status=r['status'],printed_complete_local_rounds=len(r['rounds']),
                 local_deductions=sum(len(rr['proposals'])for rr in r['rounds']),
                 terminal_kind=r.get('terminal',{}).get('kind'),reserve=r.get('terminal',{}).get('reserve'))
        if node['kind']=='accepted_sharp_guard':
            row['terminal_kind']='accepted_shared_sharp_boundary_terminal'
            row['untrusted_guard_from_raw_final']=candidate_guards[node['bound']['sha256']]
        nodes.append(row)
        if node['kind']=='slope_cover':
            parent=r['final']['angles'][node['original']]
            for child in node['children']:
                descriptor=dict(original=node['original'],parts=node['parts'],index=child['index'],
                                exact_interval=G.interval(*parent,child['index'],node['parts']))
                table(child['node'],tile,restriction_path+(descriptor,))
    for m in I_members:
        for child in m.get('children',[]):
            if child['kind']=='proof_tree':table(child['node'],tuple(m['tile']+child['tile']))
    candidate_table=dict(schema='Dc71_untrusted_literal_hand_table_specification_v1',
        status='CANDIDATE_STRUCTURE_ONLY_EXACT_ASSEMBLY_REPLAY_REQUIRED',
        original_id=G.ID,original_path=G.PATH,core_manifest_sha256=sha256(raw).hexdigest(),
        cover_index_sha256=digest(index_path),declared_I_rectangles=16,declared_H_rectangles=56,
        predicted_closed_I_from_untrusted_candidate_labels=predicted_closed,
        predicted_open_H_frontier=frontier,nodes=nodes,
        omitted_unfinished_raw_records=excluded_unfinished,
        source_context=str(context),all_inputs_came_from_one_frozen_core_manifest=True,
        candidate_accepted_sharp_guards=candidate_guards,
        index_builder_sha256=digest(__file__),new_original_cells=0,new_masks=0)
    table_path=output/'CANDIDATE_HAND_TABLE_SPECIFICATION.json';table_path.write_text(json.dumps(candidate_table,indent=2)+'\n')
    assert (context/'SHA256_MANIFEST.json').read_bytes()==raw
    for h in loaded:assert digest(context/byhash[h][0])==h
    print(json.dumps(dict(index=str(index_path),index_sha256=digest(index_path),
        hand_table_spec_sha256=digest(table_path),predicted_closed_I=predicted_closed,
        predicted_open_H_members=len(frontier),tree_nodes=len(nodes),loaded_immutable_records=len(loaded),
        selected_sharp_terminals=sum(n['kind']=='accepted_sharp_guard'for n in nodes),
        new_original_cells=0,new_masks=0)))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('context',type=Path);parser.add_argument('output',type=Path)
    a=parser.parse_args();build(a.context,a.output)
