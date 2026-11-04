"""Complete D821 proof from its accepted terminal and grafted closed complements."""
from pathlib import Path
import argparse,json,time,sys
from verify_D821_complete_original import theorem,ID
from verify_d821_root import Adapter as RootAdapter,verify_root,Checker,CORE,sha
from verify_five_complements import verify as verify_component,GUARD
import verify_d821_continuations as CONT
import verify_d821_consequence_tree as UNION_REPLAY

def main():
    ap=argparse.ArgumentParser();ap.add_argument('plan',type=Path);ap.add_argument('report',type=Path)
    a=ap.parse_args();started=time.monotonic();plan=json.loads(a.plan.read_text())
    assert plan['schema']=='D821_grafted_five_complement_complete_original_plan_v1'and plan['original_id']==ID
    premise=theorem(plan['theorem_binding']);UNION_REPLAY.install();UNION_REPLAY.UNIT_REPLAY.verify_premises()
    checker=Checker(context=CORE,ancestry=CORE/'ancestry');root_adapter=RootAdapter(checker)
    root=CONT.retain(plan['root_certificate']);ancestor,state=verify_root(root,root_adapter)
    assert state is not None and state['id']==ID
    rows,guard=GUARD.reduced_complement(state);assert guard['premises_proved']and len(rows)==5
    pm=CONT.retain(plan['five_pilot_manifest']);pilot=json.loads(pm.read_text())
    assert pilot['schema']=='D821_closed_two_link_five_domain_pilot_v1'and pilot['completed']is True
    assert pilot['parent']['sha256']==sha(root)and Path(pilot['parent']['path']).resolve()==root
    assert pilot['components']==list(range(5))and[e['component']for e in pilot['results']]==list(range(5))
    assert pilot['complete_closed_escape_declaration']and pilot['mask']=='001/00'and pilot['all_nine_original_frames']
    assert pilot['new_original_cells']==pilot['new_masks']==0
    for p,h in pilot['sources'].items():CONT.retain(dict(path=p,sha256=h))
    initial={int(k):v for k,v in plan['component_trees'].items()};assert len(initial)==len(plan['component_trees'])
    extensions={};extension_refs={}
    for reference in plan.get('continuations',[]):
        p=CONT.retain(reference);m=json.loads(p.read_text());seed=CONT.retain(m['parent']);raw=json.loads(seed.read_text())
        assert raw['schema']=='D821_certified_open_tree_leaf_seed_v1'
        key=(raw['ancestor_tree']['sha256'],raw['leaf_index'])
        assert key not in extensions and reference['sha256']not in extension_refs
        extensions[key]=reference;extension_refs[reference['sha256']]=reference
    used=set();active=set();cover_nodes=[]
    def complete_tree(reference,component,parent_component):
        p=CONT.retain(reference);digest=reference['sha256']
        assert digest not in active and digest not in used;active.add(digest)
        r=CONT.replay(p,checker)
        assert r['component']==component and r['origin_component_parent']==parent_component
        manifest=json.loads(p.read_text());assert manifest['mask']=='001/00'and manifest['all_nine_original_frames']
        children=[]
        for leaf in r['leaf_table']:
            key=(digest,leaf['index'])
            if leaf['excluded']:
                assert key not in extensions
                continue
            assert key in extensions,('Unclosed complementary leaf',component,str(p),leaf['index'])
            child=extensions[key];complete_tree(child,component,parent_component)
            children.append(dict(leaf_index=leaf['index'],continuation=child))
        active.remove(digest);used.add(digest)
        cover_nodes.append(dict(manifest=reference,component=component,locally_closed=r['complete'],
                                original_open_leaves=r['open_leaves'],grafts=children,complete_after_grafting=True))
    components=[];expected_trees=set()
    for entry in pilot['results']:
        index=entry['component'];p=CONT.retain(dict(path=str(pm.parent/entry['file']),sha256=entry['sha256']))
        assert p.name==f'component_{index}.json';raw=json.loads(p.read_text())
        assert raw['parent']==pilot['parent']and raw['component']==index
        audit,after=verify_component(p,checker,state)
        parent_component=dict(path=str(p),sha256=sha(p))
        if after is None:
            assert index not in initial;components.append(dict(component=index,pilot=audit,tree=None,complete=True));continue
        assert index in initial,('Missing component tree',index)
        reference=initial[index];tp=CONT.retain(reference);tm=json.loads(tp.read_text())
        if tm['parent']!=parent_component:
            union_path=CONT.retain(tm['parent']);union=json.loads(union_path.read_text())
            assert union['schema']==UNION_REPLAY.SCHEMA
            assert union['component_parent']==parent_component
            assert union['unchanged_component_path']==state['path']
            assert union['whole_unchanged_component_domain']is True
        complete_tree(reference,index,parent_component);expected_trees.add(reference['sha256'])
        components.append(dict(component=index,pilot=audit,tree=reference,complete=True))
    assert set(initial)=={x['component']for x in components if x['tree']is not None}
    assert used==expected_trees|set(extension_refs)and len(components)==5
    CONT.recheck();assert not active
    report=dict(schema='D821_complete_grafted_original_exact_proof_v1',status='PASS_COMPLETE_ORIGINAL_CELL',
                original_id=ID,original_path=state['path'],mask='001/00',all_nine_original_frames=True,
                original_corners=36,original_physical_pairs=36,original_center_cones_preserved=5,
                original_actual_links=['AB','BC','EF','FG'],original_strict_weak_bits=['CD'],
                closed_Q_face_excluded_by_strict_CD_equality_blocker=True,
                original_ancestor=ancestor,accepted_two_link_theorem=premise,reduced_complement_guard=guard,
                complete_closed_complement_domains=5,component_audits=components,grafted_cover_nodes=cover_nodes,
                exact_tree_reports=CONT.REPORTS,whole_original_proved=True,proposed_original_cell_credit=1,
                whole_mask_credit=0,fixed_ledger_not_modified=True,numerical_producer_imported=False,
                numerical_fields_used=False,input_sha256=CONT.RETAINED,
                plan_sha256=sha(a.plan),checker_sha256={str(Path(p).resolve()):sha(p)for p in(__file__,CONT.__file__,GUARD.__file__,UNION_REPLAY.__file__,UNION_REPLAY.HULL.__file__,UNION_REPLAY.UNIT_REPLAY.__file__)},
                seconds=time.monotonic()-started)
    a.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k]for k in('status','original_id','complete_closed_complement_domains','whole_original_proved','proposed_original_cell_credit','seconds')}),flush=True)
if __name__=='__main__':main()
