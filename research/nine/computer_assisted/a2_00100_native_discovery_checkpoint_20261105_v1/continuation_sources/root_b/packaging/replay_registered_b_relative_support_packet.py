#!/usr/bin/env python3
"""Fresh bounded-memory standard-library replay with exact archive-relative path aliases."""
from pathlib import Path
import argparse,hashlib,json,os,sys,time

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prior',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();started=time.monotonic();root=Path(__file__).resolve().parent.parent
    prior=a.prior.resolve();out=a.output.resolve();assert not out.exists()
    common=Path(os.path.commonpath((str(root),str(prior),str(out)))).resolve()
    assert str(common)not in('/','/workspace','/workspace/scratch'), 'Use one dedicated portable replay directory.'
    manifest=json.loads((root/'INPUT_MANIFEST.json').read_text());info=json.loads((root/'ORIGINAL_PROOF.json').read_text())
    for name,h in manifest['files'].items():assert sha(root/name)==h,('packet input',name)
    assert sha(prior/'SHA256_MANIFEST.json')==info['prior_manifest_sha256']
    prior_manifest=json.loads((prior/'SHA256_MANIFEST.json').read_text())
    for name,h in prior_manifest['files'].items():assert sha(prior/name)==h,('prior input',name)
    aliases={}
    for old,entry in json.loads((root/'BINDINGS.json').read_text()).items():
        assert entry['root']in('prior','packet');base=prior if entry['root']=='prior'else root
        p=(base/entry['path']).resolve();assert p.is_relative_to(base)
        assert sha(p)==entry['sha256'];aliases[old]=p
    def audit(event,args):
        if event=='open'and args and isinstance(args[0],(str,bytes)):
            name=args[0].decode()if isinstance(args[0],bytes)else args[0]
            p=Path(name).resolve()
            if str(p).startswith('/workspace/'):assert p.is_relative_to(common),('external workspace read forbidden',str(p))
    sys.addaudithook(audit);out.mkdir(parents=True)
    sys.path.insert(0,str(root/'code'))
    import verify_b_relative_support_chord_tree as EXACT
    import independent_b_difference_tree_replay as TREE
    import independent_b_whole_domain as WHOLE
    import independent_shared_sharp_terminal as SHARP
    class PortableAdapter(EXACT.Adapter):
        def retain(self,path,expected=None):
            raw=str(Path(path));p=aliases.get(raw)
            if p is None:
                candidate=Path(path).resolve()
                if candidate.is_relative_to(common):p=candidate
                else:p=self.locate(candidate).resolve()
            assert p.is_relative_to(common),('unbound path',str(path))
            found=sha(p);assert expected is None or found==expected,('changed file',str(p))
            key=str(p);assert key not in self.files or self.files[key]==found
            self.files[key]=found;return p
    adapter=PortableAdapter(prior,root/'accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1',root/'code/sharp_terminal')
    attached=info['current_definition_attachment']
    def attached_json(entry):
        assert entry['root']in('prior','packet');base=prior if entry['root']=='prior'else root
        p=(base/entry['path']).resolve();assert p.is_relative_to(base)and sha(p)==entry['sha256']
        return json.loads(p.read_text())
    frozen=attached_json(attached['frozen_definition']);current=attached_json(attached['current_register'])
    assert attached['frozen_definition']['sha256']=='ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604'
    fields=('id','sign','baseline_frontier_index','path')
    assert attached['compared_fields']==list(fields)and attached['all_231_original_definitions_unchanged']is True
    assert len(frozen['cells'])==len(current['cells'])==231
    assert [[c[k]for k in fields]for c in frozen['cells']]==[[c[k]for k in fields]for c in current['cells']]
    selected=[c for c in current['cells']if c['id']==info['original_id']]
    assert len(selected)==1 and selected[0]['path']==info['original_path']and selected[0]['status']=='OPEN'
    assert info['exact_entry']=='verify_b_relative_support_chord_tree'
    entry=info['tree'];assert entry['root']=='packet';tree=root/entry['path'];assert sha(tree)==entry['sha256']
    report=TREE.verify_tree(tree,adapter);p=json.loads(tree.read_text())['parent']
    assert WHOLE.verify(adapter.retain(p['path'],p['sha256']),adapter)
    assert report['initial_original_id']==info['original_id']and report['initial_path']==info['original_path']
    assert report['complete']==info['complete']
    if not info['open_prototype']:assert report['complete']is True and report['open_leaves']==0
    report['entire_registered_original_domain_retained']=True
    if report['complete']:
        report['status']='PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE';report['whole_original_proved']=True
    adapter.recheck()
    SHARP.verify_binding(adapter.sharp_package)
    for name,h in manifest['files'].items():assert sha(root/name)==h
    for name,h in prior_manifest['files'].items():assert sha(prior/name)==h
    assert not any(name in sys.modules for name in('numpy','scipy','highspy','physical_incircle_chords','physical_rotating_frame_center_rows','physical_general_center_cone_rows','physical_relative_support_chords'))
    assert not any(name.startswith('b_')and'runtime'in name for name in sys.modules)
    report.update(source_sha256=adapter.files,ancestry_reports=adapter.reports,
        universal_center_disk_rows_checked=adapter.center_rows,incircle_chord_rows_checked=adapter.chord_rows,rotating_center_cone_rows_checked=adapter.cone_rows,general_center_cone_rows_checked=adapter.general_cone_rows,relative_support_chord_rows_checked=adapter.relative_support_chord_rows,original_corner_rows=adapter.corner_rows,unit_corner_rows=adapter.unit_corner_rows,
        four_product_unit_corner_rows=adapter.four_corner_rows,four_product_physical_premise_bound=adapter.four_binding_bound,
        frame_square_rows=adapter.frame_square_rows,projection_square_rows=adapter.projection_square_rows,
        current_register_original_definition_attachment=attached,
        full_angle_AB_extra_terminals=adapter.extra_full_occurrences,opposite_ABID_terminals=adapter.opposite_abid_occurrences,
        full_angle_scalar_replay=adapter.full_scalar_replay,opposite_scalar_replay=adapter.opposite_scalar_replay)
    final=out/'COMPLETE_ORIGINAL_REPLAY.json';final.write_text(json.dumps(report,indent=2)+'\n')
    receipt=dict(status='PASS_PORTABLE_OPEN_PROTOTYPE'if info['open_prototype']else'PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL',
        original_id=info['original_id'],complete=report['complete'],whole_original_proved=bool(report['complete']),
        report_sha256=sha(final),packet_manifest_sha256=sha(root/'INPUT_MANIFEST.json'),
        prior_manifest_sha256=info['prior_manifest_sha256'],packet_inputs=len(manifest['files']),prior_inputs=len(prior_manifest['files']),
        every_new_bound_and_cover_replayed=True,all_inputs_rehashed_at_completion=True,external_workspace_reads_forbidden=True,
        numerical_modules_imported=False,lean_lake_ci_run=False,new_original_ledger_credit=0,new_mask_ledger_credit=0,
        seconds=time.monotonic()-started)
    (out/'PORTABLE_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
