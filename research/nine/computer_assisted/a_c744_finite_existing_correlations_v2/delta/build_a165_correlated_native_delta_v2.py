#!/usr/bin/env python3
"""Compact preservation after the finite existing-row gate has actually passed."""
from pathlib import Path
import hashlib,json
WORK=Path(__file__).resolve().parent;ROOT=WORK.parents[1]
TREE=WORK/'a165_correlated_existing_continuation_v2'
OLD=WORK/'a165_i64_exact_continued_tree_v1'
OUT=WORK/'a165_existing_correlations_native_delta_v2'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def write(p,value):
    assert not p.exists();p.write_text(json.dumps(value,indent=2)+'\n')
def main():
    report=WORK/'A165_CORRELATED_EXISTING_CONTINUATION_EXACT_REPLAY_V2.json';r=read(report)
    assert sha(report)=='eee73dfe46135c506568026e92bb32e16cbbd5751bb26b87768504fe3175061d'
    assert(r['nodes'],r['excluded_leaves'],r['open_leaves'],r['changed_payloads'],r['fresh_deductions'])==(165,118,14,6,10)
    assert not OUT.exists();OUT.mkdir();copies={}
    def cp(p,name):
        p=Path(p).resolve();q=OUT/name;assert p.is_file()and not p.is_symlink()and not q.exists()
        q.parent.mkdir(parents=True,exist_ok=True);raw=p.read_bytes();q.write_bytes(raw);assert sha(p)==sha(q)
        copies[str(p)]=dict(member=name,sha256=sha(p),bytes=len(raw))
    for version in(1,2):
        code=WORK/f'a165_correlated_existing_rows_v{version}'
        freeze=read(code/'SOURCE_BINDINGS.json')
        for name,h in freeze['files'].items():assert sha(code/name)==h;cp(code/name,f'sources/v{version}/'+name)
        cp(code/'SOURCE_BINDINGS.json',f'sources/v{version}/SOURCE_BINDINGS.json')
    cp(TREE/'manifest.json','tree/manifest.json');cp(OLD/'manifest.json','SOURCE_MANIFEST.json')
    old,new=read(OLD/'manifest.json'),read(TREE/'manifest.json');assembly=[]
    for a,b in zip(old['nodes'],new['nodes']):
        assert a['index']==b['index']and a['file']==b['file']
        assert sha(OLD/a['file'])==a['sha256']and sha(TREE/b['file'])==b['sha256']
        e=dict(index=b['index'],file=b['file'],sha256=b['sha256'])
        if a['sha256']==b['sha256']:e['source']='PREVIOUS_ACCEPTED_A165_TREE'
        else:e.update(source='THIS_DELTA',member='tree/'+b['file']);cp(TREE/b['file'],e['member'])
        assembly.append(e)
    assert sum(x['source']=='THIS_DELTA'for x in assembly)==6
    for p in [report,TREE/'CONSTRUCTION_RECEIPT.json',WORK/'A165_CORRELATED_EXISTING_CONSTRUCTION_V2.log',
        WORK/'A165_CORRELATED_EXISTING_CONTINUATION_EXACT_REPLAY_V2.log',WORK/'A165_CORRELATED_EXISTING_OBSERVED_EXECUTION_V2.json',
        WORK/'A165_CORRELATED_V1_PREPARATION_FAILURE_RECEIPT.json',WORK/'A165_CORRELATED_EXISTING_CONSTRUCTION_V1.log',
        WORK/'A165_CORRELATED_BASE_ROW_INVENTORY_V1.log',WORK/'A165_CORRELATED_V2_FROM_V1.diff',
        WORK/'A165_CORRELATED_ATTACHMENT_PREPARATION_CONTROLS_V2.json',WORK/'A165_CORRELATED_CONTROL_HARNESS_HISTORY.json',
        ROOT/'d_work/A165_EXISTING_CORRELATED_ROWS_ROOT_SOURCE_REVIEW.json',ROOT/'d_work/A165_EXISTING_CORRELATED_ROWS_V2_ROOT_SOURCE_REVIEW.json']:
        cp(p,'reports/'+p.name)
    for name in('check_a165_correlated_attachment_controls_v1.py','check_a165_correlated_attachment_controls_v2.py',
        'materialize_a165_correlated_delta_v2.py'):
        cp(WORK/name,'transport/'+name)
    cp(__file__,'transport/build_a165_correlated_native_delta_v2.py')
    write(OUT/'TREE_ASSEMBLY.json',dict(schema='A165_existing_correlations_six_payload_delta_v2',
        source_manifest_sha256=sha(OLD/'manifest.json'),continued_manifest_sha256=sha(TREE/'manifest.json'),
        reused_payloads=159,included_payloads=6,nodes=assembly))
    write(OUT/'DEPENDENCIES.json',dict(schema='A165_finite_existing_row_native_dependencies_v2',
        prior_publication_commit='b39dfbc7324319363ca7ab692958c7e9c8553835',
        prior_publication='research/nine/computer_assisted/a_c744_i64_retained_cover_continuation_v1',
        prior_delta_archive_sha256='0c479a7ae1aaf76dad59908e5185838d189280de2dcdb9abeb0440c56e8641f6',
        prior_delta_input_manifest_sha256='274e0ab65d290d61b8dee91146e2e4f2ee3316ece91bc19bbe05d6afb4e43805',
        prior_complete_manifest_sha256=sha(OLD/'manifest.json'),prior_full165_exact_report_sha256=r['source_full_consumer_report_sha256'],
        external_native_arithmetic_aliases_required=True,cold_proof_claimed=False))
    (OUT/'README.md').write_text('''# Finite continuation using existing A height and difference rows

The unchanged independent arithmetic core freshly replayed twelve appended
rounds with ten original-center deductions and nineteen checked premises.
Three printed premises use the accepted coupled I64 height row; six use
existing certified pair-difference rows. Existing coordinate bounds cancel
the other coefficients with positive exact multipliers and zero residual.
No LP, new row family, branch or path predicate was introduced.

Six retained OPEN leaves changed (151,152,154,156,157,163);159 payloads remain
byte-identical. Every initial state and earlier round is retained, all33
complete unions and132 leaf domains remain. The cover still has118 excluded
and14 OPEN leaves. All changed leaves reached a fixed point within two rounds,
below the four-round cap. Further A tactics stopped; this is zero original and
mask credit, preserving the mandatory Bf14/B16 priority.

The accepted full165 arithmetic is reused by complete identity; only these
suffixes and the complete status composition are fresh. This is native exact
evidence, not a cold self-contained proof. The raw report states that distinction.

TREE_ASSEMBLY.json maps159 omitted records to the exact previous accepted A165
tree. First reconstruct that tree using the published prior delta and its
published A1 dependency. The included byte-only materializer then combines it
with these six changed records. Its default mode only verifies all bytes and
prefixes; --output makes a fresh tree without modifying either source.

The initial constructor failed before creating any changed leaf or manifest:
it spelled the existing upper rows bound_hi_ instead of bound_up_. All frozen
v1 sources, the failure log, exact144 unchanged partial-record identities,
and the narrow v2 correction are preserved. The145/36 row-inventory assertions
were retained. The independent v2 gate observed exit0. No failed candidate was
admitted as mathematical evidence.
''')
    write(OUT/'COPY_PROVENANCE.json',copies)
    files={str(p.relative_to(OUT)):dict(bytes=p.stat().st_size,sha256=sha(p))for p in sorted(OUT.rglob('*'))if p.is_file()}
    write(OUT/'INPUT_MANIFEST.json',dict(schema='A165_existing_correlated_rows_native_delta_v2',files=files,new_original_cells=0,new_masks=0))
    print(json.dumps(dict(folder=str(OUT),input_manifest_sha256=sha(OUT/'INPUT_MANIFEST.json'),files=len(files)+1,
        bytes=sum(v['bytes']for v in files.values())+(OUT/'INPUT_MANIFEST.json').stat().st_size)),flush=True)
if __name__=='__main__':main()
