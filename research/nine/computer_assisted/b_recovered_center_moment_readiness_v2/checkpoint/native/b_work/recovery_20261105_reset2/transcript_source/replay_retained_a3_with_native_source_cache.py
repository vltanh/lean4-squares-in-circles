#!/usr/bin/env python3
"""Fresh retained-tree arithmetic with explicit same-run source proof reuse.

Only four source-provider calls are memoized. Their exact completed results
come from gate17430, whose receipt and every source input are hash-bound.
The frozen tree reader, adapters, row checks, parent attachment, arithmetic,
terminal checks and full 4/8/2 traversal execute unchanged on every node.
This entry point is a native evidence-reuse gate, not a cold portable gate.
"""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import sys
import time
import independent_original_064_bound_rows as I

if not __debug__:
    raise RuntimeError('Exact native tree replay requires assertions.')

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'tree'))
import verify_a_c744_component3_post_a1_bounds_lazy_tree as BASE
import independent_a_c744_component3_post_a1_bound_rows as POST
import independent_a_c744_component3_shared_bound_rows as SHARED
import independent_a_c744_component1_consequence as A1
import independent_a_c744_complement_consequences as COMPLEMENTS

def source_descriptor(source):
    ref=source['source_report']
    assert I.read_reference(ref)==ref['report']
    return ref['report']


def validate_root_source(source,module,binding,counts):
    assert source['binding_sha256']==module.BINDING_SHA
    assert source['original_id']==I.TARGET and source['original_path']==I.ORIGINAL_PATH
    assert source['component']==3 and source['scope']==module.SCOPE
    assert source['valid_on_whole_original']is False
    assert source['new_original_cells']==source['new_masks']==0
    report=source_descriptor(source)
    assert report['status']=='PASS_PARTIAL_TWO_LINK_COMPLEMENT_TREE'
    assert report['original_id']==I.TARGET and report['original_path']==I.ORIGINAL_PATH
    assert report['component']==3 and report['closed_domain']==module.CLOSED_DOMAIN
    assert report['conditional_parent']==binding['conditional_parent']
    assert report['nodes']==report['leaf_domains']==report['open_leaves']==1
    assert report['excluded_leaves']==0 and report['closed_unions']=={}
    assert tuple(report[k]for k in('rounds','deductions','printed_rows_checked'))==counts
    assert report['all_nine_originals_retained']is True and report['closed_shared_faces_retained']is True
    assert report['new_original_cells']==report['new_masks']==0
    tree=binding['source_tree'];manifest=Path(tree['folder'])/'manifest.json'
    assert report['input_sha256'][str(manifest)]==tree['manifest_sha256']
    assert report['input_sha256'][str(Path(tree['folder'])/tree['node_file'])]==tree['node_sha256']


def validated_cache():
    evidence,binding=I.completed_native_source()
    gate=I.read_reference(binding['native_completed_source_report'])
    expected_base=binding['source_sha256'][str(Path(BASE.__file__).resolve())]
    assert I.sha(BASE.__file__)==expected_base
    shared_binding=SHARED.verify_binding();post_binding=POST.verify_binding()
    a1_binding=A1.verify_binding();complement_binding=COMPLEMENTS.verify_binding()
    shared=gate['fresh_component3_shared_bound_source']
    post=gate['fresh_component3_post_a1_bound_source']
    a1=gate['fresh_completed_component1_consequence_source']
    complements=gate['freshly_replayed_original_complement_consequences']
    assert shared['status']=='PASS_FRESH_UNSPLIT_A_C744_COMPONENT3_BOUND_STATE'
    assert post['status']=='PASS_FRESH_UNSPLIT_A_C744_COMPONENT3_POST_A1_BOUND_STATE'
    validate_root_source(shared,SHARED,shared_binding,(4,446,1025))
    validate_root_source(post,POST,post_binding,(7,565,1436))
    assert a1['status']=='PASS_FRESH_COMPLETE_COMPONENT1_ORIGINAL_CONSEQUENCE'
    assert a1['binding_sha256']==A1.BINDING_SHA and a1['necessary_weak_row']==a1_binding['necessary_weak_row']
    a1_report=source_descriptor(a1);I.check_complete_old_report(a1_report,1)
    assert a1_report['node_payloads_replayed_lazily']is True and a1_report['numerical_producer_imported']is False
    a1_tree=a1_binding['source_tree']
    assert a1_report['input_sha256'][str(Path(a1_tree['folder'])/'manifest.json')]==a1_tree['manifest_sha256']
    assert complements['status']=='PASS_FRESH_COMPLEMENT_EXCLUSION_CONSEQUENCES'
    assert complements['binding_sha256']==COMPLEMENTS.BINDING_SHA and complements['excluded_components']==[0,2,4]
    five,zero=[I.read_reference(x)for x in complements['source_reports']]
    assert [five,zero]==[x['report']for x in complements['source_reports']]
    I.check_declaration(five);I.check_complete_old_report(zero,0)
    zero_manifest=Path(complement_binding['component0_proof']['folder'])/'manifest.json'
    assert zero['input_sha256'][str(zero_manifest)]==I.sha(zero_manifest)
    assert zero['conditional_parent']==complement_binding['whole_original_parent']
    cache=dict(post=(post,post_binding),shared=(shared,shared_binding),a1=a1,complements=complements)
    return evidence,binding,cache


def replay(tree,output):
    tree,output=Path(tree).resolve(),Path(output).resolve()
    assert not output.exists()
    started=time.monotonic()
    evidence,binding,cache=validated_cache()
    manifest_path=tree/'manifest.json'
    manifest=json.loads(manifest_path.read_text());manifest_hash=I.sha(manifest_path)
    assert manifest['id']==I.TARGET and manifest['original_path']==I.ORIGINAL_PATH
    assert manifest['component']==3
    assert manifest['closed_domain']==POST.CLOSED_DOMAIN
    # This retained cover predates I64 row installation. It is checked on its
    # original closed3/5 component, without adding or narrowing any domain.
    assert 'original_064_bound_state'not in manifest
    assert len(manifest['nodes'])==235
    assert manifest_hash=='e8a64502970e6c2da9cd3e6bfcc9605f3cc64b4c6c27565b25ba4fba8f0e8382'
    calls=dict(post=0,shared=0,a1=0,complements=0)
    originals=[(POST,'replay_source',POST.replay_source),
               (SHARED,'replay_source',SHARED.replay_source),
               (A1,'replay_source',A1.replay_source),
               (COMPLEMENTS,'replay_source_exclusions',COMPLEMENTS.replay_source_exclusions)]
    def cached_post(requested_output):
        assert POST.verify_binding()==cache['post'][1]
        calls['post']+=1;return deepcopy(cache['post'])
    def cached_shared(requested_output):
        assert SHARED.verify_binding()==cache['shared'][1]
        calls['shared']+=1;return deepcopy(cache['shared'])
    def cached_a1(requested_output):
        A1.verify_binding();calls['a1']+=1;return deepcopy(cache['a1'])
    def cached_complements(requested_output):
        COMPLEMENTS.verify_binding();calls['complements']+=1;return deepcopy(cache['complements'])
    POST.replay_source=cached_post
    SHARED.replay_source=cached_shared
    A1.replay_source=cached_a1
    COMPLEMENTS.replay_source_exclusions=cached_complements
    try:
        report=BASE.replay(tree,output)
    finally:
        for module,name,function in originals:setattr(module,name,function)
    assert calls==dict(post=1,shared=1,a1=1,complements=1)
    assert report['nodes']==235 and report['original_id']==I.TARGET and report['component']==3
    assert report['closed_domain']==POST.CLOSED_DOMAIN
    assert report['node_payloads_replayed_lazily']is True
    assert report['all_nine_originals_retained']is True and report['closed_shared_faces_retained']is True
    assert report['new_original_cells']==report['new_masks']==0
    I.verify_binding()
    assert I.sha(manifest_path)==manifest_hash
    for module,_,function in originals:
        assert I.sha(module.__file__)==binding['source_sha256'][str(Path(module.__file__).resolve())]
    report.update(native_source_evidence_mode='EXPLICIT_REUSE_OF_COMPLETED_RUN_17430_PROOF_DEPENDENCIES',
        reused_source_evidence=evidence,cached_source_provider_calls=calls,
        source_dependency_arithmetic_repeated_in_this_invocation=False,
        retained_consumer_tree_arithmetic_freshly_replayed=True,
        original_closed_3_5_component_scope_preserved=True,
        new_I64_row_used_by_this_retained_cover=False,
        cold_portable_proof_claimed=False,native_total_seconds=time.monotonic()-started)
    report['checker_dependency_sha256'][str(Path(__file__).resolve())]=I.sha(__file__)
    report['checker_dependency_sha256'][str(Path(I.__file__).resolve())]=I.sha(I.__file__)
    report['checker_dependency_sha256'][str(I.BINDING)]=I.BINDING_SHA
    output.write_text(json.dumps(report,indent=2)+'\n')
    assert not any(name in sys.modules for name in('numpy','scipy','highspy','original_064_bound_rows'))
    print(json.dumps({k:report[k]for k in('status','nodes','excluded_leaves','open_leaves','rounds','deductions',
        'printed_rows_checked','cached_source_provider_calls','retained_consumer_tree_arithmetic_freshly_replayed',
        'source_dependency_arithmetic_repeated_in_this_invocation','new_original_cells','new_masks')}),flush=True)
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('tree',type=Path);parser.add_argument('output',type=Path)
    parser.add_argument('--validate-cache-only',action='store_true')
    args=parser.parse_args()
    if args.validate_cache_only:
        evidence,binding,cache=validated_cache()
        print(json.dumps(dict(status='PASS_EXACT_COMPLETED_SOURCE_CACHE_BINDINGS',providers=list(cache),
            source_report_sha256=binding['native_completed_source_report']['sha256'],
            input_hashes=len(binding['source_sha256']),arithmetic_repeated=False)),flush=True)
    else:replay(args.tree,args.output)
