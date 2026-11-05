#!/usr/bin/env python3
"""Recorded source transformation of the reviewed strengthened complete walk."""
if not __debug__:
    raise RuntimeError('Exact wrapper transformation requires assertions.')
import ast
import difflib
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ACCEPTED='48f09d6a110fc0a735dac12300cae363369298e2098e4ccf7110f1023673968c'
def digest_bytes(raw):return sha256(raw).hexdigest()
def find_function(tree,name):
    return next(node for node in ast.walk(tree)if isinstance(node,ast.FunctionDef)and node.name==name)
def old_dispatch(tree):
    walk=find_function(tree,'walk')
    return next(node for node in ast.walk(walk)if isinstance(node,ast.If)and ast.unparse(node.test)=="kind in ('sat', 'proxy')")
def main():
    raw=(HERE/'accepted_strengthened_wrapper.py').read_bytes();assert digest_bytes(raw)==ACCEPTED
    original=raw.decode();text=original
    manager_sha=digest_bytes((HERE/'height_context_adapter.py').read_bytes())
    replacements=[
        ('Fresh full strict011 exact 4/8/2 tree replay, with no legacy ancestry.',
         'Fresh strict011 complete tree with a separately gated C-height union.'),
        ('The original whole-caller symmetry and complete 4/8/2 walk are unchanged.',
         'The old 4/8/2 dispatch and base states are unchanged; explicit height contexts are inherited.'),
        ("STRENGTHENED_ADAPTER_SHA =",f"HEIGHT_CONTEXT_ADAPTER_SHA = '{manager_sha}'\nSTRENGTHENED_ADAPTER_SHA ="),
        ('def verify(manifest_path, workspace, model_folder, corner_folder, guard_folder, scalar_output_folder):',
         'def verify(manifest_path, workspace, model_folder, corner_folder, guard_folder, scalar_output_folder, height_folder, height_scalar_output_folder):'),
        ("    for path, expected in adapter.binding_hashes().items():\n        pin(path, expected)\n    manifest_hash = pin(manifest_path)",
         "    for path, expected in adapter.binding_hashes().items():\n        pin(path, expected)\n    height_path = Path(__file__).resolve().parent/'height_context_adapter.py'\n    pin(height_path, HEIGHT_CONTEXT_ADAPTER_SHA)\n    H = read_module('strict011_height_context_attachment', height_path, HEIGHT_CONTEXT_ADAPTER_SHA)\n    height = H.Manager(adapter, I, height_folder, guard_folder, base_document, height_scalar_output_folder)\n    for path, expected in height.binding_hashes().items():\n        pin(path, expected)\n    manifest_hash = pin(manifest_path)"),
        ("assert manifest['schema'] == 'fresh_full_strict011_strengthened_representative_tree_v1'",
         "assert manifest['schema'] == 'fresh_full_strict011_C_height_context_tree_v1'"),
        ('    def walk(node_id, expected_state):','    def walk(node_id, expected_state, height_context):'),
        ("        record = json.loads(path.read_text())\n        audit, state = G.check_record(record, expected_state, adapter)",
         "        record = json.loads(path.read_text())\n        height.check_record_envelope(record, height_context)\n        height.assert_active_context(height_context)\n        adapter = height.adapter(height_context)\n        audit, state = G.check_record(record, expected_state, adapter)"),
        ("        audits.append(dict(node=node_id, file=entry['file'], sha256=entry['sha256'], arithmetic=audit))",
         "        audits.append(dict(node=node_id, file=entry['file'], sha256=entry['sha256'], arithmetic=audit, height_context=deepcopy(height_context)))"),
        ("            if kind in ('sat', 'proxy'):",
         "            if kind == H.HEIGHT_KIND:\n                height_successors = height.accept_union(node_id, state, height_context, split)\n                successors = [(child, child_state) for child, child_state, context in height_successors]\n                child_contexts = {child: context for child, child_state, context in height_successors}\n            elif kind in ('sat', 'proxy'):"),
        ("            results = [walk(child, child_state) for child, child_state in successors]",
         "            if kind != H.HEIGHT_KIND:\n                child_contexts = {child: deepcopy(height_context) for child, child_state in successors}\n            results = [walk(child, child_state, child_contexts[child]) for child, child_state in successors]"),
        ("    complete = walk(manifest['root'], initial)","    complete = walk(manifest['root'], initial, None)"),
        ("    assert 4*splits['proxy']+8*splits['sat']+2*splits['angle'] == len(entries)-1",
         "    assert 4*splits['proxy']+8*splits['sat']+2*splits['angle']+4*splits[H.HEIGHT_KIND] == len(entries)-1"),
        ('    strengthened_audit = adapter.final_audit()',
         '    strengthened_audit = adapter.final_audit()\n    height_audit = height.final_audit()'),
        ("'PASS_COMPLETE_STRICT011_STRENGTHENED_REPRESENTATIVE_PHYSICAL_TREE' if complete else 'PASS_COMPLETE_STRICT011_STRENGTHENED_REPRESENTATIVE_COVER_WITH_OPEN_DOMAINS'",
         "'PASS_COMPLETE_STRICT011_C_HEIGHT_REPRESENTATIVE_PHYSICAL_TREE' if complete else 'PASS_COMPLETE_STRICT011_C_HEIGHT_REPRESENTATIVE_COVER_WITH_OPEN_DOMAINS'"),
        ("normalized_root=True, conditional_theorem_used=strengthened_audit['conditional_theorem_used'],",
         "normalized_root=True, conditional_theorem_used=(strengthened_audit['conditional_theorem_used'] or bool(height_audit['complete_height_unions'])),"),
        ('        strengthened_attachment=strengthened_audit,',
         '        strengthened_attachment=strengthened_audit, height_cover_attachment=height_audit,'),
        ("    parser.add_argument('--scalar-output-folder', type=Path, required=True)",
         "    parser.add_argument('--scalar-output-folder', type=Path, required=True)\n    parser.add_argument('--height-folder', type=Path, required=True)\n    parser.add_argument('--height-scalar-output-folder', type=Path, required=True)"),
        ('                    args.guard_folder, args.scalar_output_folder)',
         '                    args.guard_folder, args.scalar_output_folder, args.height_folder, args.height_scalar_output_folder)')]
    changes=[]
    for index,(before,after)in enumerate(replacements):
        assert text.count(before)==1,(index,before,text.count(before))
        text=text.replace(before,after)
        changes.append(dict(index=index,before=before,after=after))
    old_ast=ast.parse(original);new_ast=ast.parse(text)
    preserved=[]
    for name in('digest','read_module','local_file','pin'):
        assert ast.dump(find_function(old_ast,name),include_attributes=False)==ast.dump(find_function(new_ast,name),include_attributes=False)
        preserved.append(name)
    assert ast.dump(old_dispatch(old_ast),include_attributes=False)==ast.dump(old_dispatch(new_ast),include_attributes=False)
    with(HERE/'verify_height_complete_tree.py').open('x')as stream:stream.write(text)
    with(HERE/'HEIGHT_WRAPPER_FROM_ACCEPTED.diff').open('x')as stream:
        stream.writelines(difflib.unified_diff(original.splitlines(True),text.splitlines(True),
            fromfile='accepted_strengthened_wrapper.py',tofile='verify_height_complete_tree.py'))
    result=dict(status='PASS_EXPLICIT_NEW_HEIGHT_UNION_WRAPPER_TRANSFORMATION',
        accepted_source_sha256=ACCEPTED,new_source_sha256=digest_bytes(text.encode()),
        height_context_adapter_sha256=manager_sha,complete_change_list=changes,
        unchanged_function_ASTs=preserved,unchanged_sat_proxy_angle_dispatch_AST=True,
        new_height_context_scope='exact parent-derived record envelope, unchanged base state dictionary',
        automatic_mask_credit=0)
    with(HERE/'WRAPPER_TRANSFORMATION.json').open('x')as stream:json.dump(result,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps(dict(status=result['status'],changes=len(changes),new_source_sha256=result['new_source_sha256'],height_context_adapter_sha256=manager_sha)))
if __name__=='__main__':main()
