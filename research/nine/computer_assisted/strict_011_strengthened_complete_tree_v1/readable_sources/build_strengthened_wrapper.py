#!/usr/bin/env python3
"""Create a new immutable wrapper by explicit changes to the frozen cover walk."""
if not __debug__:
    raise RuntimeError('Exact wrapper construction rejects optimized Python.')
import argparse
import ast
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE_SHA='c66b6e08616b49623fb6253c28ab2fb6aba1c5d70e0d645ae56b019a5a7bacae'
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def functions(source):
    return {node.name:ast.dump(node,include_attributes=False)for node in ast.walk(ast.parse(source))if isinstance(node,ast.FunctionDef)}
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--base',type=Path,required=True);args=parser.parse_args()
    assert digest(args.base)==BASE_SHA
    original=args.base.read_text();source=original
    helper_sha=digest(HERE/'strengthened_adapter.py')
    changes=[
        ('No producer, optimizer, or conditional terminal is imported. The source-bound\nwhole-caller symmetry identity is independently replayed by the new adapter.',
         'No producer or optimizer is imported. The exact corner/guard attachment is\nseparately pinned. Every used conditional theorem requires a fresh scalar replay.\nThe original whole-caller symmetry and complete 4/8/2 walk are unchanged.'),
        ("MODEL_BINDING = 'e10ee28803afc321209a9480a6cf76ce1f2ffabcfcfae5970d444d9958cfa2f4'",
         "STRENGTHENED_ADAPTER_SHA = '"+helper_sha+"'\nMODEL_BINDING = 'e10ee28803afc321209a9480a6cf76ce1f2ffabcfcfae5970d444d9958cfa2f4'"),
        ('def verify(manifest_path, workspace, model_folder):',
         'def verify(manifest_path, workspace, model_folder, corner_folder, guard_folder, scalar_output_folder):'),
        ('    adapter = I.Adapter()\n',
         "    extra_path = Path(__file__).resolve().parent/'strengthened_adapter.py'\n"
         "    pin(extra_path, STRENGTHENED_ADAPTER_SHA)\n"
         "    E = read_module('strengthened011_complete_adapter', extra_path, STRENGTHENED_ADAPTER_SHA)\n"
         "    base_document = json.loads((model_folder/'snapshots/ROOT_DOCUMENT.json').read_text())\n"
         "    adapter = E.Adapter(model_folder.parent, corner_folder, guard_folder, base_document, scalar_output_folder)\n"
         "    for path, expected in adapter.binding_hashes().items():\n"
         "        pin(path, expected)\n"),
        ("assert manifest['schema'] == 'fresh_full_strict011_representative_complete_tree_v1'",
         "assert manifest['schema'] == 'fresh_full_strict011_strengthened_representative_tree_v1'"),
        ("    return dict(status='PASS_COMPLETE_STRICT011_REPRESENTATIVE_PHYSICAL_TREE' if complete else 'PASS_COMPLETE_STRICT011_REPRESENTATIVE_COVER_WITH_OPEN_DOMAINS',",
         "    strengthened_audit = adapter.final_audit()\n"
         "    return dict(status='PASS_COMPLETE_STRICT011_STRENGTHENED_REPRESENTATIVE_PHYSICAL_TREE' if complete else 'PASS_COMPLETE_STRICT011_STRENGTHENED_REPRESENTATIVE_COVER_WITH_OPEN_DOMAINS',"),
        ('        normalized_root=True, conditional_theorem_used=False,',
         "        normalized_root=True, conditional_theorem_used=strengthened_audit['conditional_theorem_used'],\n"
         "        strengthened_attachment=strengthened_audit,"),
        ('    report = verify(args.manifest, args.workspace, args.model_folder)',
         "    report = verify(args.manifest, args.workspace, args.model_folder, args.corner_folder,\n"
         "                    args.guard_folder, args.scalar_output_folder)"),
        ('    args = parser.parse_args()',
         "    parser.add_argument('--corner-folder', type=Path, required=True)\n"
         "    parser.add_argument('--guard-folder', type=Path, required=True)\n"
         "    parser.add_argument('--scalar-output-folder', type=Path, required=True)\n"
         "    args = parser.parse_args()")]
    for old,new in changes:
        assert source.count(old)==1,old
        source=source.replace(old,new)
    before,after=functions(original),functions(source)
    for name in ('walk','local_file','digest','read_module','pin'):assert before[name]==after[name],name
    for name,raw in (('accepted_base_wrapper.py',original),('verify_strengthened_complete_tree.py',source)):
        with (HERE/name).open('x')as stream:stream.write(raw)
    value=dict(schema='explicit_strengthened_wrapper_source_transform_v1',
        base_source_sha256=BASE_SHA,helper_sha256=helper_sha,
        result_sha256=digest(HERE/'verify_strengthened_complete_tree.py'),
        unchanged_function_asts=['walk','local_file','digest','read_module','pin'],
        changes=[dict(old=old,new=new)for old,new in changes],
        active_original_wrapper_modified=False,old_complete_schema_accepted=False,
        numerical_solver_called=False,whole_mask_credit=0)
    with (HERE/'WRAPPER_TRANSFORMATION.json').open('x')as stream:json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps(dict(status='PASS_PREPARED_EXPLICIT_STRENGTHENED_WRAPPER',
                         wrapper_sha256=value['result_sha256'],helper_sha256=helper_sha)))
if __name__=='__main__':main()
