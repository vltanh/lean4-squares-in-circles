"""Index every literal node of a successfully replayed whole D821 proof.

The raw hash-bound node records retain every rational coefficient, positive
weight, residual correction and guard.  This renderer adds a readable full
case table; it supplies no new mathematical premise or closure by itself.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import hashlib
import json


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dyadic_lower(value):
    value=F(value)
    assert value>0
    lower=F(1)
    while lower>value:
        lower/=2
    return str(lower)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('report',type=Path)
    parser.add_argument('output',type=Path)
    args=parser.parse_args()
    report=json.loads(args.report.read_text())
    assert report['status']=='PASS_COMPLETE_ORIGINAL_CELL'
    assert report['original_id']=='positive-821c9a2debeed0aa'
    assert report['whole_original_proved'] is True
    assert report['complete_closed_complement_domains']==5
    args.output.mkdir(parents=True,exist_ok=False)
    covers=report['grafted_cover_nodes']
    labels={e['manifest']['sha256']:f'T{k:03d}'for k,e in enumerate(covers)}
    assert len(labels)==len(covers)
    grafts={}
    for cover in covers:
        for entry in cover['grafts']:
            key=(cover['manifest']['sha256'],entry['leaf_index'])
            assert key not in grafts
            grafts[key]=entry['continuation']
    audits={e['manifest_sha256']:e for e in report['exact_tree_reports'].values()}
    rows=[]
    lines=['# Complete D821 literal terminal and cover table','',
        'This table is rendered only from a successful complete-original replay. '
        'The associated JSON pins each raw node, which contains all exact rational rows, '
        'weights, residual payments, and original-state data.','',
        'A displayed reserve bound is a positive dyadic lower bound for the exact reserve. '
        'Every proxy, owned-axis, and angle union retains all closed alternatives. '
        'A graft continues exactly the identified independently replayed OPEN leaf.','',
        '| Tree | Component | Node | Parent | Incoming choice | Rounds | Deductions | Checked rows | Conclusion |',
        '|---|---:|---:|---:|---|---:|---:|---:|---|']
    for cover in covers:
        reference=cover['manifest'];path=Path(reference['path'])
        assert sha(path)==reference['sha256']
        manifest=json.loads(path.read_text())
        audit=audits[reference['sha256']]
        assert cover['complete_after_grafting'] is True
        local={entry['index']:entry['audit']for entry in audit['node_audits']}
        assert set(local)==set(range(len(manifest['nodes'])))
        for entry in manifest['nodes']:
            index=entry['index'];node_path=path.parent/entry['file']
            assert sha(node_path)==entry['sha256']
            node=json.loads(node_path.read_text());record=node['record'];checked=local[index]
            terminal=record.get('terminal')
            if checked['status']=='PASS_EXCLUDED_PHYSICAL_DOMAIN':
                assert terminal is not None and not node['children']
                if checked['reserve'] is not None:
                    conclusion='exact reserve >= '+dyadic_lower(checked['reserve'])
                else:
                    conclusion=terminal['kind']
            elif node['children']:
                split=node['split']
                count={'proxy':4,'sat':8,'angle':2}[split['kind']]
                assert len(node['children'])==count
                conclusion=f"complete {split['kind']}{count} cover: {node['children']}"
            else:
                continuation=grafts[reference['sha256'],index]
                conclusion='graft to '+labels[continuation['sha256']]
            literal=dict(tree=labels[reference['sha256']],component=manifest['component'],
                node=index,parent=node['parent'],depth=node['depth'],choice=node['choice'],
                original_path=node['initial']['path'],manifest=reference,
                raw_node=dict(path=str(node_path),sha256=entry['sha256']),
                audit=checked,conclusion=conclusion)
            if terminal is not None:
                literal['terminal_kind']=terminal['kind']
                literal['terminal_literal_in_raw_node']=True
            rows.append(literal)
            choice=json.dumps(node['choice'],separators=(',',':'))
            lines.append(f"| {literal['tree']} | {literal['component']} | {index} | {node['parent']} | "
                         f"{choice} | {checked['rounds']} | {checked['deductions']} | "
                         f"{checked['printed_rows_checked']} | {conclusion} |")
    assert {e['component']for e in report['component_audits']}==set(range(5))
    lines += ['', '## The five original complementary domains','',
              '| Component | Pilot conclusion | Complete continuation |',
              '|---|---|---|']
    for entry in report['component_audits']:
        tree=entry['tree']
        continuation=labels[tree['sha256']]if tree is not None else 'pilot itself excludes the domain'
        lines.append(f"| {entry['component']} | {entry['pilot']['status']} | {continuation} |")
    (args.output/'COMPLETE_TERMINAL_TABLE.md').write_text('\n'.join(lines)+'\n')
    result=dict(schema='D821_complete_literal_terminal_table_v1',
        status='RENDERED_FROM_PASS_COMPLETE_ORIGINAL_CELL',
        exact_report=dict(path=str(args.report.resolve()),sha256=sha(args.report)),
        tree_count=len(covers),node_count=len(rows),nodes=rows,
        component_audits=report['component_audits'],new_original_cell_credit_from_renderer=0,new_masks=0)
    (args.output/'COMPLETE_TERMINAL_TABLE.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],trees=len(covers),nodes=len(rows))),flush=True)


if __name__=='__main__':
    main()
