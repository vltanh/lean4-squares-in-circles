#!/usr/bin/env python3
"""One stronger, unguarded full-nine relaxation on each surviving original cell.

All existing v14 corner rows are retained, including the 128 exact rational
directions omitted by the sparse discovery accelerator. No new assumption,
geometric threshold, or case split is introduced. Every candidate is exact
replayed against the unchanged v14 verifier before a whole cell is closed.
"""
import concurrent.futures,json,signal,sys,time,traceback,warnings
from pathlib import Path

HERE=Path(__file__).resolve().parent;PACKAGE=HERE/'whole_cell_payload'

def test_cell(row):
    sys.path.insert(0,str(PACKAGE))
    import weak_outer_numeric_strict_bulk_v14_lp as M
    import weak_outer_numeric_strict_bulk_v14_verify as V
    warnings.filterwarnings('ignore');start=time.monotonic()
    original=M.linprog
    def capped(*args,**kwargs):
        options=dict(kwargs.get('options',{}));options['time_limit']=2.;options['threads']=1;kwargs['options']=options
        return original(*args,**kwargs)
    def expire(signum,frame):raise TimeoutError('full matrix direct-cell deadline')
    old=signal.signal(signal.SIGALRM,expire);signal.setitimer(signal.ITIMER_REAL,8)
    M.linprog=capped
    out={'id':row['id'],'sign':row['sign'],'path':row['path'],'status':'OPEN'}
    try:
        box,pos,ch=V.reconstruct(row['path']);fl=lambda vv:tuple(tuple(float(x) for x in v) for v in vv)
        hit,point,data=M.solve(fl(box),fl(pos),ch)
        if hit is not None:
            leaf=json.loads(json.dumps({'path':row['path'],**hit}));reserve,terminal=V.replay_leaf(leaf)
            out.update(status='CLOSED_BY_EXACT_MODEL',leaf=leaf,reserve=str(reserve),terminal=terminal)
        elif point is not None:out['relaxed_centers']=[float(x) for x in point]
    except TimeoutError:out['timed_out']=True
    except Exception:out['rejected_candidate']=traceback.format_exc()
    finally:
        M.linprog=original;signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,old)
    out['seconds']=time.monotonic()-start;return out

def main():
    register=json.loads((PACKAGE/'fixed_231_register.json').read_text())
    pending=[r for r in register['cells'] if r['status']=='OPEN']
    # Prioritize original cells whose guarded upper/upper intersection was
    # excluded, but never add those guards to this unguarded model.
    uu_ids=set()
    for name in ['UU_existing_cell_certificates.json','UU_bounded_cell_certificates.json']:
        p=HERE.parent/'agent_global'/name
        if p.exists():
            data=json.loads(p.read_text())
            records=data if isinstance(data,list) else data.get('certificates',data.get('results',[]))
            uu_ids|={r['id'] for r in records if 'id' in r}
    pending.sort(key=lambda r:(r['id'] not in uu_ids,-len(r['path'])))
    results=[];closed=[];start=time.monotonic()
    with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
        futures=[pool.submit(test_cell,row) for row in pending]
        for future in concurrent.futures.as_completed(futures):
            row=future.result();results.append(row)
            if row['status']=='CLOSED_BY_EXACT_MODEL':closed.append(row)
            report={'scope':'Unguarded entire original cells with all frozen v14 corner rows; no new geometric conditions or subdivisions.',
                    'starting_open_original_cells':178,'cells_attempted':len(results),'new_closed_original_cells':len(closed),
                    'remaining_open_original_cells':178-len(closed),'whole_mask_closed':False,'seconds':time.monotonic()-start,'results':results}
            (HERE/'dense_original_cell_report.json').write_text(json.dumps(report,indent=2)+'\n')
            (HERE/'dense_original_cell_closed.json').write_text(json.dumps(closed,indent=2)+'\n')
            print('cells',len(results),'closed',len(closed),'last',row['id'],row['status'],flush=True)
    print('DONE',len(results),len(closed),flush=True)

if __name__=='__main__':main()
