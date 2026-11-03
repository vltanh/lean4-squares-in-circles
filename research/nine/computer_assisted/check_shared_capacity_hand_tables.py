#!/usr/bin/env python3
"""Independent rational arithmetic for the short shared-capacity hand tables.

Input: a delivered portable archive containing the exact whole-parent
certificates. This script checks the short final tables only. The separate
portable physical verifier must replay every original-parent premise.
It imports no producer, geometry collector, optimizer or row generator.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse,hashlib,json,tarfile

IDS=('positive-033850931bb6d4ef','positive-3cd9c2a7981effa2')
HASHES=('793810d2986272e40daa18e3a6992a340ad1f97366a8198e3bd268f21efab4fa',
        '9044084710c58146d05a8598b37ff2a25114758f4003ae1ca969625039a859a3')

def read_certificate(archive,ident):
    matches=[n for n in archive.getnames() if n.endswith('/certificates/'+ident+'.json')]
    assert len(matches)==1,(ident,matches)
    raw=archive.extractfile(matches[0]).read()
    return raw,json.loads(raw)

def signature(row):
    return row['name'],tuple(sorted((k,F(c)) for k,c in row['coefficients'])),F(row['rhs'])

def main():
    ap=argparse.ArgumentParser();ap.add_argument('archive',type=Path);ap.add_argument('--out',type=Path)
    a=ap.parse_args();reports=[]
    with tarfile.open(a.archive) as archive:
        data=[]
        for ident,digest in zip(IDS,HASHES):
            raw,record=read_certificate(archive,ident)
            assert hashlib.sha256(raw).hexdigest()==digest
            assert record['id']==ident and record['new_branch_nodes']==0
            data.append(record)
        first,second=(x['terminal']['rows'] for x in data)
        assert len(first)==len(second)==7
        assert [signature(x) for x in first]==[signature(x) for x in second]
        p,q,s=F(108567,1048576),F(30302249,15728640),F(3837595,14680064)
        weights=[F(1),1/p,F(1),1-s,F(1),q/p-2+s,F(1)]
        assert all(w>0 for w in weights)
        coefficients=[F(0)]*54;rhs=F(0)
        for row,w in zip(first,weights):
            rhs+=w*F(row['rhs'])
            for k,c in row['coefficients']:coefficients[k]+=w*F(c)
        assert all(c==0 for c in coefficients)
        assert rhs==-F(2315620317940810579,12533921283739484160)
        reports.append({'ids':list(IDS),'status':'PASS_EXACT_SEVEN_ROW_HAND_TABLE',
                        'positive_weights':list(map(str,weights)),
                        'all_54_coefficients_zero':True,'negative_rhs':str(rhs)})
        third='positive-b696531e6d132c9e'
        if any(n.endswith('/certificates/'+third+'.json') for n in archive.getnames()):
            raw,record=read_certificate(archive,third)
            assert hashlib.sha256(raw).hexdigest()=='dc40a92af77feebf14789f65173208b936a8dc2ef2a4a0c696bf58e15a52a4ef'
            rows=record['terminal']['rows'];assert len(rows)==2
            coefficients=[F(0)]*54;rhs=F(0)
            for row in rows:
                rhs+=F(row['rhs'])
                for k,c in row['coefficients']:coefficients[k]+=F(c)
            assert all(c==0 for c in coefficients)
            assert rhs==-F(33805,131072)
            reports.append({'ids':[third],'status':'PASS_EXACT_TWO_ROW_HAND_TABLE',
                            'positive_weights':['1','1'],'all_54_coefficients_zero':True,
                            'negative_rhs':str(rhs)})
    result={'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'archive_sha256':hashlib.sha256(a.archive.read_bytes()).hexdigest(),
            'scope':'Short final-table arithmetic; full physical/induction replay is separately required.',
            'reports':reports}
    text=json.dumps(result,indent=2)+'\n'
    if a.out:a.out.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
