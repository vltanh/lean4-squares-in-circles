#!/usr/bin/env python3
"""Independent exact rational reconstruction of the central-L mixed caller table."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,sys

SOURCE=(Path(sys.argv[1])if len(sys.argv)>1 else
        Path(__file__).resolve().parent.parent/'WEAK_MIDDLE_CENTRAL_SELECTED_LEFT_WITH_SIDE_EXTRA.md')
rows=[(F(29,60),F(4,5),F(36,25),F(13,1875),F(10424,140625)),
      (F(4,5),F(19,20),F(129,100),F(43,11250),F(157867,1125000)),
      (F(19,20),F(13,12),F(119,100),F(1649,90000),F(96067,1125000))]
report=[]
for a,b,y,corner,disjoint in rows:
    assert y*y+a*a-F(91,60)**2==corner>0
    assert 1-(b-F(124,375))**2-(y-F(3,5))**2==disjoint>0
    assert y>F(81,100)
    report.append({'interval':[str(a),str(b)],'height':str(y),'center_radius_reserve':str(corner),'pair_distance_reserve':str(disjoint)})
assert F(71,100)**2>F(1,2)
assert F(121,200)-F(124,375)==F(823,3000)<F(7,25)
assert F(7,25)**2+F(24,25)**2==1
assert F(1129,3000)+F(29,60)==F(2579,3000)<F(24,25)
data={'result':'PASS','arithmetic':'exact Fraction rational identities',
      'source_file':SOURCE.name,'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
      'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'rows':report,'low_side_horizontal_reserve':'17/3000','original_cone_reserve':'301/3000',
      'scope':'three printed rows and low-side cone/disk arithmetic; separate physical review retained'}
Path(__file__).with_name('central_selected_left_hand_arithmetic_replay.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data,indent=2))
