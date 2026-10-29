from fractions import Fraction as F

D,j=100000,141421
rows=[
(F(1,3),F(2,5),103717,105410,107704,144074,6796926173),
(F(2,5),F(9,20),107552,107704,109659,146859,10898674656),
(F(9,20),F(19,40),109384,109659,110708,148206,127392976304),
(F(19,40),F(1,2),111148,110708,111804,149513,218986870228),
(F(1,2),F(21,40),112833,111804,112944,150769,9996242795),
(F(21,40),F(11,20),114428,112944,114128,151967,196501795052),
(F(11,20),F(3,5),117293,114128,116620,154136,8751748397),
(F(3,5),F(2,3),120259,116620,120186,156405,8201898243),
(F(2,3),F(1),125000,120186,141422,160079,3185240802),
]
assert j*j<2*D*D
assert rows[0][0]==F(1,3) and rows[-1][1]==1
for i,(a,b,m,u,ub,v,N) in enumerate(rows):
 assert a<=b
 assert 1<=F(m,D)<=F(5,4)
 if i:assert rows[i-1][1]==a
 assert F(u*u,D*D)>=1+a*a
 assert F(ub*ub,D*D)>=1+b*b
 assert F(v*v,D*D)>=1+F(m*m,D*D)
 assert F(79,40)>F(v,D)
 if b<1:assert F(m,D)>=b+(1-b)*F(ub,D)/(F(j,D)-b)
 else:assert F(m,D)==F(5,4)
 A,B=a.numerator,a.denominator
 calculated=79*u*B*(D+m-v)-60*u*B*v+j*(79*(B*D+m*A)-40*v*(A+B))
 assert calculated==N and N>0
 print(f'row {i+1}: PASS, exact numerator {N}')
print('PASS: all 9 rational proximity-certificate rows')
