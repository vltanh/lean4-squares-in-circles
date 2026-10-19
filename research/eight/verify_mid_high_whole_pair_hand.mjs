// Exact arithmetic replay for MID_HIGH_WHOLE_PAIR_HAND_PROOF.md.
// Run: node verify_mid_high_whole_pair_hand.mjs
// Fixed comparisons only; no search, interval subdivision, or dependencies.
const rational = (() => {

function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b){let t=a%b;a=b;b=t;}return a;}
class F{
 constructor(n,d=1n){
  if(n instanceof F){this.n=n.n;this.d=n.d;return;}
  if(typeof n==="string"){
   if(n.includes("/")){let a=n.split("/");n=BigInt(a[0]);d=BigInt(a[1]);}
   else if(n.includes(".")){let z=n.split("."),neg=z[0].startsWith("-");let whole=z[0].replace("-","");n=BigInt((whole||"0")+z[1]);if(neg)n=-n;d=10n**BigInt(z[1].length);}
   else n=BigInt(n);
  }else n=BigInt(n);
  d=BigInt(d);if(d<0n){n=-n;d=-d;}if(!d)throw Error("zero denominator");let g=gcd(n,d);this.n=n/g;this.d=d/g;
 }
 add(b){b=f(b);return new F(this.n*b.d+b.n*this.d,this.d*b.d);}
 neg(){return new F(-this.n,this.d);}
 sub(b){return this.add(f(b).neg());}
 mul(b){b=f(b);return new F(this.n*b.n,this.d*b.d);}
 div(b){b=f(b);return new F(this.n*b.d,this.d*b.n);}
 pow(k){return new F(this.n**BigInt(k),this.d**BigInt(k));}
 cmp(b){b=f(b);let n=this.n*b.d-b.n*this.d;return n<0n?-1:n>0n?1:0;}
 val(){return Number(this.n)/Number(this.d);}
 str(){return this.d===1n?String(this.n):this.n+"/"+this.d;}
}
function f(n,d){return n instanceof F?n:new F(n,d);}
function min(a,b){return f(a).cmp(b)<0?f(a):f(b);}
function max(a,b){return f(a).cmp(b)>0?f(a):f(b);}
function trim(p){p=p.map(f);while(p.length>1&&!p.at(-1).n)p.pop();return p;}
function add(...pp){let a=Array(Math.max(...pp.map(p=>p.length))).fill(f(0));for(let p of pp)for(let i=0;i<p.length;i++)a[i]=a[i].add(p[i]);return trim(a);}
function scale(p,k){return trim(p.map(z=>f(z).mul(k)));}
function mul(p,q){let a=Array(p.length+q.length-1).fill(f(0));for(let i=0;i<p.length;i++)for(let j=0;j<q.length;j++)a[i+j]=a[i+j].add(f(p[i]).mul(q[j]));return trim(a);}
function ev(p,x){let a=f(0);x=f(x);for(let z of p.slice().reverse())a=a.mul(x).add(z);return a;}
function bin(n,k){let z=1n;for(let j=1;j<=k;j++)z=z*BigInt(n-j+1)/BigInt(j);return z;}
function bern(p,l,h){p=trim(p);let n=p.length-1,l0=f(l),w=f(h).sub(l0),v=[];for(let k=0;k<=n;k++){let s=f(0);for(let j=k;j<=n;j++)s=s.add(p[j].mul(bin(j,k)).mul(l0.pow(j-k)).mul(w.pow(k)));v.push(s);}return v.map((_,k)=>v.slice(0,k+1).reduce((s,c,j)=>s.add(c.mul(new F(bin(k,j),bin(n,j)))),f(0)));}
function factorial(k){let p=1n;for(let j=2;j<=k;j++)p*=BigInt(j);return p;}
function trig(deg,sine){let a=Array(deg+1).fill(f(0));for(let j=0;2*j+Number(sine)<=deg;j++){let k=2*j+Number(sine);a[k]=new F(j%2?-1n:1n,factorial(k));}return a;}
function isqrt(n){if(n<2n)return n;let a=1n<<BigInt(Math.ceil(n.toString(2).length/2));while(true){let b=(a+n/a)/2n;if(b>=a)return a;a=b;}}
function sqrtUp(x,digits=10){x=f(x);let d=10n**BigInt(digits),n=isqrt(x.n*d*d/x.d)+1n;let r=new F(n,d);if(r.pow(2).cmp(x)<=0)throw Error("sqrt");return r;}
function floorScaled(x,d=100000000n){x=f(x);let a=x.n*d/x.d;if(x.n<0n&&x.n*d%x.d)a--;return a;}
return {F,f,min,max,trim,add,scale,mul,ev,bern,trig,sqrtUp,floorScaled,bin,factorial};

})();
const intervals = ((tools) => {

const {f,F,min,max,trig,ev,sqrtUp}=tools;
class I{
 constructor(a,b){if(a instanceof I){this.lo=a.lo;this.hi=a.hi;}else{this.lo=f(a);this.hi=b===undefined?f(a):f(b);}if(this.lo.cmp(this.hi)>0)throw Error("interval");}
 add(b){b=i(b);return new I(this.lo.add(b.lo),this.hi.add(b.hi));}
 neg(){return new I(this.hi.neg(),this.lo.neg());}
 sub(b){return this.add(i(b).neg());}
 mul(b){b=i(b);let vv=[this.lo.mul(b.lo),this.lo.mul(b.hi),this.hi.mul(b.lo),this.hi.mul(b.hi)];return new I(vv.reduce(min),vv.reduce(max));}
 div(b){b=i(b);if(b.lo.cmp(0)<=0&&b.hi.cmp(0)>=0)throw Error("division zero interval");return this.mul(new I(f(1).div(b.hi),f(1).div(b.lo)));}
 sq(){return new I(this.lo.cmp(0)<=0&&this.hi.cmp(0)>=0?f(0):min(this.lo.pow(2),this.hi.pow(2)),max(this.lo.pow(2),this.hi.pow(2)));}
 sqrt(){if(this.lo.cmp(0)<0)throw Error("negative sqrt");return new I(sqrtUp(this.lo).sub("1/10000000000"),sqrtUp(this.hi));}
}
function i(a,b){return a instanceof I?a:new I(a,b);}
const pi=i("3.14159","355/113");
function sincos(x){
 if(x==="pi/2")return {x:pi.div(2),s:i(1),c:i(0)};
 if(x==="pi/2-.02"||x==="pi/2+.02"){let a=sincos(".02"),sgn=x.includes("+")?1:-1;return {x:pi.div(2).add(i(".02").mul(sgn)),s:a.c,c:a.s.mul(-sgn)};}
 let q=f(x);return {x:i(q),s:i(ev(trig(11,true),q),ev(trig(13,true),q)),c:i(ev(trig(14,false),q),ev(trig(12,false),q))};
}
return {I,i,pi,sincos};

})(rational);
const geometry = ((rt,it) => {

const {f,ev,trig}=rt,{i,pi,sincos}=it;
const Q=f("9789/2500"),R=i("2.79842813","2.79842814"),a0=R.sub(1),a1=i("1.71322294","1.71322295"),b1=a1.mul(".4"),a2=i("1.62343405","1.62343407"),b2=a2.mul(".6");
const u=f(".089293"),v=f(".480179"),k=f("1.534906"),q=f(".045313"),cm=pi.div(4).add("2.143075"),goal=f(".8926"),checks=[],aligned=[];
function check(name,lhs,rhs=0){let z=i(lhs).sub(rhs);if(z.lo.cmp(0)<=0)throw Error(name+" "+z.lo.str());checks.push({name,margin:z.lo.str()});}
check("R lower bracket",Q.mul(2),R.lo.pow(2));check("R upper bracket",R.hi.pow(2),Q.mul(2));
for(const [name,a,t] of [["H/M",a1,".4"],["M/L",a2,".6"]]){
 let tt=f(t); const expr=x=>x.add(1).pow(2).add(x.mul(tt).pow(2));
 check(name+" arc endpoint lower",Q.mul(2),expr(a.lo));check(name+" arc endpoint upper",expr(a.hi),Q.mul(2));
}
const M1=cm.sub(a1.mul(k)).add(b1.mul(q)),M2=cm.sub(a2.mul(k)).add(b2.mul(q)),H1=a1.sub(a0).mul(u).add(b1.mul(v));
check("M marker minimum",M1,".32988");check("M marker maximum",".48080",M2);check("H marker maximum",".321454",H1);
check("M slope lower",b1.div(a1.add(1)),".252");check("M slope upper",".372",b2.div(a2.add(1)));check("H slope upper",".253",b1.div(a1.add(1)));
function atanUpper(x,n){x=f(x);let ans=f(0);for(let j=0;2*j+1<=n;j++)ans=ans.add(x.pow(2*j+1).div(2*j+1).mul(j%2?-1:1));return ans;}
check("folded M angle bound",".541",atanUpper(".6",9));check("folded H angle bound",".381",atanUpper(".4",5));
const cosNegative=f(1).sub(f(".162").pow(2).div(2));
check("negative frames MH impossible",f("2.027").mul(cosNegative),f("2.598").sub(1));
check("negative frames HM impossible",f("1.649").mul(cosNegative),f("2.399").sub(1));
check("H radius upper",f("1.306").pow(2),i(Q).sub(a1).sub(".5"));
check("M radius upper",f("1.35").pow(2),i(Q).sub(a2).sub(".5"));
check("M source extra positive axis",1,f("1.306").sub(".3246"));
check("H source extra positive axis",1,f("1.35").sub(".513"));
check("extra negative axis first quadrant MH",2,f("2.598").sub("1.027"));
check("extra negative axis first quadrant HM",2,f("2.399").sub(".649"));
check("extra negative axis after quarter",2,f("2.598").sub(f(".85").mul("1.623")));
check("positive-negative direct tail",f(".61").sub(".0378").add(".32988"),goal);
check("MH positive-positive and HM negative-negative tail",f(".93").sub(".0378").add(".32988").sub(".321454"),goal);
check("MH negative-negative and HM positive-positive tail",f("1.42").sub(".0378").sub(".48080"),goal);
check("all signs after 1.71",f(".91").mul("1.71").add(f(".09").mul(pi.lo).div(2)).sub(".48080").sub(".321454"),goal);
check("contact enlarged arc lower radial coordinate",Q.mul(2).sub(f(".8").pow(2)),f("2.68").pow(2));
check("contact enlarged arc upper radial coordinate",f("2.682").pow(2),Q.mul(2).sub(f(".8").pow(2)));
check("contact H slope upper",".3",f(".8").div("2.68"));
check("contact marker increasing",v.sub(u.mul(".3")));
check("H target contact at zero",i(".649").add(a0.mul(".9798")),"2.02");
check("H target contact at .8",f(2).add(f(".9798").mul(".8")),f("1.028").add(f("1.02").mul("1.682")));
check("H source contact at .8",f(2).sub(f("1.02").mul("1.714")).add(f(".9798").mul(".685")),f("1.682").sub(".8"));
check("H source contact at zero",a0,i("2.02").sub(a2.mul(".9798")).add(b2.mul("1.02")));
check("H target before-quarter derivative",v.sub(u.mul(".3")).mul("2.64"),"1.09");
check("H target after-quarter derivative",".91",v.mul("1.616").div(".9798"));
check("H source before-quarter derivative",v.sub(u.mul(".3")).mul(".9798").mul("3.398").div("1.3"),"1.09");
check("H source after-quarter derivative",".91",v.mul("1.7085"));
check("aligned contact concavity",f(".744").div(f("3.6").pow(3)),f(".285").div(f("3.18").pow(3)));
check("aligned first radical upper",f("3.6").pow(2),Q.mul(4).sub(f("1.649").pow(2)));
check("aligned second radical lower",Q.mul(4).sub(f("2.351").pow(2)),f("3.18").pow(2));
for(const [name,d,threshold] of [["M first",a1.sub(b1),".89921"],["M last",a2.sub(b2),".89273"]]){
 const T1=i(Q.mul(4)).sub(d.add(1).sq()).sqrt(),T2=i(Q.mul(4)).sub(i(3).sub(d).sq()).sqrt();
 const J=pi.div(4).sub("2.2122495").add(a0.mul(u)).add(d.mul(".5946665")).add(T1.mul(".7447965")).sub(T2.mul(".284736"));
 check("aligned "+name,J,threshold);aligned.push({name,value_lower:J.lo.str()});
}
return {status:"PASS",checks,aligned};
})(rational,intervals);
const endpoints = ((rt,it) => {

const {f,sqrtUp,floorScaled}=rt,{i,pi,sincos}=it;
const Q=f("9789/2500"),R=i("2.79842813","2.79842814"),a0=R.sub(1),a1=i("1.71322294","1.71322295"),b1=a1.mul(".4"),a2=i("1.62343405","1.62343407"),b2=a2.mul(".6");
const u=f(".089293"),v=f(".480179"),k=f("1.534906"),q=f(".045313"),goal=f(".8926"),cm=pi.div(4).add("2.143075");
const ends={H:[[a0,i(0)],[a1,b1]],M:[[a1,b1],[a2,b2]]},lab={H:[a0.mul(u).neg(),u,v],M:[cm,k.neg(),q]};
const checks=[],endpointRows=[];
function check(name,lhs,rhs=0){let z=i(lhs).sub(rhs);if(z.lo.cmp(0)<=0)throw Error(name+" "+z.lo.val());checks.push({name,margin:z.lo.str()});}
function signSupport(kind,U,V,where){
 if(where==="circle"){let nu=sqrtUp(U.sq().add(V.sq()).hi);return {val:U.neg().sub(R.mul(nu)),norm:nu.str()};}
 let [a,b]=ends[kind][where==="a"?0:1];return {val:U.mul(a).add(V.mul(b))};
}
function endpoint(name,xkey,ii,jj,ss,tt,lam,src,tar){
 const la=f(lam),{x,s,c}=sincos(xkey),C=s.add(c),D=s.sub(c);
 const W2=xkey==="pi/2+.02"||xkey==="1.71"?i(1).add(s).sub(c):i(1).add(s).add(c);
 const [ci,pj0,qj0]=lab[ii],[cj,pj,qj]=lab[jj];
 const U1=i(pj0).mul(ss).sub(la),V1=i(qj0).sub(la).mul(ss);
 const U2=i(pj).mul(-tt).sub(D.mul(la)),V2=C.mul(la).sub(qj).mul(tt);
 const sv=signSupport(ii,U1,V1,src),tv=signSupport(jj,U2,V2,tar);
 const bound=x.sub(W2.sub(2).mul(".09")).add(W2.mul(la)).add(ci.mul(ss)).sub(cj.mul(tt)).add(sv.val).add(tv.val);
 check(name+" at "+xkey,bound,goal);
 endpointRows.push({name,x:xkey,lower_numerator_over_1e8:floorScaled(bound.lo).toString(),norm_upper:[sv.norm,tv.norm].filter(Boolean)});
}
for(const x of [".7",".93"])endpoint("MH ++",x,"M","H",1,1,".35","a","circle");
for(const x of [".1",".61"])endpoint("MH +-",x,"M","H",1,-1,".55","circle","b");
for(const src of ["a","b"]){
 endpoint("MH -- early "+src,".9","M","H",-1,-1,".4",src,"b");
 for(const x of ["1.2","1.42"])endpoint("MH -- late "+src,x,"M","H",-1,-1,".4",src,"circle");
 for(const x of ["1.2","1.3"])endpoint("MH -+ early "+src,x,"M","H",-1,1,".4",src,"a");
 for(const x of ["1.3","pi/2-.02"])endpoint("MH -+ before "+src,x,"M","H",-1,1,".4",src,"circle");
 endpoint("MH -+ after "+src,"pi/2+.02","M","H",-1,1,".4",src,"circle");
}
for(const x of ["1.1","1.42"])endpoint("HM ++",x,"H","M",1,1,".5","circle","a");
for(const tar of ["a","b"]){
 for(const x of ["1.3","pi/2-.02"])endpoint("HM -+ before "+tar,x,"H","M",-1,1,".4","circle",tar);
 endpoint("HM -+ after "+tar,"pi/2+.02","H","M",-1,1,".4","circle",tar);
}
// All eight positive-frame impossibility barriers.
for(const [name,x,K,A,B] of [
 ["MH++",".7",a2.add(b2).sub(1),a0.sub(1),a0.add(1)],
 ["MH+-",".1",a2.add(b2).sub(1),a1.add(b1).sub(1),a1.sub(b1).add(1)],
 ["MH--",".9",a1.sub(b1).sub(1),a1.add(b1).sub(1),a1.sub(b1).add(1)],
 ["MH-+","1.2",a1.sub(b1).sub(1),a0.sub(1),a0.add(1)],
 ["HM++","1.1",a1.add(b1).sub(1),a1.sub(b1).sub(1),a1.add(b1).add(1)],
 ["HM+-",".1",a1.add(b1).sub(1),a2.add(b2).sub(1),a2.sub(b2).add(1)],
 ["HM--",".4",a0.sub(1),a2.add(b2).sub(1),a2.sub(b2).add(1)],
 ["HM-+","1.3",a0.sub(1),a1.sub(b1).sub(1),a1.add(b1).add(1)]
]){
 const {s,c}=sincos(x);check(name+" impossible margin",B.mul(c),K.add(A.mul(s)));check(name+" barrier increasing",A);
}
// Support choices whose signs do not alone decide the endpoint.
check("MH++ source increases",k.add(".35").mul(".252").add(q),".35");
for(const x of [".9","1.2"]){let {s,c}=sincos(x);check("MH-- target cut derivative "+x,s.mul(".747").add(c.mul("1.253")).mul(".4"),v.sub(u.mul(".253")));}
let f11=sincos("1.1"),f142=sincos("1.42");
check("HM++ target radial coefficient",k,f(".5").mul("1.42"));
check("HM++ target increases",f142.s.add(f142.c).mul(".5").sub(q),i(k).sub(f11.s.sub(f11.c).mul(".5")).mul(".372"));
let f13=sincos("1.3");check("MH-+ early target transverse coefficient",f13.s.add(f13.c).mul(".4"),v);
check("HM+- early target cut derivative",f(".492").mul(f("1.372").mul(".91").add(f(".628").mul(".099"))),k.mul(".372").add(q));
check("HM-- target cutoff product decreasing",f(".365"),f(".494").mul(".095"));
let f04=sincos(".4");check("HM-- derivative bound .095",f(".095"),f(".628").sub(f("1.372").mul(f04.s.lo)));
let f06=sincos(".6");check("HM-- target cut at .6",f06.c.mul("1.372").add(f06.s.mul(".628")).mul(".421"),k.mul(".372").add(q));
check("HM-- target cutoff product at least one",f06.c.mul("1.372"),1);
// Generic trigonometric scalar endpoint rules.
function AB(kind,end,tau,lam,after=false){let [a,b]=ends[kind][end==="a"?0:1],la=f(lam);return [
 (after?a.add(b.mul(tau)).sub(1).mul(la).add(".09"):i(1).add(a).add(b.mul(tau)).mul(la).sub(".09")),
 i(1).sub(a).add(b.mul(tau)).mul(la).sub(".09")];}
function noInterior(name,kind,end,tau,lam,right){let [A,B]=AB(kind,end,tau,lam),{s,c}=sincos(right);check(name+" A positive",A);check(name+" B negative",B.neg());check(name+" right derivative negative",A.mul(s).sub(B.mul(c)),1);}
noInterior("MH+-","H","b",-1,".55",".61");
noInterior("MH-+ early","H","a",1,".4","1.3");
noInterior("HM++","M","a",1,".5","1.42");
noInterior("HM-+ first endpoint","M","a",1,".4","pi/2-.02");
let [Amm,Bmm]=AB("H","b",-1,".4");check("MH-- early increasing",1,Amm.sq().add(Bmm.sq()));
let [Amp,Bmp]=AB("M","b",1,".4");check("HM-+ last endpoint concave A",Amp);check("HM-+ last endpoint concave B",Bmp);
for(const end of ["a","b"]){let [A,B]=AB("M",end,1,".4",true);check("HM-+ after increasing "+end,1,A.sq().add(B.sq()));}
// The three target-H radical scalars are concave.
for(const [name,lam,tau,left,right,nmax] of [
 ["MH++",".35",1,".7",".93",".17"],
 ["MH-- late",".4",-1,"1.2","1.42",".3"],
 ["MH-+ before",".4",1,"1.3","pi/2",".497"]
]){
 const la=f(lam),L=sincos(left),U=sincos(right),C=U.s.add(U.c),D=U.s.sub(U.c);
 const Nsq=i(u).mul(tau).add(D.mul(la)).sq().add(C.mul(la).sub(v).sq());
 // For tau=-1, the first vector component is -u+lambda D;
 // its square is (u-lambda D)^2 as required.
 check(name+" norm maximum",f(nmax).pow(2),Nsq);
 if(tau===1)check(name+" norm increasing",L.s.mul(u.add(v)),L.c.mul(v.sub(u)));
 else check(name+" norm increasing",L.s.mul(v.sub(u)),L.c.mul(u.add(v)));
 check(name+" circle concavity",L.s.mul(la.mul(2).sub(".09")),L.c.mul(".09").add(R.mul(nmax).div(4)));
}
check("MH-+ after norm lower",u.add(".4").pow(2).add(v.sub(".4").pow(2)),f(".4958").pow(2));
check("MH-+ after increasing",f(1).add(f(".71").mul(".85")),R.mul(".4").mul(v.sub(u).mul(".14").add(u).add(v)).div(".4958"));
let f171=sincos("1.71");check("sin1.71 lower",f171.s,".99");check("cos1.71 lower",f171.c,"-.14");
return {status:"PASS",checks,endpointRows};

})(rational,intervals);
const polynomial = ((rt) => {

const {F,f,add,mul,scale,bern,trig,sqrtUp,floorScaled,bin}=rt;
const Q=f("9789/2500"),u=f(".089293"),v=f(".480179"),k=f("1.534906"),q=f(".045313"),gamma=f(".8926"),Rlo=f("2.79842813"),Rhi=f("2.79842814"),a0hi=Rhi.sub(1),a2lo=f("1.62343405"),a2hi=f("1.62343407"),b2lo=a2lo.mul(".6"),b2hi=a2hi.mul(".6"),cmlo=f("3.14159").div(4).add("2.143075"),LMlo=cmlo.sub(k.mul(a2hi)).add(q.mul(b2lo)),X=[f(0),f(1)];
const S5=trig(5,true),S7=trig(7,true),S9=trig(9,true),C6=trig(6,false),C8=trig(8,false),C10=trig(10,false),rows=[],checks=[];
function check(name,lhs,rhs=0){let d=f(lhs).sub(rhs);if(d.cmp(0)<=0)throw Error(name+": "+d.str());checks.push({name,margin:d.str()});}
function row(name,lo,hi,T,V,degree,display){
 let P=add(mul(T,T),scale(V,Q.mul(-2))),bb=bern(P,lo,hi);
 while(bb.length<degree+1){let n=bb.length-1,old=bb;bb=Array.from({length:n+2},(_,j)=> (j?old[j-1].mul(new F(BigInt(j),BigInt(n+1))):f(0)).add(j<=n?old[j].mul(new F(BigInt(n+1-j),BigInt(n+1))):f(0)));}
 if(bb.length!==display.length)throw Error(name+" coefficient count");
 for(let j=0;j<bb.length;j++){check(name+" coefficient "+j,bb[j],new F(BigInt(display[j]),100000000n));if(BigInt(display[j])<=0n)throw Error("nonpositive display");}
 rows.push({name,interval:[lo,hi],polynomial_degree:P.length-1,bernstein_degree:degree,denominator:100000000,lower_numerators:display,T:T.map(x=>x.str()),P:P.map(x=>x.str()),exact_bernstein:bb.map(x=>x.str())});
}
for(const [name,lo,hi,sgn,lambda,degree,display,tmin] of [
 ["HM +- early",".1",".42",1,[".66","-.4"],14,[16425573,14694001,13058820,11525877,10099227,8781206,7572516,6472316,5478331,4586958,3793384,3091710,2475074,1935778,1465421],".05"],
 ["HM -- main",".4",".6",-1,[".64","-.365"],20,[2790748,2431170,2097554,1789715,1507438,1250488,1018601,811493,628858,470370,335684,224438,136252,70733,27473,6052,6038,26991,68459,129986,211107],".64"]
]){
 let L=lambda.map(f),A=add(scale(L,f(1).add(a2lo).sub(b2hi)),[f("-.09")]),B=add(scale(L,f(1).sub(a2hi).sub(b2hi)),[f("-.09")]);
 let K=f(".09").add(LMlo).sub(gamma).sub(u.mul(sgn>0?Rhi:Rlo).mul(sgn));
 let T=add(X,[K],scale(L,2),mul(A,C6),mul(B,S5));
 let V=add(mul(add(L,[u.mul(-sgn)]),add(L,[u.mul(-sgn)])),mul(add(L,[v.neg()]),add(L,[v.neg()])));
 row(name,lo,hi,T,V,degree,display);
 const lmin=f(lambda[0]).add(f(lambda[1]).mul(hi)),lmax=f(lambda[0]).add(f(lambda[1]).mul(lo));
 check(name+" cosine coefficient positive",lmin.mul(f(1).add(a2lo).sub(b2hi)).sub(".09"));
 check(name+" sine coefficient negative",f(".09").sub(lmax.mul(f(1).sub(a2hi).sub(b2hi))));
 // A C6 is nonnegative; B S5 >= B_min*hi.
 const Bmin=lmax.mul(f(1).sub(a2hi).sub(b2hi)).sub(".09");
 check(name+" T positive",f(lo).add(K).add(lmin.mul(2)).add(Bmin.mul(hi)),tmin);
}
for(const [name,lo,hi,ls,source,display] of [
 ["HM +- late",".42",".61",".43","endpoint",[1993448,2363210,2711713,3040020,3349187,3640262,3914285,4172290,4415303,4644341,4860415,5064530,5257681,5440858,5615045,5781215,5940339]],
 ["HM -- bridge",".6",".7",".42","circle",[566759,745406,922183,1097234,1270698,1442715,1613426,1782968,1951483,2119106,2285977,2452232,2618009,2783444,2948672,3113829,3279051]],
 ["HM -- late",".7",".93",".4","circle",[5120799,5999068,6880379,7766355,8658605,9558729,10468314,11388938,12322168,13269562,14232666,15213020,16212155,17231593,18272847,19337427,20426832]]
]){
 const la=f(ls);
 let K=f(".09").add(cmlo).add(k).add(la).sub(la.mul(a0hi)).sub(gamma),Ns;
 if(source==="circle"){Ns=sqrtUp(u.add(la).pow(2).add(v.sub(la).pow(2)));K=f(".09").add(cmlo).add(k).add(la.mul(2)).add(u.mul(Rlo)).sub(Rhi.mul(Ns)).sub(gamma);}
 const T=add(X,[K],scale(S7,la.mul(2).sub(".09")),scale(C8,"-.09"));
 const V=add([k.pow(2).add(q.pow(2)).add(la.pow(2).mul(2))],scale(S9,la.mul(2).mul(k.sub(q))),scale(C10,la.mul(-2).mul(k.add(q))));
 row(name,lo,hi,T,V,16,display);check(name+" T positive",f(lo).add(K).sub(".09"));
}
return {status:"PASS",checks,rows};

})(rational);
const result={status:"PASS",strict_comparisons:geometry.checks.length+endpoints.checks.length+polynomial.checks.length,bernstein_coefficients:polynomial.rows.reduce((n,r)=>n+r.lower_numerators.length,0),scalar_endpoints:endpoints.endpointRows.length,geometry,endpoints,polynomial};
if (typeof console !== "undefined") console.log(JSON.stringify(result,null,2));
