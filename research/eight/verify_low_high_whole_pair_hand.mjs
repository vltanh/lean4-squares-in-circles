// Exact arithmetic replay for LOW_HIGH_WHOLE_PAIR_HAND_PROOF.md.
// Run: node verify_low_high_whole_pair_hand.mjs
// Fixed comparisons only; no search, subdivision, or external dependencies.
const rational=(()=>{

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
const intervals=((tools)=>{

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
const extension=((it)=>{

const {i,pi,sincos}=it;
function sc(x){if(x==="q")return {x:pi.div(2),s:i(1),c:i(0)};if(x.startsWith("q+")||x.startsWith("q-")){let sg=x[1]==="+"?1:-1,a=sincos(x.slice(2));return {x:pi.div(2).add(a.x.mul(sg)),s:a.c,c:a.s.mul(-sg)};}if(x.startsWith("-")){let a=sincos(x.slice(1));return {x:a.x.neg(),s:a.s.neg(),c:a.c};}return sincos(x);}
return {sc};
})(intervals);
const geometry=((rt,it,ext)=>{

const {f}=rt,{i,pi}=it,{sc}=ext;
const Q=f("9789/2500"),R=i("1.978787507","1.978787508"),cg=i(".899214065",".899214066"),a0=i("1.414575670","1.414575672"),aL=i("1.298747247","1.298747249"),bL=aL.div(4),aH=i("1.199256060","1.199256062"),bH=aH.mul("3/7");
const mu=f(".403875"),q=f("1.089065"),k=f(".569472"),v=f(".390886"),K=k.add(v),goal=f(".8833"),eps=f(".00001"),cL=a0.mul(mu).neg(),cH=pi.div(4).add(cg.mul(k.sub(v))),cU=pi.div(4).sub(cg.mul(k.sub(v)));
const checks=[],values=[];
function check(name,lhs,rhs=0){let d=i(lhs).sub(rhs);if(d.lo.cmp(0)<=0)throw Error(name+" "+d.lo.str());checks.push({name,margin:d.lo.str()});}
function rad(b){return i(Q).sub(i(b).add(".5").sq()).sqrt().sub(".5");}
function rr(b){b=i(b);return b.add(".5").div(rad(b).add(".5"));}
function low(b){return cL.add(rad(b).mul(mu)).add(i(b).mul(q));}
function high(b){return cH.sub(rad(b).mul(k)).add(i(b).mul(v));}
function upper(b){return cU.sub(rad(b).mul(v)).add(i(b).mul(k));}
function arcCheck(name,aa,t){const evalp=a=>a.add(".5").pow(2).add(a.mul(t).add(".5").pow(2));check(name+" lower",Q,evalp(aa.lo));check(name+" upper",evalp(aa.hi),Q);}
check("radius lower",Q,R.lo.pow(2));check("radius upper",R.hi.pow(2),Q);
check("diagonal lower",Q.div(2),cg.lo.add(".5").pow(2));check("diagonal upper",cg.hi.add(".5").pow(2),Q.div(2));
arcCheck("low axial endpoint",a0,0);arcCheck("low cut",aL,"1/4");arcCheck("high cut",aH,"3/7");
const EL=cL.add(aL.mul(mu)).add(bL.mul(q)),EH=cH.sub(aH.mul(k)).add(bH.mul(v));
check("low marker maximum",".30683",EL);check("high marker minimum",EH,".46394");
check("low marker positive derivative",q,mu);check("low slope upper",".46",bL.add(".5").div(aL.add(".5")));
check("low slope lower",i(".5").div(a0.add(".5")),".26");
check("high slope lower",bH.add(".5").div(aH.add(".5")),".596");
check("epsilon source support",EL.sub(bL.mul(".945")),eps.neg());
check("low negative source first for lambda 1",f(1).sub(q).add(mu.mul(".26")));
check("low negative source first for lambda 1.02",f("1.02").sub(q).add(mu.mul(".26")));
check("low primary source cut lambda .9",q,mu.add(".9").mul(".46"));
check("low primary source cut lambda .7",q,mu.add(".7").mul(".46"));
const at25=f(".25").sub(f(".25").pow(3).div(3)).add(f(".25").pow(5).div(5));
check("low tangent angle .246",".246",at25);check("quarter angle .786",".786",pi.div(4));
check("high negative source secondary impossible",1,f("1.415").sub(".513"));
check("whole negative primary angle impossible",1,f("1.2").sub(f("1.298").mul(f(1).sub(f(".272").pow(2).div(2)))).add(f(".325").mul(".272")));
const s12=sc("1.2");check("high primary first quadrant barrier at1.2",s12.c.mul("1.798").add(s12.s.mul(".175")),".7");
check("high primary first quadrant barrier at0",f("1.798"),".7");
check("negative lower-high contact derivative",f(".73").mul(f("1.798").mul(f(1).sub(f(".272").pow(2).div(2))).sub(f(".5").mul(".272"))),"1.09");
check("lower-high label derivative floor",v.add(k.mul(".596")),".73");
const negP=f("1.798").mul(".92").sub(".2");
check("negative upper-high opposite-target contact derivative",K.mul(negP),"1.09");
check("negative upper-high diagonal continuation",q.sub(mu.mul(".46")).mul(negP).div(f(1).add(f(".46").mul(".4"))),"1.09");
check("negative upper-high positive-target contact derivative",K.mul(f("1.798").mul(".92").sub(f(".825").mul(".4"))),"1.09");
check("upper-high axial label derivative at1",i(k).add(rr(1).mul(v)),"1.023");
check("low axial derivative upper",".985",q.sub(mu.mul(".26")));
check("upper-high opposite-target direct tail",pi.div(4).add(f(".91").mul(".108")),goal);
check("upper-high positive-target direct tail",pi.div(4).add(".46").sub(".30683").sub(".0378"),goal);
check("lower-high opposite-target direct tail",f(".46").add(".46394").sub(".0378"),goal);
check("lower-high positive-target direct tail",f(".77").add(".46394").sub(".30683").sub(".0378"),goal);
check("low-high two-negative direct tail",f(".8").sub(".30683").add(".46394").sub(".0378"),goal);
check("low-high primary positive-target direct tail",i("2.02").sub(".30683").sub(pi.div(4)).sub(".0378"),goal);

// Derivative bounds for the lower-high contact reduction.
check("low arc rprime upper",f(".675").mul(f("1.798").pow(3)),Q);
check("normal high Gsecond lower",k.mul(Q),f(".453").mul(f("1.7").pow(3)));
check("lower-high contact transverse convexity",f(".453").mul(f(".888").pow(2)).sub(mu.mul(".675")),".08");
const s02=sc(".2");check("lower-high transverse derivative after .2",i(q.sub(mu.mul(".46"))).sub(s02.c.mul(K)).add(s02.s.mul(K.mul(".26"))));
const L0prime=i(q).sub(i(".5").div(a0.add(".5")).mul(mu));
check("lower-high axial transverse derivative",L0prime,K);
const s011=sc(".11"),s046=sc(".46");
function axialZ(x){const {s,c}=sc(x);return i(".5").add(c.mul(".5")).add(i(".5").sub(a0).mul(s));}
check("normal-high axial starts below diagonal",cg,axialZ(".11"));
check("normal-high axial ends above high cut",axialZ(".46"),bH);
check("axial P above .96",a0.sub(".5").mul(s011.c).add(s011.s.mul(".5")),".96");
check("axial Pprime below .398",".398",s011.c.mul(".5").sub(a0.sub(".5").mul(s011.s)));
check("axial P increasing through .46",s046.c.mul(".5"),a0.sub(".5").mul(s046.s));
check("normal-high axial strong convexity",f(".09").add(f(".453").mul(f(".96").pow(2))).sub(K.mul(".398")),".12");
function axialData(x,which){
 const {x:xx,s,c}=sc(x),z=axialZ(x),a=rad(z),r=z.add(".5").div(a.add(".5")),P=a0.sub(".5").mul(c).add(s.mul(".5"));
 const G=which==="normal"?high(z):upper(z),gp=which==="normal"?i(v).add(r.mul(k)):i(k).add(r.mul(v));
 return {F:xx.sub(s.add(c).sub(1).mul(".09")).add(G),Fp:i(1).sub(c.sub(s).mul(".09")).sub(gp.mul(P)),z,r,P,gp};
}
const axialN=axialData(".115","normal");
check("normal axial reference value",axialN.F,".88352");
check("normal axial reference derivative lower",axialN.Fp,"-.001");
check("normal axial reference derivative upper",".001",axialN.Fp);
check("normal axial completed-square cost",f(".88352").sub(f(".001").pow(2).div(".24")),goal);
values.push({name:"normal axial reference .115",lower:axialN.F.lo.str(),derivative:[axialN.Fp.lo.str(),axialN.Fp.hi.str()]});
// The extended diagonal-contact curve B(x) on 0 <= x <= .11.
const bdiagLo=f("-.002731159"),bdiagHi=f("-.002731156");
function diagMargin(b,x){let {s,c}=sc(x);return rad(b).mul(s).add(i(b).mul(c)).sub(i(".5").add(s.add(c).mul(".5")).sub(cg));}
check("diagonal root lower at .11",diagMargin(bdiagLo,".11").neg());
check("diagonal root upper at .11",diagMargin(bdiagHi,".11"));
check("diagonal root stays above -.003",diagMargin("-.003",".11").neg());
check("diagonal root stays below .101",i(".101").sub(i(1).sub(cg)));
check("diagonal low primary lower",rad(".101"),"1.385");
check("diagonal low primary upper","1.416",rad("-.003"));
check("diagonal low slope lower",rr("-.003"),".259");
check("diagonal low slope upper",".319",rr(".101"));
check("diagonal low rprime upper",f(".59").mul(f("1.885").pow(3)),Q);
check("diagonal P lower",f(".885").mul(f(1).sub(f(".11").pow(2).div(2))),".87");
check("diagonal P upper",".972",f(".916").add(f(".503").mul(".11")));
check("diagonal Bprime upper magnitude","1.02",f(".972").div(f(1).sub(f(".11").pow(2).div(2)).sub(f(".319").mul(".11"))));
const diagBpp=f("-.399").sub(f(2).mul(".259").mul(f(1).sub(f(".11").pow(2).div(2))).mul(".87")).add(f(".59").mul(".11").mul(f("1.02").pow(2)));
check("diagonal Bsecond less than -.77","-.77",diagBpp);
check("diagonal low marker derivative floor",q.sub(mu.mul(".319")),".95");
check("diagonal contact concavity",f(".95").mul(".77"),f(".09").mul("1.11"));
const bd=i(bdiagLo,bdiagHi),diagEnd=s011.x.sub(s011.s.add(s011.c).sub(1).mul(".09")).add(pi.div(4)).add(low(bd));
check("diagonal contact at .11",diagEnd,".88337");
values.push({name:"diagonal contact at .11",lower:diagEnd.lo.str()});
// Upper-high axial extension, used on several boundary pieces.
check("upper axial primary at .11 below .903",".903",rad(axialZ(".11")));
check("upper axial primary at0 above .79",rad(1),".79");
check("upper axial Gsecond lower",v.mul(Q),f(".55").mul(f("1.403").pow(3)));
check("upper axial Gprime upper","1.025",i(k).add(i("1.5").div("1.29").mul(v)));
check("upper axial curvature positive",f(".09").add(f(".55").mul(f(".9145").pow(2))).sub(f("1.025").mul(".5")));
const axialU=axialData(".11","upper");check("upper axial right derivative negative",axialU.Fp.neg());check("upper axial right value",axialU.F,".88353");
values.push({name:"upper axial at .11",lower:axialU.F.lo.str(),derivative_upper:axialU.Fp.hi.str()});
const s008=sc(".08"),r0=i(".5").div(a0.add(".5"));
check("low r0 below .262",".262",r0);
check("upper positive-target D0 increasing",s008.c.mul(".26"),".08");
check("upper positive-target F_B(0) decreases",f(".55").mul(".9145"),f("1.025").mul(".262"));
const ax08=axialData(".08","upper"),D08=s008.c.add(r0.mul(s008.s));
check("upper positive-target axial transverse derivative at .08",ax08.gp.mul(D08),L0prime);

// The upper-high / negative-low contact Hessian, 0 <= x <= .108.
check("Hessian high primary above .79",rad(1),".79");
check("Hessian Gsecond upper",f(".714").mul(f("1.29").pow(3)),v.mul(Q));
check("Hessian Gsecond lower",v.mul(Q),f(".55").mul(f("1.4").pow(3)));
check("Hessian low rprime lower",Q,f(".55").mul(f("1.915").pow(3)));
check("Hessian P lower",f(".885").mul(f(1).sub(f(".108").pow(2).div(2))),".879");
check("Hessian P upper",".969",a0.hi.sub(".5").add(f(".5").mul(".108")));
check("Hessian D lower",f(1).sub(f(".108").pow(2).div(2)).sub(f(".319").mul(".108")),".959");
check("Hessian E lower",f(".26").mul(f(1).sub(f(".108").pow(2).div(2))),".258");
const FxxMax=f(".09").mul("1.108").add(f(".714").mul(f(".969").pow(2))).sub(K.mul(".399"));
const FbbMax=f(".714").add(f("1.025").mul(".59").mul(".108")).sub(mu.mul(".55"));
const FbbMin=f(".55").mul(f(".959").pow(2)).sub(mu.mul(".59"));
const FxbMin=f(".55").mul(".879").mul(".959").add(K.mul(".258"));
check("Hessian Fxx upper .4",".4",FxxMax);check("Hessian Fbb upper .6",".6",FbbMax);
check("Hessian Fbb positive",FbbMin,".26");check("Hessian Fxb lower .7",FxbMin,".7");
check("Hessian determinant negative",f(".7").pow(2),f(".4").mul(".6"));
return {status:"PASS",checks,values};

})(rational,intervals,extension);
const support=((rt,it,ext)=>{

const {f,sqrtUp,floorScaled}=rt,{i,pi}=it,{sc}=ext;
const Q=f("9789/2500"),R=i("1.978787507","1.978787508"),cg=i(".899214065",".899214066"),a0=i("1.414575670","1.414575672"),aL=i("1.298747247","1.298747249"),bL=aL.div(4),aH=i("1.199256060","1.199256062"),bH=aH.mul("3/7");
const mu=f(".403875"),q=f("1.089065"),k=f(".569472"),v=f(".390886"),K=k.add(v),goal=f(".8833"),eps=f(".00001");
const ends={L:[[a0,i(0)],[aL,bL]],H:[[aH,bH],[cg,cg]]},lab={L:[a0.mul(mu).neg(),mu,q],H:[pi.div(4).add(cg.mul(k.sub(v))),k.neg(),v]};
const checks=[],endpoints=[];
function check(name,lhs,rhs=0){let z=i(lhs).sub(rhs);if(z.lo.cmp(0)<=0)throw Error(name+" "+z.lo.str());checks.push({name,margin:z.lo.str()});}
function abs(z){return z.hi.cmp(0)<=0?z.neg():z;}
function endpoint(name,xkey,ii,jj,ss,tt,axis,lambda,src,tar){
 const la=f(lambda),{x,s,c}=sc(xkey),h=abs(s).add(abs(c)).sub(1).div(2),W=i(1).add(h);
 const [ci,pj0,qj0]=lab[ii],[cj,pj,qj]=lab[jj];
 let U1,V1,U2,V2;if(axis==="f"){U1=i(pj0).mul(ss);V1=i(qj0).sub(la).mul(ss);U2=i(pj).mul(-tt).sub(s.mul(la));V2=c.mul(la).sub(qj).mul(tt);}
 else {U1=i(pj0).mul(ss).sub(la);V1=i(qj0).mul(ss);U2=i(pj).mul(-tt).add(c.mul(la));V2=s.mul(la).sub(qj).mul(tt);}
 function support(kind,U,V,which,isSource){if(which==="eps")return i(eps).neg().sub(ci.mul(ss));if(which==="o")return U.add(V).div(2).neg().sub(R.mul(sqrtUp(U.sq().add(V.sq()).hi)));const [a,b]=ends[kind][which==="a"?0:1];return U.mul(a).add(V.mul(b));}
 const F=x.sub(h.mul(".18")).add(W.mul(la)).add(ci.mul(ss)).sub(cj.mul(tt)).add(support(ii,U1,V1,src,true)).add(support(jj,U2,V2,tar,false));
 check(name+" endpoint "+xkey,F,goal);endpoints.push({name,x:xkey,lower_numerator_over_1e8:floorScaled(F.lo).toString()});
}
endpoint("LH primary negative target",".6","L","H",-1,-1,"e",".7","b","o");
for(const end of ["a","b"])for(const x of ["q","q+.45"])endpoint("LH primary positive target "+end,x,"L","H",-1,1,"e",".9","b",end);
for(const x of ["1.35","q","2.02"])endpoint("LH negative-positive secondary",x,"L","H",-1,1,"f","1.02","a","o");
for(const x of ["1.1","1.35"])endpoint("LH positive-positive cut",x,"L","H",1,1,"f",".945","eps","a");
for(const x of ["1.35","q-.02"])endpoint("LH positive-positive circle",x,"L","H",1,1,"f",".945","eps","o");
endpoint("LH positive-positive after quarter","q+.02","L","H",1,1,"f",".945","eps","b");
endpoint("LH opposite signs negative frame","-.02","L","H",1,-1,"f",".945","eps","b");
for(const x of [".02",".46"])endpoint("LH opposite signs positive frame",x,"L","H",1,-1,"f",".945","eps","o");
// All source/target support choices and initial impossibility ranges.
const x08=sc(".08"),x03=sc(".3"),x06=sc(".6"),x08b=sc(".8"),x11=sc("1.1"),x135=sc("1.35"),x045=sc(".45");
check("HL positive target initial barrier",i(".5").add(x08.c.mul(".5")),cg.add(a0.sub(".5").mul(x08.s)));
check("LH negative negative initial barrier",".5",cg.sub(".5").mul(x03.s.add(x03.c)));
check("LH negative positive initial barrier",i(".5").add(bH.add(".5").mul(x135.c)),aH.sub(".5").mul(x135.s));
check("LH positive positive initial barrier",i(".5").add(bH.add(".5").mul(x11.c)),bL.add(aH.sub(".5").mul(x11.s)));
check("LH primary negative target initial barrier",cg.add(".5").mul(x06.c),a0.sub(".5").add(cg.sub(".5").mul(x06.s)));
check("LH primary positive target first quadrant impossible","1.013",a0.sub(".5"));
check("LH primary all negative frames impossible",1,f("1.415").sub(f(".899").mul(f(1).sub(f(".272").pow(2).div(2)))).add(f(".9").mul(".272")));
check("LH primary negative-target scalar increasing",i(1).add(x08b.c.mul(".61")).add(x06.s.mul(".09")),R.mul(".7"));
check("LH primary positive-target radial coefficient",k,x045.s.mul(".9"));
for(const [name,A,B] of [["first",aH,bH],["last",cg,cg]]){
 const ca=B.mul(".9").add(".36"),sa=i(".36").sub(A.mul(".9"));
 check("LH primary positive-target concavity "+name,ca.mul(x045.c),sa.neg().mul(x045.s));
}
check("LH positive-positive target convex",x11.s.mul(".945"),k);
check("LH positive-positive target first derivative",x135.s.mul(".596").add(x135.c).mul(".945"),k.mul(".596").add(v));
const d=f(".3825"),A=bH.mul(".945").add(d),B=i(d).sub(aH.mul(".945"));
check("LH positive-positive scalar cos coefficient",A);check("LH positive-positive scalar sin coefficient",B.neg());
check("LH positive-positive scalar right derivative negative",A.mul(x135.s).sub(B.mul(x135.c)),1);
const x002=sc(".02");
check("LH negative frame target diagonal derivative",x002.s.add(x002.c).mul(".945"),K);
check("LH negative frame cost increasing in absolute angle",cg.mul(".945").add(d).mul(f(1).sub(f(".272").pow(2).div(2))),1);
check("LH after-quarter target decreases",K,".945");
check("LH after-quarter scalar increases",1,cg.mul(".945").sub(d));

function N2(x,lam,tau){const {s,c}=sc(x),la=f(lam);return i(k).mul(tau).sub(s.mul(la)).sq().add(c.mul(la).sub(v).sq());}
check("positive target norm increases after 1.35",x135.s.mul(v),x135.c.mul(k));
for(const [name,lam,nmax] of [["negative source","1.02",".597"],["positive source",".945",".543"]]){
 check(name+" H norm quarter bound",f(nmax).pow(2),N2("q",lam,1));
 check(name+" first quadrant circle concavity",x135.s.mul(f(lam).sub(".09")),x135.c.mul(".09").add(R.mul(nmax).div(4)));
}
check("negative source second quadrant norm bound",f(".905").pow(2),N2("2.02","1.02",1));
check("negative source second quadrant concavity",".93",R.mul(".905").div(4));
check("opposite signs positive frame norm bound",f("1.2").pow(2),N2(".46",".945",-1));
check("opposite signs positive frame concavity",".855",R.mul("1.2").div(4));
return {status:"PASS",checks,endpoints};

})(rational,intervals,extension);
const polynomial=((rt)=>{

const {f,F,add,mul,scale,trig,bern,floorScaled,factorial}=rt;
const Q=f("9789/2500"),mu=f(".403875"),q=f("1.089065"),k=f(".569472"),v=f(".390886"),goal=f(".8833"),K=k.add(v),X=[f(0),f(1)],rows=[],checks=[];
function check(name,lhs,rhs=0){let d=f(lhs).sub(rhs);if(d.cmp(0)<=0)throw Error(name+" "+d.str());checks.push({name,margin:d.str()});}
function row(name,lo,hi,P,den,display){let bb=bern(P,lo,hi);if(bb.length!==display.length)throw Error(name+" degree mismatch");for(let j=0;j<bb.length;j++){check(name+" coefficient "+j,bb[j],new F(BigInt(display[j]),BigInt(den)));if(BigInt(display[j])<=0n)throw Error("nonpositive display");}rows.push({name,interval:[lo,hi],degree:P.length-1,denominator:den,lower_numerators:display,P:P.map(x=>x.str()),exact_bernstein:bb.map(x=>x.str())});}
for(const [name,lo,hi,ll,display] of [
 ["upper H positive L bridge",".08",".11",[".960358"],[36350,39352,42034,44398,46446,48180,49601,50711,51512,52005,52192,52075,51656,50936,49916,48599,46986]],
 ["upper H positive L main",".11",".46",["1.005","-.407"],[46907,23046,22603,48835,104890,193825,318639,482291,687724,937892,1235776,1584407,1986883,2446388,2966207,3549739,4200512]]
]){
 const la=ll.map(f),base=f(".09").add(f("3.14159").div(4)).add(mu.mul("1.414575670")).add(mu.add(q).div(2)).sub(goal);
 const T=add([base],X,scale(la,f(".5").sub(".899214066")),mul(add(la,[f("-.09")]),trig(7,true)),scale(trig(8,false),"-.09"));
 const V=add([mu.pow(2).add(q.pow(2))],mul(la,la),scale(mul(la,add(scale(trig(9,true),mu),scale(trig(10,false),q.neg()))),2));
 row(name,lo,hi,add(mul(T,T),scale(V,Q.neg())),100000000,display);
 const lmax=ll.length===1?la[0]:la[0].add(la[1].mul(lo)),lmin=ll.length===1?la[0]:la[0].add(la[1].mul(hi));
 check(name+" lambda positive",lmin);if(name.includes("main"))check(name+" lambda below diagonal derivative",K,lmax);
 check(name+" T positive",f(lo).add(base).add(f(".5").sub(".899214066").mul(lmax)).sub(".09"));
}
{
 const cHlo=f("3.14159").div(4).add(k.sub(v).mul(".899214065"));
 const T=add([f(".09").add(".5").add(cHlo).add(k.sub(v).div(2)).sub(goal)],X,scale(add(trig(7,true),trig(6,false)),".91"));
 const V=add([k.pow(2).add(v.pow(2)).add(1)],scale(trig(9,true),k.mul(2)),scale(trig(6,false),v.mul(-2)));
 row("L negative H negative secondary",".3",".8",add(mul(T,T),scale(V,Q.neg())),100000000,[57629693,64106927,70385371,76417041,82155685,87557161,92579804,97184758,101336287,105002051,108153349,110765317,112817092,114291931,115177288]);
 check("negative-negative scalar T positive",f(".3").add(".09").add(".5").add(cHlo).add(k.sub(v).div(2)).sub(goal));
}
{
 const L=[".990906","-.28"].map(f),w=["-.19","1"].map(f);
 function compose(co,base){let p=[f(0)];for(let c of co.slice().reverse())p=add(mul(p,base),[f(c)]);return p;}
 const U1=add(compose([".7895001401","-.1939323304",".0258329638",".0063465589",".0011353387"],w),[f(".000003")]);
 const U2=add(compose([".6048369308",".9594403346","-.2050884018","-.0610720222",".0449392223"],w),[f(".000001")]);
 const e=f(".00000003"),S=trig(9,true),C=trig(8,false);
 const X1=add([k.pow(2)],mul(add(L,[v.neg()]),add(L,[v.neg()])));
 const X2=add([mu.pow(2).add(q.pow(2))],mul(L,L),scale(mul(L,add(scale(S,mu),scale(C,q.neg()))),2));
 const V=add(X,scale(C,"-.09"),mul(add(L,[f("-.09")]),add(S,[e.neg()])),L,
 [f("3.14159").div(4).add(k.sub(v).mul(".899214")).add(mu.mul("1.414575")).add(k.sub(v).add(mu).add(q).add(".18").div(2)).sub(goal)],
 scale(add(U1,U2),"-1.978788"));
 row("high-low nonaligned extension norm1",".3",".77",add(mul(U1,U1),scale(X1,-1)),10000000000,[46107,45428,44692,43715,41998,38553,32151,22091,9625]);
 row("high-low nonaligned extension norm2",".3",".77",add(mul(U2,U2),scale(X2,-1),[e.mul(-3)]),10000000000,[14892,26291,72150,224495,650842,1676221,3836335,7920705,15005681,26478271,44052700]);
 row("high-low nonaligned extension cost",".3",".77",V,10000000000,[7887247,13045323,20098966,28832262,38936090,50011101,61569449,73035241,83743732,92939289,99772210]);
 check("extension cosine remainder",e,f(".77").pow(10).div(factorial(10)));
 check("extension sine remainder",e,f(".77").pow(11).div(factorial(11)));
 check("extension norm squared remainder factor",3,mu.add(q).mul(2));
 check("extension U1 positive",f(".7895001401").sub(f(".1939323304").mul(".58")));
 check("extension U2 positive",f(".6048369308").sub(f(".2050884018").mul(f(".58").pow(2))).sub(f(".0610720222").mul(f(".58").pow(3))));
 check("extension lambda positive",f(".990906").sub(f(".28").mul(".77")),".09");
}
return {status:"PASS",checks,rows};

})(rational);
const result={proof:"LOW_HIGH_WHOLE_PAIR_HAND_PROOF.md",status:"PASS",scope:"Whole L/H table entry .8833; sixteen ordered source-axis sign branches; reflected target axes included",comparison_count:geometry.checks.length+support.checks.length+polynomial.checks.length,geometry,support,polynomial};
if(typeof console!=="undefined")console.log(JSON.stringify(result,null,2));
