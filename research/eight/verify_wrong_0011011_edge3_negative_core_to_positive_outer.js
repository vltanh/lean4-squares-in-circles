"use strict";
// Exact fixed comparisons for the final whole mixed quarter-one family.
const arithmetic=(function(){

class F {
 constructor(n,d=1n){ n=BigInt(n); d=BigInt(d); if(d===0n)throw Error("zero denominator");if(d<0n){n=-n;d=-d}let a=n<0n?-n:n,b=d;while(b){let t=a%b;a=b;b=t;}this.n=n/a;this.d=d/a; }
 static of(x){if(x instanceof F)return x;if(typeof x==="string"&&x.includes("/")){let z=x.split("/");return new F(z[0],z[1])}if(typeof x==="string"&&x.includes(".")){let sign=x.startsWith("-")?-1n:1n;let z=x.replace("-","").split(".");return new F(sign*BigInt(z[0]+z[1]),10n**BigInt(z[1].length));}return new F(x)}
 add(y){y=F.of(y);return new F(this.n*y.d+y.n*this.d,this.d*y.d)}
 sub(y){y=F.of(y);return new F(this.n*y.d-y.n*this.d,this.d*y.d)}
 mul(y){y=F.of(y);return new F(this.n*y.n,this.d*y.d)}
 div(y){y=F.of(y);return new F(this.n*y.d,this.d*y.n)}
 neg(){return new F(-this.n,this.d)}
 pow(k){return k<0?new F(this.d**BigInt(-k),this.n**BigInt(-k)):new F(this.n**BigInt(k),this.d**BigInt(k))}
 cmp(y){y=F.of(y);let z=this.n*y.d-y.n*this.d;return z>0n?1:z<0n?-1:0}
 lt(y){return this.cmp(y)<0}gt(y){return this.cmp(y)>0}
 num(){return Number(this.n)/Number(this.d)}
 str(){return this.d===1n?String(this.n):this.n+"/"+this.d}
}
const f=x=>F.of(x);
const sum=a=>a.reduce((s,x)=>s.add(x),f(0));
const fac=n=>{let r=1n;for(let j=2;j<=n;j++)r*=BigInt(j);return r}
const choose=(n,k)=>fac(n)/(fac(k)*fac(n-k));
const trig=(x,kind,degree)=>{x=f(x);let s=f(0);for(let j=kind==="sin"?1:0;j<=degree;j+=2){let sg=((j-(kind==="sin"?1:0))/2)%2?-1n:1n;s=s.add(x.pow(j).mul(new F(sg,fac(j))))}return s};
const add=(a,b)=>Array.from({length:Math.max(a.length,b.length)},(_,i)=>(a[i]||f(0)).add(b[i]||f(0)));
const scale=(a,s)=>a.map(x=>x.mul(s));
const mul=(a,b)=>{let c=Array.from({length:a.length+b.length-1},()=>f(0));a.forEach((x,i)=>b.forEach((y,j)=>c[i+j]=c[i+j].add(x.mul(y))));return c};
const monomial=(n,c=1)=>{let a=Array.from({length:n+1},()=>f(0));a[n]=f(c);return a};
const trigpoly=(kind,degree)=>{let p=Array.from({length:degree+1},()=>f(0));for(let j=kind==="sin"?1:0;j<=degree;j+=2){let sg=((j-(kind==="sin"?1:0))/2)%2?-1n:1n;p[j]=new F(sg,fac(j))}return p};
const bern=(p,l,r)=>{l=f(l);r=f(r);const n=p.length-1,h=r.sub(l);let power=Array.from({length:n+1},()=>f(0));for(let i=0;i<=n;i++)for(let j=0;j<=i;j++)power[j]=power[j].add(p[i].mul(choose(i,j)).mul(l.pow(i-j)).mul(h.pow(j)));return power.map((_,k)=>sum(power.slice(0,k+1).map((v,j)=>v.mul(choose(k,j)).div(choose(n,j)))))};
return {F,f,sum,fac,choose,trig,add,scale,mul,monomial,trigpoly,bern};
})();
const {F,f,sum,fac,choose,trig,add,scale,mul,monomial,trigpoly,bern}=arithmetic;
const intervals=(function(){

const I=(l,h=l)=>[f(l),f(h)];
const ia=(x,y)=>{x=Array.isArray(x)?x:I(x);y=Array.isArray(y)?y:I(y);return[x[0].add(y[0]),x[1].add(y[1])];};
const ineg=x=>{x=Array.isArray(x)?x:I(x);return[x[1].neg(),x[0].neg()];};
const is=(x,y)=>ia(x,ineg(y));
const im=(x,y)=>{x=Array.isArray(x)?x:I(x);y=Array.isArray(y)?y:I(y);let z=[x[0].mul(y[0]),x[0].mul(y[1]),x[1].mul(y[0]),x[1].mul(y[1])].sort((a,b)=>a.cmp(b));return[z[0],z[3]];};
const id=(x,y)=>{y=Array.isArray(y)?y:I(y);if(!y[0].gt(0))throw Error("nonpositive interval denominator");return im(x,[f(1).div(y[1]),f(1).div(y[0])]);};
const ip=(x,k)=>{x=Array.isArray(x)?x:I(x);if(k%2===0&&x[0].lt(0)&&x[1].gt(0))return[f(0),x[0].neg().gt(x[1])?x[0].pow(k):x[1].pow(k)];let z=[x[0].pow(k),x[1].pow(k)].sort((a,b)=>a.cmp(b));return z;};
function isqrt(n){if(n<0n)throw Error("negative square root");if(n<2n)return n;let z=1n<<BigInt((n.toString(2).length+1)>>1);for(;;){let y=(z+n/z)>>1n;if(y>=z)return z;z=y;}}
function rootI(x){x=Array.isArray(x)?x:I(x);if(x[0].lt(0))throw Error("negative radical");const S=10n**14n;return[new F(isqrt(x[0].n*S*S/x[0].d),S),new F(isqrt(x[1].n*S*S/x[1].d)+1n,S)];}
function trigI(x,kind){x=Array.isArray(x)?x:I(x);if(x[0].lt(0)||x[1].gt(3))throw Error("trig domain");let term=kind==="sin"?x:I(1),s=term,lo;for(let j=1;j<=16;j++){let d=kind==="sin"?(2*j)*(2*j+1):(2*j-1)*(2*j);term=ineg(id(im(term,ip(x,2)),d));s=ia(s,term);if(j===15)lo=s[0];}return[lo,s[1]];}
const sinI=x=>trigI(x,"sin"),cosI=x=>trigI(x,"cos");
const atanS=(q,n)=>{let x=f(1).div(q),z=f(0);for(let j=0;j<=n;j++)z=z.add(x.pow(2*j+1).mul(new F(j%2?-1n:1n,BigInt(2*j+1))));return z;};
const PI=I("3.141592653589793238","3.141592653589793239");
if(!atanS(5,25).mul(16).sub(atanS(239,6).mul(4)).gt(PI[0])||!atanS(5,24).mul(16).sub(atanS(239,7).mul(4)).lt(PI[1]))throw Error("Machin enclosure");
return {I,ia,ineg,is,im,id,ip,rootI,sinI,cosI,PI};
})();
const {I,ia,ineg,is,im,id,ip,rootI,sinI,cosI,PI}=intervals;
const result=(function(){

const checks=[],tables=[];
function gt(name,x,y=0){x=Array.isArray(x)?x:I(x);y=f(y);checks.push({name,pass:x[0].gt(y),lower:x[0].str(),upper:x[1].str(),threshold:y.str()});}
function lt(name,x,y=0){gt(name,ineg(x),f(y).neg());}
const Q=f("3.9156"),g=f(".98439"),v=f(".05334"),hc=f(".34492"),gamma=f(".89765"),kk=f("1.89442"),ac=f("7/12"),e=f(".22042").sub(hc.mul(ac));
const R=rootI(Q),d=is(rootI(Q.div(2)),".5"),dc=ia(".5",id(rootI(2),24)),a0=is(rootI(Q.sub(".25")),".5"),hp=id(PI,2),lo=is(hp,".7");
function a(b){return is(rootI(is(Q,ip(ia(b,".5"),2))),".5");}
function rr(b){return id(ia(b,".5"),ia(a(b),".5"));}
function rp(b){return id(Q,ip(ia(a(b),".5"),3));}
function rpp(b){return id(im(Q.mul(3),ia(b,".5")),ip(ia(a(b),".5"),5));}
function J(b){return ia(".03965",ia(im("3.85510",b),ia(im("-1.49748",ip(b,2)),im(kk.neg(),im(a(b),b)))));}
function JD(b){return is(is("3.85510",im("2.99496",b)),im(kk,is(a(b),im(b,rr(b)))));}
function JDD(b){return ia("-2.99496",im(kk,ia(im(2,rr(b)),im(b,rp(b)))));}
function JDDD(b){return im(kk,ia(im(3,rp(b)),im(b,rpp(b))));}
function atanPoint(q,upper){q=f(q);if(q.lt(0))return atanPoint(q.neg(),!upper).neg();if(q.gt(".75"))throw Error("atan outside stated domain");let z=f(0),n=upper?40:39;for(let j=0;j<=n;j++)z=z.add(q.pow(2*j+1).mul(new F(j%2?-1n:1n,BigInt(2*j+1))));return z;}
function atanI(z){z=Array.isArray(z)?z:I(z);return[atanPoint(z[0],false),atanPoint(z[1],true)];}
function Edata(B,hh){
 const h=f(hh),U=ia(a(B),".5"),V=ia(B,".5"),P=is(U,1),t=is(Q.add(1),im(2,U)),S=rootI(is(im(h.pow(2),t),1)),r=id(V,U);
 const beta=ia(id(PI,4),atanI(id(is(V,P),ia(V,P))));
 const val=is(ia(is(ia(beta,atanI(S)),S),h.div(2).sub(e).sub(g.sub(h).pow(2).div(v.mul(4)))),J(B));
 const N=is(is(Q,U),im(V,S)),D=im(U,t),Np=is(is(r,S),id(im(h.pow(2),im(V,r)),S)),Dp=im(r,is(im(2,U),t));
 return{val,first:is(id(N,D),JD(B)),second:is(id(is(im(Np,D),im(N,Dp)),ip(D,2)),JDD(B)),S,U,t};
}
gt("diagonal>.899",d,".899");lt("diagonal<.9",d,".9");lt("axial<1.415",a0,"1.415");
lt("core norm<.8",im(2,ip(dc,2)),f(".8").pow(2));
lt("H corner affine correction",is(im(hc,is(ac,dc)),v.div(4)),0);
lt("H affine maximum<.570",ia(e,im(g,dc)),".570");
gt("H derivative positive",is(g,im(v.mul(2),dc)),0);
gt("J'(.5)>.624",JD(".5"),".624");lt("J''(.5)<0",JDD(".5"),0);gt("J''(.5)>-.032",JDD(".5"),"-.032");
gt("J''(.55)>0",JDD(".55"),0);gt("middle J derivative positive",f(".624").sub(f(".032").mul(".05")),0);
lt("J'(0)<1.176",JD(0),"1.176");lt("J'(d)<1.176",JD(d),"1.176");lt("J(d)<.763568",J(d),".763568");
gt("outer r' lower",rp(0),".557");gt("J''' lower>1",kk.mul(3).mul(".557"),1);
lt("J''(.5)<-.03",JDD(".5"),"-.03");
const JLref=is(J(".3"),f(".73").mul(".3")),JLder=is(JD(".3"),".73");
lt("J affine majorant on first half",ia(JLref,id(ip(JLder,2),".06")),".108");
lt("J affine derivative at.5",is(JD(".5"),".73"),0);
lt("J affine majorant at.5",is(J(".5"),f(".73").mul(".5")),".108");
lt("J affine majorant atd",is(J(d),im(".73",d)),".108");
const B1=is(rootI(Q.sub("2.25")),".5");
gt("B1>.79",B1,".79");lt("B1<d",B1,d[0]);lt("a0-1<.415",is(a0,1),".415");
lt("lower axis1 cost derivative at quarter B=.54",is(1,im(is(g,im(v.mul(2),is(a(".54"),1))),"1.04")),0);
gt("outer U(.54)>1.68",ia(a(".54"),".5"),"1.68");lt("outer U(0)<1.915",ia(a(0),".5"),"1.915");lt("outer U(.45)<1.74",ia(a(".45"),".5"),"1.74");
gt("lower angle envelope radical at B=0",Edata(0,g).S,0);
gt("second envelope radical at B=.45",Edata(".45",".975").S,0);
gt("first envelope curvature at .32",Edata(".32",g).second,".22");
gt("first envelope value .3035",Edata(".3035",g).val,".89776733");
gt("first envelope derivative .3035 lower",Edata(".3035",g).first,"-.000006");
lt("first envelope derivative .3035 upper",Edata(".3035",g).first,".000006");
gt("strong convexity completed square",f(".89776733").sub(f(".000006").pow(2).div(".44")),gamma);
gt("first envelope derivative .32",Edata(".32",g).first,0);gt("first envelope derivative .4",Edata(".4",g).first,0);
gt("first envelope value .32",Edata(".32",g).val,".8978");
lt("first envelope curvature .4",Edata(".4",g).second,0);
gt("first envelope value .4",Edata(".4",g).val,".8985");gt("first envelope value .45",Edata(".45",g).val,".8985");
lt("second envelope curvature .45",Edata(".45",".975").second,0);
gt("second envelope value .45",Edata(".45",".975").val,".89807");gt("second envelope value .54",Edata(".54",".975").val,".89807");
const u=[f(0),f(1)],u2=mul(u,u),T=[Q.add(1),f(-2)],W=add([Q],scale(u2,-1));
const E0=add(add(scale(u2,2),scale(u,Q.mul(-4))),[Q.mul(Q.add(1))]),E0p=[Q.mul(-4),f(4)];
const A0=add(mul(mul(E0,u2),T),scale(mul(W,add(mul(mul(E0p,u),T),scale(mul(E0,add(scale(T,3),scale(u,-4))),-1))),-1));
const u5=mul(mul(u2,u2),u),T2=mul(T,T),T3=mul(T2,T),D0=add(mul(u5,T3),scale(A0,-1));
function polycheck(name,p,L,H){const b=bern(p,L,H);b.forEach((x,i)=>gt(name+" Bernstein "+i,x,0));const den=100000000n;tables.push({name,interval:[L,H],degree:p.length-1,power_coefficients:p.map(x=>x.str()),bernstein_lower_numerators:b.map(x=>String(x.n*den/x.d)),denominator:String(den),bernstein_coefficients:b.map(x=>x.str())});}
polycheck("third derivative D0",D0,"1.68","1.915");
for(const [hh,L,H]of[[g,"1.68","1.915"],[f(".975"),"1.68","1.74"]]){
 const h=f(hh),Z=add(scale(T,h.pow(2)),[f(-1)]),Z2=mul(Z,Z);
 let C=scale(mul(mul(mul(u,T2),Z),[Q]),h.pow(2).mul(3));
 C=add(C,scale(mul(mul(W,u2),T2),h.pow(4).neg()));
 C=add(C,scale(mul(mul(mul(W,u2),T),Z),h.pow(2).mul(-4)));
 C=add(C,scale(mul(T2,Z2),Q.mul(3)));C=add(C,scale(mul(mul(u,T),Z2),Q.mul(-6)));C=add(C,scale(mul(mul(W,u2),Z2),8));
 polycheck("third derivative C0 "+h.str(),C,L,H);
}
gt("lower primary phi>1.12",is(ia(".5",ia(id(sinI("1.12"),2),im("13/12",cosI("1.12")))),a0),0);
lt("cot1.12<.485",id(cosI("1.12"),sinI("1.12")),".485");
gt("lower primary b_phi positive",f("13/12").sub(f(".915").mul(".485")),0);
const bpp=f(".5").add(f(".485").pow(2)).sub(f("13/12").mul(".485"));
gt("lower primary b_phi_phi lower",bpp,".2");
lt("lower primary contact cost concavity",v.mul(2).mul(f("13/12").pow(2)).sub(g.sub(v.mul(2).mul(".415")).mul(bpp)),0);
const m43=is(rootI(Q.sub(f(".93").pow(2))),1);
gt("lower primary zero B<=.43 also secondary",ia(f("349/144").sub(Q),im(2,m43)),0);
gt("positive root for secondary implication",is(im("13/12",sinI("1.12")),id(cosI("1.12"),2)),0);
function zeroData(phi){const s=sinI(phi),c=cosI(phi),m=ia(id(s,2),im("13/12",c)),vv=is(im("13/12",s),id(c,2)),U=ia(1,m),V=rootI(is(Q,ip(U,2)));return{m,vv,U,V,B:is(V,".5")};}
lt("zero B=.43 begins after1.32",zeroData("1.32").B,".43");gt("zero B=.65 ends before1.48",zeroData("1.48").B,".65");
gt("zero B at1.32>.4",zeroData("1.32").B,".4");lt("zero B at1.48<.7",zeroData("1.48").B,".7");
gt("r(.4)>.51",rr(".4"),".51");lt("zero primary B' upper",id(rootI("205/144"),".51"),"2.35");
gt("J''(.4)>-.52",JDD(".4"),"-.52");lt("J'(.4)<.73",JD(".4"),".73");lt("J'(.7)<.74",JD(".7"),".74");
lt("zero primary K'' upper",f(".52").mul(f("2.35").pow(2)).add(f(".74").mul(Q).mul("205/144").div(f(".9").pow(3))),9);
for(const phi of["1.32","1.36","1.4","1.44","1.48"])gt("zero primary endpoint "+phi,is(f(phi).sub(e),J(zeroData(phi).B)),".9000");
gt("zero primary five-point lower envelope",f(".9").sub(f(9).mul(f(".04").pow(2)).div(8)),gamma);
gt("zero primary imported endpoint reserve",f(".9025").sub(e.sub(".01449")),gamma);
gt("quarter zero endpoint",is(is(hp,e),J(B1)),".89780");
gt("upper secondary contact positivity B=0 x=.7",is(im(is(a0,".5"),cosI(".7")),id(sinI(".7"),2)),0);
gt("upper secondary contact positivity B=d",is(d,".5"),0);
gt("upper secondary cost derivative positive",f(1).sub(g.mul(".4")),0);
gt("upper secondary zero byx=.31",is(im(is(d,".5"),ia(cosI(".31"),sinI(".31"))),".5"),0);
gt("upper secondary zero curve monotonic denominator",is(im(rr(B1),cosI(".31")),sinI(".31")),0);
gt("upper secondary first-zero uniqueness",is(im(is(B1,".5"),cosI(".31")),id(sinI(".31"),2)),0);
lt("upper secondary zero speed<.79",id(".4",is(im(rr(B1),cosI(".31")),sinI(".31"))),".79");
gt("upper secondary zero cost derivative",f(1).sub(f("1.176").mul(".79")),0);
lt("upper primary corner impossible at.3",is(ia(is(a0,".5"),im(ac.sub(".5"),sinI(".3"))),cosI(".3")),0);
lt("upper primary side speed<.4",ia(id(im(is(a0,".5"),sinI(".3")),ip(cosI(".3"),2)),id("1/12",ip(cosI(".3"),2))),".4");
lt("upper primary zero speed<.27",id(ia(id(sinI(".3"),2),"1/12"),rr(B1)),".27");
gt("upper primary zero cost derivative",f(1).sub(f("1.176").mul(".27")),0);
gt("upper primary zero remains in outer arc",is(ia(".5",id(cosI(".3"),2)),id(sinI(".3"),12)),d[1]);
const C10=trigpoly("cos",10),C8=trigpoly("cos",8),S9=trigpoly("sin",9);
const K=PI[0].div(2).sub(e).sub(".108").add(g.add(".73").div(2)).sub(gamma);
const Ap=add(add(mul(C10,[K,f(1)]),[g]),scale(S9,g.div(12).neg()));
const Pfull=add(mul(Ap,Ap),scale(add([g.pow(2)],scale(mul(C8,C8),f(".73").pow(2))),Q.neg()));
const pp=Pfull.slice(0,9);
const err=sum(Pfull.slice(9).map((c,j)=>c.lt(0)?c.neg().mul(f(".7").pow(j+9)):f(0)));
pp[0]=pp[0].sub(err);
gt("upper primary support squared numerator positive",ia(I(f(1).sub(f(".7").pow(2).div(2)).mul(K.add(".3"))),g.mul(f(1).sub(f(".7").div(12)))),0);
polycheck("upper primary squared support",pp,".3",".7");
function upper4(x){return is(ia(ia(hp,x),f("-.570").sub(".108").add(f(".73").div(2))),ia(id(f(".73").div(12),cosI(x)),im(f(".73"),im(is(a0,".5"),id(sinI(x),cosI(x))))));}
gt("upper primary-negative endpoint zero",upper4(0),"1.19");gt("upper primary-negative endpoint .7",upper4(".7"),"1.19");
return{status:checks.every(x=>x.pass)?"PASS":"FAIL",theorem:"wrong0011011_edge3_negative_core_positive_outer",Q:Q.str(),gamma:gamma.str(),comparison_count:checks.length,checks,tables,polynomial_tail_allowance:err.str(),imported_lemmas:["WRONG_0011011_ALIGNED_MIXED_QUARTER_HAND_PROOF.md","WRONG_0011011_EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md Section 5.2"]};

})();
process.stdout.write(JSON.stringify(result,null,2)+"\n");
if(result.status!=="PASS")process.exitCode=1;

