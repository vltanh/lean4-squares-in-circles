"use strict";
// Fixed exact arithmetic for the final positive OO quarter-one row.
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

const checks=[];
function gt(name,x,y=0){x=Array.isArray(x)?x:I(x);y=Array.isArray(y)?y:I(y);checks.push({name,pass:x[0].gt(y[1]),lower:x[0].str(),upper:x[1].str(),threshold:y[1].str()});}
function lt(name,x,y=0){gt(name,ineg(x),ineg(y));}
const Q=f("3.9156"),gamma=f(".89765"),kk=f("1.89442"),pk=f("-.01025"),qk=f(".16031"),tk=f(".63457");
const Rrad=rootI(Q),d=is(rootI(Q.div(2)),".5"),a0=is(rootI(Q.sub(".25")),".5"),hp=id(PI,2),lo=is(hp,".7"),B1=is(rootI(Q.sub("2.25")),".5");
function a(b){return is(rootI(is(Q,ip(ia(b,".5"),2))),".5");}
function rr(b){return id(ia(b,".5"),ia(a(b),".5"));}
function rp(b){return id(Q,ip(ia(a(b),".5"),3));}
function rpp(b){return id(im(Q.mul(3),ia(b,".5")),ip(ia(a(b),".5"),5));}
function R(b){return ia(im(pk,a(b)),ia(im(qk,b),im(tk,im(a(b),b))));}
function RD(b){return ia(ineg(im(pk,rr(b))),ia(qk,im(tk,is(a(b),im(b,rr(b))))));}
function RDD(b){return is(im(tk.mul(-2),rr(b)),im(ia(pk,im(tk,b)),rp(b)));}
function RDDD(b){return ineg(id(im(Q.mul(3),ia(tk.mul(Q),im(pk.sub(tk.div(2)),ia(b,".5")))),ip(ia(a(b),".5"),5)));}
function J(b){return ia(".03965",ia(im("3.85510",b),ia(im("-1.49748",ip(b,2)),im(kk.neg(),im(a(b),b)))));}
function JD(b){return is(is("3.85510",im("2.99496",b)),im(kk,is(a(b),im(b,rr(b)))));}
function JDD(b){return ia("-2.99496",im(kk,ia(im(2,rr(b)),im(b,rp(b)))));}
function JDDD(b){return im(kk,ia(im(3,rp(b)),im(b,rpp(b))));}
const R0=R(0),Rd=R(d),Jd=J(d);
gt("diagonal>.899",d,".899");lt("diagonal<.9",d,".9");gt("axial>1.4145",a0,"1.4145");lt("axial<1.415",a0,"1.415");
gt("negative source third derivative bracket",tk.mul(Q).add(pk.sub(tk.div(2)).mul("1.4")),0);
lt("source second derivative at zero",RDD(0),0);gt("source derivative diagonal",RD(d),".170");lt("source derivative at zero",RD(0),"1.061");
gt("source derivative at zero exceeds core slope",RD(0),"1.0424");
lt("source curvature at .1",RDD(".1"),"-.434");gt("source derivative at .6",RD(".6"),".639");
gt("source zero label",R0,"-.01450");
gt("lower quarter sine bound",sinI(lo),".764");lt("lower quarter cosine bound",cosI(lo),".645");
gt("source global chord",is(Rd,R0),im(".736",d));
gt("source short chord",is(R(".35"),R0),f(".98").mul(".35"));
gt("target derivative middle",JD(".5"),".624");gt("target second derivative middle lower",JDD(".5"),"-.032");lt("target second derivative middle upper",JDD(".5"),0);
gt("target second derivative at .55",JDD(".55"),0);gt("target derivative uniform lower",f(".624").sub(f(".032").mul(".05")),".622");
lt("target derivative at zero",JD(0),"1.176");lt("target derivative at diagonal",JD(d),"1.176");lt("target label diagonal",Jd,".763568");
gt("target curvature at B1",JDD(B1),2);lt("outer radial derivative max",rp(d),"1.431");
lt("radial logarithmic derivative",id(rpp(d),rp(d)),"2.15");
gt("contact derivative concavity reserve",kk.mul(3).sub(f("1.061").mul("2.15")),0);
gt("aligned initial contact derivative",is(im(RD(0),rr(B1)),JD(B1)),0);
gt("aligned axial endpoint",is(ia(hp,R0),J(B1)),".9025");
gt("aligned diagonal endpoint",is(ia(hp,R(is(1,d))),Jd),".8977886");
gt("late whole-angle direct",is(ia("1.676",R0),Jd),".8979");
lt("late cutoff before quarter+.11",f("1.676"),ia(hp,".11")[0]);
const tangents=[
 {l:"lo",h:"1",b:".172",q:".878955401",k:".063716016"},
 {l:"1",h:"1.1",b:".209",q:".828547105",k:".073303502"},
 {l:"1.1",h:"1.2",b:".252",q:".776312419",k:".085318707"},
 {l:"1.2",h:"1.3",b:".302",q:".724514843",k:".099625668"}];
const gs=f(".98");
function smallSupport(phi,q,k){q=f(q);k=f(k);return is(ia(ia(ia(phi,R0),gs.add(q).div(2).sub(k)),im(gs,sinI(phi))),im(Rrad,rootI(is(gs.pow(2).add(q.pow(2)),im(gs.mul(q).mul(2),cosI(phi))))));}
gt("four short supports are concave",is(im(gs,sinI(lo)),id(im(Rrad,rootI(gs.pow(2).add(f(".879").pow(2)))),4)),0);
for(let i=0;i<tangents.length;i++){const z=tangents[i];
 lt("target tangent slope "+i,JD(z.b),z.q);lt("target tangent intercept "+i,is(J(z.b),im(z.b,JD(z.b))),z.k);
 gt("short support left "+i,smallSupport(z.l==="lo"?lo:z.l,z.q,z.k),".9013");
 gt("short support right "+i,smallSupport(z.h,z.q,z.k),".9013");}
function Bcut(phi,b){const s=sinI(phi),c=cosI(phi),Z=ia(is(".5",b),s),Y=rootI(is(Q,ip(Z,2))),U=ia(im(Z,s),im(Y,c)),V=is(im(Y,s),im(Z,c)),ff=is(1,id(c,Y));
 const k=is(".5",b),fp=id(is(im(is(Q.sub(1),ip(k,2)),s),im(k,ia(1,ip(s,2)))),ip(Y,3));
 return{B:is(V,".5"),U,V,Y,ff,fp};}
function secondaryDerivative(phi,B){return is(im(RD(".35"),ia(im(rr(B),sinI(phi)),cosI(phi))),JD(B));}
gt("short-source secondary at B=.5 positive",ia(".5",ia(im(is(".5",a(".5")),sinI("1.3")),cosI("1.3"))),".08");
lt("short-source maximum target below .78",Bcut("1.3",".35").B,".78");
for(const ph of[lo,"1.3"])for(const B of[".5",".78"])gt("short-source high-target derivative "+(typeof ph==="string"?ph:"lo")+" "+B,secondaryDerivative(ph,B),0);
const cutRows=[
 ["lo",".95",".252",".346"],[".95","1.05",".345",".466"],
 ["1.05","1.15",".465",".590"],["1.15","1.3",".589",".779"]];
for(let i=0;i<cutRows.length;i++){const[l,h,bl,bh]=cutRows[i],L=l==="lo"?lo:l;
 gt("cut target lower "+i,Bcut(L,".35").B,bl);lt("cut target upper "+i,Bcut(h,".35").B,bh);
 for(const [j,ph]of[[0,L],[1,h]])for(const B of[bl,bh])gt("large-source left derivative "+i+" "+j+" "+B,secondaryDerivative(ph,B),0);}
gt("source-diagonal first target>.75",Bcut(lo,d).B,".75");
lt("source-diagonal terminal angle>1.014",Bcut("1.014",d).B,d[0]);gt("source-diagonal terminal angle<1.015",Bcut("1.015",d).B,d[1]);
gt("source-diagonal f lower",Bcut(lo,d).ff,".668");lt("source-diagonal f upper",Bcut("1.015",d).ff,".73");
gt("source-diagonal contact speed lower",f("1.399").mul(".668"),".93");
gt("target curvature above .75",JDD(".75"),"1.6");
lt("source-diagonal cost concavity",f("-1.6").mul(f(".93").pow(2)).add(f("1.176").mul("1.4").mul(f(".73").pow(2))),0);
gt("source-diagonal initial endpoint",is(ia(lo,Rd),J(Bcut(lo,d).B)),".8977888");
gt("double-diagonal endpoint",is(ia("1.014",Rd),Jd),".8984");
function targetDiagonalB(phi){return ia(".5",ia(im(is(".5",d),sinI(phi)),im(ia(".5",d),cosI(phi))));}
lt("late target-diagonal source below .5",targetDiagonalB("1.3"),".5");
gt("aligned source greater than .1",is(1,d),".1");
lt("target-diagonal cost concavity",ia(im("-.434",ip(im("1.399",sinI("1.014")),2)),f("1.061").mul(".4")),0);
gt("lower primary f' positive coefficient",Q.sub(1).sub(f(".915").pow(2)),0);
function primarySupport(phi){const g=f(".736"),q=f(".73"),s=sinI(phi),c=cosI(phi);return ia(ia(ia(phi,R0),g.add(q).div(2).sub(".108")),id(is(im(g,ia(1,im(ia(d,".5"),c))),im(Rrad,rootI(ia(g.pow(2),im(q.pow(2),ip(s,2)))))),s));}
gt("lower primary initial angle support",primarySupport(lo),".9209");
function zeroPrimaryA(phi){return ia(".5",ia(id(sinI(phi),2),im(ia(a0,".5"),cosI(phi))));}
gt("zero source lower-primary angle>1.3",zeroPrimaryA("1.3"),a0[1]);
gt("zero source lower-primary speed",is(im(ia(a0,".5"),sinI("1.3")),id(cosI("1.3"),2)),"1.7");
gt("zero source lower-primary decreasing cost",f(".622").mul("1.7"),1);
gt("primary source-diagonal first target>.66",a(targetDiagonalB(lo)),".66");
gt("target radial ratio at .66",rr(".66"),".7");
gt("target J'/r initial ratio",id(JD(".66"),rr(".66")),".95");
gt("target J'/r derivative initial",is(im(JDD(".66"),rr(".66")),im(JD(".66"),rp(".66"))),0);
gt("target ratio derivative numerator increases",kk.mul(3).mul(".7").sub(f("1.176").mul("2.15")),0);
gt("lower primary diagonal speed numerator",ia(im(is(d,".5"),cosI(lo)),im(ia(d,".5"),sinI(lo))),"1.32");
gt("lower primary diagonal decreasing cost",f(".95").mul("1.32"),1);
gt("upper secondary threshold derivative positive",is(im(rr(0),cosI(".11")),sinI(".11")),0);
gt("upper secondary diagonal threshold positive",is(".5",im(is(d,".5"),ia(cosI(".11"),sinI(".11")))),0);
lt("upper secondary source coordinate<.101",is(1,d),".101");
lt("upper secondary target concavity",f("1.061").mul("1.431").sub(2),0);
gt("upper secondary diagonal cost derivative",f(1).sub(f("1.061").mul(".4")),0);
lt("upper secondary zero speed",id(".4",is(im(rr(B1),cosI(".11")),sinI(".11"))),".54");
gt("upper secondary zero cost derivative",f(1).sub(f("1.176").mul(".54")),0);
gt("upper primary source .101 always sufficient",ia(d,".101"),1);
gt("upper primary derivative denominator",is(cosI(".11"),im(rr(".101"),sinI(".11"))),".958");
lt("upper primary source radial derivative",rp(".101"),".585");
lt("upper primary target first derivative",f(1).div(".958"),"1.044");
lt("upper primary target second derivative",f("1.431").add(f(".585").mul(".11").mul(f("1.044").pow(2))).div(".958"),"1.58");
lt("upper primary target cost concavity",f("1.061").mul("1.58").sub(2),0);
lt("upper primary diagonal speed",f(".97").div(".958"),"1.02");
gt("upper primary diagonal coordinate concavity",f(".399").sub(f(".585").mul(".11").mul(f("1.02").pow(2))),0);
function zeroUpperMargin(x){return ia(is(d,".5"),is(im(is(a0,".5"),sinI(x)),id(cosI(x),2)));}
lt("upper-primary double-zero angle>.107",zeroUpperMargin(".107"),0);gt("upper-primary double-zero angle<.108",zeroUpperMargin(".108"),0);
gt("upper-primary double-zero endpoint",is(ia(ia(hp,".107"),R0),Jd),".8997");
gt("upper-primary zero speed lower",im(is(a0,".5"),cosI(".11")),".908");
lt("upper-primary zero speed numerator",ia(id(sinI(".11"),2),is(a0,".5")),".97");
gt("upper-primary zero second derivative lower",f("1.399").mul(".399").div("1.4").sub(Q.mul(f(".97").pow(2)).div(f("1.29").pow(3))),"-1.32");
lt("upper-primary zero cost concavity",f(-2).mul(f(".908").pow(2)).add(f("1.176").mul("1.32")),0);
gt("B1 transverse plus .5>1.29",ia(B1,".5"),"1.29");
const j=f("1.176");
gt("outer slope at zero>.261",rr(0),".261");gt("outer slope at .6>.668",rr(".6"),".668");
gt("axis3 source derivative low part",f(".639").add(j.mul(f(".261").mul(".764").sub(".645"))),0);
gt("axis3 source derivative high part",f(".170").add(j.mul(f(".668").mul(".764").sub(".645"))),0);
function F3(phi){return ia(ia(ia(phi,R0),j.div(2).sub(".03965")),is(im(j.div(2),cosI(phi)),im(j,im(is(a0,".5"),sinI(phi)))));}
function F3D(phi){return is(is(1,im(j.div(2),sinI(phi))),im(j,im(is(a0,".5"),cosI(phi))));}
gt("axis3 scalar curvature",im(j,is(im(is(a0,".5"),sinI(lo)),id(cosI(lo),2))),".44");
gt("axis3 scalar reference cost",F3("1.04"),".9439");gt("axis3 scalar reference derivative lower",F3D("1.04"),"-.052");lt("axis3 scalar reference derivative upper",F3D("1.04"),".052");
gt("axis3 scalar strong-convexity bound",f(".9439").sub(f(".052").pow(2).div(".88")),".9408");
lt("outer norm cap",is(a0,1),".415");
gt("upper axis3 direct",is(ia(hp,R0),J(".415")),"1.16");
lt("lower axis4 early impossible",is(is(is(a0,".5"),id(sinI("1.2"),2)),im(ia(d,".5"),cosI("1.2"))),0);
gt("lower axis4 necessary margin increases",is(im(ia(d,".5"),sinI(lo)),id(cosI(lo),2)),0);
function B4(phi){return is(is(id(is(a0,".5"),sinI(phi)),".5"),id(im(ia(d,".5"),cosI(phi)),sinI(phi)));}
gt("lower axis4 target cap increases",is(ia(d,".5"),im(is(a0,".5"),cosI(lo))),0);
lt("lower axis4 intermediate target cap",B4("1.4"),".187");
gt("lower axis4 early cost",is(ia("1.2",R0),J(".187")),".957");
gt("lower axis4 late cost",is(ia("1.4",R0),J(".415")),".990");
lt("upper axis4 target cap",is(id(im(is(a0,".5"),ia(1,sinI(".11"))),cosI(".11")),".5"),".523");
gt("upper axis4 cost",is(ia(hp,R0),J(".523")),"1.09");
return{status:checks.every(x=>x.pass)?"PASS":"FAIL",theorem:"wrong0011011_edge3_positive_outer_positive_outer_whole",Q:Q.str(),gamma:gamma.str(),comparison_count:checks.length,checks,tangents,cutRows,imported_lemmas:["WRONG_0011011_EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md Section 3.2 zero contact and derivative bounds","WRONG_0011011_EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md Section 1 global J affine bound"]};

})();
process.stdout.write(JSON.stringify(result,null,2)+"\n");
if(result.status!=="PASS")process.exitCode=1;

