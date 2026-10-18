"use strict";
// Fixed exact arithmetic for whole O- to C- edge3.
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
const checks=[],tables=[];function gt(name,x,y=0){x=Array.isArray(x)?x:I(x);y=f(y);checks.push({name,pass:x[0].gt(y),lower:x[0].str(),upper:x[1].str(),threshold:y.str()});}function lt(name,x,y=0){gt(name,ineg(x),f(y).neg());}
const Q=f("3.9156"),g=f(".62312"),c0=f(".16823"),gamma=f(".89765"),q=f(".633"),kline=f(".1109"),ac=f("7/12");
const R=rootI(Q),d=is(rootI(Q.div(2)),".5"),dc=ia(".5",id(rootI(2),24)),a0=is(rootI(Q.sub(".25")),".5"),hp=id(PI,2),lo=is(hp,".7");
function a(b){return is(rootI(is(Q,ip(ia(b,".5"),2))),".5");}function rr(b){return id(ia(b,".5"),ia(a(b),".5"));}function rp(b){return id(Q,ip(ia(a(b),".5"),3));}
function T(b){return ia(".01670",ia(im("2.42322",b),ia(im("-.91744",ip(b,2)),im("-.95769",im(a(b),b)))));}
function TD(b){return is(is("2.42322",im("1.83488",b)),im(".95769",is(a(b),im(b,rr(b)))));}
function TDD(b){return ia("-1.83488",im(".95769",ia(im(2,rr(b)),im(b,rp(b)))));}
gt("diagonal>.899",d,".899");lt("diagonal<.9",d,".9");lt("axial<1.415",a0,"1.415");lt("core norm<.8",im(2,ip(dc,2)),f(".8").pow(2));
lt("T''(.6)<-.048",TDD(".6"),"-.048");gt("T''(.6)>-.049",TDD(".6"),"-.049");gt("T''(.7)>0",TDD(".7"),0);
gt("T'(.6)>.610",TD(".6"),".610");gt("middle derivative>.605",f(".610").sub(f(".049").mul(".1")),".605");
lt("T'(.6)<.62",TD(".6"),".62");
const ref=f(".53362"),H=is(T(ref),im(".62",ref)),HD=is(TD(ref),".62");
lt("small arc line upper",ia(H,id(ip(HD,2),".096")),".110895");
lt("line endpoint.6",is(T(".6"),im(".62",".6")),kline);lt("line endpoint.7",is(T(".7"),im(".62",".7")),kline);
lt("global line diagonal",is(T(d),im(q,d)),kline);lt("label diagonal upper",T(d),".67949");
gt("whole late direct",f("1.409").sub(".67949").add(c0),gamma);
gt("corner late direct",f("1.098").sub(".67949").add(c0).add(g.div(2)),gamma);
lt("whole late cutoff before quarter",f("1.409"),hp[0]);lt("corner cutoff before quarter",f("1.098"),hp[0]);
function norm(phi){return rootI(is(g.pow(2).add(q.pow(2)),im(g.mul(q).mul(2),cosI(phi))));}
function support(phi){return is(ia(ia(phi,c0.sub(kline).add(g.add(q).div(2))),im(g,sinI(phi))),im(R,norm(phi)));}
gt("secondary scalar concavity",is(im(g,sinI(lo)),id(im(R,norm("1.409")),4)),0);
gt("secondary scalar lower endpoint",support(lo),".984");gt("secondary scalar upper endpoint",support("1.409"),"1.099");
const C10=trigpoly("cos",10),C8=trigpoly("cos",8),S11=trigpoly("sin",11);
const K=PI[0].div(2).add(c0).sub(kline).add(g.add(q).div(2)).sub(gamma);
const A=add(add(mul(C10,[K,f(-1)]),[g]),scale(S11,g.mul("13/12")));
const P=add(mul(A,A),scale(add([g.pow(2)],scale(mul(C8,C8),q.pow(2))),Q.neg()));
let tail=f(0);for(let j=9;j<P.length;j++)if(P[j].lt(0))tail=tail.add(P[j].neg().mul(f(".7").pow(j)));
const allowance=f(".000299");lt("primary side negative tail",tail,allowance);
const P8=P.slice(0,9);P8[0]=P8[0].sub(allowance);const bs=bern(P8,".161",".7");
const floors=[".6117715",".5130297",".4132075",".3172047",".2292187",".1523344",".0883327",".0378233",".0006068"];
for(let j=0;j<bs.length;j++)gt("primary side Bernstein"+j,bs[j],floors[j]);
gt("primary side squared numerator positive",K.sub(".7"),0);
gt("primary side angle overcover",is(hp,".161"),"1.409");
tables.push({name:"whole_lower_primary_side",interval:[".161",".7"],degree:8,tail:tail.str(),allowance:allowance.str(),power_coefficients:P8.map(x=>x.str()),bernstein_coefficients:bs.map(x=>x.str()),printed_lower:floors});
const v=f(".91744"),k=f(".95769"),V=f("3.819505"),constant=f("1.6636925").add(v.mul(Q));
function M(u){return is(is(is(constant,im(v,ip(u,2))),im(k.div(2),u)),im(is(V,im(k,u)),rootI(is(Q,ip(u,2)))));}
function MD(u){const t=rootI(is(Q,ip(u,2)));return ia(is(im(v.mul(-2),u),k.div(2)),ia(im(k,t),id(im(is(V,im(k,u)),u),t)));}
function MDD(u){const t=rootI(is(Q,ip(u,2)));return ia(v.mul(-2),is(id(im(Q,is(V,im(k,u))),ip(t,3)),id(im(k.mul(2),u),t)));}
gt("negative-label third derivative positive",V.mul("1.4").sub(k.mul(Q)),0);
gt("negative-label derivative at1.4",MD("1.4"),".773");
gt("negative-label second at1.4",MDD("1.4"),"-.204");gt("negative-label second at1.5",MDD("1.5"),0);
gt("negative-label derivative lower",f(".773").sub(f(".204").mul(".1")),".75");
lt("negative-label second at1.7",MDD("1.7"),"3.212");
function contact(phi,A,B){return ia(1,is(im(ia(A,".5"),cosI(phi)),im(is(B,".5"),sinI(phi))));}
function speed(phi,A,B){return ia(im(ia(A,".5"),sinI(phi)),im(is(B,".5"),cosI(phi)));}
gt("corner contact height>1.4",contact("1.098",dc,dc),"1.4");
lt("corner contact height<1.7",contact(lo,ac,".5"),"1.7");
gt("corner cosine>.455",cosI("1.098"),".455");
gt("whole corner concavity reserve",f(12).mul(".75").mul(".455").sub("3.212"),0);
const angleRows=[["lo",".95"],[".95","1.03"],["1.03","1.098"]],endpoints=[["side",ac,".5"],["diagonal",dc,dc]],endpointRows=[];
for(let i=0;i<angleRows.length;i++){const[l,h]=angleRows[i],L=l==="lo"?lo:l;
 for(const[name,A,B]of endpoints){const speedH=speed(h,A,B);
  for(const[tag,p]of[["left",L],["right",h]])lt("corner endpoint derivative loss "+i+" "+name+" "+tag,im(MD(contact(p,A,B)),speedH),".920");
 }}
for(const[name,A,B]of endpoints){const val=ia(ia(lo,c0),ia(M(contact(lo,A,B)),im(g,B)));
 gt("corner final endpoint "+name,val,name==="side"?".9196":".897784");
 endpointRows.push({name,angle:"lo",value_lower:val[0].str(),value_upper:val[1].str()});}
for(const z of[".89774",".8983",".984","1.099",".9196",".897784"])gt("final reserve "+z,f(z),gamma);
return{status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"0011011 edge3 O- to C-, all four axes on whole quarter-one interval, both core pieces",comparisons:checks.length,checks,tables,angleRows,endpointRows};

})();
process.stdout.write(JSON.stringify(result,null,2)+"\n");
if(result.status!=="PASS")process.exitCode=1;

