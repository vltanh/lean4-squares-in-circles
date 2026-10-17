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
const Q=f("3.9156"),h=f("1.03981"),p=f(".670579666"),k0=f(".118433769"),k=f(".63457"),gamma=f(".89765"),R=rootI(Q),ac=f("7/12");
const d=is(rootI(Q.div(2)),".5"),dc=ia(".5",id(rootI(2),24)),a0=is(rootI(Q.sub(".25")),".5"),hp=id(PI,2),lo=is(hp,".7");
function a(B){return is(rootI(is(Q,ip(ia(B,".5"),2))),".5");}
function V(B){return ia(im("-.01025",a(B)),ia(im(".16031",B),im(k,im(a(B),B))));}
function D(B){const A=a(B),r=id(ia(B,".5"),ia(A,".5"));return ia(im(".01025",r),ia(".16031",im(k,is(A,im(B,r)))));}
gt("outer diagonal>.899",d,".899");lt("outer diagonal<.9",d,".9");lt("outer axial a<1.415",a0,"1.415");
lt("core radius<.8",im(2,ip(dc,2)),f(".8").pow(2));
lt("global outer radial derivative rprime<1.5",f(4).div(f("1.399").pow(3)),"1.5");
gt("radial ratio>.261",id(".5",ia(a0,".5")),".261");
lt("global V second derivative negative",f("-1.26914").mul(".261").add(f(".01025").mul("1.5")),0);
gt("V derivative at diagonal positive",f(".17056"),0);
lt("V maximum below.6481",V(d),".6481");
lt("rational upper tangent slope",D(".5725"),p);
lt("rational upper tangent intercept",is(V(".5725"),im(D(".5725"),".5725")),k0);
gt("all-axis direct bound for phi>=2.13",is(is(is("2.13",".00125"),im(h,dc)),".6481"),".8994");
gt("phi2.13 lies before quarter+.56",ia(hp,".56"),"2.13");
function margin(B,phi){return is(is(im(a(B),sinI(phi)),im(B,cosI(phi))),id(ia(1,ia(sinI(phi),cosI(phi))),2));}
lt("axis1 source b>=0 requires phi>1",margin(0,1),0);
lt("axis1 phi<=1.2 implies B<.254",margin(".254","1.2"),0);
const rr=id(".754",ia(a(".254"),".5"));
lt("axis1 combination r sinphi+cosphi decreases",is(im(rr,cosI(1)),sinI(1)),0);
lt("axis1 low-angle contact decreases in B",is(im(h,ia(im(rr,sinI(1)),cosI(1))),D(".254")),0);
gt("a(.254)>1.329",a(".254"),"1.329");
gt("a0-.5>.914",is(a0,".5"),".914");lt("cos1<.541",cosI(1),".541");
lt("zero-core boundary phi derivative<.871",f(1).add(f(".541").div(".914")).div("1.829"),".871");
gt("Vprime(.254)>.941",D(".254"),".941");
gt("zero-core boundary cost atphi1.2>.957",is("1.19875",V(".254")),".957");
function Nlow(phi){return rootI(is(h.pow(2).add(p.pow(2)),im(h.mul(p).mul(2),cosI(phi))));}
function Flow(phi){return is(ia(ia(phi,f("-.00125").sub(k0).add(h.add(p).div(2))),im(h,sinI(phi))),im(R,Nlow(phi)));}
gt("axis1 lower support concavity",is(im(h,sinI("1.2")),id(im(R,Nlow(hp)),4)),0);
gt("axis1 lower support at1.2>.9007",Flow("1.2"),".9007");
gt("axis1 lower support atquarter>.89778",Flow(hp),".89778");
function Nup(x){return rootI(ia(h.pow(2).add(p.pow(2)),im(h.mul(p).mul(2),sinI(x))));}
function Fup(x){return is(ia(ia(ia(hp,x),f("-.00125").sub(k0).add(h.add(p).div(2))),im(h,ia(sinI(x),cosI(x)))),im(R,Nup(x)));}
gt("axis1 upper support concavity",is(h,id(im(R,h.add(p)),4)),0);
gt("axis1 upper support endpoint>1.387",Fup(".7"),"1.387");
gt("lower axis2 corner barrier at left>1.5",ia(".5",ia(im(ia(dc,".5"),cosI(lo)),sinI(lo))),"1.5");
lt("axis4 upper requires x>.4",ia(ac.sub(".5"),is(im(is(a0,".5"),sinI(".4")),id(cosI(".4"),2))),0);
const Bcap=ia("-.5",ia(im(is(a0,".5"),id(sinI(".56"),cosI(".56"))),id("1/12",cosI(".56"))));
lt("axis4 upper x<=.56 implies B<.18",Bcap,".18");
lt("V(.18)<.174",V(".18"),".174");
gt("axis4 upper early direct bound>1.214",is(is(is(ia(hp,".4"),".00125"),im(h,dc)),".174"),"1.214");

const C10=trigpoly("cos",10),C8=trigpoly("cos",8),S11=trigpoly("sin",11),S9=trigpoly("sin",9);
const K=PI[0].div(2).sub(".00125").sub(k0).add(h.add(p).div(2)).sub(gamma);
for(const [name,dir,sinecoef,sp,allow,floors] of [
 ["lower",-1,h.mul("13/12"),S11,f(".000274"),[".000397",".05458",".07950",".08343",".07559",".06439",".05602",".05418",".06095"]],
 ["upper",1,h.div(-12),S9,f(".00001"),[".000661",".39201",".76842","1.10743","1.38425","1.57465","1.65928","1.62777","1.47923"]]
]){
 const A=add(add(mul(C10,[K,f(dir)]),[h]),scale(sp,sinecoef));
 const P=add(mul(A,A),scale(add([h.pow(2)],scale(mul(C8,C8),p.pow(2))),Q.neg()));
 let tail=f(0);for(let j=9;j<P.length;j++)if(P[j].lt(0))tail=tail.add(P[j].neg().mul(f(".7").pow(j)));
 lt(name+" squared polynomial tail",tail,allow);
 const P8=P.slice(0,9);P8[0]=P8[0].sub(allow);const bs=bern(P8,0,".7");
 for(let j=0;j<bs.length;j++)gt(name+" primary Bernstein "+j,bs[j],floors[j]);
 tables.push({name:name+" primary squared bound",degree:8,interval:["0",".7"],negative_tail:tail.str(),tail_allowance:allow.str(),power_coefficients:P8.map(t=>t.str()),bernstein_coefficients:bs.map(t=>t.str()),printed_lower:floors});
}
gt("positive angle coefficient for squared bounds",K.sub(".7"),".69");
gt("cos lower polynomial positive",f(1).sub(f(".7").pow(2).div(2)),".75");
gt("sine lower polynomial nonnegative after dividing x",f(1).sub(f(".7").pow(2).div(6)),0);
gt("upper squared numerator positive",h.mul(f(1).sub(f(".7").div(12))),0);
for(const z of[".8994",".957",".9007",".89778","1.387","1.214"])gt("terminal "+z+" exceedsgamma",f(z),gamma);
return{status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"0011011 edge2 core-minus to outer-plus; both core pieces, all four axes, whole quarter-one angle interval",comparisons:checks.length,checks,tables};

})();
process.stdout.write(JSON.stringify(result,null,2)+'\n');
if(result.status!=='PASS')process.exitCode=1;
