"use strict";
// Exact fixed-comparison checker for all mixed quarter-one contact families.
// All arithmetic is rational BigInt. No numerical optimizer or adaptive box cover.
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b){let t=a%b;a=b;b=t;}return a;}
class Rat{
  constructor(n,d=1n){n=BigInt(n);d=BigInt(d);if(d<0n){n=-n;d=-d;}if(!d)throw Error("zero denominator");let g=gcd(n,d);this.n=n/g;this.d=d/g;}
  add(b){b=rr(b);return new Rat(this.n*b.d+b.n*this.d,this.d*b.d);}
  neg(){return new Rat(-this.n,this.d);}
  sub(b){return this.add(rr(b).neg());}
  mul(b){b=rr(b);return new Rat(this.n*b.n,this.d*b.d);}
  div(b){b=rr(b);return new Rat(this.n*b.d,this.d*b.n);}
  pow(k){return new Rat(this.n**BigInt(k),this.d**BigInt(k));}
  cmp(b){b=rr(b);let v=this.n*b.d-b.n*this.d;return v<0n?-1:v>0n?1:0;}
  toString(){return this.d===1n?String(this.n):this.n+"/"+this.d;}
}
function rr(x){if(x instanceof Rat)return x;if(typeof x==="bigint")return new Rat(x);let s=String(x);if(s.includes("/")){let [n,d]=s.split("/");return new Rat(n,d);}if(s.includes(".")){let neg=s[0]==="-";if(neg)s=s.slice(1);let [a,b]=s.split(".");return new Rat((neg?-1n:1n)*BigInt(a+b),10n**BigInt(b.length));}return new Rat(s);}
function ii(x){return Array.isArray(x)?x:[rr(x),rr(x)];}
function ia(a,b){a=ii(a);b=ii(b);return[a[0].add(b[0]),a[1].add(b[1])];}
function ineg(a){a=ii(a);return[a[1].neg(),a[0].neg()];}
function isub(a,b){return ia(a,ineg(b));}
function im(a,b){a=ii(a);b=ii(b);let z=[a[0].mul(b[0]),a[0].mul(b[1]),a[1].mul(b[0]),a[1].mul(b[1])];z.sort((x,y)=>x.cmp(y));return[z[0],z[3]];}
function idiv(a,b){b=ii(b);if(b[0].cmp(0)<=0&&b[1].cmp(0)>=0)throw Error("division across zero");return im(a,[rr(1).div(b[1]),rr(1).div(b[0])]);}
function ipow(a,k){a=ii(a);if(k===0)return ii(1);if(k%2===0&&a[0].cmp(0)<0&&a[1].cmp(0)>0){let z=[a[0].pow(k),a[1].pow(k)].sort((x,y)=>x.cmp(y));return[rr(0),z[1]];}let z=[a[0].pow(k),a[1].pow(k)].sort((x,y)=>x.cmp(y));return z;}
function isqrt(n){if(n<0n)throw Error("negative root");if(n<2n)return n;let x=1n<<BigInt((n.toString(2).length+1)>>1);while(true){let y=(x+n/x)>>1n;if(y>=x)return x;x=y;}}
function root(a){a=ii(a);if(a[0].cmp(0)<0)throw Error("negative interval root");let scale=10n**14n;let lo=isqrt(a[0].n*scale*scale/a[0].d),hi=isqrt(a[1].n*scale*scale/a[1].d)+1n;return[new Rat(lo,scale),new Rat(hi,scale)];}

const trigCache=new Map();
function trig(x,cosine){x=ii(x);let key=(cosine?"c":"s")+x.map(a=>a.toString()).join("|");if(trigCache.has(key))return trigCache.get(key);if(x[0].cmp(0)<0||x[1].cmp(3)>0)throw Error("trig range");let term=cosine?ii(1):x,sum=term,lo;for(let j=1;j<=16;j++){let den=cosine?(2*j-1)*(2*j):(2*j)*(2*j+1);term=ineg(idiv(im(term,ipow(x,2)),den));sum=ia(sum,term);if(j===15)lo=sum[0];}let out=[lo,sum[1]];trigCache.set(key,out);return out;}
function sin(x){return trig(x,false);}function cos(x){return trig(x,true);}
function atanSeries(q,n){let x=rr(1).div(q),s=rr(0);for(let j=0;j<=n;j++)s=s.add(x.pow(2*j+1).div(2*j+1).mul(j%2?-1:1));return s;}
const PI_MACHIN=[atanSeries(5,25).mul(16).sub(atanSeries(239,6).mul(4)),atanSeries(5,24).mul(16).sub(atanSeries(239,7).mul(4))];
const PI=[rr("3.141592653589793238"),rr("3.141592653589793239")];
if(PI_MACHIN[0].cmp(PI[0])<=0||PI_MACHIN[1].cmp(PI[1])>=0)throw Error("Machin enclosure");
const P2=idiv(PI,2);
function angle(t){if(t==="p")return P2;if(t==="lo")return isub(P2,".7");if(t==="hi")return ia(P2,".7");if(String(t).startsWith("p+"))return ia(P2,String(t).slice(2));return ii(t);}
function absI(x){x=ii(x);if(x[0].cmp(0)>=0)return x;if(x[1].cmp(0)<=0)return ineg(x);return[rr(0),x[0].neg().cmp(x[1])>0?x[0].neg():x[1]];}
function dec(x,digits=9){x=rr(x);let sc=10n**BigInt(digits),n=x.n*sc/x.d;if(x.n<0n&&x.n*sc%x.d)n--;let neg=n<0n;if(neg)n=-n;let s=String(n).padStart(digits+1,"0");return(neg?"-":"")+s.slice(0,-digits)+"."+s.slice(-digits);}
function decup(x,digits=9){return dec(rr(x).neg(),digits).startsWith("-")?dec(rr(x).neg(),digits).slice(1):"-"+dec(rr(x).neg(),digits);}

function pAdd(a,b){return Array.from({length:Math.max(a.length,b.length)},(_,i)=>(a[i]||rr(0)).add(b[i]||0));}
function pNeg(a){return a.map(x=>rr(x).neg());}
function pSub(a,b){return pAdd(a,pNeg(b));}
function pScale(a,b){return a.map(x=>rr(x).mul(b));}
function pMul(a,b){let r=Array(a.length+b.length-1).fill(null).map(()=>rr(0));for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)r[i+j]=r[i+j].add(rr(a[i]).mul(b[j]));return r;}
function pPow(a,k){let r=[rr(1)];for(let j=0;j<k;j++)r=pMul(r,a);return r;}
function choose(n,k){if(k<0||k>n)return rr(0);let r=rr(1);for(let j=1;j<=k;j++)r=r.mul(n-j+1).div(j);return r;}
function bernstein(p,lo,hi){lo=rr(lo);let w=rr(hi).sub(lo),n=p.length-1,a=Array(n+1).fill(null).map(()=>rr(0));for(let j=0;j<=n;j++)for(let k=0;k<=j;k++)a[k]=a[k].add(p[j].mul(choose(j,k)).mul(lo.pow(j-k)).mul(w.pow(k)));return a.map((_,k)=>a.slice(0,k+1).reduce((s,x,i)=>s.add(x.mul(choose(k,i)).div(choose(n,i))),rr(0)));}

const input={"norm":{"status":"exact rational normalized coefficients; discovery fields omitted","Q":[9789,2500],"Cf":[{"id":0,"edge":2,"reflected":false,"ss":-1,"st":-1,"cd":-39186,"p":-33147,"q":113360,"g":113855},{"id":1,"edge":2,"reflected":true,"ss":1,"st":1,"cd":12917,"p":-9133,"q":88074,"g":62750},{"id":2,"edge":2,"reflected":false,"ss":-1,"st":1,"cd":80483,"p":51554,"q":119909,"g":113855},{"id":3,"edge":2,"reflected":true,"ss":-1,"st":1,"cd":-6772,"p":-9133,"q":88074,"g":104729},{"id":4,"edge":4,"reflected":false,"ss":-1,"st":-1,"cd":-25682,"p":-20967,"q":83048,"g":104073},{"id":5,"edge":4,"reflected":true,"ss":1,"st":1,"cd":-24510,"p":-19335,"q":76744,"g":95269},{"id":6,"edge":4,"reflected":false,"ss":-1,"st":1,"cd":1449,"p":0,"q":86884,"g":104073},{"id":7,"edge":4,"reflected":true,"ss":-1,"st":1,"cd":-25931,"p":-19335,"q":76744,"g":99195},{"id":8,"edge":4,"reflected":false,"ss":1,"st":-1,"cd":-3767,"p":-20967,"q":83048,"g":58829},{"id":9,"edge":4,"reflected":true,"ss":1,"st":-1,"cd":5267,"p":0,"q":71553,"g":95269},{"id":10,"edge":4,"reflected":false,"ss":1,"st":1,"cd":23364,"p":0,"q":86884,"g":58829},{"id":11,"edge":4,"reflected":true,"ss":-1,"st":-1,"cd":3846,"p":0,"q":71553,"g":99195},{"id":12,"edge":5,"reflected":false,"ss":-1,"st":-1,"cd":19687,"p":18602,"q":80996,"g":95269},{"id":13,"edge":5,"reflected":true,"ss":1,"st":1,"cd":21928,"p":20967,"q":83048,"g":99173},{"id":14,"edge":5,"reflected":false,"ss":-1,"st":1,"cd":21731,"p":21826,"q":83472,"g":95269},{"id":15,"edge":5,"reflected":true,"ss":-1,"st":1,"cd":20507,"p":20967,"q":83048,"g":95324},{"id":16,"edge":5,"reflected":false,"ss":1,"st":-1,"cd":21108,"p":18602,"q":80996,"g":99195},{"id":17,"edge":5,"reflected":true,"ss":1,"st":-1,"cd":-5203,"p":0,"q":86884,"g":99173},{"id":18,"edge":5,"reflected":false,"ss":1,"st":1,"cd":23152,"p":21826,"q":83472,"g":99195},{"id":19,"edge":5,"reflected":true,"ss":-1,"st":-1,"cd":-6624,"p":0,"q":86884,"g":95324},{"id":20,"edge":6,"reflected":false,"ss":-1,"st":1,"cd":7651,"p":0,"q":94766,"g":99173},{"id":21,"edge":6,"reflected":true,"ss":-1,"st":1,"cd":-21837,"p":-18602,"q":80996,"g":108816},{"id":22,"edge":6,"reflected":false,"ss":1,"st":1,"cd":9072,"p":0,"q":94766,"g":95324},{"id":23,"edge":6,"reflected":true,"ss":-1,"st":-1,"cd":-23881,"p":-21826,"q":83472,"g":108816}],"Of":[{"id":0,"edge":2,"reflected":false,"ss":-1,"st":-1,"cd":12917,"p":9133,"q":88074,"g":62750},{"id":1,"edge":2,"reflected":true,"ss":1,"st":1,"cd":-39186,"p":33147,"q":113360,"g":113855},{"id":2,"edge":2,"reflected":false,"ss":-1,"st":1,"cd":-6772,"p":9133,"q":88074,"g":104729},{"id":3,"edge":2,"reflected":true,"ss":-1,"st":1,"cd":80483,"p":-51554,"q":119909,"g":113855},{"id":4,"edge":4,"reflected":false,"ss":-1,"st":-1,"cd":-24510,"p":19335,"q":76744,"g":95269},{"id":5,"edge":4,"reflected":true,"ss":1,"st":1,"cd":-25682,"p":20967,"q":83048,"g":104073},{"id":6,"edge":4,"reflected":false,"ss":-1,"st":1,"cd":-25931,"p":19335,"q":76744,"g":99195},{"id":7,"edge":4,"reflected":true,"ss":-1,"st":1,"cd":1449,"p":0,"q":86884,"g":104073},{"id":8,"edge":4,"reflected":false,"ss":1,"st":-1,"cd":5267,"p":0,"q":71553,"g":95269},{"id":9,"edge":4,"reflected":true,"ss":1,"st":-1,"cd":-3767,"p":20967,"q":83048,"g":58829},{"id":10,"edge":4,"reflected":false,"ss":1,"st":1,"cd":3846,"p":0,"q":71553,"g":99195},{"id":11,"edge":4,"reflected":true,"ss":-1,"st":-1,"cd":23364,"p":0,"q":86884,"g":58829},{"id":12,"edge":5,"reflected":false,"ss":-1,"st":-1,"cd":21928,"p":-20967,"q":83048,"g":99173},{"id":13,"edge":5,"reflected":true,"ss":1,"st":1,"cd":19687,"p":-18602,"q":80996,"g":95269},{"id":14,"edge":5,"reflected":false,"ss":-1,"st":1,"cd":20507,"p":-20967,"q":83048,"g":95324},{"id":15,"edge":5,"reflected":true,"ss":-1,"st":1,"cd":21731,"p":-21826,"q":83472,"g":95269},{"id":16,"edge":5,"reflected":false,"ss":1,"st":-1,"cd":-5203,"p":0,"q":86884,"g":99173},{"id":17,"edge":5,"reflected":true,"ss":1,"st":-1,"cd":21108,"p":-18602,"q":80996,"g":99195},{"id":18,"edge":5,"reflected":false,"ss":1,"st":1,"cd":-6624,"p":0,"q":86884,"g":95324},{"id":19,"edge":5,"reflected":true,"ss":-1,"st":-1,"cd":23152,"p":-21826,"q":83472,"g":99195},{"id":20,"edge":6,"reflected":false,"ss":-1,"st":1,"cd":-21837,"p":18602,"q":80996,"g":108816},{"id":21,"edge":6,"reflected":true,"ss":-1,"st":1,"cd":7651,"p":0,"q":94766,"g":99173},{"id":22,"edge":6,"reflected":false,"ss":1,"st":1,"cd":-23881,"p":21826,"q":83472,"g":108816},{"id":23,"edge":6,"reflected":true,"ss":-1,"st":-1,"cd":9072,"p":0,"q":94766,"g":95324}],"denominator":100000},"labels":[{"C":{"p":[3177,0,108816]},"O":{"p":[0,0,94766]}},{"C":{"p":[25648,0,62095],"n":[-14041,0,62095]},"O":{"p":[6130,0,99940],"n":[24463,-13422,103828]}},{"C":{"n":[11680,0,113855]},"O":{"n":[-2623,9133,88074]}},{"C":{"p":[4149,0,104729],"n":[-15540,0,62750]},"O":{"p":[-68803,51554,119909],"n":[50866,-33147,113360]}},{"C":{"p":[25812,0,58829],"n":[3897,0,104073]},"O":{"p":[6294,0,71553],"n":[-23483,19335,76744]}},{"C":{"p":[2448,0,99195],"n":[1027,0,95269]},"O":{"p":[2448,0,86884],"n":[29579,-20967,83048]}},{"C":{"p":[9072,0,95324],"n":[7651,0,99173]},"O":{"p":[-20704,21826,83472],"n":[-18660,18602,80996]}}],"positiveTable":[{"idx":2,"a":"1.12","b":"1.25","l":"1.3"},{"idx":2,"a":"1.25","b":"p","l":"1.115"},{"idx":3,"a":"1.12","b":"1.25","l":"1.4"},{"idx":3,"a":"1.25","b":"p","l":"1.13855"},{"idx":6,"a":"1.12","b":"1.25","l":"1.3"},{"idx":6,"a":"1.25","b":"p","l":"1.0853"},{"idx":7,"a":"1.12","b":"1.3","l":"1.3"},{"idx":7,"a":"1.3","b":"1.4","l":"1.1"},{"idx":7,"a":"1.4","b":"p","l":"1.04073"},{"idx":14,"a":"1.12","b":"1.3","l":"1.2"},{"idx":14,"a":"1.3","b":"1.4","l":"1.06"},{"idx":14,"a":"1.4","b":"1.45","l":"1.01"},{"idx":14,"a":"1.45","b":"1.51","l":".96"},{"idx":14,"a":"1.51","b":"p","l":".95324"},{"idx":15,"a":"1.12","b":"1.3","l":"1.2"},{"idx":15,"a":"1.3","b":"1.4","l":"1.06"},{"idx":15,"a":"1.4","b":"1.45","l":"1.01"},{"idx":15,"a":"1.45","b":"1.51","l":".96"},{"idx":15,"a":"1.51","b":"p","l":".95269"},{"idx":20,"a":"1.12","b":"1.25","l":"1.3"},{"idx":20,"a":"1.25","b":"p","l":"1.1274"},{"idx":21,"a":"1.12","b":"p","l":"1.1014"}],"cornerRefs":[{"idx":0,"kind":"join","ref":1.17},{"idx":0,"kind":"diag","ref":1.075},{"idx":4,"kind":"join","ref":1.149},{"idx":4,"kind":"diag","ref":1.047},{"idx":11,"kind":"join","ref":1.061},{"idx":11,"kind":"diag","ref":0.962},{"idx":12,"kind":"join","ref":"lo"},{"idx":12,"kind":"diag","ref":"lo"},{"idx":19,"kind":"join","ref":"lo"},{"idx":19,"kind":"diag","ref":"lo"},{"idx":23,"kind":"join","ref":1.148},{"idx":23,"kind":"diag","ref":1.056}],"lambdaCf":{"1":".6275","2":"1.13855","3":"1.115","5":".95269","6":"1.04073","7":"1.0853","10":".58829","13":".99173","14":".95269","15":".95324","18":".99195","20":"1.1014","21":"1.1274","22":".95324"}};

const checks=[],tables=[],failures=[];
function gt(name,x,v=0){x=ii(x);let ok=x[0].cmp(v)>0;checks.push({name,lower:dec(x[0],12),upper:decup(x[1],12),threshold:String(v),ok});if(!ok)failures.push(checks.at(-1));}
function ge(name,x,v=0){x=ii(x);let ok=x[0].cmp(v)>=0;checks.push({name,lower:dec(x[0],12),upper:decup(x[1],12),threshold:String(v),comparison:">=",ok});if(!ok)failures.push(checks.at(-1));}
function lt(name,x,v=0){gt(name,ineg(x),rr(v).neg());}
function minI(xs){let a=xs.map(ii);return[a.reduce((v,x)=>x[0].cmp(v)<0?x[0]:v,a[0][0]),a.reduce((v,x)=>x[1].cmp(v)<0?x[1]:v,a[0][1])];}
function coeffs(r){let z={...r};for(let k of["cd","p","q","g"])z[k]=new Rat(r[k],100000);return z;}
const Cf=input.norm.Cf.map(coeffs),Of=input.norm.Of.map(coeffs),Q=rr("9789/2500"),R=root(Q),dc=ia(".5",idiv(root(2),24)),ac=rr("7/12"),d=isub(root(Q.div(2)),".5"),a0=isub(root(Q.sub(".25")),".5");
const gamma=rr(".898"),positive=[2,3,6,7,14,15,20,21],negative=[0,4,11,12,19,23];
function norm2(p,q,l,t){return root(ia(p.pow(2).add(q.pow(2)).add(l.pow(2)),im(l.mul(2),isub(im(p,sin(t)),im(q,cos(t))))));}
function W(t,quadrant){return idiv(ia(1,ia(sin(t),quadrant===1?cos(t):ineg(cos(t)))),2);}
function wholeOuter(p,q,l){return isub(l.sub(p).add(q).div(2),im(R,root(l.sub(p).pow(2).add(q.pow(2)))));}
function allMin(name,values,target=gamma){let m=minI(values);gt(name,m,target);return m;}
function polyRow(name,p,lo,hi){let bs=bernstein(p,lo,hi),lower=bs.reduce((a,b)=>a.cmp(b)<0?a:b);gt(name+" all Bernstein coefficients",lower,0);tables.push({name,interval:[String(lo),String(hi)],degree:p.length-1,coefficient_lower:bs.map(x=>dec(x,9))});}
const expected={Cf:[],Of:[]};
for(const edge of[2,4,5,6]){
 const next=(edge+1)%7;
 for(const sk of Object.keys(input.labels[edge].C))for(const tk of Object.keys(input.labels[next].C)){
  const ss=sk==="p"?1:-1,st=tk==="p"?1:-1;
  const cs=input.labels[edge].C[sk],ct=input.labels[next].C[tk],os=input.labels[edge].O[sk],ot=input.labels[next].O[tk];
  expected.Cf.push({edge,reflected:false,ss,st,cd:cs[0]-ot[0],p:ot[1],q:ot[2],g:cs[2]});
  expected.Cf.push({edge,reflected:true,ss:-st,st:-ss,cd:os[0]-ct[0],p:-os[1],q:os[2],g:ct[2]});
  expected.Of.push({edge,reflected:false,ss,st,cd:os[0]-ct[0],p:os[1],q:os[2],g:ct[2]});
  expected.Of.push({edge,reflected:true,ss:-st,st:-ss,cd:cs[0]-ot[0],p:-ot[1],q:ot[2],g:cs[2]});
 }
}
const signature=r=>["edge","reflected","ss","st","cd","p","q","g"].map(k=>String(r[k])).join(",");
for(const key of["Cf","Of"]){let e=expected[key].map(signature).sort(),a=input.norm[key].map(signature).sort();if(JSON.stringify(a)!==JSON.stringify(e))throw Error("normalized transcription "+key);}
if(Cf.length!==24||Of.length!==24)throw Error("raw coverage");
gt("pi lower",PI,"3.14159");lt("pi upper",PI,"3.14160");
gt("outer diagonal",d,".8992");lt("outer axial",a0,"1.415");gt("outer axial lower",a0,"1.4145");
gt("core diagonal lower",dc,".5589");lt("core diagonal upper",dc,".559");
gt("sin lower across quarter strip",cos(".7"),".764");lt("absolute cosine across quarter strip",sin(".7"),".645");
gt("sin .4>.389",sin(".4"),".389");
gt("cos 1.05>.497",cos("1.05"),".497");gt("cos 1.2>.362",cos("1.2"),".362");
gt("strip lower>.87",angle("lo"),".87");lt("pi/2<1.571",P2,"1.571");
// A. Core source, source +f.
for(const z of Cf){
 gt("Cf "+z.id+" norm derivative",z.q.mul(".764").sub(absI(z.p)[1].mul(".645")),0);
 if(z.st<0){
  let l=z.g;
  gt("Cf "+z.id+" axial primary sign",l.mul(".764").add(z.p),0);
  gt("Cf "+z.id+" axial secondary sign",z.q.sub(l.mul(".645")),0);
  let t=angle("lo"),F=isub(ia(ia(t,z.cd.add(l.div(2))),ia(im(z.p.neg(),a0),im(l.div(2),cos(t)))),im(im(l,isub(a0,".5")),sin(t)));
  let threshold=z.g.cmp(".954")<=0?".921":z.g.cmp(1)<=0?".940":"1.038";
  gt("Cf "+z.id+" negative-target left",F,threshold);
 }else{
  const l=rr(input.lambdaCf[z.id]);ge("Cf "+z.id+" nonnegative core support",rr(z.ss).mul(z.g.sub(l)),0);
  const lo=z.ss<0?"1":"lo",segments=[[lo,"1.25",1],["1.25","p",1],["p","p+.3",2],["p+.3","hi",2]];
  let endpoints=[];
  for(const[a,b,quad]of segments){
   const at=angle(a),bt=angle(b),N=norm2(z.p,z.q,l,bt),s=quad===1?sin(at):isub(sin(at),cos(at));
   gt("Cf "+z.id+" concavity "+a+" "+b,isub(im(l,s),idiv(im(R,N),4)),0);
   for(const t of[at,bt])endpoints.push(isub(ia(ia(t,z.cd.add(l.add(z.p).add(z.q).div(2))),im(l,quad===1?sin(t):isub(sin(t),cos(t)))),im(R,norm2(z.p,z.q,l,t))));
  }
  allMin("Cf "+z.id+" positive-target endpoints",endpoints);
 }
}
gt("Cf low-g derivative",rr(1).sub(rr(".954").mul(root(rr(".25").add(rr(".915").pow(2)))[1])),0);
gt("Cf middle-g derivative",rr(1).sub(root(rr(".25").add(rr(".915").pow(2)))[1]),"-.043");
gt("Cf high-g derivative",rr(1).sub(rr("1.139").mul(root(rr(".25").add(rr(".915").pow(2)))[1])),"-.19");
gt("Cf middle-g continuation",rr(".940").sub(rr(".043").mul(".7")),gamma);
gt("Cf high-g continuation",rr("1.038").sub(rr(".19").mul(".7")),gamma);
lt("Cf negative-source forward cap at 1",isub(isub(im(isub(a0,".5"),sin(1)),im(".5",cos(1))),".5"),0);
// B. Outer source, source +f.
for(const z of Of){
 const l=z.q,m=im(z.p,z.p.cmp(0)>=0?d:a0),t=angle("lo");
 gt("Of "+z.id+" secondary core sign",z.g.sub(l.mul(".645")),0);
 if(z.st<0){
  let F=ia(ia(t,z.cd.add(l.div(2))),ia(m,isub(im(l.div(2),cos(t)),im(l.div(12),sin(t)))));
  gt("Of "+z.id+" negative-target secondary",F,"1.381");
 }else{
  let N=root(isub(l.pow(2).add(z.g.pow(2)),im(l.mul(z.g).mul(2),cos(t))));
  let F=isub(ia(ia(t,z.cd.add(l.sub(z.g).div(2))),ia(m,im(l,cos(t)))),idiv(N,12));
  gt("Of "+z.id+" positive-target secondary left",F,l.cmp(".95")<=0?"1.103":"1.424");
 }
}
gt("Of secondary negative-target derivative",rr(1).sub(rr("1.2").mul(root(rr(".25").add(rr("1/144")))[1])),0);
gt("Of secondary low slope",rr(1).sub(rr(".95").mul(rr("13/12"))),"-.03");
gt("Of secondary high slope",rr(1).sub("1.2").sub(rr("1.139").div(12)),"-.3");
gt("Of secondary low continuation",rr("1.103").sub(rr(".03").mul(".7")),gamma);
gt("Of secondary high continuation",rr("1.424").sub(rr(".3").mul(".7")),gamma);
// Source-primary sign dominance.
for(const role of[3,4,5,6])for(const kind of["C","O"]){
 const P=input.labels[role][kind].p,N=input.labels[role][kind].n,c=rr(P[0]-N[0]).div(100000),p=rr(P[1]-N[1]).div(100000),q=rr(P[2]+N[2]).div(100000);
 gt("role "+role+" "+kind+" sign-difference derivative",q.sub(absI(p)[1]),0);
 gt("role "+role+" "+kind+" sign-difference at zero",ia(c,im(p,kind==="C"?ac:a0)),0);
}
// C. Core source, source -e.
lt("Cf positive-target primary cap at x=.4",ia(rr("1/12"),isub(im(isub(a0,".5"),sin(".4")),im(".5",cos(".4")))),0);
gt("Cf positive-target primary decreasing",rr(".8").mul(".389").add(rr("1.6").mul(".9145").mul(".764")).sub(1),0);
for(const idx of positive){
 const z=Cf[idx],l=rr("1.6"),x=ii(".7");
 gt("Cf "+idx+" primary outer X<0",l.mul(".389").add(z.p),0);gt("Cf "+idx+" primary outer Y>0",l.mul(".764").sub(z.q),0);
 const F=isub(ia(ia(P2,rr(".7").add(z.cd).sub(z.g.div(2))),ia(im(z.p.neg(),a0),im(l.div(2),cos(x)))),ia(idiv(root(l.pow(2).add(z.g.pow(2))),12),im(im(l,isub(a0,".5")),sin(x))));
 gt("Cf "+idx+" positive-target primary endpoint",F,"1.216");
}
for(const idx of negative){
 const z=Cf[idx],PP=im(z.p,z.p.cmp(0)>=0?a0:d);
 gt("Cf "+idx+" negative-target primary decreasing",z.q.mul("1.399").sub(1).sub(z.q.pow(2).div(576)),0);
 let base=isub(ia(P2,z.cd.sub(z.g.div(2)).add(z.q.div(2))),ia(PP,idiv(root(z.g.pow(2).add(z.q.pow(2))),12)));
 gt("Cf "+idx+" negative-target quarter baseline",base,"1.28");
}
let loss=isub(rr(".7"),ia(im(rr("1.134").mul(".915"),idiv(sin(".7"),cos(".7"))),im(rr("1.134").div(12),isub(idiv(1,cos(".7")),1))));
gt("Cf negative-target upper-half loss",loss,"-.21");gt("Cf negative-target continuation",rr("1.28").sub(".21"),gamma);
// D. Outer source, source -e.
lt("Of positive-target side cap at 1.12",isub(isub(a0,".5"),ia(im("13/12",cos("1.12")),im(".5",sin("1.12")))),0);
gt("Of positive-target corner threshold",rr("1.5").sub(a0[1]),0);
function fa(z,l,t,quad){return ia(ia(ia(t,z.cd),wholeOuter(z.p,z.q,l)),ia(im(l,W(t,quad)),im(l.mul(ac),cos(t))));}
const posRows=[];
for(const row of input.positiveTable){
 const z=Of[row.idx],l=rr(row.l),values=[];
 for(const t0 of[row.a,row.b]){const t=angle(t0),a=fa(z,l,t,1),b=ia(a,idiv(isub(im(l,sin(t)),z.g),2));values.push(a,b);}
 const bound=allMin("Of "+row.idx+" positive-primary "+row.a+" "+row.b,values);posRows.push({...row,minimum_lower:dec(bound[0],9)});
}
tables.push({name:"positive core target primary, side rows",rows:posRows});
for(const idx of positive){const row=input.positiveTable.filter(r=>r.idx===idx).at(-1),z=Of[idx],l=rr(row.l);ge("Of "+idx+" terminal multiplier >=g",l.sub(z.g),0);gt("Of "+idx+" terminal multiplier <=1.14",rr("1.14").sub(l),0);}
gt("Of positive-target upper-half derivative",rr(1).sub(rr("1.14").mul(rr("1.059").mul(".645").add("1/12"))),0);
// D2: straight core side.
const negativeSide=[];
for(const idx of[0,11])for(const row of[["lo","1.1","1.11"],["1.1","p",".958"]]){
 const z=Of[idx],l=rr(row[2]),values=[];
 for(const t0 of row.slice(0,2)){const t=angle(t0),a=fa(z,l,t,1),b=ia(a,idiv(isub(z.g,im(l,sin(t))),2));values.push(a,b);}
 const bound=allMin("Of "+idx+" negative-side "+row[0]+" "+row[1],values,".921");negativeSide.push({idx,a:row[0],b:row[1],lambda:row[2],minimum_lower:dec(bound[0],9)});
}
tables.push({name:"negative core target, simple side support",rows:negativeSide});
function factorial(n){let r=1n;for(let k=2;k<=n;k++)r*=BigInt(k);return r;}
function taylor(degree,cosine){let p=Array(degree+1).fill(null).map(()=>rr(0));for(let n=cosine?0:1;n<=degree;n+=2)p[n]=new Rat(((n-(cosine?0:1))/2)%2?-1n:1n,factorial(n));return p;}
const SL=taylor(7,false),SU=taylor(9,false),CL=taylor(10,true);
for(const idx of[4,12,19,23]){
 const z=Of[idx],C=z.cd.add(z.p.neg().add(z.q).add(z.g).div(2)).sub(gamma);gt("Of "+idx+" side sine coefficient",rr(".87").add(C),0);
 const T=pAdd(pAdd(pMul([C,rr(1)],SL),[z.g]),pScale(CL,z.g.mul("13/12")));
 const V=pAdd(pAdd([z.g.pow(2)],pScale(z.p.cmp(0)>=0?SL:SU,z.g.mul(z.p).mul(-2))),pScale(pPow(SU,2),z.p.pow(2).add(z.q.pow(2))));
 polyRow("Of "+idx+" side positive T",T,".87","1.571");polyRow("Of "+idx+" side squared radical majorant",pSub(pPow(T,2),pScale(V,Q)),".87","1.571");
}
// D2: late corner, lambda=.85.
for(const idx of negative){
 const z=Of[idx],l=rr(".85"),vals=[];
 for(const t0 of["1.2","p"]){
  const t=angle(t0),common=ia(ia(t,z.cd),ia(im(l,W(t,1)),wholeOuter(z.p,z.q,l)));
  const join=ia(common,ia(im(l.mul(ac),cos(t)),idiv(isub(z.g,im(l,sin(t))),2)));
  const diag=ia(common,im(dc,ia(im(l,isub(cos(t),sin(t))),z.g)));vals.push(join,diag);
 }
 allMin("Of "+idx+" late negative corner",vals,".903");
}
gt("negative diagonal late derivative",isub(1,im(".85",root(ia(ipow(ia(dc,".5"),2),ipow(isub(dc,".5"),2))))),0);
// D2: early corner, concavity in the core coordinate.
const dcA=ia(dc,".5"),dcB=isub(dc,".5");
function U(t,kind){return ia(1,isub(im(kind==="join"?"13/12":dcA,cos(t)),im(kind==="join"?0:dcB,sin(t))));}
gt("early corner u lower first band",U(angle("1.05"),"diag"),"1.47");lt("early corner u upper first band",U(angle("lo"),"join"),"1.7");
gt("early corner u lower second band",U(angle("1.2"),"diag"),"1.32");lt("early corner u upper second band",U(angle("1.05"),"join"),"1.54");
for(const idx of negative){const z=Of[idx];gt("Of "+idx+" p/q lower",z.p.div(z.q),"-.263");lt("Of "+idx+" p/q upper",z.p.div(z.q),".253");gt("Of "+idx+" q lower",z.q,".767");}
function DD(u){u=rr(u);const t2=Q.sub(u.pow(2));return im(t2,isub(u,im(".263",root(t2))));}
gt("D concavity uniform",rr(6).mul("1.32").sub(rr(".789").mul(Q.sub(rr(2).mul(rr("1.32").pow(2)))).div("1.01")),0);
gt("radical t>1.01",root(Q.sub(rr("1.7").pow(2))),"1.01");
for(const row of[["1.47","1.7","2.8"],["1.32","1.54","2.12"]])for(const u of row.slice(0,2))gt("early corner curvature ratio at "+u,im(row[2],DD(u)),Q);
gt("first core-coordinate concavity",rr(12).mul(".497").sub(rr(2).mul("2.8")),0);
gt("second core-coordinate concavity",rr(12).mul(".362").sub(rr(2).mul("2.12")),0);
gt("extended outer label monotone",rr("1.32").div(root(Q.sub(rr("1.32").pow(2)))[1]).sub(".263"),0);
// Strong convexity of the two endpoint contact curves.
gt("diagonal contact K",ia(ipow(dcA,2),ipow(dcB,2)),"1.12479");gt("join contact K",rr("13/12").pow(2),"1.12479");
const X=[rr(0),rr(1)],XM1=[rr(-1),rr(1)],T2=pSub([Q],pPow(X,2));
const E=pSub(pScale(pSub([rr("1.12479")],pPow(XM1,2)),Q),pMul(pMul(X,XM1),T2));
const AA=[rr(".65").div(".767").sub(".253"),rr(".253")];
polyRow("endpoint curvature E",E,"1.32","1.7");polyRow("endpoint curvature A",AA,"1.32","1.7");
polyRow("endpoint curvature squared bound",pSub(pPow(E,2),pMul(pPow(AA,2),pPow(T2,3))),"1.32","1.7");
const refs=[];
for(const row of input.cornerRefs){
 const z=Of[row.idx],t=angle(row.ref),A=row.kind==="join"?ii("13/12"):dcA,B=row.kind==="join"?ii(0):dcB,bC=row.kind==="join"?ii(".5"):dc;
 const u=ia(1,isub(im(A,cos(t)),im(B,sin(t)))),h=isub(u,".5"),v=root(isub(Q,ipow(u,2)));
 const F=ia(ia(t,z.cd),ia(im(z.p,h),isub(im(z.g,bC),im(z.q,isub(v,".5")))));
 const hp=ineg(ia(im(A,sin(t)),im(B,cos(t)))),Fp=ia(1,im(ia(z.p,im(z.q,idiv(u,v))),hp));
 let lower;if(row.ref==="lo"){gt("Of "+row.idx+" "+row.kind+" boundary derivative",Fp,0);lower=F;}else lower=isub(F,idiv(ipow(Fp,2),"1.3"));
 gt("Of "+row.idx+" "+row.kind+" contact reference completion",lower,gamma);
 refs.push({...row,F_lower:dec(F[0],12),derivative_interval:Fp.map((x,i)=>i?decup(x,12):dec(x,12)),completed_lower:dec(lower[0],12)});
}
tables.push({name:"early negative-core corner contact references",rows:refs});
// Negative core target, upper half.
for(const idx of negative){const z=Of[idx];gt("Of "+idx+" negative-target upper-half baseline",fa(z,z.g,P2,2),".905");}
gt("negative-target upper-half derivative",rr(1).sub(rr("1.139").mul(rr(".645").div(2).add("1/12"))),0);
const report={status:failures.length?"FAIL":"PASS",scope:"All 96 mixed C/O quarter-one raw branches of word 0010111, conditional on stated frame interval, exterior cap and role signs; each cost>.898>.89765.",Q:Q.toString(),fixed_comparisons:checks.length,raw_branches:96,normalized_secondary_rows:48,normalized_primary_representatives:28,failures,tables,checks};
if(typeof console!=="undefined")console.log(JSON.stringify(report,null,2));

