import{readFileSync as R,writeFileSync as W,mkdirSync as M}from"node:fs";
const V=[[0,-1],[0,1],[-1,0],[1,0]],L="udlr";
let G=0;
function parse(s){let r=s.split("\n").filter(x=>x.length),w=Math.max(...r.map(x=>x.length)),h=r.length,n=w*h,a=new Uint8Array(n).fill(1),g=new Uint8Array(n),b=[],p=-1;r.forEach((y,j)=>{for(let i=0;i<y.length;i++){let c=y[i],k=j*w+i;if(c=="#")continue;a[k]=0;if(c=="."||c=="*"||c=="+")g[k]=1;if(c=="$"||c=="*")b.push(k);if(c=="@"||c=="+")p=k}});return{w,h,n,a,g,b,p,D:null}}
function dists(o){let D=[];for(let s=0;s<o.n;s++){if(o.a[s]){D[s]=null;continue}let d=new Int16Array(o.n).fill(-1),q=[s];d[s]=0;for(let h=0;h<q.length;h++){let c=q[h],x=c%o.w,y=(c/o.w)|0;for(let k=0;k<4;k++){let nx=x+V[k][0],ny=y+V[k][1];if(nx<0||ny<0||nx>=o.w||ny>=o.h)continue;let t=ny*o.w+nx;if(!o.a[t]&&d[t]<0){d[t]=d[c]+1;q.push(t)}}}D[s]=d}return D}
function bfs(o,fl,bs,s){let pr=new Int32Array(o.n).fill(-1),pd=new Int8Array(o.n),q=[s];pr[s]=s;for(let h=0;h<q.length;h++){let c=q[h],x=c%o.w,y=(c/o.w)|0;for(let k=0;k<4;k++){let nx=x+V[k][0],ny=y+V[k][1];if(nx<0||ny<0||nx>=o.w||ny>=o.h)continue;let t=ny*o.w+nx;if(fl[t]&&!bs.has(t)&&pr[t]<0){pr[t]=c;pd[t]=k;q.push(t)}}}return{pr,pd}}
function path(pr,pd,s,t){let u=[];for(let c=t;c!=s;c=pr[c])u.push(L[pd[c]]);return u.reverse().join("")}
function dead(o,op,gl,bs){let W=o.w,H=o.h,S=new Set(bs),open=(x,y)=>x>=0&&y>=0&&x<W&&y<H&&op[y*W+x]==1;
for(let b of bs){if(gl[b])continue;let x=b%W,y=(b/W)|0;
for(let ax=-1;ax<=1;ax+=2)for(let ay=-1;ay<=1;ay+=2)if(!open(x+ax,y)&&!open(x,y+ay))return 1;
for(let k=0;k<4;k++){let wx=x+V[k][0],wy=y+V[k][1];if(open(wx,wy))continue;let q=k<2?[2,3]:[0,1],seg=[b],ok=0,ends=0;
for(let d of q)for(let s2=1;;s2++){let cx=x+V[d][0]*s2,cy=y+V[d][1]*s2;if(!open(cx,cy)){ends++;break}if(open(cx+V[k][0],cy+V[k][1]))break;seg.push(cy*W+cx)}
for(let c of seg)if(gl[c])ok=1;if(!ok&&ends==2)return 1}
for(let ox=-1;ox<=0;ox++)for(let oy=-1;oy<=0;oy++){let all=1,nog=1;for(let dx=0;dx<=1;dx++)for(let dy=0;dy<=1;dy++){let cx=x+ox+dx,cy=y+oy+dy;if(cx<0||cy<0||cx>=W||cy>=H)continue;let c=cy*W+cx;if(gl[c])nog=0;if(open(cx,cy)&&!S.has(c))all=0}if(all&&nog)return 1}}
let F=new Set(),ch=1;while(ch){ch=0;for(let b of bs){if(gl[b]||F.has(b))continue;let x=b%W,y=(b/W)|0,blk=(dx,dy)=>{let cx=x+dx,cy=y+dy;if(cx<0||cy<0||cx>=W||cy>=H)return 1;let c=cy*W+cx;return!open(cx,cy)||F.has(c)||(S.has(c)&&gl[c])};if(blk(-1,0)&&blk(1,0)&&blk(0,-1)&&blk(0,1)){F.add(b);ch=1}}}return F.size?1:0}
function hasg(bs,gs,D){let n=bs.length,b=1e9,u=new Array(n).fill(0);(function f(i,s){if(s>=b)return;if(i==n){b=s;return}for(let j=0;j<n;j++){if(u[j])continue;let d=D[bs[i]][gs[j]];if(d<0)continue;u[j]=1;f(i+1,s+d);u[j]=0}})(0,0);return b}
function hmin(bs,gs,D){let s=0;for(let b of bs){let m=1e9;for(let g of gs){let d=D[b][g];if(d>=0&&d<m)m=d}s+=m}return s}
function astar(o,fl,op,tg,gl,gs,bs0,p0,hf){let D=o.D,best=new Map(),done=new Set(),hp=[],tie=0,cmp=(a,b)=>a.f-b.f||a.t-b.t;
function push(nd){nd.t=tie++;hp.push(nd);let i=hp.length-1;while(i>0){let p=(i-1)>>1;if(cmp(hp[p],hp[i])<=0)break;let t=hp[p];hp[p]=hp[i];hp[i]=t;i=p}}
function pop(){let r=hp[0],l=hp.pop();if(hp.length){hp[0]=l;let i=0;for(;;){let a=2*i+1,b=a+1,m=i;if(a<hp.length&&cmp(hp[a],hp[m])<0)m=a;if(b<hp.length&&cmp(hp[b],hp[m])<0)m=b;if(m==i)break;let t=hp[m];hp[m]=hp[i];hp[i]=t;i=m}}return r}
let srt=a=>[...a].sort((x,y)=>x-y),key=(b,c)=>b.join(",")+"|"+c;
function canon(bs,p){let{pr}=bfs(o,fl,new Set(bs),p),c=1e9;for(let i=0;i<o.n;i++)if(pr[i]>=0&&i<c)c=i;return c}
let b0=srt(bs0);if(b0.every(b=>gl[b]))return"";if(dead(o,op,gl,b0))return null;
let c0=canon(b0,p0);best.set(key(b0,c0),0);push({b:b0,p:p0,g:0,f:hf(b0,gs,D),par:null,mv:"",c:c0});
let exp=0,made=1;
while(hp.length){let nd=pop(),kk=key(nd.b,nd.c);if(done.has(kk))continue;done.add(kk);
if(nd.b.every(b=>gl[b])){let u=[],c=nd;while(c){u.push(c.mv);c=c.par}return u.reverse().join("")}
if(++exp>250000||G>1500000)return null;G++;
let bs=new Set(nd.b),{pr,pd}=bfs(o,fl,bs,nd.p);
for(let i=0;i<nd.b.length;i++)for(let k=0;k<4;k++){let b=nd.b[i],dl=V[k][1]*o.w+V[k][0],fr=b-dl,to=b+dl;
if(fr<0||fr>=o.n||pr[fr]<0||!tg[to]||bs.has(to))continue;
let nb=srt(nd.b.map((x,j)=>j==i?to:x));if(dead(o,op,gl,nb))continue;
let g2=nd.g+1,c2=canon(nb,b),k2=key(nb,c2);if(best.has(k2)&&best.get(k2)<=g2)continue;
let h=hf(nb,gs,D);if(h>=1e9)continue;best.set(k2,g2);if(++made>600000)return null;
push({b:nb,p:b,g:g2,f:g2+h,par:nd,mv:path(pr,pd,nd.p,fr)+L[k],c:c2})}}
return null}
function walk(o,pl,bs,t){if(pl==t)return"";let{pr,pd}=bfs(o,(()=>{let f=new Uint8Array(o.n);for(let i=0;i<o.n;i++)f[i]=o.a[i]?0:1;return f})(),bs,pl);return pr[t]<0?null:path(pr,pd,pl,t)}
function appl(o,pl,bs,mv){for(let ch of mv){let k=L.indexOf(ch),d=V[k][1]*o.w+V[k][0],np=pl+d;if(o.a[np]!==0)return null;if(bs.has(np)){let by=np+d;if(o.a[by]!==0||bs.has(by))return null;bs.delete(np);bs.add(by)}pl=np}return pl}
function verify(o,mv){let bs=new Set(o.b),pl=appl(o,o.p,bs,mv);return pl!==null&&[...bs].every(b=>o.g[b])}
function solve(txt){let o=parse(txt);o.D=dists(o);
let F=new Uint8Array(o.n);for(let i=0;i<o.n;i++)F[i]=o.a[i]?0:1;
let gs=[];for(let i=0;i<o.n;i++)if(o.g[i])gs.push(i);
let py=(o.p/o.w)|0,hall=new Uint8Array(o.n);for(let x=0;x<o.w;x++){let c=py*o.w+x;if(F[c])hall[c]=1}
let seen=new Uint8Array(o.n),rooms=[];
for(let s=0;s<o.n;s++){if(!F[s]||(s/o.w|0)==py||seen[s])continue;
let comp=[],q=[s];seen[s]=1;
for(let h=0;h<q.length;h++){let c=q[h];comp.push(c);let x=c%o.w,y=(c/o.w)|0;for(let k=0;k<4;k++){let nx=x+V[k][0],ny=y+V[k][1];if(nx<0||ny<0||nx>=o.w||ny>=o.h)continue;let t=ny*o.w+nx;if(F[t]&&(t/o.w|0)!=py&&!seen[t]){seen[t]=1;q.push(t)}}}
let bx=comp.filter(c=>o.b.includes(c)),gl=comp.filter(c=>o.g[c]);if(!bx.length)continue;
let en=-1;for(let c of comp){let x=c%o.w,y=(c/o.w)|0;for(let k=0;k<4;k++){let nx=x+V[k][0],ny=y+V[k][1];if(ny==py&&nx>=0&&nx<o.w&&F[ny*o.w+nx]){en=ny*o.w+nx;break}}if(en>=0)break}
rooms.push({comp,bx,gl,en})}
let tot=rooms.reduce((a,r)=>a+r.bx.length,0);
if(tot==o.b.length&&rooms.every(r=>r.en>=0&&r.gl.length==r.bx.length)){
let sols=rooms.map(r=>{let fl=new Uint8Array(o.n),op=new Uint8Array(o.n),tg=new Uint8Array(o.n);
for(let c of r.comp){fl[c]=1;op[c]=1;tg[c]=1}fl[r.en]=1;for(let i=0;i<o.n;i++)if(hall[i])op[i]=1;
return astar(o,fl,op,tg,o.g,r.gl,r.bx,r.en,(bs,g2,D)=>hasg(bs,g2,D))});
if(sols.every(s=>s!==null)){let idx=rooms.map((_,i)=>i),ords=[];
(function pm(a,m){if(m==a.length){ords.push([...a]);return}for(let i=m;i<a.length;i++){let t=a[m];a[m]=a[i];a[i]=t;pm(a,m+1);t=a[m];a[m]=a[i];a[i]=t}})(idx,0);
for(let ord of ords){let pl=o.p,bs=new Set(o.b),out="",good=1;
for(let ri of ord){let r=rooms[ri],w=walk(o,pl,bs,r.en);if(w===null){good=0;break}out+=w;pl=appl(o,pl,bs,w);if(pl===null){good=0;break}out+=sols[ri];pl=appl(o,pl,bs,sols[ri]);if(pl===null){good=0;break}}
if(good&&[...bs].every(b=>o.g[b])&&verify(o,out))return out}}}
let fb=astar(o,F,F,F,o.g,gs,o.b,o.p,(bs,g2,D)=>hmin(bs,g2,D));
return fb!==null&&verify(o,fb)?fb:""}
let IN=process.env.MAKEFUN_INPUT_DIR||"/input",OU=process.env.MAKEFUN_OUTPUT_DIR||"/output";
for(let k=1;k<=5;k++){let id="i"+String(k).padStart(3,"0");let t="";try{t=R(IN+"/"+id+"/level.txt","utf8")}catch(e){}
M(OU+"/"+id,{recursive:true});W(OU+"/"+id+"/solution.txt",t?solve(t):"")}
