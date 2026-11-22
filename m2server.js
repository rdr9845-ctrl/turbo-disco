// Multiplayer 2.0 — servidor de torneios privados. Uso: node m2server.js  (porta 8081, sem dependências)
const http=require("http"),crypto=require("crypto"),fs=require("fs"),path=require("path");
const PORT=process.env.PORT||8081,DBF=path.join(process.env.DATA_DIR||__dirname,"m2db.json");
let DB={rooms:{},users:{},sec:{}};try{DB=JSON.parse(fs.readFileSync(DBF,"utf8"))}catch(e){}
let dirty=0;const save=()=>{dirty=1};
const flush=()=>{if(dirty){dirty=0;fs.writeFileSync(DBF+".tmp",JSON.stringify(DB));fs.renameSync(DBF+".tmp",DBF)}};setInterval(flush,1000);process.on("SIGINT",()=>{flush();process.exit()});
const clients=new Map(),now=()=>Date.now();
function frame(s){const b=Buffer.from(s),n=b.length;let h;if(n<126)h=Buffer.from([0x81,n]);else if(n<65536){h=Buffer.alloc(4);h[0]=0x81;h[1]=126;h.writeUInt16BE(n,2)}else{h=Buffer.alloc(10);h[0]=0x81;h[1]=127;h.writeBigUInt64BE(BigInt(n),2)}return Buffer.concat([h,b])}
function parse(s,chunk,cb){s.buf=Buffer.concat([s.buf,chunk]);for(;;){const b=s.buf;if(b.length<2)return;const op=b[0]&15,m=b[1]&128;let len=b[1]&127,o=2;if(len==126){if(b.length<4)return;len=b.readUInt16BE(2);o=4}else if(len==127){if(b.length<10)return;len=Number(b.readBigUInt64BE(2));o=10}if(len>1e6)return s.destroy();const mk=m?4:0;if(b.length<o+mk+len)return;let p=b.subarray(o+mk,o+mk+len);if(m){const k=b.subarray(o,o+4);p=Buffer.from(p.map((x,i)=>x^k[i%4]))}s.buf=b.subarray(o+mk+len);if(op==8)return s.end();if(op==9){s.write(Buffer.concat([Buffer.from([0x8a,p.length]),p]));continue}if(op==1)cb(p.toString())}}
const send=(s,o)=>{s.writable&&s.write(frame(JSON.stringify(o)))},toUser=(u,o)=>(clients.get(u)||[]).forEach(s=>send(s,o));
const gen=()=>{let c;do c="BMC-"+(1000+crypto.randomInt(9000))+"-"+Array.from({length:3},()=>"ABCDEFGHJKLMNPQRSTUVWXYZ"[crypto.randomInt(24)]).join("");while(DB.rooms[c]);return c};
const U=u=>DB.users[u]||(DB.users[u]={name:"?",av:"👤",notes:[],invites:[],hist:[]});
function notify(uids,text,code){uids.forEach(u=>{const n={id:crypto.randomUUID(),text,code,ts:now(),read:0};U(u).notes.unshift(n);U(u).notes=U(u).notes.slice(0,100);toUser(u,{t:"note",n})});save()}
const log=(r,u,x)=>{r.audit.unshift({ts:now(),by:U(u).name,x});r.audit=r.audit.slice(0,200)};
const view=r=>({...r,players:r.players.map(p=>({...p,online:clients.has(p.uid)}))});
const bc=r=>{upd(r);save();r.players.forEach(p=>toUser(p.uid,{t:"room",room:view(r)}))};
function upd(r){if(["live","done","cancel"].includes(r.status))return;const p=r.players,all=p.length>=2&&p.every(x=>x.team);const was=r.status;r.status=r.published?"sched":all&&(p.length==r.max||r.locked)?"teams":p.length<2?"wait":"open";if(r.status=="teams"&&was!="teams")notify(p.map(x=>x.uid),"Todas as equipas estão escolhidas em "+r.name,r.code)}
function rr(ids,legs){const a=ids.slice();if(a.length%2)a.push(null);const n=a.length,out=[];for(let i=0;i<n-1;i++){const m=[];for(let j=0;j<n/2;j++){const x=a[j],y=a[n-1-j];if(x&&y)m.push(i%2?[y,x]:[x,y])}out.push(m);a.splice(1,0,a.pop())}return legs>1?out.concat(out.map(m=>m.map(([x,y])=>[y,x]))):out}
let mid=0;const mkM=(r,rd,a,b,at)=>({id:r.code+"-"+(++r.seq),rd,a,b,at,st:"sched",sa:null,sb:null,rep:{},ready:{},rem:{}});
const KO=["Final","Meias-finais","Quartos de final","Oitavos de final"];
const koName=n=>n<=2?"Final":n<=4?"Meias-finais":n<=8?"Quartos de final":"Oitavos de final";
function build(r){const ids=r.players.map(p=>p.uid),t0=r.cfg.start,gap=(r.cfg.gap||2)*864e5;r.seq=0;r.matches=[];
 if(r.fmt=="league"){rr(ids,r.cfg.legs||1).forEach((m,i)=>m.forEach(([a,b])=>r.matches.push(mkM(r,"Jornada "+(i+1),a,b,t0+i*gap))))}
 else{const s=ids.sort(()=>Math.random()-.5);for(let i=0;i<s.length;i+=2){if(s[i+1])r.matches.push(mkM(r,koName(s.length),s[i],s[i+1],t0));else r.bye=(r.bye||[]).concat(s[i])}}}
function adv(r){if(r.fmt=="league"){if(r.matches.every(m=>m.st=="done")){const T=table(r);fin(r,T[0].uid)}return}
 const rd=r.matches[r.matches.length-1].rd,last=r.matches.filter(m=>m.rd==rd);if(!last.every(m=>m.st=="done"))return;
 const w=(r.bye||[]).concat(last.map(m=>m.sa>m.sb?m.a:m.b));r.bye=[];if(w.length==1)return fin(r,w[0]);
 const at=Math.max(...last.map(m=>m.at))+(r.cfg.gap||2)*864e5;for(let i=0;i<w.length;i+=2)w[i+1]?r.matches.push(mkM(r,koName(w.length),w[i],w[i+1],at)):r.bye.push(w[i]);
 notify(r.players.map(p=>p.uid),"Nova jornada publicada: "+koName(w.length),r.code)}
function table(r){const t={};r.players.forEach(p=>t[p.uid]={uid:p.uid,w:0,l:0,pf:0,pa:0});r.matches.filter(m=>m.st=="done").forEach(m=>{t[m.a].pf+=m.sa;t[m.a].pa+=m.sb;t[m.b].pf+=m.sb;t[m.b].pa+=m.sa;(m.sa>m.sb?(t[m.a].w++,t[m.b].l++):(t[m.b].w++,t[m.a].l++))});return Object.values(t).sort((a,b)=>b.w-a.w||(b.pf-b.pa)-(a.pf-a.pa)||b.pf-a.pf)}
function fin(r,u){r.status="done";r.champion=u;const p=r.players.find(x=>x.uid==u);log(r,r.org,"Campeão: "+p.name);r.players.forEach(x=>U(x.uid).hist.unshift({code:r.code,name:r.name,champion:p.name,team:p.team,ts:now()}));notify(r.players.map(x=>x.uid),"Torneio terminado. Campeão: "+p.name,r.code)}
function confirm(r,m,a,b,by){m.sa=a;m.sb=b;m.st="done";log(r,by,`Resultado ${nm(r,m.a)} ${a}-${b} ${nm(r,m.b)}`);notify([m.a,m.b],"Resultado confirmado: "+a+"-"+b,r.code);adv(r)}
const nm=(r,u)=>(r.players.find(p=>p.uid==u)||{name:"?"}).name;
function tick(){const t=now();for(const r of Object.values(DB.rooms)){if(!["sched","live"].includes(r.status))continue;
 if(r.status=="sched"&&r.matches.length&&t>=Math.min(...r.matches.map(m=>m.at))){r.status="live";bc(r)}
 for(const m of r.matches){if(m.st!="sched"||!m.at)continue;const d=m.at-t;
  for(const [k,ms,tx] of [["d",864e5,"24 horas"],["h",36e5,"1 hora"],["q",9e5,"15 minutos"]])if(d<=ms&&d>0&&!m.rem[k]){m.rem[k]=1;notify([m.a,m.b],`Jogo em ${tx}: ${nm(r,m.a)} vs ${nm(r,m.b)}`,r.code)}
  if(d<=0&&!m.rem.s){m.rem.s=1;notify([m.a,m.b],`O jogo começou: ${nm(r,m.a)} vs ${nm(r,m.b)}. Carrega em ESTOU PRONTO.`,r.code);bc(r)}
  const w=(r.cfg.wait||0)*6e4;if(r.cfg.forfeit&&d<-w&&w>=0&&(m.ready[m.a]!=m.ready[m.b])){const win=m.ready[m.a]?m.a:m.b;confirm(r,m,win==m.a?20:0,win==m.a?0:20,r.org);log(r,r.org,"Derrota por falta de comparência (regra prévia)");bc(r)}}}save()}
setInterval(tick,15000);
function handle(s,m){const E=x=>send(s,{t:"err",m:x});
 if(m.t=="hello"){if(!m.uid||!m.sec||m.sec.length<16)return E("Conta inválida");if(DB.sec[m.uid]&&DB.sec[m.uid]!=m.sec)return E("Credencial da conta inválida");DB.sec[m.uid]=m.sec;s.uid=m.uid;const u=U(m.uid);u.name=String(m.name||"Jogador").slice(0,24);u.av=String(m.av||"👤").slice(0,4);(clients.get(m.uid)||clients.set(m.uid,new Set()).get(m.uid)).add(s);save();return send(s,{t:"hi"})}
 const me=s.uid;if(!me)return E("Sem sessão");const R=()=>{const r=DB.rooms[String(m.code||"").toUpperCase()];if(!r)E("Sala não encontrada");return r},O=r=>r&&(r.org==me||E("Só o organizador"));
 if(m.t=="my"){const rs=Object.values(DB.rooms).filter(r=>r.players.some(p=>p.uid==me));return send(s,{t:"my",rooms:rs.map(view),pub:Object.values(DB.rooms).filter(r=>!r.priv&&r.status=="open").map(r=>({code:r.code,name:r.name,lg:r.lg,n:r.players.length,max:r.max})),notes:U(me).notes,invites:U(me).invites,hist:U(me).hist})}
 if(m.t=="create"){const c=m.cfg||{};if(!(c.name||"").trim()||!Array.isArray(c.teams)||c.teams.length<2)return E("Dados inválidos");const mx=Math.max(2,Math.min(16,+c.max||4)),code=gen();if(c.teams.length<mx)return E("Poucas equipas para "+mx+" participantes");
  const r=DB.rooms[code]={code,name:String(c.name).slice(0,40),desc:String(c.desc||"").slice(0,300),lg:c.lg,max:mx,teams:c.teams.slice(0,60).map(String),fmt:c.fmt=="ko"?"ko":"league",priv:c.priv!==0,tz:String(c.tz||"UTC"),org:me,players:[{uid:me,name:U(me).name,av:U(me).av,team:null}],matches:[],status:"wait",published:0,locked:0,audit:[],created:now(),seq:0,cfg:{start:+c.start||now()+864e5,gap:+c.gap||2,legs:+c.legs||1,wait:+c.wait||10,forfeit:c.forfeit?1:0}};log(r,me,"Sala criada");bc(r);return send(s,{t:"joined",code})}
 const r=R();if(!r)return;const p=r.players.find(x=>x.uid==me),started=["live","done","cancel"].includes(r.status)||r.published;
 if(m.t=="room"){if(!p&&r.priv)return E("Sala privada");return send(s,{t:"room",room:view(r)})}
 if(m.t=="join"){if(p)return send(s,{t:"joined",code:r.code});if(started||r.locked)return E("Inscrições fechadas");if(r.players.length>=r.max)return E("Sala cheia");r.players.push({uid:me,name:U(me).name,av:U(me).av,team:null});U(me).invites=U(me).invites.filter(i=>i.code!=r.code);log(r,me,"Entrou na sala");notify(r.players.filter(x=>x.uid!=me).map(x=>x.uid),U(me).name+" entrou em "+r.name,r.code);bc(r);return send(s,{t:"joined",code:r.code})}
 if(!p)return E("Não participas nesta sala");
 if(m.t=="pick"){if(started)return E("Equipas bloqueadas: o torneio já começou");if(p.team)return E("Já tens equipa. Pede autorização ao organizador.");if(!r.teams.includes(m.team))return E("Equipa inválida");const o=r.players.find(x=>x.team==m.team);if(o)return E("Equipa já reservada por "+o.name);p.team=m.team;log(r,me,"Reservou "+m.team);return bc(r)}
 if(m.t=="leave"){if(started)return E("O torneio já começou");if(r.org==me)return E("O organizador deve cancelar a sala");r.players=r.players.filter(x=>x.uid!=me);log(r,me,"Saiu (equipa libertada)");bc(r);return send(s,{t:"left"})}
 if(m.t=="ready"){const x=r.matches.find(y=>y.id==m.mid);if(!x||x.st!="sched"||![x.a,x.b].includes(me))return E("Jogo inválido");if(now()<x.at-9e5)return E("A sala abre 15 min antes");x.ready[me]=1;if(x.ready[x.a]&&x.ready[x.b]){notify([x.a,x.b],"Adversário pronto: o jogo pode começar",r.code);x.st="live"}else notify([x.a==me?x.b:x.a],nm(r,me)+" está pronto",r.code);return bc(r)}
 if(m.t=="report"){const x=r.matches.find(y=>y.id==m.mid);const a=+m.a,b=+m.b;if(!x||!["sched","live"].includes(x.st)||![x.a,x.b].includes(me))return E("Jogo inválido");if(!Number.isInteger(a)||!Number.isInteger(b)||a<0||b<0||a>300||b>300||(a==b))return E("Resultado inválido (sem empates)");x.rep[me]=[a,b];const o=x.rep[me==x.a?x.b:x.a];if(o){if(o[0]==a&&o[1]==b)confirm(r,x,a,b,me);else{x.rep={};notify([r.org,x.a,x.b],"Resultados divergentes: o organizador decide",r.code)}}else notify([x.a==me?x.b:x.a],"Aguarda a tua confirmação do resultado",r.code);return bc(r)}
 if(m.t=="note-read"){U(me).notes.forEach(n=>n.read=1);return save()}
 if(!O(r))return;
 if(m.t=="invite"){const q=String(m.name||"").toLowerCase(),u=Object.keys(DB.users).find(k=>DB.users[k].name.toLowerCase()==q);if(!u)return E("Utilizador não encontrado");U(u).invites.push({code:r.code,name:r.name,from:U(me).name});notify([u],U(me).name+" convidou-te para "+r.name+" ("+r.code+")",r.code);return E("Convite enviado")}
 if(m.t=="kick"){if(started||m.uid==me)return E("Não permitido");r.players=r.players.filter(x=>x.uid!=m.uid);log(r,me,"Removeu "+m.uid);notify([m.uid],"Foste removido de "+r.name,r.code);return bc(r)}
 if(m.t=="setteam"){const q=r.players.find(x=>x.uid==m.uid);if(!q||started)return E("Não permitido");if(m.team&&r.players.some(x=>x.team==m.team&&x.uid!=m.uid))return E("Equipa já reservada");q.team=m.team||null;log(r,me,"Alterou equipa de "+q.name);return bc(r)}
 if(m.t=="lock"){r.locked=m.v?1:0;log(r,me,r.locked?"Inscrições bloqueadas":"Inscrições reabertas");return bc(r)}
 if(m.t=="gen"){if(started)return E("Já publicado");if(r.players.length<2||!r.players.every(x=>x.team))return E("Todos os participantes precisam de equipa");Object.assign(r.cfg,m.cfg||{});r.fmt=m.fmt=="ko"?"ko":"league";build(r);log(r,me,"Calendário gerado");return bc(r)}
 if(m.t=="publish"){if(!r.matches.length)return E("Gera o calendário primeiro");r.published=1;log(r,me,"Calendário publicado");notify(r.players.map(x=>x.uid),"Calendário publicado: "+r.name,r.code);return bc(r)}
 if(m.t=="setat"||m.t=="postpone"){const x=r.matches.find(y=>y.id==m.mid);if(!x||x.st=="done")return E("Jogo inválido");if(m.t=="postpone"){x.st="postponed";log(r,me,"Adiou "+x.id)}else{x.at=+m.at;x.st="sched";x.rem={};x.ready={};log(r,me,"Reagendou "+x.id+" para "+new Date(x.at).toISOString())}notify([x.a,x.b],"Jogo "+(m.t=="postpone"?"adiado":"reagendado")+": "+nm(r,x.a)+" vs "+nm(r,x.b),r.code);return bc(r)}
 if(m.t=="setres"){const x=r.matches.find(y=>y.id==m.mid),a=+m.a,b=+m.b;if(!x||x.st=="done"||!Number.isInteger(a)||!Number.isInteger(b)||a==b)return E("Resultado inválido");log(r,me,"Resultado administrativo");confirm(r,x,a,b,me);return bc(r)}
 if(m.t=="cancel"){r.status="cancel";log(r,me,"Torneio cancelado");notify(r.players.map(x=>x.uid),"Torneio cancelado: "+r.name,r.code);return bc(r)}
}
const GAME=[path.join(__dirname,"index.html"),path.join(__dirname,"..","Basketball_Manager_Career.html")].find(f=>fs.existsSync(f));
const srv=http.createServer((q,res)=>{if(q.url=="/health")return res.end("ok");if(GAME&&(q.url=="/"||q.url.startsWith("/?")||q.url=="/index.html")){res.writeHead(200,{"Content-Type":"text/html; charset=utf-8","Cache-Control":"no-cache"});return fs.createReadStream(GAME).pipe(res)}res.statusCode=404;res.end("BMC Multiplayer 2.0")});
setInterval(()=>clients.forEach(c=>c.forEach(s=>s.writable&&s.write(Buffer.from([0x89,0])))),25000);
srv.on("upgrade",(req,s)=>{const k=req.headers["sec-websocket-key"];if(!k)return s.destroy();s.write("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: "+crypto.createHash("sha1").update(k+"258EAFA5-E914-47DA-95CA-C5AB0DC85B11").digest("base64")+"\r\n\r\n");s.buf=Buffer.alloc(0);
 s.on("data",c=>parse(s,c,t=>{try{handle(s,JSON.parse(t))}catch(e){console.error(e)}}));const cl=()=>{if(s.uid){const c=clients.get(s.uid);c&&(c.delete(s),c.size||clients.delete(s.uid))}};s.on("close",cl);s.on("error",cl)});
srv.listen(PORT,"0.0.0.0",()=>console.log("BMC Multiplayer 2.0 na porta "+PORT+(GAME?" (a servir o jogo em /)":" (jogo não encontrado)")));
