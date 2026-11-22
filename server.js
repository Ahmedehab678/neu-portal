'use strict';
// بوابة الخدمات الطلابية - Backend (Node 22+، بدون أي مكتبات خارجية)
const http=require('node:http'),fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto');
const {DatabaseSync}=require('node:sqlite');

const PORT=+process.env.PORT||3000;
const DATA=process.env.DATA_DIR||path.join(__dirname,'data');
const TZ='Africa/Cairo';
const DEPTS={affairs:{cap:120},clinic:{cap:80}};
const OWNER_ID=(process.env.ADMIN_USER||'admin').toLowerCase();
const MAX_UPLOAD=20*1048576;
const FILE_TYPES=new Set(['application/pdf','image/png','image/jpeg','image/gif','image/webp','text/plain','text/markdown','text/csv','video/mp4','video/webm']);
const SECRET=process.env.APP_SECRET||'neu-portal';
fs.mkdirSync(path.join(DATA,'files'),{recursive:true});

const db=new DatabaseSync(path.join(DATA,'app.db'));
db.exec(`PRAGMA journal_mode=WAL;
CREATE TABLE IF NOT EXISTS accounts(id TEXT PRIMARY KEY,name TEXT NOT NULL,role TEXT NOT NULL,dept TEXT DEFAULT '',salt TEXT,hash TEXT,t INTEGER);
CREATE TABLE IF NOT EXISTS sessions(token TEXT PRIMARY KEY,uid TEXT,exp INTEGER);
CREATE TABLE IF NOT EXISTS docs(path TEXT NOT NULL,id TEXT NOT NULL,data TEXT NOT NULL,PRIMARY KEY(path,id));
CREATE TABLE IF NOT EXISTS files(id TEXT PRIMARY KEY,uid TEXT,ctype TEXT,size INTEGER,t INTEGER);
CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY,v TEXT);`);
for(const c of ["ALTER TABLE accounts ADD COLUMN college TEXT DEFAULT ''","ALTER TABLE accounts ADD COLUMN year INTEGER DEFAULT 0"]){try{db.exec(c)}catch(e){}}
const q=(s,...a)=>db.prepare(s).all(...a),q1=(s,...a)=>db.prepare(s).get(...a),run=(s,...a)=>db.prepare(s).run(...a);

// ---------- أدوات ----------
const E=(code,msg)=>Object.assign(new Error(msg),{code});
const str=(v,n)=>String(v==null?'':v).trim().slice(0,n);
const sha=s=>crypto.createHash('sha256').update(s).digest('hex');
const rid=()=>crypto.randomBytes(10).toString('hex');
const norm=s=>String(s||'').trim().replace(/[^A-Za-z0-9_-]/g,'').toLowerCase().slice(0,40);
const hashPw=(pw,salt)=>crypto.scryptSync(pw,salt,32).toString('hex');
const verify=(pw,a)=>{if(!a.salt||!a.hash)return false;const x=Buffer.from(hashPw(pw,a.salt),'hex'),y=Buffer.from(a.hash,'hex');return x.length===y.length&&crypto.timingSafeEqual(x,y)};
const setPw=(id,pw)=>{const salt=crypto.randomBytes(16).toString('hex');run('UPDATE accounts SET salt=?,hash=? WHERE id=?',salt,hashPw(pw,salt),id);run('DELETE FROM sessions WHERE uid=?',id)};
const pub=a=>({id:a.id,name:a.name,role:a.role,dept:a.dept||'',college:a.college||'',year:a.year||0});
const cairoDay=o=>new Intl.DateTimeFormat('en-CA',{timeZone:TZ}).format(new Date(Date.now()+o*864e5));
function cairoMs(day,h,mi){const [y,mo,d]=day.split('-').map(Number),g=Date.UTC(y,mo-1,d,h,mi);const P=Object.fromEntries(new Intl.DateTimeFormat('en-US',{timeZone:TZ,hourCycle:'h23',year:'numeric',month:'numeric',day:'numeric',hour:'numeric',minute:'numeric'}).formatToParts(g).map(x=>[x.type,+x.value]));return g-(Date.UTC(P.year,P.month-1,P.day,P.hour,P.minute)-g)}
let lastT=0;const nowT=()=>(lastT=Math.max(Date.now(),lastT+1));
const anonId=uid=>crypto.createHmac('sha256',SECRET).update(uid).digest('hex').slice(0,12);

const hits=new Map();
function limited(k,max,win){const n=Date.now();let h=hits.get(k);if(!h||h.until<n){h={n:0,until:n+win};hits.set(k,h)}return h.n>=max?Math.ceil((h.until-n)/1000):0}
const bump=k=>{const h=hits.get(k);if(h)h.n++};
setInterval(()=>{const n=Date.now();for(const[k,h]of hits)if(h.until<n)hits.delete(k);run('DELETE FROM sessions WHERE exp<?',n)},600000).unref();
const ipOf=req=>String(req.headers['x-forwarded-for']||req.socket.remoteAddress||'').split(',')[0].trim();

// ---------- الكليات ونظام الدرجات (قابلة للتعديل من لوحة المسؤول) ----------
const SCALE=[['A+',4,97],['A',4,93],['A-',3.7,89],['B+',3.3,84],['B',3,80],['B-',2.7,76],['C+',2.3,73],['C',2,70],['C-',1.7,67],['D+',1.3,64],['D',1,60],['F',0,0]].map(([g,pts,min])=>({g,pts,min}));
const STAND=[{min:3.5,label:'ممتاز'},{min:3,label:'جيد جداً'},{min:2,label:'جيد'},{min:0,label:'إنذار أكاديمي'}];
const DEFAULT_CFG={colleges:[['engineering','كلية الهندسة',5],['computers','كلية الحاسبات والمعلومات',4],['business','كلية إدارة الأعمال',4],['pharmacy','كلية الصيدلة',5]].map(([id,name,years])=>({id,name,years,scale:SCALE,standings:STAND}))};
function getCfg(){const r=q1("SELECT v FROM meta WHERE k='config'");try{return r?JSON.parse(r.v):DEFAULT_CFG}catch(e){return DEFAULT_CFG}}
function cleanCfg(c){
  if(!c||!Array.isArray(c.colleges)||!c.colleges.length||c.colleges.length>30)throw E(400,'قائمة الكليات غير صالحة');
  const seen=new Set();
  return{colleges:c.colleges.map(x=>{
    x=x||{};const id=norm(x.id),name=str(x.name,80),years=Math.max(1,Math.min(8,Math.round(+x.years)||4));
    const scale=(Array.isArray(x.scale)?x.scale:[]).slice(0,20).map(t=>({g:str(t&&t.g,4),pts:+(t&&t.pts),min:+(t&&t.min)}));
    const standings=(Array.isArray(x.standings)?x.standings:[]).slice(0,10).map(t=>({min:+(t&&t.min),label:str(t&&t.label,40)}));
    if(!id||!name||seen.has(id))throw E(400,'كل كلية لازم يكون لها id واسم، والـ id مش متكرر');seen.add(id);
    if(scale.length<2||scale.some(t=>!t.g||!(t.pts>=0&&t.pts<=5)||!(t.min>=0&&t.min<=100)))throw E(400,`نظام درجات «${name}» غير صالح`);
    if(!standings.length||standings.some(t=>!Number.isFinite(t.min)||!t.label))throw E(400,`الحالات الأكاديمية في «${name}» غير صالحة`);
    return{id,name,years,scale,standings};
  })};
}
function cleanGpa(b){
  b=b&&typeof b==='object'?b:{};
  const num=(v,lo,hi)=>{v=+v;return Number.isFinite(v)?Math.max(lo,Math.min(hi,v)):0};
  const cs=a=>(Array.isArray(a)?a:[]).slice(0,20).map(x=>({name:str(x&&x.name,80),credits:num(x&&x.credits,0,12),grade:str(x&&x.grade,4)}));
  const p=b.prior&&typeof b.prior==='object'?{credits:num(b.prior.credits,0,300),gpa:num(b.prior.gpa,0,5)}:null,pl=b.plan||{};
  return{prior:p&&p.credits>0?p:null,terms:(Array.isArray(b.terms)?b.terms:[]).slice(0,24).map(t=>({name:str(t&&t.name,60),courses:cs(t&&t.courses)})),plan:{target:num(pl.target,0,5),courses:cs(pl.courses)}};
}

// ---------- الجلسات ----------
const cookies=req=>Object.fromEntries((req.headers.cookie||'').split(';').map(s=>s.trim().split('=')).filter(a=>a[0]).map(a=>[a[0],decodeURIComponent(a[1]||'')]));
function startSession(req,res,uid,ms){
  const tk=crypto.randomBytes(32).toString('hex');run('INSERT INTO sessions VALUES(?,?,?)',sha(tk),uid,Date.now()+ms);
  const sec=(req.headers['x-forwarded-proto']==='https'||process.env.COOKIE_SECURE==='1')?'; Secure':'';
  res.setHeader('Set-Cookie',`sid=${tk}; HttpOnly; SameSite=Lax; Path=/; Max-Age=${Math.floor(ms/1000)}${sec}`);
}
function authOf(req){
  const tk=cookies(req).sid,s=tk&&q1('SELECT * FROM sessions WHERE token=?',sha(tk));
  if(!s||s.exp<Date.now())return null;return q1('SELECT * FROM accounts WHERE id=?',s.uid)||null;
}
function need(req,role){
  const a=authOf(req);if(!a)throw E(401,'سجّل الدخول أولاً');
  if(role==='owner'){if(a.role!=='owner')throw E(403,'للمسؤول فقط');return a}
  if(a.role==='owner')throw E(403,'حساب المسؤول لا يستخدم هذه الخدمة');return a;
}

// ---------- قاعدة المستندات + SSE ----------
const getDoc=(p,id)=>{const r=q1('SELECT data FROM docs WHERE path=? AND id=?',p,id);return r?JSON.parse(r.data):null};
const putDoc=(p,id,d)=>run('INSERT INTO docs(path,id,data) VALUES(?,?,?) ON CONFLICT(path,id) DO UPDATE SET data=excluded.data',p,id,JSON.stringify(d));
const delDoc=(p,id)=>run('DELETE FROM docs WHERE path=? AND id=?',p,id);
const listDocs=p=>q('SELECT id,data FROM docs WHERE path=?',p).map(r=>({id:r.id,data:JSON.parse(r.data)}));
const clients=new Set(),dirty=new Set();
const emit=p=>dirty.add(p);
function flush(){if(!dirty.size)return;const ps=[...dirty];dirty.clear();for(const p of ps)for(const c of clients)c.write('data: '+p+'\n\n')}
setInterval(flush,150);
setInterval(()=>{for(const c of clients)c.write(': ping\n\n')},20000);

const endOf=s=>s.startMs+s.dur*60000;
const ovl=(a,b)=>a.startMs<endOf(b)&&b.startMs<endOf(a);
const ID_RE=/^[\w-]{1,100}$/,KEYS=new Set(['slots','msgs','courses','reviews','services','tickets','materials','likes']);
function parse(p,isCol){
  const s=String(p||'').split('/').filter(Boolean);
  if(isCol){if(s.length===1||(s.length===3&&s[0]==='slots'&&s[2]==='msgs'&&ID_RE.test(s[1]))){const key=s.length===1?s[0]:'msgs';if(KEYS.has(key))return{col:s.join('/'),key}}}
  else if(s.length===2&&KEYS.has(s[0])&&s[0]!=='msgs'&&ID_RE.test(s[1]))return{col:s[0],key:s[0],id:s[1]};
  throw E(400,'مسار غير صالح');
}
const mask=(d,u,f)=>d.uid===u.id?d:{...d,...f};
function view(key,u,list){
  return list.map(({id,data:d})=>{
    switch(key){
      case 'slots':return{id,data:(d.advisorId===u.id||d.studentId===u.id)?d:{...d,studentId:'',studentName:'',topic:''}};
      case 'tickets':return{id,data:(d.uid===u.id||(u.role==='staff'&&d.dept===u.dept))?d:{...d,uid:'',name:''}};
      case 'reviews':return d.uid===u.id?{id,data:d}:{id:d.courseId+'_'+anonId(d.uid),data:{...d,uid:''}};
      case 'likes':case 'materials':return{id,data:mask(d,u,{uid:''})};
      case 'courses':return{id,data:{...d,by:''}};
      default:return{id,data:d};
    }
  });
}
const SLOT_DURS=[15,20,30,45];
function svcData(u,d){
  if(u.role!=='staff'||!DEPTS[u.dept])throw E(403,'غير مسموح');
  const name=str(d.name,150);if(!name)throw E(400,'اكتب اسم الخدمة');
  const docs=(Array.isArray(d.docs)?d.docs:[]).map(x=>str(x,200)).filter(Boolean).slice(0,30);
  return{dept:u.dept,name,docs,mins:Math.max(1,Math.min(120,+d.mins||5)),notes:str(d.notes,300),sample:false,by:u.id,t:Date.now()};
}
function dbOp(u,b){
  const op=b.op,d=b.data&&typeof b.data==='object'&&!Array.isArray(b.data)?b.data:{};
  if(op==='list'){
    const{col,key}=parse(b.path,true);let l=listDocs(col);
    if(key==='msgs'){const s=getDoc('slots',col.split('/')[1]);if(!s||(s.advisorId!==u.id&&s.studentId!==u.id))return{docs:[]};l.sort((a,b)=>a.data.t-b.data.t)}
    return{docs:view(key,u,l)};
  }
  if(op==='get'){const{col,key,id}=parse(b.path,false),x=getDoc(col,id);return x?{exists:true,data:view(key,u,[{id,data:x}])[0].data}:{exists:false}}
  if(op==='add'){
    const{col,key}=parse(b.path,true),id=rid(),t=nowT();let doc;
    if(key==='slots'){
      if(u.role!=='advisor')throw E(403,'للمرشدين فقط');
      const s={startMs:+d.startMs,dur:+d.dur};
      if(!Number.isFinite(s.startMs)||!SLOT_DURS.includes(s.dur)||s.startMs<Date.now()-6e4||s.startMs>Date.now()+180*864e5)throw E(400,'موعد غير صالح');
      if(listDocs('slots').some(x=>x.data.advisorId===u.id&&ovl(x.data,s)))throw E(409,'يتداخل مع موعد آخر');
      doc={advisorId:u.id,advisorName:u.name,...s,status:'open',studentId:'',studentName:'',topic:''};
    }else if(key==='msgs'){
      const s=getDoc('slots',col.split('/')[1]),text=str(d.text,1000);
      if(!s||s.status!=='booked'||(s.advisorId!==u.id&&s.studentId!==u.id))throw E(403,'غير مسموح');if(!text)throw E(400,'رسالة فارغة');
      doc={uid:u.id,name:u.name,text,t};
    }else if(key==='courses'){
      const name=str(d.name,120),doctor=str(d.doctor,120).replace(/^د\.?\s*/,'');if(!name||!doctor)throw E(400,'اكتب اسم المادة والدكتور');
      if(listDocs('courses').some(x=>x.data.name.toLowerCase()===name.toLowerCase()&&x.data.doctor.toLowerCase()===doctor.toLowerCase()))throw E(409,'المادة موجودة بالفعل');
      doc={name,code:str(d.code,30),doctor,by:u.id,t};
    }else if(key==='services'){doc=svcData(u,d)}
    else if(key==='tickets'){
      if(u.role!=='student')throw E(403,'للطلاب فقط');
      const sv=getDoc('services',str(d.serviceId,100));if(!sv)throw E(404,'الخدمة غير موجودة');
      const day=str(d.day,10);if(![0,1,2].some(o=>cairoDay(o)===day))throw E(400,'يوم غير صالح');
      const all=listDocs('tickets').map(x=>x.data).filter(x=>x.dept===sv.dept&&x.day===day);
      if(all.filter(x=>x.status!=='cancelled').length>=(DEPTS[sv.dept]||{cap:100}).cap)throw E(409,'اكتملت حجوزات هذا اليوم');
      if(all.some(x=>x.uid===u.id&&['waiting','serving'].includes(x.status)))throw E(409,'لديك دور فعّال لنفس اليوم');
      doc={dept:sv.dept,serviceId:str(d.serviceId,100),serviceName:sv.name,day,uid:u.id,name:u.name,status:'waiting',t};
    }else if(key==='materials'){
      const f=q1('SELECT * FROM files WHERE id=?',str(d.assetId,40));if(!f||f.uid!==u.id)throw E(400,'الملف غير موجود');
      const kind=str(d.kind,5),title=str(d.title,200),subject=str(d.subject,200);
      if(!title||!subject||!['lec','sum','exam','oth'].includes(kind))throw E(400,'بيانات ناقصة');
      doc={title,subject,kind,term:str(d.term,60),desc:str(d.desc,300),assetId:f.id,url:'/_blob/'+f.id,fileName:str(d.fileName,200),size:f.size,ctype:f.ctype,uid:u.id,name:u.name,t};
    }else throw E(403,'غير مسموح');
    putDoc(col,id,doc);emit(col);return{id};
  }
  const{col,key,id}=parse(b.path,false),cur=getDoc(col,id);
  if(op==='set'){
    let doc;
    if(key==='reviews'){
      const cid=str(d.courseId,100);if(u.role!=='student'||id!==cid+'_'+u.id||!getDoc('courses',cid))throw E(403,'غير مسموح');
      const n=(v,lo,hi)=>Math.max(lo,Math.min(hi,Math.round(+v)||lo));
      doc={courseId:cid,uid:u.id,name:d.name==='طالب مجهول'?'طالب مجهول':u.name,stars:n(d.stars,1,5),diff:n(d.diff,1,5),work:n(d.work,1,5),rec:!!d.rec,text:str(d.text,600),t:Date.now()};
    }else if(key==='likes'){
      const mid=str(d.mid,100);if(id!==mid+'_'+u.id||!getDoc('materials',mid))throw E(403,'غير مسموح');doc={mid,uid:u.id};
    }else if(key==='services'){
      if(!cur||cur.dept!==u.dept)throw E(403,'غير مسموح');doc=svcData(u,d);
    }else throw E(403,'غير مسموح');
    putDoc(col,id,doc);emit(col);return{};
  }
  if(!cur)throw E(404,'غير موجود');
  if(op==='update'){
    if(key==='slots'){
      if(d.status==='booked'){
        if(u.role!=='student')throw E(403,'للطلاب فقط');
        if(cur.status!=='open'||endOf(cur)<Date.now())throw E(409,'تم حجز هذا الموعد للتو');
        if(listDocs('slots').some(x=>x.data.studentId===u.id&&x.data.status==='booked'&&endOf(x.data)>Date.now()&&ovl(x.data,cur)))throw E(409,'لديك حجز آخر في نفس الوقت');
        putDoc(col,id,{...cur,status:'booked',studentId:u.id,studentName:u.name,topic:str(d.topic,200)});
      }else if(d.status==='open'){
        if(cur.status!=='booked'||(cur.studentId!==u.id&&cur.advisorId!==u.id))throw E(403,'غير مسموح');
        putDoc(col,id,{...cur,status:'open',studentId:'',studentName:'',topic:''});
      }else throw E(403,'غير مسموح');
    }else if(key==='tickets'){
      const st=d.status;
      if(u.role==='student'){if(cur.uid!==u.id||cur.status!=='waiting'||st!=='cancelled')throw E(403,'غير مسموح')}
      else if(u.role==='staff'){if(cur.dept!==u.dept||!['waiting','serving','done','noshow','cancelled'].includes(st))throw E(403,'غير مسموح')}
      else throw E(403,'غير مسموح');
      putDoc(col,id,{...cur,status:st});
    }else throw E(403,'غير مسموح');
    emit(col);return{};
  }
  if(op==='delete'){
    if(key==='slots'){
      if(cur.advisorId!==u.id)throw E(403,'غير مسموح');
      delDoc(col,id);run('DELETE FROM docs WHERE path=?',`slots/${id}/msgs`);emit('slots');emit(`slots/${id}/msgs`);
    }else if(key==='reviews'||key==='likes'){
      if(!id.endsWith('_'+u.id))throw E(403,'غير مسموح');delDoc(col,id);emit(col);
    }else if(key==='services'){
      if(u.role!=='staff'||cur.dept!==u.dept)throw E(403,'غير مسموح');delDoc(col,id);emit(col);
    }else if(key==='materials'){
      if(cur.uid!==u.id&&u.role!=='advisor')throw E(403,'غير مسموح');
      delDoc(col,id);removeFile(cur.assetId);
      for(const l of listDocs('likes'))if(l.data.mid===id)delDoc('likes',l.id);
      emit('materials');emit('likes');
    }else throw E(403,'غير مسموح');
    return{};
  }
  throw E(400,'عملية غير معروفة');
}

// ---------- الملفات ----------
function removeFile(id){if(!id)return;run('DELETE FROM files WHERE id=?',id);try{fs.unlinkSync(path.join(DATA,'files',String(id).replace(/[^\w-]/g,'')))}catch(e){}}
function readBody(req,limit){return new Promise((ok,no)=>{const ch=[];let n=0,dead=false;req.on('data',c=>{if(dead)return;n+=c.length;if(n>limit){dead=true;no(E(413,'الملف كبير جداً'));return}ch.push(c)});req.on('end',()=>!dead&&ok(Buffer.concat(ch)));req.on('error',no)})}
const readJson=async req=>{const b=await readBody(req,1<<20);try{return b.length?JSON.parse(b.toString('utf8')):{}}catch(e){throw E(400,'طلب غير صالح')}};
async function upload(req,u){
  const ct=String(req.headers['content-type']||'').split(';')[0].trim().toLowerCase();
  if(!FILE_TYPES.has(ct))throw E(415,'صيغة غير مدعومة');
  const k='up:'+u.id,w=limited(k,40,3600e3);if(w)throw E(429,'محاولات كثيرة');bump(k);
  const buf=await readBody(req,MAX_UPLOAD),id=rid();
  fs.writeFileSync(path.join(DATA,'files',id),buf);run('INSERT INTO files VALUES(?,?,?,?,?)',id,u.id,ct,buf.length,Date.now());
  return{id,url:'/_blob/'+id,sizeBytes:buf.length,contentType:ct};
}
function serveFile(req,res,id){
  const f=q1('SELECT * FROM files WHERE id=?',id),fp=path.join(DATA,'files',String(id).replace(/[^\w-]/g,''));let st;
  try{st=fs.statSync(fp)}catch(e){}
  if(!f||!st)throw E(404,'غير موجود');
  const h={'Content-Type':f.ctype+(f.ctype.startsWith('text/')?'; charset=utf-8':''),'Accept-Ranges':'bytes','Cache-Control':'private, max-age=3600','Content-Disposition':'inline'};
  const r=/^bytes=(\d*)-(\d*)$/.exec(req.headers.range||'');
  if(r&&(r[1]||r[2])){
    const s=r[1]?+r[1]:st.size-(+r[2]);let e=r[1]&&r[2]?+r[2]:st.size-1;e=Math.min(e,st.size-1);
    if(s>e||s<0){res.writeHead(416,{'Content-Range':`bytes */${st.size}`});return res.end()}
    res.writeHead(206,{...h,'Content-Range':`bytes ${s}-${e}/${st.size}`,'Content-Length':e-s+1});fs.createReadStream(fp,{start:s,end:e}).pipe(res);
  }else{res.writeHead(200,{...h,'Content-Length':st.size});fs.createReadStream(fp).pipe(res)}
}

// ---------- الحسابات ----------
function createAccount(id,name,role,dept,pw){
  const salt=crypto.randomBytes(16).toString('hex');
  run('INSERT INTO accounts(id,name,role,dept,salt,hash,t) VALUES(?,?,?,?,?,?,?)',id,name,role,dept||'',salt,hashPw(pw,salt),Date.now());
}
function login(req,res,b,admin){
  const ip=ipOf(req),id=admin?OWNER_ID:norm(b.id),k='login:'+ip+':'+id;
  const w=limited(k,5,60000)||limited('ip:'+ip,40,60000);if(w)throw E(429,`محاولات كثيرة، انتظر ${w} ثانية`);
  bump('ip:'+ip);
  const a=q1('SELECT * FROM accounts WHERE id=?',id);
  if(!a||(admin?a.role!=='owner':a.role==='owner')||!verify(String(b.password||''),a)){bump(k);throw E(401,admin?'كلمة المرور غير صحيحة':'الرقم أو كلمة المرور غير صحيحة')}
  hits.delete(k);startSession(req,res,a.id,admin?12*3600e3:30*864e5);
  return admin?{}:{user:pub(a)};
}

// ---------- الراوتر ----------
const send=(res,code,obj)=>{const b=JSON.stringify(obj);res.writeHead(code,{'Content-Type':'application/json; charset=utf-8','Cache-Control':'no-store'});res.end(b)};
async function handle(req,res){
  const p=new URL(req.url,'http://x').pathname,m=req.method;
  res.setHeader('X-Content-Type-Options','nosniff');res.setHeader('Referrer-Policy','same-origin');res.setHeader('X-Frame-Options','DENY');
  if(m==='GET'&&(p==='/'||p==='/index.html')){res.writeHead(200,{'Content-Type':'text/html; charset=utf-8','Cache-Control':'no-cache'});return res.end(fs.readFileSync(path.join(__dirname,'index.html')))}
  if(p==='/healthz'){q1('SELECT 1');return send(res,200,{ok:true})}
  if(m!=='GET'&&m!=='HEAD'){const o=req.headers.origin;if(o){let h;try{h=new URL(o).host}catch(e){}if(h!==req.headers.host)throw E(403,'مرفوض')}}
  if(m==='GET'&&p.startsWith('/_blob/')){need(req);return serveFile(req,res,decodeURIComponent(p.slice(7)))}
  if(m==='GET'&&p==='/api/me'){const a=authOf(req);return send(res,200,a?(a.role==='owner'?{user:null,isOwner:true}:{user:pub(a),isOwner:false}):{user:null,isOwner:false})}
  if(m==='GET'&&p==='/api/stream'){need(req);res.writeHead(200,{'Content-Type':'text/event-stream','Cache-Control':'no-cache, no-transform','Connection':'keep-alive','X-Accel-Buffering':'no'});res.write('retry: 3000\n\n');clients.add(res);req.on('close',()=>clients.delete(res));return}
  if(m==='POST'&&p==='/api/login')return send(res,200,{ok:true,...login(req,res,await readJson(req),false)});
  if(m==='POST'&&p==='/api/admin/login')return send(res,200,{ok:true,...login(req,res,await readJson(req),true)});
  if(m==='POST'&&p==='/api/logout'){const tk=cookies(req).sid;if(tk)run('DELETE FROM sessions WHERE token=?',sha(tk));res.setHeader('Set-Cookie','sid=; HttpOnly; SameSite=Lax; Path=/; Max-Age=0');return send(res,200,{ok:true})}
  if(m==='POST'&&p==='/api/register'){
    const b=await readJson(req),id=norm(b.id),name=str(b.name,80),pw=String(b.password||''),ip=ipOf(req);
    if(limited('reg:'+ip,10,3600e3))throw E(429,'محاولات كثيرة، حاول لاحقاً');bump('reg:'+ip);
    if(id.length<3||name.length<2)throw E(400,'اكتب رقم الهوية (3 أحرف على الأقل) والاسم');
    if(pw.length<6||pw.length>100)throw E(400,'كلمة المرور 6 أحرف على الأقل');
    if(q1('SELECT 1 x FROM accounts WHERE id=?',id))throw E(409,'هذا الرقم مسجّل بالفعل، سجّل الدخول');
    const cl=getCfg().colleges.find(c=>c.id===str(b.college,40)),yr=Math.round(+b.year);
    if(!cl||!(yr>=1&&yr<=cl.years))throw E(400,'اختر الكلية والفرقة الدراسية');
    createAccount(id,name,'student','',pw);run('UPDATE accounts SET college=?,year=? WHERE id=?',cl.id,yr,id);startSession(req,res,id,30*864e5);
    return send(res,200,{ok:true,user:pub(q1('SELECT * FROM accounts WHERE id=?',id))});
  }
  if(m==='GET'&&p==='/api/config')return send(res,200,{ok:true,config:getCfg()});
  if(m==='POST'&&p==='/api/admin/config'){need(req,'owner');const c=cleanCfg((await readJson(req)).config);run("INSERT INTO meta VALUES('config',?) ON CONFLICT(k) DO UPDATE SET v=excluded.v",JSON.stringify(c));return send(res,200,{ok:true,config:c})}
  if(m==='POST'&&p==='/api/profile'){
    const u=need(req);if(u.role!=='student')throw E(403,'للطلاب فقط');const b=await readJson(req);
    const cl=getCfg().colleges.find(c=>c.id===str(b.college,40)),yr=Math.round(+b.year);
    if(!cl||!(yr>=1&&yr<=cl.years))throw E(400,'اختر الكلية والفرقة الدراسية');
    run('UPDATE accounts SET college=?,year=? WHERE id=?',cl.id,yr,u.id);return send(res,200,{ok:true,user:pub(q1('SELECT * FROM accounts WHERE id=?',u.id))});
  }
  if(p==='/api/gpa'){
    const u=need(req);if(u.role!=='student')throw E(403,'للطلاب فقط');
    if(m==='GET')return send(res,200,{ok:true,data:getDoc('gpa',u.id)});
    if(m==='PUT'){putDoc('gpa',u.id,cleanGpa(await readJson(req)));return send(res,200,{ok:true})}
  }
  if(m==='POST'&&p==='/api/db'){const u=need(req);return send(res,200,{ok:true,...dbOp(pub(u),await readJson(req))})}
  if(m==='POST'&&p==='/api/upload'){const u=need(req);return send(res,200,{ok:true,...await upload(req,u)})}
  if(m==='DELETE'&&p.startsWith('/api/upload/')){const u=need(req),id=p.slice(12),f=q1('SELECT * FROM files WHERE id=?',id);if(f&&(f.uid===u.id||u.role==='advisor'))removeFile(id);return send(res,200,{ok:true})}
  if(p==='/api/admin/accounts'){
    need(req,'owner');
    if(m==='GET')return send(res,200,{ok:true,accounts:q("SELECT id,name,role,dept FROM accounts WHERE role IN ('advisor','staff') ORDER BY role,name")});
    if(m==='POST'){
      const b=await readJson(req),id=norm(b.id),name=str(b.name,80),pw=String(b.password||''),role=b.role,dept=role==='staff'?str(b.dept,20):'';
      if(!id||!name||pw.length<6||!['advisor','staff'].includes(role)||(role==='staff'&&!DEPTS[dept]))throw E(400,'أكمل البيانات (كلمة المرور 6 أحرف على الأقل)');
      const ex=q1('SELECT role FROM accounts WHERE id=?',id);
      if(ex&&!['advisor','staff'].includes(ex.role))throw E(409,'هذا الرقم مستخدم لحساب آخر');
      if(ex){run('UPDATE accounts SET name=?,role=?,dept=? WHERE id=?',name,role,dept,id);setPw(id,pw)}else createAccount(id,name,role,dept,pw);
      return send(res,200,{ok:true});
    }
  }
  if(m==='DELETE'&&p.startsWith('/api/admin/accounts/')){
    need(req,'owner');const id=norm(decodeURIComponent(p.slice(20)));
    run("DELETE FROM accounts WHERE id=? AND role IN ('advisor','staff')",id);run('DELETE FROM sessions WHERE uid=?',id);return send(res,200,{ok:true});
  }
  throw E(404,'غير موجود');
}
const server=http.createServer(async(req,res)=>{
  try{await handle(req,res)}
  catch(e){
    const known=typeof e.code==='number';if(!known)console.error(e);
    if(!res.headersSent)send(res,known?e.code:500,{ok:false,error:known?e.message:'خطأ في الخادم'});
    if(e.code===413)res.on('finish',()=>req.destroy());
  }
});

// ---------- التشغيل الأول: حساب المسؤول + بيانات تجريبية ----------
const rnd=()=>crypto.randomBytes(7).toString('base64url');
function bootstrap(){
  const lines=[];
  let owner=q1("SELECT * FROM accounts WHERE role='owner'");
  const envPw=process.env.ADMIN_PASSWORD;
  if(!owner){const pw=envPw||rnd();createAccount(OWNER_ID,'مسؤول النظام','owner','',pw);if(!envPw)lines.push(`المسؤول (👑 لوحة الإدارة): ${pw}`)}
  else if(envPw&&!verify(envPw,owner))setPw(owner.id,envPw);
  if(process.env.SEED==='0'||q1("SELECT v FROM meta WHERE k='seeded'"))return lines;
  db.exec('BEGIN');
  try{
    const accts=[['advisor1','مرشد أكاديمي 1 (تجريبي)','advisor',''],['advisor2','مرشد أكاديمي 2 (تجريبي)','advisor',''],['affairs1','موظف شؤون الطلاب (تجريبي)','staff','affairs'],['clinic1','موظف العيادة الطبية (تجريبي)','staff','clinic']];
    for(const[id,name,role,dept]of accts){if(q1('SELECT 1 x FROM accounts WHERE id=?',id))continue;const pw=rnd();createAccount(id,name,role,dept,pw);lines.push(`${name}: رقم الهوية ${id} · كلمة المرور ${pw}`)}
    for(const adv of ['advisor1','advisor2'])for(let o=1;o<=3;o++){
      const a=q1('SELECT * FROM accounts WHERE id=?',adv);
      for(let i=0;i<3;i++)putDoc('slots',rid(),{advisorId:adv,advisorName:a.name,startMs:cairoMs(cairoDay(o),adv==='advisor1'?10:13,i*20),dur:20,status:'open',studentId:'',studentName:'',topic:''});
    }
    const note='بيانات استرشادية مؤقتة، تأكد من الإدارة قبل الاعتماد عليها.';
    const S=[
      ['affairs','استخراج بطاقة جامعية',['صورة شخصية حديثة','صورة البطاقة الشخصية','إيصال سداد المصروفات'],10],
      ['affairs','إثبات قيد (شهادة قيد)',['البطاقة الجامعية','إيصال سداد المصروفات'],5],
      ['affairs','بيان درجات',['البطاقة الجامعية','طلب مكتوب'],7],
      ['affairs','طلب إجازة أو وقف قيد',['طلب مكتوب','البطاقة الجامعية','موافقة ولي الأمر'],10],
      ['clinic','كشف طبي',['البطاقة الجامعية'],10],
      ['clinic','تقرير طبي لتبرير الغياب',['البطاقة الجامعية','التقرير الطبي الخارجي إن وُجد'],8],
      ['clinic','كشف طبي للقبول أو التسجيل',['صورة شخصية','البطاقة الشخصية','تحاليل مطلوبة'],12]];
    for(const[dept,name,docs,mins]of S)putDoc('services',rid(),{dept,name,docs,mins,notes:note,sample:true,by:'seed',t:Date.now()});
    for(const[name,code]of [['Circuit Analysis','ECE201'],['Electronic Circuits','ECE202'],['Digital Logic Design','ECE203'],['Power Systems','ECE301'],['EV Powertrains','ECE402'],['Embedded AI','ECE405']])putDoc('courses',rid(),{name,code,doctor:'(يُحدَّث)',by:'seed',t:Date.now()});
    run("INSERT INTO meta VALUES('seeded','1')");db.exec('COMMIT');
  }catch(e){db.exec('ROLLBACK');throw e}
  return lines;
}
const creds=bootstrap();
if(creds.length){
  const out='بيانات الدخول الأولية (غيّرها من لوحة الإدارة):\n'+creds.join('\n');
  console.log('\n'+out+'\n');try{fs.writeFileSync(path.join(DATA,'initial-credentials.txt'),out+'\n',{mode:0o600})}catch(e){}
}
server.listen(PORT,()=>console.log('الخادم يعمل على المنفذ '+PORT));
process.on('SIGTERM',()=>{server.close();db.close();process.exit(0)});
