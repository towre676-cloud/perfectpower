const {app,BrowserWindow,dialog,shell}=require('electron');
const {spawn}=require('node:child_process');
const path=require('node:path');
let worker,window,ready=false,closing=false;
app.setName('PerfectPower Explorer');
if(!app.requestSingleInstanceLock())app.quit();
else {
 app.on('second-instance',()=>{if(window){if(window.isMinimized())window.restore();window.focus();}});
 app.whenReady().then(()=>{
  const packaged=process.platform==='win32';
  const root=process.env.PP_EXPLORER_ROOT || path.join(__dirname,'repository');
  const python=process.env.PP_EXPLORER_PYTHON || (packaged?path.join(__dirname,'runtime','python','python.exe'):'python3');
  window=new BrowserWindow({width:1500,height:980,minWidth:1000,minHeight:700,show:false,title:'PerfectPower Explorer',backgroundColor:'#101a2a',icon:path.join(root,'desktop','explorer','dist','icon.png'),webPreferences:{contextIsolation:true,nodeIntegration:false,sandbox:true}});
  window.setMenuBarVisibility(false);
  const splash=`<!doctype html><html><body style="margin:0;height:100vh;display:grid;place-items:center;background:#101a2a;color:#ecede7;font-family:Segoe UI,sans-serif"><div style="text-align:center"><div style="font-size:64px;color:#b5d3ca">∑</div><h1 style="font-weight:400;letter-spacing:-1px">PerfectPower Explorer</h1><p style="color:#9baab9">Opening your mathematical observatory…</p></div></body></html>`;
  window.loadURL('data:text/html;charset=utf-8,'+encodeURIComponent(splash));window.show();
  worker=spawn(python,['-u',path.join(root,'desktop','explorer','server.py'),'--no-browser','--state',app.getPath('userData')],{cwd:root,windowsHide:true,env:{...process.env,PYTHONUTF8:'1',PYTHONPATH:path.join(root,'python')}});
  let output='',errors='';
  worker.stdout.on('data',data=>{
   output+=data.toString();if(ready)return;
   const line=output.split('\n').find(s=>s.startsWith('{'));
   if(!line)return;
   try{const receipt=JSON.parse(line);const origin=new URL(receipt.url).origin;ready=true;
    window.webContents.setWindowOpenHandler(({url})=>{if(url.startsWith('https://'))shell.openExternal(url);return {action:'deny'};});
    window.webContents.on('will-navigate',(event,url)=>{if(new URL(url).origin!==origin)event.preventDefault();});
    window.loadURL(receipt.url);
   }catch(e){/* wait for a full JSON line */}
  });
  worker.stderr.on('data',d=>{errors=(errors+d.toString()).slice(-8000);});
  worker.on('error',e=>{dialog.showErrorBox('Unable to open PerfectPower',e.message);app.quit();});
  worker.on('exit',code=>{if(!closing){dialog.showErrorBox('PerfectPower engine stopped',errors || `Engine exit ${code}. Reopen the application.`);app.quit();}});
  setTimeout(()=>{if(!ready&&!closing){dialog.showErrorBox('PerfectPower could not start',errors||'The bundled computation engine did not become ready within 30 seconds.');app.quit();}},30000);
 });
 app.on('window-all-closed',()=>app.quit());
 app.on('before-quit',()=>{closing=true;if(worker){worker.stdin.end();setTimeout(()=>worker.kill(),1500).unref();}});
}
