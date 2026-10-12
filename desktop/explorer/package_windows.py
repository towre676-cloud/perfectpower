"""Assemble the complete offline Windows application and self-extracting setup."""
import argparse,base64,hashlib,json,os,shutil,struct,subprocess,zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def package(args):
    stage=Path(args.output)/'PerfectPower-Explorer';stage.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(args.electron) as z:z.extractall(stage)
    (stage/'electron.exe').rename(stage/'PerfectPower-Runtime.exe')
    app=stage/'resources/app';app.mkdir(parents=True,exist_ok=True)
    (app/'package.json').write_text(json.dumps({'name':'perfectpower-explorer','version':'1.0.0','main':'main.cjs'}))
    shutil.copy2(ROOT/'desktop/explorer/main.cjs',app/'main.cjs')
    repo=app/'repository'
    # Include every tracked source file plus this desktop implementation; omit build caches only.
    tracked=subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode().split('\0')
    files={f for f in tracked if f}
    for p in (ROOT/'desktop/explorer').rglob('*'):
        if p.is_file() and not {'node_modules','__pycache__','test-state'}.intersection(p.relative_to(ROOT).parts):files.add(p.relative_to(ROOT).as_posix())
    files.update(['python/perfectpower/shipped_native.py'])
    for name in sorted(files):
        src=ROOT/name
        if not src.is_file():continue
        target=repo/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,target)
    runtime=app/'runtime/python';runtime.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(args.python) as z:z.extractall(runtime)
    (runtime/'python312._pth').write_text('python312.zip\n.\nLib/site-packages\n../../repository/python\nimport site\n')
    packages=runtime/'Lib/site-packages';packages.mkdir(parents=True,exist_ok=True)
    deps=[]
    for wheel in sorted(Path(args.wheels).glob('*.whl')):
        with zipfile.ZipFile(wheel) as z:
            for entry in z.infolist():
                name=entry.filename
                if '.data/purelib/' in name:name=name.split('.data/purelib/',1)[1]
                elif '.data/platlib/' in name:name=name.split('.data/platlib/',1)[1]
                elif '.data/' in name:continue
                if entry.is_dir():continue
                dest=packages/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(z.read(entry))
        deps.append({'file':wheel.name,'sha256':sha(wheel)})
    runtime_record={'python':{'file':Path(args.python).name,'sha256':sha(args.python)},'electron':{'file':Path(args.electron).name,'sha256':sha(args.electron)},'wheels':deps}
    (stage/'RUNTIME_SOURCES.json').write_text(json.dumps(runtime_record,indent=2))
    (stage/'READ-ME.txt').write_text('PerfectPower Explorer 1.0\n\nDouble-click PerfectPower-Explorer.exe.\nThe complete repository, computation engines and numerical dependencies are included.\nNo Python installation or terminal is needed. Keep this folder together.\nWindows 10/11 x64.\n\nThe program is unsigned. Native Windows GPU launch has not been exercised in this Linux build environment.\nLean, PARI, Sage and external research tools are not bundled. Their sources and documented requirements are included.\n\nRead resources/app/repository/docs/PERFECTPOWER_EXPLORER_MONOGRAPH.md for features, checks and remaining limits.\n',encoding='utf8')
    compiler=Path(args.compiler);offset=0
    c_template=r'''#define UNICODE
#define _UNICODE
#include <windows.h>
#include <commctrl.h>
#include <wchar.h>
static HWND window,progress,label;static const wchar_t *encoded=L"ENCODED";
static DWORD WINAPI install(LPVOID unused){
 wchar_t self[32768];GetModuleFileNameW(NULL,self,32768);SetEnvironmentVariableW(L"PP_EXPLORER_SETUP",self);
 wchar_t powershell[32768];GetSystemDirectoryW(powershell,32768);wcscat(powershell,L"\\WindowsPowerShell\\v1.0\\powershell.exe");
 size_t count=wcslen(encoded)+wcslen(powershell)+128;wchar_t *cmd=HeapAlloc(GetProcessHeap(),HEAP_ZERO_MEMORY,count*sizeof(wchar_t));
 swprintf(cmd,count,L"\"%ls\" -NoLogo -NoProfile -NonInteractive -EncodedCommand %ls",powershell,encoded);
 STARTUPINFOW si={0};si.cb=sizeof(si);PROCESS_INFORMATION pi={0};DWORD code=1;
 if(CreateProcessW(powershell,cmd,NULL,NULL,FALSE,CREATE_NO_WINDOW,NULL,NULL,&si,&pi)){WaitForSingleObject(pi.hProcess,INFINITE);GetExitCodeProcess(pi.hProcess,&code);CloseHandle(pi.hThread);CloseHandle(pi.hProcess);}
 HeapFree(GetProcessHeap(),0,cmd);PostMessageW(window,WM_APP,code,0);return 0;
}
static LRESULT CALLBACK proc(HWND h,UINT msg,WPARAM w,LPARAM l){
 if(msg==WM_APP){if(w==0){DestroyWindow(h);}else{SendMessageW(progress,PBM_SETMARQUEE,FALSE,0);SetWindowTextW(label,L"Installation could not finish. Your error record is in Local AppData.");MessageBoxW(h,L"Please read %LOCALAPPDATA%\\PerfectPower-Explorer-Setup-error.txt for the installation error.",L"PerfectPower Explorer",MB_OK|MB_ICONERROR);DestroyWindow(h);}return 0;}
 if(msg==WM_CLOSE){MessageBoxW(h,L"Installation is in progress. This window will close when the explorer opens.",L"PerfectPower Explorer",MB_OK);return 0;}
 if(msg==WM_DESTROY){PostQuitMessage(0);return 0;}return DefWindowProcW(h,msg,w,l);
}
int WINAPI wWinMain(HINSTANCE instance,HINSTANCE old,PWSTR command,int show){
 INITCOMMONCONTROLSEX common={sizeof(common),ICC_PROGRESS_CLASS};InitCommonControlsEx(&common);
 WNDCLASSW cls={0};cls.lpfnWndProc=proc;cls.hInstance=instance;cls.lpszClassName=L"PerfectPowerSetup";cls.hbrBackground=(HBRUSH)(COLOR_WINDOW+1);cls.hCursor=LoadCursor(NULL,IDC_ARROW);cls.hIcon=LoadIcon(instance,MAKEINTRESOURCE(1));RegisterClassW(&cls);
 window=CreateWindowW(cls.lpszClassName,L"PerfectPower Explorer",WS_OVERLAPPED|WS_CAPTION|WS_SYSMENU,(GetSystemMetrics(SM_CXSCREEN)-560)/2,(GetSystemMetrics(SM_CYSCREEN)-230)/2,560,230,NULL,NULL,instance,NULL);
 HWND title=CreateWindowW(L"STATIC",L"Opening your mathematical observatory.",WS_CHILD|WS_VISIBLE,30,27,490,32,window,NULL,instance,NULL);
 label=CreateWindowW(L"STATIC",L"Installing the complete application to your Desktop…",WS_CHILD|WS_VISIBLE,30,73,490,30,window,NULL,instance,NULL);
 HFONT font=CreateFontW(-18,0,0,0,FW_NORMAL,FALSE,FALSE,FALSE,DEFAULT_CHARSET,0,0,CLEARTYPE_QUALITY,0,L"Segoe UI");SendMessage(title,WM_SETFONT,(WPARAM)font,TRUE);SendMessage(label,WM_SETFONT,(WPARAM)font,TRUE);
 progress=CreateWindowW(PROGRESS_CLASSW,NULL,WS_CHILD|WS_VISIBLE|PBS_MARQUEE,30,126,490,15,window,NULL,instance,NULL);SendMessageW(progress,PBM_SETMARQUEE,TRUE,25);
 ShowWindow(window,SW_SHOW);UpdateWindow(window);HANDLE thread=CreateThread(NULL,0,install,NULL,0,NULL);if(thread)CloseHandle(thread);
 MSG message;while(GetMessageW(&message,NULL,0,0)>0){TranslateMessage(&message);DispatchMessageW(&message);}DeleteObject(font);return 0;
}
'''
    src=Path(args.output)/'setup.c';stub=Path(args.output)/'setup-stub.exe'
    rc=Path(args.output)/'setup.rc';ico=ROOT/'desktop/explorer/dist/icon.ico';rc.write_text('1 ICON "'+str(ico).replace('\\','/')+'"\n')
    windres=compiler.parent/'x86_64-w64-mingw32-windres';resource=Path(args.output)/'setup-resource.o'
    subprocess.run([str(windres),str(rc),'-o',str(resource)],check=True)
    launch_source=Path(args.output)/'launch.c'
    launch_source.write_text(r'''#define UNICODE
#define _UNICODE
#include <windows.h>
#include <wchar.h>
int WINAPI wWinMain(HINSTANCE instance,HINSTANCE old,PWSTR unused,int show){
 wchar_t base[32768],runtime[32768],command[32768];GetModuleFileNameW(NULL,base,32768);wchar_t *cut=wcsrchr(base,L'\\');if(!cut)return 1;*cut=0;
 swprintf(runtime,32768,L"%ls\\PerfectPower-Runtime.exe",base);swprintf(command,32768,L"\"%ls\"",runtime);
 STARTUPINFOW si={0};si.cb=sizeof(si);PROCESS_INFORMATION pi={0};
 if(!CreateProcessW(runtime,command,NULL,NULL,FALSE,0,NULL,base,&si,&pi)){MessageBoxW(NULL,L"The application runtime could not open. Keep the entire installed folder together.",L"PerfectPower Explorer",MB_OK|MB_ICONERROR);return 1;}
 CloseHandle(pi.hThread);CloseHandle(pi.hProcess);return 0;
}
''',encoding='utf8')
    subprocess.run([str(compiler),'-municode','-mwindows','-O2',str(launch_source),str(resource),'-o',str(stage/'PerfectPower-Explorer.exe'),'-static-libgcc'],check=True)
    manifest={p.relative_to(stage).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)} for p in stage.rglob('*') if p.is_file() and p!=stage/'PACKAGE_MANIFEST.json'}
    (stage/'PACKAGE_MANIFEST.json').write_text(json.dumps(manifest,indent=2))
    archive=Path(args.output)/'PerfectPower-Explorer-Complete.zip'
    with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for p in sorted(stage.rglob('*')):
            if p.is_file():z.write(p,p.relative_to(stage))
    print(json.dumps({'directory':str(stage),'archive':str(archive),'files':len(manifest),'archive_bytes':archive.stat().st_size,'archive_sha256':sha(archive)}),flush=True)
    # The setup executable carries this same ZIP. A small native GUI runs ordinary
    # built-in PowerShell archive extraction, creates a Desktop shortcut, and opens the app.
    script=r'''$ErrorActionPreference='Stop';
try {
$self=$env:PP_EXPLORER_SETUP;
$desktop=[Environment]::GetFolderPath('Desktop');
$target=Join-Path $desktop 'PerfectPower Explorer 1.0';
if(Test-Path -LiteralPath $target){$target=$target+' '+[DateTime]::Now.ToString('yyyyMMdd-HHmmss')};
$zip=Join-Path ([IO.Path]::GetTempPath()) ('PerfectPower-'+[Guid]::NewGuid().ToString('N')+'.zip');
$stream=[IO.File]::OpenRead($self);
try {$stream.Seek(OFFSET,[IO.SeekOrigin]::Begin)|Out-Null;$output=[IO.File]::Create($zip);try{$stream.CopyTo($output)}finally{$output.Dispose()}}finally{$stream.Dispose()};
if((Get-FileHash -LiteralPath $zip -Algorithm SHA256).Hash -ne 'DIGEST'){throw 'Installer archive checksum mismatch.'};
Expand-Archive -LiteralPath $zip -DestinationPath $target;
Remove-Item -LiteralPath $zip;
$exe=Join-Path $target 'PerfectPower-Explorer.exe';
$shell=New-Object -ComObject WScript.Shell;
$link=$shell.CreateShortcut((Join-Path $desktop 'PerfectPower Explorer.lnk'));
$link.TargetPath=$exe;$link.WorkingDirectory=$target;$link.Description='PerfectPower Explorer - the complete mathematical observatory';$link.Save();
Start-Process -FilePath $exe -WorkingDirectory $target;
exit 0;
} catch {
$log=Join-Path ([Environment]::GetFolderPath('LocalApplicationData')) 'PerfectPower-Explorer-Setup-error.txt';
[IO.File]::WriteAllText($log,($_|Out-String));exit 1;
}
'''
    offset=0
    for _ in range(8):
        text=script.replace('OFFSET',str(offset)).replace('DIGEST',sha(archive))
        encoded=base64.b64encode(text.encode('utf-16le')).decode()
        src.write_text(c_template.replace('ENCODED',encoded),encoding='utf8')
        subprocess.run([str(compiler),'-municode','-mwindows','-O2',str(src),str(resource),'-o',str(stub),'-lcomctl32','-static-libgcc'],check=True)
        length=stub.stat().st_size
        if length==offset:break
        offset=length
    else:raise ValueError('Installer offset did not stabilize')
    setup=Path(args.output)/'PerfectPower-Explorer-Setup.exe'
    with setup.open('wb') as out:
        out.write(stub.read_bytes())
        with archive.open('rb') as f:shutil.copyfileobj(f,out)
    assert setup.read_bytes()[offset:]==archive.read_bytes()
    (Path(args.output)/'BUILD_RECEIPT.json').write_text(json.dumps({'archive_sha256':sha(archive),'setup_sha256':sha(setup),'setup_archive_offset':offset,'repository_base':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'all_tracked_files':len(tracked)-1,'runtime_sources':runtime_record,'native_windows_execution':'not exercised in this Linux environment'},indent=2))
    print(json.dumps({'setup':str(setup),'bytes':setup.stat().st_size,'sha256':sha(setup)}),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--electron',required=True);p.add_argument('--python',required=True);p.add_argument('--wheels',required=True);p.add_argument('--output',required=True);p.add_argument('--compiler',required=True);package(p.parse_args())
