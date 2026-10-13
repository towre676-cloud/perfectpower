"""Build the explorer catalogue from the actual checkout and argparse definitions."""
import argparse, hashlib, json, re, sys, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))
class Captured(BaseException):
    def __init__(self,parser): self.parser=parser

def parser_schema(module="perfectpower.__main__"):
    original=argparse.ArgumentParser.parse_args
    def capture(self,*a,**kw): raise Captured(self)
    argparse.ArgumentParser.parse_args=capture
    try:
        import importlib
        importlib.import_module(module).main()
    except Captured as got: parser=got.parser
    finally: argparse.ArgumentParser.parse_args=original
    def export(p):
        fields=[];children={}
        for a in p._actions:
            if isinstance(a,argparse._SubParsersAction):
                children={k:export(v) for k,v in a.choices.items()};continue
            if a.dest=='help':continue
            default=a.default
            if default is argparse.SUPPRESS:default=None
            try:json.dumps(default)
            except TypeError:default=str(default)
            fields.append({'name':a.dest,'flags':a.option_strings,'required':a.required or not a.option_strings and a.nargs not in ('?','*'),'default':default,'choices':list(a.choices) if a.choices is not None else None,'help':str(a.help or ''),'boolean':isinstance(a,(argparse._StoreTrueAction,argparse._StoreFalseAction)),'true':isinstance(a,argparse._StoreTrueAction),'append':isinstance(a,argparse._AppendAction),'nargs':a.nargs,'type':getattr(a.type,'__name__','str')})
        return {'description':p.description or '', 'fields':fields,'children':children}
    result=export(parser)
    # Parent help strings are stored on the subparser action.
    for a in parser._actions:
        if isinstance(a,argparse._SubParsersAction):
            for item in a._choices_actions:
                if item.dest in result['children']:result['children'][item.dest]['description']=item.help or ''
    return result

def build():
    skip={'.git','node_modules','__pycache__','.pytest_cache','.lake','test-state'}
    files=[]
    tracked=subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode().split('\0')
    for p in (ROOT/name for name in sorted(tracked) if name):
        rel=p.relative_to(ROOT)
        if not p.is_file() or skip.intersection(rel.parts) or str(rel).startswith('desktop/explorer/dist/') or p.suffix in ('.pyc','.so','.dll'):continue
        raw=p.read_bytes();suffix=p.suffix.lower();text=''
        if suffix in ('.md','.lean','.py','.json','.txt','.toml','.c','.cpp','.html','.csv','.ts','.tsx','.js'):text=raw[:12000].decode('utf8','replace')
        title=next((s.strip('# ').strip() for s in text.splitlines() if s.startswith('# ')),p.stem.replace('_',' ').replace('-',' '))
        kind='document' if suffix=='.md' else 'proof' if suffix=='.lean' else 'data' if suffix in ('.json','.csv','.seq','.cnf','.pb') else 'visual' if suffix in ('.html','.png','.jpg','.webp','.svg') else 'code'
        files.append({'path':rel.as_posix(),'title':title[:160],'bytes':len(raw),'kind':kind,'folder':rel.parts[0],'sha256':hashlib.sha256(raw).hexdigest(),'summary':re.sub(r'\s+',' ',text[:1200])[:500] if kind=='document' else ''})
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    commands=parser_schema()['children']
    commands['blast-explorer']={'description':'Exact BLAST alignment, mining, annotation and source-adapter operations','fields':[],'children':parser_schema('perfectpower.blast_cli')['children'],'module':'perfectpower.blast_cli'}
    commands['arithmetic-transport']=dict(parser_schema('perfectpower.arithmetic_transport'),module='perfectpower.arithmetic_transport')
    result={'commit':commit,'files':files,'commands':commands,'total_bytes':sum(f['bytes'] for f in files)}
    target=ROOT/'desktop/explorer/dist/catalog.json';target.parent.mkdir(exist_ok=True);target.write_text(json.dumps(result,ensure_ascii=False))
    print(json.dumps({'files':len(files),'commands':len(result['commands']),'commit':commit,'bytes':result['total_bytes']}))
    return result
if __name__=='__main__':build()
