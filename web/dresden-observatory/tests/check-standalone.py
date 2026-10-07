from pathlib import Path
from html.parser import HTMLParser
import subprocess,tempfile
class Audit(HTMLParser):
 def __init__(self):super().__init__();self.external=[];self.modules=0;self.script=False;self.inline=[]
 def handle_starttag(self,tag,attrs):
  a=dict(attrs)
  if tag=='script':
   self.script=True
   if 'src' in a:self.external.append(a['src'])
   if a.get('type')=='module':self.modules+=1
  if tag=='link' and a.get('rel') in ('stylesheet','modulepreload'):self.external.append(a.get('href'))
 def handle_data(self,data):
  if self.script:self.inline.append(data)
 def handle_endtag(self,tag):
  if tag=='script':self.script=False
p=Path('outputs/Dresden_Codex_Observatory.html');a=Audit();a.feed(p.read_text());assert not a.external,a.external;assert a.modules==1
for s in ('/sources/page46.webp','/sources/page24.webp','/sources/Dresden_Numerical_Monograph.pdf','/sources/DresdenCalendar.lean','/sources/dresden-lean-axioms.log','/sources/dresden-lean-proof-status.json'):assert s not in p.read_text()
with tempfile.NamedTemporaryFile(suffix='.mjs') as f:
 f.write(''.join(a.inline).encode());f.flush();subprocess.run(['node','--check',f.name],check=True)
print('PASS: one valid embedded JavaScript module, embedded source assets, no external script, stylesheet or module preload.')
