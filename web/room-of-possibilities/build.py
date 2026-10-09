"""Build a self-contained offline HTML artifact from local source and renderer."""
from pathlib import Path
import subprocess

root=Path(__file__).resolve().parent
subprocess.run([str(root/'node_modules/.bin/esbuild'),str(root/'app.js'),
    '--bundle','--format=iife','--minify','--outfile='+str(root/'app.bundle.js')],check=True)
bundle=(root/'app.bundle.js').read_text().replace('</script','<\\/script')
html=(root/'shell.html').read_text().replace('/* APP_BUNDLE */',bundle)
(root/'PerfectPower-Room-of-Possibilities.html').write_text(html)
print('Built PerfectPower-Room-of-Possibilities.html')
