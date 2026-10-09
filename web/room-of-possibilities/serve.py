"""Optional local preview: py serve.py (Windows) or python3 serve.py."""
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler
from pathlib import Path
import os
import webbrowser
os.chdir(Path(__file__).resolve().parent)
url='http://127.0.0.1:8765/PerfectPower-Room-of-Possibilities.html'
print('Open '+url+'; press Ctrl+C to stop.')
webbrowser.open(url)
try:
    ThreadingHTTPServer(('127.0.0.1',8765), SimpleHTTPRequestHandler).serve_forever()
except KeyboardInterrupt:
    pass
