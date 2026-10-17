"""Assemble the tested local React/Three runtime into offline and chat copies."""
import argparse
import hashlib
import json
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WEB = ROOT / 'web/integral-families'
SITE = 'https://perfectpower-explorer-download.towre676.chatgpt.site'


class Inspect(HTMLParser):
    def __init__(self):
        super().__init__()
        self.scripts = 0
        self.external = []
        self.roots = 0

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'script':
            self.scripts += 1
            if 'src' in attrs:
                self.external.append(attrs['src'])
        if tag == 'link' and attrs.get('rel') == 'stylesheet':
            self.external.append(attrs.get('href'))
        if attrs.get('id') == 'resonance-app':
            self.roots += 1


def assemble(download, inline):
    css = (WEB / 'resonance.css').read_text()
    javascript = (WEB / 'resonance.bundle.js').read_text()
    # Retain the dependency licenses inside each portable copy.
    javascript += '\n/*\n' + (WEB / 'resonance.bundle.js.LEGAL.txt').read_text().replace('*/', '* /') + '\n*/'
    for before, after in [
        ('./calculator.html', SITE + '/integrals/calculator.html'),
        ('./atlas.html', SITE + '/integrals/atlas.html'),
        ('./unification.html', SITE + '/integrals/unification.html'),
        ('/research', SITE + '/research'),
        ('/PerfectPower-Deep-Integral-Monograph.pdf', SITE + '/PerfectPower-Deep-Integral-Monograph.pdf'),
    ]:
        javascript = javascript.replace(json.dumps(before), json.dumps(after))
    javascript = javascript.replace('</script', '<\\/script')
    standalone = (WEB / 'resonance.html').read_text()
    standalone = standalone.replace('<link rel="stylesheet" href="./resonance.css">', '<style>' + css + '</style>')
    standalone = standalone.replace('<script src="./resonance.bundle.js" defer></script>', '<script>' + javascript + '</script>')
    fragment = (WEB / 'inline-fragment.html').read_text().replace('__RESONANCE_CSS__', css).replace('__RESONANCE_JAVASCRIPT__', javascript)
    if inline and len(fragment.encode()) >= 1_000_000:
        raise ValueError('Inline visualization exceeds one megabyte')
    results = []
    copies=[(Path(download), standalone)]
    if inline:
        copies.append((Path(inline), fragment))
    for target, content in copies:
        parser = Inspect()
        parser.feed(content)
        if parser.scripts != 1 or parser.roots != 1 or parser.external:
            raise ValueError('Portable copy contains an unexpected asset dependency or mount')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)
        results.append(dict(file=str(target), bytes=target.stat().st_size,
                            sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
    return results


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--download', type=Path, required=True)
    parser.add_argument('--inline', type=Path, help='also produce a self-contained in-chat fragment')
    args = parser.parse_args()
    print(json.dumps(assemble(args.download, args.inline)))
