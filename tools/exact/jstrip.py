"""Strip Java comments (string/char-literal aware), imports, package lines and blank lines.
usage: jstrip.py OUTDIR file.java...   (writes OUTDIR/<basename>)"""
import os, sys


def strip(src):
    out, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c == '"' or c == "'":
            q = c
            j = i + 1
            while j < n and src[j] != q:
                j += 2 if src[j] == '\\' else 1
            out.append(src[i:j + 1])
            i = j + 1
        elif src.startswith('//', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
        elif src.startswith('/*', i):
            j = src.find('*/', i + 2)
            seg = src[i:(n if j < 0 else j + 2)]
            out.append('\n' * seg.count('\n'))
            i = n if j < 0 else j + 2
        else:
            out.append(c)
            i += 1
    lines = []
    for l in ''.join(out).split('\n'):
        s = l.strip()
        if not s or s.startswith('import ') or s.startswith('package ') or 'serialVersionUID' in s:
            continue
        lines.append(l.rstrip())
    return '\n'.join(lines) + '\n'


def main():
    od = sys.argv[1]
    os.makedirs(od, exist_ok=True)
    for f in sys.argv[2:]:
        with open(f, encoding='utf-8', errors='replace') as r:
            s = strip(r.read())
        with open(os.path.join(od, os.path.basename(f)), 'w', encoding='utf-8') as w:
            w.write(s)


if __name__ == '__main__':
    main()
