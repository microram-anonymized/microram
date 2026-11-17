#!/usr/bin/env python3
"""Build the single report; keep disposable TeX files in ../.build/."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT/'.build'
BUILD.mkdir(exist_ok=True)
for attempt in range(4):
    result = subprocess.run(
        ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
         '-output-directory', str(BUILD), 'REPORT.tex'],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (BUILD/f'pass-{attempt+1}.log').write_text(result.stdout)
    if result.returncode:
        print(result.stdout[-6000:])
        raise SystemExit(result.returncode)
    log = (BUILD/'REPORT.log').read_text()
    needs_rerun = any(marker in log for marker in (
        'Rerun to get', 'rerun to get', 'Label(s) may have changed',
        'Package rerunfilecheck Warning:'))
    if attempt and not needs_rerun:
        break
else:
    raise SystemExit('Report cross-references did not settle after four passes.')
if 'undefined' in log or 'multiply defined' in log:
    raise SystemExit('Unresolved or multiply-defined report references; see .build/REPORT.log.')
shutil.copy2(BUILD/'REPORT.pdf', ROOT/'REPORT.pdf')
for line in log.splitlines():
    if any(word in line for word in ('Warning', 'Overfull', 'Output written')):
        print(line)
print('Built', ROOT/'REPORT.pdf')
