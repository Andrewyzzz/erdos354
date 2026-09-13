"""Check maintained English documentation, local links, and the theorem map."""
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
DOCUMENTS = [
    'README.md', 'CREDITS.md', 'CHANGELOG.md', 'LICENSING.md',
    'proof/FORMALIZED_PROOF.md', 'proof/pdf/README.md',
    'formalization/README.md', 'formalization/STATUS.md',
    'formalization/RESULTS.md', 'formalization/ENVIRONMENT.md',
    'formalization/UPSTREAM.md', 'formalization/logs/REDACTION.md',
    'release/FORUM_POST.md', 'release/PUBLISHING.md',
]


def main():
    problems = []
    for relative in DOCUMENTS:
        path = ROOT / relative
        content = path.read_text()
        if re.search(r'[\u3400-\u4dbf\u4e00-\u9fff]', content):
            problems.append(f'{relative}: non-English maintained prose')
        for target in re.findall(r'\]\(([^\s)]+)\)', content):
            if target.startswith(('https://', 'http://', '#', 'mailto:')):
                continue
            target_path = target.split('#', 1)[0]
            if not (path.parent / target_path).exists():
                problems.append(f'{relative}: missing local link {target}')
    audit = (ROOT / 'formalization/Dyadic354/Audit.lean').read_text()
    names = set(re.findall(r'^#print axioms (\S+)', audit, re.M))
    status = (ROOT / 'formalization/STATUS.md').read_text()
    for name in re.findall(r'`((?:[A-Z]\w*\.)+\w+)`', status):
        if name.endswith(('.lean', '.md', '.json')):
            continue
        full = name if name.startswith('Dyadic354.') else 'Dyadic354.' + name
        if full not in names:
            problems.append(f'Theorem map names an unaudited declaration: {full}')
    original = (ROOT / 'proof/PROOF.md').read_text()
    current = (ROOT / 'proof/FORMALIZED_PROOF.md').read_text()
    marker = '## Appendix A. Complete finite mask certificate'
    if original.split(marker, 1)[1] != current.split(marker, 1)[1]:
        problems.append('The current manuscript appendix differs from the frozen certificate')
    if problems:
        raise SystemExit('\n'.join(problems))
    print(f'PASS: {len(DOCUMENTS)} English documents, local links, audited theorem map, and unchanged mask appendix')


if __name__ == '__main__':
    main()
