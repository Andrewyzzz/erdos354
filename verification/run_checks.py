#!/usr/bin/env python3
"""Reproduce finite checks in temporary directories. No network is used.
Default: certificate only. --full adds descent, FE, DB, and BG regressions.
Passing these tests is not a formal or independent proof certification.
"""
from __future__ import annotations
import argparse, hashlib, json, os, platform, shutil, subprocess, sys, tempfile, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    g=parser.add_mutually_exclusive_group()
    g.add_argument('--quick',action='store_true')
    g.add_argument('--full',action='store_true')
    parser.add_argument('--timeout',type=int,default=300)
    args=parser.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Do not run with -O: the checks use assertions.')
    if sys.version_info<(3,10):
        raise SystemExit('Python 3.10 or newer is required.')
    logdir=ROOT/'verification/local_logs'; logdir.mkdir(exist_ok=True)
    report={'scope':'Finite checks only; NOT a proof-assistant or peer-review certificate.',
            'mode':'full' if args.full else 'quick','python':platform.python_version(),'checks':[]}
    env=dict(os.environ); env.pop('PYTHONOPTIMIZE',None)
    env['PYTHONUTF8']='1';env['PYTHONHASHSEED']='0'
    with tempfile.TemporaryDirectory(prefix='erdos354-check-') as td:
        temp=Path(td)
        jobs=[('symbolic',ROOT/'certificate/check_templates.py')]
        if args.full:
            descent=temp/'descent';descent.mkdir()
            shutil.copy2(ROOT/'verification/descent/verify_gap_descent.py',descent)
            shutil.copy2(ROOT/'certificate/templates.json',descent/'template_certificate.json')
            legacy=temp/'legacy';legacy.mkdir()
            for p in (ROOT/'verification/legacy').glob('*.py'):shutil.copy2(p,legacy/p.name)
            nested=legacy/'prior_inputs';nested.mkdir()
            for name in ['erdos354_finite_event_decay.py','erdos354_digit_budget_bootstrap.py']:
                shutil.copy2(legacy/name,nested/name)
            for a,b in [('FE.zh-CN.md','erdos354_finite_event_decay_note.md'),('DB.zh-CN.md','erdos354_digit_budget_bootstrap_note.md')]:
                shutil.copy2(ROOT/'verification/inputs'/a,nested/b)
            jobs += [('gap_descent',descent/'verify_gap_descent.py'),
                     ('FE',legacy/'erdos354_finite_event_decay.py'),
                     ('DB',legacy/'erdos354_digit_budget_bootstrap.py'),
                     ('BG',legacy/'verify_gap_rigidity.py')]
        for label,path in jobs:
            begin=time.monotonic()
            try:
                p=subprocess.run([sys.executable,str(path)],cwd=path.parent,env=env,
                                 capture_output=True,text=True,timeout=args.timeout,check=False)
                code=p.returncode;log=p.stdout+('\nSTDERR:\n'+p.stderr if p.stderr else '')
            except subprocess.TimeoutExpired as exc:
                code=124;log='TIMEOUT: no pass is claimed.\n'
                if exc.stdout:log+=exc.stdout.decode('utf8','replace') if isinstance(exc.stdout,bytes) else exc.stdout
            (logdir/(label+'.log')).write_text(log,encoding='utf8')
            report['checks'].append({'name':label,'returncode':code,'passed':code==0,
                                    'seconds':round(time.monotonic()-begin,3),
                                    'script_sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
            print(label+(': PASS' if code==0 else ': FAIL'),flush=True)
            if code:print(log[-4000:],file=sys.stderr);break
        report['all_passed']=len(report['checks'])==len(jobs) and all(r['passed'] for r in report['checks'])
    report['proof_sha256']=hashlib.sha256((ROOT/'proof/PROOF.zh-CN.md').read_bytes()).hexdigest()
    report['english_proof_sha256']=hashlib.sha256((ROOT/'proof/PROOF.md').read_bytes()).hexdigest()
    report['certificate_sha256']=hashlib.sha256((ROOT/'certificate/templates.json').read_bytes()).hexdigest()
    (ROOT/'verification/local_run.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')
    print('Report: verification/local_run.json')
    return 0 if report['all_passed'] else 1
if __name__=='__main__':raise SystemExit(main())
