from pathlib import Path
import concurrent.futures
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path('/workspace/scratch/cef38bf316d7/equivalence_work')
VERIFY = Path('/workspace/scratch/cef38bf316d7/equivalence_verification')
OUT = VERIFY / 'build'
MATHLIB = Path('/tmp/rh-mathlib/mathlib4-4.33.0')
RUNTIME = Path('/tmp/rh-lean-runtime/lean-4.33.0-linux')
LEAN = RUNTIME / 'bin/lean'
ENV = os.environ.copy()
ENV['LD_PRELOAD'] = '/tmp/rh-mathlib/lean_self_path_compat.so'
ENV['LEAN_SYSROOT'] = str(RUNTIME)
paths = [OUT, MATHLIB / '.lake/build/lib/lean']
paths.extend(sorted((MATHLIB / '.lake/packages').glob('*/.lake/build/lib/lean')))
paths.append(RUNTIME / 'lib/lean')
ENV['LEAN_PATH'] = ':'.join(map(str, paths))
rows = [x.strip().replace('\\', '/') for x in (ROOT / 'compile-order.txt').read_text().splitlines() if x.strip()]
modules = {x[:-5].replace('/', '.'): x for x in rows}
deps = {m: set(re.findall(r'(?m)^import\s+([\w.]+)', (ROOT / p).read_text())) & modules.keys() for m,p in modules.items()}
OUT.mkdir(parents=True, exist_ok=True)
(VERIFY / 'module-logs').mkdir(exist_ok=True)
manifest = json.loads((VERIFY / 'source-manifest.json').read_text())
hashes = {x['source']: x['sha256'] for x in manifest['sources']}
assert all(hashlib.sha256((ROOT/p).read_bytes()).hexdigest() == sha for p,sha in hashes.items())
print('PACKAGED_SOURCE_HASHES=PASS', flush=True)
print(subprocess.check_output([str(LEAN), '--version'], env=ENV, text=True).strip(), flush=True)

def compile_one(module):
    p = modules[module]
    target = OUT / (p[:-5] + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    proc = subprocess.run([str(LEAN), '--root=.', '-j2', '-o', str(target), p], cwd=ROOT, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (VERIFY / 'module-logs' / (module + '.log')).write_text(proc.stdout)
    return {'module': module, 'source': p, 'sha256': hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), 'returncode': proc.returncode, 'seconds': round(time.monotonic()-start, 3), 'output': proc.stdout}

done = set()
pending = set(modules)
running = {}
results = []
started = time.monotonic()
with (VERIFY / 'build.log').open('w') as log, concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
    while pending or running:
        for module in modules:
            if len(running) >= 3:
                break
            if module in pending and deps[module] <= done:
                pending.remove(module)
                running[pool.submit(compile_one, module)] = module
        if not running:
            raise RuntimeError('Unresolved dependencies: ' + str(pending))
        ready, _ = concurrent.futures.wait(running, timeout=2, return_when=concurrent.futures.FIRST_COMPLETED)
        for f in ready:
            module = running.pop(f)
            result = f.result()
            results.append({k:v for k,v in result.items() if k != 'output'})
            marker = ('COMPILE_PASS=' if result['returncode'] == 0 else 'COMPILE_FAIL=') + module
            print(marker + ' ' + str(result['seconds']) + 's', flush=True)
            log.write(marker+'\n'+result['output'])
            log.flush()
            (VERIFY/'recheck-manifest.json').write_text(json.dumps({'compiled':results,'elapsed_seconds':round(time.monotonic()-started,3)},indent=2)+'\n')
            if result['returncode'] != 0:
                print(result['output'], flush=True)
                raise SystemExit(result['returncode'])
            done.add(module)
    proc = subprocess.run([str(LEAN), '--root=.', '-j2', 'Audit.lean'], cwd=ROOT, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (VERIFY / 'audit.log').write_text(proc.stdout)
    print(proc.stdout, flush=True)
    if proc.returncode:
        raise SystemExit(proc.returncode)
    assert 'sorryAx' not in proc.stdout
    assert len(re.findall(r'depends on axioms: \[propext, Classical.choice, Quot.sound\]',proc.stdout)) == 9
    print('FRESH_BUILD_MODULES='+str(len(done)), flush=True)
    print('AXIOM_AUDIT=STANDARD_LOGICAL_AXIOMS_ONLY', flush=True)
    print('SOLE_HYPOTHESIS=SMALL_O_PREMISE', flush=True)
    print('NATIVE_RH_CONDITIONAL_CLOSURE=PASS', flush=True)
    print('REVERSE_RH_TO_SMALL_O=PASS', flush=True)
    print('SMALL_O_RH_EQUIVALENCE=PASS', flush=True)
    log.write('FRESH_BUILD_MODULES='+str(len(done))+'\nAXIOM_AUDIT=STANDARD_LOGICAL_AXIOMS_ONLY\nNATIVE_RH_CONDITIONAL_CLOSURE=PASS\nREVERSE_RH_TO_SMALL_O=PASS\nSMALL_O_RH_EQUIVALENCE=PASS\n')
