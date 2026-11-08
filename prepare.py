#!/usr/bin/env python3
"""Recreate the recorded build configuration using one shared pinned package tree."""
import argparse,hashlib,json,pathlib,subprocess
p=argparse.ArgumentParser();p.add_argument('example');p.add_argument('--packages',type=pathlib.Path,required=True);a=p.parse_args();root=pathlib.Path(__file__).resolve().parent
index=json.loads((root/'manifest.json').read_text());row=next(x for x in index['examples'] if x['id']==a.example);case=root/row['directory'];meta=json.loads((case/'example.json').read_text());packages=a.packages.resolve()
for item in index['shared_dependencies']['packages']:
 q=packages/item['name'];actual=subprocess.check_output(['git','-C',str(q),'rev-parse','HEAD'],text=True).strip()
 if actual!=item['rev']:raise SystemExit('Wrong shared dependency pin: '+item['name'])
for item in meta['files']:
 q=case/item['path']
 if hashlib.sha256(q.read_bytes()).hexdigest()!=item['sha256']:raise SystemExit('Source hash mismatch: '+item['path'])
for item in meta['build_files']:
 raw=(case/'build-config'/item['snapshot']).read_bytes()
 if hashlib.sha256(raw).hexdigest()!=item['sha256']:raise SystemExit('Build configuration hash mismatch')
 for old,token in meta['build_path_replacements'].items():
  replacement=str(case) if token=='$CASE_ROOT' else str(packages)
  raw=raw.replace(old.encode(),replacement.encode())
 raw=raw.replace(b'/project/repo/norm-arith/.lake/packages',str(packages).encode())
 q=case/item['path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
# The validation environment supplied this single pinned shared package registry.
overrides={'version':'1.3.0','packages':[dict(name=x['name'],scope=x.get('scope',''),type='path',dir=str(packages/x['name']),inherited=x.get('inherited',True),manifestFile=x.get('manifestFile','lake-manifest.json'),configFile=x.get('configFile','lakefile.lean')) for x in index['shared_dependencies']['packages']]}
(case/'common-overrides.json').write_text(json.dumps(overrides,indent=2)+'\n')
print('Prepared',case)
print('lake --packages=common-overrides.json build '+meta['build_target'])
