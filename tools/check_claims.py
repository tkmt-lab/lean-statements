"""Check public statement/proof mappings, source hashes, and package boundaries."""
import ast
import hashlib
import json
from pathlib import Path
import re
import tomllib

from check import ROOT, read_only_correspondence

def load(name):return json.loads((ROOT/name).read_text())

def main():
    manifest=load('manifest.json');originals=read_only_correspondence(manifest)
    claims=load('claims.json');rows=claims['claims']
    assert claims['statement_only'] is True
    assert len(originals)==claims['problem_file_count']==9
    assert len(rows)==claims['claim_count']==18 and len({r['id'] for r in rows})==18
    expected={(p['id'],d['name']):(p,d) for p in manifest['problems'] for d in p['declarations']}
    actual=set()
    for row in rows:
        key=(row['id'].split('.')[0],row['declaration']);assert key in expected;actual.add(key)
        problem,decl=expected[key]
        assert row['file']==problem['file'] and row['line']==decl['normalized_line']
        text=(ROOT/row['file']).read_text();tail='\n'.join(text.splitlines()[row['line']-1:])
        assert tail.split(':= by',1)[0].rstrip()==row['statement_lean']
        assert row['body']=='by sorry (intentional statement placeholder)'
        assert row['public_proof']['executed_by_this_package'] is False
        assert row['public_proof']['url']==decl['formal_proof_url']
        assert re.search(r'/blob/[0-9a-f]{40}/.+#L[0-9]+$',row['public_proof']['url'])
        assert row['public_proof']['file_sha256']==decl['proof_file_sha256']
        assert row['source']['commit']==problem['source_commit']
        assert row['source']['sha256']==hashlib.sha256(originals[problem['id']]).hexdigest()
    assert actual==set(expected)
    summary=load('checks/statement-correspondence.json')
    recorded={(c['problem'],c['declaration']):c for run in summary['summaries'] for c in run['checks']}
    assert set(recorded)==set(expected)
    for row in rows:
        c=recorded[(row['id'].split('.')[0],row['declaration'])]
        assert c['type_equal'] and row['correspondence']['type_equal']
        assert c['lean_expr_repr_sha256']==row['correspondence']['lean_expr_repr_sha256']
    citation=load('CITATION.cff');zenodo=load('.zenodo.json')
    assert citation['version']==zenodo['version']==claims['version']==manifest['version']=='1.0.0'
    assert citation['date-released']==zenodo['publication_date']=='2026-10-23'
    assert citation['type']==zenodo['upload_type']=='software'
    assert citation['license'].lower()==zenodo['license'].lower()=='apache-2.0'
    config=tomllib.loads((ROOT/'lakefile.toml').read_text())
    previous='FormalConjecturesUtil'
    libs={x['name']:x for x in config['lean_lib']}
    for problem in manifest['problems']:
        name=problem['id']+'Statement';lib=libs[name]
        assert lib['roots']==['FormalConjectures.Paper.'+problem['id']]
        assert lib['needs']==[previous] and lib['moreLeanArgs']==['-j1','-M3072']
        previous=name
    assert config['defaultTargets']==[previous]
    # Inspect distributable source files only, never the user's local caches or logs.
    skipped={'.git','.lake','.build','work','__pycache__'}
    checked=0
    for path in ROOT.rglob('*'):
        if set(path.relative_to(ROOT).parts)&skipped or not path.is_file():continue
        if path.suffix=='.py':ast.parse(path.read_text())
        data=path.read_bytes()
        # Construct patterns so the scanner's own source is not a false positive.
        for prefix in [b'/'+b'Users/',b'/'+b'Volumes/']:
            assert prefix not in data,path.relative_to(ROOT)
        assert not re.search(rb'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}',data),path.relative_to(ROOT)
        assert path.suffix not in {'.gz','.zip','.pdf'},path.relative_to(ROOT)
        checked+=1
    print(f'PASS: {len(originals)} source files, {len(rows)} statement/proof mappings, metadata, serial build chain; {checked} public files scanned')

if __name__=='__main__':main()
