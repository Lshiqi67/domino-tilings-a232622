"""检查当前投稿材料与公开源证据的一致性；不启动 Lean 或替代外部审稿。"""
from pathlib import Path
import argparse,csv,hashlib,json,re,subprocess,zipfile
R=Path(__file__).resolve().parents[1]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--manifest',action='store_true');args=ap.parse_args()
 paper=R/'papers/en';meta=read(R/'submission/metadata.json')
 expected=read(R/'review/arxiv-v2.1/candidate-package-report.json')
 assert digest(paper/'domino-tilings-en.pdf')==expected['final_pdf_sha256']
 zpath=R/'submission/domino-arxiv-source-20261028.zip'
 assert digest(zpath)==expected['source_zip_sha256']
 with zipfile.ZipFile(zpath) as z:
  assert sorted(z.namelist())==sorted(expected['tex_files']) and len(z.namelist())==14
  assert z.testzip() is None
  for n in z.namelist():assert hashlib.sha256(z.read(n)).hexdigest()==digest(paper/n)==expected['source_sha256'][n],n
 abstract=(R/'submission/abstract.txt').read_text().strip()
 assert abstract==meta['abstract'] and abstract in (paper/'main.tex').read_text()
 assert len(abstract)<=1920 and abstract.isascii()
 assert not any(meta[k] for k in ['uploaded','submitted','server_compiled','arxiv_id','doi'])
 assert meta['authors']=='Shiqi Liu (Dalian University of Technology)'
 counts={}
 for p in (R/'papers').glob('*/archive/*/SHA256.json'):
  d=read(p)
  for n,h in d['sha256'].items():assert digest(p.parent/n)==h,(str(p),n)
  counts[p.parent.relative_to(R).as_posix()]=len(d['sha256'])
 report=read(R/'review/arxiv-v2.1/verification/lean/report.json')
 assert report['status']=='m11_passed' and all(report['checks'].values())
 for n,h in report['source_sha256'].items():assert digest(R/'lean'/n)==h,n
 assert report['module_count']==83 and report['declaration_count']==1078
 assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in report['axiom_dependencies'].values())
 with (R/'review/arxiv-v2.1/formal-coverage.csv').open(encoding='utf-8-sig',newline='') as f:rows=list(csv.DictReader(f))
 for row in rows:
  line=(R/'lean'/row['source']).read_text(encoding='utf-8-sig').splitlines()[int(row['line'])-1]
  assert row['declaration'].split('.')[-1] in line,row
 tracked=subprocess.check_output(['git','ls-files','-z'],cwd=R).decode().split('\0')
 tracked=[n for n in tracked if n]
 badlinks=[];links=0
 for n in tracked:
  if n.endswith('.md') and '/archive/' not in n and '/verification/' not in n and '/evidence/' not in n:
   p=R/n
   # Historical layout reports are checked against their own frozen versions.
   if n=='papers/en/checks/readability-revision.md':continue
   for target in re.findall(r'\]\(([^)]+)\)',p.read_text(encoding='utf-8-sig')):
    if '://' in target or target.startswith('#'):continue
    target=target.split('#')[0]
    if not (p.parent/target).exists():badlinks.append([n,target])
    links+=1
 assert not badlinks,badlinks
 for n in tracked:
  if n.endswith(('.md','.json','.txt','.csv','.cff','.bib')):
   text=(R/n).read_text(encoding='utf-8-sig')
   assert not re.search(r'[CD]:[\\/](?:Users|ai4math-Math)|1456010547@|8283789',text),(n,'private metadata')
 if args.manifest:
  manifest=read(R/'MANIFEST-SHA256.json')['sha256']
  assert set(manifest)==set(tracked)-{'MANIFEST-SHA256.json'}
  for n,h in manifest.items():assert digest(R/n)==h,n
 result={'status':'passed','scope':'文件对应、摘要、历史归档、Lean验收输入/公理、声明定位、公开链接与隐私扫描；不启动Lean',
   'tex_files':14,'pdf_pages_as_verified_in_candidate':16,'abstract_characters':len(abstract),'archived_files':counts,
   'lean_input_files':len(report['source_sha256']),'formal_endpoints':len(rows),'relative_links_checked':links,'manifest_checked':args.manifest}
 (R/'tmp').mkdir(exist_ok=True)
 (R/'tmp/release-check.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
 print(json.dumps(result,ensure_ascii=False))
if __name__=='__main__':main()
