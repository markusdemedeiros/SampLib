#!/usr/bin/env python3
"""Inventory published sampler sources, without treating every definition as an algorithm.
Run explicitly to refresh the live-site snapshot; normal builds/tests do not use the network.
"""
import hashlib
from datetime import datetime, timezone
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
ARTICLES = ['randomfunc','randomnotes','exporand','bernoulli','bernsupp','randmisc','randextract','bernapprox']
PYTHON = ['randomgen','bernoulli','betadist','moore','interval','fixed']

# These are algorithmic correspondences, not claims of literal or verified Python translation.
MAPPED = {
 'rndint': ['rndInt'], 'RNDINT':['rndInt'], 'rndintexc':['uniformInt'],
 'RNDINTEXC':['uniformInt'], 'rndintrange':['rndIntRange'], 'RNDINTRANGE':['rndIntRange'],
 'rndintexcrange':['rndIntExcRange'], 'RNDINTEXCRANGE':['rndIntExcRange'],
 'rndint_fastdiceroller':['fastDiceRoller'], 'RndIntHelperPowerOfTwo':['fastDiceRoller'],
 'RndIntHelperNonPowerOfTwo':['uniformFromModulus'], 'ZeroOrOne':['rationalCoin'],
 'zero_or_one':['rationalCoin'], 'shuffle':['shuffle'], 'Shuffle':['shuffle'],
 'sattolo':['sattolo'], 'derangement':['derangement'], 'choice':['choice'],
 'RandomKItemsFromFile':['reservoir'], 'RandomKItemsInOrder':['sampleInOrder'],
 'RandomWalk':['randomWalk'], 'randomwalk_posneg1':['randomWalk'],
 'WeightedChoice':['weightedChoice'], 'weighted_choice':['weightedChoice'],
 'CumulativeWeightedChoice':['weightedChoice'], 'Poisson1':['poissonOne'],
 'PoissonInt':['poissonRational'], 'poissonint':['poissonRational'],
 'NegativeBinomialInt':['negativeBinomial'], 'negativebinomialint':['negativeBinomial'],
 'PolyaEggenberger':['polyaEggenberger'], 'hypergeometric':['hypergeometric'],
 'PositiveIntegersWithSum':['positiveComposition'], 'IntegersWithSum':['weakComposition'],
 'Multinomial':['multinomial'], 'multinomial':['multinomial'], 'boundedGeometric':['boundedGeometric'],
 'complement':['complement'], 'product':['coinProduct'], 'disjunction':['coinDisjunction'],
 'mean':['coinMean'], 'conditional':['coinConditional'], 'evenparity':['evenParity'],
 'divoneplus':['oneDivOnePlus'], 'logistic':['logisticFactory'], 'probgenfunc':['probabilityGeneratingFactory'],
 'bernstein':['bernsteinFactory'], 'exp_minus':['expMinusMartingale'],
 'exp_minus_ext':['expMinusFactory'], 'zero_or_one_exp_minus':['expMinusRational'],
 'sin':['sineFactory'], 'cos':['cosineFactory'],
 'zero_or_one_arctan_n_div_n':['arctanOverPFactory'], 'geometric_bag':['sampleGeometricBag'],
}

class Article(HTMLParser):
 def __init__(self):
  super().__init__();self.heading=None;self.text=[];self.all=[];self.sections=[]
 def handle_starttag(self,tag,attrs):
  if tag in ['h2','h3','h4','h5']:
   self.heading=tag;self.anchor=dict(attrs).get('id');self.text=[]
 def handle_data(self,data):
  self.all.append(data)
  if self.heading:self.text.append(data)
 def handle_endtag(self,tag):
  if tag==self.heading:
   self.sections.append({'title':''.join(self.text),'anchor':self.anchor,'level':int(tag[1])})
   self.heading=None

def fetch(stem,ext):
 url=f'https://peteroupc.github.io/{stem}.{ext}'
 data=urllib.request.urlopen(url, timeout=30).read()
 return url,data.decode(),hashlib.sha256(data).hexdigest()

def main():
 sources=[];sections=[];entries=[]
 for stem in ARTICLES:
  url,text,digest=fetch(stem,'html');p=Article();p.feed(text)
  sources.append({'url':url,'sha256':digest})
  sections.extend({'url':url+'#'+(s['anchor'] or ''),**s} for s in p.sections)
  for name in dict.fromkeys(re.findall(r'\bMETHOD\s+([A-Za-z_]\w*)\s*\(',''.join(p.all))):
   entries.append({'source':url,'symbol':name,'kind':'pseudocode','helper':False})
 for stem in PYTHON:
  url,text,digest=fetch(stem,'py');sources.append({'url':url,'sha256':digest})
  stack=[]
  # Regex extraction is intentional: the published betadist.py snapshot does not
  # parse as Python (a malformed function signature). Preserve every definition,
  # including nested helpers and duplicates, without silently repairing the source.
  for lineno,line in enumerate(text.splitlines(),1):
   m=re.match(r'^(\s*)(class|def)\s+(\w+)',line)
   if not m:continue
   indent=len(m[1]);kind=m[2];name=m[3]
   while stack and stack[-1][0]>=indent:stack.pop()
   symbol='.'.join([x[1] for x in stack]+[name])
   entries.append({'source':url,'line':lineno,'symbol':symbol,'kind':kind,
                   'helper':name.startswith('_') or any(x[2]=='def' for x in stack)})
   stack.append((indent,name,kind))
 for e in entries:
  leaf=e['symbol'].split('.')[-1]
  terms=MAPPED.get(leaf,[]) if not e['helper'] else []
  e['related_terms']=terms
  e['status']='algorithmic_correspondence' if terms else 'unreviewed'
 report={'retrieved_utc':datetime.now(timezone.utc).date().isoformat(),'sources':sources,'sections':sections,'entries':entries,
         'counts':{'article_sections':len(sections),'source_entries':len(entries),
                   'correspondences':sum(bool(e['related_terms']) for e in entries)},
         'interpretation':'Sections/definitions include helpers, classes and duplicates. Counts are not distinct algorithms or a coverage percentage. Correspondences require variant/domain review and are not correctness proofs.'}
 (ROOT/'agent-docs/OccilInventory.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report['counts']))

if __name__=='__main__':main()
