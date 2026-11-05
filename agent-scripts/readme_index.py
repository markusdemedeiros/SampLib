#!/usr/bin/env python3
"""Rebuild the README's terse sampler index from Occil's published lists/tables.

Run explicitly: this reads the live website. Ordinary builds and tests are offline.
Names/formulas are indexed; explanations, benchmark tables and derivations are omitted.
Code links are curated to actual implementations and restricted parameter domains.
"""
from collections import defaultdict
from html.parser import HTMLParser
from pathlib import Path
import re
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
BASE = 'https://peteroupc.github.io/'

class Node:
    def __init__(self, tag='', attrs=(), parent=None):
        self.tag, self.attrs, self.parent, self.children = tag, dict(attrs), parent, []

    def text(self):
        if self.tag == 'sup' and ('id' in self.attrs or 'footnote' in self.attrs.get('class','')):
            return ''
        result = ''.join(c.text() if isinstance(c,Node) else c for c in self.children)
        if self.tag == 'sup': return '^(' + result + ')'
        if self.tag == 'sub': return '_(' + result + ')'
        return result

    def walk(self, tags=None):
        if tags is None or self.tag in tags:
            yield self
        for c in self.children:
            if isinstance(c,Node): yield from c.walk(tags)

    def has_ancestor(self, tag):
        p = self.parent
        while p:
            if p.tag == tag: return True
            p = p.parent
        return False

class DOM(HTMLParser):
    def __init__(self):
        super().__init__(); self.root = Node(); self.current = self.root
    def handle_starttag(self, tag, attrs):
        n=Node(tag,attrs,self.current); self.current.children.append(n)
        if tag not in ['area','base','br','col','embed','hr','img','input','link','meta','param','source','track','wbr']:
            self.current=n
    def handle_endtag(self, tag):
        n=self.current
        while n.parent:
            if n.tag==tag:
                self.current=n.parent
                return
            n=n.parent
    def handle_data(self,data): self.current.children.append(data)


def clean(s):
    return re.sub(r'\s+', ' ', s).strip().replace('\\\\','\\')


def load(name):
    p=DOM()
    p.feed(urllib.request.urlopen(BASE+name+'.html', timeout=30).read().decode())
    return p.root


def section(root, anchor):
    """Document-order nodes after this heading, before its next peer/ancestor heading."""
    nodes=list(root.walk()); start=next(i for i,n in enumerate(nodes) if n.attrs.get('id')==anchor and n.tag.startswith('h'))
    level=int(nodes[start].tag[1])
    end=start+1
    while end<len(nodes):
        n=nodes[end]
        if re.fullmatch(r'h[1-6]',n.tag) and int(n.tag[1])<=level: break
        end+=1
    return nodes[start+1:end]


def heading_context(root):
    heading=None
    for n in root.walk():
        if re.fullmatch(r'h[1-6]',n.tag): heading=n
        yield n,heading


def first_label(li):
    strongs=list(li.walk({'strong'}))
    if strongs:
        return clean(strongs[0].text())
    text=clean(li.text())
    return text.split(':',1)[0].split('. ',1)[0]


def short_table_label(text):
    s=clean(text).rstrip('.')
    # Bibliographic authors/years are not part of the sampler's name.
    s=re.sub(r'\s*\([^()]*(?:18|19|20)\d{2}[^()]*\)', '', s)
    s=re.sub(r'\s*\(see.*?\)', '', s, flags=re.I)
    return s.strip()


def rows(table):
    return [[c for c in tr.children if isinstance(c,Node) and c.tag in ['th','td']]
            for tr in table.walk({'tr'})]


def label_key(label):
    s=clean(label).lower().replace('–','-').replace('—','-')
    return s.rstrip('.').strip()


GROUPS=[]

def group(title):
    items=[]; GROUPS.append((title,items)); return items


def add(items,label,source,anchor='',impl=None,note=''):
    label=clean(label)
    # Keep aliases across source sections, but not identical entries in one section.
    if any(label_key(i[0])==label_key(label) for i in items): return
    items.append((label,BASE+source+('' if source.endswith('.py') else '.html')+('#'+anchor if anchor else ''),impl,note))


def implementation(label,kind='distribution'):
    k=label_key(label)
    if kind=='distribution':
        mapping={
            'beta distribution': ('Continuous','integer shapes; order statistic'),
            'binomial distribution': ('Discrete','direct trials'),
            'dice': ('Discrete',''),
            'exponential distribution': ('Continuous','unit rate'),
            'gamma distribution': ('Continuous','positive integer shape, unit rate'),
            'gaussian distribution': ('Continuous','standard normal'),
            'geometric distribution': ('Discrete',''),
            'laplace (double exponential) distribution': ('Continuous','unit scale'),
            'normal distribution': ('Continuous','standard normal'),
            'poisson distribution': ('Discrete','rational mean'),
            'standard normal distribution': ('Continuous',''),
            'erlang distribution': ('Continuous','unit rate'),
            'hypergeometric distribution': ('Discrete',''),
            'multinomial distribution': ('Discrete','integer weights'),
            'negative binomial distribution': ('Discrete','integer success count'),
            'uniform distribution': ('Uniform','integer interval'),
            'kth-order statistic': ('Continuous','uniform order statistic'),
            'k th-order statistic': ('Continuous','uniform order statistic'),
            'pólya-eggenberger distribution': ('Discrete','nonnegative integer reinforcement'),
            'polya-eggenberger distribution': ('Discrete','nonnegative integer reinforcement'),
            'beta binomial distribution': ('Discrete','integer shapes via reinforced urn'),
            'max-of-uniform distribution': ('Continuous','positive integer n; order statistic'),
            'min-of-uniform distribution': ('Continuous','positive integer n; order statistic'),
            'pascal distribution': ('Discrete','integer shape; failure count'),
            '“irwin-hall distribution”': ('Continuous','integer number of uniforms'),
        }
        return mapping.get(k)
    return None


def implementation_path(label, impl, note=''):
    """Keep index links on implementations rather than compatibility facades."""
    if impl == 'Factories':
        impl = 'Bernoulli/Basic'
    elif impl == 'Combinatorial':
        impl = 'Combinatorial/Basic'
    elif impl == 'More':
        key = label.lower()
        if 'bounded' in key and 'geometric' in key:
            impl = 'Discrete/Bounded'
        elif any(word in key for word in ('sattolo', 'derangement', 'bit flips')):
            impl = 'Combinatorial/Permutations'
        elif key == 'rejection sampling' and 'generic' in note:
            impl = 'Continuous/Rejection'
        elif any(word in key for word in ('weighted', 'alias', 'rejection sampling')):
            impl = 'Weighted/Sequential'
        elif label in ('Certain Polynomials', 'cλ/(cλ+d)', 'λ/(1+λ)',
                       'Probability generating function'):
            impl = 'Bernoulli/Combinators'
    return f'code/Samplers/{impl}.lean'


def main():
    docs={n:load(n) for n in ['randomfunc','randomnotes','bernoulli','exporand','randmisc','bernsupp','randextract']}
    root=docs['randomfunc']
    source_counts={}
    g=group('Uniform integers and randomization')
    explicit=[
      ('RNDINT: inclusive integers','rndint-random-integers-in-0-n','Uniform',''),
      ('RNDINTRANGE: inclusive integer range','rndintrange-random-integers-in-n-m','Uniform',''),
      ('RNDINTEXC: exclusive integers','rndintexc-random-integers-in-0-n','Uniform',''),
      ('RNDINTEXCRANGE: exclusive integer range','rndintexcrange-random-integers-in-n-m','Uniform',''),
      ('Uniform random bits','uniform-random-bits','Uniform',''),
      ('Boolean / rational probability conditions','boolean-truefalse-conditions','Uniform',''),
      ('Choice / sampling with replacement','sampling-with-replacement-choosing-a-random-item-from-a-list','Combinatorial',''),
      ('Sampling without replacement','sampling-without-replacement-choosing-several-unique-items','Combinatorial',''),
      ('Ordered subset sampling','pseudocode-for-random-sampling','Combinatorial',''),
      ('Reservoir sampling','pseudocode-for-random-sampling','Combinatorial','finite input list'),
      ('Fisher–Yates shuffle','shuffling','Combinatorial',''),
      ('Random character strings','random-character-strings',None,''),
      ('Rejection sampling','rejection-sampling','More','generic proposal/predicate'),
      ('Random walks','random-walks','Discrete','symmetric integer increments'),
      ('Random dates and times','random-dates-and-times',None,''),
      ('Randomization in statistical testing','randomization-in-statistical-testing',None,''),
      ('Markov chains','markov-chains',None,''),
      ('Coupling from the past','markov-chains',None,''),
      ('Random graphs','random-graphs','Combinatorial','independent-edge construction'),
      ('Pólya–Eggenberger urn','plyandasheggenberger-distribution','Discrete','nonnegative integer reinforcement'),
      ('Positive integer compositions','random-integers-with-a-given-positive-sum','Combinatorial',''),
      ('Nonnegative integer compositions','random-integers-with-a-given-positive-sum','Combinatorial',''),
      ('Fixed-point uniform reals','for-fixed-point-number-formats',None,''),
      ('Rational-format uniform reals','for-rational-number-formats',None,''),
      ('Floating-point uniform reals','for-floating-point-number-formats',None,''),
      ('Inverse transform sampling','inverse-transform-sampling',None,''),
      ('PDF rejection sampling','rejection-sampling-with-a-pdf-like-function',None,''),
      ('Alternating-series sampling','alternating-series','Lazy','factorial-series factories'),
      ('Mixtures of distributions','mixtures-of-distributions','Continuous',''),
      ('Markov-chain Monte Carlo','markov-chain-monte-carlo',None,''),
      ('Piecewise-linear distribution','piecewise-linear-distribution',None,''),
      ('Random point in a simplex','random-points-inside-a-simplex',None,''),
      ('Random point on a sphere','random-points-on-a-sphere',None,''),
      ('Random point in a box, ball, shell or cone','random-points-inside-a-box-ball-shell-or-cone',None,''),
      ('Random latitude and longitude','random-latitude-and-longitude',None,''),
    ]
    for label,anchor,impl,note in explicit:add(g,label,'randomfunc',anchor,impl,note)

    for title,index,anchor in [('Uniform-integer algorithm comparison',1,'rndint-random-integers-in-0-n'),('Weighted-choice algorithm comparison',2,'weighted-choice')]:
        g=group(title)
        tables=list(root.walk({'table'}));table=tables[index]
        raw_rows=rows(table)[1:]
        assert len(raw_rows)==(9 if index==1 else 14), 'source algorithm table changed'
        source_counts[title]=len(raw_rows)
        integer_labels=['Integer rejection sampling','Multiply-and-shift reduction (approximate)',
          'Modulo reduction (approximate)','Fast Dice Roller','FYKY',
          'Math Forum / Mennucci bit recycling','FP Multiply','O’Neill conclusion algorithm',
          'Debiased / bitmask rejection']
        weighted_labels=['Linear search','Linear search with cumulative weights',
          'Fast Loaded Dice Roller','Saad et al. (2020b) samplers','Rejection sampling',
          'Bringmann–Panagiotou sampler','Walker alias method','Klundert alias variant',
          'Bringmann–Larsen succinct sampler','Hübschle-Schneider–Sanders sampler',
          'Tang sampler','Loaded Die from Unfair Coins','Knuth–Yao','Han–Hoshi']
        for cells,label in zip(raw_rows,integer_labels if index==1 else weighted_labels):
            mapped={
              'Integer rejection sampling':('Uniform','non-power-of-two source helper'),
              'Fast Dice Roller':('Uniform',''),
              'Linear search':('Discrete','integer weights'),
              'Walker alias method':('More','integer thresholds'),
            }.get(label)
            if index==2 and label=='Rejection sampling':mapped=('More','integer envelope')
            add(g,label,'randomfunc',anchor,*(mapped or (None,'')))
        if title.startswith('Weighted'):
            add(g,'Integer-envelope weighted rejection','randomfunc',anchor,'More','')
            add(g,'Weighted sampling without replacement','randomfunc','weighted-choice-without-replacement','More','sequential PPS')

    # Reproduce every top-level item of the main distribution index in source order.
    nodes=section(root,'index-of-nonuniform-distributions')
    top=[n for n in nodes if n.tag=='li' and not n.has_ancestor('li')]
    assert len(top)==106, 'main source index changed; review the 26/80 split'
    source_counts['Main distribution index']=len(top)
    g=group('Distribution index — most commonly used')
    for index,li in enumerate(top):
        if index==26:g=group('Distribution index — miscellaneous')
        label=first_label(li)
        mapped=implementation(label)
        add(g,label,'randomfunc','index-of-nonuniform-distributions',*(mapped or (None,'')))
    # Named subfamilies explicitly mentioned inside index entries.
    g=group('Distribution index — named subfamilies and alternatives')
    existing={label_key(first_label(li)) for li in top}
    for n in nodes:
        if n.tag!='strong' or n.parent.tag=='a' or not n.has_ancestor('li'):continue
        label=clean(n.text())
        if ('distribution' in label.lower() or 'copula' in label.lower()) and label_key(label) not in existing:
            add(g,label,'randomfunc','index-of-nonuniform-distributions',*(implementation(label) or (None,'')))

    g=group('More random sampling methods')
    root=docs['randomnotes']
    assert len(list(root.walk({'h4'})))==11, 'companion sampler headings changed'
    for n in root.walk({'h4'}):
        label=clean(n.text());mapped={
          'normal (gaussian) distribution':('Continuous','Karney-style standard normal only'),
          'gamma distribution':('Continuous','integer shape, unit rate only'),
          'beta distribution':('Continuous','integer shapes via order statistic only'),
        }.get(label_key(label))
        add(g,label,'randomnotes',n.attrs.get('id',''),*(mapped or (None,'')))
    for n,h in heading_context(root):
        if h is None or h.tag=='h2' or h.attrs.get('id') in ['contents','notes','appendix','license']:continue
        if n.tag=='strong':
            label=clean(n.text())
            if re.search(r'distribution|copula',label,re.I):
                add(g,label.rstrip(':'),'randomnotes',h.attrs.get('id',''),*(implementation(label) or (None,'')))
        if n.tag=='pre':
            for name in re.findall(r'\bMETHOD\s+(\w+)\(',n.text()):
                if name in ['VecAdd','VecScale','Decompose']:continue
                mapped=('Continuous','Karney-style alternative, not this method') if name=='NormalRatioOfUniforms' else None
                # A different normal algorithm is not an implementation of the printed method.
                add(g,name,'randomnotes',h.attrs.get('id',''))

    for label,anchor in [
      ('Strictly geometric stable distribution','stable-distribution'),
      ('General geometric stable distribution','stable-distribution'),
      ('Symmetric Linnik distribution','stable-distribution'),
      ('Mittag-Leffler distribution','stable-distribution'),
      ('Inhomogeneous phase-type distribution','phase-type-distributions'),
      ('T–Poisson hierarchy','gaussian-and-other-copulas'),
      ('Normal-to-anything method','gaussian-and-other-copulas'),
      ('Inhomogeneous multivariate phase-type distribution','multivariate-phase-type-distributions')]:
        add(g,label,'randomnotes',anchor)

    root=docs['bernoulli']
    current=None
    for n,h in heading_context(root):
        if n.tag=='h3':
            title=clean(n.text())
            current=group('Bernoulli factories — '+title) if n.attrs.get('id','').startswith(('algorithms-for-','other-general-')) else None
        if n.tag=='h4' and current is not None:
            key=n.attrs.get('id','')
            mapped={
              'certain-polynomials':('More','rational Bernstein coefficients'),
              'bernoulli-race-and-generalizations':('Factories','two-coin race only'),
              'expminus-expminusz':('Factories','rational z'),
              'expminuslambda--z':('Lazy','z=1'),
              'c--lambda--c--lambda--d-or-cd--lambda--1--cd--lambda':('More','positive rational c/d'),
              'lambda':('Factories','two variants'),
              'lambdaxy':('Factories','0 < x/y <= 1 only'),
              'sqrtlambda':('Factories',''),
              'arctanlambda-lambda':('Lazy',''),
              'arctanlambda':('Lazy',''),
              'coslambda':('Lazy',''),
              'sinlambda':('Lazy',''),
              'ln1lambda':('Lazy',''),
              'sinlambdasqrtc--lambdasqrtc':('Lazy','c=1 only'),
              'arctanxy--yx':('Lazy','0 <= x/y <= 1'),
              'pi--4':('Lazy','arctan factory at p=1'),
            }.get(key)
            label=clean(n.text())
            label={
              'expitz-or-1minus11expz-or-expz1expz-or-11expminusz':'expit(z)',
              'expitz2-minus-1-or-tanhz2-or-expzminus1expz1':'tanh(z/2)',
              'lambdaexpz--lambdaexpz--1-minus-lambda-or-lambdaexpz--1--lambdaexpz-minus-1':'λ exp(z) / (1 + λ(exp(z)−1))',
              'mklambda-or-exp-klambdacdotln2m':'2^(-m(k+λ))',
              'xycdotlambda-or-exp-lambdacdotln2xy':'2^(-(x/y)λ)',
              'c--lambda--c--lambda--d-or-cd--lambda--1--cd--lambda':'cλ/(cλ+d)',
            }.get(key,label)
            add(current,label,'bernoulli',key,*(mapped or (None,'')))
    g=group('Bernoulli factories — other factory functions')
    other_tables=[n for n in section(root,'other-factory-functions') if n.tag=='table']
    assert len(other_tables)==1 and len(rows(other_tables[0]))-1==31, 'other factories table changed'
    source_counts['Other factory functions']=31
    for cells in rows(other_tables[0])[1:]:
        label=short_table_label(cells[0].text())
        if label.startswith('1 − 1 / (1+(μ*λ/'):
            label='μλ/(1−μ+μλ)'
        compact=re.sub(r'\s+', '', label)
        mapped={
          '1−ν':('Factories','complement'), 'ν*λ':('Factories','product'),
          '(λ+μ)/2=(1/2)*λ+(1/2)*μ':('Factories','mean'),
          'ν*1+(1−ν)*μ=ν+μ−(ν*μ)':('Factories','disjunction'),
          'λ/(1+λ)':('More','unit logistic scale'),
        }.get(compact)
        add(g,label,'bernoulli','other-factory-functions',*(mapped or (None,'')))

    # Additional target-function tables are algorithm lists, unlike the appendix's
    # proof/benchmark tables or the earlier factory-impossibility examples.
    g=group('Bernoulli factories — power-series and simulation-schema targets')
    for table,h in heading_context(root):
        if table.tag!='table':continue
        rr=rows(table);head=clean(rr[0][0].text()) if rr else ''
        allowed=head in [r'Function $f(\lambda)$','Target function f(λ)','Original function (φ(λ))','Function','Breakpoints','Type']
        if not allowed:continue
        if head=='Function' and 'Values Allowed' not in clean(table.text()):continue
        for cells in rr[1:]:
            label=short_table_label(cells[1].text() if head=='Type' else cells[0].text())
            if head=='Original function (φ(λ))':label+=' minus D'
            if head=='Breakpoints':label='Piecewise linear: '+label
            mapped={'exp(−λ)':('Lazy',''), 'cos(λ)':('Lazy','')}.get(label)
            # Only explicit exp(-p) is linked. Complementing a new input is a
            # possible composition, not a separately implemented target here.
            add(g,label,'bernoulli',h.attrs.get('id',''),*(mapped or (None,'')))
    g=group('Bernoulli factories — elementary composition and extraction')
    for label,impl,note in [
      ('Complement','Factories',''),('Product / conjunction','Factories',''),
      ('Disjunction','Factories',''),('Mean','Factories',''),('Conditional mixture','Factories',''),
      ('Even-parity factory','Factories',''),('Probability generating function','More',''),
      ('von Neumann randomness extraction','Factories',''),
    ]:add(g,label,'bernoulli','algorithms',impl,note)

    root=docs['exporand'];
    assert len(list(root.walk({'h4'})))==22, 'PSRN sampler headings changed'
    g=group('Partially sampled random numbers — building blocks')
    selected=['sampling-uniform-psrns','sampling-e-rands','addition-and-subtraction','multiplication',
      'reciprocal-and-division','comparisons','samplegeometricbag','fillgeometricbag','kthsmallest',
      'power-of-uniform-subalgorithm','beta-distribution','exponential-distribution',
      'uniformmultiply-algorithm','oberhoffs-exact-rejection-sampling-method','ratio-of-uniforms','setting-digits-by-digit-probabilities']
    for n in root.walk({'h3'}):
        key=n.attrs.get('id','')
        if key in selected:
            mapped={'sampling-uniform-psrns':('Lazy','binary prefix stream'),
                    'comparisons':('Lazy','uniform bag vs rational only'),
                    'samplegeometricbag':('Lazy','')}.get(key)
            add(g,clean(n.text()),'exporand',key,*(mapped or (None,'')))
    g=group('Partially sampled random numbers — sampler families')
    for n in root.walk({'h4'}):add(g,clean(n.text()),'exporand',n.attrs.get('id',''))
    # Lindley-related mixture table has distribution names; benchmark tables do not.
    for table in root.walk({'table'}):
        rr=rows(table)
        if rr and clean(rr[0][0].text())=='Distribution':
            for cells in rr[1:]:add(g,short_table_label(cells[0].text()),'exporand','lindley-distribution-and-lindley-like-mixtures')

    for label in ['Sushila distribution','X-Lindley distribution']:
        add(g,label,'exporand','lindley-distribution-and-lindley-like-mixtures')

    root=docs['randmisc'];g=group('Miscellaneous sampling methods')
    anchors={
      'on-a-binomial-sampler','bounded-geometric-distribution','symmetric-geometric-distribution',
      'weighted-choice-with-weights-written-as-an-integer-and-fraction',
      'distributions-with-nowhere-increasing-or-nowhere-decreasing-weights',
      'unimodal-distributions-of-weights','weighted-choice-with-log-probabilities',
      'bernoulli-distribution-for-cumulative-distribution-functions','bit-vectors-with-random-bit-flips',
      'log-uniform-distribution','sampling-unbounded-monotone-density-functions',
      'random-variate-generation-via-quantiles','batching-random-samples-via-randomness-extraction',
      'sampling-distributions-using-incomplete-information','additional-algorithms'}
    for n in root.walk({'h2','h3','h4'}):
        key=n.attrs.get('id','')
        if key not in anchors:continue
        mapped={'bounded-geometric-distribution':('More','direct bounded trials only'),
                'bit-vectors-with-random-bit-flips':('More','')}.get(key)
        add(g,clean(n.text()),'randmisc',key,*(mapped or (None,'')))
    g=group('Miscellaneous distribution families')
    for label in ['Zero-truncated Poisson','exp-G','Alpha power transformed',
      'Exponentiated / Lehmann','Transmuted-G','Cubic rank transmuted','Biweight',
      'T-R{Y}','Odd X G','Odd log-logistic G','Rayleigh-G','Rayleigh–Rayleigh',
      'Generalized gamma-G','Inverse distribution','Weighted distribution',
      'Inflated distribution','Unit distribution','CDF–quantile family',
      'Compound minimum distribution','Complementary compound maximum distribution',
      'Random-stopped extremes','Stopped sums','Episodes (S,N)']:
        add(g,label,'randmisc','certain-families-of-distributions')
    g=group('Miscellaneous distribution tables')
    table_counts=[]
    for table,h in heading_context(root):
        if table.tag!='table':continue
        rr=rows(table)
        if rr and clean(rr[0][0].text())=='This distribution:':
            table_counts.append(len(rr)-1)
            for cells in rr[1:]:
                label=short_table_label(cells[0].text())
                label=re.sub(r'\s*\([^()]*(?:[<>≥≤]|greater than)[^()]*\)', '',label).rstrip(',')
                add(g,label,'randmisc',h.attrs.get('id',''))
    assert table_counts==[6,20,6], 'miscellaneous source tables changed'
    source_counts['Miscellaneous distribution tables']=sum(table_counts)

    g=group('Additional Python permutation methods')
    add(g,'Sattolo single-cycle permutation','randomgen.py',impl='More')
    add(g,'Uniform derangement','randomgen.py',impl='More',note='full-shuffle rejection variant')

    g=group('Supplemental general factory schemes')
    root=docs['bernsupp']
    selected=['building-the-lower-and-upper-polynomials','another-general-algorithm',
      'approximate-bernoulli-factories','multiple-output-bernoulli-factory','finite-state-and-pushdown-generators']
    for n in root.walk({'h2','h3','h4'}):
        if n.attrs.get('id') in selected:add(g,clean(n.text()),'bernsupp',n.attrs['id'])

    header='''# SampLib

Occil samplers as executable ProbLang `pl%` terms, intended for continuous TotalEris (CTE) proofs. Dependency: [logsem/clutch-lean](https://github.com/logsem/clutch-lean), commit `54e780e43709d2f28386b83bffccdde498141b25`, Lean 4.35.0.

```sh
lake build
python3 tests/statistical.py
```

[Implementation details and source corrections](code/README.md) · [ProbLang wishlist](agent-docs/ProbLangWishlist.md) · [Test results](tests/latest-results.json) · [Source inventory](agent-docs/OccilInventory.json)

The interpreter suite checks output laws and seeded environment/substitution agreement; see the recorded test results above. Statistical tests are implementation evidence. The interpreter runs finite-precision Float operations.

## Formal verification

[CTE templates](SampLib/Templates.lean) provide `IsDistSpec` for probability measures on arbitrary measurable output types, encoded as ProbLang values. Specifications accept arbitrary measurable continuation credits in the current ghost state and mask. `IsDistSpec.wp` supplies a continuation rule for use under `twp_bind`, including caller resources.

[Continuous threshold Bernoulli (`realCoin`)](SampLib/Samplers/RealCoin.lean) has a CTE specification for mathematical reals and every probability `p ∈ [0,1]`, including the endpoints. The file presents the target law, expected continuation credit, measurable credit kernel, credit-conservation identity, and total weakest-precondition theorem (`twp_realCoin`). The public theorem `realCoin_distSpec` packages it as `IsDistSpec`. Adequacy corollaries are omitted. `lake build` checks the proof. Other samplers remain unverified.

## Sampler index

A terse index of Occil's sampler lists and algorithm/distribution tables, grouped by source and technique. Each name links to its source; **code** links to the implementing file when present. A qualifier limits that link to the implemented parameter range or variant. No code link means the listed technique is not implemented here. Aliases and repeated appearances across articles are retained. Benchmark, parameter, and proof-derivation tables are omitted.

Generated from the live articles by `python3 agent-scripts/readme_index.py`; review code-link mappings when refreshing.
'''
    # Broken source anchors indicate an extraction/curation error rather than
    # an implemented sampler. Fail before replacing the README.
    for _,items in GROUPS:
        for label,url,_,_ in items:
            assert label, 'empty sampler name'
            if '#' in url:
                base,anchor=url.split('#',1)
                source=base.rsplit('/',1)[-1].removesuffix('.html')
                assert anchor in {n.attrs.get('id') for n in docs[source].walk()}, (source,anchor)
    out=[header.rstrip()]
    for title,items in GROUPS:
        out.extend(['','### '+title,''])
        for label,url,impl,note in items:
            label=label.replace('[','\\[').replace(']','\\]')
            text=f'- [{label}]({url})'
            if impl:
                path=implementation_path(label, impl, note)
                if not (ROOT/path).exists():raise RuntimeError('missing code path '+path)
                text+=f' — [code]({path})'
                if note:text+=' ('+note+')'
            out.append(text)
    (ROOT/'README.md').write_text('\n'.join(out)+'\n')
    print('groups:',len(GROUPS),'entries:',sum(len(items) for _,items in GROUPS),'code links:',sum(bool(i[2]) for _,items in GROUPS for i in items))
    for title,items in GROUPS:print(len(items),title)
    print('asserted source counts:',source_counts)

if __name__=='__main__':main()
