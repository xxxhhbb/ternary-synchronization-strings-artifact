"""Finite codebook facts for the border-spectrum / two-flank proof.

These exact finite checks are not Lean formalization of the general lemmas.
The input is the unchanged 952-word list, not prior shell output.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

EXPECTED='a1b4b912d956419ef59a15e5d0926ce337614a438da25923e19a65485da05e28'
P='012021'
S='120210'
U='012021201020120210'
V='12010201210201021'


def rot(w,a):
    return ''.join(str((int(c)+a)%3) for c in w)


def trie(words):
    root={}
    for word in words:
        node=root
        for c in word:
            node=node.setdefault(c,{})
    return root


def depth(root,word):
    for i,c in enumerate(word):
        if c not in root:
            return i
        root=root[c]
    return len(word)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path)
    args=parser.parse_args()
    if not __debug__:
        raise SystemExit('Do not use python -O.')
    start=time.perf_counter()
    raw=args.source.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==EXPECTED
    base=raw.decode('ascii').splitlines()
    assert len(base)==952 and base==sorted(set(base))
    assert all(len(w)==54 and set(w)<=set('012') and w[:6]==P and w[-6:]==S for w in base)
    assert set(base)=={w[::-1] for w in base}
    fam=[[rot(w,a) for w in base] for a in range(3)]
    all_words=sum(fam,[])
    recognition=0
    for d in range(1,54):
        lhs={w[d:] for w in all_words}
        rhs={w[:d] for w in all_words}
        for w in base:
            assert not (w[:54-d] in lhs and w[54-d:] in rhs)
            recognition+=1
    assert all(w[2:4]==w[49:51]=='20' and w[3:5]==w[50:52]=='02' for w in base)
    assert {rot('20',a) for a in range(3)}.isdisjoint({rot('02',a) for a in range(3)})
    spectrum=[]
    border_queries=0
    for t in range(6,27):
        tails={w[54-t:] for w in base}
        for delta in range(3):
            hits=[]
            for w in fam[delta]:
                border_queries+=1
                if w[:t] in tails:
                    hits.append(w[:t])
            if hits:
                spectrum.append((t,delta))
    assert spectrum==[(7,0),(17,0),(18,0),(24,0),(25,0)]
    assert [k for k in range(7,27) if (k,0) in spectrum and (k-1,0) in spectrum]==[18,25]
    rows=[]
    witnesses=[]
    capacity_checks=0
    expected={(18,1):(155,97,54),(18,2):(155,97,47),
              (25,1):(22,29,24),(25,2):(22,29,14)}
    for k in (18,25):
        d={w[:k] for w in base}
        aa=[w for w in base if w[54-k:] in d]
        for b in (1,2):
            bs={w[55-k:] for w in fam[b]}
            ee=[w for w in fam[b] if w[:k-1] in bs]
            htrie=trie(w[k-1:53] for w in ee)
            ttrie=trie(w[:54-k][::-1][:53-k] for w in aa)
            sums=[]
            for ci,C in enumerate(fam[3-b]):
                h=depth(htrie,C[:54-k])
                t=depth(ttrie,C[::-1][:53-k])
                capacity_checks+=1
                sums.append(h+t)
                if h+t>=54:
                    assert (k,b,h,t)==(18,1,28,26)
                    p=10
                    ar=[(i,w) for i,w in enumerate(base) if w in aa and w[p:36]==C[28:]]
                    er=[(i,w) for i,w in enumerate(fam[b]) if w in ee and w[17:45]==C[:28]]
                    assert ar and er
                    assert {w[36:] for _,w in ar}=={U}
                    assert {w[:17] for _,w in er}=={V}
                    witnesses.append(dict(C=ci+1,h=h,t=t,p=p,
                        A=[i+1 for i,_ in ar],E=[i+1 for i,_ in er]))
            assert (len(aa),len(ee),max(sums))==expected[(k,b)]
            rows.append(dict(k=k,b=b,A_words=len(aa),E_words=len(ee),max_sum=max(sums)))
    assert len(witnesses)==2
    dd=[w for w in base if w[:18]==U]
    bb=[w for w in fam[1] if w[31:37]==S and w[37:]==V]
    assert len(dd)==79 and len(bb)==18
    assert {w[18:21] for w in dd}=={'121','201'}
    d17={w[18:35] for w in dd}; b17={w[1:18] for w in bb}
    d7={w[18:25] for w in dd}; b7={w[:2]+w[3:8] for w in bb}
    assert d17.isdisjoint(b17) and d7.isdisjoint(b7)
    assert (len(d17),len(b17),len(d7),len(b7))==(38,12,5,2)
    # Same arithmetic coverage as the audited structural proof.
    for s in range(229,464,2):
        r=(s+1)//2
        if s<269:
            assert 7<=r-108<=26
        else:
            assert s>=269
            if r%54 in (0,1):
                assert (r-54 if r%54==0 else r-55)+47 < r-1
    for s in (456,462,464):
        assert s>=377
        assert all(x%54 for x in range(s//2-1,s//2+2))
    print(json.dumps(dict(status='BORDER_FLANK_INVARIANTS_PASS',
        codebook_sha256=EXPECTED,recognition_checks=recognition,
        normalized_border_set_pairs=63,border_word_memberships=border_queries,
        border_spectrum=spectrum,capacity_checks=capacity_checks,capacity_rows=rows,
        equality_witnesses=witnesses,
        endpoint_barriers=dict(D_words=len(dd),B_words=len(bb),
            disjoint_17_sizes=[len(d17),len(b17)],disjoint_7_sizes=[len(d7),len(b7)]),
        punctured_long_word_queries=0,old_shell_certificates_loaded=0,
        seconds=time.perf_counter()-start),indent=2))


if __name__=='__main__':
    main()
