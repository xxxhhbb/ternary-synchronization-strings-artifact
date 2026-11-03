"""Reference implementation of the batched bounded-event violation oracle.

This tests event detection and cache maintenance, not the full Brinkhuis
construction or its practical performance. Only one witness is stored per
ordered pair of interval starts. All lengths are tested in one prefix-LCS
dynamic program. An explicit linked list supports constant-time selection.
"""
class PairOracle:
    def __init__(self,word,block_length,cutoff,remote_threshold,denominator):
        self.word=list(word);self.n=len(word);self.m=block_length
        self.B=cutoff;self.R=remote_threshold;self.D=denominator
        size=self.n*self.n
        self.witness=[None]*size
        self.active=[False]*size
        self.marked=[False]*size
        self.next=[-1]*size;self.prev=[-1]*size;self.head=-1
        self.evaluations=0
        for p in range(self.n):
            for q in range(p+1,self.n):self._refresh(p,q)

    def _evaluate(self,p,q):
        self.evaluations+=1
        aa=min(self.B-1,q-p)
        bb=min(self.B-1,self.n-q)
        row=[0]*(bb+1)
        for a in range(1,aa+1):
            new=[0]*(bb+1)
            for b in range(1,bb+1):
                new[b]=row[b-1]+1 if self.word[p+a-1]==self.word[q+b-1] else max(row[b],new[b-1])
                s=a+b
                eligible=s<=self.B and ((p+a==q and s>self.D)
                                       or (p+a<q and s>=self.R))
                if eligible and (s-2*new[b])*self.D<s:
                    return (p,a,q,b)
            row=new
        return None

    def _refresh(self,p,q):
        index=p*self.n+q
        answer=self._evaluate(p,q)
        self.witness[index]=answer
        if answer is not None and not self.active[index]:
            self.active[index]=True;self.prev[index]=-1;self.next[index]=self.head
            if self.head!=-1:self.prev[self.head]=index
            self.head=index
        elif answer is None and self.active[index]:
            left,right=self.prev[index],self.next[index]
            if left==-1:self.head=right
            else:self.next[left]=right
            if right!=-1:self.prev[right]=left
            self.active[index]=False;self.prev[index]=self.next[index]=-1

    def select(self):
        return None if self.head==-1 else self.witness[self.head]

    def update_blocks(self,replacements):
        blocks=sorted(replacements)
        if not blocks:return
        regions=[]
        for block in blocks:
            lo=block*self.m;hi=min(self.n,lo+self.m)
            assert 0<=lo<hi and len(replacements[block])==hi-lo
            self.word[lo:hi]=replacements[block]
            if regions and regions[-1][1]==lo:regions[-1]=(regions[-1][0],hi)
            else:regions.append((lo,hi))
        # The theorem uses at most two regions; more still works but changes
        # the constant in the affected-pair count.
        touched=[]
        def mark(p,q):
            index=p*self.n+q
            if not self.marked[index]:
                self.marked[index]=True
                touched.append(index)
        for lo,hi in regions:
            for p in range(max(0,lo-self.B+1),min(self.n-1,hi-1)+1):
                for q in range(p+1,self.n):mark(p,q)
            for q in range(max(1,lo-self.B+1),min(self.n-1,hi-1)+1):
                for p in range(q):mark(p,q)
        for index in touched:
            self._refresh(*divmod(index,self.n))
        for index in touched:
            self.marked[index]=False

    def audit_list(self):
        seen=set();last=-1;current=self.head
        while current!=-1:
            assert current not in seen and self.active[current]
            assert self.prev[current]==last and self.witness[current] is not None
            seen.add(current);last=current;current=self.next[current]
        assert seen=={i for i,value in enumerate(self.active) if value}

def lcs_reference(x,y):
    matrix=[[0]*(len(y)+1) for _ in range(len(x)+1)]
    for i,c in enumerate(x,1):
        for j,d in enumerate(y,1):
            matrix[i][j]=matrix[i-1][j-1]+1 if c==d else max(matrix[i-1][j],matrix[i][j-1])
    return matrix[-1][-1]

def audit_all(oracle):
    n=oracle.n;w=oracle.word
    assert not any(oracle.marked)
    for p in range(n):
        for q in range(p+1,n):
            first=None
            for a in range(1,min(oracle.B-1,q-p)+1):
                for b in range(1,min(oracle.B-a,n-q)+1):
                    s=a+b
                    eligible=(p+a==q and s>oracle.D) or (p+a<q and s>=oracle.R)
                    if eligible and (s-2*lcs_reference(w[p:p+a],w[q:q+b]))*oracle.D<s:
                        first=(p,a,q,b);break
                if first is not None:break
            assert oracle.witness[p*n+q]==first,(p,q,oracle.witness[p*n+q],first)
    oracle.audit_list()

if __name__=='__main__':
    from random import Random
    rng=Random(217216)
    audits=updates=0
    for n in (9,15,24):
        for cutoff,remote,D in ((5,3,2),(9,6,3),(12,7,4)):
            for m in (1,3,5):
                word=[rng.randrange(3) for _ in range(n)]
                oracle=PairOracle(word,m,cutoff,remote,D)
                audit_all(oracle);audits+=1
                for step in range(8):
                    event=oracle.select()
                    if event is None:
                        chosen={rng.randrange((n+m-1)//m)}
                    else:
                        p,a,q,b=event
                        chosen=set(range(p//m,(p+a-1)//m+1))|set(range(q//m,(q+b-1)//m+1))
                    replacements={block:[rng.randrange(3) for _ in range(min(m,n-block*m))]
                                  for block in chosen}
                    oracle.update_blocks(replacements)
                    audit_all(oracle);audits+=1;updates+=1
    print('BATCHED_PAIR_ORACLE_EXHAUSTIVE_COMPARISON_PASS',
          dict(full_state_audits=audits,updates=updates))
