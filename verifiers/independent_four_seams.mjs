// Exact direct four-equation projection. Does not use the marker prefilter,
// import the Python implementation, or read previous result files.
import fs from 'node:fs';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
const raw=fs.readFileSync(process.argv[2]);
assert.equal(crypto.createHash('sha256').update(raw).digest('hex'),
 'a1b4b912d956419ef59a15e5d0926ce337614a438da25923e19a65485da05e28');
const base=raw.toString('ascii').trim().split(/\r?\n/);
assert.equal(base.length,952);
assert.deepEqual(base,[...new Set(base)].sort());
assert(base.every(w=>w.length===54 && w.startsWith('012021') && w.endsWith('120210')));
const rot=(w,a)=>[...w].map(c=>(+c+a)%3).join('');
const fam=[0,1,2].map(a=>base.map(w=>rot(w,a)));
function sf(v){for(let h=1;h<=v.length/2;h++)for(let i=0;i+2*h<=v.length;i++)
 if(v.slice(i,i+h).join('')===v.slice(i+h,i+2*h).join(''))return false;return true;}
const outers=[];
for(let a=0;a<3;a++)for(let b=0;b<3;b++)for(let c=0;c<3;c++)for(let e=0;e<3;e++)
 if(sf([a,b,c,0,e]))outers.push([a,b,c,e]);
assert.equal(outers.length,10);
const U='012021201020120210',V='12010201210201021';
const expected=JSON.stringify([18,10,0,1,2,1,U,V]);
let queries=0,states=0,nonemptyStates=0;
const witnesses=[];
const borderSpectrum=[];
for(let t=6;t<=26;t++){
 const left=new Set(base.map(w=>w.slice(54-t)));
 const letters=[];
 for(let delta=0;delta<3;delta++)if(fam[delta].some(w=>left.has(w.slice(0,t))))letters.push(delta);
 if(letters.length)borderSpectrum.push({length:t,right_minus_left:letters});
}
assert.deepEqual(borderSpectrum,[7,17,18,24,25].map(t=>({length:t,right_minus_left:[0]})));
const borderStates=[];
for(let k=7;k<=26;k++){
 const D=new Set(fam[0].map(w=>w.slice(0,k)));
 const B=fam.map(v=>new Set(v.map(w=>w.slice(55-k))));
 for(const [a,b,c,e] of outers){
  const A=fam[a].map((w,i)=>({w,i})).filter(v=>D.has(v.w.slice(54-k)));
  const E=fam[e].map((w,i)=>({w,i})).filter(v=>B[b].has(v.w.slice(0,k-1)));
  if(A.length && E.length)borderStates.push({k,outer:[a,b,c,0,e],A:A.length,E:E.length});
  for(let p=1;p<=54-2*k;p++){
   states++;
   if(!A.length || !E.length)continue;
   nonemptyStates++;
   const left=new Map(),right=new Map();
   for(const v of A){const key=v.w.slice(p,54-k);if(!right.has(key))right.set(key,[]);right.get(key).push(v);}
   for(const v of E){const key=v.w.slice(k-1,p+2*k-1);if(!left.has(key))left.set(key,[]);left.get(key).push(v);}
   for(let ci=0;ci<952;ci++){
    queries++;
    const C=fam[c][ci],L=left.get(C.slice(0,p+k)),R=right.get(C.slice(p+k));
    if(!L || !R)continue;
    for(const av of R)for(const ev of L){
     const sig=[k,p,a,b,c,e,av.w.slice(54-k),ev.w.slice(0,k-1)];
     assert.equal(JSON.stringify(sig),expected);
     witnesses.push({signature:sig,A:av.i+1,C:ci+1,E:ev.i+1});
    }
   }
  }
 }
}
assert.equal(witnesses.length,2);
// A second computation of the scalar capacity table: direct word-pair
// LCP/LCS scans, not tries or a scan of deletion coordinates.
function commonPrefix(x,y,cap){let i=0;while(i<cap && x[i]===y[i])i++;return i;}
function commonSuffix(x,y,cap){let i=0;while(i<cap && x[x.length-1-i]===y[y.length-1-i])i++;return i;}
const capacityRows=[];
let capacityPairComparisons=0;
for(const k of [18,25]){
 const d=new Set(base.map(w=>w.slice(0,k)));
 const A=base.filter(w=>d.has(w.slice(54-k)));
 for(const b of [1,2]){
  const bs=new Set(fam[b].map(w=>w.slice(55-k)));
  const E=fam[b].filter(w=>bs.has(w.slice(0,k-1)));
  let maximum=0,positive=0;
  for(const C of fam[3-b]){
   let h=0,t=0;
   for(const e of E){capacityPairComparisons++;h=Math.max(h,commonPrefix(C,e.slice(k-1),54-k));}
   for(const a of A){capacityPairComparisons++;t=Math.max(t,commonSuffix(C,a.slice(0,54-k),53-k));}
   maximum=Math.max(maximum,h+t);
   if(h+t>=54){positive++;assert.equal(k,18);assert.equal(b,1);assert.equal(h,28);assert.equal(t,26);}
  }
  capacityRows.push({k,b,A_words:A.length,E_words:E.length,max_sum:maximum,positive});
 }
}
assert.deepEqual(capacityRows.map(v=>[v.k,v.b,v.A_words,v.E_words,v.max_sum,v.positive]),
 [[18,1,155,97,54,2],[18,2,155,97,47,0],[25,1,22,29,24,0],[25,2,22,29,14,0]]);
const targets=fam[0].filter(w=>w.startsWith(U));
const sources=fam[1].filter(w=>w.slice(31,37)==='120210' && w.slice(37)===V);
assert.equal(targets.length,79);assert.equal(sources.length,18);
const headers=[...new Set(targets.map(w=>w.slice(18,21)))].sort();
assert.deepEqual(headers,['121','201']);
let pairChecks=0;
for(const d of targets)for(const b of sources){
 pairChecks++;
 assert.notEqual(d.slice(18,35),b.slice(1,18));
 assert.notEqual(d.slice(18,25),b.slice(0,2)+b.slice(3,8));
}
// A deletion beyond coordinate 2 leaves prefix 120 unchanged. Deleting
// coordinate 1 produces 101. The only remaining possibilities are 0,2.
assert.equal(rot('012021',1).slice(0,3),'120');
assert.equal((rot('012021',1).slice(0,1)+rot('012021',1).slice(2)).slice(0,3),'101');
console.log(JSON.stringify({status:'INDEPENDENT_FOUR_SEAMS_PASS',
 algorithm:'C-first direct four-equation joins without marker pruning',
 normalized_outer_words:outers.length,phase_start_outer_states:states,
 nonempty_phase_start_outer_states:nonemptyStates,middle_codeword_queries:queries,
 borderSpectrum,borderStates,witnesses,
 capacityRows,capacity_pair_comparisons:capacityPairComparisons,
 endpoint_pair_checks:pairChecks,D_words:targets.length,B_words:sources.length,
 punctured_long_word_queries:0},null,2));
