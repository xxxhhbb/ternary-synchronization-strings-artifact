// Independent verification of sufficient uninterrupted-match bounds.
// Uses direct cyclic shifts, not normalized factors or binary search.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const here = path.dirname(fileURLToPath(import.meta.url));
const words = fs.readFileSync(path.join(here,
  '../base/inputs/codewords_54_952.txt'), 'ascii').trim().split(/\r?\n/);
if (words.length !== 952 || new Set(words).size !== 952 ||
    words.some(w => !/^[012]{54}$/.test(w))) throw Error('invalid codebook');
// null means no finite bound is claimed by this relaxation.
const bounds = [null,41,41,41,41,47,45,83,36,39,42,49,56,50,44,47,44,
  null,null,61,72,39,66,75,82,null,46,52,46,null,82,75,66,39,72,61,
  null,null,44,47,44,50,56,49,42,39,36,83,45,47,41,41,41,41];
if (bounds.length !== 54) throw Error('invalid table');
const cache = new Map();
function incompatible(p,q,len) {
  const key = `${p}/${q}/${len}`;
  if (cache.has(key)) return cache.get(key);
  const left = new Set(words.map(w => w.slice(p,p+len)));
  for (const w of words) for (let d=0;d<3;d++) {
    const shifted = [...w.slice(q,q+len)].map(c => String((Number(c)+d)%3)).join('');
    if (left.has(shifted)) {cache.set(key,false);return false;}
  }
  cache.set(key,true);return true;
}
let checked=0;
for (let lag=1;lag<54;lag++) if (bounds[lag] !== null) {
  for (let start=0;start<54;start++) {
    let p=start,q=(start+lag)%54,remaining=bounds[lag]+1,killed=false;
    while (remaining>0) {
      const len=Math.min(54-p,54-q,remaining);
      if (incompatible(p,q,len)) {killed=true;break;}
      p=(p+len)%54;q=(q+len)%54;remaining-=len;
    }
    if (!killed) throw Error(`uncertified run bound lag=${lag} phase=${start}`);
    checked++;
  }
}
if (3*Math.max(bounds[9],bounds[10],bounds[11]) >= 225)
  throw Error('452 run argument does not close');
console.log('INDEPENDENT_PHASE_RUN_BOUNDS_PASS', JSON.stringify({checked,bounds,
  factorComparisons:cache.size,total452MatchedLength:225,total452RunCapacity:147}));
