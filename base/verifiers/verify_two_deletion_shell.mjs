#!/usr/bin/env node
// Enumerate two-deletion cases at a specified total length.

import fs from "node:fs";

const M = 54, K = 952;
const TOTAL = Number(process.argv[3] ?? 464), HALF = TOTAL / 2;
if (!Number.isInteger(HALF)) throw new Error("total must be even");

function squareFree(word) {
  for (let start = 0; start < word.length; start++) {
    for (let p = 1; start + 2 * p <= word.length; p++) {
      let equal = true;
      for (let j = 0; j < p; j++) {
        if (word[start + j] !== word[start + p + j]) { equal = false; break; }
      }
      if (equal) return false;
    }
  }
  return true;
}

const outerCache = new Map();
function outerWords(length) {
  if (outerCache.has(length)) return outerCache.get(length);
  const answer = [];
  function visit(prefix) {
    if (prefix.length === length) { answer.push(prefix.slice()); return; }
    for (let c = 0; c < 3; c++) {
      prefix.push(c);
      if (squareFree(prefix)) visit(prefix);
      prefix.pop();
    }
  }
  visit([0]);
  outerCache.set(length, answer);
  return answer;
}

function groupedPairs(offset, mode, deletions) {
  let left, right;
  const pairs = [];
  if (mode === "left-longer") {
    left = HALF + 1; right = HALF - 1;
    const removed = new Set(deletions);
    const survivors = [];
    for (let i = 0; i < left; i++) if (!removed.has(i)) survivors.push(i);
    for (let j = 0; j < right; j++) pairs.push([offset + survivors[j], offset + left + j]);
  } else if (mode === "right-longer") {
    left = HALF - 1; right = HALF + 1;
    const removed = new Set(deletions);
    const survivors = [];
    for (let j = 0; j < right; j++) if (!removed.has(j)) survivors.push(j);
    for (let i = 0; i < left; i++) pairs.push([offset + i, offset + left + survivors[i]]);
  } else {
    left = right = HALF;
    const [dl, dr] = deletions;
    const xs = [], ys = [];
    for (let i = 0; i < HALF; i++) if (i !== dl) xs.push(i);
    for (let j = 0; j < HALF; j++) if (j !== dr) ys.push(j);
    for (let k = 0; k < HALF - 1; k++) pairs.push([offset + xs[k], offset + left + ys[k]]);
  }
  const groups = new Map();
  for (const [first, second] of pairs) {
    const u = Math.floor(first / M), lu = first % M;
    const v = Math.floor(second / M), lv = second % M;
    const key = `${u},${v}`;
    if (!groups.has(key)) groups.set(key, {u, v, pairs: []});
    groups.get(key).pairs.push([lu, lv]);
  }
  return {
    blockCount: Math.floor((offset + TOTAL - 1) / M) + 1,
    edges: [...groups.values()].sort((a, b) => a.u - b.u || a.v - b.v),
  };
}

function relationKey(delta, pairs) {
  return `${delta}|${pairs.map(([a, b]) => `${a}:${b}`).join(",")}`;
}

const cache = new Map();
function incompatible(words, delta, pairs) {
  const key = relationKey(delta, pairs);
  if (cache.has(key)) return cache.get(key);
  const left = new Set();
  for (const word of words) left.add(pairs.map(([p]) => word[p]).join(""));
  let answer = true;
  for (const word of words) {
    const signature = pairs
      .map(([, p]) => String((Number(word[p]) + delta) % 3))
      .join("");
    if (left.has(signature)) { answer = false; break; }
  }
  cache.set(key, answer);
  return answer;
}

function* deletionPatterns(mode) {
  if (mode === "equal") {
    for (let left = 0; left < HALF; left++) {
      for (let right = 0; right < HALF; right++) yield [left, right];
    }
  } else {
    for (let first = 0; first < HALF + 1; first++) {
      for (let second = first + 1; second < HALF + 1; second++) yield [first, second];
    }
  }
}

function verifyMode(words, mode) {
  let patterns = 0, universal = 0, contexts = 0, contextKilled = 0;
  for (let offset = 0; offset < M; offset++) {
    for (const deletions of deletionPatterns(mode)) {
      patterns++;
      const {blockCount, edges} = groupedPairs(offset, mode, deletions);
      let universalKill = false;
      for (const edge of edges) {
        if ([0, 1, 2].every(delta => incompatible(words, delta, edge.pairs))) {
          universalKill = true;
          break;
        }
      }
      if (universalKill) { universal++; continue; }

      for (const outer of outerWords(blockCount)) {
        contexts++;
        let killed = false;
        for (const edge of edges) {
          const delta = (outer[edge.v] - outer[edge.u] + 3) % 3;
          if (incompatible(words, delta, edge.pairs)) { killed = true; break; }
        }
        if (!killed) {
          throw new Error(`surviving context: ${mode} offset=${offset} deletions=${deletions} outer=${outer}`);
        }
        contextKilled++;
      }
    }
  }
  return {mode, patterns, universal, contexts, contextKilled};
}

const source = process.argv[2];
if (!source) throw new Error("usage: node verify_two_deletion_shell.mjs SOURCE [TOTAL]");
const raw = fs.readFileSync(source);
const words = raw.toString("ascii").trimEnd().split(/\r?\n/);
if (words.length !== K || new Set(words).size !== K) throw new Error(`expected ${K} distinct canonical codewords`);
if (words.some(word => !/^[012]{54}$/.test(word))) throw new Error("malformed canonical codeword");
if (words.join("\n") !== [...words].sort().join("\n")) throw new Error("canonical codewords are not sorted");
const reversals = new Set(words.map(word => [...word].reverse().join("")));
if (words.some(word => !reversals.has(word))) throw new Error("codebook is not reversal closed");

const results = ["left-longer", "right-longer", "equal"].map(mode => verifyMode(words, mode));
const totals = results.reduce((a, r) => ({
  patterns: a.patterns + r.patterns,
  universal: a.universal + r.universal,
  contexts: a.contexts + r.contexts,
  contextKilled: a.contextKilled + r.contextKilled,
}), {patterns: 0, universal: 0, contexts: 0, contextKilled: 0});

const expected = new Map([
  [456, {patterns: 5626584, universal: 5626584, contexts: 0}],
  [462, {patterns: 5775462, universal: 5775462, contexts: 0}],
  [464, {patterns: 5825520, universal: 5813074, contexts: 474732}],
]);
if (!expected.has(TOTAL)) throw new Error(`no independent expected-count record for total ${TOTAL}`);
const want = expected.get(TOTAL);
if (totals.patterns !== want.patterns) throw new Error(`unexpected pattern total ${totals.patterns}`);
if (totals.universal !== want.universal) throw new Error(`unexpected universal total ${totals.universal}`);
if (totals.contexts !== want.contexts || totals.contextKilled !== want.contexts) throw new Error("unexpected context counts");
console.log(`INDEPENDENT_TWO_DELETION_${TOTAL}_PASS`);
console.log(JSON.stringify({results, totals, relationCacheEntries: cache.size}, null, 2));
