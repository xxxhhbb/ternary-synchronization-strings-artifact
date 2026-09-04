#!/usr/bin/env node
// Independent JavaScript replay of a range of odd one-deletion shells.
// It does not import or execute the Python producer.

import fs from "node:fs";
import path from "node:path";

const M = 54, K = 952;
const FULL = (1n << BigInt(K)) - 1n;

function squareFree(word) {
  for (let start = 0; start < word.length; start++) {
    for (let p = 1; start + 2 * p <= word.length; p++) {
      let equal = true;
      for (let j = 0; j < p; j++) if (word[start + j] !== word[start + p + j]) { equal = false; break; }
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
    for (let c = 0; c < 3; c++) { prefix.push(c); if (squareFree(prefix)) visit(prefix); prefix.pop(); }
  }
  visit([0]);
  outerCache.set(length, answer);
  return answer;
}

function pattern(total, offset, deletion, orientation) {
  const longer = (total + 1) >> 1, shorter = longer - 1;
  const groups = new Map();
  function add(first, second) {
    const u = Math.floor(first / M), lu = first % M, v = Math.floor(second / M), lv = second % M;
    const key = `${u},${v}`;
    if (!groups.has(key)) groups.set(key, {u, v, pairs: []});
    groups.get(key).pairs.push([lu, lv]);
  }
  if (orientation === "left-longer") {
    for (let j = 0; j < shorter; j++) add(offset + (j < deletion ? j : j + 1), offset + longer + j);
  } else {
    for (let i = 0; i < shorter; i++) add(offset + i, offset + shorter + (i < deletion ? i : i + 1));
  }
  return {
    blockCount: Math.floor((offset + total - 1) / M) + 1,
    edges: [...groups.values()].sort((a, b) => a.u - b.u || a.v - b.v),
  };
}

function relationKey(delta, pairs) { return `${delta}|${pairs.map(([a,b]) => `${a}:${b}`).join(",")}`; }
const incompatibilityCache = new Map();
function incompatible(words, delta, pairs) {
  const key = relationKey(delta, pairs);
  if (incompatibilityCache.has(key)) return incompatibilityCache.get(key);
  const left = new Set(words.map(word => pairs.map(([p]) => word[p]).join("")));
  let answer = true;
  for (const word of words) {
    const sig = pairs.map(([,p]) => String((Number(word[p]) + delta) % 3)).join("");
    if (left.has(sig)) { answer = false; break; }
  }
  incompatibilityCache.set(key, answer);
  return answer;
}

const relationCache = new Map();
function relationGroups(words, delta, pairs) {
  const key = relationKey(delta, pairs);
  if (relationCache.has(key)) return relationCache.get(key);
  const left = new Map(), right = new Map();
  for (let r = 0; r < words.length; r++) {
    const bit = 1n << BigInt(r), word = words[r];
    const a = pairs.map(([p]) => word[p]).join("");
    const b = pairs.map(([,p]) => String((Number(word[p]) + delta) % 3)).join("");
    left.set(a, (left.get(a) ?? 0n) | bit);
    right.set(b, (right.get(b) ?? 0n) | bit);
  }
  const groups = [];
  for (const [sig, lm] of left) if (right.has(sig)) groups.push([lm, right.get(sig)]);
  relationCache.set(key, groups);
  return groups;
}

function revise(domains, rel, reverse) {
  const u = reverse ? rel.v : rel.u, v = reverse ? rel.u : rel.v;
  const old = domains[u];
  let next = 0n;
  for (const [lm, rm] of rel.groups) {
    const um = reverse ? rm : lm, vm = reverse ? lm : rm;
    if ((old & um) !== 0n && (domains[v] & vm) !== 0n) next |= old & um;
  }
  if (next === old) return false;
  domains[u] = next;
  return true;
}

function propagate(domains, relations, incident) {
  const queue = [];
  for (let i = 0; i < relations.length; i++) { queue.push([i,false]); queue.push([i,true]); }
  for (let head = 0; head < queue.length; head++) {
    const [index, reverse] = queue[head], rel = relations[index];
    if (!revise(domains, rel, reverse)) continue;
    const u = reverse ? rel.v : rel.u;
    if (domains[u] === 0n) return false;
    for (const other of incident[u]) if (other !== index) queue.push([other, relations[other].u === u]);
  }
  return true;
}

function singleton(mask) { return mask !== 0n && (mask & (mask - 1n)) === 0n; }
function solve(domains, relations, incident) {
  domains = domains.slice();
  if (!propagate(domains, relations, incident)) return null;
  let variable = -1;
  for (let i = 0; i < domains.length; i++) if (!singleton(domains[i])) { variable = i; break; }
  if (variable < 0) return domains;
  let choices = domains[variable];
  while (choices !== 0n) {
    const bit = choices & -choices;
    choices -= bit;
    const branch = domains.slice(); branch[variable] = bit;
    const answer = solve(branch, relations, incident);
    if (answer !== null) return answer;
  }
  return null;
}

if (process.argv.length !== 6) throw new Error("usage: node verify_one_deletion_range.mjs SOURCE CERT_DIR FIRST LAST");
const source = fs.readFileSync(process.argv[2]);
const words = source.toString("ascii").trimEnd().split(/\r?\n/);
if (words.length !== K || new Set(words).size !== K) throw new Error(`expected ${K} distinct canonical codewords`);
if (words.some(word => !/^[012]{54}$/.test(word))) throw new Error("malformed canonical codeword");
if (words.join("\n") !== [...words].sort().join("\n")) throw new Error("canonical codewords are not sorted");
const reversals = new Set(words.map(word => [...word].reverse().join("")));
if (words.some(word => !reversals.has(word))) throw new Error("codebook is not reversal closed");

const directory = process.argv[3], first = Number(process.argv[4]), last = Number(process.argv[5]);
let checked = 0, residuals = 0, totalCount = 0;
for (let total = first; total <= last; total += 2) {
  const csp = path.join(directory, `ONE_DELETION_SHELL_${total}_CSP.json`);
  const plain = path.join(directory, `ONE_DELETION_SHELL_${total}.json`);
  const filename = fs.existsSync(csp) ? csp : plain;
  const certificate = JSON.parse(fs.readFileSync(filename, "utf8"));
  if (certificate.total !== total) throw new Error(`certificate mismatch at ${total}`);
  const proof = Buffer.from(certificate.edge_indices_base64, "base64");
  let cursor = 0;
  const longer = (total + 1) >> 1;
  for (const orientation of ["left-longer", "right-longer"]) {
    for (let offset = 0; offset < M; offset++) {
      const initial = pattern(total, offset, 0, orientation);
      const outers = outerWords(initial.blockCount);
      for (let deletion = 0; deletion < longer; deletion++) {
        const {blockCount, edges} = pattern(total, offset, deletion, orientation);
        for (const outer of outers) {
          const selected = proof[cursor++];
          if (selected < edges.length) {
            const edge = edges[selected], delta = (outer[edge.v] - outer[edge.u] + 3) % 3;
            if (!incompatible(words, delta, edge.pairs)) throw new Error(`false edge at ${total}/${orientation}/${offset}/${deletion}`);
          } else if (selected === 255) {
            const relations = [], incident = Array.from({length: blockCount}, () => []);
            for (const edge of edges) {
              const delta = (outer[edge.v] - outer[edge.u] + 3) % 3;
              const rel = {u: edge.u, v: edge.v, groups: relationGroups(words, delta, edge.pairs)};
              const index = relations.length; relations.push(rel); incident[rel.u].push(index); incident[rel.v].push(index);
            }
            if (solve(Array(blockCount).fill(FULL), relations, incident) !== null) throw new Error(`supported residual at ${total}/${orientation}/${offset}/${deletion}`);
            residuals++;
          } else throw new Error(`invalid selected edge ${selected} at total ${total}`);
        }
      }
    }
  }
  if (cursor !== proof.length || cursor !== certificate.case_count) throw new Error(`count mismatch at ${total}`);
  checked += cursor; totalCount++;
}
console.log("INDEPENDENT_ONE_DELETION_RANGE_PASS");
console.log(JSON.stringify({first,last,shells:totalCount,cases:checked,residuals,incompatibilityCacheEntries:incompatibilityCache.size,relationCacheEntries:relationCache.size}, null, 2));
