#!/usr/bin/env node
// Verify arc inconsistency of the total-251 coordinate cores.

import fs from "node:fs";

const K = 952;

function relation(words, delta, pairs) {
  const left = new Map(), right = new Map();
  for (let choice = 0; choice < words.length; choice++) {
    let ls = "", rs = "";
    for (const [a, b] of pairs) {
      ls += words[choice][a];
      rs += String((Number(words[choice][b]) + delta) % 3);
    }
    if (!left.has(ls)) left.set(ls, []);
    if (!right.has(rs)) right.set(rs, []);
    left.get(ls).push(choice);
    right.get(rs).push(choice);
  }
  const groups = [];
  for (const [signature, lchoices] of left) {
    if (right.has(signature)) groups.push([lchoices, right.get(signature)]);
  }
  return groups;
}

function anyIn(domain, choices) {
  for (const choice of choices) if (domain[choice]) return true;
  return false;
}

function revise(domains, edge, reverse) {
  const u = reverse ? edge.v : edge.u;
  const v = reverse ? edge.u : edge.v;
  const keep = new Uint8Array(K);
  for (const [left, right] of edge.groups) {
    const source = reverse ? right : left;
    const target = reverse ? left : right;
    if (anyIn(domains[v], target)) {
      for (const choice of source) if (domains[u][choice]) keep[choice] = 1;
    }
  }
  let changed = false, nonempty = false;
  for (let i = 0; i < K; i++) {
    if (domains[u][i] !== keep[i]) changed = true;
    domains[u][i] = keep[i];
    if (keep[i]) nonempty = true;
  }
  return { changed, nonempty, vertex: u };
}

function arcInconsistent(blockCount, edges) {
  const domains = Array.from({ length: blockCount }, () => new Uint8Array(K).fill(1));
  const incident = Array.from({ length: blockCount }, () => []);
  edges.forEach((edge, index) => {
    incident[edge.u].push(index);
    incident[edge.v].push(index);
  });
  const queue = [];
  edges.forEach((_, index) => { queue.push([index, false], [index, true]); });
  let head = 0;
  while (head < queue.length) {
    const [index, reverse] = queue[head++];
    const result = revise(domains, edges[index], reverse);
    if (!result.nonempty) return true;
    if (!result.changed) continue;
    for (const other of incident[result.vertex]) {
      if (other === index) continue;
      queue.push([other, edges[other].u === result.vertex]);
    }
  }
  return false;
}

if (process.argv.length !== 4) {
  throw new Error("usage: node verify_one_deletion_cores.mjs SOURCE CORES");
}
const source = fs.readFileSync(process.argv[2]);
const words = source.toString("ascii").trimEnd().split(/\r?\n/);
if (words.length !== K || new Set(words).size !== K) throw new Error(`expected ${K} distinct canonical codewords`);
if (words.some(word => !/^[012]{54}$/.test(word))) throw new Error("malformed canonical codeword");
if (words.join("\n") !== [...words].sort().join("\n")) throw new Error("canonical codewords are not sorted");
const reversals = new Set(words.map(word => [...word].reverse().join("")));
if (words.some(word => !reversals.has(word))) throw new Error("codebook is not reversal closed");

const data = JSON.parse(fs.readFileSync(process.argv[3], "utf8"));
let covered = 0, maximum = 0;
for (const item of data.cores) {
  const rep = item.representative;
  const edges = rep.core_edges.map(edge => ({
    u: Number(edge.u),
    v: Number(edge.v),
    groups: relation(words, Number(edge.delta), edge.pairs),
  }));
  const count = rep.core_edges.reduce((sum, edge) => sum + edge.pairs.length, 0);
  maximum = Math.max(maximum, count);
  if (!arcInconsistent(rep.outer.length, edges)) {
    throw new Error(`core remained arc consistent: ${item.signature}`);
  }
  covered += Number(item.frequency);
}
if (covered !== 344 || maximum > 14) {
  throw new Error(`coverage/size mismatch: covered=${covered}, maximum=${maximum}`);
}
console.log("INDEPENDENT_TOTAL_251_COORDINATE_CORES_PASS");
console.log(JSON.stringify({ coreTypes: data.cores.length, covered, maximum }, null, 2));
