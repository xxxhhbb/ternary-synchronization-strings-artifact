import fs from "node:fs";

const CODEWORDS = {
  0: ["210201202120102012", "210201021202102012"],
  1: ["021012010201210120", "021012102010210120"],
  2: ["102120121012021201", "102120210121021201"],
};

const D19 = {
  0: "0120212012102120210",
  1: "1201020120210201021",
  2: "2012101201021012102",
};

const D23 = {
  0: "01202120102012102120210",
  1: "12010201210120210201021",
  2: "20121012021201021012102",
};

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function hasLinearSquare(word) {
  for (let end = 2; end <= word.length; end += 1) {
    for (let root = 1; 2 * root <= end; root += 1) {
      let equal = true;
      for (let index = 0; index < root; index += 1) {
        if (word[end - 2 * root + index] !== word[end - root + index]) {
          equal = false;
          break;
        }
      }
      if (equal) return true;
    }
  }
  return false;
}

function squareFreeContexts() {
  const contexts = [];
  for (let value = 0; value < 3 ** 4; value += 1) {
    let number = value;
    const letters = ["0", "0", "0", "0"];
    for (let position = 3; position >= 0; position -= 1) {
      letters[position] = String(number % 3);
      number = Math.floor(number / 3);
    }
    const context = letters.join("");
    if (!hasLinearSquare(context)) contexts.push(context);
  }
  return contexts;
}

function expandContext(context) {
  const [a, b, c, d] = context;
  const left = D19[a] + D19[b];
  const right = D23[c] + D23[d];
  return { outer: left + right, boundary: 18 * left.length };
}

function expandBrinkhuis(outer, bits) {
  let result = "";
  for (let position = 0; position < outer.length; position += 1) {
    result += CODEWORDS[outer[position]][Number(bits[position])];
  }
  return result;
}

function firstCrossingSquare(word, seam, maxRoot) {
  for (let root = 1; root <= maxRoot; root += 1) {
    const firstStart = Math.max(0, seam - 2 * root + 1);
    const lastStart = Math.min(seam - 1, word.length - 2 * root);
    for (let start = firstStart; start <= lastStart; start += 1) {
      let equal = true;
      for (let position = 0; position < root; position += 1) {
        if (word[start + position] !== word[start + root + position]) {
          equal = false;
          break;
        }
      }
      if (equal) return { root, start };
    }
  }
  return null;
}

const certificatePath = process.argv[2] ?? "UNIVERSAL_DEJEAN_TEMPLATES_17.json";
const payload = JSON.parse(fs.readFileSync(certificatePath, "utf8"));
const contexts = squareFreeContexts();
assert(contexts.length === 18, `expected 18 contexts, got ${contexts.length}`);
assert(payload.records.length === 17, "certificate must contain one record per residue");
assert(payload.max_root === 288, "unexpected root cutoff");
assert(JSON.stringify(payload.offsets) === JSON.stringify([-66, -61, 86]),
  "unexpected offset set");

const residues = new Set();
let cases = 0;
let minimumLeftBuffer = Number.POSITIVE_INFINITY;
let minimumRightBuffer = Number.POSITIVE_INFINITY;

for (const record of payload.records) {
  const { residue, gap, offset, period_pattern: pattern, choice_bits: bits } = record;
  assert(Number.isInteger(residue) && residue >= 1 && residue <= 17,
    `invalid residue ${residue}`);
  assert(!residues.has(residue), `duplicate residue ${residue}`);
  residues.add(residue);
  const expectedGap = residue + ([7, 9].includes(residue) ? 18 : 0);
  assert(gap === expectedGap, `wrong canonical gap for residue ${residue}`);
  assert(payload.offsets.includes(offset), `unlisted offset for residue ${residue}`);
  assert(/^[01]+$/.test(bits) && bits.length === 84,
    `invalid occurrence choices for residue ${residue}`);
  assert(/^[01]{1,3}$/.test(pattern),
    'invalid period pattern');
  const periodicBits = Array.from(
    { length: bits.length },
    (_, index) => pattern[index % pattern.length],
  ).join('');
  assert(bits === periodicBits,
    'choice bits do not repeat the declared pattern');

  for (const context of contexts) {
    const { outer, boundary } = expandContext(context);
    assert(outer.length === bits.length, `outer length mismatch for ${context}`);
    const seam = boundary + offset;
    const output = expandBrinkhuis(outer, bits);
    assert(seam >= 0 && seam + gap <= output.length,
      `gap leaves the context for ${context}:${residue}`);
    const defect = output.slice(0, seam) + output.slice(seam + gap);
    const leftBuffer = seam;
    const rightBuffer = defect.length - seam;
    minimumLeftBuffer = Math.min(minimumLeftBuffer, leftBuffer);
    minimumRightBuffer = Math.min(minimumRightBuffer, rightBuffer);
    assert(leftBuffer >= 2 * payload.max_root,
      `left buffer too short for ${context}:${residue}`);
    assert(rightBuffer >= 2 * payload.max_root,
      `right buffer too short for ${context}:${residue}`);
    const obstruction = firstCrossingSquare(defect, seam, payload.max_root);
    assert(obstruction === null,
      `crossing square for ${context}:${residue}: ${JSON.stringify(obstruction)}`);
    cases += 1;
  }
}

for (let residue = 1; residue <= 17; residue += 1) {
  assert(residues.has(residue), `missing residue ${residue}`);
}
assert(cases === 18 * 17, `expected 306 replay cases, got ${cases}`);

console.log(JSON.stringify({
  status: "PASS",
  implementation: "independent-javascript-universal-template-replay",
  templateRecords: payload.records.length,
  distinctOffsets: payload.offsets.length,
  contexts: contexts.length,
  cases,
  maximumRootChecked: payload.max_root,
  minimumLeftBuffer,
  minimumRightBuffer,
}, null, 2));
