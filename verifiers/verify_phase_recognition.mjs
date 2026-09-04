const CODEWORDS = {
  0: ["210201202120102012", "210201021202102012"],
  1: ["021012010201210120", "021012102010210120"],
  2: ["102120121012021201", "102120210121021201"],
};

function hasLinearSquare(word) {
  for (let end = 2; end <= word.length; end += 1) {
    for (let root = 1; 2 * root <= end; root += 1) {
      if (word.slice(end - 2 * root, end - root) === word.slice(end - root, end)) {
        return true;
      }
    }
  }
  return false;
}

function validOutputs() {
  const outputs = [];
  for (let a = 0; a < 3; a += 1) {
    for (let b = 0; b < 3; b += 1) {
      for (let c = 0; c < 3; c += 1) {
        const outer = `${a}${b}${c}`;
        if (hasLinearSquare(outer)) continue;
        for (let mask = 0; mask < 8; mask += 1) {
          let output = "";
          for (let index = 0; index < 3; index += 1) {
            output += CODEWORDS[outer[index]][(mask >> index) & 1];
          }
          outputs.push(output);
        }
      }
    }
  }
  return outputs;
}

function phaseClasses(outputs, length) {
  const classes = new Map();
  for (const output of outputs) {
    for (let start = 0; start + length <= output.length; start += 1) {
      const factor = output.slice(start, start + length);
      if (!classes.has(factor)) classes.set(factor, new Set());
      classes.get(factor).add(start % 18);
    }
  }
  return classes;
}

function ambiguities(classes) {
  return [...classes.entries()]
    .filter(([, phases]) => phases.size > 1)
    .map(([factor, phases]) => [factor, [...phases].sort((x, y) => x - y)])
    .sort(([left], [right]) => left.localeCompare(right));
}

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

const outputs = validOutputs();
assert(outputs.length === 96, `expected 96 outputs, got ${outputs.length}`);
const classes13 = phaseClasses(outputs, 13);
const classes14 = phaseClasses(outputs, 14);
const ambiguous13 = ambiguities(classes13);
const ambiguous14 = ambiguities(classes14);
const expected13 = [
  ["0121021201210", [8, 15]],
  ["1202102012021", [8, 15]],
  ["2010210120102", [8, 15]],
];

assert(JSON.stringify(ambiguous13) === JSON.stringify(expected13),
  `unexpected length-13 ambiguities: ${JSON.stringify(ambiguous13)}`);
assert(ambiguous14.length === 0, "length 14 does not determine phase");
assert(classes14.size === 198, `expected 198 length-14 factors, got ${classes14.size}`);

console.log(JSON.stringify({
  status: "PASS",
  implementation: "independent-javascript-enumeration",
  squareFreeOuterTriples: outputs.length / 8,
  threeBlockOutputs: outputs.length,
  length13Factors: classes13.size,
  length13Ambiguities: ambiguous13,
  length14Factors: classes14.size,
  length14Ambiguities: ambiguous14.length,
}, null, 2));
